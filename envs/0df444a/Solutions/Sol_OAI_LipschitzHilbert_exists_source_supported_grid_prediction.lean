-- Prove2me | solution 1 for OAI.LipschitzHilbert.exists_source_supported_grid_prediction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:37:21.411446+00:00
-- url     : https://prove2.me/submissions/9d3d7aec-6e6e-431a-825e-3b9cb57676d5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_Quantiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite quantiles for the fourth-moment gap

The lower and upper quantile choices in the proof of `phase:quantile-gap`, §7.
Weights are listed in increasing frequency order. No uniform measure on the
frequency list is assumed.
-/

open scoped BigOperators

namespace LipschitzHilbert

theorem prefixMass_succ (w : ℕ → ℝ) (n : ℕ) :
    prefixMass w (n + 1) = prefixMass w n + w n := Finset.sum_range_succ _ _

theorem prefixMass_mono {w : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) :
    Monotone (prefixMass w) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun i _ _ => hw i)

/-- The first cumulative crossing has an atom on its right and a strict
inequality immediately to its left. -/
theorem exists_first_crossing (w : ℕ → ℝ) (N : ℕ) {t : ℝ}
    (ht : 0 < t) (htN : t ≤ prefixMass w N) :
    ∃ a < N, prefixMass w a < t ∧ t ≤ prefixMass w (a + 1) := by
  classical
  let hex : ∃ n : ℕ, t ≤ prefixMass w n := ⟨N, htN⟩
  let k := Nat.find hex
  have hk : t ≤ prefixMass w k := Nat.find_spec hex
  have hkN : k ≤ N := Nat.find_min' hex htN
  have hkpos : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    simp [hz, prefixMass] at hk
    linarith
  refine ⟨k - 1, by omega, ?_, ?_⟩
  · exact lt_of_not_ge (Nat.find_min hex (show k - 1 < k by omega))
  · simpa [show k - 1 + 1 = k by omega] using hk

/-- Nonconcentration of single atoms forces the two quarter-tail quantiles
to be distinct. The inequalities also bound the mass outside their interval. -/
theorem exists_distinct_quantiles (w : ℕ → ℝ) (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hw : ∀ i, 0 ≤ w i)
    (htotal : prefixMass w N = 1) (hatom : ∀ i < N, w i ≤ 1 - κ) :
    ∃ a b : ℕ, a < b ∧ b < N ∧
      prefixMass w a < κ / 4 ∧ κ / 4 ≤ prefixMass w (a + 1) ∧
      prefixMass w b < 1 - κ / 4 ∧ 1 - κ / 4 ≤ prefixMass w (b + 1) ∧
      1 - κ / 2 ≤ prefixMass w (b + 1) - prefixMass w a := by
  obtain ⟨a, haN, ha, ha'⟩ := exists_first_crossing w N
    (show 0 < κ / 4 by linarith) (show κ / 4 ≤ prefixMass w N by rw [htotal]; linarith)
  obtain ⟨b, hbN, hb, hb'⟩ := exists_first_crossing w N
    (show 0 < 1 - κ / 4 by linarith)
    (show 1 - κ / 4 ≤ prefixMass w N by rw [htotal]; linarith)
  have hab : a < b := by
    by_contra h
    have hba : b ≤ a := by omega
    have hmono := prefixMass_mono hw hba
    have hsingle := hatom b hbN
    rw [prefixMass_succ] at hb'
    linarith
  exact ⟨a, b, hab, hbN, ha, ha', hb, hb', by linarith⟩

/-- The two closed halves cover the closed interval; midpoint atoms may be
counted twice, which has the favorable sign. -/
theorem intervalMass_le_halves {ι : Type*} [Fintype ι]
    (w frequency : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a b : ℝ) :
    intervalMass w frequency a b ≤ intervalMass w frequency a ((a + b) / 2) +
      intervalMass w frequency ((a + b) / 2) b := by
  classical
  unfold intervalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hcover : (a ≤ frequency i ∧ frequency i ≤ b) →
      (a ≤ frequency i ∧ frequency i ≤ (a + b) / 2) ∨
        ((a + b) / 2 ≤ frequency i ∧ frequency i ≤ b) := by
    intro hi
    rcases le_total (frequency i) ((a + b) / 2) with h | h
    · exact Or.inl ⟨hi.1, h⟩
    · exact Or.inr ⟨h, hi.2⟩
  split_ifs <;> first | linarith [hw i] | tauto

/-- One half of a frequency interval carries at least half its mass. -/
theorem exists_heavy_half {ι : Type*} [Fintype ι]
    (w frequency : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {a b m : ℝ}
    (hab : a ≤ b) (hm : m ≤ intervalMass w frequency a b) :
    ∃ e h : ℝ, a ≤ e ∧ e ≤ h ∧ h ≤ b ∧
      h - e = (b - a) / 2 ∧ m / 2 ≤ intervalMass w frequency e h := by
  have hs := intervalMass_le_halves w frequency hw a b
  by_cases hl : m / 2 ≤ intervalMass w frequency a ((a + b) / 2)
  · exact ⟨a, (a + b) / 2, le_rfl, by linarith, by linarith, by ring, hl⟩
  · exact ⟨(a + b) / 2, b, by linarith, by linarith, le_rfl, by ring,
      by linarith⟩

end LipschitzHilbert

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FrequencyQuantiles
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quarter-tail quantiles in a finite ordered frequency list. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem extendWeights_nonneg {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∀ i, 0 ≤ extendWeights x i := by
  intro i
  unfold extendWeights
  split <;> simp_all

theorem prefixMass_extend {N : ℕ} (x : Fin N → ℝ) {k : ℕ} (hk : k ≤ N) :
    prefixMass (extendWeights x) k = ∑ i : Fin N, if (i : ℕ) < k then x i else 0 := by
  classical
  have he : (Finset.range N).filter (fun i => i < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  calc
    _ = ∑ i ∈ Finset.range N, if i < k then extendWeights x i else 0 := by
      rw [← Finset.sum_filter, he]
      rfl
    _ = _ := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp [extendWeights, i.isLt]

/-- Quarter-tail quantiles for strictly ordered frequencies. -/
theorem finite_frequency_quantiles {N : ℕ} (x frequency : Fin N → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (hfrequency : StrictMono frequency) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hatom : ∀ i, x i ≤ 1 - κ) :
    ∃ a b : Fin N, a < b ∧
      κ / 4 ≤ (∑ i, if frequency i ≤ frequency a then x i else 0) ∧
      κ / 4 ≤ (∑ i, if frequency b ≤ frequency i then x i else 0) ∧
      1 - κ / 2 ≤ intervalMass x frequency (frequency a) (frequency b) := by
  classical
  have htotal : prefixMass (extendWeights x) N = 1 := by
    rw [prefixMass_extend x le_rfl]
    simpa only [Fin.isLt, ite_true, if_true] using hsum
  obtain ⟨a, b, hab, hbN, ha, ha', hb, hb', hcentral⟩ :=
    exists_distinct_quantiles (extendWeights x) N hκ hκ1
      (extendWeights_nonneg x hx) htotal (fun i hi => by simpa [extendWeights, hi] using hatom ⟨i, hi⟩)
  have haN : a < N := lt_trans hab hbN
  let a' : Fin N := ⟨a, haN⟩
  let b' : Fin N := ⟨b, hbN⟩
  have hleft : prefixMass (extendWeights x) (a + 1) =
      ∑ i, if frequency i ≤ frequency a' then x i else 0 := by
    rw [prefixMass_extend x (by omega)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hfrequency.le_iff_le]
    congr 1
    apply propext
    change ((i : ℕ) < a + 1 ↔ (i : ℕ) ≤ a)
    omega
  have hright : (∑ i, if frequency b' ≤ frequency i then x i else 0) =
      1 - prefixMass (extendWeights x) b := by
    rw [prefixMass_extend x hbN.le, ← hsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hfrequency.le_iff_le]
    by_cases hi : (i : ℕ) < b
    · have hn : ¬ b' ≤ i := by simpa [b', Fin.le_def] using (not_le.mpr hi)
      simp [hi, hn]
    · have hn : b' ≤ i := by simpa [b', Fin.le_def] using (Nat.le_of_not_gt hi)
      simp [hi, hn]
  have hmiddle : intervalMass x frequency (frequency a') (frequency b') =
      prefixMass (extendWeights x) (b + 1) - prefixMass (extendWeights x) a := by
    rw [prefixMass_extend x (by omega), prefixMass_extend x haN.le]
    unfold intervalMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hfrequency.le_iff_le, Fin.le_def, a', b']
    by_cases hi : (i : ℕ) < a
    · have hib : (i : ℕ) < b + 1 := by omega
      have hni : ¬ a ≤ (i : ℕ) := by omega
      simp [hi, hib, hni]
    · have hni : a ≤ (i : ℕ) := by omega
      by_cases hib : (i : ℕ) < b + 1
      · have hle : (i : ℕ) ≤ b := by omega
        simp [hi, hib, hni, hle]
      · have hle : ¬ (i : ℕ) ≤ b := by omega
        simp [hi, hib, hni, hle]
  refine ⟨a', b', hab, ?_, ?_, ?_⟩
  · rwa [← hleft]
  · rw [hright]
    linarith
  · rwa [hmiddle]

/-- Sorting by the injective frequency map removes the ordering hypothesis
from the finite quantile construction. -/
theorem frequency_quantiles {ι : Type*} [Fintype ι] (x frequency : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (hinj : Function.Injective frequency) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hatom : ∀ i, x i ≤ 1 - κ) :
    ∃ a b : ι, frequency a < frequency b ∧
      κ / 4 ≤ (∑ i, if frequency i ≤ frequency a then x i else 0) ∧
      κ / 4 ≤ (∑ i, if frequency b ≤ frequency i then x i else 0) ∧
      1 - κ / 2 ≤ intervalMass x frequency (frequency a) (frequency b) := by
  classical
  let : LinearOrder ι := LinearOrder.lift' frequency hinj
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  have he : StrictMono (fun i => frequency (e i)) := fun _ _ hij => e.strictMono hij
  have hs : (∑ i, x (e i)) = 1 := (Equiv.sum_comp e.toEquiv x).trans hsum
  obtain ⟨a, b, hab, ha, hb, hc⟩ := finite_frequency_quantiles
    (fun i => x (e i)) (fun i => frequency (e i)) (fun i => hx (e i)) hs he
      hκ hκ1 (fun i => hatom (e i))
  refine ⟨e a, e b, he hab, ?_, ?_, ?_⟩
  · rw [← Equiv.sum_comp e.toEquiv
      (fun i => if frequency i ≤ frequency (e a) then x i else 0)]
    exact ha
  · rw [← Equiv.sum_comp e.toEquiv
      (fun i => if frequency (e b) ≤ frequency i then x i else 0)]
    exact hb
  · change 1 - κ / 2 ≤ ∑ i, if frequency (e a) ≤ frequency i ∧
        frequency i ≤ frequency (e b) then x i else 0
    rw [← Equiv.sum_comp e.toEquiv
      (fun i => if frequency (e a) ≤ frequency i ∧ frequency i ≤ frequency (e b)
        then x i else 0)]
    exact hc

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_Hellinger
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite probability estimate in the phase argument

This is the Hellinger-affinity calculation in §7, proof of `phase:quantile-gap`,
of *A uniform Hilbert transform estimate for Lipschitz directions*.
The finite probability calculation is proved directly.
-/

open scoped BigOperators

namespace LipschitzHilbert

/-- Squared total variation estimate, before division of the `ℓ¹` distance by two. -/
theorem l1_sq_le_affinity {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    (∑ i, |p i - q i|) ^ 2 ≤ 4 * (1 - affinity p q ^ 2) := by
  classical
  have hid (i : ι) :
      |p i - q i| = |Real.sqrt (p i) - Real.sqrt (q i)| *
        (Real.sqrt (p i) + Real.sqrt (q i)) := by
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
  have hm : (∑ i, |Real.sqrt (p i) - Real.sqrt (q i)| ^ 2) =
      2 - 2 * affinity p q := by
    have hi (i : ι) : |Real.sqrt (p i) - Real.sqrt (q i)| ^ 2 =
        p i + q i - 2 * (Real.sqrt (p i) * Real.sqrt (q i)) := by
      rw [sq_abs, sub_sq, Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
      ring
    simp_rw [hi]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hp1, hq1, affinity]
    ring
  have ha : (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) =
      2 + 2 * affinity p q := by
    have hi (i : ι) : (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2 =
        p i + q i + 2 * (Real.sqrt (p i) * Real.sqrt (q i)) := by
      rw [add_sq, Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
      ring
    simp_rw [hi]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hq1, affinity]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun i => |Real.sqrt (p i) - Real.sqrt (q i)|)
    (fun i => Real.sqrt (p i) + Real.sqrt (q i))
  simp_rw [← hid] at hcs
  rw [hm, ha] at hcs
  nlinarith

/-- Each event deficit is at most the total variation distance. -/
theorem event_deficit_le_l1_half {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (s : Finset ι) :
    2 * |∑ i ∈ s, (p i - q i)| ≤ ∑ i, |p i - q i| := by
  classical
  have hsum : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hp1, hq1, sub_self]
  have hcomp : ∑ i ∈ Finset.univ \ s, (p i - q i) =
      -(∑ i ∈ s, (p i - q i)) := by
    have ht := Finset.sum_sdiff (f := fun i => p i - q i) (Finset.subset_univ s)
    rw [hsum] at ht
    linarith
  have hs := Finset.abs_sum_le_sum_abs (f := fun i => p i - q i) (s := s)
  have ht := Finset.abs_sum_le_sum_abs (f := fun i => p i - q i)
    (s := Finset.univ \ s)
  rw [hcomp, abs_neg] at ht
  have hadd := Finset.sum_sdiff (f := fun i => |p i - q i|) (Finset.subset_univ s)
  linarith

/-- The event estimate used to turn a quantile deficit into a fourth-moment gap. -/
theorem event_deficit_sq_le_one_sub_affinity_sq {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) (s : Finset ι) :
    (∑ i ∈ s, (p i - q i)) ^ 2 ≤ 1 - affinity p q ^ 2 := by
  have h1 := event_deficit_le_l1_half p q hp1 hq1 s
  have h2 := l1_sq_le_affinity p q hp hq hp1 hq1
  have hn : 0 ≤ ∑ i, |p i - q i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h3 : (2 * |∑ i ∈ s, (p i - q i)|) ^ 2 ≤ (∑ i, |p i - q i|) ^ 2 :=
    (sq_le_sq₀ (by positivity) hn).mpr h1
  rw [mul_pow, sq_abs] at h3
  nlinarith

/-- The completed triple law may have mass less than one. Adjoining its missing
mass at one point, where the independent law has mass zero, preserves affinity. -/
theorem subprobability_event_deficit_sq {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i ≤ 1) (hq1 : ∑ i, q i = 1) (s : Finset ι) :
    (∑ i ∈ s, (q i - p i)) ^ 2 ≤ 1 - affinity p q ^ 2 := by
  classical
  let p' : Option ι → ℝ := fun i => i.elim (1 - ∑ j, p j) p
  let q' : Option ι → ℝ := fun i => i.elim 0 q
  have hp' : ∀ i, 0 ≤ p' i := by
    intro i
    cases i with
    | none => exact sub_nonneg.mpr hp1
    | some i => exact hp i
  have hq' : ∀ i, 0 ≤ q' i := by
    intro i
    cases i with
    | none => exact le_rfl
    | some i => exact hq i
  have hp1' : ∑ i, p' i = 1 := by simp [p', Fintype.sum_option]
  have hq1' : ∑ i, q' i = 1 := by simp [q', Fintype.sum_option, hq1]
  have ha : affinity p' q' = affinity p q := by
    simp [affinity, Fintype.sum_option, p', q']
  have hs : (∑ i ∈ s.image Option.some, (p' i - q' i)) =
      -(∑ i ∈ s, (q i - p i)) := by
    rw [Finset.sum_image]
    · simp only [p', q', Option.elim_some, Finset.sum_sub_distrib]
      ring
    · intro a _ b _ hab
      exact Option.some.inj hab
  have h := event_deficit_sq_le_one_sub_affinity_sq p' q' hp' hq' hp1' hq1'
    (s.image Option.some)
  rwa [hs, neg_sq, ha] at h

/-- A definite event deficit forces the strict fourth-moment gain. This is the
last algebraic step of the manuscript's quantile-gap argument. -/
theorem strict_gap_of_event_deficit {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i ≤ 1) (hq1 : ∑ i, q i = 1) (s : Finset ι)
    {Q g : ℝ} (hQ : 0 ≤ Q) (hg : 0 ≤ g)
    (hgain : Q ^ 2 ≤ affinity p q)
    (hdeficit : g ≤ ∑ i ∈ s, (q i - p i)) :
    Q ≤ 1 - g ^ 2 / 4 := by
  have hevent := subprobability_event_deficit_sq p q hp hq hp1 hq1 s
  have hd : 0 ≤ ∑ i ∈ s, (q i - p i) := hg.trans hdeficit
  have hgsq : g ^ 2 ≤ (∑ i ∈ s, (q i - p i)) ^ 2 :=
    (sq_le_sq₀ hg hd).mpr hdeficit
  have haf : 0 ≤ affinity p q := (sq_nonneg Q).trans hgain
  have hfour : Q ^ 4 ≤ affinity p q ^ 2 := by
    have ht := (sq_le_sq₀ (sq_nonneg Q) haf).mpr hgain
    nlinarith
  have hpoly : Q ^ 4 ≥ 1 - 4 * (1 - Q) := by
    nlinarith [sq_nonneg (Q - 1), mul_nonneg (sq_nonneg (Q - 1))
      (show 0 ≤ Q ^ 2 + 2 * Q + 3 by positivity)]
  nlinarith

end LipschitzHilbert

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PhaseCombinatorics
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite-phase resonance combinatorics

These are the elementary finite combinatorial ingredients of §7,
Lemma `phase:quantile-gap`, of *A uniform Hilbert transform estimate for
Lipschitz directions*. The frequency separation is quantitative; no
assumption about additive independence is made.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem resonant_swap_right {frequency : ι → ℝ} {gap : ℝ} {i j k l : ι} :
    Resonant frequency gap i j k l ↔ Resonant frequency gap i j l k := by
  simp only [Resonant, sub_sub, add_comm (frequency k) (frequency l)]

theorem resonant_swap_pairs {frequency : ι → ℝ} {gap : ℝ} {i j k l : ι} :
    Resonant frequency gap i j k l ↔ Resonant frequency gap k l i j := by
  unfold Resonant
  have h : frequency k + frequency l - frequency i - frequency j =
      -(frequency i + frequency j - frequency k - frequency l) := by ring
  rw [h, abs_neg]

/-- Three fixed indices determine at most one fourth index. -/
theorem unique_fourth {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    {i j k l l' : ι} (h : Resonant frequency gap i j k l)
    (h' : Resonant frequency gap i j k l') : l = l' := by
  by_contra hne
  have hs := hsep hne
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h
  obtain ⟨hlo', hhi'⟩ := abs_lt.mp h'
  have hlt : |frequency l - frequency l'| < gap := by
    apply abs_lt.mpr
    constructor <;> linarith
  exact (not_lt_of_ge hs) hlt

theorem unique_second {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    {i j j' k l : ι} (h : Resonant frequency gap i j k l)
    (h' : Resonant frequency gap i j' k l) : j = j' :=
  unique_fourth hgap hsep (resonant_swap_pairs.mp h) (resonant_swap_pairs.mp h')

/-- For three fixed indices, summing a nonnegative weight over resonant
completions costs at most that weight. -/
theorem sum_completions_le [Fintype ι] {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    (i j k : ι) (a : ℝ) (ha : 0 ≤ a) :
    (∑ l, if Resonant frequency gap i j k l then a else 0) ≤ a := by
  classical
  by_cases hex : ∃ l, Resonant frequency gap i j k l
  · obtain ⟨l₀, hl₀⟩ := hex
    have heq (l : ι) :
        (if Resonant frequency gap i j k l then a else 0) =
          if l = l₀ then a else 0 := by
      by_cases hl : l = l₀
      · subst l
        simp [hl₀]
      · have hn : ¬ Resonant frequency gap i j k l := by
          intro hr
          exact hl (unique_fourth hgap hsep hr hl₀)
        simp [hl, hn]
    simp_rw [heq]
    simp
  · have hn (l : ι) : ¬ Resonant frequency gap i j k l := fun hl => hex ⟨l, hl⟩
    simpa [hn] using ha

/-- Each triple-coordinate marginal used in the fourth-moment argument
has total mass at most one. This is the first marginal, omitting the
fourth coordinate. -/
theorem resonance_triple_mass_le_one [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      if Resonant frequency gap i j k l then x i * x j * x k else 0) ≤ 1 := by
  classical
  calc
    (∑ i, ∑ j, ∑ k, ∑ l,
        if Resonant frequency gap i j k l then x i * x j * x k else 0) ≤
        ∑ i, ∑ j, ∑ k, x i * x j * x k := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact sum_completions_le hgap hsep i j k _ (mul_nonneg (mul_nonneg (hx i) (hx j)) (hx k))
    _ = 1 := by
      simp [← Finset.mul_sum, hsum]

theorem marginal_nonneg {frequency : ι → ℝ} {gap : ℝ} {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (q : Quadruple ι) : 0 ≤ marginal frequency gap x q := by
  unfold marginal
  split
  · exact mul_nonneg (mul_nonneg (hx _) (hx _)) (hx _)
  · exact le_rfl

theorem marginal_mass_le_one [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    (∑ q : Quadruple ι, marginal frequency gap x q) ≤ 1 := by
  simpa only [Fintype.sum_prod_type, marginal] using
    resonance_triple_mass_le_one hgap hsep x hx hsum

/-- Reindexing gives all four subprobability bounds without further losses. -/
theorem permuted_marginal_mass_le_one [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (e : Quadruple ι ≃ Quadruple ι) :
    (∑ q : Quadruple ι, marginal frequency gap x (e q)) ≤ 1 := by
  rw [Equiv.sum_comp e]
  exact marginal_mass_le_one hgap hsep x hx hsum

/-- The elementary affinity bound for two subprobabilities. -/
theorem affinity_le_one [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsa : ∑ i, a i ≤ 1) (hsb : ∑ i, b i ≤ 1) :
    (∑ i, Real.sqrt (a i * b i)) ≤ 1 := by
  calc
    (∑ i, Real.sqrt (a i * b i)) = ∑ i, Real.sqrt (a i) * Real.sqrt (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Real.sqrt_mul (ha i) _
    _ ≤ Real.sqrt (∑ i, a i) * Real.sqrt (∑ i, b i) :=
      Real.sum_sqrt_mul_sqrt_le Finset.univ ha hb
    _ ≤ 1 * 1 := mul_le_mul
      (by simpa using Real.sqrt_le_sqrt hsa)
      (by simpa using Real.sqrt_le_sqrt hsb)
      (Real.sqrt_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- Four-factor Hölder in the form used by the quantile argument: the square
of the geometric sum is bounded by the affinity of its first two weights. -/
theorem geometric_sum_sq_le_affinity [Fintype ι] (a b c d : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i)
    (hsc : ∑ i, c i ≤ 1) (hsd : ∑ i, d i ≤ 1) :
    (∑ i, Real.sqrt (Real.sqrt (a i * b i) * Real.sqrt (c i * d i))) ^ 2 ≤
      ∑ i, Real.sqrt (a i * b i) := by
  let A := ∑ i, Real.sqrt (a i * b i)
  let B := ∑ i, Real.sqrt (c i * d i)
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hB1 : B ≤ 1 := affinity_le_one c d hc hd hsc hsd
  have hq : (∑ i, Real.sqrt (Real.sqrt (a i * b i) * Real.sqrt (c i * d i))) ≤
      Real.sqrt A * Real.sqrt B := by
    calc
      _ = ∑ i, Real.sqrt (Real.sqrt (a i * b i)) *
          Real.sqrt (Real.sqrt (c i * d i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Real.sqrt_mul (Real.sqrt_nonneg _) _
      _ ≤ _ := Real.sum_sqrt_mul_sqrt_le Finset.univ
        (fun i => Real.sqrt_nonneg (a i * b i))
        (fun i => Real.sqrt_nonneg (c i * d i))
  have hq0 : 0 ≤ ∑ i, Real.sqrt (Real.sqrt (a i * b i) * Real.sqrt (c i * d i)) :=
    Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  calc
    _ ≤ (Real.sqrt A * Real.sqrt B) ^ 2 :=
      (sq_le_sq₀ hq0 (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))).2 hq
    _ = A * B := by rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hB1 hA
    _ = _ := mul_one A

/-- The four triple-coordinate weights have geometric mean
`(xᵢ xⱼ xₖ xₗ)^(3/4)`, written with square roots. -/
theorem geometricTerm_eq {frequency : ι → ℝ} {gap : ℝ} {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (i j k l : ι) :
    geometricTerm frequency gap x (i, j, k, l) =
      if Resonant frequency gap i j k l then
        Real.sqrt (Real.sqrt ((x i * x j * x k * x l) ^ 3)) else 0 := by
  by_cases hr : Resonant frequency gap i j k l
  · have hp := resonant_swap_pairs.mp hr
    have hl := resonant_swap_right.mp hr
    have hpl := resonant_swap_right.mp hp
    have hi := hx i
    have hj := hx j
    have hk := hx k
    have hlx := hx l
    simp only [geometricTerm, marginal, swapPairs, swapLast, Equiv.trans_apply,
      Equiv.coe_fn_mk, hr, hp, hl, hpl, ite_true, if_true]
    rw [← Real.sqrt_mul (show 0 ≤ (x i * x j * x k) * (x k * x l * x i) by positivity)]
    congr 2
    ring
  · simp [geometricTerm, marginal, swapPairs, swapLast, hr]

theorem sqrt_sqrt_cube_eq_rpow {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (Real.sqrt (u ^ 3)) = u ^ (3 / 4 : ℝ) := by
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (pow_nonneg hu _), ← Real.rpow_natCast_mul hu]
  norm_num

theorem geometricTerm_eq_rpow {frequency : ι → ℝ} {gap : ℝ} {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (i j k l : ι) :
    geometricTerm frequency gap x (i, j, k, l) =
      if Resonant frequency gap i j k l then
        (x i * x j * x k * x l) ^ (3 / 4 : ℝ) else 0 := by
  rw [geometricTerm_eq hx]
  congr 1
  exact sqrt_sqrt_cube_eq_rpow
    (mul_nonneg (mul_nonneg (mul_nonneg (hx i) (hx j)) (hx k)) (hx l))

/-- The affinity inequality that precedes the strict quantile deficit. -/
theorem resonanceSum_sq_le_affinity [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    resonanceSum frequency gap x ^ 2 ≤
      ∑ q : Quadruple ι, Real.sqrt
        (marginal frequency gap x q * marginal frequency gap x (swapPairs q)) := by
  apply geometric_sum_sq_le_affinity
  · exact fun q => marginal_nonneg hx (swapLast q)
  · exact fun q => marginal_nonneg hx ((swapPairs.trans swapLast) q)
  · exact permuted_marginal_mass_le_one hgap hsep x hx hsum swapLast
  · exact permuted_marginal_mass_le_one hgap hsep x hx hsum (swapPairs.trans swapLast)

/-- The usual constant-one fourth-moment bound, before its strict improvement. -/
theorem resonanceSum_le_one [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    resonanceSum frequency gap x ≤ 1 := by
  have hq := resonanceSum_sq_le_affinity hgap hsep x hx hsum
  have ha := affinity_le_one (marginal frequency gap x)
    (fun q => marginal frequency gap x (swapPairs q))
    (marginal_nonneg hx) (fun q => marginal_nonneg hx (swapPairs q))
    (marginal_mass_le_one hgap hsep x hx hsum)
    (permuted_marginal_mass_le_one hgap hsep x hx hsum swapPairs)
  nlinarith [sq_nonneg (resonanceSum frequency gap x - 1)]

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_Projection
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Projection of the near-resonant quadruple measure

The quantile-gap argument in §7 projects the triple weight on quadruples
to coordinates `(i,k,l)`. Unique completion makes the Hellinger affinity
of the projected measures exactly the affinity before projection.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*}

/-- The quantile event forces its resonant completion below the selected
central half interval. This is the geometric step behind the event deficit. -/
theorem resonant_event_completion_lt {frequency : ι → ℝ} {gap a b e h : ℝ}
    (hgap : 0 < gap) (hab : gap ≤ b - a) (heh : h - e ≤ (b - a) / 2)
    {i j k l : ι} (hr : Resonant frequency gap i j k l)
    (hi : b ≤ frequency i) (hk : frequency k ≤ a) (hl : frequency l ≤ h) :
    frequency j < e := by
  have hup := (abs_lt.mp hr).2
  linarith

theorem projectedMass_nonneg [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (q : Triple ι) : 0 ≤ projectedMass frequency gap x q :=
  Finset.sum_nonneg fun _ _ => marginal_nonneg hx _

theorem independentMass_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (q : Triple ι) : 0 ≤ independentMass x q :=
  mul_nonneg (mul_nonneg (hx _) (hx _)) (hx _)

theorem sum_projectedMass_eq [Fintype ι]
    (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ) :
    (∑ q : Triple ι, projectedMass frequency gap x q) =
      ∑ q : Quadruple ι, marginal frequency gap x q := by
  calc
    _ = ∑ q : Triple ι × ι, marginal frequency gap x (insertSecond q) := by
      simp only [Fintype.sum_prod_type, projectedMass, insertSecond, Equiv.coe_fn_mk]
    _ = _ := Equiv.sum_comp insertSecond _

theorem sum_projectedMass_le_one [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    (∑ q : Triple ι, projectedMass frequency gap x q) ≤ 1 := by
  rw [sum_projectedMass_eq]
  exact marginal_mass_le_one hgap hsep x hx hsum

theorem sum_independentMass_eq_one [Fintype ι]
    (x : ι → ℝ) (hsum : ∑ i, x i = 1) :
    (∑ q : Triple ι, independentMass x q) = 1 := by
  simp [Fintype.sum_prod_type, independentMass, ← Finset.mul_sum, hsum]

/-- With at most one nonzero summand, taking this square root commutes
with the sum exactly. -/
theorem sqrt_sum_mul_of_unique_support [Fintype ι] (a : ι → ℝ) (b : ℝ)
    (hunique : ∀ i j, a i ≠ 0 → a j ≠ 0 → i = j) :
    Real.sqrt ((∑ i, a i) * b) = ∑ i, Real.sqrt (a i * b) := by
  classical
  by_cases hall : ∀ i, a i = 0
  · simp [hall]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hz (j : ι) (hji : j ≠ i) : a j = 0 := by
      by_contra hj
      exact hji (hunique j i hj hi)
    have hsum : (∑ j, a j) = a i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hz j hji
      · simp
    have hsqrt : (∑ j, Real.sqrt (a j * b)) = Real.sqrt (a i * b) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hz j hji]
      · simp
    rw [hsum, hsqrt]

theorem marginal_unique_support {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (x : ι → ℝ)
    (i k l j j' : ι)
    (hj : marginal frequency gap x (i, j, k, l) ≠ 0)
    (hj' : marginal frequency gap x (i, j', k, l) ≠ 0) : j = j' := by
  have hr : Resonant frequency gap i j k l := by
    by_contra hn
    exact hj (by simp [marginal, hn])
  have hr' : Resonant frequency gap i j' k l := by
    by_contra hn
    exact hj' (by simp [marginal, hn])
  exact unique_second hgap hsep hr hr'

theorem marginal_mul_permuted_eq_independent
    (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ) (i j k l : ι) :
    marginal frequency gap x (i, j, k, l) *
        marginal frequency gap x (swapPairs (i, j, k, l)) =
      marginal frequency gap x (i, j, k, l) * independentMass x (i, k, l) := by
  classical
  by_cases hr : Resonant frequency gap i j k l
  · have hp := resonant_swap_pairs.mp hr
    simp only [marginal, swapPairs, Equiv.coe_fn_mk, hr, hp, ite_true, if_true, independentMass]
    ring
  · simp [marginal, hr]

/-- The projection preserves the affinity, because each projected point
has at most one possible resonant completion. -/
theorem projected_affinity_eq [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ) :
    (∑ q : Triple ι,
      Real.sqrt (projectedMass frequency gap x q * independentMass x q)) =
      ∑ q : Quadruple ι, Real.sqrt
        (marginal frequency gap x q * marginal frequency gap x (swapPairs q)) := by
  calc
    _ = ∑ q : Triple ι, ∑ j,
        Real.sqrt (marginal frequency gap x (q.1, j, q.2.1, q.2.2) *
          independentMass x q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact sqrt_sum_mul_of_unique_support _ _
        (fun j j' hj hj' => marginal_unique_support hgap hsep x _ _ _ j j' hj hj')
    _ = ∑ q : Triple ι × ι, Real.sqrt
        (marginal frequency gap x (insertSecond q) *
          marginal frequency gap x (swapPairs (insertSecond q))) := by
      simp only [Fintype.sum_prod_type, insertSecond, Equiv.coe_fn_mk]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      rw [marginal_mul_permuted_eq_independent]
    _ = _ := Equiv.sum_comp insertSecond (fun q : Quadruple ι =>
      Real.sqrt (marginal frequency gap x q * marginal frequency gap x (swapPairs q)))

theorem resonanceSum_nonneg [Fintype ι]
    (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ) :
    0 ≤ resonanceSum frequency gap x :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

/-- The bound in exactly the affinity convention used for finite probabilities. -/
theorem resonanceSum_sq_le_projected_affinity [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1) :
    resonanceSum frequency gap x ^ 2 ≤
      affinity (projectedMass frequency gap x) (independentMass x) := by
  calc
    _ ≤ ∑ q : Quadruple ι, Real.sqrt
        (marginal frequency gap x q * marginal frequency gap x (swapPairs q)) :=
      resonanceSum_sq_le_affinity hgap hsep x hx hsum
    _ = ∑ q : Triple ι,
        Real.sqrt (projectedMass frequency gap x q * independentMass x q) :=
      (projected_affinity_eq hgap hsep x).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      exact Real.sqrt_mul (projectedMass_nonneg hx q) _

/-- Any event with a definite deficit between the projected and independent
triple laws gives the quantitative improvement in the fourth-moment sum. -/
theorem resonanceSum_gap_of_event_deficit [Fintype ι]
    {frequency : ι → ℝ} {gap : ℝ} (hgap : 0 < gap)
    (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (s : Finset (Triple ι)) {g : ℝ} (hg : 0 ≤ g)
    (hdeficit : g ≤ ∑ q ∈ s,
      (independentMass x q - projectedMass frequency gap x q)) :
    resonanceSum frequency gap x ≤ 1 - g ^ 2 / 4 := by
  exact strict_gap_of_event_deficit
    (projectedMass frequency gap x) (independentMass x)
    (projectedMass_nonneg hx) (independentMass_nonneg hx)
    (sum_projectedMass_le_one hgap hsep x hx hsum)
    (sum_independentMass_eq_one x hsum) s
    (resonanceSum_nonneg frequency gap x) hg
    (resonanceSum_sq_le_projected_affinity hgap hsep x hx hsum) hdeficit

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_EventMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The quantile event has a positive deficit

Finite sums implement the event calculation in the proof of
`phase:quantile-gap`. The only geometric condition is the explicitly
proved fact that a resonant completion of the event lies below its
chosen central interval.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem independent_rectangular_event (x : ι → ℝ) (I K L : Finset ι) :
    (∑ q ∈ rectangularEvent I K L, independentMass x q) =
      (∑ i ∈ I, x i) * (∑ k ∈ K, x k) * (∑ l ∈ L, x l) := by
  simp only [rectangularEvent, Finset.sum_product, independentMass]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem restricted_marginal_sum_le {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (i j k : ι) (L : Finset ι) :
    (∑ l ∈ L, marginal frequency gap x (i, j, k, l)) ≤ x i * x j * x k := by
  calc
    _ ≤ ∑ l, marginal frequency gap x (i, j, k, l) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
        (fun _ _ _ => marginal_nonneg hx _)
    _ ≤ _ := sum_completions_le hgap hsep i j k _
      (mul_nonneg (mul_nonneg (hx i) (hx j)) (hx k))

/-- Forcing the missing coordinate into `J` bounds the projected event
by the independent mass of `I × K × J`. -/
theorem projected_rectangular_event_le {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (I K L J : Finset ι)
    (hcompletion : ∀ i ∈ I, ∀ k ∈ K, ∀ l ∈ L, ∀ j,
      Resonant frequency gap i j k l → j ∈ J) :
    (∑ q ∈ rectangularEvent I K L, projectedMass frequency gap x q) ≤
      (∑ i ∈ I, x i) * (∑ k ∈ K, x k) * (∑ j ∈ J, x j) := by
  classical
  simp only [rectangularEvent, Finset.sum_product, projectedMass]
  calc
    _ ≤ ∑ i ∈ I, ∑ k ∈ K, ∑ j ∈ J, x i * x j * x k := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.sum_comm]
      calc
        _ ≤ ∑ j, if j ∈ J then x i * x j * x k else 0 := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hj : j ∈ J
          · simpa only [hj, ite_true, if_true] using restricted_marginal_sum_le hgap hsep x hx i j k L
          · simp only [hj, ite_false, if_false]
            apply le_of_eq
            apply Finset.sum_eq_zero
            intro l hl
            have hn : ¬ Resonant frequency gap i j k l :=
              fun hr => hj (hcompletion i hi k hk l hl j hr)
            simp [marginal, hn]
        _ = _ := by simp
    _ = _ := by
      rw [Finset.sum_mul_sum]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- When `J ⊆ L`, the independent mass in `L \ J` is a definite event
deficit. This is the exact finite form of the manuscript's calculation. -/
theorem rectangular_event_deficit {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (I K L J : Finset ι) (hJL : J ⊆ L)
    (hcompletion : ∀ i ∈ I, ∀ k ∈ K, ∀ l ∈ L, ∀ j,
      Resonant frequency gap i j k l → j ∈ J) :
    (∑ i ∈ I, x i) * (∑ k ∈ K, x k) * (∑ l ∈ L \ J, x l) ≤
      ∑ q ∈ rectangularEvent I K L,
        (independentMass x q - projectedMass frequency gap x q) := by
  have hp := projected_rectangular_event_le hgap hsep x hx I K L J hcompletion
  have hs : (∑ l ∈ L \ J, x l) = (∑ l ∈ L, x l) - (∑ j ∈ J, x j) :=
    eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hJL)
  rw [Finset.sum_sub_distrib, independent_rectangular_event, hs, mul_sub]
  exact sub_le_sub_left hp _

/-- The source's frequency-threshold event satisfies the preceding completion
condition. Strict inequality on `J` leaves both endpoints of `[e,h]` in `L \ J`. -/
theorem threshold_event_completion {frequency : ι → ℝ} {gap a b e h : ℝ}
    (hgap : 0 < gap) (hab : gap ≤ b - a) (heh : h - e ≤ (b - a) / 2) :
    ∀ i ∈ Finset.univ.filter (fun i => b ≤ frequency i),
      ∀ k ∈ Finset.univ.filter (fun k => frequency k ≤ a),
      ∀ l ∈ Finset.univ.filter (fun l => frequency l ≤ h), ∀ j,
        Resonant frequency gap i j k l →
          j ∈ Finset.univ.filter (fun j => frequency j < e) := by
  intro i hi k hk l hl j hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hk hl ⊢
  exact resonant_event_completion_lt hgap hab heh hr hi hk hl

/-- The exact quantitative constant obtained from two quarter-tail masses
and a half of the central mass. Quantile existence supplies these hypotheses. -/
theorem quantitative_gap_of_event_mass_bounds {frequency : ι → ℝ} {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    (hκ : 0 < κ) (hκ1 : κ < 1) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (I K L J : Finset ι) (hJL : J ⊆ L)
    (hcompletion : ∀ i ∈ I, ∀ k ∈ K, ∀ l ∈ L, ∀ j,
      Resonant frequency gap i j k l → j ∈ J)
    (hI : κ / 4 ≤ ∑ i ∈ I, x i) (hK : κ / 4 ≤ ∑ k ∈ K, x k)
    (hcentral : (1 - κ / 2) / 2 ≤ ∑ l ∈ L \ J, x l) :
    resonanceSum frequency gap x ≤ 1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096 := by
  have hI0 : 0 ≤ ∑ i ∈ I, x i := Finset.sum_nonneg fun i _ => hx i
  have hK0 : 0 ≤ ∑ k ∈ K, x k := Finset.sum_nonneg fun k _ => hx k
  have hIK : (κ / 4) * (κ / 4) ≤ (∑ i ∈ I, x i) * (∑ k ∈ K, x k) :=
    mul_le_mul hI hK (by linarith) hI0
  have hproduct : κ ^ 2 * (1 - κ / 2) / 32 ≤
      (∑ i ∈ I, x i) * (∑ k ∈ K, x k) * (∑ l ∈ L \ J, x l) := by
    calc
      _ = (κ / 4) * (κ / 4) * ((1 - κ / 2) / 2) := by ring
      _ ≤ _ := mul_le_mul hIK hcentral (by linarith) (mul_nonneg hI0 hK0)
  have hdeficit := hproduct.trans
    (rectangular_event_deficit hgap hsep x hx I K L J hJL hcompletion)
  have hg : 0 ≤ κ ^ 2 * (1 - κ / 2) / 32 :=
    div_nonneg (mul_nonneg (sq_nonneg κ) (by linarith)) (by norm_num)
  calc
    resonanceSum frequency gap x ≤ 1 - (κ ^ 2 * (1 - κ / 2) / 32) ^ 2 / 4 :=
      resonanceSum_gap_of_event_deficit hgap hsep x hx hsum
        (rectangularEvent I K L) hg hdeficit
    _ = _ := by ring

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_QuantileGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative fourth-moment gap

The complete combinatorial lemma `phase:quantile-gap` in §7 of
*A uniform Hilbert transform estimate for Lipschitz directions*.
This is a supporting lemma, not the paper's main Hilbert-transform theorem.
-/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*}

theorem separated_injective {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) : Function.Injective frequency := by
  intro i j hij
  by_contra hne
  have hs := hsep hne
  rw [hij, sub_self, abs_zero] at hs
  linarith

/-- The precise strict gap, uniform in the number and positions of frequencies. -/
theorem quantile_gap [Fintype ι] {frequency : ι → ℝ} {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    (hκ : 0 < κ) (hκ1 : κ < 1) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (hatom : ∀ i, x i ≤ 1 - κ) :
    resonanceSum frequency gap x ≤ 1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096 := by
  classical
  obtain ⟨a, b, hab, ha, hb, hc⟩ := frequency_quantiles x frequency hx hsum
    (separated_injective hgap hsep) hκ hκ1 hatom
  have habgap : gap ≤ frequency b - frequency a := by
    have hne : a ≠ b := by intro h; subst b; exact lt_irrefl _ hab
    have hs := hsep hne
    rwa [abs_of_neg (sub_neg.mpr hab), neg_sub] at hs
  obtain ⟨e, h, hae, heh, hhb, hlen, hmass⟩ :=
    exists_heavy_half x frequency hx hab.le hc
  let I := Finset.univ.filter (fun i => frequency b ≤ frequency i)
  let K := Finset.univ.filter (fun i => frequency i ≤ frequency a)
  let L := Finset.univ.filter (fun i => frequency i ≤ h)
  let J := Finset.univ.filter (fun i => frequency i < e)
  have hJL : J ⊆ L := by
    intro i hi
    simp only [J, L, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.le.trans heh
  have hI : κ / 4 ≤ ∑ i ∈ I, x i := by simpa [I, Finset.sum_filter] using hb
  have hK : κ / 4 ≤ ∑ i ∈ K, x i := by simpa [K, Finset.sum_filter] using ha
  have hcentral : (1 - κ / 2) / 2 ≤ ∑ i ∈ L \ J, x i := by
    have hset : L \ J = Finset.univ.filter (fun i => e ≤ frequency i ∧ frequency i ≤ h) := by
      ext i
      simp only [L, J, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hi, hj⟩
        exact ⟨le_of_not_gt hj, hi⟩
      · rintro ⟨hi, hj⟩
        exact ⟨hj, not_lt.mpr hi⟩
    rw [hset, Finset.sum_filter]
    exact hmass
  exact quantitative_gap_of_event_mass_bounds hgap hsep hκ hκ1 x hx hsum
    I K L J hJL (threshold_event_completion hgap habgap hlen.le) hI hK hcentral

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FourthMoment
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fourth moments of separated finite Fourier sums

The exact finite expansion and Fourier-support reduction used in §7,
proof of Proposition `phase:finite-fourier`. The annihilation hypothesis
is a property of the averaging probability measure, not a new axiom.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem character_mul (a b t : ℝ) : character a t * character b t = character (a + b) t := by
  unfold character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem character_conj (a t : ℝ) : conj (character a t) = character (-a) t := by
  unfold character
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem character_four (a b c d t : ℝ) :
    character a t * character b t * conj (character c t) * conj (character d t) =
      character (a + b - c - d) t := by
  rw [character_conj, character_conj, character_mul, character_mul, character_mul]
  congr 1

theorem continuous_character (a : ℝ) : Continuous (character a) := by
  unfold character
  fun_prop

theorem integrable_character (ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ) :
    Integrable (character a) ν :=
  Integrable.of_bound (continuous_character a).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun t => (norm_character a t).le)

theorem sum_four_product (a b c d : ι → ℂ) :
    (∑ q : Quadruple ι, a q.1 * b q.2.1 * c q.2.2.1 * d q.2.2.2) =
      (∑ i, a i) * (∑ j, b j) * (∑ k, c k) * (∑ l, d l) := by
  simp only [Fintype.sum_prod_type]
  have hthree : (∑ i, a i) * (∑ j, b j) * (∑ k, c k) =
      ∑ i, ∑ j, ∑ k, a i * b j * c k := by
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
  symm
  rw [hthree]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem norm_fourth_as_product (z : ℂ) :
    ((‖z‖ ^ 4 : ℝ) : ℂ) = z * z * conj z * conj z := by
  calc
    _ = (z * conj z) ^ 2 := by
      rw [Complex.mul_conj']
      push_cast
      ring
    _ = _ := by ring

theorem fourth_power_sum_expansion (a : ι → ℂ) :
    ((‖∑ i, a i‖ ^ 4 : ℝ) : ℂ) =
      ∑ q : Quadruple ι, a q.1 * a q.2.1 * conj (a q.2.2.1) * conj (a q.2.2.2) := by
  rw [sum_four_product a a (fun i => conj (a i)) (fun i => conj (a i))]
  have hc : (∑ i, conj (a i)) = conj (∑ i, a i) :=
    (map_sum (starRingEnd ℂ) a Finset.univ).symm
  rw [hc]
  exact norm_fourth_as_product _

/-- Exact fourth-power expansion with all cross terms retained. -/
theorem finiteFourierSum_fourth_expansion (frequency : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    ((‖finiteFourierSum frequency a t‖ ^ 4 : ℝ) : ℂ) =
      ∑ q : Quadruple ι, coefficientProduct a q * character (frequencyDifference frequency q) t := by
  rw [finiteFourierSum, fourth_power_sum_expansion]
  apply Finset.sum_congr rfl
  intro q _
  rcases q with ⟨i, j, k, l⟩
  dsimp only [coefficientProduct, frequencyDifference]
  calc
    _ = (a i * a j * conj (a k) * conj (a l)) *
        (character (frequency i) t * character (frequency j) t *
          conj (character (frequency k) t) * conj (character (frequency l) t)) := by
      simp only [map_mul]
      ring
    _ = _ := by rw [character_four]

theorem norm_fourierMoment_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (s : ℝ) :
    ‖fourierMoment ν s‖ ≤ 1 := by
  calc
    ‖fourierMoment ν s‖ ≤ ∫ t, ‖character s t‖ ∂ν := norm_integral_le_integral_norm _
    _ = 1 := by simp [norm_character]

/-- The integral of the finite expansion is the finite sum of Fourier moments. -/
theorem integral_fourth_expansion (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) :
    (∫ t, ((‖finiteFourierSum frequency a t‖ ^ 4 : ℝ) : ℂ) ∂ν) =
      ∑ q : Quadruple ι, coefficientProduct a q * fourierMoment ν (frequencyDifference frequency q) := by
  simp_rw [finiteFourierSum_fourth_expansion]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q _
    exact integral_const_mul _ _
  · intro q _
    exact (integrable_character ν _).const_mul _

theorem fourth_moment_le_resonant_sum (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap : ℝ} (hν : FourierGap ν gap) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      ∑ q : Quadruple ι,
        if Resonant frequency gap q.1 q.2.1 q.2.2.1 q.2.2.2 then
          ‖a q.1‖ * ‖a q.2.1‖ * ‖a q.2.2.1‖ * ‖a q.2.2.2‖ else 0 := by
  classical
  have hexp := integral_fourth_expansion ν frequency a
  have hre : (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) =
      (∑ q : Quadruple ι,
        coefficientProduct a q * fourierMoment ν (frequencyDifference frequency q)).re := by
    rw [integral_complex_ofReal] at hexp
    exact congrArg Complex.re hexp
  rw [hre]
  calc
    _ ≤ ‖∑ q : Quadruple ι,
        coefficientProduct a q * fourierMoment ν (frequencyDifference frequency q)‖ :=
      Complex.re_le_norm _
    _ ≤ ∑ q : Quadruple ι,
        ‖coefficientProduct a q * fourierMoment ν (frequencyDifference frequency q)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q _
      by_cases hr : Resonant frequency gap q.1 q.2.1 q.2.2.1 q.2.2.2
      · simp only [hr, ite_true, if_true, norm_mul, coefficientProduct, Complex.norm_conj]
        exact mul_le_of_le_one_right (by positivity) (norm_fourierMoment_le_one ν _)
      · have hz : fourierMoment ν (frequencyDifference frequency q) = 0 :=
          hν _ (le_of_not_gt hr)
        simp [hr, hz]

/- The exponent conversion that identifies coefficient products with the
probability weights in the quantile argument. -/
omit [Fintype ι] in
theorem norm_product_eq_weight_rpow (a : ι → ℂ) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hnorm : ∀ i, ‖a i‖ = x i ^ (3 / 4 : ℝ))
    (i j k l : ι) :
    ‖a i‖ * ‖a j‖ * ‖a k‖ * ‖a l‖ =
      (x i * x j * x k * x l) ^ (3 / 4 : ℝ) := by
  rw [hnorm i, hnorm j, hnorm k, hnorm l]
  rw [Real.mul_rpow (mul_nonneg (mul_nonneg (hx i) (hx j)) (hx k)) (hx l),
    Real.mul_rpow (mul_nonneg (hx i) (hx j)) (hx k), Real.mul_rpow (hx i) (hx j)]

theorem fourth_moment_le_resonanceSum (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) (x : ι → ℝ) {gap : ℝ}
    (hν : FourierGap ν gap) (hx : ∀ i, 0 ≤ x i)
    (hnorm : ∀ i, ‖a i‖ = x i ^ (3 / 4 : ℝ)) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤ resonanceSum frequency gap x := by
  refine (fourth_moment_le_resonant_sum ν frequency a hν).trans_eq ?_
  apply Finset.sum_congr rfl
  intro q _
  rcases q with ⟨i, j, k, l⟩
  rw [geometricTerm_eq_rpow hx]
  split_ifs
  · exact norm_product_eq_weight_rpow a x hx hnorm i j k l
  · rfl

omit [Fintype ι] in
theorem coefficientMass_nonneg (a : ι → ℂ) (i : ι) : 0 ≤ coefficientMass a i :=
  Real.rpow_nonneg (norm_nonneg _) _

omit [Fintype ι] in
theorem coefficientMass_rpow (a : ι → ℂ) (i : ι) :
    coefficientMass a i ^ (3 / 4 : ℝ) = ‖a i‖ := by
  unfold coefficientMass
  rw [← Real.rpow_mul (norm_nonneg _)]
  norm_num

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceExponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional exponent comparison used in the Fourier gain. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

/-- Raising the finite mean inequality gives the exact fourth-moment cost
of changing the coefficient exponent from `4/3` to `r`. -/
theorem fourth_power_exponent_comparison (a : ι → ℂ) {r : ℝ}
    (hr : 4 / 3 ≤ r) :
    (∑ i, coefficientMass a i) ^ 3 ≤
      (Fintype.card ι : ℝ) ^ (3 - 4 / r) * (∑ i, ‖a i‖ ^ r) ^ (4 / r) := by
  have hr0 : 0 < r := by linarith
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (Finset.univ : Finset ι) (f := coefficientMass a)
    (p := 3 * r / 4) (by linarith) (fun i _ => coefficientMass_nonneg a i)
  have hinner (i : ι) : coefficientMass a i ^ (3 * r / 4) = ‖a i‖ ^ r := by
    rw [coefficientMass, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  simp only [Finset.card_univ, hinner] at h
  have hpow := Real.rpow_le_rpow
    (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => coefficientMass_nonneg a i)) _) h
    (show 0 ≤ 4 / r by positivity)
  rw [← Real.rpow_mul (Finset.sum_nonneg (fun i _ => coefficientMass_nonneg a i)),
    Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)),
    ← Real.rpow_mul (Nat.cast_nonneg _)] at hpow
  have hleft : (3 * r / 4) * (4 / r) = 3 := by field_simp
  have hright : (3 * r / 4 - 1) * (4 / r) = 3 - 4 / r := by field_simp
  simpa only [hleft, hright, Real.rpow_ofNat] using hpow

theorem fourth_power_exponent_comparison_bound (a : ι → ℂ) {r D : ℝ}
    (hr : 4 / 3 ≤ r) (hD : (Fintype.card ι : ℝ) ≤ D) :
    (∑ i, coefficientMass a i) ^ 3 ≤
      D ^ (3 - 4 / r) * (∑ i, ‖a i‖ ^ r) ^ (4 / r) := by
  apply (fourth_power_exponent_comparison a hr).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)) _)
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) hD
  have hr0 : 0 < r := by linarith
  rw [sub_nonneg, div_le_iff₀ hr0]
  linarith

omit [Fintype ι] in
theorem dimension_cost_le_exp {D c : ℝ} (hD : 1 ≤ D) (hc : 0 ≤ c) :
    D ^ (c / Real.log (2 * D)) ≤ Real.exp c := by
  have hD0 : 0 < D := by linarith
  have hlog : 0 < Real.log (2 * D) := Real.log_pos (by linarith)
  have hlogs : Real.log D ≤ Real.log (2 * D) :=
    Real.log_le_log hD0 (by linarith)
  rw [Real.rpow_def_of_pos hD0]
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc, div_le_iff₀ hlog]
  nlinarith [mul_le_mul_of_nonneg_left hlogs hc]

omit [Fintype ι] in
theorem fourth_exponent_parameters {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1 / 3) :
    4 / 3 ≤ 4 / (3 - θ) ∧ 4 / (3 - θ) ≤ 3 / 2 ∧
      3 - 4 / (4 / (3 - θ)) = θ := by
  have hd : 0 < 3 - θ := by linarith
  refine ⟨(le_div_iff₀ hd).2 (by linarith),
    (div_le_iff₀ hd).2 (by linarith), ?_⟩
  field_simp
  ring

theorem fourth_power_exponent_comparison_exp (a : ι → ℂ) {D c θ : ℝ}
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) (hc : 0 ≤ c)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1 / 3) (hdef : θ = c / Real.log (2 * D)) :
    (∑ i, coefficientMass a i) ^ 3 ≤
      Real.exp c * (∑ i, ‖a i‖ ^ (4 / (3 - θ))) ^ (3 - θ) := by
  obtain ⟨hr, _, heq⟩ := fourth_exponent_parameters hθ hθ'
  have h := fourth_power_exponent_comparison_bound a hr hcard
  have hinv : 4 / (4 / (3 - θ)) = 3 - θ := by linarith [heq]
  rw [hinv, sub_sub_cancel] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)) _))
  rw [hdef]
  exact dimension_cost_le_exp hD hc

omit [Fintype ι] in
theorem phaseConstant_pos : 0 < phaseConstant := by norm_num [phaseConstant]

omit [Fintype ι] in
theorem atomThreshold_range : 0 < atomThreshold ∧ atomThreshold < 1 := by
  norm_num [atomThreshold]

omit [Fintype ι] in
theorem phaseConstant_le_gap : phaseConstant ≤ atomThreshold ^ 4 / 16384 := by
  norm_num [phaseConstant, atomThreshold]

omit [Fintype ι] in
theorem phaseParameter_range {D : ℝ} (hD : 1 ≤ D) :
    0 < phaseConstant / Real.log (2 * D) ∧
      phaseConstant / Real.log (2 * D) ≤ 1 / 3 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 * D) := by
    have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h ⊢
      linarith
    exact htwo.trans (Real.log_le_log (by norm_num) (by linarith))
  have hpos : 0 < Real.log (2 * D) := by linarith
  refine ⟨div_pos phaseConstant_pos hpos, (div_le_iff₀ hpos).2 ?_⟩
  have hc : phaseConstant ≤ (1 / 6 : ℝ) := by norm_num [phaseConstant]
  linarith

omit [Fintype ι] in
theorem deficit_absorbs_exponential {δ c : ℝ} (hcδ : c ≤ δ) :
    (1 - δ) * Real.exp c ≤ 1 := by
  calc
    (1 - δ) * Real.exp c ≤ Real.exp (-δ) * Real.exp c := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos c).le
      linarith [Real.add_one_le_exp (-δ)]
    _ = Real.exp (c - δ) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)

omit [Fintype ι] in
theorem phaseConstant_exp_le_two : Real.exp phaseConstant ≤ 2 := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hc : phaseConstant ≤ Real.log 2 := by
    have : phaseConstant ≤ (1 / 2 : ℝ) := by norm_num [phaseConstant]
    linarith
  calc
    Real.exp phaseConstant ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hc
    _ = 2 := Real.exp_log (by norm_num)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotonicity of finite sequence norms and the small-remainder estimate. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem sum_rpow_le_rpow_sum (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {p : ℝ} (hp : 1 ≤ p) : (∑ i, x i ^ p) ≤ (∑ i, x i) ^ p := by
  have hp0 : 0 < p := by linarith
  have h (s : Finset ι) : (∑ i ∈ s, x i ^ p) ≤ (∑ i ∈ s, x i) ^ p := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow hp0.ne']
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc
        x i ^ p + ∑ j ∈ s, x j ^ p ≤ x i ^ p + (∑ j ∈ s, x j) ^ p :=
          add_le_add le_rfl ih
        _ ≤ (x i + ∑ j ∈ s, x j) ^ p :=
          Real.add_rpow_le_rpow_add (hx i) (Finset.sum_nonneg (fun j _ => hx j)) hp
  exact h Finset.univ

theorem sum_powers_exponent_comparison (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i, x i ^ q) ≤ (∑ i, x i ^ p) ^ (q / p) := by
  have h := sum_rpow_le_rpow_sum (fun i => x i ^ p)
    (fun i => Real.rpow_nonneg (hx i) p) ((le_div_iff₀ hp).2 (by simpa using hpq))
  have heq (i : ι) : (x i ^ p) ^ (q / p) = x i ^ q := by
    rw [← Real.rpow_mul (hx i)]
    congr 1
    field_simp
  simpa only [heq] using h

theorem sequenceNorm_nonneg (a : ι → ℂ) (r : ℝ) : 0 ≤ sequenceNorm a r :=
  Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (a i)) _)) _

theorem sequenceNorm_rpow (a : ι → ℂ) (r q : ℝ) :
    sequenceNorm a r ^ q = (∑ i, ‖a i‖ ^ r) ^ (q / r) := by
  unfold sequenceNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg _) _))]
  congr 1
  ring

theorem sequenceNorm_mono (a : ι → ℂ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    sequenceNorm a q ≤ sequenceNorm a p := by
  have hq : 0 < q := hp.trans_le hpq
  have h := Real.rpow_le_rpow (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg (a i)) q))
    (sum_powers_exponent_comparison (fun i => ‖a i‖) (fun i => norm_nonneg _) hp hpq)
    (show 0 ≤ 1 / q by positivity)
  rw [← Real.rpow_mul (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg (a i)) p))] at h
  have heq : q / p * (1 / q) = 1 / p := by field_simp
  simpa only [heq, sequenceNorm] using h

theorem sum_squares_le_sequenceNorm_sq (a : ι → ℂ) {r : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 2) :
    (∑ i, ‖a i‖ ^ 2) ≤ sequenceNorm a r ^ 2 := by
  have h := sum_powers_exponent_comparison (fun i => ‖a i‖)
    (fun i => norm_nonneg _) hr hr2
  simpa only [Real.rpow_ofNat, ← sequenceNorm_rpow a r 2] using h

theorem sequenceNorm_fourth_le_mass_cube (a : ι → ℂ) {r : ℝ} (hr : 4 / 3 ≤ r) :
    sequenceNorm a r ^ 4 ≤ (∑ i, coefficientMass a i) ^ 3 := by
  have h := pow_le_pow_left₀ (sequenceNorm_nonneg a r)
    (sequenceNorm_mono a (by norm_num : (0 : ℝ) < 4 / 3) hr) 4
  have heq : sequenceNorm a (4 / 3) ^ (4 : ℕ) = (∑ i, coefficientMass a i) ^ 3 := by
    rw [← Real.rpow_natCast, sequenceNorm_rpow]
    norm_num [coefficientMass]
  rwa [heq] at h

/-- The exact numerical smallness needed for the dominant coefficient case. -/
theorem sequenceNorm_le_one_div_sixtyfour (a : ι → ℂ) {r : ℝ}
    (hr : 4 / 3 ≤ r) (hsmall : ∑ i, coefficientMass a i ≤ 1 / 1023) :
    sequenceNorm a r ≤ 1 / 64 := by
  have hcube : (∑ i, coefficientMass a i) ^ 3 ≤ (1 / 1023 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => coefficientMass_nonneg a i)) hsmall 3
  have hfourth : sequenceNorm a r ^ 4 ≤ (1 / 64 : ℝ) ^ 4 :=
    (sequenceNorm_fourth_le_mass_cube a hr).trans (hcube.trans (by norm_num))
  exact (pow_le_pow_iff_left₀ (sequenceNorm_nonneg a r) (by norm_num : (0 : ℝ) ≤ 1 / 64)
    (by decide : (4 : ℕ) ≠ 0)).mp hfourth

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DominantCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The dominant-coefficient case of the finite phase estimate

These are the mean-zero fourth-moment and elementary exponent estimates
in §7, proof of Proposition `phase:finite-fourier`. A quadratic Young
inequality absorbs the cubic cross term before integration.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem finiteFourierSum_bound (frequency : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    ‖finiteFourierSum frequency a t‖ ≤ ∑ i, ‖a i‖ := by
  unfold finiteFourierSum
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_mul, norm_character, mul_one]

theorem continuous_finiteFourierSum (frequency : ι → ℝ) (a : ι → ℂ) :
    Continuous (finiteFourierSum frequency a) := by
  unfold finiteFourierSum
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_character _)

theorem integral_finiteFourierSum (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) :
    (∫ t, finiteFourierSum frequency a t ∂ν) =
      ∑ i, a i * fourierMoment ν (frequency i) := by
  unfold finiteFourierSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_const_mul _ _
  · intro i _
    exact (integrable_character ν _).const_mul _

theorem integral_finiteFourierSum_eq_zero (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap : ℝ} (hν : FourierGap ν gap)
    (hzero : ∀ i, gap / 4 ≤ |frequency i|) :
    (∫ t, finiteFourierSum frequency a t ∂ν) = 0 := by
  rw [integral_finiteFourierSum]
  apply Finset.sum_eq_zero
  intro i _
  rw [hν _ (hzero i), mul_zero]

theorem finiteFourierSum_second_expansion (frequency : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    ((‖finiteFourierSum frequency a t‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, (a i * conj (a j)) * character (frequency i - frequency j) t := by
  have hnorm : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    intro z
    rw [Complex.mul_conj']
    push_cast
    rfl
  rw [hnorm, finiteFourierSum, map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, character_conj]
  calc
    _ = (a i * conj (a j)) * (character (frequency i) t * character (-frequency j) t) := by ring
    _ = _ := by rw [character_mul]; rfl

theorem integral_finiteFourierSum_second (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 2 ∂ν) = ∑ i, ‖a i‖ ^ 2 := by
  classical
  have hm (i j : ι) : fourierMoment ν (frequency i - frequency j) =
      if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simp [fourierMoment, character]
    · simp only [hij, ite_false, if_false]
      exact hν _ (le_trans (by linarith) (hsep hij))
  have hexp : (∫ t, ((‖finiteFourierSum frequency a t‖ ^ 2 : ℝ) : ℂ) ∂ν) =
      ∑ i, ∑ j, (a i * conj (a j)) * fourierMoment ν (frequency i - frequency j) := by
    simp_rw [finiteFourierSum_second_expansion]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        exact integral_const_mul _ _
      · intro j _
        exact (integrable_character ν _).const_mul _
    · intro i _
      exact integrable_finsetSum _ fun j _ => (integrable_character ν _).const_mul _
  simp_rw [hm] at hexp
  simp only [mul_ite, mul_one, mul_zero] at hexp
  rw [integral_complex_ofReal] at hexp
  have hre := congrArg Complex.re hexp
  simpa [Complex.mul_conj', ← Complex.ofReal_pow] using hre

omit [Fintype ι] in
theorem one_add_norm_fourth_le (z : ℂ) :
    ‖1 + z‖ ^ 4 ≤ 1 + 4 * z.re + 8 * ‖z‖ ^ 2 + 3 * ‖z‖ ^ 4 := by
  have hs : ‖1 + z‖ ^ 2 = 1 + 2 * z.re + ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add]
    simp [Complex.normSq_eq_norm_sq]
    ring
  have hre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have habs : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [Complex.sq_norm_sub_sq_re z, sq_nonneg z.im]
  have hcross : z.re * ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hre (sq_nonneg ‖z‖)]
  have hyoung : 2 * ‖z‖ ^ 3 ≤ ‖z‖ ^ 2 + ‖z‖ ^ 4 := by
    nlinarith [sq_nonneg (‖z‖ - ‖z‖ ^ 2)]
  have heq : ‖1 + z‖ ^ 4 = (1 + 2 * z.re + ‖z‖ ^ 2) ^ 2 := by
    rw [← hs]
    ring
  rw [heq]
  nlinarith

omit [Fintype ι] in
theorem bounded_norm_power_integrable {ν : Measure ℝ} [IsFiniteMeasure ν]
    {U : ℝ → ℂ} (hU : AEStronglyMeasurable U ν) {B : ℝ}
    (_hB : 0 ≤ B) (hbound : ∀ t, ‖U t‖ ≤ B) (n : ℕ) :
    Integrable (fun t => ‖U t‖ ^ n) ν := by
  apply Integrable.of_bound (hU.norm.pow n) (B ^ n)
  filter_upwards [] with t
  change ‖‖U t‖ ^ n‖ ≤ B ^ n
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) n)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound t) n

omit [Fintype ι] in
theorem bounded_one_add_fourth_integrable {ν : Measure ℝ} [IsFiniteMeasure ν]
    {U : ℝ → ℂ} (hU : AEStronglyMeasurable U ν) {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ t, ‖U t‖ ≤ B) :
    Integrable (fun t => ‖1 + U t‖ ^ 4) ν := by
  apply bounded_norm_power_integrable (aestronglyMeasurable_const.add hU)
    (show 0 ≤ 1 + B by linarith)
  intro t
  calc
    ‖1 + U t‖ ≤ ‖(1 : ℂ)‖ + ‖U t‖ := norm_add_le _ _
    _ ≤ 1 + B := by simpa using add_le_add_left (hbound t) 1

/- The dominant remainder has fourth moment at most `1 + 14 b²`.
The moment assumptions here are the second and fourth moments of the
actual mean-zero remainder, before adding its dominant constant. -/
omit [Fintype ι] in
theorem mean_zero_fourth_moment_le {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {U : ℝ → ℂ} (hU : AEStronglyMeasurable U ν) {B b : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ t, ‖U t‖ ≤ B)
    (hmean : ∫ t, U t ∂ν = 0) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hsecond : ∫ t, ‖U t‖ ^ 2 ∂ν ≤ b ^ 2)
    (hfourth : ∫ t, ‖U t‖ ^ 4 ∂ν ≤ 2 * b ^ 4) :
    (∫ t, ‖1 + U t‖ ^ 4 ∂ν) ≤ 1 + 14 * b ^ 2 := by
  have hiU : Integrable U ν :=
    Integrable.of_bound hU B (Filter.Eventually.of_forall hbound)
  have hi2 := bounded_norm_power_integrable hU hB hbound 2
  have hi4 := bounded_norm_power_integrable hU hB hbound 4
  have hiplus := bounded_one_add_fourth_integrable hU hB hbound
  have hire : Integrable (fun t => (U t).re) ν := hiU.re
  have himean : ∫ t, (U t).re ∂ν = 0 := by
    have heq := integral_re hiU
    change (∫ t, (U t).re ∂ν) = (∫ t, U t ∂ν).re at heq
    rw [heq, hmean]
    rfl
  have hle : (∫ t, ‖1 + U t‖ ^ 4 ∂ν) ≤
      1 + 8 * (∫ t, ‖U t‖ ^ 2 ∂ν) + 3 * (∫ t, ‖U t‖ ^ 4 ∂ν) := by
    calc
      _ ≤ ∫ t, (1 + 4 * (U t).re + 8 * ‖U t‖ ^ 2 + 3 * ‖U t‖ ^ 4) ∂ν :=
        integral_mono hiplus
          (((integrable_const 1).add (hire.const_mul 4)).add (hi2.const_mul 8) |>.add
            (hi4.const_mul 3)) (fun t => one_add_norm_fourth_le (U t))
      _ = _ := by
        rw [integral_add (f := fun t => 1 + 4 * (U t).re + 8 * ‖U t‖ ^ 2)
          (((integrable_const 1).add (hire.const_mul 4)).add (hi2.const_mul 8))
          (hi4.const_mul 3), integral_add (f := fun t => 1 + 4 * (U t).re)
          ((integrable_const 1).add (hire.const_mul 4)) (hi2.const_mul 8),
          integral_add (f := fun _ => 1) (integrable_const 1) (hire.const_mul 4)]
        simp [integral_const_mul, himean]
  have hb4 : b ^ 4 ≤ b ^ 2 := by
    nlinarith [sq_nonneg b, mul_self_le_mul_self hb hb1,
      sq_nonneg (b ^ 2 - 1)]
  nlinarith

/- The numerical comparison in the dominant case, including the
constant-one convexity step. -/
omit [Fintype ι] in
theorem dominant_exponent_bound {b r : ℝ} (hb : 0 ≤ b) (hsmall : b ≤ 1 / 64)
    (hr : 0 < r) (hrupper : r ≤ 3 / 2) :
    1 + 14 * b ^ 2 ≤ (1 + b ^ r) ^ (4 / r) := by
  have hb1 : b ≤ 1 := by linarith
  have hpow : b ^ (2 - r) ≤ 1 / 8 := by
    calc
      b ^ (2 - r) ≤ b ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' hb hb1 (by norm_num) (by linarith)
      _ = Real.sqrt b := (Real.sqrt_eq_rpow b).symm
      _ ≤ 1 / 8 := by
        apply (Real.sqrt_le_iff).2
        constructor <;> nlinarith
  have hfactor : b ^ 2 = b ^ r * b ^ (2 - r) := by
    rw [← Real.rpow_add' hb (by linarith : r + (2 - r) ≠ 0)]
    norm_num
  have hlinear : 14 * b ^ 2 ≤ (8 / 3) * b ^ r := by
    rw [hfactor]
    nlinarith [mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hb r)]
  have hexponent : (8 / 3 : ℝ) ≤ 4 / r := by
    apply (le_div_iff₀ hr).2
    nlinarith
  calc
    1 + 14 * b ^ 2 ≤ 1 + (8 / 3) * b ^ r := by linarith
    _ ≤ 1 + (4 / r) * b ^ r :=
      add_le_add_right (mul_le_mul_of_nonneg_right hexponent (Real.rpow_nonneg hb r)) 1
    _ ≤ _ := one_add_mul_self_le_rpow_one_add
      (by linarith [Real.rpow_nonneg hb r]) (by linarith)

omit [Fintype ι] in
theorem dominant_fourth_moment_bound {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {U : ℝ → ℂ} (hU : AEStronglyMeasurable U ν) {B b r : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ t, ‖U t‖ ≤ B)
    (hmean : ∫ t, U t ∂ν = 0) (hb : 0 ≤ b) (hsmall : b ≤ 1 / 64)
    (hr : 0 < r) (hrupper : r ≤ 3 / 2)
    (hsecond : ∫ t, ‖U t‖ ^ 2 ∂ν ≤ b ^ 2)
    (hfourth : ∫ t, ‖U t‖ ^ 4 ∂ν ≤ 2 * b ^ 4) :
    (∫ t, ‖1 + U t‖ ^ 4 ∂ν) ≤ (1 + b ^ r) ^ (4 / r) :=
  (mean_zero_fourth_moment_le hU hB hbound hmean hb (by linarith) hsecond hfourth).trans
    (dominant_exponent_bound hb hsmall hr hrupper)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_HomogeneousFourthMoment
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Homogeneous fourth-moment bounds

The normalized combinatorial fourth-moment estimate is homogeneous of
degree three in the `ℓ^(4/3)` coefficient masses. These lemmas restore
the arbitrary coefficient normalization used in §7.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem resonanceSum_smul (frequency : ι → ℝ) (gap : ℝ) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) {s : ℝ} (hs : 0 ≤ s) :
    resonanceSum frequency gap (fun i => s * x i) = s ^ 3 * resonanceSum frequency gap x := by
  unfold resonanceSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rcases q with ⟨i, j, k, l⟩
  rw [geometricTerm_eq_rpow (fun i => mul_nonneg hs (hx i)), geometricTerm_eq_rpow hx]
  split_ifs
  · have heq : s * x i * (s * x j) * (s * x k) * (s * x l) =
        s ^ 4 * (x i * x j * x k * x l) := by ring
    rw [heq, Real.mul_rpow (pow_nonneg hs _)
      (mul_nonneg (mul_nonneg (mul_nonneg (hx i) (hx j)) (hx k)) (hx l))]
    congr 1
    rw [← Real.rpow_natCast s 4, ← Real.rpow_mul hs]
    norm_num
  · simp

theorem resonanceSum_le_mass_cube {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    resonanceSum frequency gap x ≤ (∑ i, x i) ^ 3 := by
  let M := ∑ i, x i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => hx i
  by_cases hzero : M = 0
  · have hxzero (i : ι) : x i = 0 := by
      have hi : x i ≤ M := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      exact le_antisymm (hi.trans hzero.le) (hx i)
    have hQ : resonanceSum frequency gap x = 0 := by
      unfold resonanceSum
      apply Finset.sum_eq_zero
      intro q _
      rw [geometricTerm_eq_rpow hx]
      simp [hxzero]
    change resonanceSum frequency gap x ≤ M ^ 3
    rw [hzero, hQ]
    norm_num
  · let y := fun i => x i / M
    have hy : ∀ i, 0 ≤ y i := fun i => div_nonneg (hx i) hM
    have hsum : ∑ i, y i = 1 := by
      dsimp [y]
      rw [← Finset.sum_div, div_self hzero]
    have hscale : (fun i => M * y i) = x := by
      funext i
      dsimp [y]
      field_simp [hzero]
    have hQ := resonanceSum_le_one hgap hsep y hy hsum
    have hhom := resonanceSum_smul frequency gap y hy hM
    rw [hscale] at hhom
    rw [hhom]
    exact mul_le_of_le_one_right (pow_nonneg hM _) hQ

theorem fourth_moment_le_mass_cube (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (∑ i, coefficientMass a i) ^ 3 :=
  (fourth_moment_le_resonanceSum ν frequency a (coefficientMass a) hν
    (coefficientMass_nonneg a) (fun i => (coefficientMass_rpow a i).symm)).trans
    (resonanceSum_le_mass_cube hgap hsep (coefficientMass a) (coefficientMass_nonneg a))

theorem resonanceSum_quantile_gap_mass_cube {frequency : ι → ℝ} {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap)
    (hκ : 0 < κ) (hκ1 : κ < 1) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hatom : ∀ i, x i ≤ (1 - κ) * ∑ j, x j) :
    resonanceSum frequency gap x ≤
      (1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096) * (∑ i, x i) ^ 3 := by
  let M := ∑ i, x i
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => hx i
  by_cases hzero : M = 0
  · have hQ : resonanceSum frequency gap x ≤ M ^ 3 :=
      resonanceSum_le_mass_cube hgap hsep x hx
    change resonanceSum frequency gap x ≤ (1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096) * M ^ 3
    rw [hzero] at hQ ⊢
    simpa using hQ
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    let y := fun i => x i / M
    have hy : ∀ i, 0 ≤ y i := fun i => div_nonneg (hx i) hM
    have hsum : ∑ i, y i = 1 := by
      dsimp [y]
      rw [← Finset.sum_div, div_self hzero]
    have hyatom (i : ι) : y i ≤ 1 - κ := (div_le_iff₀ hMpos).2 (hatom i)
    have hscale : (fun i => M * y i) = x := by
      funext i
      dsimp [y]
      field_simp [hzero]
    have hQ := quantile_gap hgap hsep hκ hκ1 y hy hsum hyatom
    have hhom := resonanceSum_smul frequency gap y hy hM
    rw [hscale] at hhom
    rw [hhom]
    exact (mul_le_mul_of_nonneg_left hQ (pow_nonneg hM _)).trans_eq (mul_comm _ _)

theorem fourth_moment_quantile_gap_mass_cube (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (hatom : ∀ i, coefficientMass a i ≤ (1 - κ) * ∑ j, coefficientMass a j) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (1 - κ ^ 4 * (1 - κ / 2) ^ 2 / 4096) * (∑ i, coefficientMass a i) ^ 3 :=
  (fourth_moment_le_resonanceSum ν frequency a (coefficientMass a) hν
    (coefficientMass_nonneg a) (fun i => (coefficientMass_rpow a i).symm)).trans
    (resonanceSum_quantile_gap_mass_cube hgap hsep hκ hκ1 (coefficientMass a)
      (coefficientMass_nonneg a) hatom)

theorem fourth_moment_quantile_gap_mass_cube_simplified
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap κ : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hκ : 0 < κ) (hκ1 : κ < 1)
    (hatom : ∀ i, coefficientMass a i ≤ (1 - κ) * ∑ j, coefficientMass a j) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (1 - κ ^ 4 / 16384) * (∑ i, coefficientMass a i) ^ 3 := by
  refine (fourth_moment_quantile_gap_mass_cube ν frequency a hgap hsep hν hκ hκ1 hatom).trans ?_
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg
    (Finset.sum_nonneg fun i _ => coefficientMass_nonneg a i) _)
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by linarith : (1 : ℝ) / 2 ≤ 1 - κ / 2) 2
  nlinarith [mul_nonneg (pow_nonneg hκ.le 4) (sub_nonneg.mpr hs)]

/-- Application of the dominant estimate to an actual finite Fourier remainder.
The two coefficient inequalities are supplied by the exponent-comparison step. -/
theorem finiteFourier_dominant_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap b r : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hzero : ∀ i, gap / 4 ≤ |frequency i|)
    (hb : 0 ≤ b) (hsmall : b ≤ 1 / 64) (hr : 0 < r) (hrupper : r ≤ 3 / 2)
    (hsecond : ∑ i, ‖a i‖ ^ 2 ≤ b ^ 2)
    (hfourth : (∑ i, coefficientMass a i) ^ 3 ≤ 2 * b ^ 4) :
    (∫ t, ‖1 + finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (1 + b ^ r) ^ (4 / r) := by
  apply dominant_fourth_moment_bound (continuous_finiteFourierSum frequency a).aestronglyMeasurable
    (Finset.sum_nonneg fun i _ => norm_nonneg (a i)) (finiteFourierSum_bound frequency a)
    (integral_finiteFourierSum_eq_zero ν frequency a hν hzero) hb hsmall hr hrupper
  · rw [integral_finiteFourierSum_second ν frequency a hgap hsep hν]
    exact hsecond
  · exact (fourth_moment_le_mass_cube ν frequency a hgap hsep hν).trans hfourth

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DominantNormalization
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact removal of a dominant Fourier carrier in §7. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι]

theorem remove_carrier_identity (frequency : ι → ℝ) (a : ι → ℂ)
    (i₀ : ι) (h₀ : a i₀ ≠ 0) (t : ℝ) :
    finiteFourierSum frequency a t = a i₀ * character (frequency i₀) t *
      (1 + finiteFourierSum (remainderFrequency frequency i₀) (remainderCoefficient a i₀) t) := by
  classical
  rw [finiteFourierSum, Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  rw [mul_add, mul_one, finiteFourierSum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [remainderFrequency, remainderCoefficient]
  calc
    a i * character (frequency i) t =
        (a i₀ * (a i / a i₀)) *
          (character (frequency i₀) t * character (frequency i - frequency i₀) t) := by
      rw [character_mul]
      have hf : frequency i₀ + (frequency i - frequency i₀) = frequency i := by ring
      rw [hf, mul_div_cancel₀ _ h₀]
    _ = _ := by ring

omit [Fintype ι] in
theorem remainderFrequency_separated {frequency : ι → ℝ} {gap : ℝ}
    (hsep : Separated frequency gap) (i₀ : ι) :
    Separated (remainderFrequency frequency i₀) gap := by
  intro i j hij
  have hval : (i : ι) ≠ j := fun h => hij (Subtype.ext h)
  have h := hsep hval
  simpa only [remainderFrequency, sub_sub_sub_cancel_right] using h

omit [Fintype ι] in
theorem remainderFrequency_away_zero {frequency : ι → ℝ} {gap : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (i₀ : ι)
    (i : RemainderIndex i₀) : gap / 4 ≤ |remainderFrequency frequency i₀ i| :=
  le_trans (by linarith) (hsep i.property)

omit [Fintype ι] in
theorem remainder_coefficientMass (a : ι → ℂ) (i₀ : ι) (i : RemainderIndex i₀) :
    coefficientMass (remainderCoefficient a i₀) i = coefficientMass a i / coefficientMass a i₀ := by
  unfold coefficientMass remainderCoefficient
  rw [norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]

theorem sum_remainder_coefficientMass (a : ι → ℂ) (i₀ : ι) :
    (∑ i : RemainderIndex i₀, coefficientMass (remainderCoefficient a i₀) i) =
      ((∑ i, coefficientMass a i) - coefficientMass a i₀) / coefficientMass a i₀ := by
  classical
  simp_rw [remainder_coefficientMass]
  rw [← Finset.sum_div]
  congr 1
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  ring

theorem sum_norm_remainder_rpow (a : ι → ℂ) (i₀ : ι) (r : ℝ) :
    (∑ i : RemainderIndex i₀, ‖remainderCoefficient a i₀ i‖ ^ r) =
      ((∑ i, ‖a i‖ ^ r) - ‖a i₀‖ ^ r) / ‖a i₀‖ ^ r := by
  classical
  simp_rw [remainderCoefficient, norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [← Finset.sum_div]
  congr 1
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  ring

theorem coefficient_norm_power_decomposition (a : ι → ℂ) (i₀ : ι)
    (h₀ : a i₀ ≠ 0) (r : ℝ) :
    (∑ i, ‖a i‖ ^ r) = ‖a i₀‖ ^ r *
      (1 + ∑ i : RemainderIndex i₀, ‖remainderCoefficient a i₀ i‖ ^ r) := by
  have hm : ‖a i₀‖ ^ r ≠ 0 := (Real.rpow_pos_of_pos (norm_pos_iff.mpr h₀) r).ne'
  rw [sum_norm_remainder_rpow]
  field_simp [hm]
  ring

theorem restore_coefficient_fourth_power (a : ι → ℂ) (i₀ : ι)
    (h₀ : a i₀ ≠ 0) {r : ℝ} (hr : 0 < r) :
    ‖a i₀‖ ^ 4 * (1 + ∑ i : RemainderIndex i₀, ‖remainderCoefficient a i₀ i‖ ^ r) ^ (4 / r) =
      (∑ i, ‖a i‖ ^ r) ^ (4 / r) := by
  rw [coefficient_norm_power_decomposition a i₀ h₀ r,
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) (by positivity),
    ← Real.rpow_mul (norm_nonneg _)]
  have he : r * (4 / r) = 4 := by field_simp
  rw [he]
  norm_num

theorem dominant_coefficient_ne_zero (a : ι → ℂ) (i₀ : ι)
    (hdom : (1 - atomThreshold) * (∑ i, coefficientMass a i) < coefficientMass a i₀) :
    a i₀ ≠ 0 := by
  intro hz
  have hsum : 0 ≤ ∑ i, coefficientMass a i :=
    Finset.sum_nonneg fun i _ => coefficientMass_nonneg a i
  have hpos : 0 ≤ (1 - atomThreshold) * ∑ i, coefficientMass a i :=
    mul_nonneg (by norm_num [atomThreshold]) hsum
  simp [coefficientMass, hz] at hdom
  exact (not_lt_of_ge hpos) hdom

theorem dominant_remainder_mass_le (a : ι → ℂ) (i₀ : ι)
    (hdom : (1 - atomThreshold) * (∑ i, coefficientMass a i) < coefficientMass a i₀) :
    (∑ i : RemainderIndex i₀, coefficientMass (remainderCoefficient a i₀) i) ≤ 1 / 1023 := by
  have h₀ := dominant_coefficient_ne_zero a i₀ hdom
  have hm : 0 < coefficientMass a i₀ :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr h₀) _
  rw [sum_remainder_coefficientMass]
  apply (div_le_iff₀ hm).2
  norm_num [atomThreshold] at hdom
  linarith

theorem remove_carrier_norm (frequency : ι → ℝ) (a : ι → ℂ)
    (i₀ : ι) (h₀ : a i₀ ≠ 0) (t : ℝ) :
    ‖finiteFourierSum frequency a t‖ = ‖a i₀‖ *
      ‖1 + finiteFourierSum (remainderFrequency frequency i₀) (remainderCoefficient a i₀) t‖ := by
  rw [remove_carrier_identity frequency a i₀ h₀ t, norm_mul, norm_mul, norm_character, mul_one]

theorem remove_carrier_fourth_moment (ν : Measure ℝ)
    (frequency : ι → ℝ) (a : ι → ℂ) (i₀ : ι) (h₀ : a i₀ ≠ 0) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) =
      ‖a i₀‖ ^ 4 * ∫ t,
        ‖1 + finiteFourierSum (remainderFrequency frequency i₀) (remainderCoefficient a i₀) t‖ ^ 4 ∂ν := by
  simp_rw [remove_carrier_norm frequency a i₀ h₀, mul_pow]
  exact integral_const_mul _ _

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_ImprovedFourthMoment
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The improved fourth moment: assembly of the quantitative gap and
the dominant-coefficient alternative from §7. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem nondominant_fourth_moment_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hatom : ∀ i, coefficientMass a i ≤
      (1 - atomThreshold) * ∑ j, coefficientMass a j) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (∑ i, ‖a i‖ ^ fourthExponent D) ^ (3 - phaseParameter D) := by
  have hθ := phaseParameter_range hD
  have hmass := fourth_moment_quantile_gap_mass_cube_simplified ν frequency a
    hgap hsep hν atomThreshold_range.1 atomThreshold_range.2 hatom
  have hdim := fourth_power_exponent_comparison_exp a hD hcard phaseConstant_pos.le
    hθ.1.le hθ.2 rfl
  have hδ : 0 ≤ 1 - atomThreshold ^ 4 / 16384 := by norm_num [atomThreshold]
  have hR : 0 ≤ (∑ i, ‖a i‖ ^ fourthExponent D) ^ (3 - phaseParameter D) :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)) _
  calc
    _ ≤ (1 - atomThreshold ^ 4 / 16384) * (∑ i, coefficientMass a i) ^ 3 := hmass
    _ ≤ (1 - atomThreshold ^ 4 / 16384) *
        (Real.exp phaseConstant * (∑ i, ‖a i‖ ^ fourthExponent D) ^
          (3 - phaseParameter D)) := mul_le_mul_of_nonneg_left hdim hδ
    _ = ((1 - atomThreshold ^ 4 / 16384) * Real.exp phaseConstant) *
        (∑ i, ‖a i‖ ^ fourthExponent D) ^ (3 - phaseParameter D) := by ring
    _ ≤ 1 * (∑ i, ‖a i‖ ^ fourthExponent D) ^ (3 - phaseParameter D) :=
      mul_le_mul_of_nonneg_right (deficit_absorbs_exponential phaseConstant_le_gap) hR
    _ = _ := one_mul _

theorem mass_cube_le_two_sequenceNorm_fourth (a : ι → ℂ) {D : ℝ}
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) :
    (∑ i, coefficientMass a i) ^ 3 ≤ 2 * sequenceNorm a (fourthExponent D) ^ 4 := by
  have hθ := phaseParameter_range hD
  obtain ⟨_, _, heq⟩ := fourth_exponent_parameters hθ.1.le hθ.2
  have hinv : 4 / fourthExponent D = 3 - phaseParameter D := by
    dsimp [fourthExponent, phaseParameter]
    linarith [heq]
  have hdim := fourth_power_exponent_comparison_exp a hD hcard phaseConstant_pos.le
    hθ.1.le hθ.2 rfl
  rw [← Real.rpow_natCast (sequenceNorm a (fourthExponent D)) 4,
    sequenceNorm_rpow]
  norm_num only [Nat.cast_ofNat]
  rw [hinv]
  exact hdim.trans (mul_le_mul_of_nonneg_right phaseConstant_exp_le_two
    (Real.rpow_nonneg (Finset.sum_nonneg
      (fun i _ => Real.rpow_nonneg (norm_nonneg (a i)) _)) _))

theorem small_remainder_fourth_moment_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hzero : ∀ i, gap / 4 ≤ |frequency i|)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hsmall : ∑ i, coefficientMass a i ≤ 1 / 1023) :
    (∫ t, ‖1 + finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (1 + ∑ i, ‖a i‖ ^ fourthExponent D) ^ (4 / fourthExponent D) := by
  have hθ := phaseParameter_range hD
  obtain ⟨hr, hrupper, _⟩ := fourth_exponent_parameters hθ.1.le hθ.2
  change 4 / 3 ≤ fourthExponent D at hr
  change fourthExponent D ≤ 3 / 2 at hrupper
  have hr0 : 0 < fourthExponent D := by linarith
  have hbpow : sequenceNorm a (fourthExponent D) ^ fourthExponent D =
      ∑ i, ‖a i‖ ^ fourthExponent D := by
    rw [sequenceNorm_rpow, div_self hr0.ne', Real.rpow_one]
  have h := finiteFourier_dominant_bound ν frequency a hgap hsep hν hzero
    (sequenceNorm_nonneg a _) (sequenceNorm_le_one_div_sixtyfour a hr hsmall)
    hr0 hrupper (sum_squares_le_sequenceNorm_sq a hr0 (by linarith))
    (mass_cube_le_two_sequenceNorm_fourth a hD hcard)
  change _ ≤ (1 + sequenceNorm a (fourthExponent D) ^ fourthExponent D) ^
    (4 / fourthExponent D) at h
  rwa [hbpow] at h

/-- The constant-one fourth-moment estimate with the improved coefficient
exponent, for arbitrary complex coefficients. This is the `p = 4` endpoint
of the manuscript's finite Fourier gain proposition. -/
theorem finite_fourth_moment_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ≤
      (∑ i, ‖a i‖ ^ fourthExponent D) ^ (4 / fourthExponent D) := by
  classical
  by_cases ha : ∀ i, coefficientMass a i ≤
      (1 - atomThreshold) * ∑ j, coefficientMass a j
  · have h := nondominant_fourth_moment_bound ν frequency a hgap hsep hν hD hcard ha
    have hθ := phaseParameter_range hD
    have hp := (fourth_exponent_parameters hθ.1.le hθ.2).2.2
    have heq : 4 / fourthExponent D = 3 - phaseParameter D := by
      dsimp [fourthExponent, phaseParameter]
      linarith [hp]
    rwa [heq]
  · push Not at ha
    obtain ⟨i₀, hi₀⟩ := ha
    have h₀ := dominant_coefficient_ne_zero a i₀ hi₀
    have hcard' : (Fintype.card (RemainderIndex i₀) : ℝ) ≤ D := by
      exact (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcard
    have hrest := small_remainder_fourth_moment_bound ν
      (remainderFrequency frequency i₀) (remainderCoefficient a i₀)
      hgap (remainderFrequency_separated hsep i₀) hν
      (remainderFrequency_away_zero hgap hsep i₀) hD hcard'
      (dominant_remainder_mass_le a i₀ hi₀)
    rw [remove_carrier_fourth_moment ν frequency a i₀ h₀]
    have hθ := phaseParameter_range hD
    have hr := (fourth_exponent_parameters hθ.1.le hθ.2).1
    have hr0 : 0 < fourthExponent D := by
      change 4 / 3 ≤ fourthExponent D at hr
      linarith
    exact (mul_le_mul_of_nonneg_left hrest (pow_nonneg (norm_nonneg _) _)).trans_eq
      (restore_coefficient_fourth_power a i₀ h₀ hr0)

theorem finite_fourier_l4_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ 4 ∂ν) ^ (1 / 4 : ℝ) ≤
      sequenceNorm a (fourthExponent D) := by
  have h := Real.rpow_le_rpow
    (integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _))
    (finite_fourth_moment_gain ν frequency a hgap hsep hν hD hcard)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [← Real.rpow_mul (Finset.sum_nonneg
    (fun i _ => Real.rpow_nonneg (norm_nonneg (a i)) _))] at h
  have heq : 4 / fourthExponent D * (1 / 4) = 1 / fourthExponent D := by ring
  simpa only [heq, sequenceNorm] using h

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoundedDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing the interpolated simple-test pairing estimate to a bounded
canonical dual test. Only finite measures and bounded functions are needed. -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace LipschitzHilbert.PhaseCombinatorics

theorem bounded_test_of_simple_tests (ν : Measure ℝ) [IsFiniteMeasure ν]
    (F : ℝ → ℂ) (hF : Measurable F) {A : ℝ} (hA : 0 ≤ A)
    (hFbound : ∀ x, ‖F x‖ ≤ A) {q : ℝ} (hq : 0 < q)
    (htest : ∀ g : SimpleFunc ℝ ℂ,
      ‖∫ x, F x * g x ∂ν‖ ≤ (∫ x, ‖g x‖ ^ q ∂ν) ^ (1 / q))
    (g : ℝ → ℂ) (hg : Measurable g) {B : ℝ}
    (hgbound : ∀ x, ‖g x‖ ≤ B) :
    ‖∫ x, F x * g x ∂ν‖ ≤ (∫ x, ‖g x‖ ^ q ∂ν) ^ (1 / q) := by
  let gₙ := fun n => SimpleFunc.approxOn g hg Set.univ 0 (Set.mem_univ _) n
  have happrox (x : ℝ) : Tendsto (fun n => gₙ n x) atTop (𝓝 (g x)) :=
    SimpleFunc.tendsto_approxOn hg (Set.mem_univ _) (by simp)
  have hbound (n : ℕ) (x : ℝ) : ‖gₙ n x‖ ≤ 2 * B := by
    have h := SimpleFunc.norm_approxOn_zero_le hg (Set.mem_univ (0 : ℂ)) x n
    exact h.trans (by nlinarith [hgbound x])
  have hpair : Tendsto (fun n => ∫ x, F x * gₙ n x ∂ν) atTop
      (𝓝 (∫ x, F x * g x ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => A * (2 * B))
    · intro n
      exact (hF.mul (gₙ n).measurable).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul (hFbound x) (hbound n x) (norm_nonneg _) hA
    · exact Filter.Eventually.of_forall fun x => tendsto_const_nhds.mul (happrox x)
  have hpower : Tendsto (fun n => ∫ x, ‖gₙ n x‖ ^ q ∂ν) atTop
      (𝓝 (∫ x, ‖g x‖ ^ q ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (2 * B) ^ q)
    · intro n
      exact ((gₙ n).measurable.norm.pow_const q).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hbound n x) hq.le
    · exact Filter.Eventually.of_forall fun x =>
        ((Real.continuous_rpow_const hq.le).tendsto _).comp (happrox x).norm
  have hroot := ((Real.continuous_rpow_const (by positivity : 0 ≤ 1 / q)).tendsto _).comp hpower
  exact le_of_tendsto_of_tendsto' hpair.norm hroot (fun n => htest (gₙ n))

theorem canonicalDual_measurable {F : ℝ → ℂ} (hF : Measurable F) (p : ℝ) :
    Measurable (canonicalDual F p) := by
  exact (Complex.continuous_conj.measurable.comp hF).mul
    ((hF.norm.pow_const (p - 2)).complex_ofReal)

theorem canonicalDual_norm (F : ℝ → ℂ) {p : ℝ} (hp : 1 < p) (x : ℝ) :
    ‖canonicalDual F p x‖ = ‖F x‖ ^ (p - 1) := by
  unfold canonicalDual
  rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  by_cases hx : F x = 0
  · simp [hx, Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
  · calc
      ‖F x‖ * ‖F x‖ ^ (p - 2) = ‖F x‖ ^ (1 : ℝ) * ‖F x‖ ^ (p - 2) := by
        rw [Real.rpow_one]
      _ = ‖F x‖ ^ (p - 1) := by
        rw [← Real.rpow_add (norm_pos_iff.mpr hx)]
        congr 1
        ring

theorem canonicalDual_pairing (F : ℝ → ℂ) {p : ℝ} (hp : 1 < p) (x : ℝ) :
    F x * canonicalDual F p x = (‖F x‖ ^ p : ℝ) := by
  unfold canonicalDual
  rw [← mul_assoc, Complex.mul_conj']
  have hreal : ‖F x‖ ^ 2 * ‖F x‖ ^ (p - 2) = ‖F x‖ ^ p := by
    by_cases hx : F x = 0
    · simp [hx, Real.zero_rpow (show p ≠ 0 by linarith)]
    · rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.mpr hx)]
      congr 1
      push_cast
      ring
  exact_mod_cast hreal

theorem bounded_lp_power_le_one_of_simple_tests (ν : Measure ℝ) [IsFiniteMeasure ν]
    (F : ℝ → ℂ) (hF : Measurable F) {A p : ℝ} (hA : 0 ≤ A)
    (hFbound : ∀ x, ‖F x‖ ≤ A) (hp : 1 < p)
    (htest : ∀ g : SimpleFunc ℝ ℂ,
      ‖∫ x, F x * g x ∂ν‖ ≤
        (∫ x, ‖g x‖ ^ (p / (p - 1)) ∂ν) ^ (1 / (p / (p - 1)))) :
    (∫ x, ‖F x‖ ^ p ∂ν) ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < p - 1 := by linarith
  have hq : 0 < p / (p - 1) := div_pos hp0 hd
  have hg : Measurable (canonicalDual F p) := canonicalDual_measurable hF p
  have hgbound (x : ℝ) : ‖canonicalDual F p x‖ ≤ A ^ (p - 1) := by
    rw [canonicalDual_norm F hp]
    exact Real.rpow_le_rpow (norm_nonneg _) (hFbound x) hd.le
  have h := bounded_test_of_simple_tests ν F hF hA hFbound hq htest
    (canonicalDual F p) hg hgbound
  have hpair : (∫ x, F x * canonicalDual F p x ∂ν) =
      ((∫ x, ‖F x‖ ^ p ∂ν) : ℝ) := by
    simp_rw [canonicalDual_pairing F hp]
    exact integral_complex_ofReal (μ := ν) (f := fun x : ℝ => ‖F x‖ ^ p)
  have hgpow (x : ℝ) : ‖canonicalDual F p x‖ ^ (p / (p - 1)) = ‖F x‖ ^ p := by
    rw [canonicalDual_norm F hp, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    field_simp
  rw [hpair, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))] at h
  simp_rw [hgpow] at h
  by_contra hnot
  have hI : 1 < ∫ x, ‖F x‖ ^ p ∂ν := lt_of_not_ge hnot
  have hexponent : 1 / (p / (p - 1)) < 1 := by
    rw [div_lt_one hq, one_lt_div hd]
    linarith
  exact (not_lt_of_ge h) (Real.rpow_lt_self_of_one_lt hI hexponent)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ExponentialVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variation of exponential weights from variation of their logarithms. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem norm_exp_sub_le_of_re_le (a b : ℂ) (C : ℝ) (ha : a.re ≤ C) (hb : b.re ≤ C) :
    ‖Complex.exp b - Complex.exp a‖ ≤ Real.exp C * ‖b - a‖ := by
  have hconvex : Convex ℝ {z : ℂ | z.re ≤ C} := by
    intro x hx y hy u v hu hv huv
    change (u • x + v • y).re ≤ C
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    change x.re ≤ C at hx
    change y.re ≤ C at hy
    have huC := mul_le_mul_of_nonneg_left hx hu
    have hvC := mul_le_mul_of_nonneg_left hy hv
    have htotal : u * C + v * C = C := by rw [← add_mul, huv, one_mul]
    linarith
  apply hconvex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => Complex.differentiableAt_exp) _ ha hb
  intro z hz
  rw [Complex.deriv_exp, Complex.norm_exp]
  exact Real.exp_le_exp.mpr hz

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FirstArrival
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first member of a set in a size-biased random order has the normalized
weights on that set, regardless of the other elements being ordered. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι : Type*} [DecidableEq ι]

theorem arrivalEvent_cons_of_mem (S : Finset ι) (i j : ι) (hj : j ∈ S) :
    (fun l => arrivalEvent S i (j :: l)) = fun _ => if j = i then 1 else 0 := by
  funext l
  simp [arrivalEvent, firstFrom, hj]

theorem arrivalEvent_cons_of_not_mem (S : Finset ι) (i j : ι) (hj : j ∉ S) :
    (fun l => arrivalEvent S i (j :: l)) = arrivalEvent S i := by
  funext l
  simp [arrivalEvent, firstFrom, hj]

theorem first_step_identity (w : ι → ℝ) (s S : Finset ι) (i : ι)
    (hsub : S ⊆ s) (hi : i ∈ S) (hs : orderMass w s ≠ 0)
    (hS : orderMass w S ≠ 0) :
    (∑ j : s, w j / orderMass w s *
      (if j.val ∈ S then if j.val = i then 1 else 0 else w i / orderMass w S)) =
      w i / orderMass w S := by
  have heq (j : ι) : w j / orderMass w s *
      (if j ∈ S then if j = i then 1 else 0 else w i / orderMass w S) =
      (if j = i then w i / orderMass w s else 0) +
        (if j ∈ S then 0 else w j) / orderMass w s * (w i / orderMass w S) := by
    by_cases hj : j ∈ S
    · by_cases hji : j = i
      · subst j; simp [hi]
      · simp [hj, hji]
    · have hji : j ≠ i := fun h => hj (h ▸ hi)
      simp [hj, hji]
  rw [Finset.sum_coe_sort s (fun j => w j / orderMass w s *
    (if j ∈ S then if j = i then 1 else 0 else w i / orderMass w S))]
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' s i (fun _ => w i / orderMass w s)]
  simp only [hsub hi, ite_true, if_true]
  rw [← Finset.sum_mul, ← Finset.sum_div]
  have hout : (∑ j ∈ s, if j ∈ S then 0 else w j) = orderMass w s - orderMass w S := by
    have hpoint (j : ι) : (if j ∈ S then 0 else w j) = w j - if j ∈ S then w j else 0 := by
      split_ifs <;> ring
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  rw [hout]
  field_simp
  ring

theorem orderAverage_arrivalEvent (w : ι → ℝ) (s S : Finset ι) (i : ι)
    (hw : ∀ j ∈ s, 0 < w j) (hsub : S ⊆ s) (hi : i ∈ S) :
    orderAverage w s (arrivalEvent S i) = w i / orderMass w S := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hs : s.Nonempty := ⟨i, hsub hi⟩
    rw [orderAverage_nonempty w s hs]
    have hrec (j : s) :
        orderAverage w (s.erase j.val) (fun l => arrivalEvent S i (j.val :: l)) =
          if j.val ∈ S then if j.val = i then 1 else 0 else w i / orderMass w S := by
      by_cases hj : j.val ∈ S
      · rw [ite_eq_left hj, arrivalEvent_cons_of_mem S i j hj]
        exact orderAverage_const w (s.erase j.val)
          (fun k hk => hw k (Finset.mem_of_mem_erase hk)) _
      · rw [ite_eq_right hj, arrivalEvent_cons_of_not_mem S i j hj]
        apply ih _ (Finset.erase_ssubset j.property)
          (fun k hk => hw k (Finset.mem_of_mem_erase hk))
        · intro k hk
          exact Finset.mem_erase.mpr ⟨fun h => hj (h ▸ hk), hsub hk⟩
    simp_rw [hrec]
    exact first_step_identity w s S i hsub hi
      (orderMass_pos w s hw hs).ne'
      (orderMass_pos w S (fun j hj => hw j (hsub hj)) ⟨i, hi⟩).ne'

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MixedNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mixed-norm comparisons for the diagonal Hilbert-valued extension. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem finite_minkowski (x : ι → κ → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    {p : ℝ} (hp : 1 ≤ p) :
    (∑ j, (∑ i, x i j) ^ p) ^ (1 / p) ≤
      ∑ i, (∑ j, x i j ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h (s : Finset ι) : (∑ j, (∑ i ∈ s, x i j) ^ p) ^ (1 / p) ≤
      ∑ i ∈ s, (∑ j, x i j ^ p) ^ (1 / p) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have hm := Real.Lp_add_le_of_nonneg (Finset.univ : Finset κ)
        (f := fun j => x i j) (g := fun j => ∑ k ∈ s, x k j) hp
        (fun j _ => hx i j) (fun j _ => Finset.sum_nonneg (fun k _ => hx k j))
      exact hm.trans (add_le_add le_rfl ih)
  exact h Finset.univ

/-- Interchanging the finite `ℓ^r` and `ℓ²` norms costs no constant when `r ≤ 2`. -/
theorem mixed_norm_comparison (x : ι → κ → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    (∑ j, (∑ i, x i j ^ r) ^ (2 / r)) ≤
      (∑ i, (∑ j, x i j ^ 2) ^ (r / 2)) ^ (2 / r) := by
  have hm := finite_minkowski (fun i j => x i j ^ r)
    (fun i j => Real.rpow_nonneg (hx i j) r)
    ((le_div_iff₀ hr).2 (by simpa using hr2))
  have heq (i : ι) (j : κ) : (x i j ^ r) ^ (2 / r) = x i j ^ (2 : ℕ) := by
    rw [← Real.rpow_mul (hx i j)]
    have he : r * (2 / r) = 2 := by field_simp
    rw [he, Real.rpow_ofNat]
  simp only [heq, one_div_div] at hm
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg
    (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg
      (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i j) r)) _)) _) hm
    (show 0 ≤ 2 / r by positivity)
  rw [← Real.rpow_mul (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i j) r)) _))] at hpow
  have hcancel : r / 2 * (2 / r) = 1 := by field_simp
  simpa only [hcancel, Real.rpow_one] using hpow

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntegralMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Minkowski inequality in the integral form needed by the
diagonal Hilbert extension. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

theorem lpNorm_nonnegative_eq (ν : Measure ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) (hpos : ∀ t, 0 ≤ f t) {p : ℝ} (hp : 0 < p) :
    lpNorm f (ENNReal.ofReal p) ν = (∫ t, f t ^ p ∂ν) ^ (1 / p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top
    hf.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  simp only [Real.norm_eq_abs, abs_of_nonneg (hpos _), one_div]

theorem integral_finite_minkowski {κ : Type*} [Fintype κ]
    (ν : Measure ℝ) [IsFiniteMeasure ν] (f : κ → ℝ → ℝ) (B : κ → ℝ)
    (hf : ∀ j, Continuous (f j)) (hpos : ∀ j t, 0 ≤ f j t)
    (hbound : ∀ j t, f j t ≤ B j) {p : ℝ} (hp : 1 ≤ p) :
    (∫ t, (∑ j, f j t) ^ p ∂ν) ^ (1 / p) ≤
      ∑ j, (∫ t, f j t ^ p ∂ν) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hmem (j : κ) : MemLp (f j) (ENNReal.ofReal p) ν := by
    apply MemLp.of_bound (hf j).aestronglyMeasurable (B j)
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos j t)]
      exact hbound j t
  have hp' : 1 ≤ ENNReal.ofReal p := by
    exact ENNReal.one_le_ofReal.mpr hp
  have h := lpNorm_sum_le (s := Finset.univ) (fun j _ => hmem j) hp'
  have hcont : Continuous (fun t => ∑ j, f j t) :=
    continuous_finsetSum _ (fun j _ => hf j)
  have hnonneg (t : ℝ) : 0 ≤ ∑ j, f j t :=
    Finset.sum_nonneg (fun j _ => hpos j t)
  have heq : (∑ j, f j) = (fun t => ∑ j, f j t) := by
    funext t
    exact Finset.sum_apply _ _ _
  rw [heq, lpNorm_nonnegative_eq ν _ hcont hnonneg hp0] at h
  simpa only [lpNorm_nonnegative_eq ν _ (hf _) (hpos _) hp0] using h

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LogEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Logarithmic energy and relative prediction deficits

The exact `p`-Lipschitz estimate for `log (1 + ‖x‖^p)` from §§9–10.
A fixed denominator then cancels from differences of log predictions,
so bounded off-path motion gives a deficit proportional to the path drop.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E]

theorem rpow_predecessor_le_one_add {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    x ^ (p - 1) ≤ 1 + x ^ p := by
  by_cases hx1 : x ≤ 1
  · have hpow := Real.rpow_le_one hx hx1 (sub_nonneg.mpr hp)
    exact hpow.trans (le_add_of_nonneg_right (Real.rpow_nonneg hx _))
  · have hpow := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) (show p - 1 ≤ p by linarith)
    exact hpow.trans (le_add_of_nonneg_left zero_le_one)

theorem hasDerivAt_scalar_logEnergy {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Real.log (1 + y ^ p))
      (p * x ^ (p - 1) / (1 + x ^ p)) x := by
  exact ((Real.hasDerivAt_rpow_const (Or.inr hp)).const_add 1).log
    (ne_of_gt (by positivity))

theorem scalar_logEnergy_derivative_bound {p x : ℝ} (hp : 1 ≤ p) (hx : 0 ≤ x) :
    ‖deriv (fun y : ℝ => Real.log (1 + y ^ p)) x‖ ≤ p := by
  rw [(hasDerivAt_scalar_logEnergy hp hx).deriv, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx _)) (by positivity))]
  apply (div_le_iff₀ (by positivity : 0 < 1 + x ^ p)).2
  exact mul_le_mul_of_nonneg_left (rpow_predecessor_le_one_add hp hx) (by linarith)

theorem scalar_logEnergy_lipschitz {p a b : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.log (1 + a ^ p) - Real.log (1 + b ^ p)| ≤ p * |a - b| := by
  have h := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hasDerivAt_scalar_logEnergy hp hx).differentiableAt)
    (fun x hx => scalar_logEnergy_derivative_bound hp hx) hb ha
  simpa only [Real.norm_eq_abs] using h

/-- The exact global logarithmic-energy Lipschitz estimate, requiring only
that the vectors lie in a normed additive group. -/
theorem logEnergy_lipschitz {p : ℝ} (hp : 1 ≤ p) (x y : E) :
    |logEnergy p x - logEnergy p y| ≤ p * ‖x - y‖ := by
  exact (scalar_logEnergy_lipschitz hp (norm_nonneg x) (norm_nonneg y)).trans
    (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by linarith))

theorem energyRatio_pos {p denominator : ℝ} (hd : 0 < denominator) (x : E) :
    0 < energyRatio p denominator x := div_pos (by positivity) hd

theorem log_energyRatio_sub (p denominator : ℝ) (hd : 0 < denominator) (x y : E) :
    Real.log (energyRatio p denominator x) - Real.log (energyRatio p denominator y) =
      logEnergy p x - logEnergy p y := by
  rw [energyRatio, energyRatio, Real.log_div (by positivity) hd.ne',
    Real.log_div (by positivity) hd.ne']
  unfold logEnergy
  ring

theorem log_energyRatio_lipschitz {p denominator : ℝ} (hp : 1 ≤ p) (hd : 0 < denominator)
    (x y : E) :
    |Real.log (energyRatio p denominator x) - Real.log (energyRatio p denominator y)| ≤
      p * ‖x - y‖ := by
  rw [log_energyRatio_sub p denominator hd]
  exact logEnergy_lipschitz hp x y

/-- A value exceeding one and a bound on numerator motion force a pointwise
lower bound with the same motion factor. The fixed denominator is unrestricted. -/
theorem energyRatio_deficit_of_exceeds_one {p denominator M : ℝ}
    (hp : 1 ≤ p) (hd : 0 < denominator) (hM : 0 ≤ M) (x y : E)
    (hy : 1 < energyRatio p denominator y) (hmotion : ‖x - y‖ ≤ M) :
    max (1 - energyRatio p denominator x) 0 ≤ p * M := by
  have hlogs := log_energyRatio_lipschitz hp hd x y
  have hlogy : 0 < Real.log (energyRatio p denominator y) := Real.log_pos hy
  have hlogx := Real.log_le_sub_one_of_pos (energyRatio_pos hd x (p := p))
  have hmove := mul_le_mul_of_nonneg_left hmotion (show 0 ≤ p by linarith)
  apply max_le
  · have hdiff := (abs_le.mp hlogs).1
    linarith
  · exact mul_nonneg (by linarith) hM

/-- For a fixed path vector, off-path vectors of size at most `B` have diameter
at most `2B`; hence a model prediction exceeding one has deficit at most `2pB`. -/
theorem fixed_path_prediction_deficit {T : Type*} {p denominator B : ℝ}
    (hp : 1 ≤ p) (hd : 0 < denominator) (hB : 0 ≤ B)
    (Y : E) (Z : T → E) (hZ : ∀ t, ‖Z t‖ ≤ B)
    (hexceeds : ∃ t, 1 < energyRatio p denominator (Y + Z t)) (t : T) :
    max (1 - energyRatio p denominator (Y + Z t)) 0 ≤ 2 * p * B := by
  obtain ⟨s, hs⟩ := hexceeds
  have hmotion : ‖(Y + Z t) - (Y + Z s)‖ ≤ 2 * B := by
    rw [add_sub_add_left_eq_sub]
    exact (norm_sub_le _ _).trans (by linarith [hZ t, hZ s])
  have h := energyRatio_deficit_of_exceeds_one hp hd (by linarith : 0 ≤ 2 * B)
    (Y + Z t) (Y + Z s) hs hmotion
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NestedAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Products of nested conditional-average factors

Finite measurable partitions model the nested mesh inside one fixed root cell.
Each factor is constant on the next partition and has average at most one on
every current cell. The product estimate below is an actual integral estimate.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

theorem integrable_finite_profile (μ : Measure α) [IsFiniteMeasure μ]
    (P : α → κ) (hP : ∀ i, MeasurableSet {x | P x = i}) (c : κ → ℝ) :
    Integrable (fun x => c (P x)) μ := by
  classical
  have heq : (fun x => c (P x)) =
      fun x => ∑ i, ({y | P y = i}.indicator (fun _ => c i)) x := by
    funext x
    symm
    rw [Finset.sum_eq_single (P x)]
    · simp
    · intro i _ hi
      exact Set.indicator_of_notMem (show x ∉ {y | P y = i} from fun h => hi h.symm) _
    · simp
  rw [heq]
  exact integrable_finsetSum _ fun i _ => (integrable_const _).indicator (hP i)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_OrderDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite distributions obtained by observing a size-biased random order. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι α : Type*} [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem orderOutcomeWeight_event (w : ι → ℝ) (s : Finset ι)
    (hw : ∀ i ∈ s, 0 < w i) (X : List ι → α) (P : α → Prop) [DecidablePred P] :
    (∑ a, if P a then orderOutcomeWeight w s X a else 0) =
      orderAverage w s (fun l => if P (X l) then 1 else 0) := by
  have hpoint (a : α) : (if P a then orderOutcomeWeight w s X a else 0) =
      orderAverage w s (fun l => if P a then if X l = a then 1 else 0 else 0) := by
    by_cases ha : P a
    · simp only [ha, ite_true, if_true, orderOutcomeWeight]
    · simp only [ha, ite_false, if_false]
      exact (orderAverage_const w s hw 0).symm
  simp_rw [hpoint]
  rw [← orderAverage_sum]
  congr 1
  funext l
  rw [Finset.sum_eq_single (X l)]
  · simp
  · intro a _ ha
    have hxa : X l ≠ a := Ne.symm ha
    simp [hxa]
  · simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierAveragingKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A positive averaging kernel with compact Fourier support

Square the norm of the Fourier transform of a smooth compactly supported
bump. Plancherel converts its Fourier moments into overlaps of translates
of the bump; disjoint supports therefore give exact annihilation.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform ComplexInnerProductSpace

namespace LipschitzHilbert

open PhaseCombinatorics

theorem schwartz_norm_sq_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fun t => ‖h t‖ ^ 2) := by
  have hbound (t : ℝ) : ‖h t‖ ^ 2 ≤ SchwartzMap.seminorm ℝ 0 0 h * ‖h t‖ := by
    nlinarith [mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ h t) (norm_nonneg (h t))]
  exact (h.integrable.norm.const_mul (SchwartzMap.seminorm ℝ 0 0 h)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h t‖)] using hbound t)

theorem fourierSquare_integrable (h : SchwartzMap ℝ ℂ) : Integrable (fourierSquare h) :=
  schwartz_norm_sq_integrable (𝓕 h)

theorem fourierSquare_nonneg (h : SchwartzMap ℝ ℂ) (t : ℝ) : 0 ≤ fourierSquare h t := sq_nonneg _

theorem fourierSquare_continuous (h : SchwartzMap ℝ ℂ) : Continuous (fourierSquare h) := by
  exact (𝓕 h).continuous.norm.pow 2

/-- Translation on the compact-frequency side becomes a unit phase. -/
theorem schwartz_fourier_translate (h : SchwartzMap ℝ ℂ) (a x : ℝ) :
    𝓕 (h.compSubConstCLM ℂ (-a)) x = character (2 * Real.pi * a) x * 𝓕 h x := by
  have ht := congrFun (Fourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure ℝ) (h : ℝ → ℂ) a) x
  have hphase : (Real.fourierChar (a * x) : ℂ) = character (2 * Real.pi * a) x := by
    simp only [Real.fourierChar_apply, character]
    congr 1
    push_cast
    ring
  simpa only [SchwartzMap.fourier_coe, Real.fourier_real_eq,
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, Function.comp_apply,
    Fourier.fourierIntegral_def, Circle.smul_def, smul_eq_mul, hphase] using ht

/-- The Fourier moment of the square is an overlap integral of the bump and
its translate. This is the exact support calculation needed for averaging. -/
theorem fourierSquare_moment (h : SchwartzMap ℝ ℂ) (a : ℝ) :
    (∫ t, (fourierSquare h t : ℂ) * character (2 * Real.pi * a) t) =
      ∫ x, inner ℂ (h x) (h (x + a)) := by
  have hplan := SchwartzMap.integral_inner_fourier_fourier h (h.compSubConstCLM ℂ (-a))
  have hpoint (t : ℝ) :
      inner ℂ (𝓕 h t) (𝓕 (h.compSubConstCLM ℂ (-a)) t) =
        (fourierSquare h t : ℂ) * character (2 * Real.pi * a) t := by
    rw [schwartz_fourier_translate]
    change inner ℂ (𝓕 h t) (character (2 * Real.pi * a) t • 𝓕 h t) = _
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    unfold fourierSquare
    push_cast
    exact mul_comm _ _
  simpa only [hpoint, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add] using hplan

/-- A bump supported in `(-r,r)` produces no moment at translation distances
at least `2r`, including the support endpoints. -/
theorem fourierSquare_moment_eq_zero (h : SchwartzMap ℝ ℂ) {r a : ℝ}
    (hsupport : ∀ x, r ≤ |x| → h x = 0) (ha : 2 * r ≤ |a|) :
    (∫ t, (fourierSquare h t : ℂ) * character (2 * Real.pi * a) t) = 0 := by
  rw [fourierSquare_moment]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  change inner ℂ (h x) (h (x + a)) = 0
  by_cases hx : r ≤ |x|
  · rw [hsupport x hx, inner_zero_left]
  · have hxa : r ≤ |x + a| := by
      have htri : |a| ≤ |x + a| + |x| := by
        have h := abs_sub (x + a) x
        simpa only [add_sub_cancel_left] using h
      linarith [lt_of_not_ge hx]
    rw [hsupport (x + a) hxa, inner_zero_right]

/-- The total mass is positive whenever the original bump is nonzero at one
point, and agrees with its squared L2 norm by Plancherel. -/
theorem fourierSquare_mass_pos (h : SchwartzMap ℝ ℂ) {x : ℝ} (hx : h x ≠ 0) :
    0 < ∫ t, fourierSquare h t := by
  change 0 < ∫ t, ‖𝓕 h t‖ ^ 2
  rw [SchwartzMap.integral_norm_sq_fourier]
  exact integral_pos_of_integrable_nonneg_nonzero (h.continuous.norm.pow 2)
    (schwartz_norm_sq_integrable h) (fun _ => sq_nonneg _)
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierAveragingMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# An actual Fourier-supported averaging probability

Normalize the positive Fourier-square kernel and instantiate its compact
frequency bump. This constructs a probability satisfying `FourierGap` for
every positive gap, rather than assuming existence of an averaging law.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

open PhaseCombinatorics

theorem fourierAveragingDensity_nonneg (h : SchwartzMap ℝ ℂ) (t : ℝ) :
    0 ≤ fourierAveragingDensity h t :=
  div_nonneg (fourierSquare_nonneg h t) (integral_nonneg (fourierSquare_nonneg h))

theorem fourierAveragingDensity_continuous (h : SchwartzMap ℝ ℂ) :
    Continuous (fourierAveragingDensity h) := (fourierSquare_continuous h).div_const _

theorem fourierAveragingDensity_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fourierAveragingDensity h) := (fourierSquare_integrable h).div_const _

theorem fourierAveragingDensity_integral (h : SchwartzMap ℝ ℂ) {x : ℝ} (hx : h x ≠ 0) :
    (∫ t, fourierAveragingDensity h t) = 1 := by
  unfold fourierAveragingDensity
  rw [integral_div, div_self (fourierSquare_mass_pos h hx).ne']

theorem fourierAveragingMeasure_isProbability (h : SchwartzMap ℝ ℂ) {x : ℝ} (hx : h x ≠ 0) :
    IsProbabilityMeasure (fourierAveragingMeasure h) := by
  constructor
  unfold fourierAveragingMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (fourierAveragingDensity_integrable h)
      (Filter.Eventually.of_forall (fourierAveragingDensity_nonneg h)),
    fourierAveragingDensity_integral h hx, ENNReal.ofReal_one]

/-- Fourier moments of the probability are the normalized kernel moments. -/
theorem fourierAveragingMeasure_moment (h : SchwartzMap ℝ ℂ) (s : ℝ) :
    fourierMoment (fourierAveragingMeasure h) s =
      ((∫ x, fourierSquare h x : ℝ) : ℂ)⁻¹ *
        ∫ t, (fourierSquare h t : ℂ) * character s t := by
  unfold fourierMoment fourierAveragingMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    ((fourierAveragingDensity_continuous h).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (fourierAveragingDensity_nonneg h _)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [fourierAveragingDensity, Complex.real_smul, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- A bump of radius `r` gives a probability with the required Fourier gap
whenever `16πr ≤ gap`. -/
theorem fourierAveragingMeasure_fourierGap (h : SchwartzMap ℝ ℂ) {r gap : ℝ}
    (hsupport : ∀ x, r ≤ |x| → h x = 0) (hband : 16 * Real.pi * r ≤ gap) :
    FourierGap (fourierAveragingMeasure h) gap := by
  intro s hs
  let a := s / (2 * Real.pi)
  have hpi : 0 < 2 * Real.pi := by positivity
  have ha : 2 * r ≤ |a| := by
    dsimp only [a]
    rw [abs_div, abs_of_pos hpi]
    apply (le_div_iff₀ hpi).2
    nlinarith
  have heq : 2 * Real.pi * a = s := by dsimp only [a]; field_simp
  rw [fourierAveragingMeasure_moment, ← heq,
    fourierSquare_moment_eq_zero h hsupport ha, mul_zero]

/-- A genuine compactly supported smooth bump for the kernel construction. -/
theorem exists_compact_frequency_bump {r : ℝ} (hr : 0 < r) :
    ∃ h : SchwartzMap ℝ ℂ, h 0 ≠ 0 ∧ ∀ x, r ≤ |x| → h x = 0 := by
  have hnhds : Set.Ioo (-r) r ∈ nhds (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, hr⟩
  obtain ⟨f, hsupp, hcompact, hsmooth, _, hzero⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hnhds
  let h : SchwartzMap ℝ ℂ :=
    (hcompact.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hsmooth)
  refine ⟨h, ?_, ?_⟩
  · change (f 0 : ℂ) ≠ 0
    rw [hzero]
    norm_num
  · intro x hx
    have hf : f x = 0 := by
      by_contra hfx
      have hmem : x ∈ tsupport f := subset_closure (show x ∈ Function.support f from hfx)
      have hlt : |x| < r := abs_lt.mpr (hsupp hmem)
      exact not_lt_of_ge hx hlt
    change (f x : ℂ) = 0
    rw [hf, Complex.ofReal_zero]

/-- Every positive gap admits an explicitly constructed averaging probability
with smooth nonnegative density and exactly vanishing outside moments. -/
theorem exists_fourierAveragingMeasure {gap : ℝ} (hgap : 0 < gap) :
    ∃ h : SchwartzMap ℝ ℂ, h 0 ≠ 0 ∧
      IsProbabilityMeasure (fourierAveragingMeasure h) ∧
      FourierGap (fourierAveragingMeasure h) gap := by
  let r := gap / (16 * Real.pi)
  have hr : 0 < r := div_pos hgap (by positivity)
  obtain ⟨h, hh, hsupport⟩ := exists_compact_frequency_bump hr
  refine ⟨h, hh, fourierAveragingMeasure_isProbability h hh,
    fourierAveragingMeasure_fourierGap h hsupport ?_⟩
  dsimp only [r]
  have hpi : 16 * Real.pi ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hpi]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierHomogeneity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring arbitrary coefficients after a unit sequence-norm estimate. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem sequenceNorm_pos_of_nonzero (a : ι → ℂ) (r : ℝ)
    (ha : ∃ i, a i ≠ 0) : 0 < sequenceNorm a r := by
  obtain ⟨i, hi⟩ := ha
  have hsum : 0 < ∑ i, ‖a i‖ ^ r :=
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hi) r).trans_le
      (Finset.single_le_sum (fun j _ => Real.rpow_nonneg (norm_nonneg (a j)) r)
        (Finset.mem_univ i))
  exact Real.rpow_pos_of_pos hsum (1 / r)

theorem normalizedCoefficient_unit (a : ι → ℂ) {r : ℝ} (hr : 0 < r)
    (ha : ∃ i, a i ≠ 0) :
    ∑ i, ‖normalizedCoefficient a r i‖ ^ r = 1 := by
  have hn := sequenceNorm_pos_of_nonzero a r ha
  have hp : sequenceNorm a r ^ r = ∑ i, ‖a i‖ ^ r := by
    rw [sequenceNorm_rpow, div_self hr.ne', Real.rpow_one]
  have hnorm : ‖(sequenceNorm a r : ℂ)‖ = sequenceNorm a r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  simp_rw [normalizedCoefficient, norm_div, hnorm,
    Real.div_rpow (norm_nonneg _) hn.le]
  rw [← Finset.sum_div, ← hp, div_self (Real.rpow_pos_of_pos hn r).ne']

theorem finiteFourierSum_normalized (frequency : ι → ℝ) (a : ι → ℂ) (r t : ℝ) :
    finiteFourierSum frequency (normalizedCoefficient a r) t =
      finiteFourierSum frequency a t / (sequenceNorm a r : ℂ) := by
  unfold finiteFourierSum normalizedCoefficient
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem restore_normalized_fourier_norm (frequency : ι → ℝ) (a : ι → ℂ)
    (r : ℝ) (ha : ∃ i, a i ≠ 0) (t : ℝ) :
    ‖finiteFourierSum frequency a t‖ = sequenceNorm a r *
      ‖finiteFourierSum frequency (normalizedCoefficient a r) t‖ := by
  have hn := sequenceNorm_pos_of_nonzero a r ha
  rw [finiteFourierSum_normalized, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hn]
  field_simp

theorem homogeneous_fourier_power_bound (ν : Measure ℝ) (frequency : ι → ℝ)
    {r p : ℝ} (hr : 0 < r) (hp : 0 < p)
    (hunit : ∀ a : ι → ℂ, (∑ i, ‖a i‖ ^ r) = 1 →
      (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ≤ 1) (a : ι → ℂ) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ≤ sequenceNorm a r ^ p := by
  classical
  by_cases ha : ∃ i, a i ≠ 0
  · have hn := sequenceNorm_pos_of_nonzero a r ha
    have h := hunit (normalizedCoefficient a r) (normalizedCoefficient_unit a hr ha)
    have heq : (fun t => ‖finiteFourierSum frequency a t‖ ^ p) =
        (fun t => sequenceNorm a r ^ p *
          ‖finiteFourierSum frequency (normalizedCoefficient a r) t‖ ^ p) := by
      funext t
      rw [restore_normalized_fourier_norm frequency a r ha t,
        Real.mul_rpow hn.le (norm_nonneg _)]
    rw [heq, integral_const_mul]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hn.le p) h
  · have hz : a = 0 := by
      funext i
      exact not_ne_iff.mp (fun hi => ha ⟨i, hi⟩)
    subst a
    simp [finiteFourierSum, sequenceNorm, Real.zero_rpow hp.ne', Real.zero_rpow hr.ne',
      Real.zero_rpow (inv_ne_zero hr.ne')]

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_InterpolationFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Analytic families for the finite Fourier interpolation

The magnitude interpolation in §7 keeps each complex phase fixed. Zero
coefficients remain zero. The identities below give exact unit boundary
norms for the coefficient and simple-test-function families.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

theorem norm_magnitudeFamily_of_ne_zero {w : ℂ} (hw : w ≠ 0) (A B : ℝ) (z : ℂ) :
    ‖magnitudeFamily w A B z‖ = ‖w‖ ^ ((1 - z.re) * A + z.re * B) := by
  have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hphase : ‖w / (‖w‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hnorm]
  simp only [magnitudeFamily, hw, ite_false, if_false]
  rw [norm_mul, hphase, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hw)]
  congr 1
  simp [Complex.mul_re]

theorem norm_magnitudeFamily_left (w : ℂ) {A : ℝ} (hA : 0 < A) (B : ℝ)
    {z : ℂ} (hz : z.re = 0) : ‖magnitudeFamily w A B z‖ = ‖w‖ ^ A := by
  by_cases hw : w = 0
  · simp [hw, Real.zero_rpow hA.ne']
  · rw [norm_magnitudeFamily_of_ne_zero hw]
    simp [hz]

theorem norm_magnitudeFamily_right (w : ℂ) (A : ℝ) {B : ℝ} (hB : 0 < B)
    {z : ℂ} (hz : z.re = 1) : ‖magnitudeFamily w A B z‖ = ‖w‖ ^ B := by
  by_cases hw : w = 0
  · simp [hw, Real.zero_rpow hB.ne']
  · rw [norm_magnitudeFamily_of_ne_zero hw]
    simp [hz]

theorem magnitudeFamily_at_real (w : ℂ) (A B t : ℝ)
    (ht : (1 - t) * A + t * B = 1) : magnitudeFamily w A B (t : ℂ) = w := by
  by_cases hw : w = 0
  · simp [hw]
  · have he : (1 - (t : ℂ)) * (A : ℂ) + (t : ℂ) * (B : ℂ) = 1 := by
      exact_mod_cast ht
    simp only [magnitudeFamily, hw, ite_false, if_false]
    rw [he, Complex.cpow_one]
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))

theorem differentiable_magnitudeFamily (w : ℂ) (A B : ℝ) :
    Differentiable ℂ (magnitudeFamily w A B) := by
  by_cases hw : w = 0
  · change Differentiable ℂ (fun z => magnitudeFamily w A B z)
    simp only [hw, magnitudeFamily_zero]
    exact differentiable_const (0 : ℂ)
  · have hf : Differentiable ℂ (fun z : ℂ => (1 - z) * (A : ℂ) + z * (B : ℂ)) := by
      fun_prop
    have hn : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
    change Differentiable ℂ (fun z => magnitudeFamily w A B z)
    simp only [magnitudeFamily, hw, ite_false, if_false]
    exact (differentiable_const (w / (‖w‖ : ℂ))).mul (hf.const_cpow (Or.inl hn))

theorem norm_magnitudeFamily_le (w : ℂ) (A B : ℝ) {z : ℂ}
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖magnitudeFamily w A B z‖ ≤ ‖w‖ ^ min A B + ‖w‖ ^ max A B := by
  by_cases hw : w = 0
  · rw [hw, magnitudeFamily_zero, norm_zero]
    positivity
  · rw [norm_magnitudeFamily_of_ne_zero hw]
    have hlo : min A B ≤ (1 - z.re) * A + z.re * B := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (min_le_left A B)) (sub_nonneg.mpr hz1),
        mul_nonneg (sub_nonneg.mpr (min_le_right A B)) hz0]
    have hhi : (1 - z.re) * A + z.re * B ≤ max A B := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_left A B)) (sub_nonneg.mpr hz1),
        mul_nonneg (sub_nonneg.mpr (le_max_right A B)) hz0]
    by_cases hnorm : 1 ≤ ‖w‖
    · exact (Real.rpow_le_rpow_of_exponent_le hnorm hhi).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hw)
        (le_of_not_ge hnorm) hlo).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem coefficientFamily_at_real (a : ι → ℂ) (r p₀ p₁ t : ℝ)
    (ht : (1 - t) * (r / p₀) + t * (r / p₁) = 1) :
    coefficientFamily a r p₀ p₁ (t : ℂ) = a := by
  funext i
  exact magnitudeFamily_at_real (a i) _ _ t ht

theorem coefficientFamily_left_power_sum (a : ι → ℂ) {r p₀ p₁ : ℝ}
    (hr : 0 < r) (hp₀ : 0 < p₀) {z : ℂ} (hz : z.re = 0) :
    (∑ i, ‖coefficientFamily a r p₀ p₁ z i‖ ^ p₀) = ∑ i, ‖a i‖ ^ r := by
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientFamily, norm_magnitudeFamily_left (a i) (div_pos hr hp₀) _ hz,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  field_simp

theorem coefficientFamily_right_power_sum (a : ι → ℂ) {r p₀ p₁ : ℝ}
    (hr : 0 < r) (hp₁ : 0 < p₁) {z : ℂ} (hz : z.re = 1) :
    (∑ i, ‖coefficientFamily a r p₀ p₁ z i‖ ^ p₁) = ∑ i, ‖a i‖ ^ r := by
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientFamily, norm_magnitudeFamily_right (a i) _ (div_pos hr hp₁) hz,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  field_simp

theorem weighted_magnitudeFamily_left_power_sum (w : ι → ℝ) (a : ι → ℂ) {r p₀ p₁ : ℝ}
    (hr : 0 < r) (hp₀ : 0 < p₀) {z : ℂ} (hz : z.re = 0) :
    (∑ i, w i * ‖coefficientFamily a r p₀ p₁ z i‖ ^ p₀) = ∑ i, w i * ‖a i‖ ^ r := by
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientFamily, norm_magnitudeFamily_left (a i) (div_pos hr hp₀) _ hz,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 2
  field_simp

theorem weighted_magnitudeFamily_right_power_sum (w : ι → ℝ) (a : ι → ℂ) {r p₀ p₁ : ℝ}
    (hr : 0 < r) (hp₁ : 0 < p₁) {z : ℂ} (hz : z.re = 1) :
    (∑ i, w i * ‖coefficientFamily a r p₀ p₁ z i‖ ^ p₁) = ∑ i, w i * ‖a i‖ ^ r := by
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficientFamily, norm_magnitudeFamily_right (a i) _ (div_pos hr hp₁) hz,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 2
  field_simp

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FiniteInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite bilinear interpolation with constant one

This is the finite simple-function step of §7. The analytic family is
constructed explicitly, and Hadamard's theorem proves the interpolated
pairing estimate from its two endpoint estimates.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem norm_finitePairing_le (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ)
    (w : κ → ℝ) (hK : ∀ i j, ‖K i j‖ ≤ w j) :
    ‖finitePairing K a b‖ ≤ (∑ i, ‖a i‖) * (∑ j, w j * ‖b j‖) := by
  unfold finitePairing
  calc
    _ ≤ ∑ i, ∑ j, ‖K i j * a i * b j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, ‖a i‖ * (w j * ‖b j‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul]
      nlinarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hK i j) (norm_nonneg (a i))) (norm_nonneg (b j))]
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem differentiable_pairingFamily (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ)
    (r s r₄ : ℝ) : Differentiable ℂ (pairingFamily K a b r s r₄) := by
  unfold pairingFamily finitePairing coefficientFamily
  apply Differentiable.fun_sum
  intro i _
  apply Differentiable.fun_sum
  intro j _
  exact ((differentiable_const (K i j)).mul
    (differentiable_magnitudeFamily (a i) _ _)).mul
    (differentiable_magnitudeFamily (b j) _ _)

theorem pairingFamily_bddAbove (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ)
    (r s r₄ : ℝ) : BddAbove ((norm ∘ pairingFamily K a b r s r₄) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  refine ⟨∑ i, ∑ j, ‖K i j‖ *
    (‖a i‖ ^ min (r / 1) (r / r₄) + ‖a i‖ ^ max (r / 1) (r / r₄)) *
    (‖b j‖ ^ min (s / 1) (s / (4 / 3)) + ‖b j‖ ^ max (s / 1) (s / (4 / 3))), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  change 0 ≤ z.re ∧ z.re ≤ 1 at hz
  simp only [Function.comp_apply]
  unfold pairingFamily finitePairing
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => norm_sum_le _ _).trans ?_)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simp only [norm_mul, coefficientFamily]
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (norm_magnitudeFamily_le (a i) _ _ hz.1 hz.2)
      (norm_nonneg _)
  · exact norm_magnitudeFamily_le (b j) _ _ hz.1 hz.2
  · exact norm_nonneg _
  · positivity

/-- The exact normalized finite pairing estimate supplied by the
coefficient and simple-test-function interpolation families. -/
theorem finite_pairing_interpolation (K : ι → κ → ℂ) (w : κ → ℝ)
    (hK : ∀ i j, ‖K i j‖ ≤ w j)
    {r s r₄ t : ℝ} (hr : 0 < r) (hs : 0 < s) (hr₄ : 0 < r₄)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrdef : (1 - t) * (r / 1) + t * (r / r₄) = 1)
    (hsdef : (1 - t) * (s / 1) + t * (s / (4 / 3)) = 1)
    (hfour : ∀ (a : ι → ℂ) (b : κ → ℂ),
      (∑ i, ‖a i‖ ^ r₄) = 1 → (∑ j, w j * ‖b j‖ ^ (4 / 3 : ℝ)) = 1 →
      ‖finitePairing K a b‖ ≤ 1)
    (a : ι → ℂ) (b : κ → ℂ)
    (ha : (∑ i, ‖a i‖ ^ r) = 1) (hb : (∑ j, w j * ‖b j‖ ^ s) = 1) :
    ‖finitePairing K a b‖ ≤ 1 := by
  let F := pairingFamily K a b r s r₄
  have hleft : ∀ z ∈ Complex.re ⁻¹' {0}, ‖F z‖ ≤ 1 := by
    intro z hz
    have hz' : z.re = 0 := hz
    have hA : (∑ i, ‖coefficientFamily a r 1 r₄ z i‖) = 1 := by
      simpa only [Real.rpow_one, ha] using
        (coefficientFamily_left_power_sum a hr (by norm_num : (0 : ℝ) < 1) hz')
    have hB : (∑ j, w j * ‖coefficientFamily b s 1 (4 / 3) z j‖) = 1 := by
      simpa only [Real.rpow_one, hb] using
        (weighted_magnitudeFamily_left_power_sum w b hs (by norm_num : (0 : ℝ) < 1) hz')
    exact (norm_finitePairing_le K _ _ w hK).trans_eq (by rw [hA, hB, mul_one])
  have hright : ∀ z ∈ Complex.re ⁻¹' {1}, ‖F z‖ ≤ 1 := by
    intro z hz
    have hz' : z.re = 1 := hz
    apply hfour
    · exact (coefficientFamily_right_power_sum a hr hr₄ hz').trans ha
    · exact (weighted_magnitudeFamily_right_power_sum w b hs (by norm_num) hz').trans hb
  have hz : (t : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := ⟨ht0, ht1⟩
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    F hz (differentiable_pairingFamily K a b r s r₄).diffContOnCl
    (pairingFamily_bddAbove K a b r s r₄) hleft hright
  have htarget : F (t : ℂ) = finitePairing K a b := by
    dsimp [F, pairingFamily]
    rw [coefficientFamily_at_real a r 1 r₄ t hrdef,
      coefficientFamily_at_real b s 1 (4 / 3) t hsdef]
  simpa only [htarget, Real.one_rpow, one_mul] using h

theorem finitePairing_div_right (K : ι → κ → ℂ) (a : ι → ℂ) (b : κ → ℂ) (c : ℂ) :
    finitePairing K a (fun j => b j / c) = finitePairing K a b / c := by
  unfold finitePairing
  simp only [← mul_div_assoc, ← Finset.sum_div]

/-- Scaling removes the unit-norm restriction on the simple test.
The coefficient sequence remains normalized. -/
theorem finite_pairing_interpolation_test (K : ι → κ → ℂ) (w : κ → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hK : ∀ i j, ‖K i j‖ ≤ w j)
    {r s r₄ t : ℝ} (hr : 0 < r) (hs : 0 < s) (hr₄ : 0 < r₄)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrdef : (1 - t) * (r / 1) + t * (r / r₄) = 1)
    (hsdef : (1 - t) * (s / 1) + t * (s / (4 / 3)) = 1)
    (hfour : ∀ (a : ι → ℂ) (b : κ → ℂ),
      (∑ i, ‖a i‖ ^ r₄) = 1 → (∑ j, w j * ‖b j‖ ^ (4 / 3 : ℝ)) = 1 →
      ‖finitePairing K a b‖ ≤ 1)
    (a : ι → ℂ) (b : κ → ℂ) (ha : (∑ i, ‖a i‖ ^ r) = 1) :
    ‖finitePairing K a b‖ ≤ (∑ j, w j * ‖b j‖ ^ s) ^ (1 / s) := by
  let S := ∑ j, w j * ‖b j‖ ^ s
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hzero : S = 0
  · have hterm (j : κ) : w j * ‖b j‖ ^ s = 0 := by
      have hle : w j * ‖b j‖ ^ s ≤ S :=
        Finset.single_le_sum (fun k _ => mul_nonneg (hw k) (Real.rpow_nonneg (norm_nonneg _) _))
          (Finset.mem_univ j)
      exact le_antisymm (hle.trans hzero.le) (mul_nonneg (hw j) (Real.rpow_nonneg (norm_nonneg _) _))
    have hlinear (j : κ) : w j * ‖b j‖ = 0 := by
      by_cases hb : b j = 0
      · simp [hb]
      · have hpos : 0 < ‖b j‖ ^ s := Real.rpow_pos_of_pos (norm_pos_iff.mpr hb) _
        have hwzero : w j = 0 := (mul_eq_zero.mp (hterm j)).resolve_right hpos.ne'
        simp [hwzero]
    have hle := norm_finitePairing_le K a b w hK
    simp only [hlinear, Finset.sum_const_zero, mul_zero] at hle
    change ‖finitePairing K a b‖ ≤ S ^ (1 / s)
    rw [hzero, Real.zero_rpow (one_div_ne_zero hs.ne')]
    exact hle
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    let B := S ^ (1 / s)
    have hB : 0 < B := Real.rpow_pos_of_pos hSpos _
    have hBpow : B ^ s = S := by
      dsimp [B]
      rw [← Real.rpow_mul hS]
      have he : (1 / s) * s = 1 := by field_simp
      rw [he, Real.rpow_one]
    let b' := fun j => b j / (B : ℂ)
    have hb' : (∑ j, w j * ‖b' j‖ ^ s) = 1 := by
      dsimp [b']
      simp_rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB.le,
        Real.div_rpow (norm_nonneg _) hB.le, ← mul_div_assoc]
      rw [← Finset.sum_div, hBpow, div_self hzero]
    have h := finite_pairing_interpolation K w hK hr hs hr₄ ht0 ht1 hrdef hsdef hfour a b' ha hb'
    dsimp [b'] at h
    rw [finitePairing_div_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hB.le] at h
    exact (div_le_one hB).mp h

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SimpleFourierPairing
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Simple tests for Fourier interpolation on the actual averaging measure

A finite measurable profile partitions the real line into its fibers.
Its matrix entries are actual Fourier integrals over those fibers. The
two finite interpolation endpoints follow from positivity and the proved
improved fourth-moment theorem.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
theorem profile_eq_sum {E : Type*} [AddCommMonoid E] (φ : ℝ → κ) (b : κ → E) (t : ℝ) :
    b (φ t) = ∑ j, ({u | φ u = j}.indicator (fun _ => b j)) t := by
  classical
  symm
  calc
    _ = ({u | φ u = φ t}.indicator (fun _ => b (φ t))) t := by
      apply Finset.sum_eq_single (φ t)
      · intro j _ hj
        exact Set.indicator_of_notMem (fun h => hj h.symm) _
      · simp
    _ = _ := by simp

omit [Fintype ι] in
theorem integrable_profile (ν : Measure ℝ) [IsFiniteMeasure ν]
    (φ : ℝ → κ) (hφ : ∀ j, MeasurableSet {t | φ t = j}) (b : κ → ℂ) :
    Integrable (fun t => b (φ t)) ν := by
  have heq : (fun t => b (φ t)) = fun t => ∑ j, ({u | φ u = j}.indicator (fun _ => b j)) t := by
    funext t
    exact profile_eq_sum φ b t
  rw [heq]
  exact integrable_finsetSum _ fun j _ => (integrable_const _).indicator (hφ j)

omit [Fintype ι] in
theorem profile_bound (φ : ℝ → κ) (b : κ → ℂ) (t : ℝ) :
    ‖b (φ t)‖ ≤ ∑ j, ‖b j‖ :=
  Finset.single_le_sum (fun j _ => norm_nonneg (b j)) (Finset.mem_univ _)

omit [Fintype ι] in
theorem integral_profile_power (ν : Measure ℝ) [IsFiniteMeasure ν]
    (φ : ℝ → κ) (hφ : ∀ j, MeasurableSet {t | φ t = j}) (b : κ → ℂ) (p : ℝ) :
    (∫ t, ‖b (φ t)‖ ^ p ∂ν) = ∑ j, ν.real {t | φ t = j} * ‖b j‖ ^ p := by
  have heq : (fun t => ‖b (φ t)‖ ^ p) =
      fun t => ∑ j, ({u | φ u = j}.indicator (fun _ => ‖b j‖ ^ p)) t := by
    funext t
    exact profile_eq_sum φ (fun j => ‖b j‖ ^ p) t
  rw [heq, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    simpa only [smul_eq_mul] using integral_indicator_const (μ := ν) (‖b j‖ ^ p) (hφ j)
  · intro j _
    exact (integrable_const _).indicator (hφ j)

omit [Fintype ι] [Fintype κ] in
theorem norm_profileMatrix_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (φ : ℝ → κ) (i : ι) (j : κ) :
    ‖profileMatrix ν frequency φ i j‖ ≤ ν.real {u | φ u = j} := by
  calc
    _ ≤ ∫ t in {u | φ u = j}, ‖character (frequency i) t‖ ∂ν := norm_integral_le_integral_norm _
    _ = _ := by simp [norm_character, Measure.real]

theorem finitePairing_profileMatrix (ν : Measure ℝ) [IsFiniteMeasure ν]
    (frequency : ι → ℝ) (φ : ℝ → κ) (hφ : ∀ j, MeasurableSet {t | φ t = j})
    (a : ι → ℂ) (b : κ → ℂ) :
    finitePairing (profileMatrix ν frequency φ) a b =
      ∫ t, finiteFourierSum frequency a t * b (φ t) ∂ν := by
  have hpoint (t : ℝ) : finiteFourierSum frequency a t * b (φ t) =
      ∑ i, ∑ j, (a i * b j) * ({u | φ u = j}.indicator (character (frequency i))) t := by
    rw [finiteFourierSum, profile_eq_sum φ b t, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases ht : φ t = j
    · simp only [Set.indicator, Set.mem_ofPred_eq, ht, ite_true, if_true]
      ring
    · simp only [Set.indicator, Set.mem_ofPred_eq, ht, ite_false, if_false, mul_zero]
  have hint (i : ι) (j : κ) : Integrable
      (fun t => (a i * b j) * ({u | φ u = j}.indicator (character (frequency i))) t) ν :=
    ((integrable_character ν _).indicator (hφ j)).const_mul _
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · unfold finitePairing
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_indicator (hφ j)]
      unfold profileMatrix
      ring
    · intro j _
      exact hint i j
  · intro i _
    exact integrable_finsetSum _ (fun j _ => hint i j)

theorem profileMatrix_fourth_endpoint (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (φ : ℝ → κ) (hφ : ∀ j, MeasurableSet {t | φ t = j})
    {gap D : ℝ} (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (a : ι → ℂ) (b : κ → ℂ)
    (ha : (∑ i, ‖a i‖ ^ fourthExponent D) = 1)
    (hb : (∑ j, ν.real {t | φ t = j} * ‖b j‖ ^ (4 / 3 : ℝ)) = 1) :
    ‖finitePairing (profileMatrix ν frequency φ) a b‖ ≤ 1 := by
  have hf : MemLp (finiteFourierSum frequency a) (ENNReal.ofReal 4) ν :=
    MemLp.of_bound (continuous_finiteFourierSum frequency a).aestronglyMeasurable
      (∑ i, ‖a i‖) (Filter.Eventually.of_forall (finiteFourierSum_bound frequency a))
  have hg : MemLp (fun t => b (φ t)) (ENNReal.ofReal (4 / 3 : ℝ)) ν :=
    MemLp.of_bound (integrable_profile ν φ hφ b).aestronglyMeasurable
      (∑ j, ‖b j‖) (Filter.Eventually.of_forall (profile_bound φ b))
  have hpq : (4 : ℝ).HolderConjugate (4 / 3) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hfour := finite_fourier_l4_gain ν frequency a hgap hsep hν hD hcard
  have hfour' : (∫ t, ‖finiteFourierSum frequency a t‖ ^ (4 : ℝ) ∂ν) ^ (1 / 4 : ℝ) ≤ 1 := by
    simpa [sequenceNorm, ha] using hfour
  rw [finitePairing_profileMatrix ν frequency φ hφ a b]
  calc
    _ ≤ ∫ t, ‖finiteFourierSum frequency a t * b (φ t)‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ t, ‖finiteFourierSum frequency a t‖ * ‖b (φ t)‖ ∂ν := by simp only [norm_mul]
    _ ≤ (∫ t, ‖finiteFourierSum frequency a t‖ ^ (4 : ℝ) ∂ν) ^ (1 / 4 : ℝ) *
        (∫ t, ‖b (φ t)‖ ^ (4 / 3 : ℝ) ∂ν) ^ (1 / (4 / 3) : ℝ) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hf hg
    _ ≤ 1 := by
      rw [integral_profile_power ν φ hφ b, hb, Real.one_rpow, mul_one]
      exact hfour'

/-- Arbitrary finite-valued measurable tests, without any normalization on
the test. This is the simple-test input to the bounded duality argument. -/
theorem simple_fourier_pairing_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (φ : ℝ → κ) (hφ : ∀ j, MeasurableSet {t | φ t = j})
    {gap D r s t : ℝ} (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hr : 0 < r) (hs : 0 < s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrdef : (1 - t) * (r / 1) + t * (r / fourthExponent D) = 1)
    (hsdef : (1 - t) * (s / 1) + t * (s / (4 / 3)) = 1)
    (a : ι → ℂ) (b : κ → ℂ) (ha : (∑ i, ‖a i‖ ^ r) = 1) :
    ‖∫ u, finiteFourierSum frequency a u * b (φ u) ∂ν‖ ≤
      (∫ u, ‖b (φ u)‖ ^ s ∂ν) ^ (1 / s) := by
  have hθ := phaseParameter_range hD
  have hr₄ : 0 < fourthExponent D := by
    apply div_pos (by norm_num : (0 : ℝ) < 4)
    change 0 < 3 - phaseConstant / Real.log (2 * D)
    linarith [hθ.2]
  rw [← finitePairing_profileMatrix ν frequency φ hφ a b,
    integral_profile_power ν φ hφ b]
  apply finite_pairing_interpolation_test (profileMatrix ν frequency φ)
    (fun j => ν.real {u | φ u = j}) (fun j => measureReal_nonneg) (norm_profileMatrix_le ν frequency φ)
    hr hs hr₄ ht0 ht1 hrdef hsdef _ a b ha
  exact profileMatrix_fourth_endpoint ν frequency φ hφ hgap hsep hν hD hcard

omit [Fintype κ] in
theorem simpleFunc_fourier_pairing_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) {gap D r s t : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hr : 0 < r) (hs : 0 < s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrdef : (1 - t) * (r / 1) + t * (r / fourthExponent D) = 1)
    (hsdef : (1 - t) * (s / 1) + t * (s / (4 / 3)) = 1)
    (a : ι → ℂ) (g : SimpleFunc ℝ ℂ) (ha : (∑ i, ‖a i‖ ^ r) = 1) :
    ‖∫ u, finiteFourierSum frequency a u * g u ∂ν‖ ≤
      (∫ u, ‖g u‖ ^ s ∂ν) ^ (1 / s) := by
  let φ : ℝ → ↥g.range := fun u => ⟨g u, g.mem_range_self u⟩
  have hφ (j : ↥g.range) : MeasurableSet {u | φ u = j} := by
    convert g.measurableSet_fiber j.val using 1
    all_goals try with_reducible_and_instances rfl
    ext u
    exact Subtype.ext_iff
  exact simple_fourier_pairing_bound ν frequency φ hφ hgap hsep hν hD hcard
    hr hs ht0 ht1 hrdef hsdef a (fun j => (j : ℂ)) ha

omit [Fintype ι] [Fintype κ] in
theorem fourier_interpolation_parameters {D p : ℝ} (hD : 1 ≤ D) (hp : 4 ≤ p) :
    0 < fourierInterpolationExponent D p ∧ 0 < p / (p - 1) ∧
    0 ≤ 4 / p ∧ 4 / p ≤ 1 ∧
    (1 - 4 / p) * (fourierInterpolationExponent D p / 1) +
      (4 / p) * (fourierInterpolationExponent D p / fourthExponent D) = 1 ∧
    (1 - 4 / p) * ((p / (p - 1)) / 1) +
      (4 / p) * ((p / (p - 1)) / (4 / 3)) = 1 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hθ := phaseParameter_range hD
  have hθ' : phaseParameter D ≤ 1 / 3 := hθ.2
  have hq : (1 + phaseParameter D) / p ≤ 1 / 3 :=
    (div_le_iff₀ hp0).2 (by linarith)
  have hd : 0 < 1 - (1 + phaseParameter D) / p := by linarith
  have hdiv : fourierInterpolationExponent D p / fourthExponent D =
      fourierInterpolationExponent D p * (3 - phaseParameter D) / 4 := by
    unfold fourthExponent
    rw [div_div_eq_mul_div]
  refine ⟨one_div_pos.mpr hd, div_pos hp0 hp1, div_nonneg (by norm_num) hp0.le,
    (div_le_one hp0).2 hp, ?_, ?_⟩
  · rw [div_one, hdiv]
    calc
      _ = fourierInterpolationExponent D p * (1 - (1 + phaseParameter D) / p) := by
        field_simp
        ring
      _ = 1 := one_div_mul_cancel hd.ne'
  · field_simp
    ring

omit [Fintype κ] in
theorem simpleFunc_fourier_pairing_bound_at_p (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) (hp : 4 ≤ p)
    (a : ι → ℂ) (g : SimpleFunc ℝ ℂ)
    (ha : (∑ i, ‖a i‖ ^ fourierInterpolationExponent D p) = 1) :
    ‖∫ u, finiteFourierSum frequency a u * g u ∂ν‖ ≤
      (∫ u, ‖g u‖ ^ (p / (p - 1)) ∂ν) ^ (1 / (p / (p - 1))) := by
  obtain ⟨hr, hs, ht0, ht1, hrdef, hsdef⟩ := fourier_interpolation_parameters hD hp
  exact simpleFunc_fourier_pairing_bound ν frequency hgap hsep hν hD hcard
    hr hs ht0 ht1 hrdef hsdef a g ha

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_FiniteFourierGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar finite Fourier gain for every real exponent `p ≥ 4`. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem normalized_finite_fourier_power_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) (hp : 4 ≤ p)
    (ha : (∑ i, ‖a i‖ ^ fourierInterpolationExponent D p) = 1) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ≤ 1 := by
  apply bounded_lp_power_le_one_of_simple_tests ν (finiteFourierSum frequency a)
    (continuous_finiteFourierSum frequency a).measurable
    (Finset.sum_nonneg (fun i _ => norm_nonneg (a i))) (finiteFourierSum_bound frequency a)
    (by linarith)
  intro g
  exact simpleFunc_fourier_pairing_bound_at_p ν frequency hgap hsep hν hD hcard hp a g ha

theorem finite_fourier_power_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) (hp : 4 ≤ p) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ≤
      sequenceNorm a (fourierInterpolationExponent D p) ^ p := by
  have hr := (fourier_interpolation_parameters hD hp).1
  apply homogeneous_fourier_power_bound ν frequency hr (by linarith) _ a
  intro b hb
  exact normalized_finite_fourier_power_gain ν frequency b hgap hsep hν hD hcard hp hb

/-- The scalar form of Proposition `phase:finite-fourier`, with its exact
constant one and its logarithmic improvement in the coefficient exponent. -/
theorem finite_fourier_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → ℝ) (a : ι → ℂ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : Separated frequency gap) (hν : FourierGap ν gap)
    (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D) (hp : 4 ≤ p) :
    (∫ t, ‖finiteFourierSum frequency a t‖ ^ p ∂ν) ^ (1 / p) ≤
      sequenceNorm a (fourierInterpolationExponent D p) := by
  have hp0 : 0 < p := by linarith
  have h := Real.rpow_le_rpow
    (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
    (finite_fourier_power_gain ν frequency a hgap hsep hν hD hcard hp)
    (show 0 ≤ 1 / p by positivity)
  rw [← Real.rpow_mul (sequenceNorm_nonneg a _)] at h
  have heq : p * (1 / p) = 1 := by field_simp
  simpa only [heq, Real.rpow_one] using h

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertFourierGain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The diagonal finite-dimensional Hilbert version of the finite Fourier gain. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem diagonal_finite_fourier_gain (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → κ → ℝ) (a : ι → κ → ℂ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : ∀ j, Separated (fun i => frequency i j) gap)
    (hν : FourierGap ν gap) (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hp : 4 ≤ p) :
    (∫ t, (∑ j, ‖finiteFourierSum (fun i => frequency i j) (fun i => a i j) t‖ ^ 2) ^
      (p / 2) ∂ν) ^ (1 / p) ≤
      (∑ i, (∑ j, ‖a i j‖ ^ 2) ^ (fourierInterpolationExponent D p / 2)) ^
        (1 / fourierInterpolationExponent D p) := by
  let F := fun j => finiteFourierSum (fun i => frequency i j) (fun i => a i j)
  let r := fourierInterpolationExponent D p
  let b := fun j => sequenceNorm (fun i => a i j) r
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := (fourier_interpolation_parameters hD hp).1
  have hθ := phaseParameter_range hD
  have hθ' : phaseParameter D ≤ 1 / 3 := hθ.2
  have hratio : (1 + phaseParameter D) / p ≤ 1 / 3 :=
    (div_le_iff₀ hp0).2 (by linarith)
  have hden : 0 < 1 - (1 + phaseParameter D) / p := by linarith
  have hr2 : r ≤ 2 := (div_le_iff₀ hden).2 (by linarith)
  have hscalar (j : κ) : (∫ t, ‖F j t‖ ^ p ∂ν) ^ (1 / p) ≤ b j :=
    finite_fourier_gain ν (fun i => frequency i j) (fun i => a i j)
      hgap (hsep j) hν hD hcard hp
  have hterm (j : κ) :
      (∫ t, (‖F j t‖ ^ 2) ^ (p / 2) ∂ν) ^ (1 / (p / 2)) ≤ b j ^ 2 := by
    have heq (t : ℝ) : (‖F j t‖ ^ 2) ^ (p / 2) = ‖F j t‖ ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      push_cast
      ring
    simp_rw [heq]
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg
      (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)) _) (hscalar j) 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul
      (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))] at hpow
    have he : (1 / p) * (2 : ℕ) = 1 / (p / 2) := by push_cast; field_simp
    rwa [he] at hpow
  have hsum := integral_finite_minkowski ν (fun j t => ‖F j t‖ ^ 2)
    (fun j => (∑ i, ‖a i j‖) ^ 2)
    (fun j => (continuous_finiteFourierSum _ _).norm.pow 2)
    (fun j t => sq_nonneg _) (fun j t =>
      pow_le_pow_left₀ (norm_nonneg _) (finiteFourierSum_bound _ _ t) 2)
    (show 1 ≤ p / 2 by linarith)
  have hb : (∑ j, b j ^ 2) = ∑ j, (∑ i, ‖a i j‖ ^ r) ^ (2 / r) := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [b]
    rw [← Real.rpow_natCast, sequenceNorm_rpow]
    norm_num
  have hmixed := mixed_norm_comparison (fun i j => ‖a i j‖)
    (fun i j => norm_nonneg _) hr0 hr2
  have hsum' := hsum.trans ((Finset.sum_le_sum (fun j _ => hterm j)).trans_eq hb)
  have hboth := hsum'.trans hmixed
  have hI : 0 ≤ ∫ t, (∑ j, ‖F j t‖ ^ 2) ^ (p / 2) ∂ν :=
    integral_nonneg (fun t => Real.rpow_nonneg
      (Finset.sum_nonneg (fun j _ => sq_nonneg ‖F j t‖)) _)
  have hroot := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hboth
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← Real.rpow_mul hI,
    ← Real.rpow_mul (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg
      (Finset.sum_nonneg (fun j _ => sq_nonneg ‖a i j‖)) _))] at hroot
  have hleft : (1 / (p / 2)) * (1 / 2) = 1 / p := by field_simp
  have hright : (2 / r) * (1 / 2) = 1 / r := by ring
  simpa only [hleft, hright, F, r] using hroot

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PhaseSelection
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging separated selections

Finite probability laws on retained subsets and the scalar weighted
phase bound from §9, using the retention cancellation of §8.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable (Ω ι : Type*) [Fintype Ω] [Fintype ι]

variable {Ω ι}

namespace FiniteSelectionLaw

omit [Fintype ι] in
theorem expected_selectedCoefficient (L : FiniteSelectionLaw Ω ι)
    (hπ : ∀ i, L.marginal i ≠ 0) (a : ι → ℂ) (i : ι) :
    (∑ ω, (L.weight ω : ℂ) * L.selectedCoefficient a ω i) = a i := by
  have hsum : (∑ ω, (L.weight ω : ℂ) * L.selectedCoefficient a ω i) =
      (L.marginal i : ℂ) * (a i / (L.marginal i : ℂ)) := by
    unfold selectedCoefficient marginal
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  rw [hsum]
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hπ i))

theorem expected_selectedFourier (L : FiniteSelectionLaw Ω ι)
    (hπ : ∀ i, L.marginal i ≠ 0) (frequency : ι → ℝ) (a : ι → ℂ) (t : ℝ) :
    (∑ ω, (L.weight ω : ℂ) * finiteFourierSum frequency (L.selectedCoefficient a ω) t) =
      finiteFourierSum frequency a t := by
  unfold finiteFourierSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← mul_assoc, ← Finset.sum_mul, L.expected_selectedCoefficient hπ a i]

end FiniteSelectionLaw

theorem sum_subset_indicator {α E : Type*} [Fintype α] [AddCommMonoid E]
    (S : Finset α) (f : α → E) :
    (∑ i, if i ∈ S then f i else 0) = ∑ i : S, f i := by
  classical
  rw [← Finset.sum_filter]
  simpa using (Finset.sum_coe_sort S f).symm

theorem selectedFourier_eq_subtype (L : FiniteSelectionLaw Ω ι)
    (frequency : ι → ℝ) (a : ι → ℂ) (ω : Ω) (t : ℝ) :
    finiteFourierSum frequency (L.selectedCoefficient a ω) t =
      finiteFourierSum (fun i : L.retained ω => frequency i)
        (fun i : L.retained ω => a i / (L.marginal i : ℂ)) t := by
  unfold finiteFourierSum FiniteSelectionLaw.selectedCoefficient
  simp only [ite_mul, zero_mul]
  exact sum_subset_indicator _ _

omit [Fintype ι] in
theorem selection_jensen (L : FiniteSelectionLaw Ω ι) (C : Ω → ℝ)
    (hC : ∀ ω, 0 ≤ C ω) {r : ℝ} (hr : 1 ≤ r) :
    (∑ ω, L.weight ω * C ω ^ (1 / r)) ≤ (∑ ω, L.weight ω * C ω) ^ (1 / r) := by
  have hr0 : 0 < r := by linarith
  have h := (Real.concaveOn_rpow (show 0 ≤ 1 / r by positivity)
    ((div_le_one hr0).2 hr)).le_map_sum (t := Finset.univ)
    (fun ω _ => L.nonnegative ω) L.total (fun ω _ => hC ω)
  simpa only [smul_eq_mul] using h

theorem retention_cancellation {π q μ r : ℝ} (hπ : 0 < π) (hq : 0 < q)
    (hqπ : q ≤ π) (hr : 1 ≤ r) (hrelation : μ * r = r - 1) :
    π ^ (1 - r) * (q ^ μ) ^ r ≤ 1 := by
  rw [← Real.rpow_mul hq.le, hrelation]
  have heq : π ^ (1 - r) * q ^ (r - 1) = (q / π) ^ (r - 1) := by
    rw [Real.div_rpow hq.le hπ.le, div_eq_mul_inv, ← Real.rpow_neg hπ.le]
    have he : 1 - r = -(r - 1) := by ring
    rw [he, mul_comm]
  rw [heq]
  exact Real.rpow_le_one (div_nonneg hq.le hπ.le) ((div_le_one hπ).2 hqπ) (by linarith)

theorem weighted_power_mean (l x : ι → ℝ) (hl : ∀ i, 0 ≤ l i) (hx : ∀ i, 0 ≤ x i)
    (htotal : ∑ i, l i ≤ 1) {r p : ℝ} (hr : 0 < r) (hrp : r ≤ p) :
    (∑ i, l i * x i ^ r) ^ (1 / r) ≤ (∑ i, l i * x i ^ p) ^ (1 / p) := by
  have hp : 0 < p := hr.trans_le hrp
  let w : Option ι → ℝ := fun i => match i with
    | none => 1 - ∑ j, l j
    | some j => l j
  let y : Option ι → ℝ := fun i => match i with
    | none => 0
    | some j => x j ^ p
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    cases i
    · exact sub_nonneg.mpr htotal
    · exact hl _
  have hy : ∀ i, 0 ≤ y i := by
    intro i
    cases i
    · rfl
    · exact Real.rpow_nonneg (hx _) _
  have hsum : ∑ i, w i = 1 := by simp [w]
  have hj := (Real.concaveOn_rpow (div_nonneg hr.le hp.le)
    ((div_le_one hp).2 hrp)).le_map_sum (t := Finset.univ)
    (fun i _ => hw i) hsum (fun i _ => hy i)
  have hpow (i : ι) : (x i ^ p) ^ (r / p) = x i ^ r := by
    rw [← Real.rpow_mul (hx i)]
    congr 1
    field_simp
  have hmean : (∑ i, l i * x i ^ r) ≤ (∑ i, l i * x i ^ p) ^ (r / p) := by
    simpa [w, y, smul_eq_mul, Real.zero_rpow (div_pos hr hp).ne', hpow] using hj
  have hout := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (hx i) _)) hmean
    (show 0 ≤ 1 / r by positivity)
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (hx i) _))] at hout
  have heq : (r / p) * (1 / r) = 1 / p := by field_simp
  simpa only [heq] using hout

theorem weighted_coefficient_cost (l : ι → ℝ) (X lambda : ι → ℂ) (π q : ι → ℝ)
    {μ r : ℝ} (hl : ∀ i, 0 ≤ l i) (hπ : ∀ i, 0 < π i) (hq : ∀ i, 0 < q i)
    (hqπ : ∀ i, q i ≤ π i) (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ μ)
    (hr : 1 ≤ r) (hμr : μ * r = r - 1) :
    (∑ i, π i * (‖((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i * X i‖ / π i) ^ r) ≤
      ∑ i, l i * ‖X i‖ ^ r := by
  apply Finset.sum_le_sum
  intro i _
  have hpower : ‖((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i * X i‖ ^ r =
      l i * ‖lambda i‖ ^ r * ‖X i‖ ^ r := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hl i) _),
      Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (hl i) _) (norm_nonneg _)) (norm_nonneg _),
      Real.mul_rpow (Real.rpow_nonneg (hl i) _) (norm_nonneg _),
      ← Real.rpow_mul (hl i)]
    have he : (1 - μ) * r = 1 := by nlinarith
    rw [he, Real.rpow_one]
  have hcancel : π i ^ (1 - r) * ‖lambda i‖ ^ r ≤ 1 := by
    refine (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (hlambda i) (by linarith))
      (Real.rpow_nonneg (hπ i).le _)).trans ?_
    exact retention_cancellation (hπ i) (hq i) (hqπ i) hr hμr
  calc
    _ = π i ^ (1 - r) * (l i * ‖lambda i‖ ^ r * ‖X i‖ ^ r) := by
      rw [Real.div_rpow (norm_nonneg _) (hπ i).le, hpower,
        Real.rpow_sub (hπ i), Real.rpow_one]
      ring
    _ = (π i ^ (1 - r) * ‖lambda i‖ ^ r) * (l i * ‖X i‖ ^ r) := by ring
    _ ≤ 1 * (l i * ‖X i‖ ^ r) :=
      mul_le_mul_of_nonneg_right hcancel (mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _))
    _ = _ := one_mul _

omit [Fintype Ω] [Fintype ι] in
theorem phase_selection_parameters {D p : ℝ} (hD : 1 ≤ D) (hp : 4 ≤ p) :
    1 ≤ fourierInterpolationExponent D p ∧ fourierInterpolationExponent D p ≤ p ∧
      phaseMu D p * fourierInterpolationExponent D p = fourierInterpolationExponent D p - 1 := by
  have hp0 : 0 < p := by linarith
  have hθ := phaseParameter_range hD
  have hθ0 : 0 < phaseParameter D := hθ.1
  have hθ1 : phaseParameter D ≤ 1 / 3 := hθ.2
  have hμ0 : 0 < phaseMu D p := div_pos (by linarith) hp0
  have hμ1 : phaseMu D p ≤ 1 / 3 := (div_le_iff₀ hp0).2 (by linarith)
  have hd : 0 < 1 - phaseMu D p := by linarith
  have hpr : (1 - phaseMu D p) * fourierInterpolationExponent D p = 1 := by
    change (1 - phaseMu D p) * (1 / (1 - phaseMu D p)) = 1
    exact mul_one_div_cancel hd.ne'
  have hpmu : p * phaseMu D p = 1 + phaseParameter D := by
    unfold phaseMu
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · change 1 ≤ 1 / (1 - phaseMu D p)
    exact (le_div_iff₀ hd).2 (by linarith)
  · change 1 / (1 - phaseMu D p) ≤ p
    exact (div_le_iff₀ hd).2 (by nlinarith)
  · nlinarith

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DiagonalPhaseSelection
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Averaging diagonal Hilbert-valued phases

The weighted prediction bound of §9 for finite-dimensional Hilbert vectors and
coordinate-dependent frequencies. The retained-set estimate is the proved
constant-one diagonal Fourier gain; the marginal cancellation is exact.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {Ω ι κ : Type*} [Fintype Ω] [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

omit [Fintype Ω] [Fintype ι] [Fintype κ] in
theorem euclidean_sum_apply {α : Type*} (s : Finset α)
    (f : α → EuclideanSpace ℂ κ) (j : κ) :
    (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

omit [Fintype Ω] [Fintype ι] in
theorem euclidean_norm_rpow (v : EuclideanSpace ℂ κ) (p : ℝ) :
    ‖v‖ ^ p = (∑ j, ‖v j‖ ^ 2) ^ (p / 2) := by
  rw [← EuclideanSpace.norm_sq_eq, ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

omit [Fintype Ω] [Fintype κ] in
theorem diagonalFourierSum_eq_sum (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (t : ℝ) :
    diagonalFourierSum frequency a t = ∑ i, diagonalModulation (frequency i) (a i) t := by
  apply PiLp.ext
  intro j
  rw [euclidean_sum_apply]
  rfl

omit [Fintype Ω] [Fintype κ] in
theorem continuous_diagonalFourierSum (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) : Continuous (diagonalFourierSum frequency a) :=
  (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
    (continuous_pi (fun _ => continuous_finiteFourierSum _ _))

omit [Fintype Ω] in
theorem diagonalFourierSum_bound (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (t : ℝ) :
    ‖diagonalFourierSum frequency a t‖ ≤ ∑ i, ‖a i‖ := by
  rw [diagonalFourierSum_eq_sum]
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl (fun i _ =>
    norm_diagonalModulation (frequency i) (a i) t))

omit [Fintype Ω] in
theorem lpNorm_diagonalFourierSum_eq (ν : Measure ℝ) (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) {p : ℝ} (hp : 0 < p) :
    lpNorm (diagonalFourierSum frequency a) (ENNReal.ofReal p) ν =
      (∫ t, ‖diagonalFourierSum frequency a t‖ ^ p ∂ν) ^ (1 / p) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top
    (continuous_diagonalFourierSum frequency a).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  simp only [one_div]

omit [Fintype Ω] in
theorem diagonal_fourier_gain_norm (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (frequency : ι → κ → ℝ) (a : ι → EuclideanSpace ℂ κ) {gap D p : ℝ}
    (hgap : 0 < gap) (hsep : ∀ j, Separated (fun i => frequency i j) gap)
    (hν : FourierGap ν gap) (hD : 1 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hp : 4 ≤ p) :
    (∫ t, ‖diagonalFourierSum frequency a t‖ ^ p ∂ν) ^ (1 / p) ≤
      (∑ i, ‖a i‖ ^ fourierInterpolationExponent D p) ^
        (1 / fourierInterpolationExponent D p) := by
  simpa only [euclidean_norm_rpow, diagonalFourierSum, PiLp.toLp_apply] using
    diagonal_finite_fourier_gain ν frequency (fun i j => a i j) hgap hsep hν hD hcard hp

namespace FiniteSelectionLaw

omit [Fintype ι] [Fintype κ] in
theorem selectedVector_apply (L : FiniteSelectionLaw Ω ι) (a : ι → EuclideanSpace ℂ κ)
    (ω : Ω) (i : ι) (j : κ) :
    L.selectedVector a ω i j = L.selectedCoefficient (fun i => a i j) ω i := by
  unfold selectedVector selectedCoefficient
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

omit [Fintype ι] in
theorem norm_selectedVector (L : FiniteSelectionLaw Ω ι) (a : ι → EuclideanSpace ℂ κ)
    (ω : Ω) (i : ι) (hπ : 0 < L.marginal i) :
    ‖L.selectedVector a ω i‖ =
      if i ∈ L.retained ω then ‖a i‖ / L.marginal i else 0 := by
  unfold selectedVector
  split_ifs <;> simp [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hπ, div_eq_mul_inv, mul_comm]

omit [Fintype κ] in
theorem expected_selectedDiagonal (L : FiniteSelectionLaw Ω ι)
    (hπ : ∀ i, L.marginal i ≠ 0) (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (t : ℝ) :
    (∑ ω, (L.weight ω : ℂ) • diagonalFourierSum frequency (L.selectedVector a ω) t) =
      diagonalFourierSum frequency a t := by
  apply PiLp.ext
  intro j
  rw [euclidean_sum_apply]
  simpa only [PiLp.smul_apply, smul_eq_mul, diagonalFourierSum, PiLp.toLp_apply,
    selectedVector_apply] using
    L.expected_selectedFourier hπ (fun i => frequency i j) (fun i => a i j) t

theorem selected_vector_cost (L : FiniteSelectionLaw Ω ι) (a : ι → EuclideanSpace ℂ κ)
    {r : ℝ} (hr : 0 < r) (hπ : ∀ i, 0 < L.marginal i) :
    (∑ ω, L.weight ω * ∑ i, ‖L.selectedVector a ω i‖ ^ r) =
      ∑ i, L.marginal i * (‖a i‖ / L.marginal i) ^ r := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [marginal, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [norm_selectedVector L a ω i (hπ i)]
  split_ifs <;> simp [Real.zero_rpow hr.ne', marginal]

end FiniteSelectionLaw

omit [Fintype κ] in
theorem selectedDiagonal_eq_subtype (L : FiniteSelectionLaw Ω ι)
    (frequency : ι → κ → ℝ) (a : ι → EuclideanSpace ℂ κ) (ω : Ω) (t : ℝ) :
    diagonalFourierSum frequency (L.selectedVector a ω) t =
      diagonalFourierSum (fun i : L.retained ω => frequency i)
        (fun i : L.retained ω => (L.marginal i : ℂ)⁻¹ • a i) t := by
  apply PiLp.ext
  intro j
  simpa only [diagonalFourierSum, PiLp.toLp_apply, FiniteSelectionLaw.selectedVector_apply,
    PiLp.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    selectedFourier_eq_subtype L (fun i => frequency i j) (fun i => a i j) ω t

theorem selected_vector_power_sum_eq_subtype (L : FiniteSelectionLaw Ω ι)
    (a : ι → EuclideanSpace ℂ κ) {r : ℝ} (hr : 0 < r) (ω : Ω) :
    (∑ i, ‖L.selectedVector a ω i‖ ^ r) =
      ∑ i : L.retained ω, ‖(L.marginal i : ℂ)⁻¹ • a i‖ ^ r := by
  have heq (i : ι) : ‖L.selectedVector a ω i‖ ^ r =
      if i ∈ L.retained ω then ‖(L.marginal i : ℂ)⁻¹ • a i‖ ^ r else 0 := by
    unfold FiniteSelectionLaw.selectedVector
    split_ifs <;> simp [Real.zero_rpow hr.ne']
  simp_rw [heq]
  exact sum_subset_indicator _ _

/-- Inverse-marginal averaging of diagonal Hilbert phases. -/
theorem selected_diagonal_fourier_gain (L : FiniteSelectionLaw Ω ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) {gap D p : ℝ}
    (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hπ : ∀ i, 0 < L.marginal i)
    (hsep : ∀ ω, 0 < L.weight ω → ∀ j,
      Separated (fun i : L.retained ω => frequency i j) gap)
    (hcard : ∀ ω, 0 < L.weight ω → ((L.retained ω).card : ℝ) ≤ D)
    (hr : 1 ≤ fourierInterpolationExponent D p) :
    (∫ t, ‖diagonalFourierSum frequency a t‖ ^ p ∂ν) ^ (1 / p) ≤
      (∑ i, L.marginal i * (‖a i‖ / L.marginal i) ^ fourierInterpolationExponent D p) ^
        (1 / fourierInterpolationExponent D p) := by
  let r := fourierInterpolationExponent D p
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := by dsimp [r]; linarith
  let G : Ω → ℝ → EuclideanSpace ℂ κ :=
    fun ω => diagonalFourierSum frequency (L.selectedVector a ω)
  have hterm (ω : Ω) : lpNorm ((L.weight ω : ℂ) • G ω) (ENNReal.ofReal p) ν ≤
      L.weight ω * (∑ i, ‖L.selectedVector a ω i‖ ^ r) ^ (1 / r) := by
    rw [lpNorm_const_smul]
    change ‖(L.weight ω : ℂ)‖ * lpNorm (G ω) (ENNReal.ofReal p) ν ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (L.nonnegative ω)]
    by_cases hw : L.weight ω = 0
    · simp [hw]
    have hwpos : 0 < L.weight ω := lt_of_le_of_ne (L.nonnegative ω) (Ne.symm hw)
    apply mul_le_mul_of_nonneg_left _ (L.nonnegative ω)
    have heq : G ω = diagonalFourierSum (fun i : L.retained ω => frequency i)
        (fun i : L.retained ω => (L.marginal i : ℂ)⁻¹ • a i) := by
      funext t
      exact selectedDiagonal_eq_subtype L frequency a ω t
    rw [heq, lpNorm_diagonalFourierSum_eq ν _ _ hp0]
    have hg := diagonal_fourier_gain_norm ν (fun i : L.retained ω => frequency i)
      (fun i : L.retained ω => (L.marginal i : ℂ)⁻¹ • a i)
      hgap (hsep ω hwpos) hν hD (by simpa using hcard ω hwpos) hp
    simpa only [selected_vector_power_sum_eq_subtype L a hr0 ω] using hg
  have hmem (ω : Ω) : MemLp ((L.weight ω : ℂ) • G ω) (ENNReal.ofReal p) ν := by
    exact (MemLp.of_bound (continuous_diagonalFourierSum frequency
      (L.selectedVector a ω)).aestronglyMeasurable
      (∑ i, ‖L.selectedVector a ω i‖)
      (Filter.Eventually.of_forall (diagonalFourierSum_bound frequency
        (L.selectedVector a ω)))).const_smul _
  have hexpect : (∑ ω, (L.weight ω : ℂ) • G ω) = diagonalFourierSum frequency a := by
    funext t
    simpa only [Finset.sum_apply, Pi.smul_apply] using
      L.expected_selectedDiagonal (fun i => (hπ i).ne') frequency a t
  calc
    _ = lpNorm (diagonalFourierSum frequency a) (ENNReal.ofReal p) ν :=
      (lpNorm_diagonalFourierSum_eq ν frequency a hp0).symm
    _ ≤ ∑ ω, lpNorm ((L.weight ω : ℂ) • G ω) (ENNReal.ofReal p) ν := by
      rw [← hexpect]
      exact lpNorm_sum_le (s := Finset.univ) (fun ω _ => hmem ω)
        (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1 ≤ p by linarith))
    _ ≤ ∑ ω, L.weight ω * (∑ i, ‖L.selectedVector a ω i‖ ^ r) ^ (1 / r) :=
      Finset.sum_le_sum (fun ω _ => hterm ω)
    _ ≤ (∑ ω, L.weight ω * ∑ i, ‖L.selectedVector a ω i‖ ^ r) ^ (1 / r) :=
      selection_jensen L _ (fun ω => Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) hr
    _ = _ := by rw [L.selected_vector_cost a hr0 hπ]

/-- The scalar marginal cancellation applies to Hilbert vectors through their norms. -/
theorem weighted_vector_coefficient_cost (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (π q : ι → ℝ) {μ r : ℝ}
    (hl : ∀ i, 0 ≤ l i) (hπ : ∀ i, 0 < π i) (hq : ∀ i, 0 < q i)
    (hqπ : ∀ i, q i ≤ π i) (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ μ)
    (hr : 1 ≤ r) (hμr : μ * r = r - 1) :
    (∑ i, π i * (‖(((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i) • X i‖ / π i) ^ r) ≤
      ∑ i, l i * ‖X i‖ ^ r := by
  simpa only [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using
    weighted_coefficient_cost l (fun i => (‖X i‖ : ℂ)) lambda π q hl hπ hq hqπ hlambda hr hμr

theorem weighted_diagonal_phase_bound (L : FiniteSelectionLaw Ω ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → κ → ℝ)
    (l q : ι → ℝ) (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ)
    {gap D p μ : ℝ} (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hsep : ∀ ω, 0 < L.weight ω → ∀ j,
      Separated (fun i : L.retained ω => frequency i j) gap)
    (hcard : ∀ ω, 0 < L.weight ω → ((L.retained ω).card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hq : ∀ i, 0 < q i) (hqπ : ∀ i, q i ≤ L.marginal i)
    (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ μ)
    (hr : 1 ≤ fourierInterpolationExponent D p)
    (hrp : fourierInterpolationExponent D p ≤ p)
    (hμr : μ * fourierInterpolationExponent D p = fourierInterpolationExponent D p - 1) :
    (∫ t, ‖diagonalFourierSum frequency
      (fun i => (((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i) • X i) t‖ ^ p ∂ν) ^ (1 / p) ≤
      (∑ i, l i * ‖X i‖ ^ p) ^ (1 / p) := by
  have hπ : ∀ i, 0 < L.marginal i := fun i => (hq i).trans_le (hqπ i)
  have hr0 : 0 < fourierInterpolationExponent D p := by linarith
  have hsel := selected_diagonal_fourier_gain L ν frequency
    (fun i => (((l i ^ (1 - μ) : ℝ) : ℂ) * lambda i) • X i) hgap hν hD hp hπ hsep hcard hr
  have hcost := weighted_vector_coefficient_cost l X lambda L.marginal q hl hπ hq hqπ hlambda hr hμr
  refine hsel.trans ((Real.rpow_le_rpow ?_ hcost (show 0 ≤ 1 / fourierInterpolationExponent D p by positivity)).trans ?_)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hπ i).le
      (Real.rpow_nonneg (div_nonneg (norm_nonneg _) (hπ i).le) _)
  · exact weighted_power_mean l (fun i => ‖X i‖) hl (fun i => norm_nonneg _) htotal hr0 hrp

/-- The full finite-dimensional diagonal weighted prediction average of §9. -/
theorem weighted_diagonal_prediction_average_at_p (L : FiniteSelectionLaw Ω ι)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → κ → ℝ)
    (l q : ι → ℝ) (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ)
    {gap D p : ℝ} (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hsep : ∀ ω, 0 < L.weight ω → ∀ j,
      Separated (fun i : L.retained ω => frequency i j) gap)
    (hcard : ∀ ω, 0 < L.weight ω → ((L.retained ω).card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hq : ∀ i, 0 < q i) (hqπ : ∀ i, q i ≤ L.marginal i)
    (hlambda : ∀ i, ‖lambda i‖ ≤ q i ^ phaseMu D p) :
    (∫ t, (1 + ‖diagonalFourierSum frequency
      (fun i => (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i) t‖ ^ p) /
      (1 + ∑ i, l i * ‖X i‖ ^ p) ∂ν) ≤ 1 := by
  obtain ⟨hr, hrp, hμr⟩ := phase_selection_parameters hD hp
  have hp0 : 0 < p := by linarith
  let a : ι → EuclideanSpace ℂ κ :=
    fun i => (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i
  have hS : 0 ≤ ∑ i, l i * ‖X i‖ ^ p :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _)
  have hroot := weighted_diagonal_phase_bound L ν frequency l q X lambda hgap hν hD hp
    hsep hcard hl htotal hq hqπ hlambda hr hrp hμr
  have hmoment : (∫ t, ‖diagonalFourierSum frequency a t‖ ^ p ∂ν) ≤ ∑ i, l i * ‖X i‖ ^ p :=
    (Real.rpow_le_rpow_iff (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) hS
      (one_div_pos.mpr hp0)).mp hroot
  have hmem : MemLp (diagonalFourierSum frequency a) (ENNReal.ofReal p) ν :=
    MemLp.of_bound (continuous_diagonalFourierSum frequency a).aestronglyMeasurable
      (∑ i, ‖a i‖) (Filter.Eventually.of_forall (diagonalFourierSum_bound frequency a))
  have hi : Integrable (fun t => ‖diagonalFourierSum frequency a t‖ ^ p) ν := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using hmem.integrable_norm_rpow'
  rw [integral_div, integral_add (integrable_const 1) hi]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact (div_le_one (by linarith : 0 < 1 + ∑ i, l i * ‖X i‖ ^ p)).2 (by linarith)

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PredictionNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From probability averages to normalized prediction steps

The probability-mixture transfer, step supremum control, and normalization
costs used in §9. All averages below are actual Bochner integrals.
-/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

variable {α : Type*} [MeasurableSpace α]

/-- Transfer from the band-limited mixture to its principal probability.
The loss is proportional to the lower deviation of the prediction. -/
theorem probability_mixture_average_le (ω τ : Measure α)
    [IsProbabilityMeasure ω] [IsProbabilityMeasure τ] (B : α → ℝ)
    {η ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hω : Integrable B ω) (hτ : Integrable B τ)
    (hlower : ∀ᵐ x ∂τ, 1 - ε ≤ B x)
    (haverage : (∫ x, B x ∂(ENNReal.ofReal (1 - η) • ω + ENNReal.ofReal η • τ)) ≤ 1) :
    (∫ x, B x ∂ω) ≤ 1 + η / (1 - η) * ε := by
  have hη : 0 < 1 - η := sub_pos.mpr hη1
  have hl : 1 - ε ≤ ∫ x, B x ∂τ := by
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono_ae (integrable_const (1 - ε)) hτ hlower
  rw [integral_add_measure (hω.smul_measure ENNReal.ofReal_ne_top)
    (hτ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hη.le, ENNReal.toReal_ofReal hη0, smul_eq_mul, smul_eq_mul] at haverage
  apply (mul_le_mul_iff_right₀ hη).mp
  have hmul := mul_le_mul_of_nonneg_left hl hη0
  have heq : (1 - η) * (1 + η / (1 - η) * ε) = 1 - η * (1 - ε) := by
    field_simp
    ring
  rw [heq]
  nlinarith

omit [MeasurableSpace α] in
/-- A log-oscillation bound gives the precise multiplicative cell-supremum
bound. It also proves the relevant supremum is finite. -/
theorem prediction_cell_sup_bounds (B : α → ℝ) (I : Set α) {x : α} (hx : x ∈ I)
    (hpositive : ∀ y ∈ I, 0 < B y) {c : ℝ}
    (hosc : ∀ y ∈ I, |Real.log (B y) - Real.log (B x)| ≤ c) :
    B x ≤ predictionCellSup B I ∧ predictionCellSup B I ≤ Real.exp c * B x := by
  have hupper (y : α) (hy : y ∈ I) : B y ≤ Real.exp c * B x := by
    calc
      B y = Real.exp (Real.log (B y)) := (Real.exp_log (hpositive y hy)).symm
      _ ≤ Real.exp (c + Real.log (B x)) := Real.exp_le_exp.mpr (by
        have h := (abs_le.mp (hosc y hy)).2
        linarith)
      _ = Real.exp c * B x := by rw [Real.exp_add, Real.exp_log (hpositive x hx)]
  have hbounded : BddAbove (B '' I) := ⟨Real.exp c * B x, by
    rintro z ⟨y, hy, rfl⟩
    exact hupper y hy⟩
  exact ⟨le_csSup hbounded ⟨x, hx, rfl⟩,
    csSup_le ⟨B x, x, hx, rfl⟩ (by rintro z ⟨y, hy, rfl⟩; exact hupper y hy)⟩

theorem predictionNormalizer_pos (ν : Measure α) (Bsharp : α → ℝ) :
    0 < predictionNormalizer ν Bsharp :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem normalizedPrediction_nonnegative (ν : Measure α) (Bsharp : α → ℝ)
    (hB : ∀ x, 0 ≤ Bsharp x) (x : α) : 0 ≤ normalizedPrediction ν Bsharp x :=
  div_nonneg (hB x) (predictionNormalizer_pos ν Bsharp).le

theorem normalizedPrediction_average_le_one (ν : Measure α) (Bsharp : α → ℝ) :
    (∫ x, normalizedPrediction ν Bsharp x ∂ν) ≤ 1 := by
  simp only [normalizedPrediction, integral_div]
  exact (div_le_one (predictionNormalizer_pos ν Bsharp)).2 (le_max_right _ _)

theorem predictionNormalizer_log_le (ν : Measure α) (Bsharp : α → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (haverage : ∫ x, Bsharp x ∂ν ≤ Real.exp c) :
    Real.log (predictionNormalizer ν Bsharp) ≤ c := by
  apply (Real.log_le_iff_le_exp (predictionNormalizer_pos ν Bsharp)).2
  exact max_le (Real.one_le_exp hc) haverage

/-- Exponential step oscillation and an additive average error yield an
additive logarithmic normalization cost. -/
theorem step_normalization_cost (ν : Measure α)
    (B Bsharp : α → ℝ) {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hB : Integrable B ν) (hsharp : Integrable Bsharp ν)
    (hmajorant : ∀ᵐ x ∂ν, Bsharp x ≤ Real.exp (b * u) * B x)
    (haverage : ∫ x, B x ∂ν ≤ 1 + a * u) :
    Real.log (predictionNormalizer ν Bsharp) ≤ (a + b) * u := by
  apply predictionNormalizer_log_le ν Bsharp (mul_nonneg (add_nonneg ha hb) hu)
  have hi := integral_mono_ae hsharp (hB.const_mul (Real.exp (b * u))) hmajorant
  rw [integral_const_mul] at hi
  calc
    _ ≤ Real.exp (b * u) * (1 + a * u) :=
      hi.trans (mul_le_mul_of_nonneg_left haverage (Real.exp_pos _).le)
    _ ≤ Real.exp (b * u) * Real.exp (a * u) :=
      mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp (a * u))
        (Real.exp_pos _).le
    _ = Real.exp ((a + b) * u) := by rw [← Real.exp_add]; congr 1; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PhaseMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Motion of diagonal Fourier predictions

Bounded frequencies give explicit Lipschitz bounds for the actual characters
and Hilbert-valued phase sums. Together with logarithmic energy control these
give the multiplicative cell-supremum bound required by §9.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem character_motion (frequency s t : ℝ) :
    ‖character frequency t - character frequency s‖ ≤ |frequency| * |t - s| := by
  have h := norm_exp_sub_le_of_re_le
    (((frequency * s : ℝ) : ℂ) * Complex.I)
    (((frequency * t : ℝ) : ℂ) * Complex.I) 0 (by simp) (by simp)
  have hd : (((frequency * t : ℝ) : ℂ) * Complex.I) -
      (((frequency * s : ℝ) : ℂ) * Complex.I) =
      ((frequency * (t - s) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hd, Real.exp_zero, one_mul, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs, abs_mul] at h
  exact h

omit [Fintype ι] in
theorem diagonalModulation_motion (frequency : κ → ℝ) (a : EuclideanSpace ℂ κ)
    {L : ℝ} (hL : 0 ≤ L) (hfrequency : ∀ j, |frequency j| ≤ L) (s t : ℝ) :
    ‖diagonalModulation frequency a t - diagonalModulation frequency a s‖ ≤
      L * ‖a‖ * |t - s| := by
  have hcoordinate (j : κ) :
      ‖(diagonalModulation frequency a t - diagonalModulation frequency a s) j‖ ≤
        ‖a j‖ * (L * |t - s|) := by
    have heq : (diagonalModulation frequency a t - diagonalModulation frequency a s) j =
        a j * (character (frequency j) t - character (frequency j) s) := by
      simp only [PiLp.sub_apply, diagonalModulation]
      ring
    rw [heq, norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((character_motion (frequency j) s t).trans
        (mul_le_mul_of_nonneg_right (hfrequency j) (abs_nonneg _))) (norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ L * ‖a‖ * |t - s|)).mp
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ j, (‖a j‖ * (L * |t - s|)) ^ 2 :=
      Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcoordinate j) 2
    _ = (L * ‖a‖ * |t - s|) ^ 2 := by
      simp_rw [mul_pow]
      rw [← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq]
      ring

/-- Uniform frequency control bounds the motion by the total coefficient norm. -/
theorem diagonalFourierSum_motion (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) {L : ℝ} (hL : 0 ≤ L)
    (hfrequency : ∀ i j, |frequency i j| ≤ L) (s t : ℝ) :
    ‖diagonalFourierSum frequency a t - diagonalFourierSum frequency a s‖ ≤
      L * (∑ i, ‖a i‖) * |t - s| := by
  rw [diagonalFourierSum_eq_sum, diagonalFourierSum_eq_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖diagonalModulation (frequency i) (a i) t -
        diagonalModulation (frequency i) (a i) s‖ := norm_sum_le _ _
    _ ≤ ∑ i, L * ‖a i‖ * |t - s| := Finset.sum_le_sum fun i _ =>
      diagonalModulation_motion (frequency i) (a i) hL (hfrequency i) s t
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- Removing the path carrier leaves a fixed vector. Its size does not enter
logarithmic motion; only the off-path Fourier coefficients contribute. -/
theorem fixed_path_diagonal_log_motion (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (Y : EuclideanSpace ℂ κ)
    {L p denominator : ℝ} (hL : 0 ≤ L) (hp : 1 ≤ p) (hd : 0 < denominator)
    (hfrequency : ∀ i j, |frequency i j| ≤ L) (s t : ℝ) :
    |Real.log (energyRatio p denominator (Y + diagonalFourierSum frequency a t)) -
      Real.log (energyRatio p denominator (Y + diagonalFourierSum frequency a s))| ≤
        p * L * (∑ i, ‖a i‖) * |t - s| := by
  have h := log_energyRatio_lipschitz hp hd (Y + diagonalFourierSum frequency a t)
    (Y + diagonalFourierSum frequency a s)
  rw [add_sub_add_left_eq_sub] at h
  refine h.trans ?_
  have hm := mul_le_mul_of_nonneg_left
    (diagonalFourierSum_motion frequency a hL hfrequency s t) (show 0 ≤ p by linarith)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [Fintype ι] [Fintype κ] in
/-- Blending a positive prediction with one contracts its logarithmic
oscillation. This proves the blend step without differentiating the ratio. -/
theorem blend_log_contraction {θ x y : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hx : 0 < x) (hy : 0 < y) :
    |Real.log ((1 - θ) * x + θ) - Real.log ((1 - θ) * y + θ)| ≤
      |Real.log x - Real.log y| := by
  let d := |Real.log x - Real.log y|
  have hpos (z : ℝ) (hz : 0 < z) : 0 < (1 - θ) * z + θ := by
    by_cases hθ : θ = 1
    · simp [hθ]
    · have hfactor : 0 < 1 - θ := sub_pos.mpr (lt_of_le_of_ne hθ1 hθ)
      exact add_pos_of_pos_of_nonneg (mul_pos hfactor hz) hθ0
  have hscale (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
      (hab : Real.log a - Real.log b ≤ d) : a ≤ Real.exp d * b := by
    calc
      a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ ≤ Real.exp (d + Real.log b) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hb]
  have hxy : x ≤ Real.exp d * y := hscale x y hx hy (le_abs_self _)
  have hyx : y ≤ Real.exp d * x := hscale y x hy hx (by
    dsimp [d]
    rw [abs_sub_comm]
    exact le_abs_self _)
  have hexp : 1 ≤ Real.exp d := Real.one_le_exp (abs_nonneg _)
  have hblend (a b : ℝ) (hab : a ≤ Real.exp d * b) :
      (1 - θ) * a + θ ≤ Real.exp d * ((1 - θ) * b + θ) := by
    have h₁ := mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr hθ1)
    have h₂ := mul_le_mul_of_nonneg_right hexp hθ0
    nlinarith
  have hlogxy : Real.log ((1 - θ) * x + θ) ≤ d + Real.log ((1 - θ) * y + θ) := by
    apply (Real.log_le_iff_le_exp (hpos x hx)).2
    rw [Real.exp_add, Real.exp_log (hpos y hy)]
    exact hblend x y hxy
  have hlogyx : Real.log ((1 - θ) * y + θ) ≤ d + Real.log ((1 - θ) * x + θ) := by
    apply (Real.log_le_iff_le_exp (hpos y hy)).2
    rw [Real.exp_add, Real.exp_log (hpos x hx)]
    exact hblend y x hyx
  exact abs_le.2 ⟨by linarith, by linarith⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_DiagonalCarrier
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing a distinguished diagonal carrier

The path-child carrier is a coordinatewise unitary. Removing it leaves the
path vector fixed and subtracts its frequency from every off-path component.
This is the exact transition to the small-drop model in §9.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

omit [Fintype κ] in
theorem diagonal_carrier_identity (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (i₀ : ι) (t : ℝ) :
    diagonalFourierSum frequency a t = diagonalModulation (frequency i₀)
      (a i₀ + diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
        (fun i : RemainderIndex i₀ => a i) t) t := by
  classical
  apply PiLp.ext
  intro j
  change finiteFourierSum (fun i => frequency i j) (fun i => a i j) t =
    (a i₀ j + finiteFourierSum (fun i : RemainderIndex i₀ => frequency i j - frequency i₀ j)
      (fun i : RemainderIndex i₀ => a i j) t) * character (frequency i₀ j) t
  rw [finiteFourierSum, Fintype.sum_eq_add_sum_subtype_ne _ i₀,
    add_mul, finiteFourierSum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, character_mul]
  congr 2
  ring

theorem diagonal_carrier_norm (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (i₀ : ι) (t : ℝ) :
    ‖diagonalFourierSum frequency a t‖ =
      ‖a i₀ + diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
        (fun i : RemainderIndex i₀ => a i) t‖ := by
  rw [diagonal_carrier_identity frequency a i₀ t, norm_diagonalModulation]

theorem diagonal_carrier_energyRatio (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (i₀ : ι) (p denominator t : ℝ) :
    energyRatio p denominator (diagonalFourierSum frequency a t) =
      energyRatio p denominator
        (a i₀ + diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
          (fun i : RemainderIndex i₀ => a i) t) := by
  unfold energyRatio
  rw [diagonal_carrier_norm]

/-- A bounded off-path coefficient mass gives the relative prediction deficit
for the original phase sum, after its carrier is removed exactly. -/
theorem diagonal_prediction_deficit (frequency : ι → κ → ℝ)
    (a : ι → EuclideanSpace ℂ κ) (i₀ : ι) {p denominator B : ℝ}
    (hp : 1 ≤ p) (hd : 0 < denominator) (hB : 0 ≤ B)
    (hmass : (∑ i : RemainderIndex i₀, ‖a i‖) ≤ B)
    (hexceeds : ∃ t, 1 < energyRatio p denominator (diagonalFourierSum frequency a t)) (t : ℝ) :
    max (1 - energyRatio p denominator (diagonalFourierSum frequency a t)) 0 ≤ 2 * p * B := by
  simp_rw [diagonal_carrier_energyRatio frequency a i₀] at hexceeds ⊢
  apply fixed_path_prediction_deficit hp hd hB (a i₀)
    (fun t => diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
      (fun i : RemainderIndex i₀ => a i) t)
    (fun t => (diagonalFourierSum_bound _ _ t).trans hmass) hexceeds

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LocalMinimaSelection
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted independent-set selection by local minima of a size-biased order. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem localMinimaLaw_marginal (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (i : ι) :
    (localMinimaLaw G hG w hw).marginal i = w i / orderMass w (closedNeighborhood G i) := by
  have hevent := orderOutcomeWeight_event w Finset.univ (fun j _ => hw j)
    (localMinimaOutcome G hG) (fun s => i ∈ s.val)
  have heq : (fun l => if i ∈ (localMinimaOutcome G hG l).val then (1 : ℝ) else 0) =
      arrivalEvent (closedNeighborhood G i) i := by
    funext l
    simp [localMinimaOutcome, localMinima, arrivalEvent]
  rw [heq] at hevent
  have hfirst := orderAverage_arrivalEvent w Finset.univ (closedNeighborhood G i) i
    (fun j _ => hw j) (Finset.subset_univ _)
    ((mem_closedNeighborhood G i i).2 (Or.inl rfl))
  have hsum : (localMinimaLaw G hG w hw).marginal i =
      ∑ a : IndependentSelection G, if i ∈ a.val then
        orderOutcomeWeight w Finset.univ (localMinimaOutcome G hG) a else 0 := by
    unfold PhaseCombinatorics.FiniteSelectionLaw.marginal
    apply Finset.sum_congr rfl
    intro a _
    by_cases hi : i ∈ a.val <;> simp [localMinimaLaw, hi]
  exact hsum.trans (hevent.trans hfirst)

theorem localMinimaLaw_marginal_lower (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (m : ι → ℝ)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i) (i : ι) :
    w i / m i ≤ (localMinimaLaw G hG w hw).marginal i := by
  rw [localMinimaLaw_marginal]
  exact div_le_div_of_nonneg_left (hw i).le
    (orderMass_pos w _ (fun j _ => hw j)
      ⟨i, (mem_closedNeighborhood G i i).2 (Or.inl rfl)⟩) (hm i)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_GraphPhaseAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted prediction using the explicitly constructed independent-set law. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

attribute [local instance] Classical.propDecidable

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem graph_weighted_diagonal_prediction_average
    (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w m : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (frequency : ι → κ → ℝ)
    (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ)
    {gap D p : ℝ} (hgap : 0 < gap) (hν : FourierGap ν gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hfrequency : ∀ i j, i ≠ j → ¬G i j → ∀ k, gap ≤ |frequency i k - frequency j k|)
    (hcard : ∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hlambda : ∀ i, ‖lambda i‖ ≤ (w i / m i) ^ phaseMu D p) :
    (∫ t, (1 + ‖diagonalFourierSum frequency
      (fun i => (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i) t‖ ^ p) /
      (1 + ∑ i, l i * ‖X i‖ ^ p) ∂ν) ≤ 1 := by
  classical
  let L := localMinimaLaw G hG w hw
  have hmass (i : ι) : 0 < m i := (orderMass_pos w _ (fun j _ => hw j)
    ⟨i, (mem_closedNeighborhood G i i).2 (Or.inl rfl)⟩).trans_le (hm i)
  apply weighted_diagonal_prediction_average_at_p L ν frequency l (fun i => w i / m i)
    X lambda hgap hν hD hp
  · intro ω _ k i j hij
    have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    exact hfrequency i.val j.val hij' (ω.property i.property j.property hij') k
  · intro ω _
    exact hcard ω.val ω.property
  · exact hl
  · exact htotal
  · intro i
    exact div_pos (hw i) (hmass i)
  · exact localMinimaLaw_marginal_lower G hG w hw m hm
  · exact hlambda

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FixedPathAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform averages of the actual graph prediction

The band-limited probability is an explicit mixture. Its graph-prediction
average is at most one by the proved phase gain. Removing the path carrier
then bounds the lower deviation by the off-path coefficient mass, preserving
the relative path drop when passing to the principal probability.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

attribute [local instance] Classical.propDecidable

omit [Fintype ι] [Fintype κ] in
theorem predictionMixture_isProbability (ω τ : Measure ℝ)
    [IsProbabilityMeasure ω] [IsProbabilityMeasure τ] {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : IsProbabilityMeasure (predictionMixture ω τ η) := by
  constructor
  simp only [predictionMixture, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hη1) hη0]
  norm_num

theorem integrable_diagonal_energyRatio (μ : Measure ℝ) [IsFiniteMeasure μ]
    (frequency : ι → κ → ℝ) (a : ι → EuclideanSpace ℂ κ)
    {p : ℝ} (hp : 0 < p) (denominator : ℝ) :
    Integrable (fun t => energyRatio p denominator (diagonalFourierSum frequency a t)) μ := by
  have hmem : MemLp (diagonalFourierSum frequency a) (ENNReal.ofReal p) μ :=
    MemLp.of_bound (continuous_diagonalFourierSum frequency a).aestronglyMeasurable
      (∑ i, ‖a i‖) (Filter.Eventually.of_forall (diagonalFourierSum_bound frequency a))
  have hi : Integrable (fun t => ‖diagonalFourierSum frequency a t‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp.le] using hmem.integrable_norm_rpow'
  exact ((integrable_const 1).add hi).div_const denominator

/-- Uniform-average transfer for the actual diagonal phase sum, with the
constant denominator canceled through exact carrier removal. -/
theorem diagonal_prediction_mixture_transfer (ω τ : Measure ℝ)
    [IsProbabilityMeasure ω] [IsProbabilityMeasure τ]
    (frequency : ι → κ → ℝ) (a : ι → EuclideanSpace ℂ κ) (i₀ : ι)
    {η p denominator B : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hp : 1 ≤ p) (hd : 0 < denominator) (hB : 0 ≤ B)
    (hmass : (∑ i : RemainderIndex i₀, ‖a i‖) ≤ B)
    (haverage : (∫ t, energyRatio p denominator (diagonalFourierSum frequency a t)
      ∂predictionMixture ω τ η) ≤ 1) :
    (∫ t, energyRatio p denominator (diagonalFourierSum frequency a t) ∂ω) ≤
      1 + η / (1 - η) * (2 * p * B) := by
  have hp0 : 0 < p := by linarith
  have hω := integrable_diagonal_energyRatio ω frequency a hp0 denominator
  have hτ := integrable_diagonal_energyRatio τ frequency a hp0 denominator
  by_cases he : ∃ t, 1 < energyRatio p denominator (diagonalFourierSum frequency a t)
  · apply probability_mixture_average_le ω τ _ hη0 hη1 hω hτ _ haverage
    apply Filter.Eventually.of_forall
    intro t
    have h := diagonal_prediction_deficit frequency a i₀ hp hd hB hmass he t
    have hm := (le_max_left (1 - energyRatio p denominator (diagonalFourierSum frequency a t)) 0).trans h
    linarith
  · have hle : ∀ t, energyRatio p denominator (diagonalFourierSum frequency a t) ≤ 1 := by
      intro t
      exact le_of_not_gt (fun h => he ⟨t, h⟩)
    have hi : (∫ t, energyRatio p denominator (diagonalFourierSum frequency a t) ∂ω) ≤ 1 := by
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
        integral_mono hω (integrable_const 1) hle
    exact hi.trans (le_add_of_nonneg_right (mul_nonneg
      (div_nonneg hη0 (sub_pos.mpr hη1).le) (by positivity)))

/-- The full graph-prediction average on the principal probability, after
paying only the off-path mass in the probability-mixture error. -/
theorem graph_prediction_uniform_average
    (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w m : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i)
    (ω τ : Measure ℝ) [IsProbabilityMeasure ω] [IsProbabilityMeasure τ]
    (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (i₀ : ι) {η gap D p B : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hgap : 0 < gap)
    (hν : FourierGap (predictionMixture ω τ η) gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hfrequency : ∀ i j, i ≠ j → ¬G i j → ∀ k, gap ≤ |frequency i k - frequency j k|)
    (hcard : ∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hlambda : ∀ i, ‖lambda i‖ ≤ (w i / m i) ^ phaseMu D p)
    (hB : 0 ≤ B)
    (hmass : (∑ i : RemainderIndex i₀,
      ‖(((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i‖) ≤ B) :
    (∫ t, (1 + ‖diagonalFourierSum frequency
      (fun i => (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i) t‖ ^ p) /
        (1 + ∑ i, l i * ‖X i‖ ^ p) ∂ω) ≤
      1 + η / (1 - η) * (2 * p * B) := by
  have := predictionMixture_isProbability ω τ hη0 hη1.le
  have hphase := graph_weighted_diagonal_prediction_average G hG w m hw hm
    (predictionMixture ω τ η) frequency l X lambda hgap hν hD hp
    hfrequency hcard hl htotal hlambda
  have hden : 0 < 1 + ∑ i, l i * ‖X i‖ ^ p :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _))
  exact diagonal_prediction_mixture_transfer ω τ frequency
    (fun i => (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i) i₀
    hη0 hη1 (by linarith) hden hB hmass hphase

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierAveragingConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convolution and the exact averaging mixture

Convolution preserves the proved Fourier gap. A central mass of the kernel
minorizes the uniform law on a smaller interval. The remaining measure is
normalized into the probability used in the prediction-mixture argument.
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory ENNReal

namespace LipschitzHilbert

open PhaseCombinatorics

theorem fourierMoment_eq_charFun (μ : Measure ℝ) (s : ℝ) :
    fourierMoment μ s = charFun μ s := by
  unfold fourierMoment
  rw [charFun_apply_real]
  simp only [character, Complex.ofReal_mul]

theorem fourierGap_conv_left (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {gap : ℝ} (hgap : FourierGap μ gap) : FourierGap (μ ∗ ν) gap := by
  intro s hs
  rw [fourierMoment_eq_charFun, charFun_conv, ← fourierMoment_eq_charFun μ,
    hgap s hs, zero_mul]

theorem convolution_apply_as_translations (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    {A : Set ℝ} (hA : MeasurableSet A) :
    (μ ∗ ν) A = ∫⁻ y, μ.map (fun x => x + y) A ∂ν := by
  rw [Measure.conv_comm, ← lintegral_indicator_one hA,
    Measure.lintegral_conv (show Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) from
      measurable_one.indicator hA)]
  apply lintegral_congr
  intro y
  rw [← lintegral_indicator_one hA, lintegral_map
    (show Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) from
      measurable_one.indicator hA) (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [add_comm]

/-- Only a central part of the convolution law is needed for minorization. -/
theorem convolution_minorization (μ ν ω : Measure ℝ) [SFinite μ] [SFinite ν]
    {S : Set ℝ} (hS : MeasurableSet S) {c : ℝ≥0∞}
    (hshift : ∀ y ∈ S, c • ω ≤ μ.map (fun x => x + y)) :
    (ν S * c) • ω ≤ μ ∗ ν := by
  apply Measure.le_iff.2
  intro A hA
  rw [convolution_apply_as_translations μ ν hA, Measure.smul_apply, smul_eq_mul]
  calc
    ν S * c * ω A = ∫⁻ y in S, c * ω A ∂ν := by
      rw [lintegral_const]
      simp only [Measure.restrict_apply_univ]
      ring
    _ ≤ ∫⁻ y in S, μ.map (fun x => x + y) A ∂ν := by
      apply setLIntegral_mono' hS
      intro y hy
      simpa only [Measure.smul_apply, smul_eq_mul] using (hshift y hy) A
    _ ≤ ∫⁻ y, μ.map (fun x => x + y) A ∂ν :=
      setLIntegral_le_lintegral _ _

theorem intervalProbability_isProbability {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalProbability a b) := by
  constructor
  simp only [intervalProbability, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, Real.volume_Icc]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab))
    ENNReal.ofReal_ne_top

theorem interval_restrict_le_translated {a b pad y : ℝ} (hy : |y| ≤ pad) :
    volume.restrict (Set.Icc a b) ≤
      (volume.restrict (Set.Icc (a - pad) (b + pad))).map (fun x => x + y) := by
  have hmap : volume.map (fun x : ℝ => x + y) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self y
  calc
    volume.restrict (Set.Icc a b) =
        (volume.restrict ((fun x : ℝ => x + y) ⁻¹' Set.Icc a b)).map
          (fun x => x + y) := by
      rw [← Measure.restrict_map (by fun_prop) measurableSet_Icc, hmap]
    _ ≤ _ := Measure.map_mono (Measure.restrict_mono_set volume (by
      intro x hx
      have hy' := abs_le.mp hy
      change a ≤ x + y ∧ x + y ≤ b at hx
      constructor <;> linarith [hx.1, hx.2])) (by fun_prop)

/-- Dividing the smaller and larger interval lengths gives the precise
minorization constant for each shift in the central kernel window. -/
theorem intervalProbability_le_translated {a b pad y : ℝ} (hab : a < b)
    (hpad : 0 ≤ pad) (hy : |y| ≤ pad) :
    (ENNReal.ofReal ((b - a) / (b - a + 2 * pad))) • intervalProbability a b ≤
      (intervalProbability (a - pad) (b + pad)).map (fun x => x + y) := by
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hlarge : 0 < b - a + 2 * pad := by positivity
  have hsmall : ENNReal.ofReal (b - a) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hlen
  have heq : ENNReal.ofReal ((b - a) / (b - a + 2 * pad)) *
      (ENNReal.ofReal (b - a))⁻¹ = (ENNReal.ofReal (b - a + 2 * pad))⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hlarge, div_eq_mul_inv]
    rw [mul_right_comm, ENNReal.mul_inv_cancel hsmall ENNReal.ofReal_ne_top, one_mul]
  unfold intervalProbability
  rw [smul_smul, heq, Measure.map_smul]
  have hlarge_eq : b + pad - (a - pad) = b - a + 2 * pad := by ring
  rw [hlarge_eq]
  apply Measure.le_iff.2
  intro A _
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  exact interval_restrict_le_translated hy

/-- The averaging law is an exact probability mixture once its uniform part
has been minorized. This introduces no new analytic hypothesis. -/
theorem probability_mixture_of_minorization (ν ω : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ω] {η : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1)
    (hminor : ENNReal.ofReal (1 - η) • ω ≤ ν) :
    ∃ τ : Measure ℝ, IsProbabilityMeasure τ ∧ predictionMixture ω τ η = ν := by
  let c : ℝ≥0∞ := ENNReal.ofReal (1 - η)
  let d : ℝ≥0∞ := ENNReal.ofReal η
  let τ := d⁻¹ • (ν - c • ω)
  have hd0 : d ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hη0
  have hdtop : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have : IsFiniteMeasure (c • ω) := by
    constructor
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_lt_top
  have hdiff : (ν - c • ω) Set.univ = d := by
    rw [Measure.sub_apply MeasurableSet.univ hminor]
    simp only [measure_univ, Measure.smul_apply, smul_eq_mul, mul_one]
    dsimp only [c, d]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1 - η)]
    congr 1
    ring
  have hτ : IsProbabilityMeasure τ := by
    constructor
    change d⁻¹ * (ν - c • ω) Set.univ = 1
    rw [hdiff, ENNReal.inv_mul_cancel hd0 hdtop]
  refine ⟨τ, hτ, ?_⟩
  unfold predictionMixture
  change c • ω + d • (d⁻¹ • (ν - c • ω)) = ν
  rw [smul_smul, ENNReal.mul_inv_cancel hd0 hdtop, one_smul, add_comm]
  exact Measure.sub_add_cancel_of_le hminor

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierAveragingTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quantitative tails of the averaging kernel

The Fourier-square kernel has a finite second moment, proved directly from
its Schwartz seminorms. This gives the polynomial tail estimate used in the
near-uniform interval convolution, with a constant from a fixed kernel.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem fourierSquare_second_moment_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fun t => t ^ 2 * fourierSquare h t) := by
  have hbound (t : ℝ) : t ^ 2 * fourierSquare h t ≤
      SchwartzMap.seminorm ℝ 2 0 (𝓕 h) * ‖𝓕 h t‖ := by
    have hb := mul_le_mul_of_nonneg_right
      (SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 h) 2 t) (norm_nonneg (𝓕 h t))
    rw [Real.norm_eq_abs, sq_abs] at hb
    simpa only [fourierSquare, mul_assoc, pow_two] using hb
  exact ((𝓕 h).integrable.norm.const_mul _).mono'
    ((continuous_id.pow 2).mul (fourierSquare_continuous h)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg t) (fourierSquare_nonneg h t))] using hbound t)

theorem fourierAveraging_second_moment_integrable (h : SchwartzMap ℝ ℂ) :
    Integrable (fun t : ℝ => t ^ 2) (fourierAveragingMeasure h) := by
  unfold fourierAveragingMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (fourierAveragingDensity_continuous h).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (fourierAveragingDensity_nonneg h _), smul_eq_mul]
  convert (fourierSquare_second_moment_integrable h).div_const
    (∫ x, fourierSquare h x) using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  unfold fourierAveragingDensity
  ring

/-- The tail outside a central interval is controlled by the second moment. -/
theorem probability_central_mass_of_second_moment (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hint : Integrable (fun t : ℝ => t ^ 2) μ)
    {R : ℝ} (hR : 0 < R) :
    1 - (∫ t : ℝ, t ^ 2 ∂μ) / R ^ 2 ≤ μ.real (Set.Icc (-R) R) := by
  let A : Set ℝ := Set.Icc (-R) R
  have hA : MeasurableSet A := measurableSet_Icc
  have htail := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun t : ℝ => sq_nonneg t) hint (R ^ 2)
  have hsub : Aᶜ ⊆ {t : ℝ | R ^ 2 ≤ t ^ 2} := by
    intro t ht
    have hnot : ¬(-R ≤ t ∧ t ≤ R) := ht
    rcases not_and_or.mp hnot with hleft | hright
    · have hlt : t < -R := lt_of_not_ge hleft
      have hh := mul_nonneg (show 0 ≤ -t - R by linarith) (show 0 ≤ -t + R by linarith)
      exact show R ^ 2 ≤ t ^ 2 by nlinarith [hh]
    · have hlt : R < t := lt_of_not_ge hright
      have hh := mul_nonneg (show 0 ≤ t - R by linarith) (show 0 ≤ t + R by linarith)
      exact show R ^ 2 ≤ t ^ 2 by nlinarith [hh]
  have hmono : μ.real Aᶜ ≤ μ.real {t : ℝ | R ^ 2 ≤ t ^ 2} :=
    measureReal_mono hsub
  have hcomp : μ.real Aᶜ = 1 - μ.real A := by
    rw [measureReal_compl hA, probReal_univ]
  rw [hcomp] at hmono
  have hdiv : μ.real {t : ℝ | R ^ 2 ≤ t ^ 2} ≤
      (∫ t : ℝ, t ^ 2 ∂μ) / R ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hR)).2 (by nlinarith [htail])
  dsimp only [A] at hmono
  linarith

/-- Dilation changes the Fourier gap by the reciprocal physical scale. -/
theorem fourierGap_map_dilation (μ : Measure ℝ) [IsFiniteMeasure μ]
    {gap scale : ℝ} (hscale : 0 < scale) (hgap : PhaseCombinatorics.FourierGap μ gap) :
    PhaseCombinatorics.FourierGap (μ.map (fun t => scale * t)) (gap / scale) := by
  intro s hs
  unfold PhaseCombinatorics.fourierMoment
  rw [integral_map (by fun_prop) (PhaseCombinatorics.continuous_character s).aestronglyMeasurable]
  have hchar (t : ℝ) : PhaseCombinatorics.character s (scale * t) =
      PhaseCombinatorics.character (scale * s) t := by
    unfold PhaseCombinatorics.character
    have heq : s * (scale * t) = scale * s * t := by ring
    rw [heq]
  simp only [hchar]
  apply hgap
  rw [abs_mul, abs_of_pos hscale]
  have h := (div_le_iff₀ hscale).1 (show gap / 4 / scale ≤ |s| by
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    ring)
  nlinarith

theorem second_moment_map_dilation (μ : Measure ℝ) [IsFiniteMeasure μ] (scale : ℝ) :
    (∫ t : ℝ, t ^ 2 ∂μ.map (fun t => scale * t)) =
      scale ^ 2 * ∫ t : ℝ, t ^ 2 ∂μ := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  exact integral_const_mul _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierAveragingMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Near-uniform Fourier-supported averaging

The averaging probability in §9 is the convolution of the uniform law on
an expanded interval with a dilated, fixed Fourier-square probability.
Its explicit loss is expansion/length plus a second-moment tail.
-/

noncomputable section

open MeasureTheory
open scoped MeasureTheory ENNReal

namespace LipschitzHilbert

open PhaseCombinatorics

theorem interval_convolution_minorization (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b pad η : ℝ} (hab : a < b) (hpad : 0 ≤ pad)
    (hmass : 1 - η ≤ μ.real (Set.Icc (-pad) pad) *
      ((b - a) / (b - a + 2 * pad))) :
    ENNReal.ofReal (1 - η) • intervalProbability a b ≤
      intervalProbability (a - pad) (b + pad) ∗ μ := by
  have : IsProbabilityMeasure (intervalProbability (a - pad) (b + pad)) :=
    intervalProbability_isProbability (by linarith)
  have hminor := convolution_minorization
    (intervalProbability (a - pad) (b + pad)) μ (intervalProbability a b)
    measurableSet_Icc (fun y hy => intervalProbability_le_translated hab hpad (abs_le.mpr hy))
  have hcoeff : ENNReal.ofReal (1 - η) ≤ μ (Set.Icc (-pad) pad) *
      ENNReal.ofReal ((b - a) / (b - a + 2 * pad)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _), ← measureReal_def,
      ← ENNReal.ofReal_mul measureReal_nonneg]
    exact ENNReal.ofReal_le_ofReal hmass
  refine le_trans ?_ hminor
  apply Measure.le_iff.2
  intro A _
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr

theorem expansion_tail_loss {H pad tail mass : ℝ}
    (hH : 0 < H) (hpad : 0 ≤ pad) (htail : 0 ≤ tail) (hmass : 1 - tail ≤ mass) :
    1 - (2 * pad / H + tail) ≤ mass * (H / (H + 2 * pad)) := by
  have hlarge : 0 < H + 2 * pad := by positivity
  have hratio : 0 ≤ H / (H + 2 * pad) := by positivity
  have hm := mul_le_mul_of_nonneg_right hmass hratio
  have hlower : 1 - (2 * pad / H + tail) ≤
      (1 - tail) * (H / (H + 2 * pad)) := by
    have heq : (1 - tail) * (H / (H + 2 * pad)) - (1 - (2 * pad / H + tail)) =
        (2 * pad * (2 * pad + H * tail)) / (H * (H + 2 * pad)) := by
      field_simp
      ring
    have hnonneg : 0 ≤ (2 * pad * (2 * pad + H * tail)) / (H * (H + 2 * pad)) := by
      positivity
    rw [← heq] at hnonneg
    linarith
  exact hlower.trans hm

/-- Explicit near-uniform probability and exact remainder. The only input
about the base kernel is its proved probability, Fourier gap, and moment. -/
theorem interval_fourier_mixture (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hmoment : Integrable (fun t : ℝ => t ^ 2) μ)
    {a b pad scale gap : ℝ} (hab : a < b) (hpad : 0 < pad) (hscale : 0 < scale)
    (hgap : FourierGap μ gap)
    (hsmall : 2 * pad / (b - a) +
      scale ^ 2 * (∫ t : ℝ, t ^ 2 ∂μ) / pad ^ 2 < 1) :
    let η := 2 * pad / (b - a) + scale ^ 2 * (∫ t : ℝ, t ^ 2 ∂μ) / pad ^ 2
    0 < η ∧ η < 1 ∧ ∃ τ : Measure ℝ, IsProbabilityMeasure τ ∧
      predictionMixture (intervalProbability a b) τ η =
        intervalProbability (a - pad) (b + pad) ∗ μ.map (fun t => scale * t) ∧
      FourierGap (predictionMixture (intervalProbability a b) τ η) (gap / scale) := by
  dsimp only
  let η := 2 * pad / (b - a) + scale ^ 2 * (∫ t : ℝ, t ^ 2 ∂μ) / pad ^ 2
  have hH : 0 < b - a := sub_pos.mpr hab
  have hmoment0 : 0 ≤ ∫ t : ℝ, t ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hη0 : 0 < η := by dsimp [η]; positivity
  have : IsProbabilityMeasure (intervalProbability a b) := intervalProbability_isProbability hab
  have : IsProbabilityMeasure (intervalProbability (a - pad) (b + pad)) :=
    intervalProbability_isProbability (by linarith)
  have : IsProbabilityMeasure (μ.map (fun t => scale * t)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have hint : Integrable (fun t : ℝ => t ^ 2) (μ.map (fun t => scale * t)) := by
    apply (integrable_map_measure (by fun_prop) (by fun_prop)).2
    simpa only [Function.comp_def, mul_pow] using hmoment.const_mul (scale ^ 2)
  have hmass := probability_central_mass_of_second_moment
    (μ.map (fun t => scale * t)) hint hpad
  rw [second_moment_map_dilation] at hmass
  have hminor := interval_convolution_minorization (μ.map (fun t => scale * t)) hab hpad.le
    (expansion_tail_loss hH hpad.le (by positivity) hmass)
  obtain ⟨τ, hτ, hmix⟩ := probability_mixture_of_minorization
    (intervalProbability (a - pad) (b + pad) ∗ μ.map (fun t => scale * t))
    (intervalProbability a b) hη0 hsmall hminor
  refine ⟨hη0, hsmall, τ, hτ, hmix, ?_⟩
  rw [hmix, Measure.conv_comm]
  exact fourierGap_conv_left _ _ (fourierGap_map_dilation μ hscale hgap)

/-- A fixed actual Schwartz-square kernel suffices for all interval lengths
and dilation parameters. Its second moment is a single finite constant. -/
theorem exists_fixed_fourier_averaging_kernel :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ FourierGap μ 1 ∧
      Integrable (fun t : ℝ => t ^ 2) μ := by
  obtain ⟨h, hh, hprob, hgap⟩ := exists_fourierAveragingMeasure (by norm_num : 0 < (1 : ℝ))
  exact ⟨fourierAveragingMeasure h, hprob, hgap, fourierAveraging_second_moment_integrable h⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FourierAveragingScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The source scales for the near-uniform averaging probability

Write `h = G^(-1/16)`. The expansion padding is `H*h/2` and the
physical kernel scale is `H*h²`. The resulting loss is exactly
`h + 4*M*h²`, hence at most a fixed constant times `h`.
-/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

open PhaseCombinatorics

theorem averaging_loss_at_source_scales {H h M : ℝ} (hH : 0 < H) (hh : 0 < h) :
    2 * (H * h / 2) / H + (H * h ^ 2) ^ 2 * M / (H * h / 2) ^ 2 =
      h + 4 * M * h ^ 2 := by
  field_simp [hH.ne', hh.ne']
  ring

theorem averaging_source_loss_bound {h M : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hM : 0 ≤ M) :
    h + 4 * M * h ^ 2 ≤ (1 + 4 * M) * h := by
  have hs : h ^ 2 ≤ h := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4 * M)]

/-- A universal averaging constant and a genuine probability remainder at
every source scale. This discharges the probability-mixture existence
obligation used by the graph prediction argument. -/
theorem exists_source_scale_averaging_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b h : ℝ), a < b → 0 < h → h ≤ 1 → C * h < 1 / 2 →
      ∃ (η : ℝ) (τ : Measure ℝ), 0 < η ∧ η ≤ C * h ∧ η < 1 / 2 ∧
        IsProbabilityMeasure τ ∧
        FourierGap (predictionMixture (intervalProbability a b) τ η)
          (1 / ((b - a) * h ^ 2)) := by
  obtain ⟨μ, hprob, hgap, hmoment⟩ := exists_fixed_fourier_averaging_kernel
  let M := ∫ t : ℝ, t ^ 2 ∂μ
  have hM : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  refine ⟨1 + 4 * M, by linarith, ?_⟩
  intro a b h hab hh0 hh1 hsmall
  have hH : 0 < b - a := sub_pos.mpr hab
  have hpad : 0 < (b - a) * h / 2 := by positivity
  have hscale : 0 < (b - a) * h ^ 2 := by positivity
  let η := h + 4 * M * h ^ 2
  have hηbound : η ≤ (1 + 4 * M) * h := averaging_source_loss_bound hh0.le hh1 hM
  have hηsmall : η < 1 / 2 := hηbound.trans_lt hsmall
  have hformula := averaging_loss_at_source_scales (M := M) hH hh0
  have hsmall' : 2 * ((b - a) * h / 2) / (b - a) +
      ((b - a) * h ^ 2) ^ 2 * (∫ t : ℝ, t ^ 2 ∂μ) / ((b - a) * h / 2) ^ 2 < 1 := by
    rw [hformula]
    exact hηsmall.trans (by norm_num)
  obtain ⟨hη0, _, τ, hτ, _, hν⟩ := interval_fourier_mixture μ hmoment hab hpad hscale hgap hsmall'
  rw [hformula] at hη0 hν
  exact ⟨η, τ, hη0, hηbound, hηsmall, hτ, hν⟩

/-- The manuscript's powers of `G`, with a universal error coefficient. -/
theorem exists_power_scale_averaging_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b G : ℝ), a < b → 1 ≤ G →
      C * G ^ (-(1 / 16 : ℝ)) < 1 / 2 →
      ∃ (η : ℝ) (τ : Measure ℝ), 0 < η ∧ η ≤ C * G ^ (-(1 / 16 : ℝ)) ∧
        η < 1 / 2 ∧ IsProbabilityMeasure τ ∧
        FourierGap (predictionMixture (intervalProbability a b) τ η)
          (1 / ((b - a) * G ^ (-(1 / 8 : ℝ)))) := by
  obtain ⟨C, hC, hmain⟩ := exists_source_scale_averaging_constant
  refine ⟨C, hC, ?_⟩
  intro a b G hab hG hsmall
  have hG0 : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hh0 : 0 < G ^ (-(1 / 16 : ℝ)) := Real.rpow_pos_of_pos hG0 _
  have hh1 : G ^ (-(1 / 16 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
  obtain ⟨η, τ, hη0, hηC, hηhalf, hτ, hν⟩ := hmain a b _ hab hh0 hh1 hsmall
  have hsquare : (G ^ (-(1 / 16 : ℝ))) ^ 2 = G ^ (-(1 / 8 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hG0.le]
    norm_num
  rw [hsquare] at hν
  exact ⟨η, τ, hη0, hηC, hηhalf, hτ, hν⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_PredictionCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Measurable step-supremum prediction factors

Inside one root cell, a finite measurable partition gives an explicit
step supremum. Logarithmic cell oscillation controls its normalization,
producing the actual nonnegative, measurable, average-one factor.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

omit [MeasurableSpace α] [Fintype κ] in
theorem predictionStepSup_constant (B : α → ℝ) (I : Set α) (P : α → κ)
    {x y : α} (hxy : P x = P y) : predictionStepSup B I P x = predictionStepSup B I P y := by
  simp only [predictionStepSup, hxy]

theorem measurable_finite_profile (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) (c : κ → ℝ) :
    Measurable (fun x => c (P x)) := by
  classical
  have heq : (fun x => c (P x)) =
      fun x => ∑ i, ({y | P y = i}.indicator (fun _ => c i)) x := by
    funext x
    symm
    rw [Finset.sum_eq_single (P x)]
    · simp
    · intro i _ hi
      exact Set.indicator_of_notMem (show x ∉ {y | P y = i} from fun h => hi h.symm) _
    · simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hP i)

theorem measurable_predictionStepSup (B : α → ℝ) (I : Set α) (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) : Measurable (predictionStepSup B I P) :=
  measurable_finite_profile P hP (fun i => predictionCellSup B (predictionCell I P i))

theorem integrable_predictionStepSup (μ : Measure α) [IsFiniteMeasure μ]
    (B : α → ℝ) (I : Set α) (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) : Integrable (predictionStepSup B I P) μ :=
  integrable_finite_profile μ P hP (fun i => predictionCellSup B (predictionCell I P i))

omit [MeasurableSpace α] [Fintype κ] in
theorem predictionStepSup_bounds (B : α → ℝ) (I : Set α) (P : α → κ)
    (hpositive : ∀ x ∈ I, 0 < B x) {c : ℝ}
    (hosc : ∀ x ∈ I, ∀ y ∈ I, P y = P x → |Real.log (B y) - Real.log (B x)| ≤ c)
    {x : α} (hx : x ∈ I) :
    B x ≤ predictionStepSup B I P x ∧ predictionStepSup B I P x ≤ Real.exp c * B x := by
  exact prediction_cell_sup_bounds B (predictionCell I P (P x)) ⟨hx, rfl⟩
    (fun y hy => hpositive y hy.1) (fun y hy => hosc x hx y hy.1 hy.2)

omit [MeasurableSpace α] [Fintype κ] in
theorem predictionStepSup_nonnegative (B : α → ℝ) (I : Set α) (P : α → κ)
    (hpositive : ∀ x ∈ I, 0 < B x) {c : ℝ}
    (hosc : ∀ x ∈ I, ∀ y ∈ I, P y = P x → |Real.log (B y) - Real.log (B x)| ≤ c)
    (x : α) : 0 ≤ predictionStepSup B I P x := by
  classical
  by_cases hcell : ∃ y, y ∈ I ∧ P y = P x
  · obtain ⟨y, hy, hxy⟩ := hcell
    rw [← predictionStepSup_constant B I P hxy]
    exact (hpositive y hy).le.trans (predictionStepSup_bounds B I P hpositive hosc hy).1
  · have he : predictionCell I P (P x) = ∅ := by
      ext y
      simp only [predictionCell, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy hxy
      exact hcell ⟨y, hy, hxy⟩
    simp [predictionStepSup, he, predictionCellSup]

/-- Construct the normalized step factor explicitly, including measurability,
constancy on finer cells, integral at most one, and the pointwise comparison. -/
theorem exists_normalized_prediction_steps (μ : Measure α) [IsProbabilityMeasure μ]
    (B : α → ℝ) (I : Set α) (P : α → κ)
    (hP : ∀ i, MeasurableSet {x | P x = i}) (hsupport : ∀ᵐ x ∂μ, x ∈ I)
    (hpositive : ∀ x ∈ I, 0 < B x) (hB : Integrable B μ)
    {a b u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (haverage : ∫ x, B x ∂μ ≤ 1 + a * u)
    (hosc : ∀ x ∈ I, ∀ y ∈ I, P y = P x → |Real.log (B y) - Real.log (B x)| ≤ b * u) :
    ∃ Γ : α → ℝ, Measurable Γ ∧ Integrable Γ μ ∧ (∀ x, 0 ≤ Γ x) ∧
      (∫ x, Γ x ∂μ) ≤ 1 ∧ (∀ x y, P x = P y → Γ x = Γ y) ∧
      ∀ x ∈ I, B x ≤ Real.exp ((a + b) * u) * Γ x := by
  let S := predictionStepSup B I P
  let Γ := normalizedPrediction μ S
  have hS : Integrable S μ := integrable_predictionStepSup μ B I P hP
  have hS0 : ∀ x, 0 ≤ S x := predictionStepSup_nonnegative B I P hpositive hosc
  have hmajorant : ∀ᵐ x ∂μ, S x ≤ Real.exp (b * u) * B x := by
    filter_upwards [hsupport] with x hx
    exact (predictionStepSup_bounds B I P hpositive hosc hx).2
  have hcost := step_normalization_cost μ B S ha hb hu hB hS hmajorant haverage
  have hnorm := predictionNormalizer_pos μ S
  refine ⟨Γ, ?_, ?_, ?_, normalizedPrediction_average_le_one μ S, ?_, ?_⟩
  · exact (measurable_predictionStepSup B I P hP).div_const _
  · exact hS.div_const _
  · exact normalizedPrediction_nonnegative μ S hS0
  · intro x y hxy
    unfold Γ normalizedPrediction
    exact congrArg (fun z : ℝ => z / predictionNormalizer μ S)
      (predictionStepSup_constant B I P hxy)
  · intro x hx
    have hm : predictionNormalizer μ S ≤ Real.exp ((a + b) * u) :=
      (Real.log_le_iff_le_exp hnorm).mp hcost
    have hrestore : S x = predictionNormalizer μ S * Γ x := by
      dsimp [Γ, normalizedPrediction]
      field_simp
    calc
      B x ≤ S x := (predictionStepSup_bounds B I P hpositive hosc hx).1
      _ = predictionNormalizer μ S * Γ x := hrestore
      _ ≤ Real.exp ((a + b) * u) * Γ x :=
        mul_le_mul_of_nonneg_right hm (normalizedPrediction_nonnegative μ S hS0 x)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_GraphPredictionFactor
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A constructed step factor for the graph prediction

For the fixed snapshot model of §9, combine graph selection, carrier removal,
probability-mixture transfer, finite-cell supremums, and exact normalization.
The resulting factor is an actual measurable step function of average at most
one. Every loss in its comparison retains the off-path mass parameter `u`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]

attribute [local instance] Classical.propDecidable

omit [Fintype ι] [Fintype κ] [Fintype σ] in
theorem positive_blend {θ x : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx : 0 < x) :
    0 < (1 - θ) * x + θ := by
  by_cases hθ : θ = 1
  · simp [hθ]
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne hθ1 hθ)) hx) hθ0

/-- The finite-snapshot graph prediction admits a measurable normalized step
factor, with only a relative off-path-mass loss in its pointwise comparison. -/
theorem graph_prediction_step_factor
    (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w m : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i)
    (ω τ : Measure ℝ) [IsProbabilityMeasure ω] [IsProbabilityMeasure τ]
    (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (i₀ : ι) (I : Set ℝ) (P : ℝ → σ)
    {η gap D p K u L H θ : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hgap : 0 < gap)
    (hν : FourierGap (predictionMixture ω τ η) gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hfrequency : ∀ i j, i ≠ j → ¬G i j → ∀ k, gap ≤ |frequency i k - frequency j k|)
    (hcard : ∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hlambda : ∀ i, ‖lambda i‖ ≤ (w i / m i) ^ phaseMu D p)
    (hK : 0 ≤ K) (hu : 0 ≤ u) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hmass : (∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lambda D p i‖) ≤ K * u)
    (hfrequencyBound : ∀ i : RemainderIndex i₀, ∀ j, |frequency i j - frequency i₀ j| ≤ L)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ∀ i, MeasurableSet {t | P t = i}) (hsupport : ∀ᵐ t ∂ω, t ∈ I)
    (hdiameter : ∀ s ∈ I, ∀ t ∈ I, P t = P s → |t - s| ≤ H) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ Integrable Γ ω ∧ (∀ t, 0 ≤ Γ t) ∧
      (∫ t, Γ t ∂ω) ≤ 1 ∧ (∀ s t, P s = P t → Γ s = Γ t) ∧
      ∀ t ∈ I, (1 - θ) * graphPredictionValue frequency l X lambda D p t + θ ≤
        Real.exp (((η / (1 - η) * (2 * p * K)) + p * L * K * H) * u) * Γ t := by
  let a := predictionCoefficients l X lambda D p
  let denominator := 1 + ∑ i, l i * ‖X i‖ ^ p
  let β := graphPredictionValue frequency l X lambda D p
  let B := fun t => (1 - θ) * β t + θ
  have hp1 : 1 ≤ p := by linarith
  have hd : 0 < denominator := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _))
  have hβpos (t : ℝ) : 0 < β t := energyRatio_pos hd _
  have hβint : Integrable β ω := integrable_diagonal_energyRatio ω frequency a (by linarith) denominator
  have hBint : Integrable B ω := (hβint.const_mul _).add (integrable_const θ)
  have hβaverage : (∫ t, β t ∂ω) ≤ 1 + (η / (1 - η) * (2 * p * K)) * u := by
    have h := graph_prediction_uniform_average G hG w m hw hm ω τ frequency l X lambda i₀
      hη0 hη1 hgap hν hD hp hfrequency hcard hl htotal hlambda (mul_nonneg hK hu) hmass
    change (∫ t, β t ∂ω) ≤ 1 + η / (1 - η) * (2 * p * (K * u)) at h
    simpa only [mul_assoc] using h
  have herror : 0 ≤ η / (1 - η) * (2 * p * K) := by positivity
  have hBaverage : (∫ t, B t ∂ω) ≤ 1 + (η / (1 - η) * (2 * p * K)) * u := by
    dsimp only [B]
    rw [integral_add (hβint.const_mul _) (integrable_const _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hmul := mul_le_mul_of_nonneg_left hβaverage (sub_nonneg.mpr hθ1)
    have hnonneg := mul_nonneg herror hu
    have hdrop := mul_nonneg hθ0 hnonneg
    nlinarith
  have hcarrier (t : ℝ) : β t = energyRatio p denominator
      (a i₀ + diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
        (fun i : RemainderIndex i₀ => a i) t) :=
    diagonal_carrier_energyRatio frequency a i₀ p denominator t
  have hosc : ∀ s ∈ I, ∀ t ∈ I, P t = P s →
      |Real.log (B t) - Real.log (B s)| ≤ (p * L * K * H) * u := by
    intro s hs t ht hst
    have hb := blend_log_contraction hθ0 hθ1 (hβpos t) (hβpos s)
    have hlog : |Real.log (β t) - Real.log (β s)| ≤
        p * L * (∑ i : RemainderIndex i₀, ‖a i‖) * |t - s| := by
      rw [hcarrier t, hcarrier s]
      exact fixed_path_diagonal_log_motion (diagonalRemainderFrequency frequency i₀)
        (fun i : RemainderIndex i₀ => a i) (a i₀) hL hp1 hd hfrequencyBound s t
    refine hb.trans (hlog.trans ?_)
    calc
      _ ≤ p * L * (∑ i : RemainderIndex i₀, ‖a i‖) * H :=
        mul_le_mul_of_nonneg_left (hdiameter s hs t ht hst) (by positivity)
      _ ≤ p * L * (K * u) * H :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by positivity)) hH
      _ = _ := by ring
  exact exists_normalized_prediction_steps ω B I P hP hsupport
    (fun t _ => positive_blend hθ0 hθ1 (hβpos t)) hBint herror (by positivity) hu hBaverage hosc

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FiniteLineGrid
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite line partitions, nested at an integer branching ratio. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

namespace FiniteLineGrid

attribute [local instance] Classical.propDecidable

/-- Two points of one finer cell differ by at most its mesh width. -/
theorem same_index_distance (g : FiniteLineGrid) {level : ℕ} (hlevel : level ≤ g.depth)
    {x y : ℝ} (hx : x ∈ g.root) (hy : y ∈ g.root)
    (hxy : g.index level x = g.index level y) :
    |x - y| ≤ g.width / (g.branching : ℝ) ^ level := by
  have hG : 0 < (g.branching : ℝ) := by exact_mod_cast g.branching_pos
  have hp : 0 < (g.branching : ℝ) ^ level := pow_pos hG _
  have hxn : 0 ≤ ((x - g.origin) / g.width) * (g.branching : ℝ) ^ level :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hx.1) g.width_pos.le) hp.le
  have hyn : 0 ≤ ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hy.1) g.width_pos.le) hp.le
  have hf : ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ =
      ⌊((y - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ := by
    have h := congrArg Fin.val hxy
    simpa only [index, Nat.min_eq_left hlevel, rawIndex, ite_eq_left hx, ite_eq_left hy] using h
  have hxlo := Nat.floor_le hxn
  have hylo := Nat.floor_le hyn
  have hxhi := Nat.lt_floor_add_one (((x - g.origin) / g.width) * (g.branching : ℝ) ^ level)
  have hyhi := Nat.lt_floor_add_one (((y - g.origin) / g.width) * (g.branching : ℝ) ^ level)
  rw [hf] at hxlo hxhi
  have hnorm : |((x - g.origin) / g.width) * (g.branching : ℝ) ^ level -
      ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have heq : ((x - g.origin) / g.width) * (g.branching : ℝ) ^ level -
      ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level =
      (x - y) * ((g.branching : ℝ) ^ level / g.width) := by ring
  rw [heq, abs_mul, abs_of_pos (div_pos hp g.width_pos)] at hnorm
  apply (le_div_iff₀ hp).mpr
  have h := mul_le_mul_of_nonneg_right hnorm g.width_pos.le
  calc
    |x - y| * (g.branching : ℝ) ^ level =
        (|x - y| * ((g.branching : ℝ) ^ level / g.width)) * g.width := by
          field_simp [g.width_pos.ne']
    _ ≤ 1 * g.width := h
    _ = g.width := one_mul _

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_LineGridPrediction
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The snapshot prediction factor on the actual finite line-cell mesh. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

attribute [local instance] Classical.propDecidable

theorem intervalProbability_ae_mem_Ico (a b : ℝ) :
    ∀ᵐ x ∂intervalProbability a b, x ∈ Ico a b := by
  apply Measure.ae_smul_measure
  have hmem : ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Icc a b :=
    ae_restrict_mem measurableSet_Icc
  have hne : ∀ᵐ x ∂volume.restrict (Icc a b), x ≠ b :=
    (show ∀ᵐ x : ℝ ∂volume, x ≠ b by
      rw [ae_iff]
      have hs : {x : ℝ | ¬x ≠ b} = {b} := by ext x; simp
      rw [hs]
      exact measure_singleton b).filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [hmem, hne] with x hx hxb
  exact ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩

namespace FiniteLineGrid

/-- Apply the constructed graph predictor to a finite uniform line grid.
There is no free measurable partition or cell-diameter hypothesis here. -/
theorem graph_prediction_step {ι κ : Type*} [Fintype ι] [Fintype κ]
    (grid : FiniteLineGrid) (level : ℕ) (hlevel : level ≤ grid.depth)
    (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w m : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i)
    (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (i₀ : ι)
    {η gap D p K u freqBound θ : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hgap : 0 < gap)
    (hν : FourierGap (predictionMixture
      (intervalProbability grid.origin (grid.origin + grid.width)) τ η) gap)
    (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hfrequency : ∀ i j, i ≠ j → ¬G i j → ∀ k, gap ≤ |frequency i k - frequency j k|)
    (hcard : ∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hlambda : ∀ i, ‖lambda i‖ ≤ (w i / m i) ^ phaseMu D p)
    (hK : 0 ≤ K) (hu : 0 ≤ u) (hfreqBound : 0 ≤ freqBound)
    (hmass : (∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lambda D p i‖) ≤ K * u)
    (hfrequencyBound : ∀ i : RemainderIndex i₀, ∀ j,
      |frequency i j - frequency i₀ j| ≤ freqBound)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧
      Integrable Γ (intervalProbability grid.origin (grid.origin + grid.width)) ∧
      (∀ t, 0 ≤ Γ t) ∧
      (∫ t, Γ t ∂intervalProbability grid.origin (grid.origin + grid.width)) ≤ 1 ∧
      (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
      ∀ t ∈ grid.root, (1 - θ) * graphPredictionValue frequency l X lambda D p t + θ ≤
        Real.exp (((η / (1 - η) * (2 * p * K)) +
          p * freqBound * K * (grid.width / (grid.branching : ℝ) ^ level)) * u) * Γ t := by
  let : IsProbabilityMeasure (intervalProbability grid.origin (grid.origin + grid.width)) :=
    intervalProbability_isProbability (by linarith [grid.width_pos])
  exact graph_prediction_step_factor G hG w m hw hm
    (intervalProbability grid.origin (grid.origin + grid.width)) τ frequency l X lambda
    i₀ grid.root (grid.index level) hη0 hη1 hgap hν hD hp hfrequency hcard hl htotal hlambda
    hK hu hfreqBound (div_nonneg grid.width_pos.le (pow_nonneg (Nat.cast_nonneg _) _))
    hmass hfrequencyBound hθ0 hθ1 (grid.measurable_index_fiber level)
    (intervalProbability_ae_mem_Ico _ _) (fun s hs t ht hst =>
      grid.same_index_distance hlevel ht hs hst)

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual rounded dyadic parameters in the manuscript. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert.SourceParameters

theorem log_step_bounds {L : ℝ} (hL : 0 ≤ L) :
    L ^ (7 / 10 : ℝ) ≤ Real.log (step L) ∧
      Real.log (step L) ≤ L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 ≤ L ^ (7 / 10 : ℝ) / (2 * Real.log 2) := by positivity
  have hlo := Nat.le_ceil (L ^ (7 / 10 : ℝ) / (2 * Real.log 2))
  have hhi := (Nat.ceil_lt_add_one hr).le
  rw [step, Real.log_pow, stepExponent, Nat.cast_mul, Nat.cast_ofNat]
  constructor
  · have h := mul_le_mul_of_nonneg_right hlo (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : L ^ (7 / 10 : ℝ) / (2 * Real.log 2) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) := div_mul_cancel₀ _ (by positivity)
    rw [heq] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hhi (show 0 ≤ 2 * Real.log 2 by positivity)
    have heq : (L ^ (7 / 10 : ℝ) / (2 * Real.log 2) + 1) * (2 * Real.log 2) =
        L ^ (7 / 10 : ℝ) + 2 * Real.log 2 := by
      rw [add_mul, div_mul_cancel₀ _ (by positivity), one_mul]
    rw [heq] at h
    nlinarith

end LipschitzHilbert.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructed near-uniform averaging at the actual rounded source scale. -/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace LipschitzHilbert

open PhaseCombinatorics

theorem source_step_tendsto_atTop : Tendsto SourceParameters.step atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ ((Real.tendsto_exp_atTop).comp
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  have h := Real.exp_le_exp.mpr (SourceParameters.log_step_bounds hL).1
  simpa only [Function.comp_apply, Real.exp_log (SourceParameters.step_pos L)] using h

/-- At every sufficiently large source parameter and every finite line
interval, the Fourier-gap averaging law is an actual convex mixture
of the uniform interval law and a probability remainder. -/
theorem exists_source_averaging_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ L : ℝ in atTop, ∀ a b : ℝ, a < b →
      ∃ (eta : ℝ) (remainder : Measure ℝ),
        0 < eta ∧ eta ≤ C * SourceParameters.step L ^ (-(1 / 16 : ℝ)) ∧
        eta < 1 / 2 ∧ IsProbabilityMeasure remainder ∧
        FourierGap (predictionMixture (intervalProbability a b) remainder eta)
          (1 / ((b - a) * SourceParameters.step L ^ (-(1 / 8 : ℝ)))) := by
  obtain ⟨C, hC, haverage⟩ := exists_power_scale_averaging_constant
  refine ⟨C, hC, ?_⟩
  have hdecay : Tendsto (fun L => C * SourceParameters.step L ^ (-(1 / 16 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (tendsto_const_nhds (x := C)).mul
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp
        source_step_tendsto_atTop)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with L hL hsmall
  intro a b hab
  exact haverage a b (SourceParameters.step L) hab
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hsmall

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourceGridPrediction
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the snapshot predictor at the manuscript's averaging scale.
The near-uniform probability and its remainder are supplied by the
Fourier kernel construction, before the graph and line grid are chosen. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem exists_source_grid_prediction :
    ∃ C L0 : ℝ, 1 ≤ C ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
      ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
      ∀ (w m : ι → ℝ), (∀ i, 0 < w i) →
      (∀ i, orderMass w (closedNeighborhood G i) ≤ m i) →
      ∀ (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
        (lambda : ι → ℂ) (i₀ : ι) (D p K u freqBound θ : ℝ),
      1 ≤ D → 4 ≤ p →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) ≤
          |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i, 0 ≤ l i) → (∑ i, l i) ≤ 1 →
      (∀ i, ‖lambda i‖ ≤ (w i/m i)^phaseMu D p) →
      0 ≤ K → 0 ≤ u → 0 ≤ freqBound →
      (∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lambda D p i‖) ≤ K*u →
      (∀ i : RemainderIndex i₀, ∀ j, |frequency i j-frequency i₀ j| ≤ freqBound) →
      0 ≤ θ → θ ≤ 1 →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ t, 0 ≤ Γ t) ∧
        (∫ t, Γ t ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ t ∈ grid.root, (1-θ)*graphPredictionValue frequency l X lambda D p t+θ ≤
          Real.exp ((4*C*SourceParameters.step L^(-(1/16:ℝ))*p*K+
            p*freqBound*K*(grid.width/(grid.branching:ℝ)^level))*u)*Γ t := by
  obtain ⟨C,hC,haverage⟩ := exists_source_averaging_constant
  obtain ⟨L0,hL0⟩ := eventually_atTop.mp haverage
  refine ⟨C,L0,hC,?_⟩
  intro L hL ι κ _ _ grid level hlevel G hG w m hw hm frequency l X lambda i₀
    D p K u freqBound θ hD hp hfrequency hcard hl htotal hlambda hK hu hfreq hmass hfreqBound hθ0 hθ1
  obtain ⟨eta,remainder,heta,hetaC,hetahalf,hremainder,hnu⟩ :=
    hL0 L hL grid.origin (grid.origin+grid.width) (by linarith [grid.width_pos])
  have hwidth : grid.origin+grid.width-grid.origin = grid.width := by ring
  rw [hwidth] at hnu
  let := hremainder
  have hgap : 0 < 1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) := by
    have := grid.width_pos
    have := SourceParameters.step_pos L
    positivity
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := grid.graph_prediction_step level hlevel
    G hG w m hw hm remainder frequency l X lambda i₀ heta.le (by linarith) hgap hnu hD hp
    hfrequency hcard hl htotal hlambda hK hu hfreq hmass hfreqBound hθ0 hθ1
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  have hp0 : 0 ≤ p := by linarith
  have hfactor : eta/(1-eta) ≤ 2*eta := by
    apply (div_le_iff₀ (by linarith : 0 < 1-eta)).mpr
    nlinarith
  have herror : eta/(1-eta)*(2*p*K) ≤ 4*C*SourceParameters.step L^(-(1/16:ℝ))*p*K := by
    calc
      _ ≤ (2*eta)*(2*p*K) := mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ ≤ (2*(C*SourceParameters.step L^(-(1/16:ℝ))))*(2*p*K) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hetaC (by norm_num)) (by positivity)
      _ = _ := by ring
  intro t ht
  apply (hpoint t ht).trans
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (add_le_add_left herror _) hu)) (hpos t)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero snapshot vectors do not enter the angular count. Retain the chosen
path even when its snapshot vanishes, so all relative errors use the same path. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

private theorem sum_restrict_zero {ι M : Type} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] (S : Finset ι) (F : ι → M) (hzero : ∀ i ∉ S, F i = 0) :
    (∑ i : S, F i) = ∑ i, F i := by
  rw [Finset.sum_coe_sort]
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hzero i hi)

private theorem sum_injective_nonneg {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι → ι') (he : Function.Injective e) (F : ι' → ℝ) (hF : ∀ i, 0 ≤ F i) :
    (∑ i, F (e i)) ≤ ∑ i, F i := by
  classical
  exact OAI.sum_le_sum_of_injOn e (fun _ _ _ _ h => he h)
    (by simp) (fun _ _ => le_rfl) (fun i _ _ => hF i)

private theorem restricted_neighborhood_mass {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (G : ι → ι → Prop) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (i : S) :
    orderMass (fun j : S => w j) (closedNeighborhood (fun j k : S => G j k) i) ≤
      orderMass w (closedNeighborhood G i) := by
  classical
  unfold orderMass
  let J := closedNeighborhood (fun j k : S => G j k) i
  have hsub : J.image Subtype.val ⊆ closedNeighborhood G i := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    rcases (mem_closedNeighborhood _ _ _).mp hk with he | hg
    · exact (mem_closedNeighborhood _ _ _).mpr (Or.inl (congrArg Subtype.val he))
    · exact (mem_closedNeighborhood _ _ _).mpr (Or.inr hg)
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hw j)
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at h
  exact h

/-- The graph count is needed only on nonzero snapshot children and the path.
The original prediction and its full off-path coefficient budget are preserved. -/
theorem exists_source_supported_grid_prediction_oai :
    ∃ C L0 : ℝ, 1 ≤ C ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (grid : FiniteLineGrid) (level : ℕ), level ≤ grid.depth →
      ∀ (G : ι → ι → Prop), (∀ ⦃i j⦄, G i j → G j i) →
      ∀ (w m : ι → ℝ), (∀ i, 0 < w i) →
      (∀ i, orderMass w (closedNeighborhood G i) ≤ m i) →
      ∀ (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
        (lam : ι → ℂ) (i₀ : ι) (D p K u freqBound θ : ℝ),
      1 ≤ D → 4 ≤ p →
      (∀ i j, i ≠ j → ¬G i j → ∀ k,
        1/(grid.width*SourceParameters.step L^(-(1/8:ℝ))) ≤
          |frequency i k-frequency j k|) →
      (∀ S : Finset ι, (∀ i ∈ S, X i ≠ 0 ∨ i = i₀) →
        (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card:ℝ) ≤ D) →
      (∀ i, 0 ≤ l i) → (∑ i, l i) ≤ 1 →
      (∀ i, ‖lam i‖ ≤ (w i/m i)^phaseMu D p) →
      0 ≤ K → 0 ≤ u → 0 ≤ freqBound →
      (∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lam D p i‖) ≤ K*u →
      (∀ i : RemainderIndex i₀, ∀ j, |frequency i j-frequency i₀ j| ≤ freqBound) →
      0 ≤ θ → θ ≤ 1 →
      ∃ Γ : ℝ → ℝ, Measurable Γ ∧
        Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
        (∀ t, 0 ≤ Γ t) ∧
        (∫ t, Γ t ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
        (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
        ∀ t ∈ grid.root, (1-θ)*graphPredictionValue frequency l X lam D p t+θ ≤
          Real.exp ((4*C*SourceParameters.step L^(-(1/16:ℝ))*p*K+
            p*freqBound*K*(grid.width/(grid.branching:ℝ)^level))*u)*Γ t := by
  classical
  obtain ⟨C,L0,hC,hgrid⟩ := exists_source_grid_prediction
  refine ⟨C,L0,hC,?_⟩
  intro L hL ι κ _ _ grid level hlevel G hG w m hw hm frequency l X lam i₀
    D p K u freqBound θ hD hp hsep hcard hl htotal hlam hK hu hfreq hmass hfreqBound hθ0 hθ1
  let S : Finset ι := Finset.univ.filter (fun i => X i ≠ 0 ∨ i = i₀)
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  have hpath : i₀ ∈ S := by simp [S]
  let path : S := ⟨i₀,hpath⟩
  have hsupport (i : ι) (hi : i ∉ S) : X i = 0 := by
    have h : X i = 0 ∧ i ≠ i₀ := by simpa [S] using hi
    exact h.1
  have hcard' (J : Finset S)
      (hJ : (J : Set S).Pairwise (fun i j => ¬G i.val j.val)) : (J.card:ℝ) ≤ D := by
    have h := hcard (J.image Subtype.val) (by
      intro i hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp j.property).2) (by
      intro i hi j hj hij
      obtain ⟨i',hi',rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨j',hj',rfl⟩ := Finset.mem_image.mp hj
      exact hJ hi' hj' (fun h => hij (congrArg Subtype.val h)))
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h
  let e : RemainderIndex path → RemainderIndex i₀ := fun i =>
    ⟨i.val.val, fun hi => i.property (Subtype.ext hi)⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : RemainderIndex i₀ => a.val) hij
  have hmass' : (∑ i : RemainderIndex path,
      ‖predictionCoefficients (fun i : S => l i) (fun i => X i) (fun i => lam i) D p i‖) ≤ K*u :=
    (sum_injective_nonneg e he (fun i => ‖predictionCoefficients l X lam D p i‖)
      (fun _ => norm_nonneg _)).trans hmass
  have htotal' : (∑ i : S, l i) ≤ 1 :=
    (sum_injective_nonneg Subtype.val Subtype.val_injective l hl).trans htotal
  have hm' (i : S) : orderMass (fun j : S => w j)
      (closedNeighborhood (fun j k : S => G j k) i) ≤ m i := by
    convert (restricted_neighborhood_mass S G w (fun i => (hw i).le) i).trans (hm i) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ext j
    simp only [mem_closedNeighborhood]
  obtain ⟨Γ,hmeas,hint,hpos,havg,hcell,hpoint⟩ := hgrid L hL S κ grid level hlevel
    (fun i j : S => G i j) (fun {_ _} h => hG h) (fun i : S => w i) (fun i => m i)
    (fun i => hw i) hm'
    (fun i : S => frequency i) (fun i => l i) (fun i => X i) (fun i => lam i) path
    D p K u freqBound θ hD hp
    (fun i j hij hfar k => hsep i j (fun h => hij (Subtype.ext h)) hfar k)
    hcard' (fun i => hl i) htotal' (fun i => hlam i) hK hu hfreq hmass'
    (fun i k => hfreqBound (e i) k) hθ0 hθ1
  refine ⟨Γ,hmeas,hint,hpos,havg,hcell,?_⟩
  have heq (t : ℝ) : graphPredictionValue (fun i : S => frequency i) (fun i => l i)
      (fun i => X i) (fun i => lam i) D p t = graphPredictionValue frequency l X lam D p t := by
    unfold graphPredictionValue
    rw [diagonalFourierSum_eq_sum,diagonalFourierSum_eq_sum]
    apply congrArg₂ (energyRatio p)
    · apply congrArg (fun r : ℝ => 1+r)
      exact sum_restrict_zero S (fun i => l i*‖X i‖^p) (by
        intro i hi
        simp only [hsupport i hi,norm_zero,Real.zero_rpow (by linarith : p ≠ 0),mul_zero])
    · exact sum_restrict_zero S
        (fun i => diagonalModulation (frequency i) (predictionCoefficients l X lam D p i) t)
        (by intro i hi; simp only [predictionCoefficients,hsupport i hi,smul_zero];
            exact (diagonalModulationIsometry (frequency i) t).map_zero)
  intro t ht
  simpa only [heq] using hpoint t ht

end LipschitzHilbert

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.exists_source_supported_grid_prediction_oai := @OAI.LipschitzHilbert.exists_source_supported_grid_prediction_oai
