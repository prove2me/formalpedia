-- Prove2me | solution 1 for OAI.LipschitzHilbert.PacketLatticeData.eventually_original_parent_marked_path_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T19:55:22.563319+00:00
-- url     : https://prove2.me/submissions/1aec0ec4-7a96-4c61-b3c4-4908a34140f4

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002
import Theorems.Thm_OAI_LipschitzHilbert_PacketLatticeData_eventually_physical_parent_full_residual_square

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
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

omit [Fintype ι] in
theorem phaseConstant_pos : 0 < phaseConstant := by norm_num [phaseConstant]

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

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic variation and its dimension-free Euclidean comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem finiteCubicVariation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : 0 ≤ finiteCubicVariation F N := by
  classical
  apply Finset.le_sup'_of_le (f := fun p : Fin (N + 1) → Fin (N + 1) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
    (Finset.mem_univ (fun _ => 0))
  simp

theorem partition_le_finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ≤
      finiteCubicVariation F N := by
  classical
  simpa only [finiteCubicVariation, ite_eq_left hp] using
    (Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
      (Finset.mem_univ p))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationIntervals
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint interval selections, including selections depending on a point,
are controlled by one finite cubic variation. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

private theorem intervalPoint_le {S : ℕ} (a b : Fin S → ℕ) (N j : ℕ)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N) : intervalPoint a b N j ≤ N := by
  unfold intervalPoint
  split_ifs with h hpar
  · exact (hab _).trans (hb _)
  · exact hb _
  · exact le_rfl

private theorem intervalPoint_mono {S : ℕ} (a b : Fin S → ℕ) (N : ℕ)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N)
    (horder : ∀ i j, i < j → b i ≤ a j) : Monotone (intervalPoint a b N) := by
  intro i j hij
  by_cases hj : j / 2 < S
  · have hi : i / 2 < S := by omega
    have hdiv : i / 2 ≤ j / 2 := Nat.div_le_div_right hij
    by_cases heq : i / 2 = j / 2
    · have hidx : (⟨i / 2, hi⟩ : Fin S) = ⟨j / 2, hj⟩ := Fin.ext heq
      unfold intervalPoint
      rw [dite_eq_left hi, dite_eq_left hj, hidx]
      by_cases hip : i % 2 = 0
      · rw [ite_eq_left hip]
        by_cases hjp : j % 2 = 0
        · rw [ite_eq_left hjp]
        · rw [ite_eq_right hjp]
          exact hab _
      · rw [ite_eq_right hip]
        by_cases hjp : j % 2 = 0
        · omega
        · rw [ite_eq_right hjp]
    · have hlt : (⟨i / 2, hi⟩ : Fin S) < ⟨j / 2, hj⟩ := by
        change i / 2 < j / 2
        omega
      have hsep := horder ⟨i / 2, hi⟩ ⟨j / 2, hj⟩ hlt
      unfold intervalPoint
      rw [dite_eq_left hi, dite_eq_left hj]
      split_ifs
      · exact (hab _).trans hsep
      · exact ((hab _).trans hsep).trans (hab _)
      · exact hsep
      · exact hsep.trans (hab _)
  · have hj' : intervalPoint a b N j = N := by simp only [intervalPoint, dite_eq_right hj]
    rw [hj']
    exact intervalPoint_le a b N i hab hb

/-- Padding with the terminal endpoint embeds all selected intervals into
a monotone partition of the stopped sequence. There is no measurability
assumption on how the intervals were selected. -/
theorem ordered_intervals_le_variation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N S : ℕ) (a b : Fin S → ℕ) (hS : S ≤ N)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N)
    (horder : ∀ i j, i < j → b i ≤ a j) :
    (∑ i, ‖F (b i) - F (a i)‖ ^ 3) ≤
      finiteCubicVariation (fun n => F (min n N)) (2 * N) := by
  classical
  let p : Fin (2 * N + 1) → Fin (2 * N + 1) := fun i =>
    ⟨intervalPoint a b N i, lt_of_le_of_lt (intervalPoint_le a b N i hab hb) (by omega)⟩
  have hp : Monotone p := fun i j hij => intervalPoint_mono a b N hab hb horder hij
  let e : Fin S → Fin (2 * N) := fun i => ⟨2 * i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    dsimp only [e] at h
    omega
  have hpa (i : Fin S) : (p (e i).castSucc).val = a i := by
    simp [p, e, intervalPoint, show (2 * i.val) / 2 = i.val by omega,
      show (2 * i.val) % 2 = 0 by omega, i.isLt]
  have hpb (i : Fin S) : (p (e i).succ).val = b i := by
    simp [p, e, intervalPoint, show (2 * i.val + 1) / 2 = i.val by omega, i.isLt]
  have hselect : (∑ i, ‖F (b i) - F (a i)‖ ^ 3) ≤
      ∑ i : Fin (2 * N), ‖F (min (p i.succ) N) - F (min (p i.castSucc) N)‖ ^ 3 := by
    refine OAI.sum_le_sum_of_injOn (s := Finset.univ) (t := Finset.univ)
      e (fun i _ j _ hij => he hij) (Finset.subset_univ _) ?_ ?_
    · intro i _
      rw [hpa, hpb, min_eq_left (hb i), min_eq_left ((hab i).trans (hb i))]
    · intro i _ _
      positivity
  exact hselect.trans (partition_le_finiteCubicVariation
    (fun n => F (min n N)) (2 * N) p hp)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntervalOscillation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual maxima of subinterval sums on residual segments. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem intervalOscillation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) : 0 ≤ intervalOscillation F N a b := by
  classical
  apply Finset.le_sup'_of_le (b := ((0 : Fin (N + 1)), (0 : Fin (N + 1))))
    (f := fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0) (Finset.mem_univ _)
  split_ifs <;> positivity

theorem exists_intervalOscillation_eq {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) :
    ∃ c d : ℕ, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ intervalOscillation F N a b = ‖F d - F c‖ := by
  classical
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0)
  change intervalOscillation F N a b = _ at hq
  by_cases h : a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b
  · rw [ite_eq_left h] at hq
    exact ⟨q.1, q.2, h.1, h.2.1, h.2.2, hq⟩
  · rw [ite_eq_right h] at hq
    exact ⟨a, a, le_rfl, le_rfl, hab, by simpa only [sub_self, norm_zero] using hq⟩

theorem increment_le_intervalOscillation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b c d : ℕ) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hb : b ≤ N) :
    ‖F d - F c‖ ≤ intervalOscillation F N a b := by
  classical
  let q : Fin (N + 1) × Fin (N + 1) :=
    (⟨c, by omega⟩, ⟨d, by omega⟩)
  have h := Finset.le_sup'
    (fun q : Fin (N + 1) × Fin (N + 1) =>
      if a ≤ q.1.val ∧ q.1.val ≤ q.2.val ∧ q.2.val ≤ b then
        ‖F q.2 - F q.1‖ else 0) (Finset.mem_univ q)
  simpa only [intervalOscillation, q,
    ite_eq_left (show a ≤ c ∧ c ≤ d ∧ d ≤ b from ⟨hac, hcd, hdb⟩)] using h

/-- Choose an actual maximizing subinterval in every disjoint segment,
then use one common variation bound for all segments together. -/
theorem intervalOscillation_cube_sum {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N S : ℕ) (a b : Fin S → ℕ) (hS : S ≤ N)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N)
    (horder : ∀ i j, i < j → b i ≤ a j) :
    (∑ i, intervalOscillation F N (a i) (b i) ^ 3) ≤
      finiteCubicVariation (fun n => F (min n N)) (2 * N) := by
  choose c d hac hcd hdb heq using fun i =>
    exists_intervalOscillation_eq F N (a i) (b i) (hab i)
  simp_rw [heq]
  exact ordered_intervals_le_variation F N S c d hS hcd
    (fun i => (hdb i).trans (hb i))
    (fun i j hij => (hdb i).trans ((horder i j hij).trans (hac j)))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_DisjointIntervalVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reorder an actual finite family of disjoint residual intervals before
applying the common cubic variation bound. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

/-- Positive-length disjoint intervals can be sorted by their actual
starting indices. Their number is bounded by the finite horizon. -/
theorem disjoint_intervalOscillation_cube_sum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) (a b : ι → ℕ)
    (hab : ∀ i, a i < b i) (hb : ∀ i, b i ≤ N)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, intervalOscillation F N (a i) (b i) ^ 3) ≤
      finiteCubicVariation (fun n => F (min n N)) (2 * N) := by
  classical
  have hinj : Function.Injective a := by
    intro i j heq
    by_contra hne
    rcases hdisjoint i j hne with h | h
    · have hi := hab i
      omega
    · have hj := hab j
      omega
  let index : ι → Fin N := fun i => ⟨a i, (hab i).trans_le (hb i)⟩
  have hiinj : Function.Injective index := by
    intro i j hij
    apply hinj
    exact congrArg Fin.val hij
  have hcard : Fintype.card ι ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective index hiinj
  let : LinearOrder ι := LinearOrder.lift' a hinj
  let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
  have horder (i j : Fin (Fintype.card ι)) (hij : i < j) : b (e i) ≤ a (e j) := by
    have hlt : a (e i) < a (e j) := e.strictMono hij
    rcases hdisjoint (e i) (e j) (e.injective.ne hij.ne) with h | h
    · exact h
    · have hj := hab (e j)
      omega
  have h := intervalOscillation_cube_sum F N (Fintype.card ι)
    (fun i => a (e i)) (fun i => b (e i)) hcard (fun i => (hab (e i)).le)
    (fun i => hb (e i)) horder
  calc
    _ = ∑ i : Fin (Fintype.card ι), intervalOscillation F N (a (e i)) (b (e i)) ^ 3 :=
      (e.toEquiv.sum_comp (fun i => intervalOscillation F N (a i) (b i) ^ 3)).symm
    _ ≤ _ := h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_HierarchyVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full-root logarithmic variation bound for shifted angular blocks. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem sliding_window_sum_le (P : ℕ → ℝ) (N K : ℕ)
    (hP : ∀ j < N, 0 ≤ P j) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico (i + 1 - K) (i + 1), P j) ≤
      (K : ℝ) * ∑ j ∈ Finset.range N, P j := by
  classical
  have hrow (i : ℕ) (hi : i ∈ Finset.range N) :
      (∑ j ∈ Finset.Ico (i + 1 - K) (i + 1), P j) =
        ∑ j ∈ Finset.range N, if j ∈ Finset.Ico (i + 1 - K) (i + 1) then P j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at *
    omega
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hP j (Finset.mem_range.mp hj))
  have hsub : (Finset.range N).filter (fun i => j ∈ Finset.Ico (i + 1 - K) (i + 1)) ⊆
      Finset.Ico j (j + K) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at *
    omega
  have hcard := Finset.card_le_card hsub
  simp only [Nat.card_Ico, Nat.add_sub_cancel_left] at hcard
  exact_mod_cast hcard

theorem sum_log_ratios (n : ℕ → ℝ) (N : ℕ) (hn : ∀ j ≤ N, 0 < n j) :
    (∑ j ∈ Finset.range N, Real.log (n j / n (j + 1))) = Real.log (n 0 / n N) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      Real.log (n j / n (j + 1)) = Real.log (n j) - Real.log (n (j + 1)) :=
    Real.log_div (hn j (by have := Finset.mem_range.mp hj; omega)).ne'
      (hn (j + 1) (by have := Finset.mem_range.mp hj; omega)).ne'
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub']
  exact (Real.log_div (hn 0 (Nat.zero_le N)).ne' (hn N le_rfl).ne').symm

theorem sum_log_ratios_Ico (n : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hn : ∀ j ≤ b, 0 < n j) :
    (∑ j ∈ Finset.Ico a b, Real.log (n j / n (j + 1))) = Real.log (n a / n b) := by
  rw [Finset.sum_Ico_eq_sub _ hab, sum_log_ratios n b hn,
    sum_log_ratios n a (fun j hj => hn j (hj.trans hab))]
  rw [Real.log_div (hn 0 (Nat.zero_le b)).ne' (hn b le_rfl).ne',
    Real.log_div (hn 0 (Nat.zero_le b)).ne' (hn a hab).ne',
    Real.log_div (hn a hab).ne' (hn b le_rfl).ne']
  ring

theorem full_root_log_variation (n R : ℕ → ℝ) (N K : ℕ)
    (hn : ∀ j ≤ N, 0 < n j) (hmono : AntitoneOn n (Set.Iic N))
    (hR : ∀ i < N, R i ≤ Real.log (n (i + 1 - K) / n (i + 1))) :
    (∑ i ∈ Finset.range N, R i) ≤ (K : ℝ) * Real.log (n 0 / n N) := by
  have hP (j : ℕ) (hj : j < N) : 0 ≤ Real.log (n j / n (j + 1)) := by
    apply Real.log_nonneg
    exact (one_le_div (hn (j + 1) (by omega))).2
      (hmono (by change j ≤ N; omega) (by change j + 1 ≤ N; omega) (by omega))
  have hwindow (i : ℕ) (hi : i ∈ Finset.range N) :
      R i ≤ ∑ j ∈ Finset.Ico (i + 1 - K) (i + 1), Real.log (n j / n (j + 1)) := by
    rw [sum_log_ratios_Ico n _ _ (Nat.sub_le _ _) (fun j hj => hn j
      (hj.trans (by have := Finset.mem_range.mp hi; omega)))]
    exact hR i (Finset.mem_range.mp hi)
  calc
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico (i + 1 - K) (i + 1),
        Real.log (n j / n (j + 1)) := Finset.sum_le_sum hwindow
    _ ≤ (K : ℝ) * ∑ j ∈ Finset.range N, Real.log (n j / n (j + 1)) :=
      sliding_window_sum_le _ N K hP
    _ = _ := by rw [sum_log_ratios n N hn]

end LipschitzHilbert

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

theorem logarithm_increment_bound (a P R : ℝ) (z : ℂ)
    (ha : 0 ≤ a) (hP : 0 ≤ P) (hR : 0 ≤ R) :
    ‖((a * P : ℝ) : ℂ) - z * (R : ℂ)‖ ≤ a * P + ‖z‖ * R := by
  calc
    _ ≤ ‖((a * P : ℝ) : ℂ)‖ + ‖z * (R : ℂ)‖ := norm_sub_le _ _
    _ = _ := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha hP),
        abs_of_nonneg hR]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SeparatedPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cardinality of separated frequencies in one bounded interval. -/

noncomputable section

namespace LipschitzHilbert.PhaseCombinatorics

theorem ordered_separated_index_bound {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ)
    (hf : StrictMono f) {gap : ℝ} (hsep : Separated f gap) (i : Fin N) :
    (i.val : ℝ) * gap ≤ f i - f ⟨0, hN⟩ := by
  have h (k : ℕ) (hk : k < N) : (k : ℝ) * gap ≤ f ⟨k, hk⟩ - f ⟨0, hN⟩ := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k < N := by omega
      have hstep := @hsep (⟨k + 1, hk⟩ : Fin N) ⟨k, hk'⟩ (by
        intro heq
        have hv := congrArg Fin.val heq
        change k + 1 = k at hv
        omega)
      have hmono : f ⟨k, hk'⟩ < f ⟨k + 1, hk⟩ := hf (by
        change k < k + 1
        omega)
      rw [abs_of_pos (sub_pos.mpr hmono)] at hstep
      have hprev := ih hk'
      push_cast
      nlinarith
  exact h i.val i.isLt

theorem separated_card_le_span {ι : Type*} [Fintype ι] (frequency : ι → ℝ)
    {gap a b : ℝ} (hgap : 0 < gap) (hab : a ≤ b)
    (hsep : Separated frequency gap) (hbound : ∀ i, a ≤ frequency i ∧ frequency i ≤ b) :
    (Fintype.card ι : ℝ) ≤ 1 + (b - a) / gap := by
  classical
  by_cases hN : Fintype.card ι = 0
  · rw [hN]
    have hdiv := div_nonneg (sub_nonneg.mpr hab) hgap.le
    norm_num
    linarith
  · have hNpos : 0 < Fintype.card ι := Nat.pos_of_ne_zero hN
    have hinj : Function.Injective frequency := by
      intro i j hij
      by_contra hne
      have h := @hsep i j hne
      rw [hij, sub_self, abs_zero] at h
      linarith
    let : LinearOrder ι := LinearOrder.lift' frequency hinj
    let e : Fin (Fintype.card ι) ≃o ι := Fintype.orderIsoFinOfCardEq ι rfl
    have hf : StrictMono (fun i => frequency (e i)) := fun _ _ hij => e.strictMono hij
    have he_sep : Separated (fun i => frequency (e i)) gap := by
      intro i j hij
      exact @hsep (e i) (e j) (fun h => hij (e.injective h))
    let last : Fin (Fintype.card ι) := ⟨Fintype.card ι - 1, by omega⟩
    have hindex := ordered_separated_index_bound hNpos _ hf he_sep last
    have hspan : ((Fintype.card ι : ℝ) - 1) * gap ≤ b - a := by
      have hlast := (hbound (e last)).2
      have hfirst := (hbound (e ⟨0, hNpos⟩)).1
      dsimp only [last] at hindex
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one] at hindex
      linarith
    have hdiv := (le_div_iff₀ hgap).2 hspan
    linarith

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MarkedShells
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Marked mass shells

The shell estimate and weighted sum of §10, `res:marked-shell-count` and
`res:marked-weight-sum`. A positive drop at every marked index makes the
corresponding masses separated. We use shells of ratio four, grouping
pairs of the manuscript's dyadic shells, so that the geometric ratio is
at most one half throughout the required exponent range.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

theorem marked_mass_separated (n : ℕ → ℝ) (hn : Antitone n)
    (S : Finset ℕ) {c : ℝ} (hdrop : ∀ i ∈ S, c ≤ n i - n (i + 1)) :
    Separated (fun i : S => n i) c := by
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstep := hdrop i i.property
    have horder := hn (show i.val + 1 ≤ j.val by omega)
    have hmono := hn hlt.le
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    linarith
  · have hstep := hdrop j j.property
    have horder := hn (show j.val + 1 ≤ i.val by omega)
    have hmono := hn hgt.le
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    linarith

theorem separated_shell_card {ι : Type*} [Fintype ι] (mass : ι → ℝ)
    {c t b : ℝ} (hc : 0 < c) (htb : t ≤ b)
    (hsep : Separated mass c) (S : Finset ι)
    (hS : ∀ i ∈ S, t ≤ mass i ∧ mass i ≤ b) :
    (S.card : ℝ) ≤ 1 + (b - t) / c := by
  classical
  have hs : Separated (fun i : S => mass i) c := by
    intro i j hij
    exact hsep (fun h => hij (Subtype.ext h))
  simpa only [Fintype.card_coe] using
    separated_card_le_span (fun i : S => mass i) hc htb hs (fun i => hS i i.property)

private theorem four_rpow_le_half {q : ℝ} (hq : q ≤ -(1 / 2 : ℝ)) :
    (4 : ℝ) ^ q ≤ 1 / 2 := by
  have h : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hq).trans_eq h

/-- A separated finite family above `M` has a summable negative-power
weight, uniformly in its cardinality and its largest mass. -/
theorem separated_negative_power_sum {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) {c M e : ℝ} (hc : 0 < c) (hM : 1 ≤ M)
    (he : e ≤ -(3 / 2 : ℝ)) (hsep : Separated mass c)
    (hmass : ∀ i, M ≤ mass i) :
    (∑ i, mass i ^ e) ≤ 2 * (1 + 3 / c) * M ^ (e + 1) := by
  classical
  have hM0 : 0 < M := by linarith
  have he0 : e ≤ 0 := by linarith
  have hq : e + 1 ≤ -(1 / 2 : ℝ) := by linarith
  have hex (i : ι) : ∃ r : ℕ, (4 : ℝ) ^ r * M ≤ mass i ∧
      mass i < 4 * ((4 : ℝ) ^ r * M) := by
    obtain ⟨r, hr, hr'⟩ := exists_nat_pow_near
      ((one_le_div hM0).mpr (hmass i)) (by norm_num : (1 : ℝ) < 4)
    refine ⟨r, (le_div_iff₀ hM0).mp hr, ?_⟩
    have h := (div_lt_iff₀ hM0).mp hr'
    rw [pow_succ] at h
    nlinarith
  choose shell hshell using hex
  let R : Finset ℕ := Finset.univ.image shell
  have hR (i : ι) : shell i ∈ R := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hshell_bound (r : ℕ) :
      (∑ i ∈ Finset.univ.filter (fun i => shell i = r), mass i ^ e) ≤
        (1 + 3 / c) * M ^ (e + 1) * (1 / 2 : ℝ) ^ r := by
    let t : ℝ := (4 : ℝ) ^ r * M
    have ht0 : 0 < t := mul_pos (pow_pos (by norm_num) _) hM0
    have ht1 : 1 ≤ t := by
      have hp : (1 : ℝ) ≤ 4 ^ r := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)
      dsimp [t]
      nlinarith
    have hcard := separated_shell_card mass hc (show t ≤ 4 * t by linarith) hsep
      (Finset.univ.filter (fun i => shell i = r)) (by
        intro i hi
        have hi' : shell i = r := (Finset.mem_filter.mp hi).2
        change (4 : ℝ) ^ r * M ≤ mass i ∧ mass i ≤ 4 * ((4 : ℝ) ^ r * M)
        constructor
        · simpa only [hi'] using (hshell i).1
        · simpa only [hi'] using (hshell i).2.le)
    have hcard' : ((Finset.univ.filter (fun i => shell i = r)).card : ℝ) ≤
        (1 + 3 / c) * t := by
      have hc0 : 0 ≤ 3 / c := by positivity
      have hcalc : 1 + (4 * t - t) / c ≤ (1 + 3 / c) * t := by
        have heq : 1 + (4 * t - t) / c = 1 + (3 / c) * t := by ring
        rw [heq]
        nlinarith
      exact hcard.trans hcalc
    calc
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => shell i = r), t ^ e := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        exact Real.rpow_le_rpow_of_nonpos ht0 (by simpa [t, hi'] using (hshell i).1) he0
      _ = ((Finset.univ.filter (fun i => shell i = r)).card : ℝ) * t ^ e := by simp
      _ ≤ ((1 + 3 / c) * t) * t ^ e :=
        mul_le_mul_of_nonneg_right hcard' (Real.rpow_nonneg ht0.le _)
      _ = (1 + 3 / c) * M ^ (e + 1) * ((4 : ℝ) ^ (e + 1)) ^ r := by
        rw [show ((1 + 3 / c) * t) * t ^ e = (1 + 3 / c) * t ^ (e + 1) by
          rw [Real.rpow_add_one ht0.ne']; ring]
        dsimp [t]
        rw [Real.mul_rpow (by positivity) hM0.le, ← Real.rpow_pow_comm (by norm_num)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (four_rpow_le_half hq) r)
        (by positivity)
  calc
    _ = ∑ r ∈ R, ∑ i ∈ Finset.univ.filter (fun i => shell i = r), mass i ^ e :=
      (Finset.sum_fiberwise_of_maps_to (fun i _ => hR i) _).symm
    _ ≤ ∑ r ∈ R, (1 + 3 / c) * M ^ (e + 1) * (1 / 2 : ℝ) ^ r :=
      Finset.sum_le_sum fun r _ => hshell_bound r
    _ = ((1 + 3 / c) * M ^ (e + 1)) * ∑ r ∈ R, (1 / 2 : ℝ) ^ r :=
      (Finset.mul_sum ..).symm
    _ ≤ ((1 + 3 / c) * M ^ (e + 1)) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (summable_geometric_two.sum_le_tsum R (fun r _ => by positivity)).trans_eq
        tsum_geometric_two
    _ = _ := by ring

/-- The manuscript's marked weight bound follows from the actual
positive mass drops, with an explicit constant depending only on `c`. -/
theorem marked_weight_sum (n : ℕ → ℝ) (hn : Antitone n) (S : Finset ℕ)
    {c M μ : ℝ} (hc : 0 < c) (hM : 1 ≤ M) (hμ : μ ≤ 1 / 12)
    (hdrop : ∀ i ∈ S, c ≤ n i - n (i + 1)) (hmass : ∀ i ∈ S, M ≤ n i) :
    (∑ i ∈ S, n i ^ (-2 + 2 * μ)) ≤
      2 * (1 + 3 / c) * M ^ (-1 + 2 * μ) := by
  have h := separated_negative_power_sum (fun i : S => n i) hc hM
    (show -2 + 2 * μ ≤ -(3 / 2 : ℝ) by linarith)
    (marked_mass_separated n hn S hdrop) (fun i => hmass i i.property)
  rw [← Finset.sum_coe_sort S (fun i => n i ^ (-2 + 2 * μ))]
  simpa only [show -2 + 2 * μ + 1 = -1 + 2 * μ by ring] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SegmentMassSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unary-segment negative-power weight sum in §10
`res:segment-weight-sum`. Ratio-sixteen shells give geometric ratio at
most one half for every exponent used by the manuscript. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

private theorem sixteen_rpow_le_half {q : ℝ} (hq : q ≤ -(1 / 4 : ℝ)) :
    (16 : ℝ) ^ q ≤ 1 / 2 := by
  have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hsixteen : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
    convert hfour using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have h : (16 : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), hsixteen]
    norm_num
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hq).trans_eq h

/-- Finite shell summation from a linear shell-cardinality estimate.
The bound is independent of the number of populated shells. -/
theorem finite_shell_power_sum {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) {M C e : ℝ} (hM : 1 ≤ M) (hC : 0 ≤ C)
    (he : e ≤ -(5 / 4 : ℝ)) (hmass : ∀ i, M ≤ mass i)
    (hcount : ∀ (t : ℝ) (S : Finset ι), M ≤ t →
      (∀ i ∈ S, t ≤ mass i ∧ mass i ≤ 16 * t) → (S.card : ℝ) ≤ C * t) :
    (∑ i, mass i ^ e) ≤ 2 * C * M ^ (e + 1) := by
  classical
  have hM0 : 0 < M := by linarith
  have he0 : e ≤ 0 := by linarith
  have hq : e + 1 ≤ -(1 / 4 : ℝ) := by linarith
  have hex (i : ι) : ∃ r : ℕ, (16 : ℝ) ^ r * M ≤ mass i ∧
      mass i < 16 * ((16 : ℝ) ^ r * M) := by
    obtain ⟨r, hr, hr'⟩ := exists_nat_pow_near
      ((one_le_div hM0).mpr (hmass i)) (by norm_num : (1 : ℝ) < 16)
    refine ⟨r, (le_div_iff₀ hM0).mp hr, ?_⟩
    have h := (div_lt_iff₀ hM0).mp hr'
    rw [pow_succ] at h
    nlinarith
  choose shell hshell using hex
  let R : Finset ℕ := Finset.univ.image shell
  have hR (i : ι) : shell i ∈ R := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hshell_bound (r : ℕ) :
      (∑ i ∈ Finset.univ.filter (fun i => shell i = r), mass i ^ e) ≤
        C * M ^ (e + 1) * (1 / 2 : ℝ) ^ r := by
    let t : ℝ := (16 : ℝ) ^ r * M
    have ht0 : 0 < t := mul_pos (pow_pos (by norm_num) _) hM0
    have htM : M ≤ t := by
      have hp : (1 : ℝ) ≤ 16 ^ r := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 16)
      dsimp [t]
      nlinarith
    have hcard := hcount t (Finset.univ.filter (fun i => shell i = r)) htM (by
      intro i hi
      have hi' : shell i = r := (Finset.mem_filter.mp hi).2
      change (16 : ℝ) ^ r * M ≤ mass i ∧ mass i ≤ 16 * ((16 : ℝ) ^ r * M)
      constructor
      · simpa only [hi'] using (hshell i).1
      · simpa only [hi'] using (hshell i).2.le)
    calc
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => shell i = r), t ^ e := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        exact Real.rpow_le_rpow_of_nonpos ht0 (by simpa [t, hi'] using (hshell i).1) he0
      _ = ((Finset.univ.filter (fun i => shell i = r)).card : ℝ) * t ^ e := by simp
      _ ≤ (C * t) * t ^ e :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg ht0.le _)
      _ = C * M ^ (e + 1) * ((16 : ℝ) ^ (e + 1)) ^ r := by
        rw [show (C * t) * t ^ e = C * t ^ (e + 1) by
          rw [Real.rpow_add_one ht0.ne']; ring]
        dsimp [t]
        rw [Real.mul_rpow (by positivity) hM0.le, ← Real.rpow_pow_comm (by norm_num)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (sixteen_rpow_le_half hq) r)
        (by positivity)
  calc
    _ = ∑ r ∈ R, ∑ i ∈ Finset.univ.filter (fun i => shell i = r), mass i ^ e :=
      (Finset.sum_fiberwise_of_maps_to (fun i _ => hR i) _).symm
    _ ≤ ∑ r ∈ R, C * M ^ (e + 1) * (1 / 2 : ℝ) ^ r :=
      Finset.sum_le_sum fun r _ => hshell_bound r
    _ = (C * M ^ (e + 1)) * ∑ r ∈ R, (1 / 2 : ℝ) ^ r := (Finset.mul_sum ..).symm
    _ ≤ (C * M ^ (e + 1)) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (summable_geometric_two.sum_le_tsum R (fun r _ => by positivity)).trans_eq
        tsum_geometric_two
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntervalSegmentCharging
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary segments may charge whole disjoint drop intervals. This includes
completed segments directly, without replacing their drops by single steps. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

/-- A whole completed segment, or the interruption charged by a remainder,
provides a fixed positive drop. Pairwise disjoint charge intervals give the
same shell count as single-step charges, including one final uncharged piece. -/
theorem interval_charged_segment_shell_card {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (charge : ι → Option (ℕ × ℕ)) (n : ℕ → ℝ)
    (hn : Antitone n)
    (hnone : ∀ i j, charge i = none → charge j = none → i = j)
    (hdisjoint : ∀ i j a b c d, i ≠ j → charge i = some (a,b) →
      charge j = some (c,d) → b ≤ c ∨ d ≤ a)
    {drop lo hi : ℝ} (hdrop : 0 < drop) (hlohi : lo ≤ hi)
    (hcharge : ∀ i a b, charge i = some (a,b) →
      mass i - 2 ≤ n a ∧ n a ≤ mass i ∧ drop ≤ n a - n b)
    (S : Finset ι) (hS : ∀ i ∈ S, lo ≤ mass i ∧ mass i ≤ hi) :
    (S.card : ℝ) ≤ 2 + (hi - lo + 2) / drop := by
  classical
  let T := S.filter (fun i => charge i ≠ none)
  have hsome (i : T) : charge i = some ((charge i).getD (0,0)) := by
    cases hi : charge i with
    | none => exact False.elim ((Finset.mem_filter.mp i.property).2 hi)
    | some p => simp
  have hbound (i : T) : lo - 2 ≤ n ((charge i).getD (0,0)).1 ∧
      n ((charge i).getD (0,0)).1 ≤ hi := by
    have hiS := (Finset.mem_filter.mp i.property).1
    have h := hcharge i _ _ (hsome i)
    change mass i - 2 ≤ n ((charge i).getD (0,0)).1 ∧
      n ((charge i).getD (0,0)).1 ≤ mass i ∧
      drop ≤ n ((charge i).getD (0,0)).1 - n ((charge i).getD (0,0)).2 at h
    exact ⟨by linarith [(hS i hiS).1, h.1], h.2.1.trans (hS i hiS).2⟩
  have hsep : Separated (fun i : T => n ((charge i).getD (0,0)).1) drop := by
    intro i j hij
    have hne : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
    have h := hdisjoint i j _ _ _ _ hne (hsome i) (hsome j)
    rcases h with h | h
    · have hmono := hn h
      have hd := (hcharge i _ _ (hsome i)).2.2
      change n ((charge j).getD (0,0)).1 ≤ n ((charge i).getD (0,0)).2 at hmono
      change drop ≤ n ((charge i).getD (0,0)).1 - n ((charge i).getD (0,0)).2 at hd
      have hle : drop ≤ n ((charge i).getD (0,0)).1 - n ((charge j).getD (0,0)).1 := by
        linarith
      exact hle.trans (le_abs_self _)
    · have hmono := hn h
      have hd := (hcharge j _ _ (hsome j)).2.2
      change n ((charge i).getD (0,0)).1 ≤ n ((charge j).getD (0,0)).2 at hmono
      change drop ≤ n ((charge j).getD (0,0)).1 - n ((charge j).getD (0,0)).2 at hd
      have hle : drop ≤ n ((charge j).getD (0,0)).1 - n ((charge i).getD (0,0)).1 := by
        linarith
      exact hle.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  have hT : (T.card : ℝ) ≤ 1 + (hi - lo + 2) / drop := by
    have h := separated_card_le_span (fun i : T => n ((charge i).getD (0,0)).1)
      hdrop (show lo - 2 ≤ hi by linarith) hsep hbound
    have heq : hi - (lo - 2) = hi - lo + 2 := by ring
    simpa only [Fintype.card_coe, heq] using h
  have hnoneCard : (S.filter (fun i => charge i = none)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hnone i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun i => charge i = none)
  have hcount : S.card ≤ T.card + 1 := by
    dsimp [T]
    omega
  exact (show (S.card : ℝ) ≤ (T.card : ℝ) + 1 by exact_mod_cast hcount).trans (by linarith)

theorem interval_charged_segment_weight_sum {ι : Type*} [Fintype ι]
    (mass : ι → ℝ) (charge : ι → Option (ℕ × ℕ)) (n : ℕ → ℝ)
    (hn : Antitone n)
    (hnone : ∀ i j, charge i = none → charge j = none → i = j)
    (hdisjoint : ∀ i j a b c d, i ≠ j → charge i = some (a,b) →
      charge j = some (c,d) → b ≤ c ∨ d ≤ a)
    {drop M μ : ℝ} (hdrop : 0 < drop) (hM : 1 ≤ M) (hμ : μ ≤ 1 / 12)
    (hmass : ∀ i, M ≤ mass i)
    (hcharge : ∀ i a b, charge i = some (a,b) →
      mass i - 2 ≤ n a ∧ n a ≤ mass i ∧ drop ≤ n a - n b) :
    (∑ i, mass i ^ ((-1 + μ) * (3 / 2 : ℝ))) ≤
      2 * (2 + 17 / drop) * M ^ (-(1 / 2 : ℝ) + 3 * μ / 2) := by
  have h := finite_shell_power_sum mass hM (show 0 ≤ 2 + 17 / drop by positivity)
    (show (-1 + μ) * (3 / 2 : ℝ) ≤ -(5 / 4 : ℝ) by linarith) hmass (fun t S ht hS => by
      have ht1 : 1 ≤ t := hM.trans ht
      have h := interval_charged_segment_shell_card mass charge n hn hnone hdisjoint hdrop
        (show t ≤ 16 * t by linarith) hcharge S hS
      apply h.trans
      have hpos : 0 ≤ (t - 1) / drop := div_nonneg (by linarith) hdrop.le
      have heq : (2 + 17 / drop) * t - (2 + (16 * t - t + 2) / drop) =
          2 * (t - 1) + 2 * ((t - 1) / drop) := by ring
      linarith)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

end LipschitzHilbert

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

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_VertexIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrating the vertex amount

The actual finite terminal flow gives pointwise good-path domination on the
large-mass region. Integrating that domination together with the
small-mass estimate extracts the normalized vertex energy from its
nonnegative amount. This is the finite nonnegative assembly in §11.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {α κ ι : Type*} [MeasurableSpace α] [Fintype κ] [Fintype ι] {N : ℕ}

attribute [local instance] Classical.propDecidable

section Energy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [MeasurableSpace α] [Fintype κ] [Fintype ι] in
theorem normalized_vertex_energy_eq {n a p : ℝ} (hn : 0 < n) (hp : p ≠ 0) (A : E) :
    ‖(n ^ (a / p - 1)) • A‖ ^ p = n ^ (a - p) * ‖A‖ ^ p := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn.le _),
    Real.mul_rpow (Real.rpow_nonneg hn.le _) (norm_nonneg _), ← Real.rpow_mul hn.le]
  have heq : (a / p - 1) * p = a - p := by
    have h := div_mul_cancel₀ a hp
    nlinarith
  rw [heq]

end Energy

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Unary residual energies

The amount is the actual `vertexAmount` from §11. Its logarithmic motion
and the small correction `log(1+h/V)` are the analytic ingredients of
the unary-segment telescope in §10, equation `src-28`.
-/

noncomputable section

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem vertexAmount_pos {n a p : ℝ} (hn : 0 < n) (A : E) :
    0 < vertexAmount n A a p := by
  unfold vertexAmount
  positivity

omit [NormedSpace ℝ E] in
theorem mass_le_vertexAmount {n a p : ℝ} (hn : 0 ≤ n) (A : E) :
    n ≤ vertexAmount n A a p := by
  unfold vertexAmount
  exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hn _) (Real.rpow_nonneg (norm_nonneg A) _))

/-- Here `mu=(a-1)/p`, so this is exactly the normalization used in §10. -/
theorem vertexAmount_eq_normalized {n a p : ℝ} (hn : 0 < n) (hp : p ≠ 0) (A : E) :
    vertexAmount n A a p = n * (1 + ‖(n ^ ((a - 1) / p - 1)) • A‖ ^ p) := by
  rw [normalized_vertex_energy_eq hn hp]
  unfold vertexAmount
  have heq : n * n ^ (a - 1 - p) = n ^ (a - p) := by
    calc
      n * n ^ (a - 1 - p) = n ^ (1 : ℝ) * n ^ (a - 1 - p) := by rw [Real.rpow_one]
      _ = n ^ ((1 : ℝ) + (a - 1 - p)) := (Real.rpow_add hn _ _).symm
      _ = n ^ (a - p) := by congr 1; ring
  rw [mul_add, mul_one, ← mul_assoc, heq]

theorem log_vertexAmount_eq {n a p : ℝ} (hn : 0 < n) (hp : p ≠ 0) (A : E) :
    Real.log (vertexAmount n A a p) = Real.log n +
      logEnergy p ((n ^ ((a - 1) / p - 1)) • A) := by
  rw [vertexAmount_eq_normalized hn hp,
    Real.log_mul hn.ne' (by positivity)]
  rfl

theorem log_vertexAmount_lipschitz {n a p : ℝ} (hn : 0 < n) (hp : 1 ≤ p) (A A' : E) :
    |Real.log (vertexAmount n A a p) - Real.log (vertexAmount n A' a p)| ≤
      p * n ^ ((a - 1) / p - 1) * ‖A - A'‖ := by
  rw [log_vertexAmount_eq hn (by linarith : p ≠ 0),
    log_vertexAmount_eq hn (by linarith : p ≠ 0), add_sub_add_left_eq_sub]
  have h := logEnergy_lipschitz hp ((n ^ ((a - 1) / p - 1)) • A)
    ((n ^ ((a - 1) / p - 1)) • A')
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hn.le _)] at h
  simpa only [mul_assoc] using h

omit [NormedSpace ℝ E] in
/-- Increasing the mass and contracting the amplitude makes the amount
a subsolution, apart from the exact mass drop. -/
theorem vertexAmount_subsolution {n n' a p : ℝ} (hn' : 0 < n') (hn : n' ≤ n)
    (hap : a ≤ p) (hp : 0 ≤ p) (A A' : E) (hA : ‖A‖ ≤ ‖A'‖) :
    vertexAmount n A a p ≤ (n - n') + vertexAmount n' A' a p := by
  have hmass := Real.rpow_le_rpow_of_nonpos hn' hn (sub_nonpos.mpr hap)
  have hamp := Real.rpow_le_rpow (norm_nonneg A) hA hp
  have hprod : n ^ (a - p) * ‖A‖ ^ p ≤ n' ^ (a - p) * ‖A'‖ ^ p := by
    calc
      _ ≤ n' ^ (a - p) * ‖A‖ ^ p :=
        mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg (norm_nonneg A) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hamp (Real.rpow_nonneg hn'.le _)
  unfold vertexAmount
  linarith

private theorem hasDerivAt_logCorrection {h z : ℝ} (hh : 0 ≤ h) :
    HasDerivAt (logCorrection h) (-h / (Real.exp z + h)) z := by
  change HasDerivAt (fun t : ℝ => Real.log (Real.exp t + h) - t) _ z
  have hd := (((Real.hasDerivAt_exp z).add_const h).log
    (show Real.exp z + h ≠ 0 by positivity)).sub (hasDerivAt_id z)
  have heq : -h / (Real.exp z + h) = Real.exp z / (Real.exp z + h) - 1 := by
    field_simp [show Real.exp z + h ≠ 0 by positivity]
    ring
  rw [heq]
  exact hd

private theorem logCorrection_derivative_bound {h n z : ℝ}
    (hh : 0 ≤ h) (hn : 0 < n) (hz : Real.log n ≤ z) :
    ‖deriv (logCorrection h) z‖ ≤ h / n := by
  have hexp : n ≤ Real.exp z := by
    rw [← Real.exp_log hn]
    exact Real.exp_le_exp.mpr hz
  rw [(hasDerivAt_logCorrection hh).deriv, Real.norm_eq_abs, abs_div,
    abs_neg, abs_of_nonneg hh, abs_of_pos (by positivity : 0 < Real.exp z + h)]
  exact div_le_div_of_nonneg_left hh hn (by linarith)

private theorem logCorrection_log {h V : ℝ} (hh : 0 ≤ h) (hV : 0 < V) :
    logCorrection h (Real.log V) = Real.log (1 + h / V) := by
  unfold logCorrection
  rw [Real.exp_log hV, ← Real.log_div (by positivity : V + h ≠ 0) hV.ne']
  congr 1
  field_simp [hV.ne']

/-- The residual denominator correction has Lipschitz constant `h/n`
in logarithmic coordinates whenever both amounts are at least `n`. -/
theorem log_correction_lipschitz {h n V W : ℝ} (hh : 0 ≤ h) (hn : 0 < n)
    (hV : n ≤ V) (hW : n ≤ W) :
    |Real.log (1 + h / V) - Real.log (1 + h / W)| ≤
      (h / n) * |Real.log V - Real.log W| := by
  have hVp : 0 < V := hn.trans_le hV
  have hWp : 0 < W := hn.trans_le hW
  have h := (convex_Ici (Real.log n)).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hasDerivAt_logCorrection hh).differentiableAt)
    (fun z hz => logCorrection_derivative_bound hh hn hz)
    (Real.log_le_log hn hW) (Real.log_le_log hn hV)
  simpa only [Real.norm_eq_abs, logCorrection_log hh hVp, logCorrection_log hh hWp] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MarkedCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual logarithmic marked-residual estimate of §10, `src-27`
and `res:marked-cost`, from the square sum and positive marked drops. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem marked_log_correction_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n a p d : ℝ} (hn : 0 < n) (hp : 1 ≤ p) (hd : 0 < d) (A A₀ : E) :
    Real.log (vertexAmount n A a p / d) - Real.log (vertexAmount n A₀ a p / d) ≤
      p * n ^ ((a - 1) / p - 1) * ‖A - A₀‖ := by
  rw [Real.log_div (vertexAmount_pos (a := a) (p := p) hn A).ne' hd.ne',
    Real.log_div (vertexAmount_pos (a := a) (p := p) hn A₀).ne' hd.ne', sub_sub_sub_cancel_right]
  exact (le_abs_self _).trans (log_vertexAmount_lipschitz hn hp A A₀)

theorem marked_log_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ → ℝ) (hn : Antitone n) (S : Finset ℕ)
    (A A₀ : ℕ → E) (denominator : ℕ → ℝ)
    {a p c M B : ℝ} (hp : 1 ≤ p) (hc : 0 < c) (hM : 1 ≤ M)
    (hμ : (a - 1) / p ≤ 1 / 12) (hB : 0 ≤ B)
    (hdrop : ∀ i ∈ S, c ≤ n i - n (i + 1))
    (hmass : ∀ i ∈ S, M ≤ n i) (hden : ∀ i ∈ S, 0 < denominator i)
    (hsquare : (∑ i ∈ S, ‖A i - A₀ i‖ ^ 2) ≤ B ^ 2) :
    (∑ i ∈ S, (Real.log (vertexAmount (n i) (A i) a p / denominator i) -
        Real.log (vertexAmount (n i) (A₀ i) a p / denominator i))) ≤
      p * Real.sqrt (2 * (1 + 3 / c)) *
        M ^ (-(1 / 2 : ℝ) + (a - 1) / p) * B := by
  have hM0 : 0 < M := by linarith
  have hnp (i : ℕ) (hi : i ∈ S) : 0 < n i := hM0.trans_le (hmass i hi)
  have hweights := marked_weight_sum n hn S hc hM hμ hdrop hmass
  have hweightSquare :
      (∑ i ∈ S, (n i ^ ((a - 1) / p - 1)) ^ 2) ≤
        2 * (1 + 3 / c) * M ^ (-1 + 2 * ((a - 1) / p)) := by
    convert hweights using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hnp i hi).le]
    congr 1
    ring
  have hrootWeight : Real.sqrt (∑ i ∈ S, (n i ^ ((a - 1) / p - 1)) ^ 2) ≤
      Real.sqrt (2 * (1 + 3 / c)) * M ^ (-(1 / 2 : ℝ) + (a - 1) / p) := by
    apply (Real.sqrt_le_sqrt hweightSquare).trans_eq
    rw [Real.sqrt_mul (by positivity)]
    simp_rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hM0.le]
    congr 2
    ring
  have hrootResidual : Real.sqrt (∑ i ∈ S, ‖A i - A₀ i‖ ^ 2) ≤ B := by
    exact (Real.sqrt_le_sqrt hsquare).trans_eq (Real.sqrt_sq hB)
  calc
    _ ≤ ∑ i ∈ S, p * n i ^ ((a - 1) / p - 1) * ‖A i - A₀ i‖ :=
      Finset.sum_le_sum fun i hi => marked_log_correction_le (hnp i hi) hp (hden i hi) _ _
    _ = p * ∑ i ∈ S, n i ^ ((a - 1) / p - 1) * ‖A i - A₀ i‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ p * (Real.sqrt (∑ i ∈ S, (n i ^ ((a - 1) / p - 1)) ^ 2) *
        Real.sqrt (∑ i ∈ S, ‖A i - A₀ i‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt S _ _) (by linarith)
    _ ≤ p * ((Real.sqrt (2 * (1 + 3 / c)) *
        M ^ (-(1 / 2 : ℝ) + (a - 1) / p)) * B) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul hrootWeight hrootResidual (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SummationByParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summation by parts for the weighted vector amplitudes of the hierarchy. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_weighted_sum_le_variation (w : ℕ → ℂ) (f : ℕ → E) (N : ℕ) (B : ℝ)
    (hB : ∀ k ≤ N, ‖∑ i ∈ Finset.range (k + 1), f i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (N + 1), w i • f i‖ ≤
      (‖w N‖ + ∑ i ∈ Finset.range N, ‖w (i + 1) - w i‖) * B := by
  rw [Finset.sum_range_by_parts]
  simp only [Nat.add_sub_cancel]
  calc
    _ ≤ ‖w N • ∑ i ∈ Finset.range (N + 1), f i‖ +
        ‖∑ i ∈ Finset.range N, (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), f j‖ :=
      norm_sub_le _ _
    _ ≤ ‖w N‖ * B + ∑ i ∈ Finset.range N, ‖w (i + 1) - w i‖ * B := by
      apply add_le_add
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hB N le_rfl) (norm_nonneg _)
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hB i (by have := Finset.mem_range.mp hi; omega))
          (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SegmentWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight variation on a later segment, paid for by full-root mass loss. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem boundaryLog_nonnegative (n m : ℕ → ℝ) (i : ℕ)
    (hn : 0 < n (i + 1)) (hm : n (i + 1) ≤ m i) : 0 ≤ boundaryLog n m i := by
  exact Real.log_nonneg ((one_le_div hn).2 hm)

theorem boundaryLog_le_root_ratio (n m : ℕ → ℝ) (i K : ℕ)
    (hn : 0 < n (i + 1)) (hm : 0 < m i) (hmn : m i ≤ n (i + 1 - K)) :
    boundaryLog n m i ≤ Real.log (n (i + 1 - K) / n (i + 1)) := by
  exact Real.log_le_log (div_pos hm hn) (div_le_div_of_nonneg_right hmn hn.le)

theorem segmentLog_re_le (n R : ℕ → ℝ) (z : ℕ → ℂ) (a lower : ℝ) (start k : ℕ)
    (ha : 0 ≤ a) (hlower : 0 < lower) (hn : lower ≤ n k)
    (hR : ∀ i < k, 0 ≤ R i) (hz : ∀ i < k, 0 ≤ (z i).re) :
    (segmentLog n R z a start k).re ≤ -a * Real.log lower := by
  have hlog : Real.log lower ≤ Real.log (n k) := Real.log_le_log hlower hn
  have hsum : 0 ≤ ∑ i ∈ Finset.Ico start k, (z i).re * R i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hz i (Finset.mem_Ico.mp hi).2)
      (hR i (Finset.mem_Ico.mp hi).2))
  simp only [segmentLog, Complex.sub_re, Complex.ofReal_re, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith

theorem segmentLog_increment (n R : ℕ → ℝ) (z : ℕ → ℂ) (a : ℝ) (start k : ℕ)
    (hstart : start ≤ k) (hn : 0 < n k) (hn' : 0 < n (k + 1)) :
    segmentLog n R z a start (k + 1) - segmentLog n R z a start k =
      ((a * Real.log (n k / n (k + 1)) : ℝ) : ℂ) - z k * (R k : ℂ) := by
  rw [segmentLog, segmentLog, Finset.sum_Ico_succ_top hstart, Real.log_div hn.ne' hn'.ne']
  push_cast
  ring

theorem segmentLog_variation (n R : ℕ → ℝ) (z : ℕ → ℂ)
    (start N K : ℕ) (a Z : ℝ) (ha : 0 ≤ a) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, 0 < n j) (hmono : AntitoneOn n (Set.Iic N))
    (hR0 : ∀ j < N, 0 ≤ R j)
    (hR : ∀ j < N, R j ≤ Real.log (n (j + 1 - K) / n (j + 1)))
    (hz : ∀ j < N, ‖z j‖ ≤ Z) :
    (∑ j ∈ Finset.Ico start N,
      ‖segmentLog n R z a start (j + 1) - segmentLog n R z a start j‖) ≤
      (a + Z * K) * Real.log (n 0 / n N) := by
  have hP (j : ℕ) (hj : j < N) : 0 ≤ Real.log (n j / n (j + 1)) := by
    apply Real.log_nonneg
    exact (one_le_div (hn (j + 1) (by omega))).2
      (hmono (by change j ≤ N; omega) (by change j + 1 ≤ N; omega) (by omega))
  calc
    _ ≤ ∑ j ∈ Finset.Ico start N, (a * Real.log (n j / n (j + 1)) + Z * R j) := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hsj, hjN⟩ := Finset.mem_Ico.mp hj
      rw [segmentLog_increment n R z a start j hsj (hn j (by omega)) (hn (j + 1) (by omega))]
      exact (logarithm_increment_bound a _ _ _ ha (hP j hjN) (hR0 j hjN)).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hz j hjN) (hR0 j hjN)))
    _ ≤ ∑ j ∈ Finset.range N, (a * Real.log (n j / n (j + 1)) + Z * R j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      · intro j hj _
        have hjN := Finset.mem_range.mp hj
        exact add_nonneg (mul_nonneg ha (hP j hjN)) (mul_nonneg hZ (hR0 j hjN))
    _ = a * Real.log (n 0 / n N) + Z * ∑ j ∈ Finset.range N, R j := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_log_ratios n N hn]
    _ ≤ a * Real.log (n 0 / n N) + Z * ((K : ℝ) * Real.log (n 0 / n N)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (full_root_log_variation n R N K hn hmono hR) hZ)
    _ = _ := by ring

theorem segmentWeight_variation (n R : ℕ → ℝ) (z : ℕ → ℂ)
    (start N K : ℕ) (a lower Z : ℝ) (ha : 0 ≤ a) (hlower : 0 < lower) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, lower ≤ n j) (hmono : AntitoneOn n (Set.Iic N))
    (hR0 : ∀ j < N, 0 ≤ R j)
    (hR : ∀ j < N, R j ≤ Real.log (n (j + 1 - K) / n (j + 1)))
    (hz0 : ∀ j < N, 0 ≤ (z j).re) (hz : ∀ j < N, ‖z j‖ ≤ Z) :
    ‖segmentWeight n R z a start N‖ +
      (∑ j ∈ Finset.Ico start N,
        ‖segmentWeight n R z a start (j + 1) - segmentWeight n R z a start j‖) ≤
      lower ^ (-a) * (1 + (a + Z * K) * Real.log (n 0 / n N)) := by
  let C := -a * Real.log lower
  have hn0 : ∀ j ≤ N, 0 < n j := fun j hj => hlower.trans_le (hn j hj)
  have hbound (j : ℕ) (hj : j ≤ N) : (segmentLog n R z a start j).re ≤ C :=
    segmentLog_re_le n R z a lower start j ha hlower (hn j hj)
      (fun i hi => hR0 i (hi.trans_le hj)) (fun i hi => hz0 i (hi.trans_le hj))
  have hend : ‖segmentWeight n R z a start N‖ ≤ Real.exp C := by
    rw [segmentWeight, Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hbound N le_rfl)
  have hsum : (∑ j ∈ Finset.Ico start N,
      ‖segmentWeight n R z a start (j + 1) - segmentWeight n R z a start j‖) ≤
        Real.exp C * ∑ j ∈ Finset.Ico start N,
          ‖segmentLog n R z a start (j + 1) - segmentLog n R z a start j‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjN := (Finset.mem_Ico.mp hj).2
    exact norm_exp_sub_le_of_re_le _ _ C (hbound j (by omega)) (hbound (j + 1) (by omega))
  have hcost := segmentLog_variation n R z start N K a Z ha hZ hn0 hmono hR0 hR hz
  have htotal := add_le_add hend (hsum.trans (mul_le_mul_of_nonneg_left hcost (Real.exp_pos C).le))
  have heq : Real.exp C = lower ^ (-a) := by
    rw [Real.rpow_def_of_pos hlower]
    simp only [C]
    congr 1
    ring
  rw [heq] at htotal
  nlinarith

theorem boundary_weight_variation (n m : ℕ → ℝ) (z : ℕ → ℂ)
    (start N K : ℕ) (a lower Z : ℝ) (ha : 0 ≤ a) (hlower : 0 < lower) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, lower ≤ n j) (hmono : AntitoneOn n (Set.Iic N))
    (hm : ∀ j < N, n (j + 1) ≤ m j ∧ m j ≤ n (j + 1 - K))
    (hz0 : ∀ j < N, 0 ≤ (z j).re) (hz : ∀ j < N, ‖z j‖ ≤ Z) :
    ‖segmentWeight n (boundaryLog n m) z a start N‖ +
      (∑ j ∈ Finset.Ico start N,
        ‖segmentWeight n (boundaryLog n m) z a start (j + 1) -
          segmentWeight n (boundaryLog n m) z a start j‖) ≤
      lower ^ (-a) * (1 + (a + Z * K) * Real.log (n 0 / n N)) := by
  have hn0 (j : ℕ) (hj : j < N) : 0 < n (j + 1) :=
    hlower.trans_le (hn (j + 1) (by omega))
  exact segmentWeight_variation n (boundaryLog n m) z start N K a lower Z
    ha hlower hZ hn hmono
    (fun j hj => boundaryLog_nonnegative n m j (hn0 j hj) (hm j hj).1)
    (fun j hj => boundaryLog_le_root_ratio n m j K (hn0 j hj)
      ((hn0 j hj).trans_le (hm j hj).1) (hm j hj).2) hz0 hz

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SegmentAmplitudes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vector summation by parts on arbitrary hierarchy segments. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_weighted_Ico_le_variation (w : ℕ → ℂ) (f : ℕ → E)
    (start N : ℕ) (B : ℝ) (hstart : start ≤ N)
    (hB : ∀ k, start ≤ k → k ≤ N → ‖∑ i ∈ Finset.Ico start (k + 1), f i‖ ≤ B) :
    ‖∑ i ∈ Finset.Ico start (N + 1), w i • f i‖ ≤
      (‖w N‖ + ∑ i ∈ Finset.Ico start N, ‖w (i + 1) - w i‖) * B := by
  have hpartial (k : ℕ) (hk : k ≤ N - start) :
      ‖∑ i ∈ Finset.range (k + 1), f (start + i)‖ ≤ B := by
    have hb := hB (start + k) (by omega) (by omega)
    rw [Finset.sum_Ico_eq_sum_range, show start + k + 1 - start = k + 1 by omega] at hb
    exact hb
  have h := norm_weighted_sum_le_variation (fun i => w (start + i))
    (fun i => f (start + i)) (N - start) B hpartial
  have hlength : N + 1 - start = N - start + 1 := by omega
  have hend : start + (N - start) = N := by omega
  simpa only [Finset.sum_Ico_eq_sum_range, hlength, hend, Nat.add_assoc] using h

theorem boundary_segment_amplitude_bound (n m : ℕ → ℝ) (z : ℕ → ℂ) (f : ℕ → E)
    (start N K : ℕ) (a lower Z B : ℝ) (hstart : start ≤ N)
    (ha : 0 ≤ a) (hlower : 0 < lower) (hZ : 0 ≤ Z) (hB0 : 0 ≤ B)
    (hn : ∀ j ≤ N, lower ≤ n j) (hmono : AntitoneOn n (Set.Iic N))
    (hm : ∀ j < N, n (j + 1) ≤ m j ∧ m j ≤ n (j + 1 - K))
    (hz0 : ∀ j < N, 0 ≤ (z j).re) (hz : ∀ j < N, ‖z j‖ ≤ Z)
    (hB : ∀ k, start ≤ k → k ≤ N → ‖∑ i ∈ Finset.Ico start (k + 1), f i‖ ≤ B) :
    ‖∑ i ∈ Finset.Ico start (N + 1), segmentWeight n (boundaryLog n m) z a start i • f i‖ ≤
      (lower ^ (-a) * (1 + (a + Z * K) * Real.log (n 0 / n N))) * B :=
  (norm_weighted_Ico_le_variation _ f start N B hstart hB).trans
    (mul_le_mul_of_nonneg_right
      (boundary_weight_variation n m z start N K a lower Z ha hlower hZ hn hmono hm hz0 hz) hB0)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_ComplementaryMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative motion of a mass fraction retains its complementary mass. -/

noncomputable section

namespace LipschitzHilbert

/-- The logarithm is Lipschitz on a positive half-line, with the sharp
reciprocal lower-bound constant. -/
theorem log_motion_of_lower_bound {x y c : ℝ} (hc : 0 < c)
    (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by
  have hdir (a b : ℝ) (ha : c ≤ a) (hb : c ≤ b) :
      Real.log a - Real.log b ≤ |a - b| / c := by
    have ha0 : 0 < a := hc.trans_le ha
    have hb0 : 0 < b := hc.trans_le hb
    calc
      Real.log a - Real.log b = Real.log (a / b) :=
        (Real.log_div ha0.ne' hb0.ne').symm
      _ ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
      _ = (a - b) / b := by field_simp
      _ ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
      _ ≤ |a - b| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hb
  apply abs_le.mpr
  constructor
  · have h := hdir y x hy hx
    rw [abs_sub_comm y x] at h
    linarith
  · exact hdir x y hx hy

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual decaying top weights and their motion along a reference line. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace SlopeBox

theorem radius_nonnegative (T : SlopeBox) (z : ℝ × ℝ) : 0 ≤ T.radius z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem weight_pos (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    0 < T.weight K D z := by
  unfold weight
  have hr := T.radius_nonnegative z
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) D)
    (Real.rpow_pos_of_pos (by positivity) _)

theorem radius_line_motion (T : SlopeBox) (s t : ℝ) (z : ℝ × ℝ) :
    |T.radius (lineShift s t z) - T.radius z| ≤
      |t| * (1 / T.length + |s - T.slope| / T.width) := by
  have hx : T.horizontal (lineShift s t z) - T.horizontal z = t / T.length := by
    unfold horizontal lineShift
    dsimp
    ring
  have hy : T.transverse (lineShift s t z) - T.transverse z =
      (s - T.slope) * t / T.width := by
    unfold transverse lineShift
    dsimp
    ring
  calc
    _ = |(|T.horizontal (lineShift s t z)| - |T.horizontal z|) +
        (|T.transverse (lineShift s t z)| - |T.transverse z|)| := by
      congr 1
      unfold radius
      ring
    _ ≤ |(|T.horizontal (lineShift s t z)| - |T.horizontal z|)| +
        |(|T.transverse (lineShift s t z)| - |T.transverse z|)| := abs_add_le _ _
    _ ≤ |T.horizontal (lineShift s t z) - T.horizontal z| +
        |T.transverse (lineShift s t z) - T.transverse z| :=
      add_le_add (abs_abs_sub_abs_le_abs_sub _ _) (abs_abs_sub_abs_le_abs_sub _ _)
    _ = _ := by
      rw [hx, hy, abs_div, abs_div, abs_mul, abs_of_pos T.length_pos,
        abs_of_pos T.width_pos]
      ring

theorem log_weight (T : SlopeBox) {K : ℝ} (hK : 0 < K) (D : ℝ) (z : ℝ × ℝ) :
    Real.log (T.weight K D z) = D * Real.log 2 - D * Real.log (1 + T.radius z / K) := by
  have hr := T.radius_nonnegative z
  have hbase : 0 < 1 + T.radius z / K := by positivity
  rw [weight, Real.log_mul (Real.rpow_pos_of_pos (by norm_num) D).ne'
    (Real.rpow_pos_of_pos hbase (-D)).ne', Real.log_rpow (by norm_num), Real.log_rpow hbase]
  ring

/-- No differentiability of absolute values is needed: the logarithm of the
actual weight has this global reference-line motion bound. -/
theorem log_weight_line_motion (T : SlopeBox) {K D : ℝ} (hK : 0 < K) (hD : 0 ≤ D)
    (s t : ℝ) (z : ℝ × ℝ) :
    |Real.log (T.weight K D (lineShift s t z)) - Real.log (T.weight K D z)| ≤
      (D / K) * (1 / T.length + |s - T.slope| / T.width) * |t| := by
  have hb (w : ℝ × ℝ) : 1 ≤ 1 + T.radius w / K := by
    exact le_add_of_nonneg_right (div_nonneg (T.radius_nonnegative w) hK.le)
  have hlog := log_motion_of_lower_bound (by norm_num : (0 : ℝ) < 1)
    (hb (lineShift s t z)) (hb z)
  have heq : (1 + T.radius (lineShift s t z) / K) - (1 + T.radius z / K) =
      (T.radius (lineShift s t z) - T.radius z) / K := by ring
  rw [div_one, heq, abs_div, abs_of_pos hK] at hlog
  have hmove := T.radius_line_motion s t z
  rw [T.log_weight hK, T.log_weight hK]
  calc
    _ = |-(D * (Real.log (1 + T.radius (lineShift s t z) / K) -
        Real.log (1 + T.radius z / K)))| := by congr 1; ring
    _ = D * |Real.log (1 + T.radius (lineShift s t z) / K) -
        Real.log (1 + T.radius z / K)| := by
      rw [abs_neg, abs_mul, abs_of_nonneg hD]
    _ ≤ D * (|T.radius (lineShift s t z) - T.radius z| / K) :=
      mul_le_mul_of_nonneg_left hlog hD
    _ ≤ D * ((|t| * (1 / T.length + |s - T.slope| / T.width)) / K) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmove hK.le) hD
    _ = _ := by ring

end SlopeBox

/-- Termwise logarithmic motion is inherited by every nonempty positive
subsum, with the same constant. This applies equally to complementary masses. -/
theorem positive_sum_log_motion {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (a b : ι → ℝ) {δ : ℝ}
    (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ s, 0 < b i)
    (hmotion : ∀ i ∈ s, |Real.log (b i) - Real.log (a i)| ≤ δ) :
    |Real.log (∑ i ∈ s, b i) - Real.log (∑ i ∈ s, a i)| ≤ δ := by
  have hsumA : 0 < ∑ i ∈ s, a i := Finset.sum_pos ha hne
  have hsumB : 0 < ∑ i ∈ s, b i := Finset.sum_pos hb hne
  have hupper (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
      (h : Real.log x - Real.log y ≤ δ) : x ≤ Real.exp δ * y := by
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ ≤ Real.exp (δ + Real.log y) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hy]
  have hBA : (∑ i ∈ s, b i) ≤ Real.exp δ * ∑ i ∈ s, a i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hupper (b i) (a i) (hb i hi) (ha i hi)
      (abs_le.mp (hmotion i hi)).2
  have hAB : (∑ i ∈ s, a i) ≤ Real.exp δ * ∑ i ∈ s, b i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hupper (a i) (b i) (ha i hi) (hb i hi) (by
      have h := (abs_le.mp (hmotion i hi)).1
      linarith)
  have hlogBA := Real.log_le_log hsumB hBA
  have hlogAB := Real.log_le_log hsumA hAB
  rw [Real.log_mul (Real.exp_pos _).ne' hsumA.ne', Real.log_exp] at hlogBA
  rw [Real.log_mul (Real.exp_pos _).ne' hsumB.ne', Real.log_exp] at hlogAB
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The manuscript's mass motion bound for any fixed nonempty top set,
proved directly from its actual weights on every reference line. -/
theorem top_mass_log_line_motion {ι : Type*} (tops : ι → SlopeBox) (a : Finset ι)
    (hne : a.Nonempty) {K D C : ℝ} (hK : 0 < K) (hD : 0 ≤ D)
    (s t : ℝ) (z : ℝ × ℝ)
    (hlocal : ∀ i ∈ a,
      (D / K) * (1 / (tops i).length + |s - (tops i).slope| / (tops i).width) ≤ C) :
    |Real.log (∑ i ∈ a, (tops i).weight K D (SlopeBox.lineShift s t z)) -
      Real.log (∑ i ∈ a, (tops i).weight K D z)| ≤ C * |t| := by
  apply positive_sum_log_motion a hne
    (fun i => (tops i).weight K D z)
    (fun i => (tops i).weight K D (SlopeBox.lineShift s t z))
    (fun i _ => (tops i).weight_pos hK D z)
    (fun i _ => (tops i).weight_pos hK D _)
  intro i hi
  exact ((tops i).log_weight_line_motion hK hD s t z).trans
    (mul_le_mul_of_nonneg_right (hlocal i hi) (abs_nonneg t))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translated nested angular grids and their actual eligible-top masses. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace AngularGrid

theorem index_parent (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.index (level + 1) slope / (g.branching : ℤ) = g.index level slope := by
  have hG : g.branching ≠ 0 := by have h := g.branching_ge_two; omega
  simpa only [index, pow_succ, mul_assoc] using
    (Int.mul_natCast_floor_div_cancel hG
      (((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level))

variable {ι X : Type*}

theorem cellTops_subset_parent (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (level : ℕ) (child : ℤ) :
    g.cellTops tops slope precision cutoff (level + 1) child ⊆
      g.cellTops tops slope precision cutoff level (child / (g.branching : ℤ)) := by
  intro i hi
  obtain ⟨hit, hindex, heligible⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  apply (g.mem_cellTops _ _ _ _ _ _ _).2
  refine ⟨hit, ?_, g.eligible_parent (hp i hit) level heligible⟩
  rw [← g.index_parent level (slope i), hindex]

theorem mass_nonnegative (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 ≤ weight i x)
    (level : ℕ) (cell : ℤ) (x : X) :
    0 ≤ g.mass tops slope precision cutoff weight level cell x :=
  Finset.sum_nonneg fun i _ => hw i x

theorem mass_pos_of_member (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (cell : ℤ) (x : X) {i : ι}
    (hi : i ∈ g.cellTops tops slope precision cutoff level cell) :
    0 < g.mass tops slope precision cutoff weight level cell x := by
  classical
  exact (hw i x).trans_le (Finset.single_le_sum (fun j _ => (hw j x).le) hi)

/-- An eligible top supplies a strictly positive summand on its own path. -/
theorem path_mass_pos (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 < weight i x)
    (level : ℕ) (top : ι) (htop : top ∈ tops) (heligible : g.eligible cutoff (precision top) level)
    (x : X) : 0 < g.mass tops slope precision cutoff weight level (g.index level (slope top)) x :=
  g.mass_pos_of_member tops slope precision cutoff weight hw level _ x
    ((g.mem_cellTops _ _ _ _ _ _ _).2 ⟨htop, rfl, heligible⟩)

/-- Child mass is at most parent mass, with the eligibility restriction
already built into both finite sums. -/
theorem mass_le_parent (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (hw : ∀ i x, 0 ≤ weight i x) (level : ℕ) (child : ℤ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) child x ≤
      g.mass tops slope precision cutoff weight level (child / (g.branching : ℤ)) x := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (g.cellTops_subset_parent tops slope precision cutoff hp level child) (fun i _ _ => hw i x)

/-- Along any fixed top's angular path the actual mass is antitone. -/
theorem path_mass_antitone (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    (hw : ∀ i x, 0 ≤ weight i x) (top : ι) (x : X) :
    Antitone fun level => g.mass tops slope precision cutoff weight level (g.index level (slope top)) x := by
  apply antitone_nat_of_succ_le
  intro level
  simpa only [g.index_parent] using
    g.mass_le_parent tops slope precision cutoff weight hp hw level (g.index (level + 1) (slope top)) x

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric separation in the actual translated angular grid. -/

noncomputable section

namespace LipschitzHilbert.AngularGrid

/-- The floor assignment is exactly the half-open translated interval. -/
theorem slope_mem_cell (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.left level (g.index level slope) ≤ slope ∧
      slope < g.left level (g.index level slope) + g.width level := by
  let a := ((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level
  have hlow := Int.floor_le a
  have hhigh := Int.lt_floor_add_one a
  have heq : g.width level * a = slope - g.origin := by
    unfold width a
    have hG : (g.branching : ℝ) ≠ 0 := by
      exact_mod_cast (show g.branching ≠ 0 by have h := g.branching_ge_two; omega)
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
  have hlow' := mul_le_mul_of_nonneg_left hlow (g.width_pos level).le
  have hhigh' := mul_lt_mul_of_pos_left hhigh (g.width_pos level)
  rw [heq] at hlow' hhigh'
  change g.origin + g.width level * (⌊a⌋ : ℝ) ≤ slope ∧
    slope < g.origin + g.width level * (⌊a⌋ : ℝ) + g.width level
  constructor <;> nlinarith

theorem slope_dist_center_le (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    |slope - g.center level (g.index level slope)| ≤ g.width level / 2 := by
  obtain ⟨hl, hr⟩ := g.slope_mem_cell level slope
  unfold center
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem same_cell_diameter (g : AngularGrid) (level : ℕ) {s t : ℝ}
    (hcell : g.index level s = g.index level t) : |s - t| ≤ g.width level := by
  obtain ⟨hs0, hs1⟩ := g.slope_mem_cell level s
  obtain ⟨ht0, ht1⟩ := g.slope_mem_cell level t
  rw [hcell] at hs0 hs1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem eligible_iff_precision_le (g : AngularGrid) (cutoff precision : ℝ) (level : ℕ) :
    g.eligible cutoff precision level ↔ precision ≤ cutoff / (g.branching : ℝ) ^ level := by
  have hG : (0 : ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have h := g.branching_ge_two; omega)
  exact (le_div_iff₀ (pow_pos hG level)).symm

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses formed from actual top sets in a common angular ancestor. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_eq_of_add (g : AngularGrid) (base steps : ℕ) {s t : ℝ}
    (h : g.index (base + steps) s = g.index (base + steps) t) :
    g.index base s = g.index base t := by
  induction steps with
  | zero => simpa using h
  | succ steps ih =>
    apply ih
    rw [← g.index_parent (base + steps) s, ← g.index_parent (base + steps) t]
    simpa only [Nat.add_succ] using congrArg (fun a : ℤ => a / g.branching) h

theorem index_eq_of_le (g : AngularGrid) {base level : ℕ} (hle : base ≤ level)
    {s t : ℝ} (h : g.index level s = g.index level t) :
    g.index base s = g.index base t := by
  obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact g.index_eq_of_add base steps h

/-- Tops in a descendant cell remain eligible and lie in its actual ancestor. -/
theorem cellTops_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  intro i hi
  obtain ⟨hit, hindex, he⟩ := (g.mem_cellTops _ _ _ _ _ _ _).1 hi
  exact (g.mem_cellTops _ _ _ _ _ _ _).2
    ⟨hit, g.index_eq_of_le hle hindex, g.eligible_of_le (hp i hit) hle he⟩

theorem parent_subset_boundary (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (base level : ℕ) (gap s : ℝ) :
    g.cellTops tops slope precision cutoff level (g.index level s) ⊆
      g.boundaryTops tops slope precision cutoff base level gap s := by
  classical
  exact Finset.subset_union_left

theorem boundary_subset_ancestor (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ i ∈ tops, 0 ≤ precision i)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) :
    g.boundaryTops tops slope precision cutoff base level gap s ⊆
      g.cellTops tops slope precision cutoff base (g.index base s) := by
  classical
  apply Finset.union_subset
  · exact g.cellTops_subset_ancestor tops slope precision cutoff hp hle s
  · exact Finset.filter_subset _ _

/-- The immediate child, parent, boundary and block ancestor have ordered masses. -/
theorem boundary_mass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {base level : ℕ} (hle : base ≤ level) (gap s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level + 1) (g.index (level + 1) s) x ≤
        g.mass tops slope precision cutoff weight level (g.index level s) x ∧
    g.mass tops slope precision cutoff weight level (g.index level s) x ≤
        g.boundaryMass tops slope precision cutoff weight base level gap s x ∧
    g.boundaryMass tops slope precision cutoff weight base level gap s x ≤
        g.mass tops slope precision cutoff weight base (g.index base s) x := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h := g.mass_le_parent tops slope precision cutoff weight hp hw level
      (g.index (level + 1) s) x
    simpa only [g.index_parent] using h
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.parent_subset_boundary tops slope precision cutoff base level gap s)
      (fun i _ _ => hw i x)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (g.boundary_subset_ancestor tops slope precision cutoff hp hle gap s)
      (fun i _ _ => hw i x)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularPacketAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite packet amplitudes for the actual translated angular grid.
The stopping level belongs to the packet, independently of when its
assigned top loses eligibility. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {σ E : Type*} [AddCommMonoid E] [Module ℂ E]

theorem packetPathProduct_split (g : AngularGrid) (transition : ℕ → ℤ → ℂ)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (slope : ℝ) :
    g.packetPathProduct transition a c slope =
      g.packetPathProduct transition a b slope * g.packetPathProduct transition b c slope :=
  (Finset.prod_Ico_consecutive (fun j => transition j (g.index (j + 1) slope)) hab hbc).symm

theorem packetPathProduct_eq_of_cell (g : AngularGrid) (transition : ℕ → ℤ → ℂ)
    (a b : ℕ) {s t : ℝ} (hcell : g.index b s = g.index b t) :
    g.packetPathProduct transition a b s = g.packetPathProduct transition a b t := by
  unfold packetPathProduct
  apply Finset.prod_congr rfl
  intro j hj
  rw [g.index_eq_of_le (Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2) hcell]

/-- Splitting at a block endpoint isolates exactly the packets that stop
inside the block. No eligibility mass is substituted for these packets. -/
theorem packetAmplitude_split (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    {lower upper : ℕ} (hlu : lower ≤ upper) (cell : ℤ) :
    g.packetAmplitude packets slope stop base transition lower cell =
      g.packetResidual packets slope stop base transition lower upper cell +
      ∑ s ∈ (g.packetSet packets slope stop lower cell).filter (fun s => upper ≤ stop s),
        g.packetPathProduct transition lower upper (slope s) •
          (g.packetPathProduct transition upper (stop s) (slope s) • base s) := by
  classical
  unfold packetAmplitude packetResidual
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (g.packetSet packets slope stop lower cell) (fun s => stop s < upper)
    (fun s => g.packetPathProduct transition lower (stop s) (slope s) • base s)
  rw [← hsplit]
  congr 1
  simp only [not_lt]
  apply Finset.sum_congr rfl
  intro s hs
  rw [g.packetPathProduct_split transition hlu (Finset.mem_filter.mp hs).2, mul_smul]

/-- The block decomposition of the finite packet amplitude. The cells
are actual descendants of the parent and cover all packets surviving
the block; empty cells contribute zero. -/
theorem packetAmplitude_block (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    {lower upper : ℕ} (hlu : lower ≤ upper) (parent : ℤ)
    (cells : Finset ℤ) (representative : ℤ → ℝ)
    (hcell : ∀ c ∈ cells, g.index upper (representative c) = c)
    (hparent : ∀ c ∈ cells, g.index lower (representative c) = parent)
    (hcover : ∀ s ∈ g.packetSet packets slope stop lower parent,
      upper ≤ stop s → g.index upper (slope s) ∈ cells) :
    g.packetAmplitude packets slope stop base transition lower parent =
      g.packetResidual packets slope stop base transition lower upper parent +
      ∑ c ∈ cells, g.packetPathProduct transition lower upper (representative c) •
        g.packetAmplitude packets slope stop base transition upper c := by
  classical
  rw [g.packetAmplitude_split packets slope stop base transition hlu parent]
  congr 1
  let long := (g.packetSet packets slope stop lower parent).filter (fun s => upper ≤ stop s)
  have hmaps : ∀ s ∈ long, g.index upper (slope s) ∈ cells := fun s hs =>
    hcover s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro c hc
  have hset : long.filter (fun s => g.index upper (slope s) = c) =
      g.packetSet packets slope stop upper c := by
    ext s
    constructor
    · intro hs
      obtain ⟨hs, heq⟩ := Finset.mem_filter.mp hs
      obtain ⟨hs, hstop⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, heq, hstop⟩
    · intro hs
      obtain ⟨hsp, heq, hstop⟩ := Finset.mem_filter.mp hs
      have hancestor := g.index_eq_of_le hlu (heq.trans (hcell c hc).symm)
      rw [hparent c hc] at hancestor
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hsp, hancestor, hlu.trans hstop⟩, hstop⟩, heq⟩
  rw [hset, packetAmplitude, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have heq : g.index upper (slope s) = g.index upper (representative c) :=
    (Finset.mem_filter.mp hs).2.1.trans (hcell c hc).symm
  rw [g.packetPathProduct_eq_of_cell transition lower upper heq]

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularAnalyticWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic transition weights for the shared angular packet family.
The exact modulus is the child-to-boundary mass ratio raised to the
real part of the corresponding complex parameter. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

theorem analyticTransition_norm (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) (hm : 0 < mass (level + 1) cell) (hb : 0 < boundary level cell) :
    ‖analyticTransition mass boundary phase level cell‖ =
      (mass (level + 1) cell / boundary level cell) ^ (phase level).re := by
  rw [analyticTransition, Complex.norm_exp, Real.rpow_def_of_pos (div_pos hm hb)]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem analyticTransition_norm_le_one (mass boundary : ℕ → ℤ → ℝ) (phase : ℕ → ℂ)
    (level : ℕ) (cell : ℤ) (hm : 0 < mass (level + 1) cell) (hb : 0 < boundary level cell)
    (hle : mass (level + 1) cell ≤ boundary level cell) (hphase : 0 ≤ (phase level).re) :
    ‖analyticTransition mass boundary phase level cell‖ ≤ 1 := by
  rw [analyticTransition_norm mass boundary phase level cell hm hb]
  exact Real.rpow_le_one (div_nonneg hm.le hb.le) ((div_le_one hb).mpr hle) hphase

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShiftedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted block endpoints of §8. The first block is allowed
to be shorter. Every transition has one phase tag, and each completed
block contains its distinguished phase exactly at the last transition. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert.ShiftedBlocks

variable {K : ℕ}

theorem endpoint_first_bounds (σ : Fin K) : 1 ≤ endpoint σ 1 ∧ endpoint σ 1 ≤ K := by
  simp only [endpoint_succ, Nat.zero_mul, Nat.add_zero]
  have hs := σ.isLt
  omega

theorem endpoint_step (σ : Fin K) (j : ℕ) :
    endpoint σ (j + 2) = endpoint σ (j + 1) + K := by
  simp only [show j + 2 = (j + 1) + 1 by omega, endpoint_succ, Nat.add_mul, Nat.one_mul]
  omega

theorem endpoint_width_le (σ : Fin K) (j : ℕ) :
    endpoint σ (j + 1) ≤ endpoint σ j + K := by
  cases j with
  | zero => simpa using (endpoint_first_bounds σ).2
  | succ j => exact le_of_eq (endpoint_step σ j)

end LipschitzHilbert.ShiftedBlocks

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteLineCells
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact intervals underlying the finite line-mesh index maps. -/

noncomputable section

open Set

namespace LipschitzHilbert.FiniteLineGrid

theorem index_eq_iff_mem_cell (g : FiniteLineGrid) {level : ℕ}
    (hl : level ≤ g.depth) {x : ℝ} (hx : x ∈ g.root) (i : ℕ) :
    (g.index level x).val = i ↔ x ∈ g.cell level i := by
  have hG : (0 : ℝ) < g.branching := by exact_mod_cast g.branching_pos
  have hrep : (x - g.origin) / g.width * (g.branching : ℝ) ^ level =
      (x - g.origin) / g.meshWidth level := by
    unfold meshWidth
    field_simp
  have hn : 0 ≤ (x - g.origin) / g.meshWidth level :=
    div_nonneg (sub_nonneg.mpr hx.1) (g.meshWidth_pos level).le
  simp only [index, rawIndex, Nat.min_eq_left hl, ite_eq_left hx, hrep]
  rw [Nat.floor_eq_iff hn]
  change (i : ℝ) ≤ (x - g.origin) / g.meshWidth level ∧
      (x - g.origin) / g.meshWidth level < i + 1 ↔
    g.origin + g.meshWidth level * i ≤ x ∧ x < g.origin + g.meshWidth level * (i + 1)
  rw [le_div_iff₀ (g.meshWidth_pos level), div_lt_iff₀ (g.meshWidth_pos level)]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> nlinarith

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing localized packet variations with summable box weights. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem cubicVariation_nonneg {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) :
    0 ≤ cubicVariation F N := Real.rpow_nonneg (finiteCubicVariation_nonneg F N) _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationSubsequence
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling partial sums at increasing times cannot increase variation. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem finiteCubicVariation_comp_le {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (q : ℕ → ℕ) (hq : Monotone q) (hN : q N ≤ N) :
    finiteCubicVariation (fun n => F (q n)) N ≤ finiteCubicVariation F N := by
  classical
  unfold finiteCubicVariation
  apply Finset.sup'_le
  intro p _
  by_cases hp : Monotone p
  · rw [ite_eq_left hp]
    let r : Fin (N + 1) → Fin (N + 1) := fun k =>
      ⟨q (p k).val, by have := (hq (show (p k).val ≤ N by omega)).trans hN; omega⟩
    have hr : Monotone r := by
      intro i j hij
      exact hq (hp hij)
    exact partition_le_finiteCubicVariation F N r hr
  · rw [ite_eq_right hp]
    exact finiteCubicVariation_nonneg F N

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual last eligible angular level exists for every positive
precision. Packet stopping precedes the stopping of its assigned top. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem eligible_iff_le_lastEligible (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hstart : g.eligible cutoff precision 0) (n : ℕ) :
    g.eligible cutoff precision n ↔ n ≤ g.lastEligible cutoff precision hp := by
  let h := g.exists_ineligible cutoff precision hp
  have hfirst : 0 < Nat.find h := by
    by_contra hn
    have hz : Nat.find h = 0 := by omega
    apply Nat.find_spec h
    simpa only [hz] using hstart
  constructor
  · intro hn
    by_contra hle
    have hfind : Nat.find h ≤ n := by
      change ¬n ≤ Nat.find h - 1 at hle
      omega
    exact Nat.find_spec h (g.eligible_of_le hp.le hfind hn)
  · intro hn
    have hlt : n < Nat.find h := by
      change n ≤ Nat.find h - 1 at hn
      omega
    exact Classical.not_not.mp (Nat.find_min h hlt)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StoppingScaleIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stopping-level bands are intervals of the original source length
index. This is the bridge from interval concentration to summation by
parts over angular stopping levels. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem antitone_stopping_band_interval {N : ℕ} (stop : Fin N → ℕ)
    (hstop : Antitone stop) (a b : ℕ) :
    ∃ lower upper : ℕ, lower ≤ upper ∧ upper ≤ N ∧
      ∀ j : Fin N, (a ≤ stop j ∧ stop j < b) ↔ lower ≤ j.val ∧ j.val < upper := by
  let s := Finset.univ.filter (fun j : Fin N => a ≤ stop j ∧ stop j < b)
  by_cases hs : s.Nonempty
  · let lo := s.min' hs
    let hi := s.max' hs
    have hlo : lo ∈ s := s.min'_mem hs
    have hhi : hi ∈ s := s.max'_mem hs
    have hlh : lo ≤ hi := s.min'_le hi hhi
    refine ⟨lo.val, hi.val+1, by omega, by omega, ?_⟩
    intro j
    constructor
    · intro hj
      have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have hl := s.min'_le j hjs
      have hr := s.le_max' j hjs
      exact ⟨hl, by change j.val ≤ hi.val at hr; omega⟩
    · intro hj
      have hlj : lo ≤ j := hj.1
      have hjh : j ≤ hi := by change j.val ≤ hi.val; omega
      have hstoplo := (Finset.mem_filter.mp hlo).2.2
      have hstophi := (Finset.mem_filter.mp hhi).2.1
      exact ⟨hstophi.trans (hstop hjh), (hstop hlj).trans_lt hstoplo⟩
  · refine ⟨0,0,le_rfl,Nat.zero_le _,?_⟩
    intro j
    constructor
    · intro hj
      exact False.elim (hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩)
    · intro hj
      omega

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationDisjointExact
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint intervals fit into a partition of the original finite
horizon. Each interval is collapsed to one jump at its right endpoint;
the gaps contribute additional nonnegative variation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

private theorem intervalCollapse_mono (a b : ℕ) : Monotone (intervalCollapse a b) := by
  intro k l hkl
  unfold intervalCollapse
  split_ifs with hk hl
  · exact min_le_min hkl le_rfl
  · exact (min_le_left _ _).trans hkl
  · omega
  · exact hkl

private theorem disjointCollapse_mono {ι : Type*} [Fintype ι] (a b : ι → ℕ) :
    Monotone (disjointCollapse a b) := by
  intro k l hkl
  apply Finset.le_inf'
  intro q _
  have h := Finset.inf'_le
    (fun q : Option ι => q.elim k (fun i => intervalCollapse (a i) (b i) k))
    (Finset.mem_univ q)
  apply h.trans
  cases q with
  | none => exact hkl
  | some i => exact intervalCollapse_mono (a i) (b i) hkl

private theorem disjointCollapse_le {ι : Type*} [Fintype ι] (a b : ι → ℕ) (k : ℕ) :
    disjointCollapse a b k ≤ k :=
  Finset.inf'_le_of_le (f := fun q : Option ι =>
    q.elim k (fun i => intervalCollapse (a i) (b i) k))
    (Finset.mem_univ none) le_rfl

private theorem disjointCollapse_endpoints {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (hab : ∀ i, a i < b i)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) (i : ι) :
    disjointCollapse a b (b i) = b i ∧
      disjointCollapse a b (b i-1) = a i := by
  constructor
  · apply le_antisymm (disjointCollapse_le a b _)
    apply Finset.le_inf'
    intro q _
    cases q with
    | none => exact le_rfl
    | some j =>
      dsimp only [Option.elim_some]
      by_cases hij : i = j
      · subst j
        simp [intervalCollapse]
      · rcases hdisjoint i j hij with h | h
        · have hi : b i ≤ a j := h
          unfold intervalCollapse
          split_ifs <;> omega
        · have hj := hab i
          have hbji : b j ≤ b i := h.trans hj.le
          simp [intervalCollapse,not_lt.mpr hbji]
  · apply le_antisymm
    · have heq : intervalCollapse (a i) (b i) (b i-1) = a i := by
        have hi := hab i
        unfold intervalCollapse
        rw [ite_eq_left (by omega),min_eq_right (by omega)]
      exact (Finset.inf'_le
        (fun q : Option ι => q.elim (b i-1) (fun j => intervalCollapse (a j) (b j) (b i-1)))
        (Finset.mem_univ (some i))).trans_eq heq
    · apply Finset.le_inf'
      intro q _
      have hi := hab i
      cases q with
      | none => dsimp only [Option.elim_none]; omega
      | some j =>
        dsimp only [Option.elim_some]
        by_cases hij : i = j
        · subst j
          unfold intervalCollapse
          split_ifs <;> omega
        · rcases hdisjoint i j hij with h | h
          · unfold intervalCollapse
            split_ifs <;> omega
          · have hbji : b j ≤ b i-1 := by omega
            simp only [intervalCollapse,not_lt.mpr hbji,ite_false, if_false]
            omega

/-- No padding or multiplicative loss is needed for disjoint intervals
inside the original finite horizon. -/
theorem disjoint_increment_cube_sum_exact {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) (a b : ι → ℕ)
    (hab : ∀ i, a i < b i) (hb : ∀ i, b i ≤ N)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, ‖F (b i)-F (a i)‖^3) ≤ finiteCubicVariation F N := by
  classical
  let p : Fin (N+1) → Fin (N+1) := fun k =>
    ⟨disjointCollapse a b k.val, (disjointCollapse_le a b k.val).trans_lt k.isLt⟩
  have hp : Monotone p := fun _ _ h => disjointCollapse_mono a b h
  let e : ι → Fin N := fun i => ⟨b i-1, by have := hab i; have := hb i; omega⟩
  have he : Function.Injective e := by
    intro i j hij
    have heq := congrArg Fin.val hij
    dsimp only [e] at heq
    by_contra hne
    have hi := hab i
    have hj := hab j
    rcases hdisjoint i j hne with h | h <;> omega
  have hpa (i : ι) : (p (e i).castSucc).val = a i :=
    (disjointCollapse_endpoints a b hab hdisjoint i).2
  have hpb (i : ι) : (p (e i).succ).val = b i := by
    have hi := hab i
    change disjointCollapse a b (b i-1+1) = b i
    rw [Nat.sub_add_cancel (by omega)]
    exact (disjointCollapse_endpoints a b hab hdisjoint i).1
  have hselect : (∑ i, ‖F (b i)-F (a i)‖^3) ≤
      ∑ j : Fin N, ‖F (p j.succ)-F (p j.castSucc)‖^3 := by
    refine OAI.sum_le_sum_of_injOn (s := Finset.univ) (t := Finset.univ)
      e (fun i _ j _ h => he h) (Finset.subset_univ _) ?_ ?_
    · intro i _
      rw [hpa,hpb]
    · intro j _ _
      positivity
  exact hselect.trans (partition_le_finiteCubicVariation F N p hp)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketLatticeData
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite packet family before choosing a reference direction.
There is no small-shear condition on its slopes. That condition is proved
only for the labels retained in a short reference cone. -/
noncomputable section
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone * w ≤ P.width)
  (hfrequency : ∀ k, |P.frequency k| ≤ F / w)

local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_actualZ (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).actualZ j l u = P.actualZ j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u +
      (oldSlope - newSlope) * P.actualX j
        (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  dsimp [SourceLabeledLattice.actualZ, actualZ, actualX, referenceFamily,
    SourceLabeledLattice.length, length]
  ring

theorem referenceFamily_physicalPacket (j : Fin N) (l : (Q).labels j)
    (u : Item j l) (k : κ) :
    (Q).physicalPacket newSlope j l u k = P.physicalPacket oldSlope j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u k := by
  let l₀ := P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l
  have hx := P.referenceFamily_actualX oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  have hz := P.referenceFamily_actualZ oldSlope newSlope referenceLength cone w F
    hw hcone hF hwide hfrequency j l u
  unfold SourceLabeledLattice.physicalPacket physicalPacket
  rw [hx, hz]
  have hc : P.actualZ j l₀ u + (oldSlope - newSlope) * P.actualX j l₀ u +
      newSlope * P.actualX j l₀ u = P.actualZ j l₀ u + oldSlope * P.actualX j l₀ u := by ring
  have hs : newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope)) =
      oldSlope + P.rowSlope j l₀ := by ring
  change physicalPlanarPacket (P.profile j l₀ u k) _ _ (P.length j) P.width
    (newSlope + (P.rowSlope j l₀ + (oldSlope - newSlope))) (P.frequency k) _ _ = _
  rw [hc, hs]

end PacketLatticeData
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
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataCoefficient
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analyzing coefficients for unrestricted packet lattices and their
exact transport to the local reference lattice. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

variable (oldSlope newSlope referenceLength cone w F : ℝ)
  (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F) (hwide : cone*w≤P.width)
  (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency

theorem referenceFamily_multiplier_coefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope
      (P.referenceSelector oldSlope newSlope referenceLength cone w F hw hcone hF hwide hfrequency b)
      v g j l u =
    P.physicalMultiplierCoefficient oldSlope b v g j
      (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u := by
  ext k
  simp only [SourceLabeledLattice.physicalMultiplierCoefficient,physicalMultiplierCoefficient,
    analyzingCoefficient,WithLp.ofLp_toLp]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hp := congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
    (P.referenceFamily_physicalPacket oldSlope newSlope referenceLength cone w F
      hw hcone hF hwide hfrequency j l u k)
  dsimp only [referenceSelector]
  rw [hp]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularBoundaryLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Locality of every top entering a boundary mass, including boundaries
whose block ancestor starts before the current path cell. The estimate uses
the immediate child-neighbor relation and therefore does not depend on that
ancestor's width. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

theorem width_antitone (g : AngularGrid) : Antitone g.width := by
  intro h i hhi
  have hG : (1:ℝ) ≤ g.branching := by
    exact_mod_cast (show 1 ≤ g.branching by have := g.branching_ge_two; omega)
  unfold width
  exact div_le_div_of_nonneg_left g.rootWidth_pos.le (by positivity)
    (pow_le_pow_right₀ hG hhi)

/-- Neighboring children control all slopes in those children. -/
theorem slopes_close_of_neighbors (g : AngularGrid) (level : ℕ) (gap s t : ℝ)
    (hnear : g.neighbors level gap (g.index level s) (g.index level t)) :
    |s-t| ≤ gap + 2*g.width level := by
  have hs := g.slope_dist_center_le level s
  have ht := g.slope_dist_center_le level t
  have hc : |g.center level (g.index level s)-g.center level (g.index level t)| <
      gap+g.width level := hnear
  have htriangle : |s-t| ≤ |s-g.center level (g.index level s)| +
      |g.center level (g.index level s)-g.center level (g.index level t)| +
      |g.center level (g.index level t)-t| := by
    calc
      _ = |(s-g.center level (g.index level s)) +
          (g.center level (g.index level s)-g.center level (g.index level t)) +
          (g.center level (g.index level t)-t)| := by congr 1; ring
      _ ≤ |(s-g.center level (g.index level s)) +
          (g.center level (g.index level s)-g.center level (g.index level t))| +
          |g.center level (g.index level t)-t| := abs_add_le _ _
      _ ≤ _ := add_le_add
        (abs_add_le (s-g.center level (g.index level s))
          (g.center level (g.index level s)-g.center level (g.index level t))) le_rfl
  rw [abs_sub_comm (g.center level (g.index level t)) t] at htriangle
  linarith

/-- The immediate-child neighborhood gives locality even when `base < h`.
All such tops are also eligible at the current path level `h`. -/
theorem boundaryTop_locality (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap : 0 ≤ gap)
    (s sR : ℝ) (hs : g.index h s = g.index h sR) {t : ι}
    (ht : t ∈ g.boundaryTops tops slope precision cutoff base i gap s) :
    t ∈ tops ∧ g.eligible cutoff (precision t) h ∧
      |slope t-sR| ≤ 3*g.width h+gap := by
  have hwidth := g.width_pos h
  rcases Finset.mem_union.mp ht with hparent | hnear
  · obtain ⟨htt,hcell,he⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp hparent
    have hcellh : g.index h (slope t) = g.index h sR :=
      (g.index_eq_of_le hhi hcell).trans hs
    refine ⟨htt,g.eligible_of_le (hp t htt) hhi he,?_⟩
    have hd := g.same_cell_diameter h hcellh
    linarith
  · obtain ⟨hbase,he,hneighbors,_⟩ := Finset.mem_filter.mp hnear
    have htt := ((g.mem_cellTops _ _ _ _ _ _ _).mp hbase).1
    have hd := g.slopes_close_of_neighbors (i+1) gap s (slope t) hneighbors
    have hsR := g.same_cell_diameter h hs
    have hw := g.width_antitone (hhi.trans (Nat.le_succ i))
    refine ⟨htt,g.eligible_of_le (hp t htt) (hhi.trans (Nat.le_succ i)) he,?_⟩
    have htriangle : |slope t-sR| ≤ |slope t-s|+|s-sR| := by
      simpa only [sub_add_sub_cancel] using abs_add_le (slope t-s) (s-sR)
    rw [abs_sub_comm (slope t) s] at htriangle
    linarith

/-- Every nonempty submass, including a complementary top set, inherits
its logarithmic line-motion bound from the concrete boundary locality. -/
theorem boundary_submass_log_line_motion (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w W cutoff K D : ℝ) (hw : 0 < w) (hW : 0 < W)
    (hK : 0 < K) (hD : 0 ≤ D) (hwidth : ∀ t ∈ tops, W ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap : 0 ≤ gap)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (A : Finset ι) (hA : A.Nonempty)
    (hsub : A ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cutoff base i gap s)
    (a : ℝ) (z : ℝ × ℝ) :
    |Real.log (∑ t ∈ A, (T t).weight K D (SlopeBox.lineShift sR a z)) -
      Real.log (∑ t ∈ A, (T t).weight K D z)| ≤
        ((D/K) * (cutoff/((g.branching:ℝ)^h*w) + (3*g.width h+gap)/W)) * |a| := by
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ w/(T t).length :=
    (div_pos hw (T t).length_pos).le
  apply top_mass_log_line_motion T A hA hK hD sR a z
  intro t ht
  have hlocal := g.boundaryTop_locality tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cutoff hp base h i hhi gap hgap s sR hs (hsub ht)
  have hprec := (g.eligible_iff_precision_le cutoff (w/(T t).length) h).mp hlocal.2.1
  have hlength : 1/(T t).length ≤ cutoff/((g.branching:ℝ)^h*w) := by
    calc
      1/(T t).length = (w/(T t).length)/w := by
        field_simp [hw.ne', (T t).length_pos.ne']
      _ ≤ (cutoff/(g.branching:ℝ)^h)/w := div_le_div_of_nonneg_right hprec hw.le
      _ = _ := div_div _ _ _
  have hR : 0 ≤ 3*g.width h+gap := by have := g.width_pos h; positivity
  have hslope : |sR-(T t).slope|/(T t).width ≤ (3*g.width h+gap)/W := by
    calc
      _ ≤ (3*g.width h+gap)/(T t).width :=
        div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using hlocal.2.2)
          (T t).width_pos.le
      _ ≤ _ := div_le_div_of_nonneg_left hR hW (hwidth t hlocal.1)
  exact mul_le_mul_of_nonneg_left (add_le_add hlength hslope) (div_nonneg hD hK.le)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary masses and logarithmic variation along actual eligible top
paths. Every boundary uses the start of the block whose last transition
is the current level, in the shared family of all shifted groupings. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι X : Type*}

attribute [local instance] Classical.propDecidable

theorem index_center (g : AngularGrid) (level : ℕ) (cell : ℤ) :
    g.index level (g.center level cell) = cell := by
  have hG : (g.branching : ℝ) ≠ 0 := by
    exact_mod_cast (show g.branching ≠ 0 by have := g.branching_ge_two; omega)
  have heq : ((g.center level cell - g.origin) / g.rootWidth) *
      (g.branching : ℝ)^level = (cell : ℝ) + 1/2 := by
    unfold center left width
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
    ring
  unfold index
  rw [heq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num

theorem boundaryTops_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) {base level : ℕ} (hle : base ≤ level)
    (gap : ℝ) {s t : ℝ} (hc : g.index (level+1) s = g.index (level+1) t) :
    g.boundaryTops tops slope precision cutoff base level gap s =
      g.boundaryTops tops slope precision cutoff base level gap t := by
  have hp := g.index_eq_of_le (Nat.le_succ level) hc
  have ha := g.index_eq_of_le (hle.trans (Nat.le_succ level)) hc
  simp only [boundaryTops, outsideNearTops, hp, ha, hc]

theorem boundaryMass_eq_of_cell (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {base level : ℕ} (hle : base ≤ level) (gap : ℝ) {s t : ℝ}
    (hc : g.index (level+1) s = g.index (level+1) t) (x : X) :
    g.boundaryMass tops slope precision cutoff weight base level gap s x =
      g.boundaryMass tops slope precision cutoff weight base level gap t x := by
  unfold boundaryMass
  rw [g.boundaryTops_eq_of_cell tops slope precision cutoff hle gap hc]

theorem sourceBoundaryMass_path (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level
        (g.index (level+1) s) x =
      g.boundaryMass tops slope precision cutoff weight (level+1-K) level (gap level) s x := by
  apply g.boundaryMass_eq_of_cell tops slope precision cutoff weight (by omega)
  exact g.index_center (level+1) _

theorem sourceBoundaryMass_bounds (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (level : ℕ) (s : ℝ) (x : X) :
    g.mass tops slope precision cutoff weight (level+1) (g.index (level+1) s) x ≤
      g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ∧
    g.sourceBoundaryMass tops slope precision cutoff weight K gap level (g.index (level+1) s) x ≤
      g.mass tops slope precision cutoff weight (level+1-K) (g.index (level+1-K) s) x := by
  rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK gap]
  have h := g.boundary_mass_bounds tops slope precision cutoff weight hp hw
    (by omega : level+1-K ≤ level) (gap level) s x
  exact ⟨h.1.trans h.2.1, h.2.2⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSourceAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shared source amplitude uses the packet's stopping mass and the
actual boundary mass at each transition. The assigned top supplies the
positive mass required by every logarithm along the packet's path. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

variable {ι σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

attribute [local instance] Classical.propDecidable

theorem sourceTransition_norm_le_one (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 < weight i x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (x : X) (level : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (level+1)) (hz : 0 ≤ (phase level).re) :
    ‖g.sourceTransition tops slope precision cutoff weight K gap phase x level
      (g.index (level+1) (slope top))‖ ≤ 1 := by
  have hn := g.path_mass_pos tops slope precision cutoff weight hw (level+1) top htop he x
  have hb := (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
    (fun i x => (hw i x).le) hK gap level (slope top) x).1
  exact analyticTransition_norm_le_one _ _ phase level _ hn (hn.trans_le hb) hb hz

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularMassMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source averaging scale makes every boundary submass move
by order G^(-1/2), including submasses from other shifted blocks. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- The two locality terms are small on the manuscript's averaging cell.
The stronger B² eligibility and width hypotheses retain a spare factor B. -/
theorem source_mass_motion_budget {rho child w B G gap a : ℝ}
    (_hrho : 0 < rho) (hchild : 0 < child) (hw : 0 < w)
    (hB : 1 ≤ B) (hG : 0 < G) (hgap : gap ≤ rho)
    (hblock : rho ≤ B*child) (ha : |a| ≤ w/(child*Real.sqrt G)) :
    (rho/(B^2*w)+(3*rho+gap)/(B^2*w))*|a| ≤ 5/Real.sqrt G := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hroot : 0 < Real.sqrt G := Real.sqrt_pos.mpr hG
  have hden : 0 < B^2*w := mul_pos (sq_pos_of_pos hB0) hw
  have hra : rho*|a| ≤ B*w/Real.sqrt G := by
    calc
      _ ≤ (B*child)*(w/(child*Real.sqrt G)) :=
        mul_le_mul hblock ha (abs_nonneg _) (mul_pos hB0 hchild).le
      _ = _ := by field_simp [hchild.ne', hroot.ne']
  calc
    _ = ((4*rho+gap)*|a|)/(B^2*w) := by ring
    _ ≤ (5*(rho*|a|))/(B^2*w) := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith [abs_nonneg a]
    _ ≤ (5*(B*w/Real.sqrt G))/(B^2*w) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hra (by norm_num)) hden.le
    _ = (5/Real.sqrt G)/B := by field_simp [hB0.ne', hw.ne', hroot.ne']
    _ ≤ 5/Real.sqrt G := div_le_self (by positivity) hB

namespace AngularGrid

variable {ι : Type*}

/-- At H=w/(child sqrt G), concrete boundary submasses have uniformly
small logarithmic motion. Here the top width lower bound is exactly the
consequence W=m w≥B²w used in the source. -/
theorem boundary_submass_source_motion (g : AngularGrid) (tops : Finset ι)
    (T : ι → SlopeBox) (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B)
    (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (A : Finset ι) (hA : A.Nonempty)
    (hsub : A ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (a : ℝ) (ha : |a| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ) :
    |Real.log (∑ t ∈ A, (T t).weight K D (SlopeBox.lineShift sR a z)) -
      Real.log (∑ t ∈ A, (T t).weight K D z)| ≤
        (5*D/K)/Real.sqrt (g.branching:ℝ) := by
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hG : (0:ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have := g.branching_ge_two; omega)
  have hmotion := g.boundary_submass_log_line_motion tops T w (B^2*w) (g.rootWidth/B^2)
    K D hw (mul_pos (sq_pos_of_pos hB0) hw) hK hD hwidth base h i hhi gap hgap0
    s sR hs A hA hsub a z
  have heq : (g.rootWidth/B^2)/((g.branching:ℝ)^h*w) = g.width h/(B^2*w) := by
    simp only [width, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq] at hmotion
  have hbudget := source_mass_motion_budget (g.width_pos h) hchild hw hB hG hgap hblock ha
  calc
    _ ≤ (D/K)*(g.width h/(B^2*w)+(3*g.width h+gap)/(B^2*w))*|a| := hmotion
    _ = (D/K)*((g.width h/(B^2*w)+(3*g.width h+gap)/(B^2*w))*|a|) := by ring
    _ ≤ (D/K)*(5/Real.sqrt (g.branching:ℝ)) :=
      mul_le_mul_of_nonneg_left hbudget (div_nonneg hD hK.le)
    _ = _ := by ring

end AngularGrid

/-- A logarithmic perturbation of a nonzero exponential gives relative
complex motion; the bound does not involve the original logarithm. -/
theorem exponential_relative_motion {a b : ℂ} {E : ℝ}
    (hE : 0 ≤ E) (hmove : ‖b-a‖ ≤ E) :
    ‖Complex.exp b/Complex.exp a-1‖ ≤ Real.exp E*E := by
  have harg : (b-a).re ≤ E := (Complex.re_le_norm _).trans hmove
  have h := norm_exp_sub_le_of_re_le 0 (b-a) E hE harg
  rw [Complex.exp_zero, sub_zero] at h
  have heq : Complex.exp b/Complex.exp a = Complex.exp (b-a) := by
    rw [Complex.exp_sub]
  rw [heq]
  exact h.trans (mul_le_mul_of_nonneg_left hmove (Real.exp_pos E).le)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictionMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mass rescaling and block-transition motion for the snapshot prediction.
Every estimate is relative to the positive snapshot masses; no positive
lower cutoff is imposed on a mass. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem massPowerScale_exp {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (a b : ℝ) :
    massPowerScale n c a b = Real.exp (a*Real.log n+b*Real.log c) := by
  rw [massPowerScale, Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hc, ← Real.exp_add]
  congr 1
  ring

theorem massPowerScale_relative_motion {n n' c c' δ : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 < c) (hc' : 0 < c') (hδ : 0 ≤ δ)
    (hN : |Real.log n'-Real.log n| ≤ δ) (hC : |Real.log c'-Real.log c| ≤ δ)
    (a b : ℝ) :
    let E := (|a|+|b|)*δ
    |massPowerScale n' c' a b/massPowerScale n c a b-1| ≤ Real.exp E*E := by
  dsimp only
  have harg : |(a*Real.log n'+b*Real.log c')-(a*Real.log n+b*Real.log c)| ≤
      (|a|+|b|)*δ := by
    calc
      _ = |a*(Real.log n'-Real.log n)+b*(Real.log c'-Real.log c)| := by congr 1; ring
      _ ≤ |a*(Real.log n'-Real.log n)|+|b*(Real.log c'-Real.log c)| := abs_add_le _ _
      _ = |a| * |Real.log n'-Real.log n|+|b| * |Real.log c'-Real.log c| := by
        rw [abs_mul,abs_mul]
      _ ≤ |a| * δ+|b| * δ := add_le_add (mul_le_mul_of_nonneg_left hN (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hC (abs_nonneg _))
      _ = _ := by ring
  have h := exponential_relative_motion
    (a := ((a*Real.log n+b*Real.log c : ℝ):ℂ))
    (b := ((a*Real.log n'+b*Real.log c' : ℝ):ℂ))
    (show 0 ≤ (|a|+|b|)*δ by positivity)
    (by simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using harg)
  rw [massPowerScale_exp hn' hc',massPowerScale_exp hn hc]
  simpa only [← Complex.ofReal_exp,← Complex.ofReal_div,← Complex.ofReal_one,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h

theorem positive_relative_motion_to_sub {s s' q : ℝ} (hs : 0 < s)
    (h : |s'/s-1| ≤ q) : |s'-s| ≤ q*s := by
  have heq : s'/s-1 = (s'-s)/s := by field_simp [hs.ne']
  rw [heq,abs_div,abs_of_pos hs] at h
  exact (div_le_iff₀ hs).mp h

namespace AngularGrid

theorem source_path_product_norm_le_one {ι X : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ) (x : X)
    (lower upper : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) upper)
    (hphase : ∀ j ∈ Finset.Ico lower upper, 0 ≤ (phase j).re) :
    ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      lower upper (slope top)‖ ≤ 1 := by
  rw [packetPathProduct,norm_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.Ico lower upper, (1:ℝ) := by
      apply Finset.prod_le_prod
      · intro j _
        exact norm_nonneg _
      · intro j hj
        exact g.sourceTransition_norm_le_one tops slope precision cutoff weight hp hw hK gap phase x j top
          htop (g.eligible_of_le (hp top htop) (by have := (Finset.mem_Ico.mp hj).2; omega) he) (hphase j hj)
    _ = _ := by simp

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathCoefficientMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dominant path coefficient from actual complementary top masses.
Empty complementary sets contribute zero and retain the path-drop factor. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid

theorem source_submass_relative_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (base h i : ℕ) (hhi : h ≤ i) (gap : ℝ) (hgap0 : 0 ≤ gap) (hgap : gap ≤ g.width h)
    (s sR : ℝ) (hs : g.index h s = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (A : Finset ι) (hA : A ⊆ g.boundaryTops tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) base i gap s)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ) :
    let mass := fun x => ∑ t ∈ A, (T t).weight K D x
    let δ := (5*D/K)/Real.sqrt (g.branching:ℝ)
    |mass (SlopeBox.lineShift sR b z)-mass z| ≤ Real.exp δ*δ*mass z := by
  classical
  dsimp only
  by_cases hne : A.Nonempty
  · have hm := g.boundary_submass_source_motion tops T w B K D hw hB hK hD hwidth
      base h i hhi gap hgap0 hgap s sR hs child hchild hblock A hne hA b hb z
    have hp (x : ℝ × ℝ) : 0 < ∑ t ∈ A, (T t).weight K D x :=
      Finset.sum_pos (fun t _ => (T t).weight_pos hK D x) hne
    have hrel := massPowerScale_relative_motion (hp z) (hp (SlopeBox.lineShift sR b z))
      (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1)
      (show 0 ≤ (5*D/K)/Real.sqrt (g.branching:ℝ) by positivity)
      hm (by simp; positivity) 1 0
    simp only [massPowerScale,Real.rpow_one,Real.rpow_zero,mul_one,one_mul,
      abs_one,abs_zero,add_zero] at hrel
    exact positive_relative_motion_to_sub (hp z) hrel
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.sum_empty,sub_self,abs_zero,mul_zero,le_refl]

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLineGrid
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual nested line grid with the rounded manuscript step. A single
refinement has mesh H/G, small enough to retain the G^(-1/16) error when
the carrier spread times H is at most G^(15/16). -/

noncomputable section
namespace LipschitzHilbert

theorem sourceLineGrid_mesh (L origin width : ℝ) (depth level : ℕ) (hwidth : 0 < width) :
    (sourceLineGrid L origin width depth hwidth).meshWidth level =
      width/(SourceParameters.step L)^level := by
  simp only [FiniteLineGrid.meshWidth,sourceLineGrid,SourceParameters.step,Nat.cast_pow,Nat.cast_ofNat]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source line scales for a whole angular block. Refinement from the
child scale to the parent scale cancels the angular branching exactly. -/

noncomputable section
namespace LipschitzHilbert

theorem source_block_line_mesh (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (lower start : ℕ) (hle : lower ≤ start)
    (hbranch : (g.branching : ℝ) = SourceParameters.step L) :
    (sourceLineGrid L origin (sourceLineScale g L w start) (start-lower)
      (sourceLineScale_pos g L hw start)).meshWidth (start-lower) =
      sourceLineScale g L w lower := by
  rw [sourceLineGrid_mesh]
  have hG := SourceParameters.step_pos L
  have hpow : SourceParameters.step L ^ start =
      SourceParameters.step L ^ lower * SourceParameters.step L ^ (start-lower) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  unfold sourceLineScale AngularGrid.width
  rw [hbranch, hpow]
  field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual shifted angular blocks meet the source scale conditions.
The first block is included with its original shorter length. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

/-- The ratio of actual angular widths is exactly the iterated step. -/
theorem source_width_ratio (g : AngularGrid) (L : ℝ) {lower upper : ℕ}
    (hle : lower ≤ upper) (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    g.width lower = SourceParameters.step L^(upper-lower)*g.width upper := by
  have hp : SourceParameters.step L^upper =
      SourceParameters.step L^lower*SourceParameters.step L^(upper-lower) := by
    rw [← pow_add,Nat.add_sub_of_le hle]
  unfold width
  rw [hbranch,hp]
  field_simp [(SourceParameters.step_pos L).ne']

/-- Every source block has width ratio between G and B, with exactly the
same conclusion for the initial block. -/
theorem source_shifted_width_bounds (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L)) (j : ℕ) :
    SourceParameters.step L*g.width (ShiftedBlocks.endpoint σ (j+1)) ≤
        g.width (ShiftedBlocks.endpoint σ j) ∧
      g.width (ShiftedBlocks.endpoint σ j) ≤
        SourceParameters.branching L*g.width (ShiftedBlocks.endpoint σ (j+1)) := by
  have hle := (ShiftedBlocks.endpoint_strictMono hK σ) (Nat.lt_succ_self j)
  change ShiftedBlocks.endpoint σ j < ShiftedBlocks.endpoint σ (j+1) at hle
  have hlen := ShiftedBlocks.endpoint_width_le σ j
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  rw [g.source_width_ratio L hle.le hbranch]
  constructor
  · apply mul_le_mul_of_nonneg_right _ (g.width_pos _).le
    calc
      SourceParameters.step L = SourceParameters.step L^1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hG (by omega)
  · apply mul_le_mul_of_nonneg_right _ (g.width_pos _).le
    exact pow_le_pow_right₀ hG (by omega)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_BoundaryTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cancellation of boundary losses along an eligible path in §11. -/

open scoped BigOperators

namespace LipschitzHilbert

/-- Shifting a finite difference sum leaves only its two boundary blocks. -/
theorem sum_range_shift_difference (a : ℕ → ℝ) (k r : ℕ) :
    (∑ i ∈ Finset.range k, (a i - a (i + r))) =
      (∑ i ∈ Finset.range r, a i) - ∑ i ∈ Finset.range r, a (i + k) := by
  have hkr := Finset.sum_range_add a k r
  have hrk := Finset.sum_range_add a r k
  have hlen : (∑ i ∈ Finset.range (k + r), a i) =
      ∑ i ∈ Finset.range (r + k), a i := by rw [Nat.add_comm k r]
  have hs1 : (∑ i ∈ Finset.range k, a (i + r)) =
      ∑ i ∈ Finset.range k, a (r + i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm i r]
  have hs2 : (∑ i ∈ Finset.range r, a (i + k)) =
      ∑ i ∈ Finset.range r, a (k + i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm i k]
  rw [Finset.sum_sub_distrib, hs1, hs2]
  linarith

end LipschitzHilbert

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_ResidualOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Abel summation bounds the actual weighted packet increments by the
unweighted maximum over subintervals of their common prefix sequence. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem interval_packet_sum_le {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (H a b c d : ℕ) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hb : b ≤ H) :
    ‖∑ j ∈ Finset.Ico c d, f j‖ ≤ intervalOscillation (packetPrefix f) H a b := by
  rw [Finset.sum_Ico_eq_sub _ hcd]
  exact increment_le_intervalOscillation (packetPrefix f) H a b c d hac hcd hdb hb

/-- The coefficient-variation estimate uses the full root mass ratio.
The packet maximum itself is restricted to the current segment. -/
theorem boundary_segment_amplitude_le_oscillation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (n m : ℕ → ℝ) (z : ℕ → ℂ) (f : ℕ → E)
    (start N K H a b : ℕ) (power lower Z : ℝ)
    (hstart : start ≤ N) (ha : a ≤ start) (hb : N + 1 ≤ b) (hbH : b ≤ H)
    (hpower : 0 ≤ power) (hlower : 0 < lower) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, lower ≤ n j) (hmono : AntitoneOn n (Set.Iic N))
    (hm : ∀ j < N, n (j + 1) ≤ m j ∧ m j ≤ n (j + 1 - K))
    (hz0 : ∀ j < N, 0 ≤ (z j).re) (hz : ∀ j < N, ‖z j‖ ≤ Z) :
    ‖∑ j ∈ Finset.Ico start (N + 1),
      segmentWeight n (boundaryLog n m) z power start j • f j‖ ≤
      (lower ^ (-power) * (1 + (power + Z * K) * Real.log (n 0 / n N))) *
        intervalOscillation (packetPrefix f) H a b := by
  apply boundary_segment_amplitude_bound n m z f start N K power lower Z _ hstart
    hpower hlower hZ (intervalOscillation_nonneg _ _ _ _) hn hmono hm hz0 hz
  intro k hsk hkN
  exact interval_packet_sum_le f H a b start (k + 1) ha (by omega) (by omega) hbH

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_PathDrops
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic budget for relative drops on an active hierarchy path. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem pathDrop_le_log (n : ℕ → ℝ) (i : ℕ)
    (hi : 0 < n i) (hi' : 0 < n (i + 1)) :
    pathDrop n i ≤ Real.log (n i / n (i + 1)) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hi hi')
  rw [inv_div] at h
  calc
    _ = 1 - n (i + 1) / n i := by unfold pathDrop; field_simp
    _ ≤ _ := h

theorem pathDrop_le_one (n : ℕ → ℝ) (i : ℕ) (hi : 0 < n i)
    (hi' : 0 ≤ n (i + 1)) : pathDrop n i ≤ 1 := by
  exact (div_le_one hi).2 (by linarith)

theorem pathDrop_nonnegative (n : ℕ → ℝ) (i : ℕ) (hi : 0 < n i)
    (hmono : n (i + 1) ≤ n i) : 0 ≤ pathDrop n i :=
  div_nonneg (sub_nonneg.mpr hmono) hi.le

theorem active_path_drop_budget (n : ℕ → ℝ) (N : ℕ) {M : ℝ}
    (hM : 0 < M) (hactive : ∀ i < N, M < n i) (hlast : 0 ≤ n N) :
    (∑ i ∈ Finset.range N, pathDrop n i) ≤ 1 + max 0 (Real.log (n 0 / M)) := by
  cases N with
  | zero => simp only [Finset.sum_range_zero]; positivity
  | succ N =>
    have hn (i : ℕ) (hi : i ≤ N) : 0 < n i := hM.trans (hactive i (by omega))
    have hpre : (∑ i ∈ Finset.range N, pathDrop n i) ≤ Real.log (n 0 / n N) := by
      calc
        _ ≤ ∑ i ∈ Finset.range N, Real.log (n i / n (i + 1)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hiN := Finset.mem_range.mp hi
          exact pathDrop_le_log n i (hn i (by omega)) (hn (i + 1) (by omega))
        _ = _ := sum_log_ratios n N hn
    have hlog : Real.log (n 0 / n N) ≤ Real.log (n 0 / M) := by
      apply Real.log_le_log (div_pos (hn 0 (Nat.zero_le N)) (hn N le_rfl))
      exact div_le_div_of_nonneg_left (hn 0 (Nat.zero_le N)).le hM
        (hactive N (by omega)).le
    have hlastdrop := pathDrop_le_one n N (hn N le_rfl) hlast
    rw [Finset.sum_range_succ]
    linarith [le_max_right 0 (Real.log (n 0 / M))]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLineWindow
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual coarse line cell carries a local grid with exactly the same
fine partitions as the global line grid. This identifies the local
prediction factors before they are patched over coarse cells. -/

noncomputable section
open Set
namespace LipschitzHilbert.FiniteLineGrid

theorem lineWindow_root (g : FiniteLineGrid) (coarse i depth : ℕ) :
    (g.lineWindow coarse i depth).root = g.cell coarse i := by
  change Ico (g.origin+g.meshWidth coarse*i)
      ((g.origin+g.meshWidth coarse*i)+g.meshWidth coarse) =
    Ico (g.origin+g.meshWidth coarse*i) (g.origin+g.meshWidth coarse*((i:ℝ)+1))
  congr 1
  ring

theorem lineWindow_meshWidth (g : FiniteLineGrid) (coarse i depth k : ℕ) :
    (g.lineWindow coarse i depth).meshWidth k = g.meshWidth (coarse+k) := by
  simp only [meshWidth,lineWindow,pow_add,div_div]

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedDrop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path mass at shifted block endpoints is set to zero as soon as
the distinguished top becomes ineligible, even if other tops continue.
The actual drop has the same factor-two reference-window comparison,
including this terminal block. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem shiftedPathMass_nonneg {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hw : ∀ t x, 0 ≤ weight t x)
    (σ : Fin K) (top : ι) (x : X) (j : ℕ) :
    0 ≤ g.shiftedPathMass tops slope precision cutoff weight σ top x j := by
  unfold shiftedPathMass
  split_ifs
  · exact Finset.sum_nonneg fun t _ => hw t x
  · exact le_rfl

theorem shiftedPathMass_antitone {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 ≤ weight t x) (hK : 0 < K)
    (σ : Fin K) (top : ι) (htop : top ∈ tops) (x : X) :
    Antitone (g.shiftedPathMass tops slope precision cutoff weight σ top x) := by
  intro j k hjk
  have hlevel := (ShiftedBlocks.endpoint_strictMono hK σ).monotone hjk
  by_cases hk : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ k)
  · have hj := g.eligible_of_le (hp top htop) hlevel hk
    rw [shiftedPathMass,ite_eq_left hk,shiftedPathMass,ite_eq_left hj]
    exact g.path_mass_antitone tops slope precision cutoff weight hp hw top x hlevel
  · rw [shiftedPathMass,ite_eq_right hk]
    exact g.shiftedPathMass_nonneg tops slope precision cutoff weight hw σ top x j

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMassStopping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite mass stopping index. A terminal ineligible top has
zero path mass, so the source cutoff is attained without a positive lower
bound on any individual top weight. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem firstMassStop_spec (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) :
    firstMassStop n count M ≤ count ∧ n (firstMassStop n count M) ≤ M ∧
      ∀ j < firstMassStop n count M, M < n j := by
  have hex : ∃ j : ℕ, j ≤ count ∧ n j ≤ M := ⟨count,le_rfl,hlast⟩
  rw [firstMassStop,dite_eq_left hex]
  refine ⟨(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩
  intro j hj
  have hn := Nat.find_min hex hj
  have hcount := (Nat.le_of_lt hj).trans (Nat.find_spec hex).1
  exact lt_of_not_ge fun h => hn ⟨hcount,h⟩

theorem firstMassStop_after (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) (hanti : Antitone n) {j : ℕ}
    (hj : firstMassStop n count M ≤ j) : n j ≤ M :=
  (hanti hj).trans (firstMassStop_spec n count M hlast).2.1

theorem firstMassStop_active_iff (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hlast : n count ≤ M) (hanti : Antitone n) (j : ℕ) :
    j < firstMassStop n count M ↔ M < n j := by
  constructor
  · exact (firstMassStop_spec n count M hlast).2.2 j
  · intro hj
    by_contra hn
    exact (not_lt_of_ge (firstMassStop_after n count M hlast hanti (Nat.le_of_not_gt hn))) hj

namespace AngularGrid

theorem shiftedPathMass_terminal_zero {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (σ : Fin K) (top : ι) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ count))
    (x : X) : g.shiftedPathMass tops slope precision cutoff weight σ top x count = 0 := by
  rw [shiftedPathMass,ite_eq_right hterminal]

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePhaseParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform phase and amplitude estimates at the actual source parameters. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

open PhaseCombinatorics

theorem phaseMu_positive_le {D p : ℝ} (hD : 1 ≤ D) (hp : 0 < p) :
    0 < phaseMu D p ∧ phaseMu D p ≤ (4 / 3 : ℝ) / p := by
  have hθ := phaseParameter_range hD
  change 0 < phaseParameter D ∧ phaseParameter D ≤ 1 / 3 at hθ
  constructor
  · exact div_pos (by linarith [hθ.1]) hp
  · exact div_le_div_of_nonneg_right (by linarith [hθ.2]) hp.le

/-- The source's global top-mass bound grows by at most `exp(3 sqrt L)`
after taking the phase power, uniformly in the direction-count parameter. -/
theorem source_phase_mass_bound {D L N : ℝ}
    (hD : 1 ≤ D) (hL : 1 ≤ L) (hN : 0 < N) (hlogN : Real.log N ≤ 2 * L) :
    N ^ phaseMu D (Real.sqrt L) ≤ Real.exp (3 * Real.sqrt L) := by
  have hL0 : 0 ≤ L := by linarith
  have hp : 0 < Real.sqrt L := Real.sqrt_pos.2 (by linarith)
  have hμ := phaseMu_positive_le hD hp
  have hsq := Real.sq_sqrt hL0
  rw [Real.rpow_def_of_pos hN]
  apply Real.exp_le_exp.mpr
  calc
    Real.log N * phaseMu D (Real.sqrt L) ≤ (2 * L) * phaseMu D (Real.sqrt L) :=
      mul_le_mul_of_nonneg_right hlogN hμ.1.le
    _ ≤ (2 * L) * ((4 / 3 : ℝ) / Real.sqrt L) :=
      mul_le_mul_of_nonneg_left hμ.2 (by positivity)
    _ = (8 / 3 : ℝ) * Real.sqrt L := by
      field_simp [hp.ne']
      nlinarith
    _ ≤ 3 * Real.sqrt L := by nlinarith [Real.sqrt_nonneg L]

/-- The amplitude scale `L^C (1+N^mu)` is smaller than every fixed
positive power of the actual rounded dyadic step. This is the source's
subpower estimate used to absorb all marked-cell comparison errors. -/
theorem eventually_source_subpower_amplitude (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ D N : ℝ, 1 ≤ D → 0 < N → Real.log N ≤ 2 * L →
      L ^ C * (1 + N ^ phaseMu D (Real.sqrt L)) ≤ SourceParameters.step L ^ δ := by
  have hpow := tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)
  have hlog : Tendsto (fun L : ℝ => Real.log L / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 10)).tendsto_div_nhds_zero
  have hroot : Tendsto (fun L : ℝ => Real.sqrt L / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hL]
    norm_num
  have hconst : Tendsto (fun L : ℝ => Real.log 2 / L ^ (7 / 10 : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := Real.log 2)).mul (tendsto_inv_atTop_zero.comp hpow)
  have hsum := ((hlog.const_mul C).add hconst).add (hroot.const_mul 3)
  simp only [mul_zero, add_zero] at hsum
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsum.eventually (gt_mem_nhds hδ)] with L hL hsmall
  intro D N hD hN hlogN
  have hL0 : 0 < L := by linarith
  have hpower : 0 < L ^ (7 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hbudget : C * Real.log L + Real.log 2 + 3 * Real.sqrt L ≤ δ * L ^ (7 / 10 : ℝ) := by
    apply (div_le_iff₀ hpower).mp
    convert hsmall.le using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hmass := source_phase_mass_bound hD hL hN hlogN
  have hone : 1 ≤ Real.exp (3 * Real.sqrt L) := Real.one_le_exp (by positivity)
  calc
    _ ≤ L ^ C * (2 * Real.exp (3 * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hL0.le _)
    _ = Real.exp (C * Real.log L + Real.log 2 + 3 * Real.sqrt L) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        Real.rpow_def_of_pos hL0]
      rw [mul_comm C (Real.log L)]
      ring
    _ ≤ Real.exp (δ * L ^ (7 / 10 : ℝ)) := Real.exp_le_exp.mpr hbudget
    _ ≤ SourceParameters.step L ^ δ := by
      rw [Real.rpow_def_of_pos (SourceParameters.step_pos L)]
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left (SourceParameters.log_step_bounds hL0.le).1 hδ.le).trans_eq
        (mul_comm δ _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceCellMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's marking rule uses the infimum of the parent mass
and the supremum of its absolute drop over the entire line cell. The
possible unmarked large drop is the last active index, hence is unique. -/

noncomputable section
open Set
namespace LipschitzHilbert

theorem sourceMarkedCell_active {I : Set ℝ} {n h : ℝ → ℝ} {M x : ℝ}
    (hn : ∀ y ∈ I, 0 ≤ n y) (hm : sourceMarkedCell I n h M) (hx : x ∈ I) :
    M < n x :=
  hm.1.trans_le (csInf_le ⟨0,by rintro _ ⟨y,hy,rfl⟩; exact hn y hy⟩ ⟨x,hx,rfl⟩)

/-- Relative motion on the entire cell turns the supremum condition
into a uniform positive absolute drop, also for a half-open cell. -/
theorem sourceMarkedCell_drop {I : Set ℝ} {n h : ℝ → ℝ} {M E x : ℝ}
    (hE : 0 < E) (hm : sourceMarkedCell I n h M) (hx : x ∈ I)
    (hmove : ∀ y ∈ I, h y ≤ E*h x) : (1/2:ℝ)/E ≤ h x := by
  apply (div_le_iff₀ hE).mpr
  have hs : sSup (h '' I) ≤ E*h x :=
    csSup_le ⟨h x,⟨x,hx,rfl⟩⟩ (by rintro _ ⟨y,hy,rfl⟩; exact hmove y hy)
  linarith [hm.2]

/-- If an unmarked cell contains a drop of at least one, its mass
infimum is at most M. Relative motion bounds every mass by E*M. -/
theorem source_unmarked_large_drop {I : Set ℝ} {n h : ℝ → ℝ} {M E x : ℝ}
    (hE : 0 < E) (hx : x ∈ I) (hm : ¬ sourceMarkedCell I n h M)
    (hlarge : 1 ≤ h x) (hbounded : BddAbove (h '' I))
    (hmove : ∀ y ∈ I, n x ≤ E*n y) : n x ≤ E*M := by
  have hsup : (1/2:ℝ) ≤ sSup (h '' I) :=
    (by norm_num : (1/2:ℝ) ≤ 1).trans (hlarge.trans (le_csSup hbounded ⟨x,hx,rfl⟩))
  have hinf : sInf (n '' I) ≤ M := le_of_not_gt (fun he => hm ⟨he,hsup⟩)
  have hlo : n x/E ≤ sInf (n '' I) :=
    le_csInf ⟨n x,⟨x,hx,rfl⟩⟩ (by
      rintro _ ⟨y,hy,rfl⟩
      apply (div_le_iff₀ hE).mpr
      simpa only [mul_comm] using hmove y hy)
  have he := mul_le_mul_of_nonneg_left (hlo.trans hinf) hE.le
  calc
    n x = E*(n x/E) := by field_simp
    _ ≤ E*M := he

/-- A unit absolute drop from a mass below M+1 crosses the stopping
threshold. This is the exceptional index in the source decomposition. -/
theorem source_unmarked_crosses_cutoff {I : Set ℝ} {n next : ℝ → ℝ} {M E x : ℝ}
    (hE : 0 < E) (hx : x ∈ I)
    (hm : ¬ sourceMarkedCell I n (fun y => n y-next y) M)
    (hlarge : 1 ≤ n x-next x)
    (hbounded : BddAbove ((fun y => n y-next y) '' I))
    (hmove : ∀ y ∈ I, n x ≤ E*n y) (hsmall : E*M < M+1) : next x < M := by
  have hn := source_unmarked_large_drop hE hx hm hlarge hbounded hmove
  linarith

/-- The marked/unmarked dichotomy under the quantitative relative motion
used for the actual source weights. -/
theorem source_cell_marking_cases (I : Set ℝ) (n next : ℝ → ℝ) (M q : ℝ)
    (hn : ∀ y ∈ I, 0 ≤ n y) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hsmall : (1+q)*M < M+1)
    (hmove : ∀ x ∈ I, ∀ y ∈ I,
      n x ≤ (1+q)*n y ∧ n x-next x ≤ (1+q)*(n y-next y))
    (x : ℝ) (hx : x ∈ I) :
    (sourceMarkedCell I n (fun y => n y-next y) M →
      M < n x ∧ (1/4:ℝ) ≤ n x-next x) ∧
    (¬ sourceMarkedCell I n (fun y => n y-next y) M →
      1 ≤ n x-next x → n x < M+1 ∧ next x < M) := by
  have hE : 0 < 1+q := by linarith
  have hbounded : BddAbove ((fun y => n y-next y) '' I) :=
    ⟨(1+q)*(n x-next x),by rintro _ ⟨y,hy,rfl⟩; exact (hmove y hy x hx).2⟩
  constructor
  · intro hm
    refine ⟨sourceMarkedCell_active hn hm hx,?_⟩
    have hl := sourceMarkedCell_drop hE hm hx (fun y hy => (hmove y hy x hx).2)
    have hlo : (1/4:ℝ) ≤ (1/2:ℝ)/(1+q) := by
      apply (le_div_iff₀ hE).mpr
      linarith
    exact hlo.trans hl
  · intro hm hlarge
    have hnlarge := source_unmarked_large_drop hE hx hm hlarge hbounded
      (fun y hy => (hmove x hx y hy).1)
    exact ⟨hnlarge.trans_lt hsmall,source_unmarked_crosses_cutoff hE hx hm hlarge hbounded
      (fun y hy => (hmove x hx y hy).1) hsmall⟩

/-- Every exceptional unmarked large drop is the last active index.
There can be only one, independently of the number of angular levels. -/
theorem source_exceptional_index_unique (n : ℕ → ℝ) (M : ℝ)
    (hanti : Antitone n) (exceptional : ℕ → Prop)
    (hactive : ∀ j, exceptional j → M < n j)
    (hstop : ∀ j, exceptional j → n (j+1) ≤ M) :
    Set.Subsingleton {j | exceptional j} := by
  intro i hi j hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hle := hanti (show i+1 ≤ j by omega)
    exact (not_lt_of_ge (hle.trans (hstop i hi))) (hactive j hj)
  · have hle := hanti (show j+1 ≤ i by omega)
    exact (not_lt_of_ge (hle.trans (hstop j hj))) (hactive i hi)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_HierarchyNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized child identity

Exact algebra for §8, equation (src-25): the ratio of the parent amount
(with the residual omitted) to its child denominator equals the weighted
prediction ratio. No estimates or hierarchy hypotheses enter this identity.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem child_normalization_coefficient {n m μ : ℝ} (hn : 0 < n) (hm : 0 < m) :
    (m / n) ^ (1 - μ) * m ^ (μ - 1) = n ^ (μ - 1) := by
  rw [Real.div_rpow hm.le hn.le]
  have hm' : m ^ (1 - μ) * m ^ (μ - 1) = 1 := by
    rw [← Real.rpow_add hm, show (1 - μ) + (μ - 1) = 0 by ring, Real.rpow_zero]
  have hn' : (n ^ (1 - μ))⁻¹ = n ^ (μ - 1) := by
    rw [← Real.rpow_neg hn.le]
    congr 1
    ring
  calc
    _ = (m ^ (1 - μ) * m ^ (μ - 1)) * (n ^ (1 - μ))⁻¹ := by ring
    _ = _ := by rw [hm', one_mul, hn']

theorem normalized_child_sum (n : ℝ) (m : ι → ℝ) (A : ι → E) (lambda : ι → ℂ)
    (μ : ℝ) (hn : 0 < n) (hm : ∀ i, 0 < m i) :
    (∑ i, ((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * lambda i) •
      (((m i ^ (μ - 1) : ℝ) : ℂ) • A i)) =
      ((n ^ (μ - 1) : ℝ) : ℂ) • ∑ i, lambda i • A i := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_smul]
  congr 1
  have hc := congrArg (fun r : ℝ => (r : ℂ)) (child_normalization_coefficient hn (hm i) (μ := μ))
  push_cast at hc
  calc
    _ = (((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * ((m i ^ (μ - 1) : ℝ) : ℂ))) * lambda i := by ring
    _ = _ := by rw [hc]

theorem normalized_vector_power (m : ℝ) (A : E) (μ p : ℝ) (hm : 0 < m) :
    ‖((m ^ (μ - 1) : ℝ) : ℂ) • A‖ ^ p = m ^ ((μ - 1) * p) * ‖A‖ ^ p := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hm.le _),
    Real.mul_rpow (Real.rpow_nonneg hm.le _) (norm_nonneg _), ← Real.rpow_mul hm.le]

/-- Equation (src-25), with every scalar power and normalization explicit. -/
theorem normalized_child_ratio (n : ℝ) (m : ι → ℝ) (A : ι → E) (lambda : ι → ℂ)
    (μ α p : ℝ) (hn : 0 < n) (hm : ∀ i, 0 < m i) (hrelation : p * μ = α - 1) :
    (n + n ^ (α - p) * ‖∑ i, lambda i • A i‖ ^ p) /
      (n + ∑ i, m i ^ (α - p) * ‖A i‖ ^ p) =
    (1 + ‖∑ i, ((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * lambda i) •
      (((m i ^ (μ - 1) : ℝ) : ℂ) • A i)‖ ^ p) /
      (1 + ∑ i, (m i / n) * ‖((m i ^ (μ - 1) : ℝ) : ℂ) • A i‖ ^ p) := by
  have hexp : 1 + (μ - 1) * p = α - p := by nlinarith
  have hnum : n * (1 + ‖∑ i, ((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * lambda i) •
      (((m i ^ (μ - 1) : ℝ) : ℂ) • A i)‖ ^ p) =
      n + n ^ (α - p) * ‖∑ i, lambda i • A i‖ ^ p := by
    rw [normalized_child_sum n m A lambda μ hn hm, normalized_vector_power n _ μ p hn]
    have hpow : n * n ^ ((μ - 1) * p) = n ^ (α - p) := by
      calc
        _ = n ^ (1 : ℝ) * n ^ ((μ - 1) * p) := by rw [Real.rpow_one]
        _ = n ^ (1 + (μ - 1) * p) := (Real.rpow_add hn _ _).symm
        _ = _ := by rw [hexp]
    calc
      _ = n + (n * n ^ ((μ - 1) * p)) * ‖∑ i, lambda i • A i‖ ^ p := by ring
      _ = _ := by rw [hpow]
  have hden : n * (1 + ∑ i, (m i / n) * ‖((m i ^ (μ - 1) : ℝ) : ℂ) • A i‖ ^ p) =
      n + ∑ i, m i ^ (α - p) * ‖A i‖ ^ p := by
    rw [mul_add, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [normalized_vector_power (m i) (A i) μ p (hm i)]
    have hpow : m i * m i ^ ((μ - 1) * p) = m i ^ (α - p) := by
      calc
        _ = m i ^ (1 : ℝ) * m i ^ ((μ - 1) * p) := by rw [Real.rpow_one]
        _ = m i ^ (1 + (μ - 1) * p) := (Real.rpow_add (hm i) _ _).symm
        _ = _ := by rw [hexp]
    calc
      _ = (m i * m i ^ ((μ - 1) * p)) * ‖A i‖ ^ p := by field_simp
      _ = _ := by rw [hpow]
  rw [← hnum, ← hden]
  exact mul_div_mul_left _ _ hn.ne'

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_AngularSegmentWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact exponential form of a source path product beginning at
an arbitrary angular level. This connects the shared family with the
full-root-paid segment variation estimate. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem segmentWeight_eq_path_product (n b : ℕ → ℝ) (phase : ℕ → ℂ)
    (a : ℝ) (start N : ℕ) (hn : 0 < n N)
    (hn' : ∀ j ∈ Finset.Ico start N, 0 < n (j+1))
    (hb : ∀ j ∈ Finset.Ico start N, 0 < b j) :
    segmentWeight n (boundaryLog n b) phase a start N =
      ((n N ^ (-a) : ℝ) : ℂ) * ∏ j ∈ Finset.Ico start N,
        Complex.exp (phase j * (Real.log (n (j+1) / b j) : ℂ)) := by
  have hpow : ((n N ^ (-a) : ℝ) : ℂ) =
      Complex.exp ((-a * Real.log (n N) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hn, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hpow, ← Complex.exp_sum, ← Complex.exp_add, segmentWeight, segmentLog]
  congr 1
  have hsum : (∑ j ∈ Finset.Ico start N, phase j * (Real.log (n (j+1) / b j) : ℂ)) =
      -(∑ j ∈ Finset.Ico start N, phase j * (boundaryLog n b j : ℂ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [boundaryLog, Real.log_div (hn' j hj).ne' (hb j hj).ne',
      Real.log_div (hb j hj).ne' (hn' j hj).ne']
    push_cast
    ring
  rw [hsum]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockChildren
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual block children are the nonempty eligible-top cells. Their
canonical representatives are slopes of eligible tops, including cells
whose packet amplitude is zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem sourceBlockTop_spec {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    let t := g.sourceBlockTop tops slope precision cutoff lower upper parent c
    t ∈ tops ∧ g.index lower (slope t) = parent ∧
      g.eligible cutoff (precision t) upper ∧ g.index upper (slope t) = c.val := by
  have h := (Finset.mem_image.mp c.property).choose_spec
  obtain ⟨hc,he⟩ := Finset.mem_filter.mp h.1
  have ht := (g.mem_cellTops tops slope precision cutoff lower parent _).mp hc
  exact ⟨ht.1,ht.2.1,he,h.2⟩

theorem sourceBlockTop_mem_child {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (c : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    g.sourceBlockTop tops slope precision cutoff lower upper parent c ∈
      g.cellTops tops slope precision cutoff upper c.val := by
  obtain ⟨ht,_,he,hi⟩ := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent c
  exact (g.mem_cellTops tops slope precision cutoff upper c.val _).mpr ⟨ht,hi,he⟩

/-- Every eligible top in the parent selects one of these children. -/
theorem mem_sourceBlockCells_of_top {ι : Type*} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (lower upper : ℕ) (parent : ℤ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hle : lower ≤ upper)
    (top : ι) (htop : top ∈ tops) (hparent : g.index lower (slope top) = parent)
    (he : g.eligible cutoff (precision top) upper) :
    g.index upper (slope top) ∈ g.sourceBlockCells tops slope precision cutoff lower upper parent := by
  apply Finset.mem_image.mpr
  refine ⟨top,Finset.mem_filter.mpr ⟨?_,he⟩,rfl⟩
  exact (g.mem_cellTops tops slope precision cutoff lower parent top).mpr
    ⟨htop,hparent,g.eligible_of_le (hp top htop) hle he⟩

/-- Using the nonempty top children gives the exact packet decomposition.
A child with no surviving packet contributes its actual zero amplitude. -/
theorem sourcePacketAmplitude_block_children {ι σ X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → ι)
    (stop : σ → ℕ) (value : σ → E) (phase : ℕ → ℂ) (a : ℝ) (x : X)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    {lower upper : ℕ} (hle : lower ≤ upper) (parent : ℤ) :
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      value phase a x lower parent =
    g.packetResidual packets (fun s => slope (assigned s)) stop
      (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x) lower upper parent +
    ∑ c : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
        lower upper (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent c)) •
      g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        value phase a x upper c.val := by
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  let representative := fun c : ℤ =>
    if hc : c ∈ cells then slope (g.sourceBlockTop tops slope precision cutoff lower upper parent ⟨c,hc⟩)
      else 0
  have hrep (c : ℤ) (hc : c ∈ cells) :
      representative c = slope (g.sourceBlockTop tops slope precision cutoff lower upper parent ⟨c,hc⟩) := by
    simp only [representative,dite_eq_left hc]
  have hb := g.packetAmplitude_block packets (fun s => slope (assigned s)) stop
    (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
    (g.sourceTransition tops slope precision cutoff weight K gap phase x) hle parent cells representative
    (fun c hc => by rw [hrep c hc]; exact (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent ⟨c,hc⟩).2.2.2)
    (fun c hc => by rw [hrep c hc]; exact (g.sourceBlockTop_spec tops slope precision cutoff lower upper parent ⟨c,hc⟩).2.1)
    (by
      intro s hs hstop
      obtain ⟨hsp,hi,_⟩ := Finset.mem_filter.mp hs
      exact g.mem_sourceBlockCells_of_top tops slope precision cutoff lower upper parent hp hle
        (assigned s) (hassigned s hsp) hi
        (g.eligible_of_le (hp _ (hassigned s hsp)) hstop (heligible s hsp)))
  change g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
    value phase a x lower parent = _ at hb
  rw [← Finset.sum_coe_sort] at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [hrep c.val c.property]
  rfl

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceNodeRatio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized prediction is exactly the source node ratio with its
packet residual removed. The denominator retains the stopped-top mass
and every nonempty eligible child, including zero-amplitude children. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- Exact source equation (src-25), in the actual prediction notation. -/
theorem sourcePredictionValue_eq_nodeRatio (n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) (μ α p : ℝ)
    (hn : 0 < n) (hc : ∀ i, 0 < c i) (hrelation : p*μ = α-1) :
    sourcePredictionValue p μ n c A lam =
      sourceNodeRatio n c A α p (∑ i, lam i • A i) := by
  have h := normalized_child_ratio n c A lam μ α p hn hc hrelation
  simp only [sourcePredictionValue,energyRatio,sourceNodeRatio,sourceNodeDenominator,vertexAmount,
    RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul,mul_assoc] at h ⊢
  convert h.symm using 2
  all_goals try with_reducible_and_instances rfl

/-- Removing a residual is literal subtraction in the parent amplitude,
with the child denominator left unchanged. -/
theorem sourcePredictionValue_eq_residual_free_ratio
    (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (parentAmplitude residual : EuclideanSpace ℂ κ) (μ α p : ℝ)
    (hn : 0 < n) (hc : ∀ i, 0 < c i) (hrelation : p*μ = α-1)
    (hdecomp : parentAmplitude = residual+∑ i, lam i • A i) :
    sourcePredictionValue p μ n c A lam =
      sourceNodeRatio n c A α p (parentAmplitude-residual) := by
  rw [hdecomp,add_sub_cancel_left]
  exact sourcePredictionValue_eq_nodeRatio n c A lam μ α p hn hc hrelation

namespace AngularGrid
attribute [local instance] Classical.propDecidable

/-- On an actual source block, the normalized predictor is exactly beta0:
the node amount with its literal packet residual removed, divided by the
original stopped-mass/child-amount denominator. -/
theorem source_block_residual_free_ratio {τ σ X : Type*}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hprecision : ∀ t ∈ tops, 0 ≤ precision t)
    (hweight : ∀ t x, 0 < weight t x) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : σ → EuclideanSpace ℂ κ) (phase : ℕ → ℂ) (a : ℝ) (x : X)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    {lower upper : ℕ} (hle : lower ≤ upper) (parent : ℤ)
    (hparent : (g.cellTops tops slope precision cutoff lower parent).Nonempty)
    (μ α p : ℝ) (hrelation : p*μ = α-1) :
    let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
    let c := fun i : cells => g.mass tops slope precision cutoff weight upper i.val x
    let A := fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a x upper i.val
    let lam := fun i : cells => g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight K gap phase x) lower upper
      (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i))
    let n := g.mass tops slope precision cutoff weight lower parent x
    let parentAmplitude := g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a x lower parent
    let residual := g.packetResidual packets (fun s => slope (assigned s)) stop
      (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x) lower upper parent
    sourcePredictionValue p μ n c A lam =
      sourceNodeRatio n c A α p (parentAmplitude-residual) := by
  dsimp only
  obtain ⟨t,ht⟩ := hparent
  have hn := g.mass_pos_of_member tops slope precision cutoff weight hweight lower parent x ht
  have hc (i : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
      0 < g.mass tops slope precision cutoff weight upper i.val x :=
    g.mass_pos_of_member tops slope precision cutoff weight hweight upper i.val x
      (g.sourceBlockTop_mem_child tops slope precision cutoff lower upper parent i)
  apply sourcePredictionValue_eq_residual_free_ratio _ _ _ _ _ _ μ α p hn hc hrelation
  exact g.sourcePacketAmplitude_block_children tops slope precision cutoff weight hprecision K gap
    packets assigned stop value phase a x hassigned heligible hle parent

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnarySegmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual stopping indices for the greedy unary-segment decomposition. -/

noncomputable section

namespace LipschitzHilbert

/-- End a completed unary segment at the first accumulated unit drop.
Since each constituent drop is smaller than one, its total is below two. -/
theorem exists_first_unit_drop (n : ℕ → ℝ) (start finish : ℕ)
    (horder : start ≤ finish) (htotal : 1 ≤ n start - n finish)
    (hstep : ∀ j, start ≤ j → j < finish → n j - n (j + 1) < 1) :
    ∃ cut, start < cut ∧ cut ≤ finish ∧ 1 ≤ n start - n cut ∧
      n start - n cut < 2 ∧ ∀ j, start ≤ j → j < cut → n start - n j < 1 := by
  classical
  let P := fun j => start ≤ j ∧ j ≤ finish ∧ 1 ≤ n start - n j
  have hex : ∃ j, P j := ⟨finish, horder, le_rfl, htotal⟩
  let cut := Nat.find hex
  have hcut : P cut := Nat.find_spec hex
  have hstrict : start < cut := by
    have hne : start ≠ cut := by
      intro heq
      have h := hcut.2.2
      rw [← heq, sub_self] at h
      norm_num at h
    exact lt_of_le_of_ne hcut.1 hne
  have hbefore : ∀ j, start ≤ j → j < cut → n start - n j < 1 := by
    intro j hj hjcut
    have hnot : ¬P j := Nat.find_min hex hjcut
    have hjfinish : j ≤ finish := hjcut.le.trans hcut.2.1
    by_contra h
    exact hnot ⟨hj, hjfinish, le_of_not_gt h⟩
  have hpred : n start - n (cut - 1) < 1 := hbefore (cut - 1) (by omega) (by omega)
  have hlast := hstep (cut - 1) (by omega) (by omega)
  have hsucc : cut - 1 + 1 = cut := by omega
  rw [hsucc] at hlast
  exact ⟨cut, hstrict, hcut.2.1, hcut.2.2, by linarith, hbefore⟩

/-- Greedy unit-drop stopping constructs the partition, with at most the
last segment incomplete. There is no bound on the number of tiny drops. -/
theorem exists_unary_segment_partition (n : ℕ → ℝ) (start finish : ℕ)
    (horder : start ≤ finish)
    (hstep : ∀ j, start ≤ j → j < finish → n j - n (j + 1) < 1) :
    Nonempty (UnarySegmentPartition n start finish) := by
  classical
  by_cases hempty : start = finish
  · subst finish
    exact ⟨{
      blocks := ∅
      bounds := by simp
      cover := by intro j hj hj'; omega
      ordered := by simp
      drop_lt_two := by simp
      completed := by simp }⟩
  have hstrict : start < finish := lt_of_le_of_ne horder hempty
  by_cases htotal : 1 ≤ n start - n finish
  · obtain ⟨cut, hcut, hcutend, hdrop, htwo, _⟩ :=
      exists_first_unit_drop n start finish horder htotal hstep
    obtain ⟨tail⟩ := exists_unary_segment_partition n cut finish hcutend
      (fun j hj hjf => hstep j (hcut.le.trans hj) hjf)
    refine ⟨{
      blocks := insert (start, cut) tail.blocks
      bounds := ?_
      cover := ?_
      ordered := ?_
      drop_lt_two := ?_
      completed := ?_ }⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨le_rfl, hcut, hcutend⟩
      · have h := tail.bounds b hb
        exact ⟨hcut.le.trans h.1, h.2⟩
    · intro j hj hjf
      by_cases hjc : j < cut
      · exact ⟨(start,cut), Finset.mem_insert_self _ _, hj, hjc⟩
      · obtain ⟨b, hb, hbj, hjb⟩ := tail.cover j (by omega) hjf
        exact ⟨b, Finset.mem_insert_of_mem hb, hbj, hjb⟩
    · intro b hb c hc hbc
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rcases Finset.mem_insert.mp hc with rfl | hc
        · exact False.elim (hbc rfl)
        · exact Or.inl (tail.bounds c hc).1
      · rcases Finset.mem_insert.mp hc with rfl | hc
        · exact Or.inr (tail.bounds b hb).1
        · exact tail.ordered b hb c hc hbc
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact htwo
      · exact tail.drop_lt_two b hb
    · intro b hb hbf
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hdrop
      · exact tail.completed b hb hbf
  · refine ⟨{
      blocks := {(start,finish)}
      bounds := ?_
      cover := ?_
      ordered := ?_
      drop_lt_two := ?_
      completed := ?_ }⟩
    · intro b hb
      obtain rfl := Finset.mem_singleton.mp hb
      exact ⟨le_rfl, hstrict, le_rfl⟩
    · intro j hj hjf
      exact ⟨(start,finish), Finset.mem_singleton_self _, hj, hjf⟩
    · intro b hb c hc hbc
      exact False.elim (hbc ((Finset.mem_singleton.mp hb).trans (Finset.mem_singleton.mp hc).symm))
    · intro b hb
      obtain rfl := Finset.mem_singleton.mp hb
      exact (lt_of_not_ge htotal).trans (by norm_num)
    · intro b hb hbf
      obtain rfl := Finset.mem_singleton.mp hb
      exact False.elim (Nat.lt_irrefl _ hbf)
termination_by finish - start
decreasing_by omega

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryPartitionSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact summation over the constructed unary segments. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

namespace UnarySegmentPartition

variable {n : ℕ → ℝ} {start finish : ℕ}

theorem indices_disjoint (P : UnarySegmentPartition n start finish) :
    Set.PairwiseDisjoint (P.blocks : Set (ℕ × ℕ)) (fun b => Finset.Ico b.1 b.2) := by
  intro b hb c hc hbc
  apply Finset.disjoint_left.mpr
  intro j hjb hjc
  obtain ⟨hbj, hjb⟩ := Finset.mem_Ico.mp hjb
  obtain ⟨hcj, hjc⟩ := Finset.mem_Ico.mp hjc
  rcases P.ordered b hb c hc hbc with h | h <;> omega

theorem indices_union (P : UnarySegmentPartition n start finish) :
    P.blocks.biUnion (fun b => Finset.Ico b.1 b.2) = Finset.Ico start finish := by
  ext j
  constructor
  · intro hj
    obtain ⟨b, hb, hjb⟩ := Finset.mem_biUnion.mp hj
    have h := P.bounds b hb
    have hj' := Finset.mem_Ico.mp hjb
    exact Finset.mem_Ico.mpr ⟨h.1.trans hj'.1, hj'.2.trans_le h.2.2⟩
  · intro hj
    obtain ⟨b, hb, hjb, hbj⟩ := P.cover j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_Ico.mpr ⟨hjb, hbj⟩⟩

theorem sum_blocks {E : Type*} [AddCommMonoid E]
    (P : UnarySegmentPartition n start finish) (f : ℕ → E) :
    (∑ b ∈ P.blocks, ∑ j ∈ Finset.Ico b.1 b.2, f j) =
      ∑ j ∈ Finset.Ico start finish, f j := by
  rw [← Finset.sum_biUnion P.indices_disjoint, P.indices_union]

end UnarySegmentPartition

theorem sum_Ico_mass_drop (n : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ j ∈ Finset.Ico a b, (n j - n (j + 1))) = n a - n b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [Finset.sum_Ico_succ_top hb, ih]
    ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryRuns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual consecutive unary runs and their interruption endpoints. -/

noncomputable section

namespace LipschitzHilbert

namespace UnaryRunPartition

theorem separated {unary : ℕ → Prop} {start finish : ℕ}
    (P : UnaryRunPartition unary start finish) {r s : ℕ × ℕ}
    (hr : r ∈ P.runs) (hs : s ∈ P.runs) (hne : r ≠ s) :
    r.2 < s.1 ∨ s.2 < r.1 := by
  rcases P.ordered r hr s hs hne with h | h
  · left
    have hsf := (P.bounds s hs).2
    have hrf : r.2 < finish := h.trans_lt (hsf.1.trans_le hsf.2)
    have hneq : r.2 ≠ s.1 := by
      intro heq
      exact P.interruption r hr hrf (heq ▸ P.inside s hs s.1 le_rfl hsf.1)
    exact lt_of_le_of_ne h hneq
  · right
    have hrf := (P.bounds r hr).2
    have hsf : s.2 < finish := h.trans_lt (hrf.1.trans_le hrf.2)
    have hneq : s.2 ≠ r.1 := by
      intro heq
      exact P.interruption s hs hsf (heq ▸ P.inside r hr r.1 le_rfl hrf.1)
    exact lt_of_le_of_ne h hneq

theorem end_injective {unary : ℕ → Prop} {start finish : ℕ}
    (P : UnaryRunPartition unary start finish) :
    Function.Injective (fun r : P.runs => r.val.2) := by
  intro r s heq
  change r.val.2 = s.val.2 at heq
  by_contra hne
  have h := P.ordered r.val r.property s.val s.property (fun h => hne (Subtype.ext h))
  have hr := (P.bounds r.val r.property).2.1
  have hs := (P.bounds s.val s.property).2.1
  rcases h with h | h <;> omega

end UnaryRunPartition

theorem UnarySegmentPartition.end_injective {n : ℕ → ℝ} {start finish : ℕ}
    (P : UnarySegmentPartition n start finish) :
    Function.Injective (fun r : P.blocks => r.val.2) := by
  intro r s heq
  change r.val.2 = s.val.2 at heq
  by_contra hne
  have h := P.ordered r.val r.property s.val s.property (fun h => hne (Subtype.ext h))
  have hr := (P.bounds r.val r.property).2.1
  have hs := (P.bounds s.val s.property).2.1
  rcases h with h | h <;> omega

private theorem exists_unary_run_end (unary : ℕ → Prop) (start finish : ℕ)
    (hstart : start < finish) (hu : unary start) :
    ∃ stop, start < stop ∧ stop ≤ finish ∧
      (∀ j, start ≤ j → j < stop → unary j) ∧
      (stop < finish → ¬ unary stop) := by
  classical
  let P := fun k => start ≤ k ∧ k ≤ finish ∧ (k = finish ∨ ¬ unary k)
  have hex : ∃ k, P k := ⟨finish, hstart.le, le_rfl, Or.inl rfl⟩
  let stop := Nat.find hex
  have hs : P stop := Nat.find_spec hex
  have hstrict : start < stop := by
    have hne : start ≠ stop := by
      intro heq
      rcases hs.2.2 with h | h
      · omega
      · exact h (heq ▸ hu)
    omega
  refine ⟨stop, hstrict, hs.2.1, ?_, ?_⟩
  · intro j hj hjstop
    by_contra hnot
    exact Nat.find_min hex hjstop ⟨hj, hjstop.le.trans hs.2.1, Or.inr hnot⟩
  · intro hstop
    exact hs.2.2.resolve_left (by omega)

/-- Consecutive runs are constructed from the predicate itself, including
their first nonunary interruption or the final path endpoint. -/
theorem exists_unary_run_partition (unary : ℕ → Prop) (start finish : ℕ)
    (horder : start ≤ finish) : Nonempty (UnaryRunPartition unary start finish) := by
  classical
  by_cases heq : start = finish
  · subst finish
    exact ⟨{
      runs := ∅
      bounds := by simp
      inside := by simp
      cover := by intro j hj hj'; omega
      ordered := by simp
      interruption := by simp }⟩
  have hstrict : start < finish := by omega
  by_cases hu : unary start
  · obtain ⟨stop, hs, hsf, hin, hinterrupt⟩ := exists_unary_run_end unary start finish hstrict hu
    obtain ⟨tail⟩ := exists_unary_run_partition unary stop finish hsf
    refine ⟨{
      runs := insert (start, stop) tail.runs
      bounds := ?_
      inside := ?_
      cover := ?_
      ordered := ?_
      interruption := ?_ }⟩
    · intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact ⟨le_rfl, hs, hsf⟩
      · have h := tail.bounds r hr
        exact ⟨hs.le.trans h.1, h.2⟩
    · intro r hr j hj hjr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hin j hj hjr
      · exact tail.inside r hr j hj hjr
    · intro j hj hjf hjunary
      by_cases hjstop : j < stop
      · exact ⟨(start,stop), Finset.mem_insert_self _ _, hj, hjstop⟩
      · obtain ⟨r, hr, hrj, hjr⟩ := tail.cover j (by omega) hjf hjunary
        exact ⟨r, Finset.mem_insert_of_mem hr, hrj, hjr⟩
    · intro r hr s hs' hrs
      rcases Finset.mem_insert.mp hr with rfl | hr
      · rcases Finset.mem_insert.mp hs' with rfl | hs'
        · exact False.elim (hrs rfl)
        · exact Or.inl (tail.bounds s hs').1
      · rcases Finset.mem_insert.mp hs' with rfl | hs'
        · exact Or.inr (tail.bounds r hr).1
        · exact tail.ordered r hr s hs' hrs
    · intro r hr hrf
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hinterrupt hrf
      · exact tail.interruption r hr hrf
  · obtain ⟨tail⟩ := exists_unary_run_partition unary (start + 1) finish hstrict
    refine ⟨{
      runs := tail.runs
      bounds := ?_
      inside := tail.inside
      cover := ?_
      ordered := tail.ordered
      interruption := tail.interruption }⟩
    · intro r hr
      have h := tail.bounds r hr
      exact ⟨by omega, h.2⟩
    · intro j hj hjf hjunary
      have hne : j ≠ start := by intro he; exact hu (he ▸ hjunary)
      exact tail.cover j (by omega) hjf hjunary
termination_by finish - start
decreasing_by all_goals omega

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryRunCharging
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Charge completed unary segments to themselves and remainders to the
next genuine interruption. The final path remainder is the only exception. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)

private theorem runSegment_eq (i j : UnaryRunSegment R P)
    (hr : i.1 = j.1) (hb : i.2.val.2 = j.2.val.2) : i = j := by
  rcases i with ⟨r, b⟩
  rcases j with ⟨s, c⟩
  dsimp only at hr hb
  subst s
  have hbc : b = c := (P r).end_injective hb
  subst c
  rfl

theorem unaryRunCharge_none (i : UnaryRunSegment R P)
    (hi : unaryRunCharge R P i = none) :
    i.2.val.2 = i.1.val.2 ∧ i.1.val.2 = finish := by
  have hb := (P i.1).bounds i.2.val i.2.property
  have hr := R.bounds i.1.val i.1.property
  unfold unaryRunCharge at hi
  split_ifs at hi with hseg hrun
  exact ⟨by omega, by omega⟩

theorem unaryRunCharge_some (i : UnaryRunSegment R P) (a b : ℕ)
    (hi : unaryRunCharge R P i = some (a,b)) :
    (a = i.2.val.1 ∧ b = i.2.val.2 ∧ i.2.val.2 < i.1.val.2) ∨
      (a = i.1.val.2 ∧ b = i.1.val.2 + 1 ∧
        i.2.val.2 = i.1.val.2 ∧ i.1.val.2 < finish) := by
  have hb := (P i.1).bounds i.2.val i.2.property
  unfold unaryRunCharge at hi
  split_ifs at hi with hseg hrun
  · have heq := Option.some.inj hi
    exact Or.inl ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm, hseg⟩
  · have heq := Option.some.inj hi
    exact Or.inr ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm,
      by omega, hrun⟩

theorem unaryRunCharge_none_unique (i j : UnaryRunSegment R P)
    (hi : unaryRunCharge R P i = none) (hj : unaryRunCharge R P j = none) : i = j := by
  obtain ⟨hbi, hri⟩ := unaryRunCharge_none R P i hi
  obtain ⟨hbj, hrj⟩ := unaryRunCharge_none R P j hj
  have hr : i.1 = j.1 := R.end_injective (hri.trans hrj.symm)
  exact runSegment_eq R P i j hr (by rw [hbi, hbj, hri, hrj])

theorem unaryRunCharge_bounds (i : UnaryRunSegment R P) (a b : ℕ)
    (hi : unaryRunCharge R P i = some (a,b)) :
    i.1.val.1 ≤ a ∧ b ≤ i.1.val.2 + 1 := by
  have hb := (P i.1).bounds i.2.val i.2.property
  rcases unaryRunCharge_some R P i a b hi with h | h
  · obtain ⟨rfl, rfl, _⟩ := h
    exact ⟨hb.1, by omega⟩
  · obtain ⟨rfl, rfl, _, _⟩ := h
    exact ⟨hb.1.trans (hb.2.1.le.trans hb.2.2), le_rfl⟩

theorem unaryRunCharge_disjoint (i j : UnaryRunSegment R P) (a b c d : ℕ)
    (hij : i ≠ j) (hi : unaryRunCharge R P i = some (a,b))
    (hj : unaryRunCharge R P j = some (c,d)) : b ≤ c ∨ d ≤ a := by
  by_cases hr : i.1 = j.1
  · have hne : i.2.val ≠ j.2.val := by
      intro heq
      exact hij (runSegment_eq R P i j hr (congrArg Prod.snd heq))
    have hjmem : j.2.val ∈ (P i.1).blocks := by
      rw [hr]
      exact j.2.property
    have horder := (P i.1).ordered i.2.val i.2.property j.2.val hjmem hne
    rcases unaryRunCharge_some R P i a b hi with hci | hci
    · rcases unaryRunCharge_some R P j c d hj with hcj | hcj
      · rcases hci with ⟨rfl, rfl, _⟩
        rcases hcj with ⟨rfl, rfl, _⟩
        exact horder
      · left
        rw [hci.2.1, hcj.1, ← hr]
        exact (P i.1).bounds i.2.val i.2.property |>.2.2
    · rcases unaryRunCharge_some R P j c d hj with hcj | hcj
      · right
        rw [hcj.2.1, hci.1, hr]
        exact (P j.1).bounds j.2.val j.2.property |>.2.2
      · have hend : i.2.val.2 = j.2.val.2 := by rw [hci.2.2.1, hcj.2.2.1, hr]
        exact False.elim (hij (runSegment_eq R P i j hr hend))
  · have hir := unaryRunCharge_bounds R P i a b hi
    have hjr := unaryRunCharge_bounds R P j c d hj
    have hne : i.1.val ≠ j.1.val := fun h => hr (Subtype.ext h)
    rcases R.separated i.1.property j.1.property hne with h | h
    · exact Or.inl (hir.2.trans ((Nat.succ_le_of_lt h).trans hjr.1))
    · exact Or.inr (hjr.2.trans ((Nat.succ_le_of_lt h).trans hir.1))

theorem unaryRunCharge_mass_drop (hn : Antitone n) {c : ℝ} (hc : c ≤ 1)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬ unary j → c ≤ n j - n (j + 1))
    (i : UnaryRunSegment R P) (a b : ℕ) (hi : unaryRunCharge R P i = some (a,b)) :
    n i.2.val.1 - 2 ≤ n a ∧ n a ≤ n i.2.val.1 ∧ c ≤ n a - n b := by
  have hb := (P i.1).bounds i.2.val i.2.property
  have hr := R.bounds i.1.val i.1.property
  rcases unaryRunCharge_some R P i a b hi with h | h
  · obtain ⟨rfl, rfl, hlast⟩ := h
    exact ⟨by linarith, le_rfl, hc.trans ((P i.1).completed i.2.val i.2.property hlast)⟩
  · obtain ⟨rfl, rfl, hend, hlast⟩ := h
    have hdrop := (P i.1).drop_lt_two i.2.val i.2.property
    rw [hend] at hdrop
    refine ⟨by linarith, hn (hb.2.1.le.trans hb.2.2), ?_⟩
    exact hinterruption i.1.val.2 (hr.1.trans hr.2.1.le) hlast
      (R.interruption i.1.val i.1.property hlast)

/-- All actual unary runs share one charged weight bound. Completed
segments pay their own drops, and every nonfinal remainder pays the next
interruption. There is only one uncharged final remainder on the path. -/
theorem unary_runs_weight_sum (hn : Antitone n) {c M μ : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 1 ≤ M) (hμ : μ ≤ 1 / 12)
    (hmass : ∀ i : UnaryRunSegment R P, M ≤ n i.2.val.1)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬ unary j → c ≤ n j - n (j + 1)) :
    (∑ i : UnaryRunSegment R P, (n i.2.val.1) ^ ((-1 + μ) * (3 / 2 : ℝ))) ≤
      2 * (2 + 17 / c) * M ^ (-(1 / 2 : ℝ) + 3 * μ / 2) := by
  exact interval_charged_segment_weight_sum (fun i : UnaryRunSegment R P => n i.2.val.1)
    (unaryRunCharge R P) n hn (unaryRunCharge_none_unique R P)
    (unaryRunCharge_disjoint R P) hc hM hμ hmass
    (unaryRunCharge_mass_drop R P hn hc1 hinterruption)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryRunVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One common residual variation controls segments from every unary run. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)

theorem unaryRunSegment_intervals_disjoint (i j : UnaryRunSegment R P) (hij : i ≠ j) :
    i.2.val.2 ≤ j.2.val.1 ∨ j.2.val.2 ≤ i.2.val.1 := by
  by_cases hr : i.1 = j.1
  · rcases i with ⟨r,b⟩
    rcases j with ⟨s,c⟩
    dsimp only at hr hij ⊢
    subst s
    have hne : b.val ≠ c.val := by
      intro h
      have heq : b = c := Subtype.ext h
      exact hij (by cases heq; rfl)
    exact (P r).ordered b.val b.property c.val c.property hne
  · have hne : i.1.val ≠ j.1.val := fun h => hr (Subtype.ext h)
    have hbi := (P i.1).bounds i.2.val i.2.property
    have hbj := (P j.1).bounds j.2.val j.2.property
    rcases R.ordered i.1.val i.1.property j.1.val j.1.property hne with h | h
    · exact Or.inl (hbi.2.2.trans (h.trans hbj.1))
    · exact Or.inr (hbj.2.2.trans (h.trans hbi.1))

/-- The actual block-to-angular-level map preserves disjointness. Hence
all unary segments, including different runs, use a single variation bound. -/
theorem unary_runs_oscillation_cube_sum {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (level : ℕ → ℕ) (hlevel : StrictMono level) (N : ℕ)
    (hend : level finish ≤ N) :
    (∑ i : UnaryRunSegment R P,
      intervalOscillation F N (level i.2.val.1) (level i.2.val.2) ^ 3) ≤
      finiteCubicVariation (fun k => F (min k N)) (2 * N) := by
  apply disjoint_intervalOscillation_cube_sum F N
    (fun i : UnaryRunSegment R P => level i.2.val.1)
    (fun i : UnaryRunSegment R P => level i.2.val.2)
  · intro i
    exact hlevel ((P i.1).bounds i.2.val i.2.property).2.1
  · intro i
    have hb := (P i.1).bounds i.2.val i.2.property
    have hr := R.bounds i.1.val i.1.property
    exact (hlevel.monotone (hb.2.2.trans hr.2.2)).trans hend
  · intro i j hij
    exact (unaryRunSegment_intervals_disjoint R P i j hij).imp
      (fun h => hlevel.monotone h) (fun h => hlevel.monotone h)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryRunResidual
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic residual cost over all constructed unary runs. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem unary_runs_residual_sum {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    (hn : Antitone n) {c M μ V : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 1 ≤ M) (hμ : μ ≤ 1 / 12) (hV : 0 ≤ V)
    (hmass : ∀ i : UnaryRunSegment R P, M ≤ n i.2.val.1)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬ unary j → c ≤ n j - n (j + 1))
    {E : Type*} [NormedAddCommGroup E] (F : ℕ → E)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (N : ℕ) (hend : level finish ≤ N)
    (hvariation : finiteCubicVariation (fun k => F (min k N)) (2 * N) ≤ V ^ 3) :
    (∑ i : UnaryRunSegment R P, (n i.2.val.1) ^ (-1 + μ) *
      intervalOscillation F N (level i.2.val.1) (level i.2.val.2)) ≤
      (2 * (2 + 17 / c)) ^ (2 / 3 : ℝ) * M ^ (-(1 / 3 : ℝ) + μ) * V := by
  let mass : UnaryRunSegment R P → ℝ := fun i => n i.2.val.1
  let residual : UnaryRunSegment R P → ℝ := fun i =>
    intervalOscillation F N (level i.2.val.1) (level i.2.val.2)
  have hresidual (i : UnaryRunSegment R P) : 0 ≤ residual i :=
    intervalOscillation_nonneg _ _ _ _
  have hcube : ∑ i, residual i ^ 3 ≤ V ^ 3 :=
    (unary_runs_oscillation_cube_sum R P F level hlevel N hend).trans hvariation
  have hM0 : 0 < M := by linarith
  have hmass0 (i : UnaryRunSegment R P) : 0 < mass i := hM0.trans_le (hmass i)
  have hweight := unary_runs_weight_sum R P hn hc hc1 hM hμ hmass hinterruption
  have hws : (∑ i, (mass i ^ (-1 + μ)) ^ (3 / 2 : ℝ)) ≤
      2 * (2 + 17 / c) * M ^ (-(1 / 2 : ℝ) + 3 * μ / 2) := by
    convert hweight using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    rw [← Real.rpow_mul (hmass0 i).le]
  have hweightRoot : (∑ i, (mass i ^ (-1 + μ)) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
      (2 * (2 + 17 / c)) ^ (2 / 3 : ℝ) * M ^ (-(1 / 3 : ℝ) + μ) := by
    apply (Real.rpow_le_rpow
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Real.rpow_nonneg (hmass0 i).le _) _)
      hws (by norm_num : (0 : ℝ) ≤ 2 / 3)).trans_eq
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hM0.le _), ← Real.rpow_mul hM0.le]
    congr 2
    ring
  have hresidualRoot : (∑ i, residual i ^ (3 : ℝ)) ^ (1 / 3 : ℝ) ≤ V := by
    have hcube' : (∑ i, residual i ^ (3 : ℝ)) ≤ V ^ (3 : ℝ) := by
      convert hcube using 1
      · apply Finset.sum_congr rfl
        intro i _
        exact Real.rpow_natCast _ 3
      · exact Real.rpow_natCast _ 3
    apply (Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hresidual i) _)
      hcube' (by norm_num : (0 : ℝ) ≤ 1 / 3)).trans_eq
    rw [← Real.rpow_mul hV]
    norm_num
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
    (f := fun i => mass i ^ (-1 + μ)) (g := residual)
    (show Real.HolderConjugate (3 / 2 : ℝ) 3 by norm_num [Real.holderConjugate_iff])
    (fun i _ => Real.rpow_nonneg (hmass0 i).le _) (fun i _ => hresidual i)
  norm_num only [one_div_div, div_one] at hholder
  exact hholder.trans (mul_le_mul hweightRoot hresidualRoot
    (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hresidual i) _) _)
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hM0.le _)))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryTelescope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The unary-segment energy telescope

This is the finite cancellation behind §10, equation `src-28`. The actual
and propagated endpoint amounts agree, leaving only amplitude errors and
the small baseline-denominator corrections.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

private theorem log_add_baseline {V h : ℝ} (hV : 0 < V) (hh : 0 ≤ h) :
    Real.log (h + V) = Real.log V + Real.log (1 + h / V) := by
  rw [← Real.log_mul hV.ne' (show 1 + h / V ≠ 0 by positivity)]
  congr 1
  field_simp [hV.ne']
  ring

theorem unary_log_telescope (N : ℕ) (V W h beta : ℕ → ℝ)
    (hV : ∀ i ≤ N, 0 < V i) (hW : ∀ i ≤ N, 0 < W i)
    (hh : ∀ i < N, 0 ≤ h i) (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ V i / (h i + V (i + 1)))
    (hstar : ∀ i < N, W i ≤ h i + W (i + 1)) (hend : W N = V N) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤ Real.log (V 0 / W 0) +
      ∑ i ∈ Finset.range N,
        (Real.log (1 + h i / W (i + 1)) - Real.log (1 + h i / V (i + 1))) := by
  have hstep (i : ℕ) (hi : i < N) :
      Real.log (beta i) ≤
        ((Real.log (V i) - Real.log (W i)) -
          (Real.log (V (i + 1)) - Real.log (W (i + 1)))) +
        (Real.log (1 + h i / W (i + 1)) - Real.log (1 + h i / V (i + 1))) := by
    have hVnext := hV (i + 1) (by omega)
    have hWi := hW i hi.le
    have hWnext := hW (i + 1) (by omega)
    have hdenom : 0 < h i + V (i + 1) := add_pos_of_nonneg_of_pos (hh i hi) hVnext
    have hp := Real.log_le_log (mul_pos (hbeta i hi) hdenom)
      ((le_div_iff₀ hdenom).mp (hprediction i hi))
    rw [Real.log_mul (hbeta i hi).ne' hdenom.ne', log_add_baseline hVnext (hh i hi)] at hp
    have hs := Real.log_le_log hWi (hstar i hi)
    rw [log_add_baseline hWnext (hh i hi)] at hs
    linarith
  have htel : (∑ i ∈ Finset.range N,
      ((Real.log (V i) - Real.log (W i)) -
        (Real.log (V (i + 1)) - Real.log (W (i + 1))))) =
      Real.log (V 0 / W 0) := by
    have h := sum_range_shift_difference (fun i => Real.log (V i) - Real.log (W i)) N 1
    simpa only [Finset.sum_range_one, zero_add, hend, sub_self, sub_zero,
      Real.log_div (hV 0 (Nat.zero_le _)).ne' (hW 0 (Nat.zero_le _)).ne'] using h
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (((Real.log (V i) - Real.log (W i)) -
          (Real.log (V (i + 1)) - Real.log (W (i + 1)))) +
          (Real.log (1 + h i / W (i + 1)) - Real.log (1 + h i / V (i + 1)))) :=
      Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)
    _ = _ := by rw [Finset.sum_add_distrib, htel]

/-- The telescope, with each surviving correction controlled by an
actual logarithmic-energy error and the relative baseline drop. -/
theorem unary_log_telescope_errors (N : ℕ) (V W n h beta error : ℕ → ℝ)
    (hn : ∀ i ≤ N, 0 < n i)
    (hV : ∀ i ≤ N, n i ≤ V i) (hW : ∀ i ≤ N, n i ≤ W i)
    (hh : ∀ i < N, 0 ≤ h i) (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ V i / (h i + V (i + 1)))
    (hstar : ∀ i < N, W i ≤ h i + W (i + 1)) (hend : W N = V N)
    (herror : ∀ i ≤ N, |Real.log (V i) - Real.log (W i)| ≤ error i) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤ error 0 +
      ∑ i ∈ Finset.range N, (h i / n (i + 1)) * error (i + 1) := by
  have hVp (i : ℕ) (hi : i ≤ N) := (hn i hi).trans_le (hV i hi)
  have hWp (i : ℕ) (hi : i ≤ N) := (hn i hi).trans_le (hW i hi)
  apply (unary_log_telescope N V W h beta hVp hWp hh hbeta hprediction hstar hend).trans
  apply add_le_add
  · rw [Real.log_div (hVp 0 (Nat.zero_le _)).ne' (hWp 0 (Nat.zero_le _)).ne']
    exact (le_abs_self _).trans (herror 0 (Nat.zero_le _))
  · apply Finset.sum_le_sum
    intro i hi
    have hin : i < N := Finset.mem_range.mp hi
    have hiN : i + 1 ≤ N := by omega
    have hc := log_correction_lipschitz (hh i hin) (hn (i + 1) hiN)
      (hW (i + 1) hiN) (hV (i + 1) hiN)
    have he : |Real.log (W (i + 1)) - Real.log (V (i + 1))| ≤ error (i + 1) := by
      simpa only [abs_sub_comm] using herror (i + 1) hiN
    exact (le_abs_self _).trans (hc.trans (mul_le_mul_of_nonneg_left he
      (div_nonneg (hh i hin) (hn (i + 1) hiN).le)))

section Vertex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Applying the scalar telescope to the actual vertex amounts gives
the finite form of `src-28` before the segment mass comparison. -/
theorem unary_vertex_telescope (N : ℕ) (n : ℕ → ℝ) (A Astar : ℕ → E)
    (beta : ℕ → ℝ) {a p D : ℝ} (hp : 1 ≤ p) (hap : a ≤ p)
    (hn : ∀ i ≤ N, 0 < n i) (hmass : ∀ i < N, n (i + 1) ≤ n i)
    (hcontraction : ∀ i < N, ‖Astar i‖ ≤ ‖Astar (i + 1)‖)
    (hend : Astar N = A N) (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ vertexAmount (n i) (A i) a p /
      (n i - n (i + 1) + vertexAmount (n (i + 1)) (A (i + 1)) a p))
    (herror : ∀ i ≤ N, ‖A i - Astar i‖ ≤ D) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤
      p * n 0 ^ ((a - 1) / p - 1) * D +
        ∑ i ∈ Finset.range N, ((n i - n (i + 1)) / n (i + 1)) *
          (p * n (i + 1) ^ ((a - 1) / p - 1) * D) := by
  apply unary_log_telescope_errors N
    (fun i => vertexAmount (n i) (A i) a p)
    (fun i => vertexAmount (n i) (Astar i) a p) n
    (fun i => n i - n (i + 1)) beta
    (fun i => p * n i ^ ((a - 1) / p - 1) * D) hn
  · exact fun i hi => mass_le_vertexAmount (hn i hi).le (A i)
  · exact fun i hi => mass_le_vertexAmount (hn i hi).le (Astar i)
  · exact fun i hi => sub_nonneg.mpr (hmass i hi)
  · exact hbeta
  · exact hprediction
  · intro i hi
    exact vertexAmount_subsolution (hn (i + 1) (by omega)) (hmass i hi) hap
      (by linarith) (Astar i) (Astar (i + 1)) (hcontraction i hi)
  · simp only [hend]
  · intro i hi
    exact (log_vertexAmount_lipschitz (hn i hi) hp (A i) (Astar i)).trans
      (mul_le_mul_of_nonneg_left (herror i hi)
        (mul_nonneg (by linarith) (Real.rpow_nonneg (hn i hi).le _)))

/-- A lower mass bound makes all the energy Lipschitz constants uniform.
Only the sum of relative drops remains; no factor counts unary indices. -/
theorem unary_vertex_telescope_uniform (N : ℕ) (n : ℕ → ℝ) (A Astar : ℕ → E)
    (beta : ℕ → ℝ) {a p D m : ℝ} (hp : 1 ≤ p) (hap : a ≤ p)
    (hm : 0 < m) (hD : 0 ≤ D) (hn : ∀ i ≤ N, m ≤ n i)
    (hmass : ∀ i < N, n (i + 1) ≤ n i)
    (hcontraction : ∀ i < N, ‖Astar i‖ ≤ ‖Astar (i + 1)‖)
    (hend : Astar N = A N) (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ vertexAmount (n i) (A i) a p /
      (n i - n (i + 1) + vertexAmount (n (i + 1)) (A (i + 1)) a p))
    (herror : ∀ i ≤ N, ‖A i - Astar i‖ ≤ D) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤
      (p * m ^ ((a - 1) / p - 1) * D) *
        (1 + ∑ i ∈ Finset.range N, (n i - n (i + 1)) / n (i + 1)) := by
  have hnp (i : ℕ) (hi : i ≤ N) : 0 < n i := hm.trans_le (hn i hi)
  have hexponent : (a - 1) / p - 1 ≤ 0 := by
    have hp0 : 0 < p := by linarith
    have hdiv : (a - 1) / p ≤ 1 := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  have hweight (i : ℕ) (hi : i ≤ N) :
      p * n i ^ ((a - 1) / p - 1) * D ≤ p * m ^ ((a - 1) / p - 1) * D := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hm (hn i hi) hexponent) (by linarith)) hD
  have h := unary_vertex_telescope N n A Astar beta hp hap hnp hmass
    hcontraction hend hbeta hprediction herror
  apply h.trans
  calc
    _ ≤ (p * m ^ ((a - 1) / p - 1) * D) +
        ∑ i ∈ Finset.range N, ((n i - n (i + 1)) / n (i + 1)) *
          (p * m ^ ((a - 1) / p - 1) * D) := by
      apply add_le_add (hweight 0 (Nat.zero_le _))
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      exact mul_le_mul_of_nonneg_left (hweight (i + 1) (by omega))
        (div_nonneg (sub_nonneg.mpr (hmass i hiN)) (hnp (i + 1) (by omega)).le)
    _ = _ := by rw [← Finset.sum_mul]; ring

end Vertex

/-- The mass drop over a segment telescopes even if the segment contains
arbitrarily many very small unary drops. -/
theorem segment_relative_drop_sum_le (N : ℕ) (n : ℕ → ℝ) {m : ℝ} (hm : 0 < m)
    (hn : ∀ i ≤ N, m ≤ n i) (hmass : ∀ i < N, n (i + 1) ≤ n i) :
    (∑ i ∈ Finset.range N, (n i - n (i + 1)) / n (i + 1)) ≤ (n 0 - n N) / m := by
  calc
    _ ≤ ∑ i ∈ Finset.range N, (n i - n (i + 1)) / m := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr (hmass i hiN)) hm (hn (i + 1) (by omega))
    _ = (∑ i ∈ Finset.range N, (n i - n (i + 1))) / m := (Finset.sum_div ..).symm
    _ = _ := by
      have h := sum_range_shift_difference n N 1
      simp only [Finset.sum_range_one, zero_add] at h
      rw [h]

theorem half_mass_rpow_le {x e : ℝ} (hx : 0 < x) (he : -1 ≤ e) :
    (x / 2) ^ e ≤ 2 * x ^ e := by
  have htwo : (2 : ℝ) ^ (-e) ≤ 2 := by
    calc
      (2 : ℝ) ^ (-e) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one _
  calc
    (x / 2) ^ e = x ^ e * (2 : ℝ) ^ (-e) := by
      rw [Real.div_rpow hx.le (by norm_num), div_eq_mul_inv, Real.rpow_neg (by norm_num)]
    _ ≤ x ^ e * 2 := mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hx.le _)
    _ = 2 * x ^ e := mul_comm _ _

/-- The final `src-28` estimate, with an explicit absolute constant, on
a segment whose total mass drop is at most two. -/
theorem unary_vertex_telescope_short_segment {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (n : ℕ → ℝ) (A Astar : ℕ → E) (beta : ℕ → ℝ)
    {a p D : ℝ} (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p) (hD : 0 ≤ D)
    (hstart : 4 ≤ n 0) (hn : ∀ i ≤ N, n 0 - 2 ≤ n i)
    (hmass : ∀ i < N, n (i + 1) ≤ n i)
    (hcontraction : ∀ i < N, ‖Astar i‖ ≤ ‖Astar (i + 1)‖)
    (hend : Astar N = A N) (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ vertexAmount (n i) (A i) a p /
      (n i - n (i + 1) + vertexAmount (n (i + 1)) (A (i + 1)) a p))
    (herror : ∀ i ≤ N, ‖A i - Astar i‖ ≤ D) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤
      4 * p * n 0 ^ ((a - 1) / p - 1) * D := by
  have hp0 : 0 < p := by linarith
  have hn0 : 0 < n 0 := by linarith
  have hm : 0 < n 0 / 2 := by positivity
  have hnm (i : ℕ) (hi : i ≤ N) : n 0 / 2 ≤ n i := by
    linarith [hn i hi]
  have hrel := segment_relative_drop_sum_le N n hm hnm hmass
  have hrel1 : (∑ i ∈ Finset.range N, (n i - n (i + 1)) / n (i + 1)) ≤ 1 := by
    apply hrel.trans
    exact (div_le_one hm).mpr (by linarith [hn N le_rfl])
  have he : -1 ≤ (a - 1) / p - 1 := by
    have h := div_nonneg (sub_nonneg.mpr ha) hp0.le
    linarith
  have hhalf := half_mass_rpow_le hn0 he
  have hweight := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf hp0.le) hD
  have hC : p * (n 0 / 2) ^ ((a - 1) / p - 1) * D ≤
      2 * (p * n 0 ^ ((a - 1) / p - 1) * D) := by nlinarith
  have hC0 : 0 ≤ p * (n 0 / 2) ^ ((a - 1) / p - 1) * D := by positivity
  calc
    _ ≤ (p * (n 0 / 2) ^ ((a - 1) / p - 1) * D) *
        (1 + ∑ i ∈ Finset.range N, (n i - n (i + 1)) / n (i + 1)) :=
      unary_vertex_telescope_uniform N n A Astar beta hp hap hm hD hnm hmass
        hcontraction hend hbeta hprediction herror
    _ ≤ (p * (n 0 / 2) ^ ((a - 1) / p - 1) * D) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    _ ≤ _ := by nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_UnaryPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact propagation along unary segments

Finite iteration of §10 `res:unary-decomposition`. The residual coefficient
is the actual product of preceding path coefficients. Discarded-top
errors are summed against mass drops rather than the number of tops or
levels, as required in `res:segment-perturbation`.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem unaryPropagator_succ_right (coeff : ℕ → ℂ) {start finish : ℕ}
    (h : start ≤ finish) :
    unaryPropagator coeff start (finish + 1) = unaryPropagator coeff start finish * coeff finish :=
  Finset.prod_Ico_succ_top h coeff

theorem unaryPropagator_succ_left (coeff : ℕ → ℂ) {start finish : ℕ}
    (h : start < finish) :
    unaryPropagator coeff start finish = coeff start * unaryPropagator coeff (start + 1) finish :=
  Finset.prod_eq_prod_Ico_succ_bot h coeff

theorem unaryPropagator_norm_le_one (coeff : ℕ → ℂ) (start finish : ℕ)
    (hcoeff : ∀ j ∈ Finset.Ico start finish, ‖coeff j‖ ≤ 1) :
    ‖unaryPropagator coeff start finish‖ ≤ 1 := by
  rw [unaryPropagator, norm_prod]
  exact Finset.prod_le_one (fun j _ => norm_nonneg _) hcoeff

section Vector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
private theorem sum_Ico_forward_difference (f : ℕ → E) {start finish : ℕ}
    (h : start ≤ finish) :
    (∑ i ∈ Finset.Ico start finish, (f i - f (i + 1))) = f start - f finish := by
  induction finish, h using Nat.le_induction with
  | base => simp
  | succ finish h ih =>
    rw [Finset.sum_Ico_succ_top h, ih]
    abel

/-- Iteration retains the exact common product on every residual term. -/
theorem unary_iteration (coeff : ℕ → ℂ) (A U W : ℕ → E) {start finish : ℕ}
    (h : start ≤ finish)
    (hstep : ∀ i ∈ Finset.Ico start finish, A i = coeff i • A (i + 1) + U i + W i) :
    A start - unaryPropagator coeff start finish • A finish =
      (∑ i ∈ Finset.Ico start finish, unaryPropagator coeff start i • U i) +
      ∑ i ∈ Finset.Ico start finish, unaryPropagator coeff start i • W i := by
  have hterm (i : ℕ) (hi : i ∈ Finset.Ico start finish) :
      unaryPropagator coeff start i • U i + unaryPropagator coeff start i • W i =
        unaryPropagator coeff start i • A i -
          unaryPropagator coeff start (i + 1) • A (i + 1) := by
    rw [unaryPropagator_succ_right coeff (Finset.mem_Ico.mp hi).1,
      mul_smul, hstep i hi, smul_add, smul_add]
    abel
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl hterm]
  rw [sum_Ico_forward_difference (fun i => unaryPropagator coeff start i • A i) h]
  simp

theorem propagated_endpoint_contraction (coeff : ℕ → ℂ) (A : E) {i finish : ℕ}
    (hi : i < finish) (hcoeff : ‖coeff i‖ ≤ 1) :
    ‖unaryPropagator coeff i finish • A‖ ≤
      ‖unaryPropagator coeff (i + 1) finish • A‖ := by
  rw [unaryPropagator_succ_left coeff hi, mul_smul, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hcoeff

/-- Whole discarded-top errors cost only the total mass drop. -/
theorem discarded_unary_error_sum (coeff : ℕ → ℂ) (W : ℕ → E) (n : ℕ → ℝ)
    {start finish : ℕ} {ε : ℝ} (h : start ≤ finish)
    (hcoeff : ∀ j ∈ Finset.Ico start finish, ‖coeff j‖ ≤ 1)
    (hW : ∀ j ∈ Finset.Ico start finish, ‖W j‖ ≤ ε * (n j - n (j + 1))) :
    ‖∑ i ∈ Finset.Ico start finish, unaryPropagator coeff start i • W i‖ ≤
      ε * (n start - n finish) := by
  calc
    _ ≤ ∑ i ∈ Finset.Ico start finish, ‖unaryPropagator coeff start i • W i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.Ico start finish, ε * (n i - n (i + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      have hp := unaryPropagator_norm_le_one coeff start i (by
        intro j hj
        apply hcoeff j
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
          (Finset.mem_Ico.mp hj).2.trans (Finset.mem_Ico.mp hi).2⟩)
      exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans (hW i hi)
    _ = ε * (n start - n finish) := by
      rw [← Finset.mul_sum, sum_Ico_forward_difference n h]

/-- The propagated main residual sum and discarded-top error give the
amplitude perturbation used by the unary energy telescope. -/
theorem unary_perturbation_bound (coeff : ℕ → ℂ) (A U W : ℕ → E) (n : ℕ → ℝ)
    {start finish : ℕ} {ε D : ℝ} (h : start ≤ finish)
    (hcoeff : ∀ j ∈ Finset.Ico start finish, ‖coeff j‖ ≤ 1)
    (hstep : ∀ i ∈ Finset.Ico start finish, A i = coeff i • A (i + 1) + U i + W i)
    (hU : ‖∑ i ∈ Finset.Ico start finish, unaryPropagator coeff start i • U i‖ ≤ D)
    (hW : ∀ j ∈ Finset.Ico start finish, ‖W j‖ ≤ ε * (n j - n (j + 1))) :
    ‖A start - unaryPropagator coeff start finish • A finish‖ ≤
      D + ε * (n start - n finish) := by
  rw [unary_iteration coeff A U W h hstep]
  exact (norm_add_le _ _).trans (add_le_add hU
    (discarded_unary_error_sum coeff W n h hcoeff hW))

end Vector

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite path-product argument in §10. Marked indices retain the
residual-free predictor; all consecutive unary runs use one common cubic
variation estimate. The remaining unmarked large-drop index is unique.
The estimates are independent of the number of angular levels. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace UnaryRunPartition

theorem indices_disjoint {unary : ℕ → Prop} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish) :
    Set.PairwiseDisjoint (R.runs : Set (ℕ × ℕ)) (fun r => Finset.Ico r.1 r.2) := by
  intro r hr s hs hrs
  apply Finset.disjoint_left.mpr
  intro j hjr hjs
  have hjr' := Finset.mem_Ico.mp hjr
  have hjs' := Finset.mem_Ico.mp hjs
  rcases R.ordered r hr s hs hrs with h | h <;> omega

theorem indices_union {unary : ℕ → Prop} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish) :
    R.runs.biUnion (fun r => Finset.Ico r.1 r.2) =
      (Finset.Ico start finish).filter unary := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨r,hr,hjr⟩ := Finset.mem_biUnion.mp hj
    have hb := R.bounds r hr
    have hi := Finset.mem_Ico.mp hjr
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨hb.1.trans hi.1,hi.2.trans_le hb.2.2⟩,R.inside r hr j hi.1 hi.2⟩
  · intro hj
    obtain ⟨hi,hu⟩ := Finset.mem_filter.mp hj
    obtain ⟨r,hr,hlo,hhi⟩ := R.cover j (Finset.mem_Ico.mp hi).1
      (Finset.mem_Ico.mp hi).2 hu
    exact Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_Ico.mpr ⟨hlo,hhi⟩⟩

theorem sum_runs {unary : ℕ → Prop} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish) {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) :
    (∑ r ∈ R.runs, ∑ j ∈ Finset.Ico r.1 r.2, f j) =
      ∑ j ∈ (Finset.Ico start finish).filter unary, f j := by
  classical
  rw [← Finset.sum_biUnion R.indices_disjoint,R.indices_union]

theorem sum_segments {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    {E : Type*} [AddCommMonoid E] (f : ℕ → E) :
    (∑ i : UnaryRunSegment R P, ∑ j ∈ Finset.Ico i.2.val.1 i.2.val.2, f j) =
      ∑ j ∈ (Finset.Ico start finish).filter unary, f j := by
  classical
  rw [Fintype.sum_sigma]
  have h (r : R.runs) :
      (∑ b : (P r).blocks, ∑ j ∈ Finset.Ico b.val.1 b.val.2, f j) =
        ∑ j ∈ Finset.Ico r.val.1 r.val.2, f j := by
    rw [← Finset.sum_subtype (P r).blocks (p := fun b => b ∈ (P r).blocks)
      (by simp) (fun b : ℕ × ℕ => ∑ j ∈ Finset.Ico b.1 b.2, f j)]
    exact (P r).sum_blocks f
  simp_rw [h]
  rw [← Finset.sum_subtype R.runs (p := fun r => r ∈ R.runs)
    (by simp) (fun r : ℕ × ℕ => ∑ j ∈ Finset.Ico r.1 r.2, f j)]
  exact R.sum_runs f

end UnaryRunPartition

/-- The discarded-top contributions sum against true relative drops,
also when the unary indices have many separate consecutive runs. -/
theorem source_unary_runs_weighted_drop {unary : ℕ → Prop} {n : ℕ → ℝ}
    {start finish : ℕ} (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    (hn : Antitone n) {μ Q : ℝ} (hμ : μ ≤ 1)
    (hnpos : ∀ j ∈ Finset.Ico start finish, 0 < n j)
    (hQ : ∀ j ∈ Finset.Ico start finish, n j^μ ≤ Q) :
    (∑ i : UnaryRunSegment R P,
      n i.2.val.1^(μ-1)*(n i.2.val.1-n i.2.val.2)) ≤
        Q*∑ j ∈ (Finset.Ico start finish).filter unary, pathDrop n j := by
  have hstep (i : UnaryRunSegment R P) :
      n i.2.val.1^(μ-1)*(n i.2.val.1-n i.2.val.2) ≤
        ∑ j ∈ Finset.Ico i.2.val.1 i.2.val.2, Q*pathDrop n j := by
    have hb := (P i.1).bounds i.2.val i.2.property
    have hr := R.bounds i.1.val i.1.property
    rw [← sum_Ico_mass_drop n hb.2.1.le,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjb := Finset.mem_Ico.mp hj
    have hjf : j ∈ Finset.Ico start finish := Finset.mem_Ico.mpr
      ⟨hr.1.trans (hb.1.trans hjb.1),hjb.2.trans_le (hb.2.2.trans hr.2.2)⟩
    have hjpos := hnpos j hjf
    have hdrop := sub_nonneg.mpr (hn (Nat.le_succ j))
    calc
      _ ≤ n j^(μ-1)*(n j-n (j+1)) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hjpos (hn hjb.1) (by linarith)) hdrop
      _ = n j^μ*pathDrop n j := by rw [Real.rpow_sub_one hjpos.ne',pathDrop]; ring
      _ ≤ Q*pathDrop n j := mul_le_mul_of_nonneg_right (hQ j hjf)
        (pathDrop_nonnegative n j hjpos (hn (Nat.le_succ j)))
  calc
    _ ≤ ∑ i : UnaryRunSegment R P,
        ∑ j ∈ Finset.Ico i.2.val.1 i.2.val.2, Q*pathDrop n j := Finset.sum_le_sum
      (fun i _ => hstep i)
    _ = _ := by rw [R.sum_segments P,Finset.mul_sum]

/-- Reindex the actual unary energy telescope to an arbitrary segment.
The propagated comparison amplitude is required only on that segment. -/
theorem source_unary_segment_log_cost {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ → ℝ) (A Astar : ℕ → E) (beta : ℕ → ℝ)
    {e f : ℕ} {a p D : ℝ} (hef : e ≤ f)
    (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p) (hD : 0 ≤ D)
    (hstart : 4 ≤ n e) (hn : Antitone n) (hdrop : n e-n f ≤ 2)
    (hcontraction : ∀ j ∈ Finset.Ico e f, ‖Astar j‖ ≤ ‖Astar (j+1)‖)
    (hend : Astar f = A f) (hbeta : ∀ j ∈ Finset.Ico e f, 0 < beta j)
    (hprediction : ∀ j ∈ Finset.Ico e f, beta j ≤
      vertexAmount (n j) (A j) a p /
        (n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) a p))
    (herror : ∀ j ∈ Finset.Icc e f, ‖A j-Astar j‖ ≤ D) :
    (∑ j ∈ Finset.Ico e f, Real.log (beta j)) ≤ 4*p*n e^((a-1)/p-1)*D := by
  have h := unary_vertex_telescope_short_segment (f-e)
    (fun j => n (e+j)) (fun j => A (e+j)) (fun j => Astar (e+j))
    (fun j => beta (e+j)) hp ha hap hD (by simpa using hstart) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [Finset.sum_Ico_eq_sum_range,Nat.add_zero] using h
  · intro j hj
    have hmono := hn (show e+j ≤ f by omega)
    simpa only [Nat.add_zero] using (show n e-2 ≤ n (e+j) by linarith)
  · intro j _
    exact hn (by omega)
  · intro j hj
    simpa only [Nat.add_assoc] using hcontraction (e+j) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
  · simpa only [Nat.add_sub_of_le hef] using hend
  · intro j hj
    exact hbeta (e+j) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
  · intro j hj
    simpa only [Nat.add_assoc] using hprediction (e+j) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩)
  · intro j hj
    exact herror (e+j) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)

/-- All unary runs use one cubic-variation budget. The local error bound
is the actual propagated amplitude error from Abel summation, not a
hypothesis about the path product. -/
theorem source_unary_runs_log_cost {unary : ℕ → Prop} {n : ℕ → ℝ}
    {start finish : ℕ} (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    (A : ℕ → E) (Astar : ℕ → ℕ → ℕ → E) (beta : ℕ → ℝ)
    (profile : ℕ → F) (level : ℕ → ℕ) (hlevel : StrictMono level) (N : ℕ)
    (hendlevel : level finish ≤ N) (hn : Antitone n)
    {a p c M V C ε Q : ℝ} (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p)
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 4 ≤ M) (hμ : (a-1)/p ≤ 1/12)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hmass : ∀ j ∈ (Finset.Ico start finish).filter unary, M ≤ n j)
    (hnpos : ∀ j ∈ Finset.Ico start finish, 0 < n j)
    (hQ : ∀ j ∈ Finset.Ico start finish, n j^((a-1)/p) ≤ Q)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬unary j → c ≤ n j-n (j+1))
    (hvariation : finiteCubicVariation (fun k => profile (min k N)) (2*N) ≤ V^3)
    (hbeta : ∀ j ∈ (Finset.Ico start finish).filter unary, 0 < beta j)
    (hprediction : ∀ j ∈ (Finset.Ico start finish).filter unary, beta j ≤
      vertexAmount (n j) (A j) a p /
        (n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) a p))
    (hcontraction : ∀ i : UnaryRunSegment R P,
      ∀ j ∈ Finset.Ico i.2.val.1 i.2.val.2,
        ‖Astar i.2.val.1 i.2.val.2 j‖ ≤ ‖Astar i.2.val.1 i.2.val.2 (j+1)‖)
    (hend : ∀ i : UnaryRunSegment R P,
      Astar i.2.val.1 i.2.val.2 i.2.val.2 = A i.2.val.2)
    (herror : ∀ i : UnaryRunSegment R P, ∀ j ∈ Finset.Icc i.2.val.1 i.2.val.2,
      ‖A j-Astar i.2.val.1 i.2.val.2 j‖ ≤
        C*intervalOscillation profile N (level i.2.val.1) (level i.2.val.2)+
          ε*(n i.2.val.1-n i.2.val.2)) :
    (∑ j ∈ (Finset.Ico start finish).filter unary, Real.log (beta j)) ≤
      4*p*C*((2*(2+17/c))^(2/3:ℝ)*M^(-(1/3:ℝ)+(a-1)/p)*V)+
        4*p*ε*(Q*∑ j ∈ (Finset.Ico start finish).filter unary, pathDrop n j) := by
  have hmember (i : UnaryRunSegment R P) {j : ℕ}
      (hj : j ∈ Finset.Ico i.2.val.1 i.2.val.2) :
      j ∈ (Finset.Ico start finish).filter unary := by
    have hb := (P i.1).bounds i.2.val i.2.property
    have hr := R.bounds i.1.val i.1.property
    have hi := Finset.mem_Ico.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨hr.1.trans (hb.1.trans hi.1),hi.2.trans_le (hb.2.2.trans hr.2.2)⟩,
      R.inside i.1.val i.1.property j (hb.1.trans hi.1) (hi.2.trans_le hb.2.2)⟩
  have hstart (i : UnaryRunSegment R P) : M ≤ n i.2.val.1 :=
    hmass _ (hmember i (Finset.mem_Ico.mpr ⟨le_rfl,(P i.1).bounds _ i.2.property |>.2.1⟩))
  have hres := unary_runs_residual_sum R P hn hc hc1 (by linarith : 1 ≤ M) hμ hV
    hstart hinterruption profile level hlevel N hendlevel hvariation
  have hdrop := source_unary_runs_weighted_drop R P hn (by linarith : (a-1)/p ≤ 1) hnpos hQ
  have hseg (i : UnaryRunSegment R P) :
      (∑ j ∈ Finset.Ico i.2.val.1 i.2.val.2, Real.log (beta j)) ≤
      4*p*n i.2.val.1^((a-1)/p-1)*
        (C*intervalOscillation profile N (level i.2.val.1) (level i.2.val.2)+
          ε*(n i.2.val.1-n i.2.val.2)) := by
    have hb := (P i.1).bounds i.2.val i.2.property
    apply source_unary_segment_log_cost n A (Astar i.2.val.1 i.2.val.2) beta
      hb.2.1.le hp ha hap ?_ (hM.trans (hstart i)) hn
      ((P i.1).drop_lt_two _ i.2.property).le (hcontraction i) (hend i)
      (fun j hj => hbeta j (hmember i hj)) (fun j hj => hprediction j (hmember i hj)) (herror i)
    exact add_nonneg (mul_nonneg hC (intervalOscillation_nonneg ..))
      (mul_nonneg hε (sub_nonneg.mpr (hn hb.2.1.le)))
  calc
    _ = ∑ i : UnaryRunSegment R P,
        ∑ j ∈ Finset.Ico i.2.val.1 i.2.val.2, Real.log (beta j) := (R.sum_segments P _).symm
    _ ≤ ∑ i : UnaryRunSegment R P, 4*p*n i.2.val.1^((a-1)/p-1)*
        (C*intervalOscillation profile N (level i.2.val.1) (level i.2.val.2)+
          ε*(n i.2.val.1-n i.2.val.2)) := Finset.sum_le_sum (fun i _ => hseg i)
    _ = 4*p*C*(∑ i : UnaryRunSegment R P, n i.2.val.1^(-1+(a-1)/p)*
          intervalOscillation profile N (level i.2.val.1) (level i.2.val.2))+
        4*p*ε*(∑ i : UnaryRunSegment R P, n i.2.val.1^((a-1)/p-1)*
          (n i.2.val.1-n i.2.val.2)) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [show -1+(a-1)/p = (a-1)/p-1 by ring]
      ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hres (by positivity))
      (mul_le_mul_of_nonneg_left hdrop (by positivity))

/-- The comparison amplitudes used above can be the literal products of
the path coefficients and the endpoint amplitude. This discharges their
contraction and endpoint conditions from the true unary recurrence. -/
theorem source_unary_propagated_log_cost {unary : ℕ → Prop} {n : ℕ → ℝ}
    {start finish : ℕ} (R : UnaryRunPartition unary start finish)
    (P : ∀ r : R.runs, UnarySegmentPartition n r.val.1 r.val.2)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] (A U W : ℕ → E) (coeff : ℕ → ℂ) (beta : ℕ → ℝ)
    (profile : ℕ → F) (level : ℕ → ℕ) (hlevel : StrictMono level) (N : ℕ)
    (hendlevel : level finish ≤ N) (hn : Antitone n)
    {a p c M V C ε Q : ℝ} (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p)
    (hc : 0 < c) (hc1 : c ≤ 1) (hM : 4 ≤ M) (hμ : (a-1)/p ≤ 1/12)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hmass : ∀ j ∈ (Finset.Ico start finish).filter unary, M ≤ n j)
    (hnpos : ∀ j ∈ Finset.Ico start finish, 0 < n j)
    (hQ : ∀ j ∈ Finset.Ico start finish, n j^((a-1)/p) ≤ Q)
    (hinterruption : ∀ j, start ≤ j → j < finish → ¬unary j → c ≤ n j-n (j+1))
    (hvariation : finiteCubicVariation (fun k => profile (min k N)) (2*N) ≤ V^3)
    (hbeta : ∀ j ∈ (Finset.Ico start finish).filter unary, 0 < beta j)
    (hprediction : ∀ j ∈ (Finset.Ico start finish).filter unary, beta j ≤
      vertexAmount (n j) (A j) a p /
        (n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) a p))
    (hcoeff : ∀ j ∈ (Finset.Ico start finish).filter unary, ‖coeff j‖ ≤ 1)
    (hstep : ∀ j ∈ (Finset.Ico start finish).filter unary,
      A j = coeff j • A (j+1)+U j+W j)
    (hW : ∀ j ∈ (Finset.Ico start finish).filter unary, ‖W j‖ ≤ ε*(n j-n (j+1)))
    (hU : ∀ i : UnaryRunSegment R P, ∀ j ∈ Finset.Icc i.2.val.1 i.2.val.2,
      ‖∑ k ∈ Finset.Ico j i.2.val.2, unaryPropagator coeff j k • U k‖ ≤
        C*intervalOscillation profile N (level i.2.val.1) (level i.2.val.2)) :
    (∑ j ∈ (Finset.Ico start finish).filter unary, Real.log (beta j)) ≤
      4*p*C*((2*(2+17/c))^(2/3:ℝ)*M^(-(1/3:ℝ)+(a-1)/p)*V)+
        4*p*ε*(Q*∑ j ∈ (Finset.Ico start finish).filter unary, pathDrop n j) := by
  have hmember (i : UnaryRunSegment R P) {j : ℕ}
      (hj : j ∈ Finset.Ico i.2.val.1 i.2.val.2) :
      j ∈ (Finset.Ico start finish).filter unary := by
    have hb := (P i.1).bounds i.2.val i.2.property
    have hr := R.bounds i.1.val i.1.property
    have hi := Finset.mem_Ico.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨hr.1.trans (hb.1.trans hi.1),hi.2.trans_le (hb.2.2.trans hr.2.2)⟩,
      R.inside i.1.val i.1.property j (hb.1.trans hi.1) (hi.2.trans_le hb.2.2)⟩
  apply source_unary_runs_log_cost R P A
    (fun _ f j => unaryPropagator coeff j f • A f) beta profile level hlevel N
    hendlevel hn hp ha hap hc hc1 hM hμ hV hC hε hmass hnpos hQ
    hinterruption hvariation hbeta hprediction
  · intro i j hj
    exact propagated_endpoint_contraction coeff (A i.2.val.2)
      (Finset.mem_Ico.mp hj).2 (hcoeff j (hmember i hj))
  · intro i
    simp
  · intro i j hj
    have hjb := Finset.mem_Icc.mp hj
    have htail (k : ℕ) (hk : k ∈ Finset.Ico j i.2.val.2) :
        k ∈ (Finset.Ico start finish).filter unary :=
      hmember i (Finset.mem_Ico.mpr
        ⟨hjb.1.trans (Finset.mem_Ico.mp hk).1,(Finset.mem_Ico.mp hk).2⟩)
    have he := unary_perturbation_bound coeff A U W n hjb.2
      (fun k hk => hcoeff k (htail k hk)) (fun k hk => hstep k (htail k hk))
      (hU i j hj) (fun k hk => hW k (htail k hk))
    exact he.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (hn hjb.1) _) hε))

/-- The exceptional factor is controlled just by its amplitude and the
baseline mass in its denominator. -/
theorem source_exceptional_factor_le {E : Type*} [NormedAddCommGroup E]
    (A : E) {n denominator M C a p : ℝ}
    (hn : 0 < n) (hden : n ≤ denominator) (hM : n ≤ M+1)
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hp : 0 ≤ p) (hA : ‖A‖ ≤ C*n) :
    vertexAmount n A a p/denominator ≤ 1+C^p*(M+1)^(a-1) := by
  have henergy : n^(a-p)*‖A‖^p ≤ C^p*n^a := by
    calc
      _ ≤ n^(a-p)*(C*n)^p := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hA hp) (Real.rpow_nonneg hn.le _)
      _ = C^p*n^a := by
        rw [Real.mul_rpow hC hn.le]
        calc
          n^(a-p)*(C^p*n^p) = C^p*(n^(a-p)*n^p) := by ring
          _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring
  have hbase : vertexAmount n A a p/denominator ≤ vertexAmount n A a p/n :=
    div_le_div_of_nonneg_left (vertexAmount_pos (a := a) (p := p) hn A).le hn hden
  apply hbase.trans
  calc
    _ ≤ (n+C^p*n^a)/n := div_le_div_of_nonneg_right (by
      unfold vertexAmount
      linarith) hn.le
    _ = 1+C^p*n^(a-1) := by
      rw [add_div,div_self hn.ne',mul_div_assoc,← Real.rpow_sub_one hn.ne']
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hn.le hM (show 0 ≤ a-1 by linarith)) (Real.rpow_nonneg hC _))

/-- Split a finite active product into marked, unary and exceptional
indices. The exceptional contribution costs once, even if its logarithm
is negative. -/
theorem source_path_product_of_log_costs (count : ℕ) (marked unary exceptional : ℕ → Prop)
    (beta beta0 : ℕ → ℝ) (markedCost unaryCost exceptionalCost : ℝ)
    (hbeta : ∀ j < count, 0 < beta j) (hbeta0 : ∀ j < count, marked j → 0 < beta0 j)
    (hpartition : ∀ j < count,
      (marked j ∨ unary j ∨ exceptional j) ∧
        ¬(marked j ∧ unary j) ∧ ¬(marked j ∧ exceptional j) ∧ ¬(unary j ∧ exceptional j))
    (hmarked : (∑ j ∈ (Finset.range count).filter marked,
      (Real.log (beta j)-Real.log (beta0 j))) ≤ markedCost)
    (hunary : (∑ j ∈ (Finset.range count).filter unary, Real.log (beta j)) ≤ unaryCost)
    (hexceptional : Set.Subsingleton {j | j < count ∧ exceptional j})
    (hcost : 0 ≤ exceptionalCost)
    (hexbound : ∀ j < count, exceptional j → Real.log (beta j) ≤ exceptionalCost) :
    (∏ j ∈ Finset.range count, beta j) ≤
      Real.exp (markedCost+unaryCost+exceptionalCost)*
        ∏ j ∈ Finset.range count, if marked j then beta0 j else 1 := by
  classical
  have hexsum : (∑ j ∈ (Finset.range count).filter exceptional, Real.log (beta j)) ≤
      exceptionalCost := by
    let S := (Finset.range count).filter exceptional
    have hsub : (S : Set ℕ).Subsingleton := by
      intro i hi j hj
      exact hexceptional ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1,
        (Finset.mem_filter.mp hi).2⟩ ⟨Finset.mem_range.mp (Finset.mem_filter.mp hj).1,
        (Finset.mem_filter.mp hj).2⟩
    by_cases hempty : S = ∅
    · simpa only [S,hempty,Finset.sum_empty] using hcost
    · obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hS : S = {j} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hj,fun i hi => hsub hi hj⟩
      change (∑ j ∈ S, Real.log (beta j)) ≤ exceptionalCost
      rw [hS,Finset.sum_singleton]
      exact hexbound j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
        (Finset.mem_filter.mp hj).2
  have hsplit :
      (∑ j ∈ Finset.range count, (Real.log (beta j)-
        Real.log (if marked j then beta0 j else 1))) =
      (∑ j ∈ (Finset.range count).filter marked, (Real.log (beta j)-Real.log (beta0 j)))+
      (∑ j ∈ (Finset.range count).filter unary, Real.log (beta j))+
      (∑ j ∈ (Finset.range count).filter exceptional, Real.log (beta j)) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hcover,hmU,hmE,huE⟩ := hpartition j (Finset.mem_range.mp hj)
    rcases hcover with hm | hu | he
    · have hnu : ¬unary j := fun h => hmU ⟨hm,h⟩
      have hne : ¬exceptional j := fun h => hmE ⟨hm,h⟩
      simp [hm,hnu,hne]
    · have hnm : ¬marked j := fun h => hmU ⟨h,hu⟩
      have hne : ¬exceptional j := fun h => huE ⟨hu,h⟩
      simp [hu,hnm,hne]
    · have hnm : ¬marked j := fun h => hmE ⟨h,he⟩
      have hnu : ¬unary j := fun h => huE ⟨h,he⟩
      simp [he,hnm,hnu]
  have hmodel (j : ℕ) (hj : j < count) : 0 < if marked j then beta0 j else 1 := by
    split_ifs with hm
    · exact hbeta0 j hj hm
    · norm_num
  have hlog : Real.log (∏ j ∈ Finset.range count, beta j)-
      Real.log (∏ j ∈ Finset.range count, if marked j then beta0 j else 1) ≤
        markedCost+unaryCost+exceptionalCost := by
    rw [Real.log_prod (fun j hj => (hbeta j (Finset.mem_range.mp hj)).ne'),
      Real.log_prod (fun j hj => (hmodel j (Finset.mem_range.mp hj)).ne'),← Finset.sum_sub_distrib,
      hsplit]
    linarith
  have hmodelp := Finset.prod_pos (s := Finset.range count)
    (fun j hj => hmodel j (Finset.mem_range.mp hj))
  have hactualp := Finset.prod_pos (s := Finset.range count)
    (fun j hj => hbeta j (Finset.mem_range.mp hj))
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub,Real.exp_log hactualp,Real.exp_log hmodelp] at he
  exact (div_le_iff₀ hmodelp).mp he

/-- The exact marked correction for the parent amplitude and its literal
residual-free value. The square sum is over the marked blocks only. -/
theorem source_marked_log_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ → ℝ) (hn : Antitone n) (S : Finset ℕ)
    (A residual : ℕ → E) (denominator : ℕ → ℝ)
    {a p c M B : ℝ} (hp : 1 ≤ p) (hc : 0 < c) (hM : 1 ≤ M)
    (hμ : (a-1)/p ≤ 1/12) (hB : 0 ≤ B)
    (hdrop : ∀ j ∈ S, c ≤ n j-n (j+1))
    (hmass : ∀ j ∈ S, M ≤ n j) (hden : ∀ j ∈ S, 0 < denominator j)
    (hsquare : (∑ j ∈ S, ‖residual j‖^2) ≤ B^2) :
    (∑ j ∈ S, (Real.log (vertexAmount (n j) (A j) a p/denominator j)-
      Real.log (vertexAmount (n j) (A j-residual j) a p/denominator j))) ≤
      p*Real.sqrt (2*(1+3/c))*M^(-(1/2:ℝ)+(a-1)/p)*B := by
  apply marked_log_cost n hn S A (fun j => A j-residual j) denominator
    hp hc hM hμ hB hdrop hmass hden
  simpa only [sub_sub_cancel] using hsquare

/-- Actual vertex ratios admit the finite source path bound. The unary
cost is supplied by `source_unary_runs_log_cost`; the marked cost and
unique exceptional factor are proved here from their local data. -/
theorem source_path_product_from_vertex_costs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (count : ℕ) (n : ℕ → ℝ) (A residual : ℕ → E) (denominator : ℕ → ℝ)
    (marked : ℕ → Prop) {a p c M B U C : ℝ}
    (hn : Antitone n) (hp : 1 ≤ p) (ha : 1 ≤ a) (hc : 0 < c)
    (hM : 1 ≤ M) (hμ : (a-1)/p ≤ 1/12) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hactive : ∀ j < count, M < n j)
    (hden : ∀ j < count, n j ≤ denominator j)
    (hdrop : ∀ j < count, marked j → c ≤ n j-n (j+1))
    (hsquare : (∑ j ∈ (Finset.range count).filter marked, ‖residual j‖^2) ≤ B^2)
    (hunary : (∑ j ∈ (Finset.range count).filter
      (fun j => ¬marked j ∧ n j-n (j+1) < 1),
      Real.log (vertexAmount (n j) (A j) a p/denominator j)) ≤ U)
    (hexstop : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n (j+1) ≤ M)
    (hexmass : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n j ≤ M+1)
    (hexamp : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → ‖A j‖ ≤ C*n j) :
    (∏ j ∈ Finset.range count, vertexAmount (n j) (A j) a p/denominator j) ≤
      Real.exp (p*Real.sqrt (2*(1+3/c))*M^(-(1/2:ℝ)+(a-1)/p)*B+U+
        Real.log (1+C^p*(M+1)^(a-1)))*
      ∏ j ∈ Finset.range count,
        if marked j then vertexAmount (n j) (A j-residual j) a p/denominator j else 1 := by
  classical
  let unary := fun j => ¬marked j ∧ n j-n (j+1) < 1
  let exceptional := fun j => ¬marked j ∧ 1 ≤ n j-n (j+1)
  have hnp (j : ℕ) (hj : j < count) : 0 < n j := by linarith [hactive j hj]
  have hdp (j : ℕ) (hj : j < count) : 0 < denominator j :=
    (hnp j hj).trans_le (hden j hj)
  have hmark := source_marked_log_cost n hn ((Finset.range count).filter marked)
    A residual denominator hp hc hM hμ hB
    (fun j hj => hdrop j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
      (Finset.mem_filter.mp hj).2)
    (fun j hj => (hactive j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)).le)
    (fun j hj => hdp j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)) hsquare
  apply source_path_product_of_log_costs count marked unary exceptional
    (fun j => vertexAmount (n j) (A j) a p/denominator j)
    (fun j => vertexAmount (n j) (A j-residual j) a p/denominator j)
    (p*Real.sqrt (2*(1+3/c))*M^(-(1/2:ℝ)+(a-1)/p)*B) U
    (Real.log (1+C^p*(M+1)^(a-1)))
  · intro j hj
    exact div_pos (vertexAmount_pos (hnp j hj) _) (hdp j hj)
  · intro j hj _
    exact div_pos (vertexAmount_pos (hnp j hj) _) (hdp j hj)
  · intro j _
    dsimp only [unary,exceptional]
    by_cases hm : marked j
    · tauto
    · have hd : ¬(n j-n (j+1) < 1 ∧ 1 ≤ n j-n (j+1)) := by
        rintro ⟨h₁,h₂⟩
        exact (not_lt_of_ge h₂) h₁
      rcases lt_or_ge (n j-n (j+1)) 1 with h | h <;> tauto
  · exact hmark
  · simpa only [Finset.sum_filter,unary] using hunary
  · exact source_exceptional_index_unique n M hn
      (fun j => j < count ∧ exceptional j)
      (fun j hj => hactive j hj.1)
      (fun j hj => hexstop j hj.1 hj.2.1 hj.2.2)
  · apply Real.log_nonneg
    exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hC _)
      (Real.rpow_nonneg (by linarith : 0 ≤ M+1) _))
  · intro j hj hex
    apply Real.log_le_log (div_pos (vertexAmount_pos (hnp j hj) _) (hdp j hj))
    exact source_exceptional_factor_le (A j) (hnp j hj) (hden j hj)
      (hexmass j hj hex.1 hex.2) hC ha (by linarith) (hexamp j hj hex.1 hex.2)

/-- Assemble the full finite active path directly from residual square
sums, the common cubic variation, and the actual propagated recurrence.
The only interval hypothesis is the Abel bound on the propagated main
residuals. It is imposed on unary intervals of total drop below two,
exactly the intervals constructed in the proof. -/
theorem source_path_product_from_propagated_residuals
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [NormedAddCommGroup F]
    (count : ℕ) (n : ℕ → ℝ) (A U W residual : ℕ → E)
    (coeff : ℕ → ℂ) (denominator : ℕ → ℝ) (marked : ℕ → Prop)
    (profile : ℕ → F) (level : ℕ → ℕ) (hlevel : StrictMono level) (N : ℕ)
    (hendlevel : level count ≤ N) (hn : Antitone n)
    {a p c M B V C ε Q Cex : ℝ}
    (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p) (hc : 0 < c) (hc1 : c ≤ 1)
    (hM : 4 ≤ M) (hμ : (a-1)/p ≤ 1/12)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hCex : 0 ≤ Cex)
    (hactive : ∀ j < count, M < n j)
    (hden : ∀ j < count, n j ≤ denominator j)
    (hmarked : ∀ j < count, marked j → c ≤ n j-n (j+1))
    (hsquare : (∑ j ∈ (Finset.range count).filter marked, ‖residual j‖^2) ≤ B^2)
    (hQ : ∀ j < count, n j^((a-1)/p) ≤ Q)
    (hvariation : finiteCubicVariation (fun k => profile (min k N)) (2*N) ≤ V^3)
    (hpathden : ∀ j < count, ¬marked j → n j-n (j+1) < 1 →
      n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) a p ≤ denominator j)
    (hcoeff : ∀ j < count, ¬marked j → n j-n (j+1) < 1 → ‖coeff j‖ ≤ 1)
    (hstep : ∀ j < count, ¬marked j → n j-n (j+1) < 1 →
      A j = coeff j • A (j+1)+U j+W j)
    (hW : ∀ j < count, ¬marked j → n j-n (j+1) < 1 → ‖W j‖ ≤ ε*(n j-n (j+1)))
    (hU : ∀ e f, e < f → f ≤ count → n e-n f < 2 →
      (∀ k ∈ Finset.Ico e f, ¬marked k ∧ n k-n (k+1) < 1) →
      ∀ j ∈ Finset.Icc e f,
        ‖∑ k ∈ Finset.Ico j f, unaryPropagator coeff j k • U k‖ ≤
          C*intervalOscillation profile N (level e) (level f))
    (hexstop : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n (j+1) ≤ M)
    (hexmass : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n j ≤ M+1)
    (hexamp : ∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → ‖A j‖ ≤ Cex*n j) :
    (∏ j ∈ Finset.range count, vertexAmount (n j) (A j) a p/denominator j) ≤
      Real.exp (p*Real.sqrt (2*(1+3/c))*M^(-(1/2:ℝ)+(a-1)/p)*B+
        (4*p*C*((2*(2+17/c))^(2/3:ℝ)*M^(-(1/3:ℝ)+(a-1)/p)*V)+
          4*p*ε*(Q*∑ j ∈ (Finset.range count).filter
            (fun j => ¬marked j ∧ n j-n (j+1) < 1), pathDrop n j))+
        Real.log (1+Cex^p*(M+1)^(a-1)))*
      ∏ j ∈ Finset.range count,
        if marked j then vertexAmount (n j) (A j-residual j) a p/denominator j else 1 := by
  classical
  let unary := fun j => ¬marked j ∧ n j-n (j+1) < 1
  obtain ⟨R⟩ := exists_unary_run_partition unary 0 count (Nat.zero_le count)
  have hparts (r : R.runs) : Nonempty (UnarySegmentPartition n r.val.1 r.val.2) := by
    apply exists_unary_segment_partition n r.val.1 r.val.2
      (R.bounds r.val r.property).2.1.le
    intro j hje hjf
    exact (R.inside r.val r.property j hje hjf).2
  let P := fun r : R.runs => Classical.choice (hparts r)
  have hnp (j : ℕ) (hj : j < count) : 0 < n j := by linarith [hactive j hj]
  have hdp (j : ℕ) (hj : j < count) : 0 < denominator j := (hnp j hj).trans_le (hden j hj)
  have hmem (j : ℕ) (hj : j ∈ @Finset.filter ℕ unary
      (fun j => Classical.propDecidable (unary j)) (Finset.Ico 0 count)) :
      j < count ∧ ¬marked j ∧ n j-n (j+1) < 1 := by
    simpa only [Finset.mem_filter,Finset.mem_Ico,Nat.zero_le,true_and,unary] using hj
  have hlog := source_unary_propagated_log_cost R P A U W coeff
    (fun j => vertexAmount (n j) (A j) a p/denominator j)
    profile level hlevel N hendlevel hn hp ha hap hc hc1 hM hμ hV hC hε
    (fun j hj => (hactive j (hmem j hj).1).le)
    (fun j hj => hnp j (Finset.mem_Ico.mp hj).2)
    (fun j hj => hQ j (Finset.mem_Ico.mp hj).2) ?_ hvariation ?_ ?_
    (fun j hj => hcoeff j (hmem j hj).1 (hmem j hj).2.1 (hmem j hj).2.2)
    (fun j hj => hstep j (hmem j hj).1 (hmem j hj).2.1 (hmem j hj).2.2)
    (fun j hj => hW j (hmem j hj).1 (hmem j hj).2.1 (hmem j hj).2.2) ?_
  · apply source_path_product_from_vertex_costs count n A residual denominator marked
      hn hp ha hc (by linarith : 1 ≤ M) hμ hB hCex hactive hden hmarked hsquare
      ?_ hexstop hexmass hexamp
    simpa only [Nat.Ico_zero_eq_range,Finset.sum_filter,unary] using hlog
  · intro j _ hj hnot
    by_cases hm : marked j
    · exact hmarked j hj hm
    · have hg : 1 ≤ n j-n (j+1) := le_of_not_gt (fun h => hnot ⟨hm,h⟩)
      exact hc1.trans hg
  · intro j hj
    have hjc := (hmem j hj).1
    exact div_pos (vertexAmount_pos (hnp j hjc) _) (hdp j hjc)
  · intro j hj
    obtain ⟨hjc,hm,hs⟩ := hmem j hj
    have hnext : 0 < n (j+1) := by linarith [hactive j hjc]
    have hbase : 0 < n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) a p :=
      add_pos_of_nonneg_of_pos (sub_nonneg.mpr (hn (Nat.le_succ j))) (vertexAmount_pos hnext _)
    exact div_le_div_of_nonneg_left (vertexAmount_pos (hnp j hjc) _).le hbase
      (hpathden j hjc hm hs)
  · intro i j hj
    have hb := (P i.1).bounds i.2.val i.2.property
    have hr := R.bounds i.1.val i.1.property
    apply hU i.2.val.1 i.2.val.2 hb.2.1 (hb.2.2.trans hr.2.2)
      ((P i.1).drop_lt_two _ i.2.property) ?_ j hj
    intro k hk
    have hki := Finset.mem_Ico.mp hk
    exact R.inside i.1.val i.1.property k (hb.1.trans hki.1) (hki.2.trans_le hb.2.2)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualPropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact propagation of source residual packets. The same angular
transition product occurs at every shift. A packet continuing in the
path child therefore acquires a coefficient depending only on its stop
level; Abel summation applies to one fixed raw packet prefix. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

namespace AngularGrid
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem packetAmplitude_filter_split (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    (keep : σ → Prop) (level : ℕ) (cell : ℤ) :
    g.packetAmplitude packets slope stop base transition level cell =
      g.packetAmplitude (packets.filter keep) slope stop base transition level cell+
        g.packetAmplitude (packets.filter fun s => ¬keep s) slope stop base transition level cell := by
  simp only [packetAmplitude,packetSet,Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : keep q <;> simp [hq]

/-- The product of all complete block coefficients is the one common
angular transition product over their union. -/
theorem packetPathProduct_blocks (g : AngularGrid) (transition : ℕ → ℤ → ℂ)
    (level : ℕ → ℕ) (hlevel : Monotone level) (s : ℝ) {e f : ℕ} (hef : e ≤ f) :
    unaryPropagator (fun j => g.packetPathProduct transition (level j) (level (j+1)) s) e f =
      g.packetPathProduct transition (level e) (level f) s := by
  induction f, hef using Nat.le_induction with
  | base => simp [unaryPropagator,packetPathProduct]
  | succ f hef ih =>
    rw [unaryPropagator_succ_right _ hef,ih,
      ← g.packetPathProduct_split transition (hlevel hef) (hlevel (Nat.le_succ f))]

/-- A packet whose top lies in the path child has the same partial
transition coefficient as the path itself, through its stopping level. -/
theorem propagated_packet_coefficient (g : AngularGrid) (transition : ℕ → ℤ → ℂ)
    (level : ℕ → ℕ) (hlevel : Monotone level) (pathSlope packetSlope : ℝ)
    {e j stop : ℕ} (hej : e ≤ j) (hstop : level j ≤ stop) (hstop' : stop ≤ level (j+1))
    (hcell : g.index (level (j+1)) packetSlope = g.index (level (j+1)) pathSlope) :
    unaryPropagator (fun b => g.packetPathProduct transition (level b) (level (b+1)) pathSlope) e j *
      g.packetPathProduct transition (level j) stop packetSlope =
        g.packetPathProduct transition (level e) stop pathSlope := by
  rw [g.packetPathProduct_blocks transition level hlevel pathSlope hej,
    g.packetPathProduct_eq_of_cell transition (level j) stop (g.index_eq_of_le hstop' hcell),
    ← g.packetPathProduct_split transition (hlevel hej) hstop]

/-- Generic one-child recurrence. The complementary summand is the
entire amplitude of packets whose tops leave the distinguished child. -/
theorem packetAmplitude_one_child (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    (keep : σ → Prop) {lower upper : ℕ} (hlu : lower ≤ upper) (s : ℝ)
    (hkeep : ∀ q ∈ packets, keep q → g.index upper (slope q) = g.index upper s)
    (hlong : ∀ q ∈ packets, upper ≤ stop q →
      g.index upper (slope q) = g.index upper s → keep q) :
    g.packetAmplitude packets slope stop base transition lower (g.index lower s) =
      g.packetPathProduct transition lower upper s •
        g.packetAmplitude packets slope stop base transition upper (g.index upper s)+
      g.packetResidual (packets.filter keep) slope stop base transition lower upper (g.index lower s)+
      g.packetAmplitude (packets.filter fun q => ¬keep q) slope stop base transition lower
        (g.index lower s) := by
  have hupper : g.packetAmplitude (packets.filter keep) slope stop base transition upper
      (g.index upper s) = g.packetAmplitude packets slope stop base transition upper (g.index upper s) := by
    unfold packetAmplitude
    congr 1
    ext q
    simp only [packetSet,Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨hqp,hcell,hstop⟩
      exact ⟨⟨hqp,hlong q hqp hstop hcell⟩,hcell,hstop⟩
  have hblock := g.packetAmplitude_block (packets.filter keep) slope stop base transition
    hlu (g.index lower s) {g.index upper s} (fun _ => s)
    (by intro c hc; exact (Finset.mem_singleton.mp hc).symm)
    (by intro c _; rfl) (by
      intro q hq _
      have hqp := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1)
      exact Finset.mem_singleton.mpr (hkeep q hqp.1 hqp.2))
  simp only [Finset.sum_singleton,hupper] at hblock
  rw [g.packetAmplitude_filter_split packets slope stop base transition keep lower (g.index lower s),hblock]
  abel

variable {ι X : Type*}

/-- The recurrence uses the actual eligible-top child, not a selected
packet child or a positive-amplitude child. -/
theorem sourcePacketAmplitude_unary_recurrence (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → ι) (stop : σ → ℕ)
    (value : σ → E) (phase : ℕ → ℂ) (a : ℝ) (x : X)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (heligible : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop q))
    {lower upper : ℕ} (hlu : lower ≤ upper) (pathSlope : ℝ) :
    let keep := fun q => assigned q ∈ g.cellTops tops slope precision cutoff upper
      (g.index upper pathSlope)
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop value
      phase a x lower (g.index lower pathSlope) =
      g.packetPathProduct transition lower upper pathSlope •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop value
          phase a x upper (g.index upper pathSlope)+
      g.packetResidual (packets.filter keep) (fun q => slope (assigned q)) stop base transition
        lower upper (g.index lower pathSlope)+
      g.packetAmplitude (packets.filter fun q => ¬keep q) (fun q => slope (assigned q)) stop base
        transition lower (g.index lower pathSlope) := by
  dsimp only
  have hkeep (q : σ) (_hq : q ∈ packets)
      (hq : assigned q ∈ g.cellTops tops slope precision cutoff upper (g.index upper pathSlope)) :
      g.index upper (slope (assigned q)) = g.index upper pathSlope :=
    ((g.mem_cellTops _ _ _ _ _ _ _).mp hq).2.1
  have hlong (q : σ) (hqp : q ∈ packets) (hstop : upper ≤ stop q)
      (hcell : g.index upper (slope (assigned q)) = g.index upper pathSlope) :
      assigned q ∈ g.cellTops tops slope precision cutoff upper (g.index upper pathSlope) :=
    (g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨hassigned q hqp,hcell,
      g.eligible_of_le (hp _ (hassigned q hqp)) hstop (heligible q hqp)⟩
  have h := g.packetAmplitude_one_child packets (fun q => slope (assigned q)) stop
    (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
    (g.sourceTransition tops slope precision cutoff weight K gap phase x)
    (fun q => assigned q ∈ g.cellTops tops slope precision cutoff upper (g.index upper pathSlope))
    hlu pathSlope hkeep hlong
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp only [sourcePacketAmplitude,packetAmplitude,packetResidual,
    packetSet,Finset.sum_filter]
  congr 3
  all_goals
    funext q
    by_cases hq : assigned q ∈ g.cellTops tops slope precision cutoff upper (g.index upper pathSlope)
    · simp only [hq,ite_true, if_true,not_true_eq_false,ite_false, if_false]
    · simp only [hq,ite_false, if_false,not_false_eq_true,ite_true, if_true]

/-- The actual source coefficient is the common later-starting weight
whenever the packet and path share the relevant terminal cell. -/
theorem source_packet_common_weight (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (a : ℝ) (x : X) (pathTop : ι) (htop : pathTop ∈ tops) (upper : ℕ)
    (he : g.eligible cutoff (precision pathTop) upper)
    (packetTop : ι) {start stop : ℕ} (hstop : stop ≤ upper)
    (hcell : g.index upper (slope packetTop) = g.index upper (slope pathTop)) :
    let n := fun j => g.mass tops slope precision cutoff weight j (g.index j (slope pathTop)) x
    let m := fun j => g.sourceBoundaryMass tops slope precision cutoff weight K gap j
      (g.index (j+1) (slope pathTop)) x
    g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      start stop (slope packetTop)*
      ((g.mass tops slope precision cutoff weight stop (g.index stop (slope packetTop)) x^(-a) : ℝ) : ℂ) =
      segmentWeight n (boundaryLog n m) phase a start stop := by
  dsimp only
  have hn (j : ℕ) (hj : j ≤ upper) :
      0 < g.mass tops slope precision cutoff weight j (g.index j (slope pathTop)) x :=
    g.path_mass_pos tops slope precision cutoff weight hw j pathTop htop
      (g.eligible_of_le (hp pathTop htop) hj he) x
  rw [g.packetPathProduct_eq_of_cell _ start stop (g.index_eq_of_le hstop hcell),
    g.index_eq_of_le hstop hcell]
  rw [segmentWeight_eq_path_product _ _ phase a start stop (hn stop hstop)
    (fun j hj => hn (j+1) ((Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2).trans hstop))
    (fun j hj => (hn (j+1) ((Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2).trans hstop)).trans_le
      (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
        (fun t x => (hw t x).le) hK gap j (slope pathTop) x).1)]
  simp only [packetPathProduct,sourceTransition,analyticTransition]
  ring

end AngularGrid

/-- Grouping a finite packet sum by its actual integer stopping level. -/
theorem weighted_packet_sum_by_stop {σ E : Type*} [AddCommMonoid E] [Module ℂ E]
    (packets : Finset σ) (stop : σ → ℕ) (value : σ → E) (weight : ℕ → ℂ)
    (lower upper : ℕ) :
    (∑ q ∈ packets.filter (fun q => lower ≤ stop q ∧ stop q < upper),
      weight (stop q) • value q) =
    ∑ k ∈ Finset.Ico lower upper,
      weight k • ∑ q ∈ packets.filter (fun q => stop q = k), value q := by
  classical
  let S := packets.filter (fun q => lower ≤ stop q ∧ stop q < upper)
  have hmap : ∀ q ∈ S, stop q ∈ Finset.Ico lower upper := by
    intro q hq
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hq).2
  rw [show packets.filter (fun q => lower ≤ stop q ∧ stop q < upper) = S from rfl,
    ← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro k hk
  have hset : S.filter (fun q => stop q = k) = packets.filter (fun q => stop q = k) := by
    ext q
    simp only [S,Finset.mem_filter]
    constructor
    · tauto
    · intro hq
      refine ⟨⟨hq.1,?_⟩,hq.2⟩
      simpa only [hq.2] using Finset.mem_Ico.mp hk
  rw [hset,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [(Finset.mem_filter.mp hq).2]

/-- Consecutive block intervals exactly fill the corresponding angular
interval, regardless of their unequal lengths. -/
theorem sum_consecutive_block_intervals {E : Type*} [AddCommMonoid E]
    (level : ℕ → ℕ) (hlevel : Monotone level) (f : ℕ → E)
    {e b : ℕ} (heb : e ≤ b) :
    (∑ j ∈ Finset.Ico e b, ∑ k ∈ Finset.Ico (level j) (level (j+1)), f k) =
      ∑ k ∈ Finset.Ico (level e) (level b), f k := by
  induction b, heb using Nat.le_induction with
  | base => simp
  | succ b heb ih =>
    rw [Finset.sum_Ico_succ_top heb,ih]
    exact Finset.sum_Ico_consecutive f (hlevel heb) (hlevel (Nat.le_succ b))

namespace AngularGrid
variable {σ ι X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Stop intervals belonging to different blocks are disjoint. -/
theorem block_of_stop_unique (level : ℕ → ℕ) (hlevel : StrictMono level)
    {i j k : ℕ} (hi : level i ≤ k ∧ k < level (i+1))
    (hj : level j ≤ k ∧ k < level (j+1)) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have h := hlevel.monotone (show i+1 ≤ j by omega)
    omega
  · have h := hlevel.monotone (show j+1 ≤ i by omega)
    omega

theorem fixedPathResidualPackets_block (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (level : ℕ → ℕ) (hlevel : StrictMono level)
    (count : ℕ) (pathSlope : ℝ) {j : ℕ} (hj : j < count) :
    (g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count pathSlope).filter
      (fun q => level j ≤ stop q ∧ stop q < level (j+1)) =
    (g.sourceContinuingPackets tops slope precision cutoff packets assigned (level (j+1)) pathSlope).filter
      (fun q => level j ≤ stop q ∧ stop q < level (j+1)) := by
  ext q
  simp only [fixedPathResidualPackets,sourceContinuingPackets,Finset.mem_filter]
  constructor
  · rintro ⟨⟨hqp,k,hk,hks,hkt⟩,hjs⟩
    have heq : k = j := block_of_stop_unique level hlevel hks hjs
    subst k
    exact ⟨⟨hqp,hkt⟩,hjs⟩
  · rintro ⟨⟨hqp,hkt⟩,hjs⟩
    exact ⟨⟨hqp,j,hj,hjs,hkt⟩,hjs⟩

/-- Once a packet's top continues in the path child, its parent-cell
condition in the residual is automatic by angular-grid nesting. -/
theorem packetResidual_continuing_eq (g : AngularGrid) (packets : Finset σ)
    (slope : σ → ℝ) (stop : σ → ℕ) (base : σ → E) (transition : ℕ → ℤ → ℂ)
    (keep : σ → Prop) {lower upper : ℕ} (hlu : lower ≤ upper) (s : ℝ)
    (hkeep : ∀ q ∈ packets, keep q → g.index upper (slope q) = g.index upper s) :
    g.packetResidual (packets.filter keep) slope stop base transition lower upper (g.index lower s) =
      ∑ q ∈ (packets.filter keep).filter (fun q => lower ≤ stop q ∧ stop q < upper),
        g.packetPathProduct transition lower (stop q) (slope q) • base q := by
  unfold packetResidual
  apply Finset.sum_congr
  · ext q
    simp only [packetSet,Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨⟨hqp,hqk⟩,hlo,hhi⟩
      exact ⟨⟨⟨hqp,hqk⟩,g.index_eq_of_le hlu (hkeep q hqp hqk),hlo⟩,hhi⟩
  · intro q _
    rfl

/-- After propagation from an earlier block, the continuing residual
uses the same coefficient at each stop level. Every packet remains in
the deterministic path residual subset defined above. -/
theorem source_propagated_residual_eq (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (value : σ → E) (phase : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ)
    (pathTop : ι) (htop : pathTop ∈ tops)
    {e j : ℕ} (hej : e ≤ j) (hj : j < count)
    (he : g.eligible cutoff (precision pathTop) (level (j+1))) :
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
    let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)
    let n := fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x
    let m := fun k => g.sourceBoundaryMass tops slope precision cutoff weight K gap k
      (g.index (k+1) (slope pathTop)) x
    unaryPropagator (fun b => g.packetPathProduct transition (level b) (level (b+1)) (slope pathTop)) e j •
      g.packetResidual (g.sourceContinuingPackets tops slope precision cutoff packets assigned
        (level (j+1)) (slope pathTop)) (fun q => slope (assigned q)) stop base transition
        (level j) (level (j+1)) (g.index (level j) (slope pathTop)) =
    ∑ q ∈ Q.filter (fun q => level j ≤ stop q ∧ stop q < level (j+1)),
      segmentWeight n (boundaryLog n m) phase a (level e) (stop q) • value q := by
  dsimp only
  let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
  let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
  let keep := fun q => assigned q ∈ g.cellTops tops slope precision cutoff
    (level (j+1)) (g.index (level (j+1)) (slope pathTop))
  have hkeep (q : σ) (_hq : q ∈ packets) (hk : keep q) :
      g.index (level (j+1)) (slope (assigned q)) = g.index (level (j+1)) (slope pathTop) :=
    (g.mem_cellTops _ _ _ _ _ _ _).mp hk |>.2.1
  have hres := g.packetResidual_continuing_eq packets
    (fun q => slope (assigned q)) stop base transition keep
    (hlevel.monotone (Nat.le_succ j)) (slope pathTop) hkeep
  have hset : @Finset.filter σ keep (fun q => Classical.propDecidable (keep q)) packets =
      g.sourceContinuingPackets tops slope precision cutoff packets assigned
      (level (j+1)) (slope pathTop) := by
    ext q
    simp only [Finset.mem_filter,sourceContinuingPackets,keep]
  rw [hset] at hres
  rw [hres]
  rw [← g.fixedPathResidualPackets_block tops slope precision cutoff packets assigned stop
    level hlevel count (slope pathTop) hj,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hqc : q ∈ (g.sourceContinuingPackets tops slope precision cutoff packets assigned
      (level (j+1)) (slope pathTop)).filter
      (fun q => level j ≤ stop q ∧ stop q < level (j+1)) := by
    rw [← g.fixedPathResidualPackets_block tops slope precision cutoff packets assigned stop
      level hlevel count (slope pathTop) hj]
    exact hq
  obtain ⟨hqchild,hs⟩ := Finset.mem_filter.mp hqc
  have hqpacket := (Finset.mem_filter.mp hqchild).1
  have hcell := hkeep q hqpacket (Finset.mem_filter.mp hqchild).2
  have hmcell := g.index_eq_of_le hs.2.le hcell
  have hc := g.propagated_packet_coefficient transition level hlevel.monotone
    (slope pathTop) (slope (assigned q)) hej hs.1 hs.2.le hcell
  have hwgt := g.source_packet_common_weight tops slope precision cutoff weight hp hw hK gap phase
    a x pathTop htop (level (j+1)) he pathTop hs.2.le rfl (start := level e)
  change _ • (_ • base q) = _
  simp only [base,sourcePacketBase,smul_smul]
  rw [← mul_assoc,hc,hmcell]
  exact congrArg (fun z : ℂ => z • value q) hwgt

/-- The sum of propagated residuals over consecutive blocks is one
weighted stop-level interval of the fixed raw residual family. -/
theorem source_propagated_residual_interval (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (value : σ → E) (phase : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ)
    (pathTop : ι) (htop : pathTop ∈ tops)
    {e f : ℕ} (hef : e ≤ f) (hfc : f ≤ count)
    (he : g.eligible cutoff (precision pathTop) (level f)) :
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
    let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)
    let n := fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x
    let m := fun k => g.sourceBoundaryMass tops slope precision cutoff weight K gap k
      (g.index (k+1) (slope pathTop)) x
    (∑ j ∈ Finset.Ico e f,
      unaryPropagator (fun b => g.packetPathProduct transition (level b) (level (b+1)) (slope pathTop)) e j •
        g.packetResidual (g.sourceContinuingPackets tops slope precision cutoff packets assigned
          (level (j+1)) (slope pathTop)) (fun q => slope (assigned q)) stop base transition
          (level j) (level (j+1)) (g.index (level j) (slope pathTop))) =
    ∑ k ∈ Finset.Ico (level e) (level f),
      segmentWeight n (boundaryLog n m) phase a (level e) k •
        ∑ q ∈ Q.filter (fun q => stop q = k), value q := by
  dsimp only
  calc
    _ = ∑ j ∈ Finset.Ico e f, ∑ q ∈
        (g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)).filter
          (fun q => level j ≤ stop q ∧ stop q < level (j+1)),
        segmentWeight
          (fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x)
          (boundaryLog (fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x)
            (fun k => g.sourceBoundaryMass tops slope precision cutoff weight K gap k (g.index (k+1) (slope pathTop)) x))
          phase a (level e) (stop q) • value q := by
      apply Finset.sum_congr rfl
      intro j hj
      exact g.source_propagated_residual_eq tops slope precision cutoff weight hp hw hK gap
        packets assigned stop value phase a x level hlevel count pathTop htop
        (Finset.mem_Ico.mp hj).1 ((Finset.mem_Ico.mp hj).2.trans_le hfc)
        (g.eligible_of_le (hp pathTop htop)
          (hlevel.monotone (Nat.succ_le_of_lt (Finset.mem_Ico.mp hj).2)) he)
    _ = ∑ j ∈ Finset.Ico e f, ∑ k ∈ Finset.Ico (level j) (level (j+1)),
        segmentWeight
          (fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x)
          (boundaryLog (fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x)
            (fun k => g.sourceBoundaryMass tops slope precision cutoff weight K gap k (g.index (k+1) (slope pathTop)) x))
          phase a (level e) k •
          ∑ q ∈ (g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)).filter
            (fun q => stop q = k), value q := by
      apply Finset.sum_congr rfl
      intro j _
      exact weighted_packet_sum_by_stop _ stop value _ _ _
    _ = _ := sum_consecutive_block_intervals level hlevel.monotone _ hef

/-- Abel summation of the actual propagated residuals. All raw sums use
the one fixed residual packet subset. The coefficient cost involves
the full-root mass ratio, even for a segment starting much later. -/
theorem source_propagated_residual_bound (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → ι) (stop : σ → ℕ) (value : σ → E) (phase : ℕ → ℂ)
    (a : ℝ) (x : X) (level : ℕ → ℕ) (hlevel : StrictMono level) (count : ℕ)
    (pathTop : ι) (htop : pathTop ∈ tops)
    {e f : ℕ} (hef : e < f) (hfc : f ≤ count)
    (he : g.eligible cutoff (precision pathTop) (level f)) (H : ℕ) (hH : level f ≤ H)
    {lower Z : ℝ} (ha : 0 ≤ a) (hlower : 0 < lower) (hZ : 0 ≤ Z)
    (hnlower : lower ≤ g.mass tops slope precision cutoff weight (level f)
      (g.index (level f) (slope pathTop)) x)
    (hz0 : ∀ k < level f, 0 ≤ (phase k).re) (hz : ∀ k < level f, ‖phase k‖ ≤ Z) :
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
    let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)
    let n := fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x
    let raw := fun k => ∑ q ∈ Q.filter (fun q => stop q = k), value q
    ‖∑ j ∈ Finset.Ico e f,
      unaryPropagator (fun b => g.packetPathProduct transition (level b) (level (b+1)) (slope pathTop)) e j •
        g.packetResidual (g.sourceContinuingPackets tops slope precision cutoff packets assigned
          (level (j+1)) (slope pathTop)) (fun q => slope (assigned q)) stop base transition
          (level j) (level (j+1)) (g.index (level j) (slope pathTop))‖ ≤
      lower^(-a)*(1+(a+Z*K)*Real.log (n 0/lower))*
        intervalOscillation (packetPrefix raw) H (level e) (level f) := by
  dsimp only
  rw [g.source_propagated_residual_interval tops slope precision cutoff weight hp hw hK gap
    packets assigned stop value phase a x level hlevel count pathTop htop hef.le hfc he]
  let n := fun k => g.mass tops slope precision cutoff weight k (g.index k (slope pathTop)) x
  let m := fun k => g.sourceBoundaryMass tops slope precision cutoff weight K gap k
    (g.index (k+1) (slope pathTop)) x
  let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope pathTop)
  let raw := fun k => ∑ q ∈ Q.filter (fun q => stop q = k), value q
  have hnf : lower ≤ n (level f) := hnlower
  have hanti : Antitone n := g.path_mass_antitone tops slope precision cutoff weight hp
    (fun t x => (hw t x).le) pathTop x
  have hf0 : 0 < level f := (Nat.zero_le (level e)).trans_lt (hlevel hef)
  have hlast : level f-1+1 = level f := by omega
  have hn (j : ℕ) (hj : j ≤ level f-1) : lower ≤ n j :=
    hnf.trans (hanti (by omega))
  have hm (j : ℕ) (_hj : j < level f-1) : n (j+1) ≤ m j ∧ m j ≤ n (j+1-K) :=
    g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp (fun t x => (hw t x).le)
      hK gap j (slope pathTop) x
  have hab := boundary_segment_amplitude_le_oscillation n m phase raw
    (level e) (level f-1) K H (level e) (level f) a lower Z
    (by have := hlevel hef; omega) le_rfl (by omega) hH ha hlower hZ hn
    (hanti.antitoneOn _) hm (fun k hk => hz0 k (by omega)) (fun k hk => hz k (by omega))
  rw [hlast] at hab
  apply hab.trans
  apply mul_le_mul_of_nonneg_right _ (intervalOscillation_nonneg ..)
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hlower.le _)
  apply add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by positivity : 0 ≤ a+Z*K))
  · have hn0 : 0 < n 0 := hlower.trans_le (hn 0 (Nat.zero_le _))
    exact Real.log_le_log (div_pos hn0 (hlower.trans_le (hn _ le_rfl)))
      (div_le_div_of_nonneg_left hn0.le hlower (hn _ le_rfl))

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed residual collection is grouped by stopping level in the
unary recurrence and by packet length in the reference-line variation.
Antitone stopping transports every disjoint collection of level bands
to disjoint length bands. Empty bands contribute zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem packetPartialSum_sub_eq_band {N : ℕ} {E : Type*} [AddCommGroup E]
    (f : Fin N → E) {a b : ℕ} (hab : a ≤ b) :
    packetPartialSum f b-packetPartialSum f a =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => a ≤ j.val ∧ j.val < b), f j := by
  simp only [packetPartialSum,Finset.sum_filter,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hja : j.val < a
  · have hjb : j.val < b := hja.trans_le hab
    simp [hja,hjb,not_le.mpr hja]
  · by_cases hjb : j.val < b
    · simp [hja,hjb,not_lt.mp hja]
    · simp [hja,hjb]

/-- Exact regrouping by stopping levels for any fixed packet subset. -/
theorem sum_packet_stopping_fibers {σ E : Type*} [AddCommMonoid E]
    (Q : Finset σ) (stop : σ → ℕ) (value : σ → E) (a b : ℕ) :
    (∑ k ∈ Finset.Ico a b, ∑ q ∈ Q.filter (fun q => stop q = k), value q) =
      ∑ q ∈ Q.filter (fun q => a ≤ stop q ∧ stop q < b), value q := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : stop q ∈ Finset.Ico a b
  · rw [Finset.sum_eq_single_of_mem (stop q) hq]
    · simp only [ite_true, if_true,ite_eq_left (Finset.mem_Ico.mp hq)]
    · intro k _ hk
      exact ite_eq_right (Ne.symm hk)
  · rw [Finset.sum_eq_zero]
    · exact (ite_eq_right (fun h => hq (Finset.mem_Ico.mpr h))).symm
    · intro k hk
      exact ite_eq_right (fun heq => hq (by simpa only [heq] using hk))

/-- Grouping by packet length preserves multiplicities and arbitrary
fixed packet selection. -/
theorem packet_stopping_band_eq_length_band {σ E : Type*} [AddCommMonoid E]
    {N : ℕ} (Q : Finset σ) (lengthIndex : σ → Fin N) (stop : Fin N → ℕ)
    (value : σ → E) (a b : ℕ) :
    (∑ q ∈ Q.filter (fun q => a ≤ stop (lengthIndex q) ∧ stop (lengthIndex q) < b), value q) =
      ∑ j ∈ Finset.univ.filter (fun j => a ≤ stop j ∧ stop j < b),
        ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q := by
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
    (Finset.sum_fiberwise_eq_sum_filter Q
      (Finset.univ.filter (fun j => a ≤ stop j ∧ stop j < b)) lengthIndex value).symm

/-- Zero-length intervals may be discarded before applying the finite
disjoint-interval variation bound. -/
theorem disjoint_increment_cube_sum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) (a b : ι → ℕ)
    (hab : ∀ i, a i ≤ b i) (hb : ∀ i, b i ≤ N)
    (hdisjoint : ∀ i j, i ≠ j → a i < b i → a j < b j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, ‖F (b i)-F (a i)‖^3) ≤ finiteCubicVariation F N := by
  let active := Finset.univ.filter (fun i : ι => a i < b i)
  have hzero (i : ι) (hi : i ∈ Finset.univ) (hni : i ∉ active) :
      ‖F (b i)-F (a i)‖^3 = 0 := by
    have hn : ¬a i < b i := fun h => hni (Finset.mem_filter.mpr ⟨hi,h⟩)
    have heq : a i = b i := le_antisymm (hab i) (not_lt.mp hn)
    simp [heq]
  calc
    _ = ∑ i ∈ active, ‖F (b i)-F (a i)‖^3 :=
      (Finset.sum_subset (Finset.subset_univ active) hzero).symm
    _ = ∑ i : active, ‖F (b i.val)-F (a i.val)‖^3 := by
      exact (Finset.sum_subtype active (p := fun i => i ∈ active) (by simp)
        (fun i : ι => ‖F (b i)-F (a i)‖^3))
    _ ≤ _ := disjoint_increment_cube_sum_exact F N
      (fun i : active => a i.val) (fun i => b i.val)
      (fun i => (Finset.mem_filter.mp i.property).2) (fun i => hb i.val)
      (fun i j hij => hdisjoint i.val j.val (fun h => hij (Subtype.ext h))
        (Finset.mem_filter.mp i.property).2 (Finset.mem_filter.mp j.property).2)

/-- Disjoint stopping-level intervals become disjoint intervals of the
one fixed length sequence, including when some length fibers are empty. -/
theorem disjoint_stopping_band_cube_sum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] {N : ℕ} (f : Fin N → E)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (a b : ι → ℕ)
    (hdisjoint : ∀ i j, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    (∑ i, ‖∑ j ∈ Finset.univ.filter (fun j => a i ≤ stop j ∧ stop j < b i), f j‖^3) ≤
      finiteCubicVariation (packetPartialSum f) N := by
  choose lower upper hlu hu hband using fun i =>
    antitone_stopping_band_interval stop hstop (a i) (b i)
  have hdis (i j : ι) (hij : i ≠ j) (hi : lower i < upper i)
      (hj : lower j < upper j) : upper i ≤ lower j ∨ upper j ≤ lower i := by
    by_contra hn
    have h1 : lower j < upper i := by omega
    have h2 : lower i < upper j := by omega
    have hmaxi : max (lower i) (lower j) < upper i := max_lt_iff.mpr ⟨hi,h1⟩
    have hmaxj : max (lower i) (lower j) < upper j := max_lt_iff.mpr ⟨h2,hj⟩
    let k : Fin N := ⟨max (lower i) (lower j), hmaxi.trans_le (hu i)⟩
    have hki : a i ≤ stop k ∧ stop k < b i := (hband i k).mpr ⟨le_max_left _ _,hmaxi⟩
    have hkj : a j ≤ stop k ∧ stop k < b j := (hband j k).mpr ⟨le_max_right _ _,hmaxj⟩
    rcases hdisjoint i j hij with h | h <;> omega
  have heq (i : ι) :
      (∑ j ∈ Finset.univ.filter (fun j => a i ≤ stop j ∧ stop j < b i), f j) =
        packetPartialSum f (upper i)-packetPartialSum f (lower i) := by
    rw [packetPartialSum_sub_eq_band f (hlu i)]
    apply Finset.sum_congr
    · ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact hband i j
    · intro j _
      rfl
  simp_rw [heq]
  exact disjoint_increment_cube_sum (packetPartialSum f) N lower upper hlu hu hdis

/-- The cubic variation of the stop-grouped raw prefix is controlled by
the original length-grouped raw prefix, independently of angular depth. -/
theorem stopping_prefix_cubic_variation {σ E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (Q : Finset σ) (lengthIndex : σ → Fin N)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (value : σ → E) (H : ℕ) :
    let raw := fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q
    let bands := fun j => ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q
    finiteCubicVariation (packetPrefix raw) H ≤
      finiteCubicVariation (packetPartialSum bands) N := by
  dsimp only
  apply Finset.sup'_le
  intro p _
  split_ifs with hp
  · have hband (i : Fin H) :
        packetPrefix (fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q)
          (p i.succ)-
        packetPrefix (fun k => ∑ q ∈ Q.filter (fun q => stop (lengthIndex q) = k), value q)
          (p i.castSucc) =
        ∑ j ∈ Finset.univ.filter (fun j => (p i.castSucc).val ≤ stop j ∧ stop j < (p i.succ).val),
          ∑ q ∈ Q.filter (fun q => lengthIndex q = j), value q := by
      rw [packetPrefix,packetPrefix,← Finset.sum_Ico_eq_sub _ (hp (Fin.castSucc_le_succ i)),
        sum_packet_stopping_fibers,packet_stopping_band_eq_length_band]
    simp_rw [hband]
    apply disjoint_stopping_band_cube_sum _ stop hstop
      (fun i : Fin H => (p i.castSucc).val) (fun i => (p i.succ).val)
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (hp (show i.succ ≤ j.castSucc by
        change i.val+1 ≤ j.val
        exact Nat.succ_le_of_lt h))
    · exact Or.inr (hp (show j.succ ≤ i.castSucc by
        change j.val+1 ≤ i.val
        exact Nat.succ_le_of_lt h))
  · exact finiteCubicVariation_nonneg _ _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceBlockPathMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source predictor's off-child fractions are bounded by the actual
forward path drop. The final ineligible path has drop one even if other
children still continue. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

theorem sourcePredictionValue_pos {ι κ : Type} [Fintype ι] [Fintype κ]
    (p μ n : ℝ) (hn : 0 < n) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) :
    0 < sourcePredictionValue p μ n c A lam := by
  unfold sourcePredictionValue
  apply energyRatio_pos
  have hs : 0 ≤ ∑ i, (c i/n)*‖(c i)^(μ-1) • A i‖^p :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (div_nonneg (hc i) hn.le)
      (Real.rpow_nonneg (norm_nonneg _) _))
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceNodeMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurability of the original source node ratios and the finite active
path product. These are the integrands used for line-to-plane gluing,
independently of any selected snapshot predictors. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

variable {X : Type*} {ι κ : Type} [MeasurableSpace X] [Fintype ι] [Fintype κ]

omit [MeasurableSpace X] in
/-- The measurable active product agrees exactly with the finite prefix
ending at the first mass crossing. The terminal mass may be zero. -/
theorem sourceActiveProduct_eq_stopped_product (n beta : X → ℕ → ℝ)
    (M : ℝ) (count : ℕ) (x : X) (hfinal : n x count ≤ M) (hanti : Antitone (n x)) :
    sourceActiveProduct n beta M count x =
      ∏ j ∈ Finset.range (firstMassStop (n x) count M), beta x j := by
  let stop := firstMassStop (n x) count M
  have hs : stop ≤ count := (firstMassStop_spec (n x) count M hfinal).1
  unfold sourceActiveProduct
  calc
    _ = ∏ j ∈ Finset.range stop, if M < n x j then beta x j else 1 := by
      symm
      apply Finset.prod_subset (Finset.range_mono hs)
      intro j _ hj
      have hjs : ¬j < stop := fun h => hj (Finset.mem_range.mpr h)
      have hn : ¬M < n x j := fun h => hjs
        ((firstMassStop_active_iff (n x) count M hfinal hanti j).mpr h)
      simp only [ite_eq_right hn]
    _ = ∏ j ∈ Finset.range stop, beta x j := by
      apply Finset.prod_congr rfl
      intro j hj
      exact ite_eq_left ((firstMassStop_active_iff (n x) count M hfinal hanti j).mp
        (Finset.mem_range.mp hj))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePathPrediction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The residual-free predictor on the actual packet path. Its child
family and coefficients are the same ones used by the physical estimate. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X : Type*} {κ : Type} [MeasurableSpace X] [Fintype κ]

omit [MeasurableSpace X] in
theorem sourceShiftedPathPrediction_pos {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hw : ∀ t x, 0 < weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a p μ : ℝ) (tag : Fin Kb) (top : τ)
    (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j)) :
    0 < g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets
      assigned stop value phase a p μ tag top x j := by
  unfold sourceShiftedPathPrediction sourceBlockPrediction
  apply sourcePredictionValue_pos
  · exact g.path_mass_pos tops slope precision cutoff weight hw _ top htop he x
  · intro i
    exact g.mass_nonnegative tops slope precision cutoff weight (fun t x => (hw t x).le)
      _ i.val x

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMotionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The quantitative small factors in predictable motion. Fixed powers
and constants are absorbed only after the packet and weight estimates. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

/-- Every fixed polynomial prefactor in the exact source motion bounds
is dominated by a quarter-power gain of the actual rounded dyadic step. -/
theorem eventually_source_polynomial_motion (C p : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      C*L^p/Real.sqrt (SourceParameters.step L) ≤
        SourceParameters.step L^(-(1/4:ℝ)) := by
  have hsub := eventually_source_subpower_amplitude (p+1) (1/4) (by norm_num)
  filter_upwards [hsub, eventually_ge_atTop (max 1 C)] with L hL hlarge
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hCL : C ≤ L := (le_max_right _ _).trans hlarge
  have hpower : L^(p+1) ≤ SourceParameters.step L^(1/4:ℝ) := by
    have h := hL 1 1 (by norm_num) (by norm_num) (by simp; positivity)
    have hn : 0 ≤ L^(p+1) := Real.rpow_nonneg hL0.le _
    norm_num at h
    linarith
  have hpoly : C*L^p ≤ SourceParameters.step L^(1/4:ℝ) := by
    calc
      _ ≤ L*L^p := mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hL0.le _)
      _ = L^(p+1) := by rw [Real.rpow_add hL0, Real.rpow_one]; ring
      _ ≤ _ := hpower
  calc
    _ ≤ SourceParameters.step L^(1/4:ℝ)/Real.sqrt (SourceParameters.step L) :=
      div_le_div_of_nonneg_right hpoly (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub (SourceParameters.step_pos L)]
      norm_num

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Phase_SourcePredictableDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial bounds for the source predictable-motion
coefficient, before its dyadic gain is absorbed. -/

noncomputable section
namespace LipschitzHilbert

theorem source_blockCount_le_square {L : ℝ} (hL : 5 ≤ L) :
    (SourceParameters.blockCount L : ℝ) ≤ L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlog : Real.log L ≤ 2*Real.sqrt L := by
    have hb := Real.log_le_rpow_div hL0 (by norm_num : (0:ℝ)<1/2)
    rw [← Real.sqrt_eq_rpow] at hb
    linarith
  have hsq : Real.log L^2 ≤ 4*L := by
    have ht := pow_le_pow_left₀ hlog0 hlog 2
    have hr := Real.sq_sqrt hL0
    nlinarith
  have hceil : (SourceParameters.blockCount L : ℝ) ≤ Real.log L^2+1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log L))).le
  exact hceil.trans (by nlinarith)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseBlocks
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source line windows grow along the angular path. Reading those
windows in reverse gives increasing levels in one finite line grid. Only
the factors are reordered: the stopping budget retains its forward mass
path, including the possibility of a zero terminal mass. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.ShiftedBlocks

variable {K : ℕ}

theorem reverseLevel_le (σ : Fin K) (count k : ℕ) :
    reverseLevel σ count k ≤ endpoint σ count := Nat.sub_le _ _

theorem reverseLevel_monotone (hK : 0 < K) (σ : Fin K) (count : ℕ) :
    Monotone (reverseLevel σ count) := by
  intro a b hab
  exact Nat.sub_le_sub_left ((endpoint_strictMono hK σ).monotone
    (Nat.sub_le_sub_left hab count)) _

end LipschitzHilbert.ShiftedBlocks

namespace LipschitzHilbert

theorem source_reverse_line_mesh {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) (count k : ℕ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    (sourceReverseLineGrid g L origin hw σ count).meshWidth
        (ShiftedBlocks.reverseLevel σ count k) =
      sourceLineScale g L w (ShiftedBlocks.endpoint σ (count-k)) := by
  have hle := (ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.sub_le count k)
  have hm := source_block_line_mesh g L origin hw
    (ShiftedBlocks.endpoint σ (count-k)) (ShiftedBlocks.endpoint σ count) hle hbranch
  simpa only [sourceReverseLineGrid,ShiftedBlocks.reverseLevel,sourceLineGrid_mesh] using hm

/-- The coarse side of original block j is its child window. -/
theorem source_reverse_block_coarse {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ} (hj : j < count)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    (sourceReverseLineGrid g L origin hw σ count).meshWidth
        (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)) =
      sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) := by
  rw [source_reverse_line_mesh g L origin hw σ hK count _ hbranch]
  congr 2
  unfold ShiftedBlocks.reverseIndex
  omega

/-- Refining that child window across the block gives its parent mesh. -/
theorem source_reverse_block_fine {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ} (hj : j < count)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) :
    (sourceReverseLineGrid g L origin hw σ count).meshWidth
        (ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)) =
      sourceLineScale g L w (ShiftedBlocks.endpoint σ j) := by
  rw [source_reverse_line_mesh g L origin hw σ hK count _ hbranch]
  congr 2
  unfold ShiftedBlocks.reverseIndex
  omega

theorem source_reverse_local_mesh {K : ℕ} (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ} (hj : j < count)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) (i : ℕ) :
    let grid := sourceReverseLineGrid g L origin hw σ count
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
    (grid.lineWindow coarse i (fine-coarse)).width =
        sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) ∧
      (grid.lineWindow coarse i (fine-coarse)).meshWidth (fine-coarse) =
        sourceLineScale g L w (ShiftedBlocks.endpoint σ j) := by
  dsimp only
  constructor
  · exact source_reverse_block_coarse g L origin hw σ hK hj hbranch
  · rw [FiniteLineGrid.lineWindow_meshWidth,
      Nat.add_sub_of_le (ShiftedBlocks.reverseLevel_monotone hK σ count (Nat.le_succ _))]
    exact source_reverse_block_fine g L origin hw σ hK hj hbranch

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceTerminalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The least ineligible shifted endpoint provides a finite terminal
generation without enlarging the source root line window past its top.
This includes exactly one final block after the last eligible endpoint. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem firstIneligibleShiftedBlock_spec {K : ℕ} (g : AngularGrid) (cutoff precision : ℝ)
    (hp : 0 < precision) (hK : 0 < K) (σ : Fin K) :
    ¬g.eligible cutoff precision
      (ShiftedBlocks.endpoint σ (g.firstIneligibleShiftedBlock cutoff precision hp hK σ)) :=
  Nat.find_spec (g.exists_shifted_terminal cutoff precision hp hK σ)

theorem eligible_before_firstIneligibleShiftedBlock {K : ℕ}
    (g : AngularGrid) (cutoff precision : ℝ) (hp : 0 < precision) (hK : 0 < K)
    (σ : Fin K) {j : ℕ} (hj : j < g.firstIneligibleShiftedBlock cutoff precision hp hK σ) :
    g.eligible cutoff precision (ShiftedBlocks.endpoint σ j) := by
  exact Classical.not_not.mp
    (Nat.find_min (g.exists_shifted_terminal cutoff precision hp hK σ) hj)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed residual packet collection uses only endpoints at which
the reference top is still eligible. Its packets are shorter than that
top and lie in the reference angular cone. These are the geometric
hypotheses of the existing reference-line variation estimate. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem not_eligible_above_lastEligible (g : AngularGrid)
    (cutoff precision : ℝ) (hp : 0 < precision)
    (hzero : g.eligible cutoff precision 0) {k : ℕ}
    (hk : g.lastEligible cutoff precision hp < k) :
    ¬g.eligible cutoff precision k := by
  intro he
  exact (not_le.mpr hk) ((g.eligible_iff_le_lastEligible cutoff precision hp hzero k).mp he)

/-- The definition with natural subtraction stays monotone even at
empty scales that were already ineligible at level zero. -/
theorem lastEligible_antitone_precision_global (g : AngularGrid) (cutoff p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q) :
    g.lastEligible cutoff q hq ≤ g.lastEligible cutoff p hp := by
  unfold lastEligible
  apply Nat.sub_le_sub_right
  apply Nat.find_le
  intro he
  apply Nat.find_spec (g.exists_ineligible cutoff p hp)
  apply (mul_le_mul_of_nonneg_right hpq (by positivity)).trans
  exact he

theorem source_length_stopping_antitone {N : ℕ} (g : AngularGrid)
    (cutoff : ℝ) {w : ℝ} (hw : 0 < w) (length : Fin N → ℝ)
    (hlen : ∀ j, 0 < length j) (horder : Antitone length) :
    Antitone (fun j => g.lastEligible cutoff (w/length j) (div_pos hw (hlen j))) := by
  intro i j hij
  exact g.lastEligible_antitone_precision_global cutoff _ _ (div_pos hw (hlen i))
    (div_pos hw (hlen j))
    (div_le_div_of_nonneg_left hw.le (hlen j) (horder hij))

/-- A shorter stopping time means a strictly shorter physical packet
than any reference length still eligible at the block endpoint. -/
theorem residual_packet_length_and_cone (g : AngularGrid)
    {w B packetLength referenceLength C packetSlope assignedSlope referenceSlope : ℝ}
    (hw : 0 < w) (hB : 0 < B) (hp : 0 < packetLength) (hR : 0 < referenceLength)
    (hzero : g.eligible (g.rootWidth/B^2) (w/packetLength) 0)
    {upper : ℕ}
    (hstop : g.lastEligible (g.rootWidth/B^2) (w/packetLength) (div_pos hw hp) < upper)
    (hreference : g.eligible (g.rootWidth/B^2) (w/referenceLength) upper)
    (hcell : g.index upper assignedSlope = g.index upper referenceSlope)
    (hangle : |packetSlope-assignedSlope| ≤ C*(w/packetLength)) :
    packetLength < referenceLength ∧
      |packetSlope-referenceSlope| ≤ (C+B^2)*(w/packetLength) := by
  have hnot := g.not_eligible_above_lastEligible (g.rootWidth/B^2) (w/packetLength)
    (div_pos hw hp) hzero hstop
  have hpacket : (g.rootWidth/B^2)/(g.branching:ℝ)^upper < w/packetLength := by
    exact not_le.mp (fun h => hnot ((g.eligible_iff_precision_le _ _ _).mpr h))
  have href := (g.eligible_iff_precision_le _ _ _).mp hreference
  have hprec : w/referenceLength < w/packetLength := href.trans_lt hpacket
  have hlen : packetLength < referenceLength := by
    by_contra hn
    have hle := div_le_div_of_nonneg_left hw.le hR (not_lt.mp hn)
    exact (not_le.mpr hprec) hle
  have hwidth : g.width upper < B^2*(w/packetLength) := by
    have heq : (g.rootWidth/B^2)/(g.branching:ℝ)^upper = g.width upper/B^2 := by
      unfold width
      ring
    rw [heq] at hpacket
    have h := (div_lt_iff₀ (sq_pos_of_pos hB)).mp hpacket
    simpa only [mul_comm] using h
  refine ⟨hlen,?_⟩
  calc
    |packetSlope-referenceSlope| ≤ |packetSlope-assignedSlope|+|assignedSlope-referenceSlope| :=
      abs_sub_le _ _ _
    _ ≤ C*(w/packetLength)+g.width upper := add_le_add hangle (g.same_cell_diameter upper hcell)
    _ ≤ C*(w/packetLength)+B^2*(w/packetLength) := add_le_add le_rfl hwidth.le
    _ = _ := by ring

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledStoppingVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original masked physical packets, grouped by their actual stopping
levels, have the same fixed length-variation bound used in the reference
event. This includes clamped prefixes and every disjoint unary run. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem cubicVariation_cube {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : cubicVariation F N ^ 3 = finiteCubicVariation F N := by
  rw [cubicVariation, ← Real.rpow_natCast, ← Real.rpow_mul (finiteCubicVariation_nonneg F N)]
  norm_num

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

theorem physicalMaskedValue_length_sum (y x : ℝ) (j : Fin N) :
    (∑ q ∈ Finset.univ.filter (fun q : P.PacketIndex => q.1 = j),
      P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x) q) =
        P.physicalMaskedBand alt hAlt t b v g T L A y j x := by
  classical
  rw [Finset.sum_filter,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [ite_true, if_true]
    ext k
    simp only [Fintype.sum_sigma,physicalMaskedValue,physicalMaskedBand,
      WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  · intro k _ hkj
    simp only [hkj,ite_false, if_false,Finset.sum_const_zero]
  · simp

/-- One fixed original variation controls the stopping prefix at every
angular horizon, without a factor depending on that horizon. -/
theorem physicalStoppingPrefix_variation_le (stop : Fin N → ℕ)
    (hstop : Antitone stop) (y x : ℝ) (H : ℕ) :
    finiteCubicVariation (P.physicalStoppingPrefix alt hAlt t b v g T L A stop (x,y+t*x)) H ≤
      P.physicalMaskedVariation alt hAlt t b v g T L A y x ^ 3 := by
  have h := stopping_prefix_cubic_variation (Finset.univ : Finset P.PacketIndex)
    (fun q => q.1) stop hstop (P.physicalMaskedValue alt hAlt t b v g T L A (x,y+t*x)) H
  dsimp only at h
  simp_rw [P.physicalMaskedValue_length_sum alt hAlt t b v g T L A y x] at h
  rw [physicalMaskedVariation,cubicVariation_cube]
  exact h

/-- The clamping in the stopped path theorem preserves this bound. -/
theorem physicalStoppingPrefix_clamped_variation_le (stop : Fin N → ℕ)
    (hstop : Antitone stop) (y x : ℝ) (H : ℕ) :
    finiteCubicVariation (fun k =>
      P.physicalStoppingPrefix alt hAlt t b v g T L A stop (x,y+t*x) (min k H)) (2*H) ≤
        P.physicalMaskedVariation alt hAlt t b v g T L A y x ^ 3 := by
  apply (finiteCubicVariation_comp_le _ _ (fun k => min k H)
    (fun _ _ h => min_le_min h le_rfl) (min_le_left _ _)).trans
  exact P.physicalStoppingPrefix_variation_le alt hAlt t b v g T L A stop hstop y x (2*H)

theorem physicalStoppingPrefix_good_bound (stop : Fin N → ℕ)
    (hstop : Antitone stop) (y x : ℝ) (H : ℕ) {V : ℝ}
    (hV : P.physicalMaskedVariation alt hAlt t b v g T L A y x ≤ V) :
    finiteCubicVariation (fun k =>
      P.physicalStoppingPrefix alt hAlt t b v g T L A stop (x,y+t*x) (min k H)) (2*H) ≤ V^3 := by
  exact (P.physicalStoppingPrefix_clamped_variation_le alt hAlt t b v g T L A
    stop hstop y x H).trans (pow_le_pow_left₀ (cubicVariation_nonneg _ _) hV 3)

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSnapshotWindow
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The predictor uses displacement from a chosen good snapshot. Translate
its exact probability law and line-grid indices back to physical coordinates. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

namespace FiniteLineGrid

theorem snapshot_displacement_le_width (g : FiniteLineGrid) {x₀ x : ℝ}
    (h₀ : x₀ ∈ g.root) (hx : x ∈ g.root) : |x-x₀| ≤ g.width := by
  rw [abs_le]
  constructor <;> linarith [h₀.1,h₀.2,hx.1,hx.2]

end FiniteLineGrid

/-- Both parameterizations name the same physical point of the reference
line, so packet-motion estimates apply to the chosen snapshot. -/
theorem lineShift_snapshot (s y x₀ x : ℝ) :
    SlopeBox.lineShift s (x-x₀) (x₀,y+s*x₀) = (x,y+s*x) := by
  unfold SlopeBox.lineShift
  congr 1 <;> ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMarkingParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual relative mass-motion error is small even after multiplication
by the polynomial stopping threshold. These fixed-parameter bounds supply
the source's exceptional-cell argument. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_marking_parameters (D Kw A_M : ℝ)
    (hD : 0 ≤ D) (hKw : 0 < Kw) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      let q := Real.exp δ*δ
      q ≤ 1/8 ∧ (1+q)*L^A_M < L^A_M+1 := by
  let C := 5*D/Kw
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventually_source_polynomial_motion (8*Real.exp C*C) A_M,
    eventually_ge_atTop (1:ℝ)] with L hpoly hL
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hs : 1 ≤ Real.sqrt (SourceParameters.step L) := by
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    simpa using hG
  have hδ : C/Real.sqrt (SourceParameters.step L) ≤ C := div_le_self hC hs
  have hδ0 : 0 ≤ C/Real.sqrt (SourceParameters.step L) := div_nonneg hC (Real.sqrt_nonneg _)
  have hM : 1 ≤ L^A_M := Real.one_le_rpow hL hAM
  have he := Real.exp_le_exp.mpr hδ
  have hqM : (Real.exp (C/Real.sqrt (SourceParameters.step L))*
      (C/Real.sqrt (SourceParameters.step L)))*L^A_M ≤ 1/8 := by
    have hgain : SourceParameters.step L^(-(1/4:ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num)
    have hbound := hpoly.trans hgain
    have hq := mul_le_mul_of_nonneg_right he hδ0
    have hm := mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg (by linarith : 0 ≤ L) A_M)
    have heq : (8*Real.exp C*C)*L^A_M/Real.sqrt (SourceParameters.step L) =
        8*((Real.exp C*(C/Real.sqrt (SourceParameters.step L)))*L^A_M) := by ring
    rw [heq] at hbound
    linarith
  have hq0 : 0 ≤ Real.exp (C/Real.sqrt (SourceParameters.step L))*
      (C/Real.sqrt (SourceParameters.step L)) := mul_nonneg (Real.exp_pos _).le hδ0
  have hq := (mul_le_mul_of_nonneg_left hM hq0).trans hqM
  dsimp only
  change Real.exp (C/Real.sqrt (SourceParameters.step L))*(C/Real.sqrt (SourceParameters.step L)) ≤ 1/8 ∧ _
  refine ⟨by simpa only [mul_one] using hq,?_⟩
  change (1+Real.exp (C/Real.sqrt (SourceParameters.step L))*
    (C/Real.sqrt (SourceParameters.step L)))*L^A_M < L^A_M+1
  nlinarith

/-- The conclusion is uniform over the source weight scale Kw≥1. -/
theorem eventually_source_marking_parameters_uniform (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ Kw : ℝ, 1 ≤ Kw →
      let δ := (5*D/Kw)/Real.sqrt (SourceParameters.step L)
      let q := Real.exp δ*δ
      q ≤ 1/8 ∧ (1+q)*L^A_M < L^A_M+1 := by
  filter_upwards [eventually_source_marking_parameters D 1 A_M hD (by norm_num) hAM,
    eventually_ge_atTop (1:ℝ)] with L hbase hL
  intro Kw hKw
  have hs : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  have hd0 : 0 ≤ (5*D/Kw)/Real.sqrt (SourceParameters.step L) := by positivity
  have hd : (5*D/Kw)/Real.sqrt (SourceParameters.step L) ≤
      (5*D/1)/Real.sqrt (SourceParameters.step L) := by
    apply div_le_div_of_nonneg_right _ hs.le
    simpa only [div_one] using div_le_self (show 0 ≤ 5*D by positivity) hKw
  have hq := mul_le_mul (Real.exp_le_exp.mpr hd) hd hd0 (Real.exp_pos _).le
  dsimp only at hbase ⊢
  refine ⟨hq.trans hbase.1,?_⟩
  have hq1 : 1+Real.exp ((5*D/Kw)/Real.sqrt (SourceParameters.step L))*
      ((5*D/Kw)/Real.sqrt (SourceParameters.step L)) ≤
      1+Real.exp ((5*D/1)/Real.sqrt (SourceParameters.step L))*
        ((5*D/1)/Real.sqrt (SourceParameters.step L)) := by linarith
  have hm := mul_le_mul_of_nonneg_right hq1
    (Real.rpow_nonneg (by linarith : 0 ≤ L) A_M)
  exact hm.trans_lt hbase.2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceShiftedCellMotion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute path drops are sums over the actual lost tops. This gives
the cellwise relative motion needed by the source's infimum/supremum
marking rule, including a terminal block with no continuing path child. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem shiftedPathLossTops_subset {ι : Type*} {K : ℕ} (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (σ : Fin K) (top : ι) (j : ℕ) :
    g.shiftedPathLossTops tops slope precision cutoff σ top j ⊆
      g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
        (g.index (ShiftedBlocks.endpoint σ j) (slope top)) := by
  unfold shiftedPathLossTops
  split_ifs
  · exact Finset.sdiff_subset
  · exact Finset.Subset.refl _

theorem shiftedPathMass_difference {ι X : Type*} {K : ℕ} (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hK : 0 < K) (σ : Fin K)
    (top : ι) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j)) (x : X) :
    g.shiftedPathMass tops slope precision cutoff weight σ top x j-
        g.shiftedPathMass tops slope precision cutoff weight σ top x (j+1) =
      ∑ t ∈ g.shiftedPathLossTops tops slope precision cutoff σ top j, weight t x := by
  rw [shiftedPathMass,ite_eq_left he]
  unfold shiftedPathLossTops
  split_ifs with hn
  · rw [shiftedPathMass,ite_eq_left hn]
    exact sub_eq_iff_eq_add.mpr (Finset.sum_sdiff (f := fun t => weight t x)
      (g.cellTops_subset_ancestor tops slope precision cutoff hp
        ((ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)) (slope top))).symm
  · rw [shiftedPathMass,ite_eq_right hn,sub_zero]
    rfl

/-- Parent mass and absolute loss have the same relative motion bound:
each is a positive sum over a subset of the parent tops. -/
theorem source_shifted_absolute_motion {ι : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (ShiftedBlocks.endpoint σ j))
    (sR : ℝ) (hs : g.index (ShiftedBlocks.endpoint σ j) (T top).slope =
      g.index (ShiftedBlocks.endpoint σ j) sR)
    (hblock : g.width (ShiftedBlocks.endpoint σ j) ≤ B*g.width (ShiftedBlocks.endpoint σ (j+1)))
    (b : ℝ) (hb : |b| ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)))
    (z : ℝ × ℝ) :
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) (fun t x => (T t).weight Kw D x) σ top x
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    |n (SlopeBox.lineShift sR b z) j-n z j| ≤ Real.exp δ*δ*n z j ∧
      |(n (SlopeBox.lineShift sR b z) j-n (SlopeBox.lineShift sR b z) (j+1))-
        (n z j-n z (j+1))| ≤ Real.exp δ*δ*(n z j-n z (j+1)) := by
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cut := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let lo := ShiftedBlocks.endpoint σ j
  let hi := ShiftedBlocks.endpoint σ (j+1)
  let parent := g.cellTops tops slope precision cut lo (g.index lo (slope top))
  let loss := g.shiftedPathLossTops tops slope precision cut σ top j
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hparent := g.parent_subset_boundary tops slope precision cut 0 lo 0 (slope top)
  have hm (A : Finset ι) (hA : A ⊆ parent) :=
    g.source_submass_relative_motion tops T w B Kw D hw hB hKw hD hwidth
      0 lo lo le_rfl 0 (by norm_num) (g.width_pos lo).le (slope top) sR hs
      (g.width hi) (g.width_pos hi) hblock A (hA.trans hparent) b hb z
  have hn (x : ℝ × ℝ) :
      g.shiftedPathMass tops slope precision cut weight σ top x j = ∑ t ∈ parent, weight t x := by
    rw [shiftedPathMass,ite_eq_left he]
    rfl
  have hl (x : ℝ × ℝ) :=
    g.shiftedPathMass_difference tops slope precision cut weight hp hK σ top j he x
  change |g.shiftedPathMass tops slope precision cut weight σ top (SlopeBox.lineShift sR b z) j-
    g.shiftedPathMass tops slope precision cut weight σ top z j| ≤
      (Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*((5*D/Kw)/Real.sqrt (g.branching:ℝ)))*
        g.shiftedPathMass tops slope precision cut weight σ top z j ∧
    |(g.shiftedPathMass tops slope precision cut weight σ top (SlopeBox.lineShift sR b z) j-
      g.shiftedPathMass tops slope precision cut weight σ top (SlopeBox.lineShift sR b z) (j+1))-
      (g.shiftedPathMass tops slope precision cut weight σ top z j-
        g.shiftedPathMass tops slope precision cut weight σ top z (j+1))| ≤
      (Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*((5*D/Kw)/Real.sqrt (g.branching:ℝ)))*
        (g.shiftedPathMass tops slope precision cut weight σ top z j-
          g.shiftedPathMass tops slope precision cut weight σ top z (j+1))
  constructor
  · simpa only [hn] using hm parent (Finset.Subset.refl _)
  · simpa only [hl] using hm loss (g.shiftedPathLossTops_subset tops slope precision cut σ top j)

/-- Every pair of physical points in one reference cell has the above
motion bound. This is uniform over cells and their position on the line. -/
theorem source_shifted_line_cell_motion {ι : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (ShiftedBlocks.endpoint σ j))
    (sR y : ℝ) (hs : g.index (ShiftedBlocks.endpoint σ j) (T top).slope =
      g.index (ShiftedBlocks.endpoint σ j) sR)
    (hblock : g.width (ShiftedBlocks.endpoint σ j) ≤ B*g.width (ShiftedBlocks.endpoint σ (j+1)))
    (grid : FiniteLineGrid)
    (hgrid : grid.width ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)))
    (x z : ℝ) (hx : x ∈ grid.root) (hz : z ∈ grid.root) :
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) (fun t x => (T t).weight Kw D x)
      σ top (x,y+sR*x)
    let q := Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
      ((5*D/Kw)/Real.sqrt (g.branching:ℝ))
    n x j ≤ (1+q)*n z j ∧
      n x j-n x (j+1) ≤ (1+q)*(n z j-n z (j+1)) := by
  have hb := (grid.snapshot_displacement_le_width hz hx).trans hgrid
  have hm := g.source_shifted_absolute_motion tops T w B Kw D hw hB hKw hD hwidth
    hK σ j top he sR hs hblock (x-z) hb (z,y+sR*z)
  rw [lineShift_snapshot] at hm
  dsimp only
  constructor
  · have h := (abs_le.mp hm.1).2
    linarith
  · have h := (abs_le.mp hm.2).2
    linarith

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalCellMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source marking dichotomy for actual top weights on an arbitrary
reference-line cell of the prescribed block length. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LipschitzHilbert.AngularGrid

theorem eventually_source_physical_cell_marking (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ), 0 < w → 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (_hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (j : ℕ) (top : ι),
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length)
        (ShiftedBlocks.endpoint σ j) →
    ∀ (y : ℝ) (grid : FiniteLineGrid),
      grid.width ≤ sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) →
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2)
      (fun t z => (T t).weight Kw D z) σ top (x,y+(T top).slope*x)
    let mark := sourceMarkedCell grid.root (fun x => n x j)
      (fun x => n x j-n x (j+1)) (L^A_M)
    ∀ x ∈ grid.root,
      (mark → L^A_M < n x j ∧ (1/4:ℝ) ≤ n x j-n x (j+1)) ∧
      (¬mark → 1 ≤ n x j-n x (j+1) → n x j < L^A_M+1 ∧ n x (j+1) < L^A_M) := by
  filter_upwards [eventually_source_marking_parameters_uniform D A_M hD hAM]
    with L hnumeric
  intro ι g tops T w Kw hw hKw hbranch hwidth hK σ j top he y grid hgrid
  dsimp only
  intro x hx
  let q := Real.exp ((5*D/Kw)/Real.sqrt (SourceParameters.step L))*
    ((5*D/Kw)/Real.sqrt (SourceParameters.step L))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hnum := hnumeric Kw hKw
  apply source_cell_marking_cases grid.root
    (fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2)
      (fun t z => (T t).weight Kw D z) σ top (x,y+(T top).slope*x) j)
    (fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2)
      (fun t z => (T t).weight Kw D z) σ top (x,y+(T top).slope*x) (j+1))
    (L^A_M) q
  · intro z _
    exact g.shiftedPathMass_nonneg tops _ _ _ _
      (fun t z => ((T t).weight_pos (zero_lt_one.trans_le hKw) D z).le) σ top _ j
  · exact hq0
  · exact hnum.1.trans (by norm_num)
  · exact hnum.2
  · intro a ha b hb
    have hB : 1 ≤ SourceParameters.branching L :=
      one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    have hg : grid.width ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*
        Real.sqrt (g.branching:ℝ)) := by
      simpa only [sourceLineScale,hbranch,Real.sqrt_eq_rpow] using hgrid
    have hm := g.source_shifted_line_cell_motion tops T w (SourceParameters.branching L)
      Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hK σ j top he
      (T top).slope y rfl (g.source_shifted_width_bounds L hbranch hK σ j).2
      grid hg a b ha hb
    simpa only [hbranch] using hm
  · exact hx

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceReverseCellMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal source marking rule on every nested reverse-grid cell.
Eligibility is derived from the actual first terminal block. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LipschitzHilbert.AngularGrid

theorem eventually_source_reverse_cell_marking (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ) (hw : 0 < w), 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (top : ι) (origin y : ℝ),
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
      (div_pos hw (T top).length_pos) hK σ
    let grid := sourceReverseLineGrid g L origin hw σ count
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
      σ top (x,y+(T top).slope*x)
    ∀ j < count, ∀ i : ℕ,
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    let mark := sourceMarkedCell (grid.cell coarse i) (fun x => n x j)
      (fun x => n x j-n x (j+1)) (L^A_M)
    ∀ x ∈ grid.cell coarse i,
      (mark → L^A_M < n x j ∧ (1/4:ℝ) ≤ n x j-n x (j+1)) ∧
      (¬mark → 1 ≤ n x j-n x (j+1) → n x j < L^A_M+1 ∧ n x (j+1) < L^A_M) := by
  filter_upwards [eventually_source_physical_cell_marking D A_M hD hAM]
    with L hmark
  intro ι g tops T w Kw hw hKw hbranch hwidth hK σ top origin y
  dsimp only
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ
  let grid := sourceReverseLineGrid g L origin hw σ count
  intro j hj i x hx
  let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
  let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
  have he := g.eligible_before_firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ hj
  have hwgrid : (grid.lineWindow coarse i (fine-coarse)).width ≤
      sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) :=
    (source_reverse_local_mesh g L origin hw σ hK hj hbranch i).1.le
  have hxgrid : x ∈ (grid.lineWindow coarse i (fine-coarse)).root := by
    rwa [FiniteLineGrid.lineWindow_root]
  have hm := hmark ι g tops T w Kw hw hKw hbranch hwidth hK σ j top he y
    (grid.lineWindow coarse i (fine-coarse)) hwgrid x hxgrid
  simpa only [FiniteLineGrid.lineWindow_root] using hm

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceLabeledPacketRestriction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Any fixed residual packet subset is itself a lattice family, with
unchanged geometry, analyzing integrals and alternate synthesis waves.
Restricting the item fibers preserves the lattice constants exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- Exact scalar/vector sums over the selected packet family. -/
theorem sum_restrictPackets {E : Type*} [AddCommMonoid E] (Q : Finset P.PacketIndex)
    (f : P.PacketIndex → E) :
    (∑ q : (P.restrictPackets Q).PacketIndex, f ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩) =
      ∑ q ∈ Q, f q := by
  have h := Equiv.sum_comp (P.restrictedPacketEquiv Q) (fun q : Q => f q.val)
  exact h.trans (Finset.sum_subtype Q (p := fun q => q ∈ Q) (by simp) f).symm

theorem sum_restrictPackets_filter {E : Type*} [AddCommMonoid E] (Q : Finset P.PacketIndex)
    (f : P.PacketIndex → E) (keep : P.PacketIndex → Prop) :
    (∑ q ∈ Finset.univ.filter (fun q : (P.restrictPackets Q).PacketIndex =>
      keep ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩), f ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩) =
      ∑ q ∈ Q.filter keep, f q := by
  simp only [Finset.sum_filter]
  exact P.sum_restrictPackets Q (fun q => if keep q then f q else 0)

variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)

theorem restrictPackets_physicalMaskedValue (Q : Finset P.PacketIndex)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (q : (P.restrictPackets Q).PacketIndex) :
    (P.restrictPackets Q).physicalMaskedValue (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val) L A z q =
      P.physicalMaskedValue alt hAlt t b v g T L A z ⟨q.1,⟨q.2.1,q.2.2.val⟩⟩ := rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceConditions
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frozen main coefficients vanish outside the fixed selector cone.
Restricting the main reference family to that cone is an exact identity;
its carrier bound therefore does not inherit the wide error cone. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

/-- A finite source sum supported on the reference labels equals the
sum in the literal restricted family. -/
theorem sum_referenceLabels_of_zero {E : Type*} [AddCommMonoid E]
    (oldSlope newSlope referenceLength cone w : ℝ) (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l →
      ∀ u, f l u = 0) :
    (∑ l : P.referenceLabels oldSlope newSlope referenceLength cone w j,
      ∑ u : Item j l, f (P.referenceOriginalLabel oldSlope newSlope referenceLength cone w j l) u) =
      ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have hrestrict := Equiv.sum_comp (P.referenceLabelsEquiv oldSlope newSlope referenceLength cone w j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j //
      ¬P.referenceCondition oldSlope newSlope referenceLength cone w j l},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    exact Finset.sum_eq_zero (fun u _ => hzero l.val l.property u)
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (P.referenceCondition oldSlope newSlope referenceLength cone w j)
    (fun l : P.labels j => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact hrestrict.trans hsum

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceProperties
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The physical selector centers are invariant under recentering.
Restricting to the reference cone can only decrease their local count. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l)) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u :=
  P.referenceFamily_multiplier_coefficient oldSlope newSlope R cone w F hw hcone hF hwide hfrequency b v f j l u

theorem referenceFamily_alternate_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) :
    ((Q).withProfile (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))).physicalPacket
      newSlope j l u k = (P.withProfile alt hAlt).physicalPacket oldSlope j (orig j l) u k :=
  (P.withProfile alt hAlt).referenceFamily_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l u k

/-- A selected set supported in the reference cone has the identical
sum after the literal label restriction, including empty item fibers. -/
theorem sum_referenceFamily_selected {E : Type*} [AddCommMonoid E]
    (S : Finset P.PacketIndex) (f : P.PacketIndex → E)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    (∑ u ∈ (Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S),
      f ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) = ∑ u ∈ S, f u := by
  have hs : (Finset.univ.filter fun u : P.PacketIndex => u ∈ S) = S := by
    ext u
    simp
  conv_rhs => rw [← hs,Finset.sum_filter]
  simp only [Finset.sum_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact P.sum_referenceLabels_of_zero oldSlope newSlope R cone w j
    (fun l u => if (⟨j,⟨l,u⟩⟩ : P.PacketIndex) ∈ S then f ⟨j,⟨l,u⟩⟩ else 0)
    (by
      intro l hl u
      rw [ite_eq_right]
      exact fun hu => hl (hS ⟨j,⟨l,u⟩⟩ hu))

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceMasked
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact masked amplitudes and residuals survive the local reference change. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0<w) (hcone : 0 ≤ cone) (hF : 0≤F)
  (hwide : cone*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physicalMaskedValue
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (u : (Q).PacketIndex) :
    (Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l)) L A z u =
    P.physicalMaskedValue alt hAlt oldSlope b v f T L A z ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ := by
  ext k
  simp only [physicalMaskedValue,SourceLabeledLattice.physicalMaskedValue,WithLp.ofLp_toLp]
  rw [P.referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]
  rw [P.referenceFamily_alternate_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledGoodEvents
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype _root_.OAI.LipschitzHilbert.SourceLabeledLattice.restrictedPacketItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable reference events for the original error, positive main
square and full masked variation. All three thresholds are fixed before
the angular path or mass cutoff is selected. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A e s r : ℝ)

theorem physicalReferenceBad_compl_bounds (z : ℝ×ℝ)
    (hz : z ∉ P.physicalReferenceBad alt hAlt t a b v g T L A e s r) :
    P.physicalAngularError t a b v g z < L^e ∧
    P.physicalMainSquareOnPlane t a b v g z < L^s ∧
    P.physicalMaskedVariation alt hAlt t b v g T L A (z.2-t*z.1) z.1 < L^r := by
  have h (i : Fin 3) : z ∉ P.physicalReferenceEvent alt hAlt t a b v g T L A e s r i :=
    fun hi => hz (mem_iUnion.mpr ⟨i,hi⟩)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [physicalReferenceEvent,ite_true, if_true,Set.mem_ofPred_eq] at h0
  simp only [physicalReferenceEvent,show (1 : Fin 3) ≠ 0 by decide,ite_false, if_false,ite_true, if_true,
    Set.mem_ofPred_eq] at h1
  simp only [physicalReferenceEvent,show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide,ite_false, if_false,Set.mem_ofPred_eq] at h2
  exact ⟨lt_of_not_ge h0,lt_of_not_ge h1,lt_of_not_ge h2⟩

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_ResidualBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Final source-parameter budgets for the marked and unary residual costs. -/

noncomputable section

open Filter
open scoped Topology

namespace LipschitzHilbert

/-- The mass cutoff is chosen after the fixed polynomial losses. Both
residual exponents in §10 are at most `-1/4`. -/
theorem residual_polynomial_budget {L A C μ : ℝ}
    (hL : 1 ≤ L) (hμ : μ ≤ 1 / 12) (hA : 0 ≤ A)
    (hchoice : 4 * (C + 1 / 2) ≤ A) :
    L ^ (1 / 2 : ℝ) * L ^ C * (L ^ A) ^ (-(1 / 3 : ℝ) + μ) ≤ 1 ∧
      L ^ (1 / 2 : ℝ) * L ^ C * (L ^ A) ^ (-(1 / 2 : ℝ) + μ) ≤ 1 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hM : 1 ≤ L ^ A := Real.one_le_rpow hL hA
  have hbase : L ^ (1 / 2 : ℝ) * L ^ C * (L ^ A) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
    rw [← Real.rpow_add hL0, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  constructor
  · apply le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hM (by linarith : -(1 / 3 : ℝ) + μ ≤ -(1 / 4 : ℝ)))
      (by positivity)) hbase
  · apply le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hM (by linarith : -(1 / 2 : ℝ) + μ ≤ -(1 / 4 : ℝ)))
      (by positivity)) hbase

/-- The discarded-top error stays negligible after the source's
`exp(C sqrt L)` mass bound and any fixed polynomial loss. -/
theorem eventually_discarded_residual_small (p C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (-L) * Real.exp (C * Real.sqrt L) * L ^ p ≤ 1 := by
  have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (1 / 2)
    (by norm_num)
  filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop (4 * C ^ 2),
    hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with L hL hlarge hsmall
  have hsq := Real.sq_sqrt hL
  have hr := Real.sqrt_nonneg L
  have hroot : 2 * C ≤ Real.sqrt L := by nlinarith
  have hlinear : C * Real.sqrt L ≤ L / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hr]
  calc
    _ = L ^ p * Real.exp (-L + C * Real.sqrt L) := by rw [Real.exp_add]; ring
    _ ≤ L ^ p * Real.exp (-(1 / 2 : ℝ) * L) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
        (Real.rpow_nonneg hL _)
    _ ≤ 1 := hsmall.le

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualWeightBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The common residual coefficient bound is polynomial in the source
parameter. Its exponent is fixed before selecting the mass cutoff. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_source_residual_weight_budget (Cmass : ℝ) (hCmass : 0 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop, ∀ (a Z Nmass nroot : ℝ) (K : ℕ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (K:ℝ) ≤ L^2 →
      0 < Nmass → Real.log Nmass ≤ 2*L → 1 ≤ nroot → nroot ≤ L^Cmass*Nmass →
      1+(a+Z*K)*Real.log nroot ≤ L^6 := by
  filter_upwards [eventually_ge_atTop (max 1 (3*(Cmass+2)+1))] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hlarge : 3*(Cmass+2)+1 ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := zero_lt_one.trans_le hL1
  intro a Z Nmass nroot K _ha0 ha1 hZ0 hZ hK hN hlogN hn1 hn
  have hn0 : 0 < nroot := zero_lt_one.trans_le hn1
  have hlogpos : 0 ≤ Real.log nroot := Real.log_nonneg hn1
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  have hlog : Real.log nroot ≤ (Cmass+2)*L := by
    calc
      _ ≤ Real.log (L^Cmass*Nmass) := Real.log_le_log hn0 hn
      _ = Cmass*Real.log L+Real.log Nmass := by
        rw [Real.log_mul (Real.rpow_pos_of_pos hLpos _).ne' hN.ne',Real.log_rpow hLpos]
      _ ≤ Cmass*L+2*L := add_le_add (mul_le_mul_of_nonneg_left hlogL hCmass) hlogN
      _ = _ := by ring
  have hpow4 : 1 ≤ L^4 := one_le_pow₀ hL1
  have hZK : Z*K ≤ 2*L^4 := by
    calc
      _ ≤ (2*L^2)*L^2 := mul_le_mul hZ hK (Nat.cast_nonneg K) (by positivity)
      _ = _ := by ring
  have hc : a+Z*K ≤ 3*L^4 := by linarith
  have hmain : (a+Z*K)*Real.log nroot ≤ (3*L^4)*((Cmass+2)*L) :=
    mul_le_mul hc hlog hlogpos (by positivity)
  have hpow5 : 1 ≤ L^5 := one_le_pow₀ hL1
  calc
    _ ≤ 1+(3*L^4)*((Cmass+2)*L) := add_le_add le_rfl hmain
    _ = 1+(3*(Cmass+2))*L^5 := by ring
    _ ≤ (1+3*(Cmass+2))*L^5 := by nlinarith
    _ ≤ L*L^5 := mul_le_mul_of_nonneg_right (by linarith : 1+3*(Cmass+2) ≤ L)
      (by positivity)
    _ = L^6 := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePropagatedTailBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual propagated residual tail has one fixed polynomial loss.
This estimate uses the full-root mass bound, including for later starts. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

theorem intervalOscillation_le_of_subinterval {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (H a b c d : ℕ) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hb : b ≤ H) : intervalOscillation F H c d ≤ intervalOscillation F H a b := by
  obtain ⟨u,v,hcu,huv,hvd,heq⟩ := exists_intervalOscillation_eq F H c d hcd
  rw [heq]
  exact increment_le_intervalOscillation F H a b u v (hac.trans hcu) huv (hvd.trans hdb) hb

namespace AngularGrid

theorem eventually_source_propagated_tail_bound (Cmass : ℝ) (hCmass : 0 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ σ X E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ), (∀ t ∈ tops, 0 ≤ precision t) → (∀ t x, 0 < weight t x) →
    ∀ (K : ℕ), 0 < K → (K:ℝ) ≤ L^2 →
    ∀ (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : σ → E) (phase : ℕ → ℂ) (a Z Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (x : X) (level : ℕ → ℕ), StrictMono level →
    ∀ (count : ℕ) (top : τ), top ∈ tops →
    ∀ (e f H : ℕ), e < f → f ≤ count → level f ≤ H →
      g.eligible cutoff (precision top) (level f) →
      1 ≤ g.mass tops slope precision cutoff weight (level f) (g.index (level f) (slope top)) x →
      g.mass tops slope precision cutoff weight 0 (g.index 0 (slope top)) x ≤ L^Cmass*Nmass →
      (∀ k < level f, 0 ≤ (phase k).re) → (∀ k < level f, ‖phase k‖ ≤ Z) →
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x
    let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope top)
    let raw := fun k => ∑ q ∈ Q.filter (fun q => stop q = k), value q
    ∀ j ∈ Finset.Icc e f,
      ‖∑ k ∈ Finset.Ico j f,
        unaryPropagator (fun b => g.packetPathProduct transition (level b) (level (b+1)) (slope top)) j k •
          g.packetResidual (g.sourceContinuingPackets tops slope precision cutoff packets assigned
            (level (k+1)) (slope top)) (fun q => slope (assigned q)) stop base transition
            (level k) (level (k+1)) (g.index (level k) (slope top))‖ ≤
        L^6*intervalOscillation (packetPrefix raw) H (level e) (level f) := by
  filter_upwards [eventually_source_residual_weight_budget Cmass hCmass] with L hbudget
  intro τ σ X E _ _ g tops slope precision cutoff weight hp hw K hK hKL gap packets
    assigned stop value phase a Z Nmass ha0 ha1 hZ0 hZ hN hlogN x level hlevel count top
    htop e f H hef hfc hH he hnend hnroot hz0 hz
  dsimp only
  intro j hj
  have hji := Finset.mem_Icc.mp hj
  let Q := g.fixedPathResidualPackets tops slope precision cutoff packets assigned stop level count (slope top)
  let raw := fun k => ∑ q ∈ Q.filter (fun q => stop q = k), value q
  have hnonneg : 0 ≤ L^6*intervalOscillation (packetPrefix raw) H (level e) (level f) :=
    mul_nonneg (by positivity) (intervalOscillation_nonneg ..)
  by_cases hjf : j = f
  · subst j
    simpa only [Finset.Ico_self,Finset.sum_empty,norm_zero] using hnonneg
  · have hjlt : j < f := lt_of_le_of_ne hji.2 hjf
    have hb := g.source_propagated_residual_bound tops slope precision cutoff weight hp hw hK gap
      packets assigned stop value phase a x level hlevel count top htop hjlt hfc he H hH
      ha0 (by norm_num : (0:ℝ)<1) hZ0 hnend hz0 hz
    have hn0 : 1 ≤ g.mass tops slope precision cutoff weight 0 (g.index 0 (slope top)) x :=
      hnend.trans (g.path_mass_antitone tops slope precision cutoff weight hp
        (fun t x => (hw t x).le) top x (Nat.zero_le _))
    have hnum := hbudget a Z Nmass
      (g.mass tops slope precision cutoff weight 0 (g.index 0 (slope top)) x) K
      ha0 ha1 hZ0 hZ hKL hN hlogN hn0 hnroot
    simp only [Real.one_rpow,one_mul,div_one] at hb
    apply hb.trans
    apply mul_le_mul hnum
      (intervalOscillation_le_of_subinterval (packetPrefix raw) H (level e) (level f)
        (level j) (level f) (hlevel.monotone hji.1) (hlevel.monotone hji.2) le_rfl hH)
      (intervalOscillation_nonneg ..) (by positivity)

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPhysicalPropagatedTail
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagated residuals for the original masked physical packets use
exactly the fixed-subset prefix controlled by the reference event. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData

/-- The path's propagated unary residuals are controlled by the original
physical prefix of its one deterministic residual subset. -/
theorem eventually_selected_physical_propagated_tail_bound
    (Cmass : ℝ) (hCmass : 0 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (v : ℝ×ℝ → ℝ) (test : ℝ×ℝ → EuclideanSpace ℂ κ)
      (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (A : ℝ)
      (τ : Type*) (grid : AngularGrid) (tops : Finset τ)
      (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → ℝ×ℝ → ℝ),
      (∀ top ∈ tops, 0 ≤ precision top) → (∀ top z, 0 < weight top z) →
    ∀ (K : ℕ), 0 < K → (K:ℝ) ≤ L^2 →
    ∀ (gap : ℕ → ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (stop : Fin N → ℕ) (phase : ℕ → ℂ) (a Z Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (z : ℝ×ℝ) (level : ℕ → ℕ), StrictMono level →
    ∀ (count : ℕ) (top : τ), top ∈ tops →
    ∀ (e f H : ℕ), e < f → f ≤ count → level f ≤ H →
      grid.eligible cutoff (precision top) (level f) →
      1 ≤ grid.mass tops slope precision cutoff weight (level f)
        (grid.index (level f) (slope top)) z →
      grid.mass tops slope precision cutoff weight 0 (grid.index 0 (slope top)) z ≤
        L^Cmass*Nmass →
      (∀ k < level f, 0 ≤ (phase k).re) → (∀ k < level f, ‖phase k‖ ≤ Z) →
    let value := P.physicalMaskedValue alt hAlt t b v test T L A z
    let transition := grid.sourceTransition tops slope precision cutoff weight K gap phase z
    let base := grid.sourcePacketBase tops slope precision cutoff weight assigned
      (fun q => stop q.1) value a z
    let Q := grid.fixedPathResidualPackets tops slope precision cutoff packets assigned
      (fun q => stop q.1) level count (slope top)
    ∀ j ∈ Finset.Icc e f,
      ‖∑ k ∈ Finset.Ico j f,
        unaryPropagator (fun k => grid.packetPathProduct transition
          (level k) (level (k+1)) (slope top)) j k •
          grid.packetResidual (grid.sourceContinuingPackets tops slope precision cutoff
            packets assigned (level (k+1)) (slope top))
            (fun q => slope (assigned q)) (fun q => stop q.1) base transition
            (level k) (level (k+1)) (grid.index (level k) (slope top))‖ ≤
        L^6*intervalOscillation
          (P.selectedPhysicalPrefix alt hAlt t b v test T L A Q stop z)
          H (level e) (level f) := by
  filter_upwards [AngularGrid.eventually_source_propagated_tail_bound Cmass hCmass] with L htail
  intro N κ Label Item _ _ P alt hAlt t b v test T A τ grid tops slope precision cutoff weight
    hp hw K hK hKL gap packets assigned stop phase a Z Nmass ha0 ha1 hZ0 hZ hN hlogN
    z level hlevel count top htop e finish H hef hfc hH he hnend hnroot hz0 hz
  dsimp only
  simpa only [selectedPhysicalPrefix] using htail τ P.PacketIndex (ℝ×ℝ) (EuclideanSpace ℂ κ)
    grid tops slope precision cutoff weight hp hw K hK hKL gap packets assigned
    (fun q => stop q.1) (P.physicalMaskedValue alt hAlt t b v test T L A z)
    phase a Z Nmass ha0 ha1 hZ0 hZ hN hlogN z level hlevel count top htop
    e finish H hef hfc hH he hnend hnroot hz0 hz

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceLabeledSelectedVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact stopping prefixes for the fixed residual subset. The variation
is that of its literal restricted physical family; subset selection causes
no additional factor in any profile or geometric constant. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

theorem selectedPhysicalPrefix_eq_restricted (Q : Finset P.PacketIndex)
    (stop : Fin N → ℕ) (z : ℝ×ℝ) :
    P.selectedPhysicalPrefix alt hAlt t b v g T L A Q stop z =
      (P.restrictPackets Q).physicalStoppingPrefix (P.restrictedAlternate alt Q)
        (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val)
        L A stop z := by
  unfold selectedPhysicalPrefix physicalStoppingPrefix
  congr 1
  funext k
  symm
  simp_rw [P.restrictPackets_physicalMaskedValue alt hAlt Q]
  ext i
  simp only [WithLp.ofLp_sum,Finset.sum_apply]
  convert P.sum_restrictPackets_filter Q
    (fun q => P.physicalMaskedValue alt hAlt t b v g T L A z q i)
    (fun q => stop q.1 = k) using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> ext q <;> simp)

/-- The original fixed residual subset has the required clamped prefix
bound on its own reference event, for every angular horizon. -/
theorem selectedPhysicalPrefix_good_bound (Q : Finset P.PacketIndex)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (y x : ℝ) (H : ℕ) {V : ℝ}
    (hV : (P.restrictPackets Q).physicalMaskedVariation (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val)
      L A y x ≤ V) :
    finiteCubicVariation (fun k =>
      P.selectedPhysicalPrefix alt hAlt t b v g T L A Q stop (x,y+t*x) (min k H)) (2*H) ≤ V^3 := by
  rw [P.selectedPhysicalPrefix_eq_restricted alt hAlt t b v g T L A Q stop]
  exact (P.restrictPackets Q).physicalStoppingPrefix_good_bound (P.restrictedAlternate alt Q)
    (P.restrictedAlternate_bound alt hAlt Q) t b v g (fun j l u => T j l u.val)
    L A stop hstop y x H hV

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStoppedAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The amplitude on a distinguished top path stops when that top becomes
ineligible. Other surviving children remain in the original denominator. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem sourceNodeDenominator_ge_mass {ι κ : Type} [Fintype ι] [Fintype κ]
    (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ)
    (hc : ∀ i, 0 ≤ c i) : n ≤ sourceNodeDenominator n c A α p := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hc i) _)
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem sourceNodeDenominator_ge_child {ι κ : Type} [Fintype ι] [Fintype κ]
    (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ)
    (hc : ∀ i, 0 ≤ c i) (i : ι) :
    n-c i+vertexAmount (c i) (A i) α p ≤ sourceNodeDenominator n c A α p := by
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun k => (c k)^(α-p)*‖A k‖^p)
    (fun k _ => mul_nonneg (Real.rpow_nonneg (hc k) _)
      (Real.rpow_nonneg (norm_nonneg _) _)) (Finset.mem_univ i)
  dsimp only [vertexAmount,sourceNodeDenominator]
  linarith

namespace AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

theorem source_shifted_ratio_eq_amount_div_denominator {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → τ) (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (tag : Fin Kb) (top : τ) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j)) :
    g.sourceShiftedPathRatio tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p tag top x j =
    vertexAmount (g.shiftedPathMass tops slope precision cutoff weight tag top x j)
      (g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap packets assigned stop
        value phase a tag top x j) α p /
      g.sourceShiftedPathDenominator tops slope precision cutoff weight K gap packets assigned stop
        value phase a α p tag top x j := by
  simp only [sourceShiftedPathRatio,sourceBlockNodeRatio,sourceNodeRatio,shiftedPathMass,
    sourceShiftedPathAmplitude,ite_eq_left he,sourceShiftedPathDenominator]

theorem source_active_path_eq_stopped_product {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hprecision : ∀ t ∈ tops, 0 ≤ precision t) (hweight : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ) (phase : ℕ → ℂ)
    (a α p M : ℝ) (hM : 0 ≤ M) (hKb : 0 < Kb) (tag : Fin Kb)
    (top : τ) (htop : top ∈ tops) (count : ℕ)
    (hterminal : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag count)) (x : X) :
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a α p M tag top count x =
    ∏ j ∈ Finset.range
      (firstMassStop (g.shiftedPathMass tops slope precision cutoff weight tag top x) count M),
      g.sourceShiftedPathRatio tops slope precision cutoff weight K gap packets assigned stop value
        phase a α p tag top x j := by
  apply sourceActiveProduct_eq_stopped_product
  · rw [g.shiftedPathMass_terminal_zero tops slope precision cutoff weight tag top count hterminal]
    exact hM
  · exact g.shiftedPathMass_antitone tops slope precision cutoff weight hprecision hweight
      hKb tag top htop x

/-- The true denominator controls the next distinguished path node, even
when the path terminates while other children survive. -/
theorem source_shifted_path_denominator_ge_next {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hprecision : ∀ t ∈ tops, 0 ≤ precision t) (hweight : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p : ℝ) (hp : 0 < p) (hKb : 0 < Kb)
    (tag : Fin Kb) (top : τ) (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j)) :
    let n := g.shiftedPathMass tops slope precision cutoff weight tag top x
    let A := g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a tag top x
    n j-n (j+1)+vertexAmount (n (j+1)) (A (j+1)) α p ≤
      g.sourceShiftedPathDenominator tops slope precision cutoff weight K gap packets
        assigned stop value phase a α p tag top x j := by
  dsimp only
  let lower := ShiftedBlocks.endpoint tag j
  let upper := ShiftedBlocks.endpoint tag (j+1)
  let parent := g.index lower (slope top)
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have hn := g.mass_nonnegative tops slope precision cutoff weight hweight
  by_cases hnext : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag (j+1))
  · have hi : g.index upper (slope top) ∈ cells := g.mem_sourceBlockCells_of_top tops
      slope precision cutoff lower upper parent hprecision
      ((ShiftedBlocks.endpoint_strictMono hKb tag).monotone (Nat.le_succ j)) top htop rfl hnext
    have h := sourceNodeDenominator_ge_child
      (g.mass tops slope precision cutoff weight lower parent x)
      (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
      (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x upper i.val) α p (fun i => hn _ _ x)
      ⟨g.index upper (slope top),hi⟩
    simpa only [shiftedPathMass,sourceShiftedPathAmplitude,ite_eq_left he,
      ite_eq_left hnext,sourceShiftedPathDenominator] using h
  · have h := sourceNodeDenominator_ge_mass
      (g.mass tops slope precision cutoff weight lower parent x)
      (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
      (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x upper i.val) α p (fun i => hn _ _ x)
    simpa only [shiftedPathMass,sourceShiftedPathAmplitude,ite_eq_left he,
      ite_eq_right hnext,sourceShiftedPathDenominator,sub_zero,vertexAmount,norm_zero,
      Real.zero_rpow (ne_of_gt hp),mul_zero,add_zero] using h

end AngularGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStoppedRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source residual identities on the actual mass-stopped path.
A unary step cannot terminate the distinguished top while its mass is active. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

theorem shiftedPathMass_ne_zero_eligible {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (tag : Fin Kb) (top : τ) (x : X) (j : ℕ)
    (hn : g.shiftedPathMass tops slope precision cutoff weight tag top x j ≠ 0) :
    g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j) := by
  by_contra he
  exact hn (by simp only [shiftedPathMass,ite_eq_right he])

theorem source_unary_next_eligible {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (tag : Fin Kb) (top : τ) (x : X) (j : ℕ) {M : ℝ} (hM : 1 ≤ M)
    (hactive : M < g.shiftedPathMass tops slope precision cutoff weight tag top x j)
    (hdrop : g.shiftedPathMass tops slope precision cutoff weight tag top x j-
      g.shiftedPathMass tops slope precision cutoff weight tag top x (j+1) < 1) :
    g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag (j+1)) := by
  apply g.shiftedPathMass_ne_zero_eligible tops slope precision cutoff weight tag top x
  have hpos : 0 < g.shiftedPathMass tops slope precision cutoff weight tag top x (j+1) := by
    linarith
  exact hpos.ne'

theorem source_stopped_unary_recurrence {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hprecision : ∀ t ∈ tops, 0 ≤ precision t) (hweight : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → τ) (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a : ℝ) (hphase : ∀ k, 0 ≤ (phase k).re)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (heligible : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop q))
    (hKb : 0 < Kb) (tag : Fin Kb) (top : τ) (htop : top ∈ tops)
    (x : X) (j : ℕ) {M : ℝ} (hM : 1 ≤ M)
    (hactive : M < g.shiftedPathMass tops slope precision cutoff weight tag top x j)
    (hdrop : g.shiftedPathMass tops slope precision cutoff weight tag top x j-
      g.shiftedPathMass tops slope precision cutoff weight tag top x (j+1) < 1) :
    let lower := ShiftedBlocks.endpoint tag j
    let upper := ShiftedBlocks.endpoint tag (j+1)
    let A := g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a tag top x
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let keep := fun q => assigned q ∈ g.cellTops tops slope precision cutoff upper
      (g.index upper (slope top))
    let lam := g.packetPathProduct transition lower upper (slope top)
    ‖lam‖ ≤ 1 ∧ A j = lam • A (j+1)+
      g.packetResidual (packets.filter keep) (fun q => slope (assigned q)) stop base transition
        lower upper (g.index lower (slope top))+
      g.packetAmplitude (packets.filter fun q => ¬keep q) (fun q => slope (assigned q)) stop base
        transition lower (g.index lower (slope top)) := by
  dsimp only
  have hnext := g.source_unary_next_eligible tops slope precision cutoff weight tag top x j
    hM hactive hdrop
  have hlo := (ShiftedBlocks.endpoint_strictMono hKb tag).monotone (Nat.le_succ j)
  have he := g.eligible_of_le (hprecision top htop) hlo hnext
  refine ⟨g.source_path_product_norm_le_one tops slope precision cutoff weight hprecision
    hweight hK gap phase x _ _ top htop hnext (fun k _ => hphase k),?_⟩
  have hr := g.sourcePacketAmplitude_unary_recurrence tops slope precision cutoff weight
    hprecision K gap packets assigned stop (value x) phase a x hassigned heligible hlo (slope top)
  simpa only [sourceShiftedPathAmplitude,ite_eq_left he,ite_eq_left hnext] using hr

/-- Removing the actual block residual gives exactly the predictor used
in the physical marked integral, with the original child denominator. -/
theorem source_stopped_residual_free_ratio {Kb : ℕ} (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hprecision : ∀ t ∈ tops, 0 ≤ precision t) (hweight : ∀ t x, 0 < weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a α p μ : ℝ) (hrelation : p*μ = α-1)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (heligible : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop q))
    (hKb : 0 < Kb) (tag : Fin Kb) (top : τ) (htop : top ∈ tops) (x : X) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j)) :
    let residual := g.packetResidual packets (fun q => slope (assigned q)) stop
      (g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      (ShiftedBlocks.endpoint tag j) (ShiftedBlocks.endpoint tag (j+1))
      (g.index (ShiftedBlocks.endpoint tag j) (slope top))
    g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets assigned stop
      value phase a p μ tag top x j =
    vertexAmount (g.shiftedPathMass tops slope precision cutoff weight tag top x j)
      (g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap packets assigned stop
        value phase a tag top x j-residual) α p /
      g.sourceShiftedPathDenominator tops slope precision cutoff weight K gap packets assigned stop
        value phase a α p tag top x j := by
  have hparent : (g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint tag j)
      (g.index (ShiftedBlocks.endpoint tag j) (slope top))).Nonempty :=
    ⟨top,(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩⟩
  have hr := g.source_block_residual_free_ratio tops slope precision cutoff weight hprecision
    hweight K gap packets assigned stop (value x) phase a x hassigned heligible
    ((ShiftedBlocks.endpoint_strictMono hKb tag).monotone (Nat.le_succ j))
    (g.index (ShiftedBlocks.endpoint tag j) (slope top)) hparent μ α p hrelation
  simpa only [sourceShiftedPathPrediction,sourceBlockPrediction,shiftedPathMass,
    sourceShiftedPathAmplitude,ite_eq_left he,sourceShiftedPathDenominator,sourceNodeRatio] using hr

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePhysicalUnaryEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A low-drop unary segment on the active mass path ends strictly
before the terminal block and still has the positive mass required by
the physical propagated-residual estimate. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

theorem firstMassStop_unary_endpoint (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hM : 4 ≤ M) (hlast : n count = 0) {e f : ℕ}
    (hef : e < f) (hf : f ≤ firstMassStop n count M) (hdrop : n e-n f < 2) :
    f < count ∧ 1 ≤ n f := by
  have hlastM : n count ≤ M := by rw [hlast]; linarith
  have hs := firstMassStop_spec n count M hlastM
  have he : e < firstMassStop n count M := hef.trans_le hf
  have hactive := hs.2.2 e he
  have hn : 2 < n f := by linarith
  have hfc : f ≤ count := hf.trans hs.1
  have hne : f ≠ count := by intro h; rw [h,hlast] at hn; linarith
  exact ⟨lt_of_le_of_ne hfc hne,by linarith⟩

namespace AngularGrid

theorem source_stopped_unary_endpoint {τ X : Type*} {Kb : ℕ}
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (shift : Fin Kb) (top : τ) (x : X) (count : ℕ)
    (hterminal : ¬grid.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift count))
    (M : ℝ) (hM : 4 ≤ M) {e f : ℕ} (hef : e < f)
    (hf : f ≤ firstMassStop (grid.shiftedPathMass tops slope precision cutoff weight shift top x)
      count M)
    (hdrop : grid.shiftedPathMass tops slope precision cutoff weight shift top x e-
      grid.shiftedPathMass tops slope precision cutoff weight shift top x f < 2) :
    f ≤ count-1 ∧
      grid.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift f) ∧
      1 ≤ grid.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift f)
        (grid.index (ShiftedBlocks.endpoint shift f) (slope top)) x := by
  have h := firstMassStop_unary_endpoint
    (grid.shiftedPathMass tops slope precision cutoff weight shift top x) count M hM
    (grid.shiftedPathMass_terminal_zero tops slope precision cutoff weight shift top count hterminal x)
    hef hf hdrop
  have he := grid.shiftedPathMass_ne_zero_eligible tops slope precision cutoff weight shift top x f
    (ne_of_gt (lt_of_lt_of_le zero_lt_one h.2))
  refine ⟨by omega,he,?_⟩
  simpa only [shiftedPathMass,ite_eq_left he] using h.2

end AngularGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataPhysicalUnaryEndpoint
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
namespace PacketLatticeData

/-- The active-path conditions supply the endpoint eligibility and
positive mass in the actual propagated physical residual estimate. Its
fixed reference subset omits the one terminal block. -/
theorem eventually_selected_active_physical_unary_tail
    (Cmass : ℝ) (hCmass : 0 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (v : ℝ×ℝ → ℝ) (test : ℝ×ℝ → EuclideanSpace ℂ κ)
      (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (A : ℝ)
      (τ : Type*) (grid : AngularGrid) (tops : Finset τ)
      (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → ℝ×ℝ → ℝ),
      (∀ top ∈ tops, 0 ≤ precision top) → (∀ top z, 0 < weight top z) →
    ∀ (K : ℕ) (_hK : 0 < K), (K:ℝ) ≤ L^2 →
    ∀ (shift : Fin K) (gap : ℕ → ℝ) (packets : Finset P.PacketIndex)
      (assigned : P.PacketIndex → τ) (stop : Fin N → ℕ) (phase : ℕ → ℂ)
      (a Z Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (z : ℝ×ℝ) (count : ℕ) (top : τ), top ∈ tops →
      (¬grid.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift count)) →
    ∀ (M : ℝ), 4 ≤ M → ∀ (H : ℕ), ShiftedBlocks.endpoint shift count ≤ H →
      grid.mass tops slope precision cutoff weight 0 (grid.index 0 (slope top)) z ≤
        L^Cmass*Nmass →
      (∀ k < ShiftedBlocks.endpoint shift count, 0 ≤ (phase k).re) →
      (∀ k < ShiftedBlocks.endpoint shift count, ‖phase k‖ ≤ Z) →
    let n := grid.shiftedPathMass tops slope precision cutoff weight shift top z
    let level := ShiftedBlocks.endpoint shift
    let value := P.physicalMaskedValue alt hAlt t b v test T L A z
    let transition := grid.sourceTransition tops slope precision cutoff weight K gap phase z
    let base := grid.sourcePacketBase tops slope precision cutoff weight assigned
      (fun q => stop q.1) value a z
    let Q := grid.fixedPathResidualPackets tops slope precision cutoff packets assigned
      (fun q => stop q.1) level (count-1) (slope top)
    ∀ e f, e < f → f ≤ firstMassStop n count M → n e-n f < 2 →
    ∀ j ∈ Finset.Icc e f,
      ‖∑ k ∈ Finset.Ico j f,
        unaryPropagator (fun k => grid.packetPathProduct transition
          (level k) (level (k+1)) (slope top)) j k •
          grid.packetResidual (grid.sourceContinuingPackets tops slope precision cutoff
            packets assigned (level (k+1)) (slope top))
            (fun q => slope (assigned q)) (fun q => stop q.1) base transition
            (level k) (level (k+1)) (grid.index (level k) (slope top))‖ ≤
        L^6*intervalOscillation
          (P.selectedPhysicalPrefix alt hAlt t b v test T L A Q stop z)
          H (level e) (level f) := by
  filter_upwards [eventually_selected_physical_propagated_tail_bound Cmass hCmass]
    with L htail
  intro N κ Label Item _ _ P alt hAlt t b v test T A τ grid tops slope precision cutoff weight
    hp hw K hK hKL shift gap packets assigned stop phase a Z Nmass ha ha1 hZ hZL hN hlogN
    z count top htop hterminal M hM H hH hroot hphase hphaseNorm
  dsimp only
  intro e f hef hf hdrop j hj
  have he := grid.source_stopped_unary_endpoint tops slope precision cutoff weight shift top z
    count hterminal M hM hef hf hdrop
  have hfc : f ≤ count := he.1.trans (Nat.sub_le _ _)
  have hlevel := (ShiftedBlocks.endpoint_strictMono hK shift).monotone hfc
  exact htail N κ Label Item P alt hAlt t b v test T A τ grid tops slope precision cutoff weight
    hp hw K hK hKL gap packets assigned stop phase a Z Nmass ha ha1 hZ hZL hN hlogN
    z (ShiftedBlocks.endpoint shift) (ShiftedBlocks.endpoint_strictMono hK shift) (count-1) top htop
    e f H hef he.1 (hlevel.trans hH) he.2.1 he.2.2 hroot
    (fun k hk => hphase k (hk.trans_le hlevel))
    (fun k hk => hphaseNorm k (hk.trans_le hlevel)) j hj

end PacketLatticeData
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceSelectedGoodEvent
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reference event of a fixed selected packet family controls its
actual stopped prefixes and every disjoint unary run at the same point. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A e s r : ℝ)

/-- A good reference point bounds the selected physical stopping prefix
at every angular horizon, with its original analyzing coefficients. -/
theorem selectedPhysicalPrefix_good_event_bound (Q : Finset P.PacketIndex)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (z : ℝ×ℝ)
    (hz : z ∉ (P.restrictPackets Q).physicalReferenceBad (P.restrictedAlternate alt Q)
      (P.restrictedAlternate_bound alt hAlt Q) t a b v g (fun j l u => T j l u.val)
      L A e s r) (H : ℕ) :
    finiteCubicVariation (fun k => P.selectedPhysicalPrefix alt hAlt t b v g T L A Q stop z
      (min k H)) (2*H) ≤ (L^r)^3 := by
  have hgood := (P.restrictPackets Q).physicalReferenceBad_compl_bounds
    (P.restrictedAlternate alt Q) (P.restrictedAlternate_bound alt hAlt Q)
    t a b v g (fun j l u => T j l u.val) L A e s r z hz
  have hpoint : (z.1,z.2-t*z.1+t*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have h := P.selectedPhysicalPrefix_good_bound alt hAlt t b v g T L A Q stop hstop
    (z.2-t*z.1) z.1 H hgood.2.2.le
  simpa only [hpoint] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataReferenceSelectedVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A good event in recentered reference coordinates bounds the original
selected stopping prefix exactly, including its clamped variation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w
variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

theorem referenceFamily_selectedPhysicalPrefix
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (stop : Fin N → ℕ) (z : ℝ×ℝ) :
    (Q).selectedPhysicalPrefix (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l)) L A
      ((Finset.univ : Finset (Q).PacketIndex).filter
        (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)) stop z =
      P.selectedPhysicalPrefix alt hAlt oldSlope b v f T L A S stop z := by
  unfold selectedPhysicalPrefix SourceLabeledLattice.selectedPhysicalPrefix
  congr 1
  funext k
  have hs := P.sum_referenceFamily_selected oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency S
    (fun u => if stop u.1 = k then P.physicalMaskedValue alt hAlt oldSlope b v f T L A z u
      else 0) hS
  simp only [Finset.sum_filter] at hs ⊢
  simp_rw [P.referenceFamily_physicalMaskedValue oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f T L A z]
  exact hs

/-- The reference good event controls every original selected prefix
after recentering, with no angular-horizon or label-count factor. -/
theorem referenceFamily_selected_good_bound
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (a e s r : ℝ) (z : ℝ×ℝ)
    (hgood : z ∉ ((Q).restrictPackets ((Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S))).physicalReferenceBad
      ((Q).restrictedAlternate (fun j l => alt j (orig j l)) _)
      ((Q).restrictedAlternate_bound (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l)) _)
      newSlope a (fun j l => b j (orig j l)) v f (fun j l u => T j (orig j l) u.val)
      L A e s r) (H : ℕ) :
    finiteCubicVariation (fun k => P.selectedPhysicalPrefix alt hAlt oldSlope b v f T L A
      S stop z (min k H)) (2*H) ≤ (L^r)^3 := by
  have h := (Q).selectedPhysicalPrefix_good_event_bound
    (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l)) newSlope a
    (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l)) L A e s r
    ((Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)) stop hstop z hgood H
  simpa only [P.referenceFamily_selectedPhysicalPrefix oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f T L A S hS stop z] using h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataScaleGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype _root_.OAI.LipschitzHilbert.PacketLatticeData.selectedItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem length_antitone (P : PacketLatticeData N κ Label Item) : Antitone P.length := by
  intro i j hij
  unfold length
  exact div_le_div_of_nonneg_left P.topLength_pos.le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij)

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketPathProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The path-product theorem applied to original packet amplitudes.
The remaining analytic inputs are explicit square sums and propagated
residual bounds; no path-product estimate is assumed. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

theorem source_active_packet_prefix_product {Kb : ℕ} {F : Type*} [NormedAddCommGroup F]
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hprecision : ∀ t ∈ tops, 0 ≤ precision t)
    (hweight : ∀ t x, 0 < weight t x) {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (phase : ℕ → ℂ) (a α p μ : ℝ)
    (hphase : ∀ k, 0 ≤ (phase k).re) (hrelation : p*μ = α-1)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (heligible : ∀ q ∈ packets, g.eligible cutoff (precision (assigned q)) (stop q))
    (hKb : 0 < Kb) (tag : Fin Kb) (top : τ) (htop : top ∈ tops) (x : X)
    (count H : ℕ) (hH : ShiftedBlocks.endpoint tag count ≤ H)
    (marked : ℕ → Prop) (profile : ℕ → F) (c M B V C ε Q Cex : ℝ)
    (hp : 1 ≤ p) (hα : 1 ≤ α) (hαp : α ≤ p) (hc : 0 < c) (hc1 : c ≤ 1)
    (hM : 4 ≤ M) (hμ : (α-1)/p ≤ 1/12)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hCex : 0 ≤ Cex) :
    let n := g.shiftedPathMass tops slope precision cutoff weight tag top x
    let amp := g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a tag top x
    let level := ShiftedBlocks.endpoint tag
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let residual := fun j => g.packetResidual packets (fun q => slope (assigned q)) stop base
      transition (level j) (level (j+1)) (g.index (level j) (slope top))
    let keep := fun j q => assigned q ∈ g.cellTops tops slope precision cutoff (level (j+1))
      (g.index (level (j+1)) (slope top))
    let U := fun j => g.packetResidual (packets.filter (keep j)) (fun q => slope (assigned q))
      stop base transition (level j) (level (j+1)) (g.index (level j) (slope top))
    let W := fun j => g.packetAmplitude (packets.filter fun q => ¬keep j q)
      (fun q => slope (assigned q)) stop base transition (level j) (g.index (level j) (slope top))
    let coeff := fun j => g.packetPathProduct transition (level j) (level (j+1)) (slope top)
    (∀ j < count, M < n j) →
    (∀ j < count, marked j → c ≤ n j-n (j+1)) →
    (∑ j ∈ (Finset.range count).filter marked, ‖residual j‖^2) ≤ B^2 →
    (∀ j < count, n j^((α-1)/p) ≤ Q) →
    finiteCubicVariation (fun k => profile (min k H)) (2*H) ≤ V^3 →
    (∀ j < count, ¬marked j → n j-n (j+1) < 1 → ‖W j‖ ≤ ε*(n j-n (j+1))) →
    (∀ e f, e < f → f ≤ count → n e-n f < 2 →
      (∀ k ∈ Finset.Ico e f, ¬marked k ∧ n k-n (k+1) < 1) →
      ∀ j ∈ Finset.Icc e f, ‖∑ k ∈ Finset.Ico j f, unaryPropagator coeff j k • U k‖ ≤
        C*intervalOscillation profile H (level e) (level f)) →
    (∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n (j+1) ≤ M) →
    (∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → n j ≤ M+1) →
    (∀ j < count, ¬marked j → 1 ≤ n j-n (j+1) → ‖amp j‖ ≤ Cex*n j) →
    (∏ j ∈ Finset.range count, g.sourceShiftedPathRatio tops slope precision cutoff weight K gap
      packets assigned stop value phase a α p tag top x j) ≤
      Real.exp (p*Real.sqrt (2*(1+3/c))*M^(-(1/2:ℝ)+(α-1)/p)*B+
        (4*p*C*((2*(2+17/c))^(2/3:ℝ)*M^(-(1/3:ℝ)+(α-1)/p)*V)+
          4*p*ε*(Q*∑ j ∈ (Finset.range count).filter
            (fun j => ¬marked j ∧ n j-n (j+1) < 1), pathDrop n j))+
        Real.log (1+Cex^p*(M+1)^(α-1)))*
      ∏ j ∈ Finset.range count, if marked j then
        g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets assigned stop
          value phase a p μ tag top x j else 1 := by
  dsimp only
  let n := g.shiftedPathMass tops slope precision cutoff weight tag top x
  let amp := g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap
    packets assigned stop value phase a tag top x
  let level := ShiftedBlocks.endpoint tag
  let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x
  let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
  let residual := fun j => g.packetResidual packets (fun q => slope (assigned q)) stop base
    transition (level j) (level (j+1)) (g.index (level j) (slope top))
  let keep := fun j q => assigned q ∈ g.cellTops tops slope precision cutoff (level (j+1))
    (g.index (level (j+1)) (slope top))
  let U := fun j => g.packetResidual (packets.filter (keep j)) (fun q => slope (assigned q))
    stop base transition (level j) (level (j+1)) (g.index (level j) (slope top))
  let W := fun j => g.packetAmplitude (packets.filter fun q => ¬keep j q)
    (fun q => slope (assigned q)) stop base transition (level j) (g.index (level j) (slope top))
  let coeff := fun j => g.packetPathProduct transition (level j) (level (j+1)) (slope top)
  let den := g.sourceShiftedPathDenominator tops slope precision cutoff weight K gap
    packets assigned stop value phase a α p tag top x
  intro hactive hmarked hsquare hQ hvariation hW hU hexstop hexmass hexamp
  have he (j : ℕ) (hj : j < count) :
      g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag j) :=
    g.shiftedPathMass_ne_zero_eligible tops slope precision cutoff weight tag top x j
      (ne_of_gt (by have := hactive j hj; linarith))
  have hden (j : ℕ) (hj : j < count) : n j ≤ den j := by
    have h := sourceNodeDenominator_ge_mass
      (g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x)
      (fun i : g.sourceBlockCells tops slope precision cutoff (level j) (level (j+1))
        (g.index (level j) (slope top)) =>
        g.mass tops slope precision cutoff weight (level (j+1)) i.val x)
      (fun i => g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
        (value x) phase a x (level (j+1)) i.val) α p
      (fun i => g.mass_nonnegative tops slope precision cutoff weight
        (fun t z => (hweight t z).le) _ i.val x)
    simpa only [n,den,shiftedPathMass,sourceShiftedPathDenominator,ite_eq_left (he j hj)] using h
  have hrec (j : ℕ) (hj : j < count) (_hm : ¬marked j) (hd : n j-n (j+1) < 1) :
      ‖coeff j‖ ≤ 1 ∧ amp j = coeff j • amp (j+1)+U j+W j :=
    g.source_stopped_unary_recurrence tops slope precision cutoff weight hprecision hweight
      hK gap packets assigned stop value phase a hphase hassigned heligible hKb tag top htop x j
      (by linarith : 1 ≤ M) (hactive j hj) hd
  have hprod := source_path_product_from_propagated_residuals count n amp U W residual coeff den
    marked profile level (ShiftedBlocks.endpoint_strictMono hKb tag) H hH
    (g.shiftedPathMass_antitone tops slope precision cutoff weight hprecision
      (fun t z => (hweight t z).le) hKb tag top htop x)
    hp hα hαp hc hc1 hM hμ hB hV hC hε hCex hactive hden hmarked hsquare hQ hvariation
    (fun j hj _ _ => g.source_shifted_path_denominator_ge_next tops slope precision cutoff weight
      hprecision (fun t z => (hweight t z).le) K gap packets assigned stop value phase a α p
      (by linarith : 0 < p) hKb tag top htop x j (he j hj))
    (fun j hj hm hd => (hrec j hj hm hd).1)
    (fun j hj hm hd => (hrec j hj hm hd).2) hW hU hexstop hexmass hexamp
  have hleft : (∏ j ∈ Finset.range count,
      g.sourceShiftedPathRatio tops slope precision cutoff weight K gap packets assigned stop value
        phase a α p tag top x j) =
      ∏ j ∈ Finset.range count, vertexAmount (n j) (amp j) α p/den j := by
    apply Finset.prod_congr rfl
    intro j hj
    exact g.source_shifted_ratio_eq_amount_div_denominator tops slope precision cutoff weight
      K gap packets assigned stop value phase a α p tag top x j (he j (Finset.mem_range.mp hj))
  have hright : (∏ j ∈ Finset.range count,
      if marked j then vertexAmount (n j) (amp j-residual j) α p/den j else 1) =
      ∏ j ∈ Finset.range count, if marked j then
        g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets assigned stop
          value phase a p μ tag top x j else 1 := by
    apply Finset.prod_congr rfl
    intro j hj
    split_ifs with hm
    · exact (g.source_stopped_residual_free_ratio tops slope precision cutoff weight hprecision hweight
        K gap packets assigned stop value phase a α p μ hrelation hassigned heligible hKb tag top htop
        x j (he j (Finset.mem_range.mp hj))).symm
    · rfl
  rw [hleft]
  exact hprod.trans_eq (congrArg (fun z => _*z) hright)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMarkedStop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cell marks vanish after the first mass crossing, so passing
between the stopped prefix and the complete marked product is exact. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem source_marked_product_stop (n beta : ℕ → ℝ) (marked : ℕ → Prop)
    (count : ℕ) (M : ℝ) (hlast : n count ≤ M) (hanti : Antitone n)
    (hmarked : ∀ j < count, marked j → M < n j) :
    (∏ j ∈ Finset.range (firstMassStop n count M), if marked j then beta j else 1) =
      ∏ j ∈ Finset.range count, if marked j then beta j else 1 := by
  apply Finset.prod_subset (Finset.range_mono (firstMassStop_spec n count M hlast).1)
  intro j hj hnot
  have hstop : firstMassStop n count M ≤ j := by
    have : ¬j < firstMassStop n count M := by simpa only [Finset.mem_range] using hnot
    omega
  have hm : ¬marked j := fun hm =>
    (not_lt_of_ge (firstMassStop_after n count M hlast hanti hstop))
      (hmarked j (Finset.mem_range.mp hj) hm)
  exact ite_eq_right hm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceResidualCostBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed polynomial residual losses are absorbed by the source
mass cutoff, uniformly for the full permitted range of the phase exponent. -/

noncomputable section
namespace LipschitzHilbert

theorem source_principal_residual_costs {L Cmarked Cunary A_M μ C₁ C₂ : ℝ}
    (hL : 1 ≤ L) (hC₁ : C₁ ≤ L) (hC₂ : C₂ ≤ L) (hAM : 0 ≤ A_M)
    (hchoice : 4*(max Cmarked Cunary+3/2) ≤ A_M) (hμ : μ ≤ 1/12) :
    Real.sqrt L*C₁*L^Cmarked*(L^A_M)^(-(1/2:ℝ)+μ)+
      Real.sqrt L*C₂*L^Cunary*(L^A_M)^(-(1/3:ℝ)+μ) ≤ 2 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hbudget := residual_polynomial_budget (C := max Cmarked Cunary+1)
    hL hμ hAM (by linarith)
  have hcoeff (C b : ℝ) (hC : C ≤ L) (hb : b ≤ max Cmarked Cunary) :
      C*L^b ≤ L^(max Cmarked Cunary+1) := by
    calc
      _ ≤ L*L^b := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hL0.le _)
      _ ≤ L*L^(max Cmarked Cunary) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL hb) hL0.le
      _ = _ := by rw [Real.rpow_add hL0,Real.rpow_one]; ring
  have hmarked : Real.sqrt L*C₁*L^Cmarked*(L^A_M)^(-(1/2:ℝ)+μ) ≤ 1 := by
    calc
      _ = L^(1/2:ℝ)*(C₁*L^Cmarked)*(L^A_M)^(-(1/2:ℝ)+μ) := by
        rw [Real.sqrt_eq_rpow]; ring
      _ ≤ L^(1/2:ℝ)*L^(max Cmarked Cunary+1)*(L^A_M)^(-(1/2:ℝ)+μ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hcoeff C₁ Cmarked hC₁ (le_max_left _ _))
            (Real.rpow_nonneg hL0.le _)) (Real.rpow_nonneg (Real.rpow_nonneg hL0.le _) _)
      _ ≤ 1 := hbudget.2
  have hunary : Real.sqrt L*C₂*L^Cunary*(L^A_M)^(-(1/3:ℝ)+μ) ≤ 1 := by
    calc
      _ = L^(1/2:ℝ)*(C₂*L^Cunary)*(L^A_M)^(-(1/3:ℝ)+μ) := by
        rw [Real.sqrt_eq_rpow]; ring
      _ ≤ L^(1/2:ℝ)*L^(max Cmarked Cunary+1)*(L^A_M)^(-(1/3:ℝ)+μ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hcoeff C₂ Cunary hC₂ (le_max_right _ _))
            (Real.rpow_nonneg hL0.le _)) (Real.rpow_nonneg (Real.rpow_nonneg hL0.le _) _)
      _ ≤ 1 := hbudget.1
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceUnaryErrorBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mask error stays negligible after the phase-mass factor and the
entire logarithmic path-drop sum. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

theorem eventually_source_unary_error_scale (q C R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ L : ℝ in atTop,
      4*Real.sqrt L*(L^q*Real.exp (-L*Real.log L))*(Real.exp (C*Real.sqrt L)*(R*L)) ≤ 1 := by
  filter_upwards [eventually_discarded_residual_small (q+4) C,
    eventually_ge_atTop (max 4 R),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with L hsmall hlarge hlog
  have hL : 4 ≤ L := (le_max_left _ _).trans hlarge
  have hRL : R ≤ L := (le_max_right _ _).trans hlarge
  have hL0 : 0 < L := by linarith
  have hs : Real.sqrt L ≤ L := by
    have := Real.sq_sqrt hL0.le
    have := Real.sqrt_nonneg L
    nlinarith
  have hc : 4*Real.sqrt L*R*L ≤ L^4 := by
    calc
      _ ≤ L*L*L*L := by gcongr
      _ = _ := by ring
  calc
    _ = (4*Real.sqrt L*R*L)*L^q*Real.exp (-L*Real.log L+C*Real.sqrt L) := by
      rw [Real.exp_add]
      ring
    _ ≤ L^4*L^q*Real.exp (-L+C*Real.sqrt L) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL0.le _)
      · apply Real.exp_le_exp.mpr
        nlinarith
      · exact (Real.exp_pos _).le
      · positivity
    _ = Real.exp (-L)*Real.exp (C*Real.sqrt L)*L^(q+4) := by
      rw [Real.exp_add,← Real.rpow_natCast L 4,← Real.rpow_add hL0]
      norm_num only [Nat.cast_ofNat]
      have heq : (4:ℝ)+q = q+4 := by ring
      rw [heq]
      ring
    _ ≤ 1 := hsmall

/-- Uniformly over a finite active prefix and any subcollection of its
indices, the physical off-child contribution costs at most one. -/
theorem eventually_source_unary_error_budget (q C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ → ℝ) (count : ℕ) (S : Finset ℕ),
      S ⊆ Finset.range count → Antitone n →
    ∀ (M p ε Q : ℝ), 1 ≤ M → 0 ≤ p → p ≤ Real.sqrt L →
      0 ≤ ε → ε ≤ L^q*Real.exp (-L*Real.log L) →
      0 ≤ Q → Q ≤ Real.exp (C*Real.sqrt L) →
      (∀ j < count, M < n j) → 0 ≤ n count → Real.log (n 0) ≤ 3*L →
      4*p*ε*(Q*∑ j ∈ S, pathDrop n j) ≤ 1 := by
  filter_upwards [eventually_source_unary_error_scale q C 4 (by norm_num),
    eventually_ge_atTop (1:ℝ)] with L hscale hL
  intro n count S hS hanti M p ε Q hM hp hpL hε hεL hQ hQL hactive hlast hlog
  have hM0 : 0 < M := by linarith
  have hnonneg (j : ℕ) (hj : j ∈ Finset.range count) : 0 ≤ pathDrop n j :=
    pathDrop_nonnegative n j (hM0.trans (hactive j (Finset.mem_range.mp hj)))
      (hanti (Nat.le_succ j))
  have hsum0 : 0 ≤ ∑ j ∈ S, pathDrop n j := Finset.sum_nonneg fun j hj => hnonneg j (hS hj)
  have hsum : (∑ j ∈ S, pathDrop n j) ≤ 4*L := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hS (fun j hj _ => hnonneg j hj)).trans
    by_cases hc : count = 0
    · simp only [hc,Finset.sum_range_zero]
      linarith
    have hn0 := hM0.trans (hactive 0 (Nat.pos_of_ne_zero hc))
    have hlogM : Real.log (n 0/M) ≤ 3*L :=
      (Real.log_le_log (div_pos hn0 hM0) (div_le_self hn0.le hM)).trans hlog
    have hb := active_path_drop_budget n count hM0 hactive hlast
    have hm : max 0 (Real.log (n 0/M)) ≤ 3*L := max_le (by linarith) hlogM
    linarith
  calc
    _ ≤ 4*Real.sqrt L*(L^q*Real.exp (-L*Real.log L))*
        (Real.exp (C*Real.sqrt L)*(4*L)) := by gcongr
    _ ≤ 1 := hscale

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourcePathCostBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full path exponent has a uniform constant once the two residual
norms have polynomial bounds. The prescribed cutoff absorbs both costs. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

theorem eventually_source_path_cost_budget (Cmarked Cunary q Cmass A_M : ℝ)
    (hAM : 0 ≤ A_M) (hchoice : 4*(max Cmarked (Cunary+6)+3/2) ≤ A_M) :
    ∀ᶠ L : ℝ in atTop, ∀ (n : ℕ → ℝ) (count : ℕ) (S : Finset ℕ),
      S ⊆ Finset.range count → Antitone n →
    ∀ B V ε Q μ : ℝ, 0 ≤ B → B ≤ L^Cmarked → 0 ≤ V → V ≤ L^Cunary →
      0 ≤ ε → ε ≤ L^q*Real.exp (-L*Real.log L) →
      0 ≤ Q → Q ≤ Real.exp (Cmass*Real.sqrt L) → μ ≤ 1/12 →
      (∀ j < count, L^A_M < n j) → 0 ≤ n count → Real.log (n 0) ≤ 3*L →
      Real.sqrt L*Real.sqrt 26*(L^A_M)^(-(1/2:ℝ)+μ)*B+
        (4*Real.sqrt L*L^6*((140:ℝ)^(2/3:ℝ)*(L^A_M)^(-(1/3:ℝ)+μ)*V)+
          4*Real.sqrt L*ε*(Q*∑ j ∈ S, pathDrop n j)) ≤ 3 := by
  filter_upwards [eventually_source_unary_error_budget q Cmass,
    eventually_ge_atTop (max 1 (max (Real.sqrt 26) (4*(140:ℝ)^(2/3:ℝ))))]
    with L hunary hLbig
  have hL : 1 ≤ L := (le_max_left _ _).trans hLbig
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have h₁ : Real.sqrt 26 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hLbig)
  have h₂ : 4*(140:ℝ)^(2/3:ℝ) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hLbig)
  intro n count S hS hanti B V ε Q μ hB hBL hV hVL hε hεL hQ hQL hμ hactive hlast hlog
  have hmain := source_principal_residual_costs hL h₁ h₂ hAM hchoice hμ
  have hM : 1 ≤ L^A_M := Real.one_le_rpow hL hAM
  have herr := hunary n count S hS hanti (L^A_M) (Real.sqrt L) ε Q
    hM (Real.sqrt_nonneg L) le_rfl hε hεL hQ hQL hactive hlast hlog
  have hBterm : Real.sqrt L*Real.sqrt 26*(L^A_M)^(-(1/2:ℝ)+μ)*B ≤
      Real.sqrt L*Real.sqrt 26*L^Cmarked*(L^A_M)^(-(1/2:ℝ)+μ) := by
    calc
      _ ≤ Real.sqrt L*Real.sqrt 26*(L^A_M)^(-(1/2:ℝ)+μ)*L^Cmarked := by gcongr
      _ = _ := by ring
  have hVterm : 4*Real.sqrt L*L^6*((140:ℝ)^(2/3:ℝ)*(L^A_M)^(-(1/3:ℝ)+μ)*V) ≤
      Real.sqrt L*(4*(140:ℝ)^(2/3:ℝ))*L^(Cunary+6)*(L^A_M)^(-(1/3:ℝ)+μ) := by
    calc
      _ ≤ 4*Real.sqrt L*L^6*((140:ℝ)^(2/3:ℝ)*(L^A_M)^(-(1/3:ℝ)+μ)*L^Cunary) := by gcongr
      _ = _ := by
        have hpow : L^(6:ℝ) = L^(6:ℕ) := by exact Real.rpow_natCast L 6
        rw [Real.rpow_add hL0,hpow]
        ring
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourcePacketStoppedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original stopped packet product has the source's uniform path
bound once its two reference residual norms have polynomial control. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem eventually_source_packet_stopped_bound
    (Cmarked Cunary q Cmass A_M : ℝ) (hAM : 0 < A_M)
    (hchoice : 4*(max Cmarked (Cunary+6)+3/2) ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (τ σ X : Type*) (κ : Type) [Fintype κ],
    ∀ (Kb : ℕ) (F : Type*) [NormedAddCommGroup F]
      (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
      (weight : τ → X → ℝ), (∀ t ∈ tops, 0 ≤ precision t) →
      (∀ t x, 0 < weight t x) →
    ∀ (K : ℕ), 0 < K → ∀ (gap : ℕ → ℝ)
      (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
      (value : X → σ → EuclideanSpace ℂ κ) (phase : ℕ → ℂ) (a α μ : ℝ),
      (∀ k, 0 ≤ (phase k).re) → Real.sqrt L*μ = α-1 →
      (∀ z ∈ packets, assigned z ∈ tops) →
      (∀ z ∈ packets, g.eligible cutoff (precision (assigned z)) (stop z)) →
    ∀ (_hKb : 0 < Kb) (tag : Fin Kb) (top : τ), top ∈ tops →
    ∀ (x : X) (count H : ℕ), ShiftedBlocks.endpoint tag count ≤ H →
      (¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint tag count)) →
    ∀ (marked : ℕ → Prop) (profile : ℕ → F) (Cex : ℝ),
      1 ≤ α → α ≤ Real.sqrt L → (α-1)/Real.sqrt L ≤ 1/12 → 0 ≤ Cex →
    let n := g.shiftedPathMass tops slope precision cutoff weight tag top x
    let finish := firstMassStop n count (L^A_M)
    let amp := g.sourceShiftedPathAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a tag top x
    let level := ShiftedBlocks.endpoint tag
    let base := g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x
    let transition := g.sourceTransition tops slope precision cutoff weight K gap phase x
    let residual := fun j => g.packetResidual packets (fun z => slope (assigned z)) stop base
      transition (level j) (level (j+1)) (g.index (level j) (slope top))
    let keep := fun j z => assigned z ∈ g.cellTops tops slope precision cutoff (level (j+1))
      (g.index (level (j+1)) (slope top))
    let U := fun j => g.packetResidual (packets.filter (keep j)) (fun z => slope (assigned z))
      stop base transition (level j) (level (j+1)) (g.index (level j) (slope top))
    let W := fun j => g.packetAmplitude (packets.filter fun z => ¬keep j z)
      (fun z => slope (assigned z)) stop base transition (level j) (g.index (level j) (slope top))
    let coeff := fun j => g.packetPathProduct transition (level j) (level (j+1)) (slope top)
    Real.log (n 0) ≤ 3*L →
    (∀ j < count, marked j → L^A_M < n j) →
    (∀ j < finish, marked j → (1/4:ℝ) ≤ n j-n (j+1)) →
    (∑ j ∈ (Finset.range finish).filter marked, ‖residual j‖^2) ≤ (L^Cmarked)^2 →
    (∀ j < finish, n j^((α-1)/Real.sqrt L) ≤ Real.exp (Cmass*Real.sqrt L)) →
    finiteCubicVariation (fun k => profile (min k H)) (2*H) ≤ (L^Cunary)^3 →
    (∀ j < finish, ¬marked j → n j-n (j+1) < 1 →
      ‖W j‖ ≤ (L^q*Real.exp (-L*Real.log L))*(n j-n (j+1))) →
    (∀ e f, e < f → f ≤ finish → n e-n f < 2 →
      (∀ k ∈ Finset.Ico e f, ¬marked k ∧ n k-n (k+1) < 1) →
      ∀ j ∈ Finset.Icc e f, ‖∑ k ∈ Finset.Ico j f, unaryPropagator coeff j k • U k‖ ≤
        L^6*intervalOscillation profile H (level e) (level f)) →
    (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → n (j+1) ≤ L^A_M) →
    (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → n j ≤ L^A_M+1) →
    (∀ j < finish, ¬marked j → 1 ≤ n j-n (j+1) → ‖amp j‖ ≤ Cex*n j) →
    g.sourceActivePathValue tops slope precision cutoff weight K gap packets assigned stop value
      phase a α (Real.sqrt L) (L^A_M) tag top count x ≤
      (Real.exp 3*(1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1)))*
        ∏ j ∈ Finset.range count, if marked j then
          g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap packets assigned stop
            value phase a (Real.sqrt L) μ tag top x j else 1 := by
  filter_upwards [eventually_source_path_cost_budget Cmarked Cunary q Cmass A_M hAM.le hchoice,
    (tendsto_rpow_atTop hAM).eventually_ge_atTop 4,eventually_ge_atTop (1:ℝ)]
    with L hbudget hM hL
  intro τ σ X κ _ Kb F _ g tops slope precision cutoff weight hp hw K hK gap packets assigned stop
    value phase a α μ hphase hrelation hassigned heligible hKb tag top htop x count H hH
    hterminal marked profile Cex hα hαp hμ hCex
  dsimp only
  let n := g.shiftedPathMass tops slope precision cutoff weight tag top x
  let finish := firstMassStop n count (L^A_M)
  intro hlog hmarkActive hmarkDrop hsquare hQ hvariation hW hU hexstop hexmass hexamp
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hroot : 1 ≤ Real.sqrt L := (Real.le_sqrt (by norm_num) hL0.le).mpr (by simpa using hL)
  have hnlast : n count ≤ L^A_M := by
    rw [show n count = 0 from g.shiftedPathMass_terminal_zero tops slope precision cutoff
      weight tag top count hterminal x]
    exact Real.rpow_nonneg hL0.le _
  have hs := firstMassStop_spec n count (L^A_M) hnlast
  have hnanti : Antitone n := g.shiftedPathMass_antitone tops slope precision cutoff weight hp
    (fun t z => (hw t z).le) hKb tag top htop x
  have hfinish : ShiftedBlocks.endpoint tag finish ≤ H :=
    ((ShiftedBlocks.endpoint_strictMono hKb tag).monotone hs.1).trans hH
  have hprod := g.source_active_packet_prefix_product tops slope precision cutoff weight hp hw
    hK gap packets assigned stop value phase a α (Real.sqrt L) μ hphase hrelation hassigned
    heligible hKb tag top htop x finish H hfinish marked profile (1/4) (L^A_M)
    (L^Cmarked) (L^Cunary) (L^6) (L^q*Real.exp (-L*Real.log L))
    (Real.exp (Cmass*Real.sqrt L)) Cex hroot hα hαp (by norm_num) (by norm_num) hM hμ
    (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _) (by positivity)
    (by positivity) hCex hs.2.2 hmarkDrop hsquare hQ hvariation hW hU hexstop hexmass hexamp
  have hcost := hbudget n finish
    ((Finset.range finish).filter fun j => ¬marked j ∧ n j-n (j+1) < 1)
    (Finset.filter_subset ..) hnanti (L^Cmarked) (L^Cunary)
    (L^q*Real.exp (-L*Real.log L)) (Real.exp (Cmass*Real.sqrt L))
    ((α-1)/Real.sqrt L) (Real.rpow_nonneg hL0.le _) le_rfl
    (Real.rpow_nonneg hL0.le _) le_rfl (by positivity) le_rfl (by positivity) le_rfl
    hμ hs.2.2 (g.shiftedPathMass_nonneg tops slope precision cutoff weight
      (fun t z => (hw t z).le) tag top x finish) hlog
  norm_num only at hprod
  let pred := fun j => g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap
    packets assigned stop value phase a (Real.sqrt L) μ tag top x j
  have hpred : 0 ≤ ∏ j ∈ Finset.range finish, if marked j then pred j else 1 := by
    apply Finset.prod_nonneg
    intro j hj
    split_ifs
    · apply (g.sourceShiftedPathPrediction_pos tops slope precision cutoff weight hw
        K gap packets assigned stop value phase a (Real.sqrt L) μ tag top htop x j _).le
      exact g.shiftedPathMass_ne_zero_eligible tops slope precision cutoff weight tag top x j
        (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<4) (hM.trans (hs.2.2 j (Finset.mem_range.mp hj)).le)))
    · exact zero_le_one
  have hCpos : 0 < 1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1) := by positivity
  rw [g.source_active_path_eq_stopped_product tops slope precision cutoff weight hp
    (fun t z => (hw t z).le) K gap packets assigned stop value phase a α (Real.sqrt L)
    (L^A_M) (Real.rpow_nonneg hL0.le _) hKb tag top htop count hterminal x]
  apply hprod.trans
  rw [Real.exp_add,Real.exp_log hCpos]
  have he := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hCpos.le
  have hm := mul_le_mul_of_nonneg_right he hpred
  have hstop := source_marked_product_stop n pred marked count (L^A_M) hnlast hnanti hmarkActive
  calc
    _ ≤ (Real.exp 3*(1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1)))*
        (∏ j ∈ Finset.range finish, if marked j then pred j else 1) := hm
    _ = _ := congrArg (fun z => (Real.exp 3*(1+Cex^(Real.sqrt L)*(L^A_M+1)^(α-1)))*z) hstop

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceMarkedResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full residual square controls every marked prefix chosen later
by the spatial mass stopping rule. No choice of marks costs a factor. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem marked_prefix_square_le {E : Type*} [NormedAddCommGroup E]
    (residual : ℕ → E) (count finish : ℕ) (hfinish : finish ≤ count)
    (marked : ℕ → Prop) {B : ℝ}
    (hfull : (∑ j : Fin count, ‖residual j.val‖^2) ≤ B) :
    (∑ j ∈ (Finset.range finish).filter marked, ‖residual j‖^2) ≤ B := by
  classical
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.filter_subset marked _).trans (Finset.range_mono hfinish))
    (fun j _ _ => sq_nonneg ‖residual j‖))
  rw [← Fin.sum_univ_eq_sum_range (fun j => ‖residual j‖^2) count]
  exact hfull

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStoppedMassPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The phase power of every active stopped mass is bounded by the
same subexponential factor. This uses the mass at the initial node,
rather than a separate bound at every generation. -/

noncomputable section
namespace LipschitzHilbert

theorem mass_power_le_exp_sqrt {L n N α : ℝ}
    (hL : 1 ≤ L) (hn : 0 ≤ n) (hN : 0 < N) (hnN : n ≤ N)
    (hα : 1 ≤ α) (hα3 : α ≤ 3) (hlog : Real.log N ≤ 3*L) :
    n^((α-1)/Real.sqrt L) ≤ Real.exp (6*Real.sqrt L) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs2 := Real.sq_sqrt hL0.le
  have he : 0 ≤ (α-1)/Real.sqrt L := div_nonneg (by linarith) hs.le
  apply (Real.rpow_le_rpow hn hnN he).trans
  rw [Real.rpow_def_of_pos hN]
  apply Real.exp_le_exp.mpr
  calc
    Real.log N*((α-1)/Real.sqrt L) ≤ (3*L)*((α-1)/Real.sqrt L) :=
      mul_le_mul_of_nonneg_right hlog he
    _ ≤ (3*L)*(2/Real.sqrt L) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (by linarith) hs.le) (by positivity)
    _ = 6*Real.sqrt L := by
      field_simp
      nlinarith

theorem stopped_mass_power_le_exp_sqrt (n : ℕ → ℝ) (count : ℕ) (M L α : ℝ)
    (hL : 1 ≤ L) (hM : 0 ≤ M) (hanti : Antitone n) (hlast : n count ≤ M)
    (hα : 1 ≤ α) (hα3 : α ≤ 3) (hlog : Real.log (n 0) ≤ 3*L)
    {j : ℕ} (hj : j < firstMassStop n count M) :
    n j^((α-1)/Real.sqrt L) ≤ Real.exp (6*Real.sqrt L) := by
  have hactive := (firstMassStop_spec n count M hlast).2.2 j hj
  have hnj : 0 < n j := hM.trans_lt hactive
  have hnj0 : n j ≤ n 0 := hanti (Nat.zero_le j)
  exact mass_power_le_exp_sqrt hL hnj.le (hnj.trans_le hnj0) hnj0 hα hα3 hlog

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataParentStoppedBound
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parent-cone version of the stopped physical path estimate.
 The two literal physical reference events discharge the square and
variation inputs of the stopped path estimate. The propagated unary
residual and mass power estimates follow from the active mass path itself.
The remaining local hypotheses concern marking and off-child amplitudes. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_physical_parent_stopped_bound
    (q D Cmass qoff A_M : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (hCmass : 0 ≤ Cmass)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*q+13) (2*q+17)+3/2) ≤ A_M)
    (Klocal Hlocal : ℕ) :
    ∀ᶠ L : ℝ in atTop, physicalParentStoppedBoundAt q D Cmass qoff A_M L Klocal Hlocal := by
  have hchoice' : 4*(max (3*q+13) ((2*q+11)+6)+3/2) ≤ A_M := by
    simpa only [show (2*q+11)+6 = 2*q+17 by ring] using hchoice
  filter_upwards [eventually_physical_parent_full_residual_square q D hq hD Klocal Hlocal,
    eventually_selected_active_physical_unary_tail Cmass hCmass,
    AngularGrid.eventually_source_packet_stopped_bound (3*q+13) (2*q+11) qoff 6 A_M hAM hchoice',
    (tendsto_rpow_atTop hAM).eventually_ge_atTop 4,eventually_ge_atTop (9:ℝ)]
    with L hsquare htail hbound hM hL
  unfold physicalParentStoppedBoundAt
  intro N κ Label Item _ _ P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops slope precision T A s w R C F hw hR
    hbranch hK shift hzero hp top htop hprecision hcone hF hwide hfrequency hparentCone hparentWide
    cut stop weight count phase hz Z Nmass α μ ha ha1 hZ hZL hphase hN hlogN
    hα hα3 hμ hrelation z packets assigned hassigned heligible hangle
    squarePackets Qsquare origSquare squareSelected S Q orig selected hsquareEvent hreference n finish value level transition base W amp
    H marked Cex hH hCex hlog hroot hmarked hdrop hW hexstop hexmass hexamp
  let profile := P.selectedPhysicalPrefix alt hAlt t b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A S stop z
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hKL := source_blockCount_le_square (show 5 ≤ L by linarith)
  have hwpos (top : τ) (z : ℝ×ℝ) : 0 < weight top z :=
    (T top).weight_pos (Real.rpow_pos_of_pos hL0 _) D z
  have hterminal : ¬grid.eligible cut (precision top) (ShiftedBlocks.endpoint shift count) := by
    rw [hprecision]
    exact grid.firstIneligibleShiftedBlock_spec cut (w/R) (div_pos hw hR) hK shift
  have hnlast : n count ≤ L^A_M := by
    rw [show n count = 0 from grid.shiftedPathMass_terminal_zero tops slope precision cut
      weight shift top count hterminal z]
    positivity
  have hfinish := (firstMassStop_spec n count (L^A_M) hnlast).1
  have hnanti := grid.shiftedPathMass_antitone tops slope precision cut weight hp
    (fun top z => (hwpos top z).le) hK shift top htop z
  have hS : ∀ u ∈ S, P.referenceCondition t (slope top) R
      (C+(SourceParameters.branching L)^2) w u.1 u.2.1 := by
    intro u hu
    obtain ⟨huP,j,hj,hstop,hchild⟩ := Finset.mem_filter.mp hu
    have href : grid.eligible cut (w/R) (ShiftedBlocks.endpoint shift (j+1)) := by
      apply grid.eligible_before_firstIneligibleShiftedBlock
      omega
    have hcell := ((grid.mem_cellTops _ _ _ _ _ _ _).mp hchild).2.1
    have hg := grid.residual_packet_length_and_cone hw (SourceParameters.branching_pos L)
      (P.length_pos u.1) hR (hzero u.1) hstop.2 href hcell (hangle u huP)
    exact ⟨hg.1.le,by simpa only [mul_div_assoc] using hg.2⟩
  have hvariation : finiteCubicVariation (fun k => profile (min k H)) (2*H) ≤
      (L^(2*q+11))^3 := by
    exact P.referenceFamily_selected_good_bound t (slope top) R
      (C+(SourceParameters.branching L)^2) w F hw hcone hF hwide hfrequency
      alt hAlt b v f (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A S hS stop
      (grid.source_length_stopping_antitone cut hw P.length P.length_pos P.length_antitone)
      (w/P.topLength) (q+8) (2*q+9) (2*q+11) z hreference H
  have hfull := hsquare N κ Label Item P horder hP alt hAlt t (w/P.topLength) d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops slope precision T A s w R C F (slope top)
    hw hR hparentCone hF hparentWide hfrequency hbranch hK shift hzero hp phase hz a ha ha1
    z packets assigned hassigned heligible hangle hsquareEvent
  apply hbound τ P.PacketIndex (ℝ×ℝ) κ
    (SourceParameters.blockCount L) (EuclideanSpace ℂ κ) grid tops slope precision
    cut weight hp hwpos (SourceParameters.blockCount L) hK (grid.sourceBoundaryGap L)
    packets assigned (fun u => stop u.1) value phase a α μ hz hrelation hassigned heligible
    hK shift top htop z count H hH hterminal marked profile Cex hα
    (hα3.trans ((Real.le_sqrt (by norm_num) hL0.le).mpr (by nlinarith))) hμ hCex
    hlog hmarked hdrop
  · exact marked_prefix_square_le _ count _ hfinish marked hfull
  · intro j hj
    exact stopped_mass_power_le_exp_sqrt n count (L^A_M) L α hL1
      (Real.rpow_nonneg hL0.le _) hnanti hnlast hα hα3 hlog hj
  · exact hvariation
  · exact hW
  · intro e fEnd hef hfEnd hdiff _ j hj
    exact htail N κ Label Item P alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) A τ grid tops slope precision cut weight hp hwpos
      (SourceParameters.blockCount L) hK hKL shift (grid.sourceBoundaryGap L) packets assigned
      stop phase a Z Nmass ha ha1 hZ hZL hN hlogN z count top htop hterminal
      (L^A_M) hM H hH hroot (fun k _ => hz k) (fun k _ => hphase k) e fEnd hef hfEnd hdiff j hj
  · exact hexstop
  · exact hexmass
  · exact hexamp

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceAssignedStoppedInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The original-packet local bounds give exactly the amplitude inputs of
`physicalStoppedBoundAt`. The terminal distinguished top may disappear
while other children remain; the actual cell loss is still bounded by
the stopped path loss. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X : Type*} {κ : Type} [Fintype κ]

/-- Local node and off-child estimates transfer to the mass-stopped path
without altering the packet coefficients or the terminal mass convention. -/
theorem source_stopped_local_envelope {Kb : ℕ}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cut : ℝ) (weight : τ → X → ℝ) (hw : ∀ t x, 0 ≤ weight t x)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (phase : ℕ → ℂ) (a : ℝ) (hKb : 0 < Kb) (shift : Fin Kb)
    (top : τ) (x : X) (count : ℕ) (M C CW : ℝ) (hM : 0 ≤ M) (hCW : 0 ≤ CW)
    (hterminal : ¬g.eligible cut (precision top) (ShiftedBlocks.endpoint shift count))
    (hnode : ∀ level cell,
      ‖g.sourcePacketAmplitude tops slope precision cut weight K gap packets assigned stop
        (value x) phase a x level cell‖ ≤ C*g.mass tops slope precision cut weight level cell x)
    (hoff : ∀ lower upper, lower ≤ upper → ∀ s,
      g.mass tops slope precision cut weight lower (g.index lower s) x-
        g.mass tops slope precision cut weight upper (g.index upper s) x < 1 →
      ‖g.sourcePacketAmplitude tops slope precision cut weight K gap
        (packets.filter (fun q => assigned q ∉ g.cellTops tops slope precision cut
          upper (g.index upper s))) assigned stop (value x) phase a x lower (g.index lower s)‖ ≤
        CW*(g.mass tops slope precision cut weight lower (g.index lower s) x-
          g.mass tops slope precision cut weight upper (g.index upper s) x)) :
    let n := g.shiftedPathMass tops slope precision cut weight shift top x
    let finish := firstMassStop n count M
    let amp := g.sourceShiftedPathAmplitude tops slope precision cut weight K gap
      packets assigned stop value phase a shift top x
    let base := g.sourcePacketBase tops slope precision cut weight assigned stop (value x) a x
    let transition := g.sourceTransition tops slope precision cut weight K gap phase x
    let W := fun j => g.packetAmplitude
      (packets.filter (fun q => assigned q ∉ g.cellTops tops slope precision cut
        (ShiftedBlocks.endpoint shift (j+1))
        (g.index (ShiftedBlocks.endpoint shift (j+1)) (slope top))))
      (fun q => slope (assigned q)) stop base transition
      (ShiftedBlocks.endpoint shift j) (g.index (ShiftedBlocks.endpoint shift j) (slope top))
    (∀ j, ‖amp j‖ ≤ C*n j) ∧
      (∀ j < finish, n j-n (j+1) < 1 → ‖W j‖ ≤ CW*(n j-n (j+1))) := by
  dsimp only
  let n := g.shiftedPathMass tops slope precision cut weight shift top x
  have hnlast : n count ≤ M := by
    rw [show n count = 0 from g.shiftedPathMass_terminal_zero tops slope precision
      cut weight shift top count hterminal x]
    exact hM
  constructor
  · intro j
    by_cases he : g.eligible cut (precision top) (ShiftedBlocks.endpoint shift j)
    · simpa only [sourceShiftedPathAmplitude,shiftedPathMass,ite_eq_left he] using
        hnode (ShiftedBlocks.endpoint shift j) (g.index (ShiftedBlocks.endpoint shift j) (slope top))
    · simp only [sourceShiftedPathAmplitude,shiftedPathMass,ite_eq_right he,norm_zero,mul_zero,le_refl]
  · intro j hj hdrop
    have hnpos : 0 < n j := lt_of_le_of_lt hM ((firstMassStop_spec n count M hnlast).2.2 j hj)
    have he := g.shiftedPathMass_ne_zero_eligible tops slope precision cut weight
      shift top x j hnpos.ne'
    have hcell :
        g.mass tops slope precision cut weight (ShiftedBlocks.endpoint shift j)
          (g.index (ShiftedBlocks.endpoint shift j) (slope top)) x-
        g.mass tops slope precision cut weight (ShiftedBlocks.endpoint shift (j+1))
          (g.index (ShiftedBlocks.endpoint shift (j+1)) (slope top)) x ≤ n j-n (j+1) := by
      dsimp only [n]
      rw [shiftedPathMass,ite_eq_left he]
      by_cases hnext : g.eligible cut (precision top) (ShiftedBlocks.endpoint shift (j+1))
      · rw [shiftedPathMass,ite_eq_left hnext]
      · rw [shiftedPathMass,ite_eq_right hnext,sub_zero]
        exact sub_le_self _ (g.mass_nonnegative tops slope precision cut weight hw _ _ x)
    have hb := hoff (ShiftedBlocks.endpoint shift j) (ShiftedBlocks.endpoint shift (j+1))
      ((ShiftedBlocks.endpoint_strictMono hKb shift).monotone (Nat.le_succ j))
      (slope top) (lt_of_le_of_lt hcell hdrop)
    exact hb.trans (mul_le_mul_of_nonneg_left hcell hCW)

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceStoppedMarking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal marks along each spatial path provide the active/drop
and unique-exception hypotheses used by the stopped product theorem. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LipschitzHilbert.AngularGrid

theorem eventually_source_stopped_marking (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ) (hw : 0 < w), 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hK : 0 < SourceParameters.blockCount L) (tag : Fin (SourceParameters.blockCount L))
      (top : ι) (origin y : ℝ),
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
      (div_pos hw (T top).length_pos) hK tag
    let grid := sourceReverseLineGrid g L origin hw tag count
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
      tag top (x,y+(T top).slope*x)
    ∀ x ∈ grid.root,
    let marked := fun j => sourceMarkedCell
      (grid.cell (ShiftedBlocks.reverseLevel tag count (ShiftedBlocks.reverseIndex count j))
        (grid.index (ShiftedBlocks.reverseLevel tag count (ShiftedBlocks.reverseIndex count j)) x).val)
      (fun z => n z j) (fun z => n z j-n z (j+1)) (L^A_M)
    (∀ j < count, marked j → L^A_M < n x j ∧ (1/4:ℝ) ≤ n x j-n x (j+1)) ∧
    (∀ j < count, ¬marked j → 1 ≤ n x j-n x (j+1) →
      n x j ≤ L^A_M+1 ∧ n x (j+1) ≤ L^A_M) := by
  filter_upwards [eventually_source_reverse_cell_marking D A_M hD hAM] with L hmark
  intro ι g tops T w Kw hw hKw hbranch hwidth hK tag top origin y
  dsimp only
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK tag
  let grid := sourceReverseLineGrid g L origin hw tag count
  intro x hx
  have hb (j : ℕ) (hj : j < count) := hmark ι g tops T w Kw hw hKw hbranch hwidth
    hK tag top origin y j hj
  have hc (j : ℕ) : x ∈ grid.cell
      (ShiftedBlocks.reverseLevel tag count (ShiftedBlocks.reverseIndex count j))
      (grid.index (ShiftedBlocks.reverseLevel tag count (ShiftedBlocks.reverseIndex count j)) x).val :=
    (grid.index_eq_iff_mem_cell (ShiftedBlocks.reverseLevel_le tag count _) hx _).mp rfl
  constructor
  · intro j hj hm
    exact (hb j hj _ x (hc j)).1 hm
  · intro j hj hm hd
    exact ⟨((hb j hj _ x (hc j)).2 hm hd).1.le,
      ((hb j hj _ x (hc j)).2 hm hd).2.le⟩

end LipschitzHilbert.AngularGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketDataOriginalParentMarkedPath
attribute [-instance] _root_.OAI.LipschitzHilbert.PacketLatticeData.assignedTopItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual source cell marks and local original-packet estimates
supply the remaining hypotheses of the stopped-path theorem. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_original_parent_marked_path_bound_oai
    (q D Cmass qoff A_M : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) (hCmass : 0 ≤ Cmass)
    (hAM : 0 < A_M) (hchoice : 4*(max (3*q+13) (2*q+17)+3/2) ≤ A_M)
    (Klocal Hlocal : ℕ) :
    ∀ᶠ L : ℝ in atTop, originalParentMarkedPathBoundAt q D Cmass qoff A_M L Klocal Hlocal := by

  filter_upwards [eventually_physical_parent_stopped_bound q D Cmass qoff A_M hq hD hCmass
    hAM hchoice Klocal Hlocal,
    AngularGrid.eventually_source_stopped_marking D A_M hD hAM.le, eventually_ge_atTop (1:ℝ)]
    with L hphysical hmark hL
  unfold originalParentMarkedPathBoundAt
  intro N κ Label Item _ _ P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops T A s w R C F hw hR slope precision
    hbranch hK shift hzero hp top htop hRtop hcone hF hwide hfrequency hparentCone hparentWide
    cut stop weight count phase hz Z Nmass α μ ha ha1 hZ hZL hphase hN hlogN
    hα hα3 hμ hrelation z packets assigned hassigned heligible hangle
    squarePackets Qsquare origSquare squareSelected S Q orig selected hsquareEvent hreference n finish value level transition base W amp
    origin y x hzpoint line mass marked hx hKw hwidth Cex hCex hlog hroot hnode hoff
  subst R
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hprecision : precision top = w/(T top).length := rfl
  have hterminal : ¬grid.eligible cut (precision top) (ShiftedBlocks.endpoint shift count) := by
    rw [hprecision]
    exact grid.firstIneligibleShiftedBlock_spec cut (w/(T top).length) (div_pos hw hR) hK shift
  have hwpos (u : τ) (zz : ℝ×ℝ) : 0 < weight u zz :=
    (T u).weight_pos (zero_lt_one.trans_le hKw) D zz
  have he := grid.source_stopped_local_envelope tops slope precision cut weight
    (fun u zz => (hwpos u zz).le) (SourceParameters.blockCount L) (grid.sourceBoundaryGap L)
    packets assigned (fun u => stop u.1) value phase a hK shift top z count
    (L^A_M) Cex (L^qoff*Real.exp (-L*Real.log L))
    (Real.rpow_nonneg hL0.le _) (by positivity)
    hterminal hnode hoff
  have hm := hmark τ grid tops T w (L^(A+2)) hw hKw hbranch hwidth
    hK shift top origin y
  have hmx := hm x (by simpa only [count,line] using hx)
  have hm0 : ∀ j < count, marked j
      (line.index (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) x).val →
        L^A_M < n j ∧ (1/4:ℝ) ≤ n j-n (j+1) := by
    simpa only [mass,n,hzpoint,count,line,marked,slope,precision,weight,cut] using hmx.1
  have hm1 : ∀ j < count, ¬marked j
      (line.index (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) x).val →
        1 ≤ n j-n (j+1) → n j ≤ L^A_M+1 ∧ n (j+1) ≤ L^A_M := by
    simpa only [mass,n,hzpoint,count,line,marked,slope,precision,weight,cut] using hmx.2
  have hnlast : n count ≤ L^A_M := by
    rw [show n count = 0 from grid.shiftedPathMass_terminal_zero tops slope precision cut
      weight shift top count hterminal z]
    exact Real.rpow_nonneg hL0.le _
  have hfinish : finish ≤ count := (firstMassStop_spec n count (L^A_M) hnlast).1
  have h := hphysical N κ Label Item P horder hP alt hAlt t a d radius hd hradius hlocal
    b hb hb1 hsupp v hv f hf hf1 τ grid tops slope precision T A s w (T top).length C F hw hR
    hbranch hK shift hzero hp top htop hprecision hcone hF hwide hfrequency hparentCone hparentWide
    phase hz Z Nmass α μ ha ha1 hZ hZL hphase hN hlogN hα hα3 hμ hrelation
    z packets assigned hassigned heligible hangle hsquareEvent hreference
    (level count) (fun j => marked j
      (line.index (ShiftedBlocks.reverseLevel shift count (ShiftedBlocks.reverseIndex count j)) x).val)
    Cex le_rfl hCex hlog hroot
    (fun j hj hm => (hm0 j hj hm).1)
    (fun j hj hm => (hm0 j (lt_of_lt_of_le hj hfinish) hm).2)
    (fun j hj _ hd => he.2 j hj hd)
    (fun j hj hm hd => (hm1 j (lt_of_lt_of_le hj hfinish) hm hd).2)
    (fun j hj hm hd => (hm1 j (lt_of_lt_of_le hj hfinish) hm hd).1)
    (fun j _ _ _ => he.1 j)
  simpa only [reverseMarkedValue,FiniteLineGrid.markedValue,hzpoint] using h

end LipschitzHilbert.PacketLatticeData

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PacketLatticeData.eventually_original_parent_marked_path_bound_oai := @OAI.LipschitzHilbert.PacketLatticeData.eventually_original_parent_marked_path_bound_oai
