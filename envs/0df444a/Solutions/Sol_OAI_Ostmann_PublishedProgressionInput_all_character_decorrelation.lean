-- Prove2me | solution 1 for OAI.Ostmann.PublishedProgressionInput.all_character_decorrelation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:59:40.31207+00:00
-- url     : https://prove2.me/submissions/34b37ae0-91c0-4564-8918-a5249bd6f633

import Mathlib
import Definitions.Def_OstmannComplete
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_PublishedProgressionInput_eventual_tested_character_shell_contradiction

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityIncrementTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite density increment for selecting a rich block

A low-density child of a block forces a definite increase in another child.
Iterating cannot exceed a fixed upper density, so a block with no low child
occurs before a bounded depth.
-/

namespace Ostmann

open scoped BigOperators Classical

private theorem density_child_increment {M : ℕ} (hM : 0 < M)
    (x : Fin M → ℝ) (D d : ℝ) (hd : 0 < d) (hD : d ≤ D)
    (hmean : ∑ i, x i = M * D) (hbad : ∃ i, x i < d / 2) :
    ∃ i, D + d / (4 * M) ≤ x i := by
  obtain ⟨i, hi⟩ := hbad
  by_contra! h
  have hsum : (∑ j ∈ Finset.univ.erase i, x j) ≤
      ((Finset.univ.erase i).card : ℝ) * (D + d / (4 * M)) := by
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, (D + d / (4 * M)) :=
        Finset.sum_le_sum (fun j _ => (h j).le)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.erase i).card : ℝ) = (M : ℝ) - 1 := by
    have hh := Finset.card_erase_add_one (Finset.mem_univ i)
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    have hh' : ((Finset.univ.erase i).card : ℝ) + 1 = M := by exact_mod_cast hh
    linarith
  have heq := Finset.sum_erase_add (Finset.univ : Finset (Fin M)) x (Finset.mem_univ i)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (M : ℝ) * (d / (4 * M)) = d / 4 := by field_simp
  rw [hcard] at hsum
  nlinarith [div_nonneg hd.le (by positivity : (0 : ℝ) ≤ 4 * M)]

/-- The fixed increment forces a rich node before the density ceiling is
reached. A node is an actual ordered list of child choices. -/
theorem exists_rich_density_node {M : ℕ} (hM : 0 < M) (H : ℕ)
    (D : List (Fin M) → ℝ) (d U : ℝ) (hd : 0 < d)
    (hroot : d ≤ D [])
    (hmean : ∀ w, w.length < H → (∑ i, D (w ++ [i])) = M * D w)
    (hupper : ∀ w, w.length ≤ H → D w ≤ U)
    (hdepth : U < d + H * (d / (4 * M))) :
    ∃ w : List (Fin M), w.length < H ∧ ∀ i, d / 2 ≤ D (w ++ [i]) := by
  let ε := d / (4 * M)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsteps : ∀ j ≤ H,
      (∃ w : List (Fin M), w.length < j ∧ ∀ i, d / 2 ≤ D (w ++ [i])) ∨
      ∃ w : List (Fin M), w.length = j ∧ d + j * ε ≤ D w := by
    intro j
    induction j with
    | zero => intro _; exact Or.inr ⟨[], rfl, by simpa using hroot⟩
    | succ j ih =>
      intro hj
      rcases ih (by omega) with ⟨w, hw, hgood⟩ | ⟨w, hw, hD⟩
      · exact Or.inl ⟨w, by omega, hgood⟩
      · by_cases hgood : ∀ i, d / 2 ≤ D (w ++ [i])
        · exact Or.inl ⟨w, by omega, hgood⟩
        · have hbad : ∃ i, D (w ++ [i]) < d / 2 := by simpa using hgood
          obtain ⟨i, hi⟩ := density_child_increment hM (fun i => D (w ++ [i])) (D w) d hd
            (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hε.le])
            (hmean w (by omega)) hbad
          right
          refine ⟨w ++ [i], by simp [hw], ?_⟩
          change D w + ε ≤ D (w ++ [i]) at hi
          push_cast
          linarith
  rcases hsteps H le_rfl with h | ⟨w, hw, hD⟩
  · exact h
  · have hu := hupper w hw.le
    exact False.elim (by dsimp [ε] at hD; linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_IntervalDensityTree
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Equal subdivisions of actual intervals

Cumulative mass functions give exact averaging identities on the interval
partition, so the density-increment tree applies to concrete interval masses.
-/

namespace Ostmann

open scoped BigOperators

theorem intervalNode_child {M : ℕ} (a L : ℝ) (w : List (Fin M)) (i : Fin M) :
    intervalNode a L (w ++ [i]) =
      ((intervalNode a L w).1 + (i : ℝ) * ((intervalNode a L w).2 / M),
        (intervalNode a L w).2 / M) := by
  simp only [intervalNode, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem intervalNode_width_pos {M : ℕ} (hM : 0 < M) (a L : ℝ) (hL : 0 < L)
    (w : List (Fin M)) : 0 < (intervalNode a L w).2 := by
  induction w generalizing a L with
  | nil => exact hL
  | cons i w ih =>
    change 0 < (intervalNode (a + (i : ℝ) * (L / M)) (L / M) w).2
    exact ih _ _ (div_pos hL (by exact_mod_cast hM))

private theorem equal_interval_mass_sum {M : ℕ} (hM : 0 < M)
    (φ : ℝ → ℝ) (a L : ℝ) :
    (∑ i : Fin M,
      (φ (a + ((i : ℝ) + 1) * (L / M)) - φ (a + (i : ℝ) * (L / M)))) =
      φ (a + L) - φ a := by
  have hh := Finset.sum_range_sub (fun j : ℕ => φ (a + (j : ℝ) * (L / M))) M
  rw [Finset.sum_range] at hh
  have he : (M : ℝ) * (L / M) = L := by
    have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, he] using hh

theorem intervalNodeDensity_average {M : ℕ} (hM : 0 < M) (φ : ℝ → ℝ)
    (a L : ℝ) (hL : 0 < L) (w : List (Fin M)) :
    (∑ i, intervalNodeDensity φ a L (w ++ [i])) = M * intervalNodeDensity φ a L w := by
  have hW := intervalNode_width_pos hM a L hL w
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [intervalNodeDensity, intervalNode_child]
  have he (i : Fin M) :
      (intervalNode a L w).1 + (i : ℝ) * ((intervalNode a L w).2 / M) +
        (intervalNode a L w).2 / M =
      (intervalNode a L w).1 + ((i : ℝ) + 1) * ((intervalNode a L w).2 / M) := by ring
  simp_rw [he]
  rw [← Finset.sum_div, equal_interval_mass_sum hM]
  field_simp

theorem intervalNode_width {M : ℕ} (_hM : 0 < M) (a L : ℝ) (w : List (Fin M)) :
    (intervalNode a L w).2 = L / (M : ℝ) ^ w.length := by
  induction w generalizing a L with
  | nil => simp [intervalNode]
  | cons i w ih =>
    change (intervalNode (a + (i : ℝ) * (L / M)) (L / M) w).2 = _
    rw [ih, List.length_cons, pow_succ]
    ring

theorem intervalNode_bounds {M : ℕ} (hM : 0 < M) (a L : ℝ) (hL : 0 ≤ L)
    (w : List (Fin M)) :
    a ≤ (intervalNode a L w).1 ∧
      (intervalNode a L w).1 + (intervalNode a L w).2 ≤ a + L := by
  induction w generalizing a L with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons i w ih =>
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hiM : (i : ℝ) + 1 ≤ M := by exact_mod_cast i.isLt
    have hq : 0 ≤ L / M := div_nonneg hL hMr.le
    have hbound := mul_le_mul_of_nonneg_right hiM hq
    have he : (M : ℝ) * (L / M) = L := by field_simp
    rw [he] at hbound
    change a ≤ (intervalNode (a + (i : ℝ) * (L / M)) (L / M) w).1 ∧ _
    have h := ih (a + (i : ℝ) * (L / M)) (L / M) hq
    constructor
    · exact (le_add_of_nonneg_right (mul_nonneg hi0 hq)).trans h.1
    · change (intervalNode (a + (i : ℝ) * (L / M)) (L / M) w).1 +
        (intervalNode (a + (i : ℝ) * (L / M)) (L / M) w).2 ≤ a + L
      linarith [h.2]

theorem intervalNode_width_lower {M : ℕ} (hM : 0 < M) (a L : ℝ) (hL : 0 ≤ L)
    (H : ℕ) (w : List (Fin M)) (hw : w.length ≤ H) :
    L / (M : ℝ) ^ H ≤ (intervalNode a L w).2 := by
  rw [intervalNode_width hM]
  apply div_le_div_of_nonneg_left hL (by positivity)
  exact pow_le_pow_right₀ (by exact_mod_cast hM : (1 : ℝ) ≤ M) hw

/-- A concrete cumulative mass function has a rich interval node once its
root density is positive and all relevant interval densities are bounded. -/
theorem exists_rich_interval_node {M : ℕ} (hM : 0 < M) (H : ℕ)
    (φ : ℝ → ℝ) (a L d U : ℝ) (hL : 0 < L) (hd : 0 < d)
    (hroot : d ≤ (φ (a + L) - φ a) / L)
    (hupper : ∀ w : List (Fin M), w.length ≤ H → intervalNodeDensity φ a L w ≤ U)
    (hdepth : U < d + H * (d / (4 * M))) :
    ∃ w : List (Fin M), w.length < H ∧
      ∀ i, d / 2 ≤ intervalNodeDensity φ a L (w ++ [i]) := by
  apply exists_rich_density_node hM H (intervalNodeDensity φ a L) d U hd
  · exact hroot
  · intro w _
    exact intervalNodeDensity_average hM φ a L hL w
  · exact hupper
  · exact hdepth

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_WeightedIntervalMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cumulative and interval masses of a finite weighted set -/

namespace Ostmann

open scoped BigOperators Classical

theorem weightedCDF_mono (P : Finset ℕ) (x μ : ℕ → ℝ) (hμ : ∀ p ∈ P, 0 ≤ μ p) :
    Monotone (weightedCDF P x μ) := by
  intro a b hab
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2.trans hab⟩
  · intro p hp _
    exact hμ p (Finset.mem_filter.mp hp).1

theorem weightedCDF_sub (P : Finset ℕ) (x μ : ℕ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    weightedCDF P x μ b - weightedCDF P x μ a = weightedIntervalMass P x μ a b := by
  simp only [weightedCDF, weightedIntervalMass, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hpa : x p ≤ a
  · have hpb := hpa.trans hab
    simp [hpa, hpb, not_lt.mpr hpa]
  · by_cases hpb : x p ≤ b <;> simp [hpa, hpb, lt_of_not_ge hpa]

/-- The concrete density on a tree node is its actual weighted interval
mass divided by its interval length. -/
theorem intervalNodeDensity_weightedCDF {M : ℕ} (hM : 0 < M)
    (P : Finset ℕ) (x μ : ℕ → ℝ) (a L : ℝ) (hL : 0 < L) (w : List (Fin M)) :
    intervalNodeDensity (weightedCDF P x μ) a L w =
      weightedIntervalMass P x μ (intervalNode a L w).1
        ((intervalNode a L w).1 + (intervalNode a L w).2) / (intervalNode a L w).2 := by
  rw [intervalNodeDensity, weightedCDF_sub]
  exact le_add_of_nonneg_right (intervalNode_width_pos hM a L hL w).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Basic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sets in Ostmann's inverse Goldbach problem

We use `ℕ` for the manuscript's nonnegative integers. The threshold convention
uses `N ≤ n`; changing finitely many initial values does not affect it.
-/

namespace Ostmann

open scoped symmDiff

/-- Each sufficiently large sum of elements of the summands is prime. -/
theorem EventuallyPrimeSumset.prime_add {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N, ∀ a ∈ A, ∀ b ∈ B, N ≤ a + b → (a + b).Prime := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun a ha b hb hab => (hN (a + b) hab).mp ⟨a, ha, b, hb, rfl⟩⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RichSubintervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every sufficiently long subinterval of a rich grid is rich -/

namespace Ostmann

open scoped BigOperators

private theorem grid_increment_lower (f : ℕ → ℝ) (M : ℕ) (c : ℝ)
    (hstep : ∀ i < M, c ≤ f (i + 1) - f i) (j l : ℕ) (hjl : j ≤ l) (hl : l ≤ M) :
    ((l - j : ℕ) : ℝ) * c ≤ f l - f j := by
  have hiter : ∀ n : ℕ, j + n ≤ M → (n : ℝ) * c ≤ f (j + n) - f j := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hs := hstep (j + n) (by omega)
      rw [Nat.cast_succ]
      have he : j + (n + 1) = j + n + 1 := by omega
      rw [he]
      linarith
  simpa only [Nat.add_sub_of_le hjl] using hiter (l - j) (by omega)

/-- A monotone cumulative mass whose grid cells have density at least `d`
has density at least `d/2` on each internal interval at least four cells long. -/
theorem rich_grid_subinterval (φ : ℝ → ℝ) (hmono : Monotone φ)
    (M : ℕ) (a h d : ℝ) (hh : 0 < h) (hd : 0 ≤ d)
    (hstep : ∀ i : ℕ, i < M →
      d * h ≤ φ (a + ((i : ℝ) + 1) * h) - φ (a + (i : ℝ) * h))
    (u v : ℝ) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ a + M * h)
    (hlong : 4 * h ≤ v - u) :
    (d / 2) * (v - u) ≤ φ v - φ u := by
  let j := ⌈(u - a) / h⌉₊
  let l := ⌊(v - a) / h⌋₊
  have hu0 : 0 ≤ (u - a) / h := div_nonneg (sub_nonneg.mpr hau) hh.le
  have hv0 : 0 ≤ (v - a) / h := div_nonneg (sub_nonneg.mpr (hau.trans huv)) hh.le
  have huj : u ≤ a + (j : ℝ) * h := by
    have hs := (div_le_iff₀ hh).mp (Nat.le_ceil ((u - a) / h))
    linarith
  have hju : a + (j : ℝ) * h < u + h := by
    have hs := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hu0) hh
    have he : ((u - a) / h + 1) * h = u - a + h := by field_simp
    rw [he] at hs
    linarith
  have hlv : a + (l : ℝ) * h ≤ v := by
    have hs := (le_div_iff₀ hh).mp (Nat.floor_le hv0)
    linarith
  have hvl : v < a + ((l : ℝ) + 1) * h := by
    have hs := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one ((v - a) / h))
    linarith
  have hjl : j ≤ l := by
    by_contra! hbad
    have hbad' : (l : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr hbad)
    nlinarith
  have hlM : l ≤ M := by
    have hle : (l : ℝ) ≤ M := by nlinarith
    exact_mod_cast hle
  have hgrid := grid_increment_lower (fun i => φ (a + (i : ℝ) * h)) M (d * h)
    (by intro i hi; simpa only [Nat.cast_add, Nat.cast_one] using hstep i hi) j l hjl hlM
  rw [Nat.cast_sub hjl] at hgrid
  have hgap : (v - u) / 2 ≤ ((l : ℝ) - j) * h := by nlinarith
  have hmass : φ (a + (l : ℝ) * h) - φ (a + (j : ℝ) * h) ≤ φ v - φ u := by
    have hu := hmono huj
    have hv := hmono hlv
    linarith
  have hprod := mul_le_mul_of_nonneg_left hgap hd
  nlinarith

/-- A uniform unit-interval mass bound gives a linear bound, with just one
boundary interval of overhead. -/
theorem cdf_interval_upper (φ : ℝ → ℝ) (hmono : Monotone φ)
    (a₀ A : ℝ) (hA : 0 ≤ A)
    (hunit : ∀ a, a₀ ≤ a → φ (a + 1) - φ a ≤ A)
    (a b : ℝ) (ha : a₀ ≤ a) (hab : a ≤ b) :
    φ b - φ a ≤ A * (b - a + 1) := by
  let N := ⌈b - a⌉₊
  have hN : b ≤ a + (N : ℝ) := by have := Nat.le_ceil (b - a); linarith
  have hNup : (N : ℝ) < b - a + 1 := Nat.ceil_lt_add_one (sub_nonneg.mpr hab)
  have hsum := grid_increment_lower (fun i => -φ (a + (i : ℝ))) N (-A)
    (by
      intro i _
      have h := hunit (a + i) (ha.trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
      push_cast
      rw [add_assoc] at h
      linarith) 0 N (Nat.zero_le _) le_rfl
  simp only [Nat.sub_zero, Nat.cast_zero, add_zero] at hsum
  have hmono' := hmono hN
  nlinarith

/-- A long interval of positive density contains a whole block of any
prescribed fixed length with at least half that density. The only loss is
the final incomplete block. -/
theorem exists_dense_fixed_block (φ : ℝ → ℝ) (a L B d A : ℝ)
    (hL : 0 ≤ L) (hB : 0 < B) (hd : 0 < d) (hA : 0 ≤ A)
    (hupper : ∀ u v, a ≤ u → u ≤ v → v ≤ a + L →
      φ v - φ u ≤ A * (v - u + 1))
    (hroot : d * L ≤ φ (a + L) - φ a)
    (hlarge : 2 * A * (B + 1) < d * L) :
    ∃ b, a ≤ b ∧ b + B ≤ a + L ∧ (d / 2) * B ≤ φ (b + B) - φ b := by
  let N := ⌊L / B⌋₊
  have hNB : (N : ℝ) * B ≤ L :=
    (le_div_iff₀ hB).mp (Nat.floor_le (div_nonneg hL hB.le))
  have hLN : L < ((N : ℝ) + 1) * B :=
    (div_lt_iff₀ hB).mp (Nat.lt_floor_add_one (L / B))
  have htail := hupper (a + N * B) (a + L)
    (le_add_of_nonneg_right (by positivity)) (by linarith) le_rfl
  have hsum : (∑ i ∈ Finset.range N,
      (φ (a + ((i : ℝ) + 1) * B) - φ (a + (i : ℝ) * B))) =
        φ (a + N * B) - φ a := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] using
      Finset.sum_range_sub (fun i : ℕ => φ (a + (i : ℝ) * B)) N
  have hfull : (d / 2) * L < φ (a + N * B) - φ a := by nlinarith
  have hex : ∃ i ∈ Finset.range N,
      (d / 2) * B ≤ φ (a + ((i : ℝ) + 1) * B) - φ (a + (i : ℝ) * B) := by
    by_contra! hn
    have hs := Finset.sum_le_sum (fun i hi => (hn i hi).le)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    rw [hsum] at hs
    nlinarith
  obtain ⟨i, hi, hdense⟩ := hex
  have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hi
  have hlast := mul_le_mul_of_nonneg_right hiN hB.le
  refine ⟨a + (i : ℝ) * B, le_add_of_nonneg_right (by positivity), by linarith, ?_⟩
  simpa only [add_mul, one_mul, add_assoc] using hdense

theorem rich_interval_node_subinterval {M : ℕ} (hM : 0 < M)
    (φ : ℝ → ℝ) (hmono : Monotone φ) (a L d : ℝ) (hL : 0 < L) (hd : 0 ≤ d)
    (w : List (Fin M))
    (hrich : ∀ i, d ≤ intervalNodeDensity φ a L (w ++ [i]))
    (u v : ℝ) (hu : (intervalNode a L w).1 ≤ u) (huv : u ≤ v)
    (hv : v ≤ (intervalNode a L w).1 + (intervalNode a L w).2)
    (hlong : 4 * ((intervalNode a L w).2 / M) ≤ v - u) :
    (d / 2) * (v - u) ≤ φ v - φ u := by
  have hW := intervalNode_width_pos hM a L hL w
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hh := div_pos hW hMr
  apply rich_grid_subinterval φ hmono M (intervalNode a L w).1
    ((intervalNode a L w).2 / M) d hh hd
  · intro i hi
    have hr := hrich ⟨i, hi⟩
    simp only [intervalNodeDensity, intervalNode_child] at hr
    have hr := (le_div_iff₀ hh).mp hr
    simpa only [add_mul, one_mul, add_assoc] using hr
  · exact hu
  · exact huv
  · have he : (M : ℝ) * ((intervalNode a L w).2 / M) = (intervalNode a L w).2 := by
      field_simp
    rwa [he]
  · exact hlong

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Residues
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complementary residue supports

The elementary reduction in §2 of the manuscript. Only the exclusion of
composite sums is used to separate the tail supports at a prime.
-/

namespace Ostmann

/-- The residue-support reduction requires only unboundedness of a summand. -/
theorem tailResidues_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ) :
    (tailResidues A N p).Nonempty := by
  have hnot : ¬ BddAbove A := fun h => hA (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨a, ha, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨(a : ZMod p), a, ⟨ha, hlarge⟩, rfl⟩

theorem negTailResidues_nonempty {B : Set ℕ} (hB : B.Infinite) (N p : ℕ) :
    (negTailResidues B N p).Nonempty := by
  have hnot : ¬ BddAbove B := fun h => hB (Set.finite_iff_bddAbove.mpr h)
  obtain ⟨b, hb, hlarge⟩ := (not_bddAbove_iff.mp hnot) (N + p)
  exact ⟨-(b : ZMod p), b, ⟨hb, hlarge⟩, rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Collision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Elementary collision estimates

These are the finite probability and support-size inequalities used in §2
and in the final collision argument of §3. No analytic estimate is assumed.
-/

namespace Ostmann

open scoped BigOperators

/-- Exact squared distance from uniform probability on a finite support. -/
theorem collision_sub_uniform {α : Type*} (s : Finset α) (μ : α → ℝ)
    (hs : s.Nonempty) (hmass : ∑ x ∈ s, μ x = 1) :
    ∑ x ∈ s, (μ x - 1 / (s.card : ℝ)) ^ 2 =
      (∑ x ∈ s, μ x ^ 2) - 1 / (s.card : ℝ) := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  calc
    ∑ x ∈ s, (μ x - 1 / (s.card : ℝ)) ^ 2 =
        ∑ x ∈ s, (μ x ^ 2 - (2 / (s.card : ℝ)) * μ x +
          (1 / (s.card : ℝ)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x ∈ s, μ x ^ 2) -
          2 * (∑ x ∈ s, μ x) / (s.card : ℝ) +
          (s.card : ℝ) * (1 / (s.card : ℝ)) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by rw [hmass]; field_simp; ring

/-- Disjoint nonempty supports occupying at most `p` residues have combined
collision probability at least `4 / p`. -/
theorem four_div_le_inverse_add_inverse {a b p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ p) :
    4 / p ≤ 1 / a + 1 / b := by
  have hp : 0 < p := lt_of_lt_of_le (add_pos ha hb) hab
  have habpos : 0 < a * b := mul_pos ha hb
  have hnum : 4 * (a * b) ≤ p * (a + b) := by
    nlinarith [sq_nonneg (a - b), mul_nonneg (le_of_lt (add_pos ha hb)) (sub_nonneg.mpr hab)]
  apply (div_le_iff₀ hp).mpr
  have hratio : 4 ≤ (p * (a + b)) / (a * b) := (le_div_iff₀ habpos).mpr hnum
  calc
    4 ≤ p * (a + b) / (a * b) := hratio
    _ = (1 / a + 1 / b) * p := by field_simp; ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeDivisors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-divisor budget in the collision argument

A distinct pair of integers at distance at most `X` contributes at most
`log X` to the sum of `log p` over primes at which it collides. This is the
elementary counting step behind the larger-sieve use in §§2–3.
-/

namespace Ostmann

open scoped BigOperators

/-- The off-diagonal prime-collision budget, in the ordered-pair convention. -/
theorem sum_log_congruent_primes_le_of_sub_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hdiff : y - x ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) := by
  have hpos : 0 < y - x := Nat.sub_pos_of_lt hxy
  have hbudget := sum_log_prime_divisors_le (P.filter (fun p => x ≡ y [MOD p])) hpos
    (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
    (fun p hp => (Finset.mem_filter.mp hp).2.dvd')
  exact hbudget.trans (Real.log_le_log (by exact_mod_cast hpos)
    (by exact_mod_cast hdiff))

/-- The collision budget for a pair in the initial interval `[0,X]`. -/
theorem sum_log_congruent_primes_le (P : Finset ℕ) {x y X : ℕ}
    (hxy : x < y) (hy : y ≤ X) (hprime : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P.filter (fun p => x ≡ y [MOD p]), Real.log (p : ℝ) ≤
      Real.log (X : ℝ) :=
  sum_log_congruent_primes_le_of_sub_le P hxy ((Nat.sub_le y x).trans hy) hprime

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_WeightedCollision
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weighted prime collisions

The elementary weighted pair count used in Lemma 2.5 (collision stability).
The diagonal is paid for by the largest atom; unequal pairs are paid for by
one logarithm of the interval length.
-/

namespace Ostmann

open scoped BigOperators

theorem primeCollisionWeight_self (P : Finset ℕ) (a : ℕ) :
    primeCollisionWeight P a a = ∑ p ∈ P, Real.log (p : ℝ) := by
  simp [primeCollisionWeight, Nat.ModEq.refl]

theorem primeCollisionWeight_symm (P : Finset ℕ) (a b : ℕ) :
    primeCollisionWeight P a b = primeCollisionWeight P b a := by
  unfold primeCollisionWeight
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _ => ⟨fun h => h.symm, fun h => h.symm⟩)

theorem primeCollisionWeight_le_log {P : Finset ℕ} {a b X : ℕ}
    (hab : a ≠ b) (ha : a ≤ X) (hb : b ≤ X) (hP : ∀ p ∈ P, p.Prime) :
    primeCollisionWeight P a b ≤ Real.log (X : ℝ) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact sum_log_congruent_primes_le P hab hb hP
  · rw [primeCollisionWeight_symm]
    exact sum_log_congruent_primes_le P hba ha hP

/-- The weighted pair count from an off-diagonal logarithmic budget. -/
theorem weighted_prime_collision_bound_of_budget (P S : Finset ℕ) (μ : ℕ → ℝ) (L m : ℝ)
    (hL : 0 ≤ L) (hP : ∀ p ∈ P, p.Prime) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m)
    (hbudget : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → primeCollisionWeight P a b ≤ L) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      L + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  classical
  let W : ℝ := ∑ p ∈ P, Real.log (p : ℝ)
  have hW : 0 ≤ W := Finset.sum_nonneg (fun p hp => Real.log_nonneg (by exact_mod_cast (hP p hp).one_le))
  have hpair : ∀ a ∈ S, ∀ b ∈ S,
      primeCollisionWeight P a b ≤ L + if a = b then W else 0 := by
    intro a ha b hb
    by_cases hab : a = b
    · subst b
      simp only [primeCollisionWeight_self, ite_true, if_true]
      dsimp [W] at *
      linarith
    · simpa [hab] using hbudget a ha b hb hab
  have hsquares : (∑ a ∈ S, μ a ^ 2) ≤ m := by
    calc
      (∑ a ∈ S, μ a ^ 2) ≤ ∑ a ∈ S, m * μ a := by
        apply Finset.sum_le_sum
        intro a ha
        nlinarith [hμ a ha, hatom a ha]
      _ = m := by rw [← Finset.mul_sum, hmass, mul_one]
  calc
    _ ≤ ∑ a ∈ S, ∑ b ∈ S, μ a * μ b * (L + if a = b then W else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hpair a ha b hb) (mul_nonneg (hμ a ha) (hμ b hb))
    _ = L + W * ∑ a ∈ S, μ a ^ 2 := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hconstant : (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * L) = L := by
        calc
          _ = ∑ a ∈ S, μ a * (∑ b ∈ S, μ b) * L := by
            apply Finset.sum_congr rfl
            intro a _
            rw [← Finset.sum_mul, ← Finset.mul_sum]
          _ = L := by
            rw [hmass]
            simp only [mul_one]
            rw [← Finset.sum_mul, hmass, one_mul]
      rw [hconstant]
      congr 1
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq]
      calc
        (∑ a ∈ S, if a ∈ S then μ a * μ a * W else 0) =
            ∑ a ∈ S, W * μ a ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [ha, ite_true, if_true]
          ring
        _ = W * ∑ a ∈ S, μ a ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ L + W * m := add_le_add_right (mul_le_mul_of_nonneg_left hsquares hW) L
    _ = _ := by dsimp [W]; ring

/-- Weighted larger-sieve pair bound on the interval `[0,X]`. -/
theorem weighted_prime_collision_bound (P S : Finset ℕ) (μ : ℕ → ℝ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ a ∈ S, a ≤ X) (hμ : ∀ a ∈ S, 0 ≤ μ a)
    (hmass : ∑ a ∈ S, μ a = 1) (hatom : ∀ a ∈ S, μ a ≤ m) :
    (∑ a ∈ S, ∑ b ∈ S, μ a * μ b * primeCollisionWeight P a b) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) :=
  weighted_prime_collision_bound_of_budget P S μ (Real.log X) m
    (Real.log_nonneg (by exact_mod_cast hX)) hP hμ hmass hatom
    (fun a ha b hb hab => primeCollisionWeight_le_log hab (hS a ha) (hS b hb) hP)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Projection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residue projection of finite probability measures

These identities connect the pair count in `WeightedCollision` with the
collision norm of a projected measure, as used in Lemma 2.5 of the paper.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_fiberMass_mul {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β) (F : β → ℝ)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y * F y = ∑ a ∈ s, μ a * F (f a) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to hf (fun a => μ a * F (f a))]
  apply Finset.sum_congr rfl
  intro y _
  unfold fiberMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

theorem sum_fiberMass {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, fiberMass s μ f y = ∑ a ∈ s, μ a := by
  simpa only [mul_one] using sum_fiberMass_mul s t μ f (fun _ => 1) hf

theorem sum_fiberMass_sq {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : Finset β) (μ : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) :
    ∑ y ∈ t, (fiberMass s μ f y) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if f a = f b then μ a * μ b else 0 := by
  classical
  simp only [pow_two]
  rw [sum_fiberMass_mul s t μ f (fiberMass s μ f) hf]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiberMass, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro b _
  simp only [eq_comm]

theorem residueMass_sq (s : Finset ℕ) (μ : ℕ → ℝ) {p : ℕ}
    (hp : 0 < p) :
    ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, if a ≡ b [MOD p] then μ a * μ b else 0 :=
  sum_fiberMass_sq s (Finset.range p) μ (fun a => a % p)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt a hp))

/-- Reorder the weighted residue collisions as a sum over integer pairs. -/
theorem weighted_residueMass_sq (P s : Finset ℕ) (μ : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) =
    ∑ a ∈ s, ∑ b ∈ s, μ a * μ b * primeCollisionWeight P a b := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ a ∈ s, ∑ b ∈ s,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [residueMass_sq s μ (hP p hp).pos]
      simp only [Finset.mul_sum]
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ p ∈ P,
        Real.log (p : ℝ) * (if a ≡ b [MOD p] then μ a * μ b else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [primeCollisionWeight, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring

/-- The quantitative weighted collision bound for projected probabilities. -/
theorem residue_collision_bound (P s : Finset ℕ) (μ : ℕ → ℝ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ a ∈ s, a ≤ X) (hμ : ∀ a ∈ s, 0 ≤ μ a)
    (hmass : ∑ a ∈ s, μ a = 1) (hatom : ∀ a ∈ s, μ a ≤ m) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  rw [weighted_residueMass_sq P s μ hP]
  exact weighted_prime_collision_bound P s μ X m hX hP hs hμ hmass hatom

/-- Residue labels may be changed (in particular, negated) without changing
the collision norm, provided they identify exactly the congruent pairs. -/
theorem fiberMass_sq_eq_residueMass_sq (s t : Finset ℕ) (μ : ℕ → ℝ)
    (f : ℕ → ℕ) {p : ℕ} (hp : 0 < p)
    (hf : ∀ a ∈ s, f a ∈ t)
    (hcongr : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ a ≡ b [MOD p]) :
    (∑ r ∈ t, (fiberMass s μ f r) ^ 2) =
      ∑ r ∈ Finset.range p, (residueMass s μ p r) ^ 2 := by
  rw [sum_fiberMass_sq s t μ f hf, residueMass_sq s μ hp]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [hcongr a ha b hb]

/-- The weighted pair bound applies on any chosen residue support, including
the negative residue support of the second summand. -/
theorem fiber_collision_bound (P s : Finset ℕ) (μ : ℕ → ℝ)
    (t : ℕ → Finset ℕ) (f : ℕ → ℕ → ℕ) (X : ℕ) (m : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hs : ∀ a ∈ s, a ≤ X) (hμ : ∀ a ∈ s, 0 ≤ μ a)
    (hmass : ∑ a ∈ s, μ a = 1) (hatom : ∀ a ∈ s, μ a ≤ m)
    (hf : ∀ p ∈ P, ∀ a ∈ s, f p a ∈ t p)
    (hcongr : ∀ p ∈ P, ∀ a ∈ s, ∀ b ∈ s, f p a = f p b ↔ a ≡ b [MOD p]) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      ∑ r ∈ t p, (fiberMass s μ (f p) r) ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ) := by
  convert residue_collision_bound P s μ X m hX hP hs hμ hmass hatom using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro p hp
  rw [fiberMass_sq_eq_residueMass_sq s (t p) μ (f p) (hP p hp).pos
    (hf p hp) (hcongr p hp)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Stability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite collision-stability inequality

This is the finite quantitative calculation in Lemma 2.5 of the manuscript.
The final theorem takes the exact numerical consequences of Chebyshev's
bound and Mertens' first theorem at the chosen cutoff as explicit hypotheses.
No main theorem of the manuscript is assumed here.
-/

namespace Ostmann

open scoped BigOperators

theorem collisionDefect_nonneg {p : ℕ} (s t : Finset ℕ) (μ ν : ℕ → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty) (hcard : s.card + t.card ≤ p) :
    0 ≤ collisionDefect p s t μ ν := by
  have hspos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hcard' : (s.card : ℝ) + t.card ≤ p := by exact_mod_cast hcard
  have hgap := four_div_le_inverse_add_inverse hspos htpos hcard'
  have hμ : 0 ≤ ∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hν : 0 ≤ ∑ r ∈ t, (ν r - 1 / (t.card : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold collisionDefect
  linarith

theorem collisionDefect_eq (p : ℕ) (s t : Finset ℕ) (μ ν : ℕ → ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hμ : ∑ r ∈ s, μ r = 1) (hν : ∑ r ∈ t, ν r = 1) :
    collisionDefect p s t μ ν =
      (∑ r ∈ s, μ r ^ 2) + (∑ r ∈ t, ν r ^ 2) - 4 / (p : ℝ) := by
  unfold collisionDefect
  rw [collision_sub_uniform s μ hs hμ, collision_sub_uniform t ν ht hν]
  ring

/-- The sum of stability defects is the sum of the collision energies minus
the universal baseline `4 ∑ log p / p`. -/
theorem weighted_collisionDefect_eq (P : Finset ℕ) (s t : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hμ : ∀ p ∈ P, ∑ r ∈ s p, μ p r = 1)
    (hν : ∀ p ∈ P, ∑ r ∈ t p, ν p r = 1) :
    (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (s p) (t p) (μ p) (ν p)) =
      (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) +
      (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) -
      4 * ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ) := by
  calc
    _ = ∑ p ∈ P,
        ((Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) +
        (Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) -
        4 * (Real.log (p : ℝ) / (p : ℝ))) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [collisionDefect_eq p (s p) (t p) (μ p) (ν p)
        (hs p hp) (ht p hp) (hμ p hp) (hν p hp)]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- A finite, explicit form of collision stability. The two energy bounds
come from `residue_collision_bound`; the last two hypotheses are exactly
the prime-sum estimates needed at the cutoff, rather than full asymptotic
theories. Mertens' first theorem (1874) supplies the lower prime sum. -/
theorem collision_stability_of_prime_sums (P : Finset ℕ)
    (s t : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ)
    (X Q : ℕ) (m K C : ℝ)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hμ : ∀ p ∈ P, ∑ r ∈ s p, μ p r = 1)
    (hν : ∀ p ∈ P, ∑ r ∈ t p, ν p r = 1)
    (hm : 0 ≤ m)
    (henergyμ : (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ s p, μ p r ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ))
    (henergyν : (∑ p ∈ P, Real.log (p : ℝ) * ∑ r ∈ t p, ν p r ^ 2) ≤
      Real.log (X : ℝ) + m * ∑ p ∈ P, Real.log (p : ℝ))
    (hchebyshev : (∑ p ∈ P, Real.log (p : ℝ)) ≤ K * Q)
    (hmertens : Real.log (Q : ℝ) - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) :
    (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (s p) (t p) (μ p) (ν p)) ≤
      2 * Real.log (X : ℝ) - 4 * Real.log (Q : ℝ) + 4 * C + 2 * m * K * Q := by
  rw [weighted_collisionDefect_eq P s t μ ν hs ht hμ hν]
  have hweight := mul_le_mul_of_nonneg_left hchebyshev hm
  nlinarith

/-- Apply the stability inequality to two actual finite measures on integers.
The maps `f` and `g` label their residue classes; allowing a relabeling is
needed for the negative second summand. The prime-sum hypotheses are the
finite specializations of the published inputs used here. -/
theorem finite_measure_collision_stability (P A B : Finset ℕ)
    (μ ν : ℕ → ℝ) (s t : ℕ → Finset ℕ) (f g : ℕ → ℕ → ℕ)
    (X Q : ℕ) (m K C : ℝ)
    (hX : 1 ≤ X) (hP : ∀ p ∈ P, p.Prime)
    (hA : ∀ a ∈ A, a ≤ X) (hB : ∀ b ∈ B, b ≤ X)
    (hμ : ∀ a ∈ A, 0 ≤ μ a) (hν : ∀ b ∈ B, 0 ≤ ν b)
    (hmassμ : ∑ a ∈ A, μ a = 1) (hmassν : ∑ b ∈ B, ν b = 1)
    (hatomμ : ∀ a ∈ A, μ a ≤ m) (hatomν : ∀ b ∈ B, ν b ≤ m)
    (hs : ∀ p ∈ P, (s p).Nonempty) (ht : ∀ p ∈ P, (t p).Nonempty)
    (hf : ∀ p ∈ P, ∀ a ∈ A, f p a ∈ s p)
    (hg : ∀ p ∈ P, ∀ b ∈ B, g p b ∈ t p)
    (hcongrf : ∀ p ∈ P, ∀ a ∈ A, ∀ b ∈ A, f p a = f p b ↔ a ≡ b [MOD p])
    (hcongrg : ∀ p ∈ P, ∀ a ∈ B, ∀ b ∈ B, g p a = g p b ↔ a ≡ b [MOD p])
    (hm : 0 ≤ m)
    (hchebyshev : (∑ p ∈ P, Real.log (p : ℝ)) ≤ K * Q)
    (hmertens : Real.log (Q : ℝ) - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) :
    (∑ p ∈ P, Real.log (p : ℝ) *
      collisionDefect p (s p) (t p) (fiberMass A μ (f p)) (fiberMass B ν (g p))) ≤
      2 * Real.log (X : ℝ) - 4 * Real.log (Q : ℝ) + 4 * C + 2 * m * K * Q := by
  apply collision_stability_of_prime_sums P s t
    (fun p => fiberMass A μ (f p)) (fun p => fiberMass B ν (g p))
    X Q m K C hs ht
  · intro p hp
    rw [sum_fiberMass A (s p) μ (f p) (hf p hp)]
    exact hmassμ
  · intro p hp
    rw [sum_fiberMass B (t p) ν (g p) (hg p hp)]
    exact hmassν
  · exact hm
  · exact fiber_collision_bound P A μ s f X m hX hP hA hμ hmassμ hatomμ hf hcongrf
  · exact fiber_collision_bound P B ν t g X m hX hP hB hν hmassν hatomν hg hcongrg
  · exact hchebyshev
  · exact hmertens

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailStability
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collision stability on the two summand tails

This specializes the finite collision bound to the complementary supports
forced by an eventual prime decomposition. Prime-sum estimates remain
explicit hypotheses; no statement about the existence of a decomposition
is assumed as an analytic input.
-/

namespace Ostmann

open scoped BigOperators

theorem negativeResidue_eq_iff {p a b : ℕ} (hp : 0 < p) :
    negativeResidue p a = negativeResidue p b ↔ a ≡ b [MOD p] := by
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  unfold negativeResidue
  rw [(ZMod.val_injective p).eq_iff, neg_inj, ZMod.natCast_eq_natCast_iff]

theorem tailSupport_subset (A : Set ℕ) (N p : ℕ) :
    tailSupport A N p ⊆ Finset.range p := by
  classical
  exact Finset.filter_subset _ _

theorem mod_mem_tailSupport {A : Set ℕ} {N p a : ℕ} (hp : 0 < p)
    (ha : a ∈ A) (hlarge : N + p < a) : a % p ∈ tailSupport A N p := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt a hp), ?_⟩
  have heq : ((a % p : ℕ) : ZMod p) = (a : ZMod p) := by simp
  rw [heq]
  exact ⟨a, ⟨ha, hlarge⟩, rfl⟩

theorem tailSupport_nonempty {A : Set ℕ} (hA : A.Infinite) (N p : ℕ)
    (hp : 0 < p) : (tailSupport A N p).Nonempty := by
  obtain ⟨_, a, ⟨ha, hlarge⟩, rfl⟩ := tailResidues_nonempty hA N p
  exact ⟨a % p, mod_mem_tailSupport hp ha hlarge⟩

theorem negativeResidue_mem_complement {A B : Set ℕ} {N p b : ℕ}
    (hp : 0 < p) (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p))
    (hb : b ∈ B) (hlarge : N + p < b) :
    negativeResidue p b ∈ Finset.range p \ tailSupport A N p := by
  classical
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
  intro hmem
  have ha := (Finset.mem_filter.mp hmem).2
  change ((-(b : ZMod p)).val : ZMod p) ∈ tailResidues A N p at ha
  rw [ZMod.natCast_zmod_val] at ha
  exact Set.disjoint_left.mp hdisjoint ha ⟨b, ⟨hb, hlarge⟩, rfl⟩

theorem tailSupport_complement_nonempty {A B : Set ℕ} (hB : B.Infinite)
    {N p : ℕ} (hp : 0 < p)
    (hdisjoint : Disjoint (tailResidues A N p) (negTailResidues B N p)) :
    (Finset.range p \ tailSupport A N p).Nonempty := by
  obtain ⟨_, b, ⟨hb, hlarge⟩, rfl⟩ := negTailResidues_nonempty hB N p
  exact ⟨negativeResidue p b, negativeResidue_mem_complement hp hdisjoint hb hlarge⟩

theorem tailSupport_card_add_complement (A : Set ℕ) (N p : ℕ) :
    (tailSupport A N p).card + (Finset.range p \ tailSupport A N p).card = p := by
  rw [Nat.add_comm, Finset.card_sdiff_add_card_eq_card (tailSupport_subset A N p)]
  exact Finset.card_range p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeSumInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators

theorem prime_log_weight_le (Q : ℕ) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ)) ≤ Real.log 4 * Q := by
  rw [← Chebyshev.theta_eq_sum_primesLE_log]
  exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg Q)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensPrimeBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact published Mertens input for logarithmic prime bands

F. Mertens, J. reine angew. Math. 78 (1874), 46–62, first theorem,
DOI 10.1515/crll.1874.78.46. Both sides of the bounded-error estimate
are needed to subtract the lower cutoff; the collision argument uses
only its previously recorded lower-bound consequence.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem MertensEstimate.lower {C : ℝ} (h : MertensEstimate C) : MertensLowerBound C := by
  intro Q hQ
  have hh := (abs_le.mp (h Q hQ)).1
  linarith

theorem MertensEstimate.upper {C : ℝ} (h : MertensEstimate C) (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) ≤ Real.log Q + C := by
  have hh := (abs_le.mp (h Q hQ)).2
  linarith

theorem floor_exp_log_bounds (T : ℝ) (hT : 1 ≤ T) :
    1 ≤ ⌊Real.exp T⌋₊ ∧ T - Real.log 2 ≤ Real.log (⌊Real.exp T⌋₊ : ℝ) ∧
      Real.log (⌊Real.exp T⌋₊ : ℝ) ≤ T := by
  have he : 2 ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfloor : (1 : ℕ) ≤ ⌊Real.exp T⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (by linarith)
  have hfp : (0 : ℝ) < ⌊Real.exp T⌋₊ := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hfloor)
  have hhalf : Real.exp T / 2 ≤ (⌊Real.exp T⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor (Real.exp T)
    linarith
  have hlo := Real.log_le_log (show 0 < Real.exp T / 2 by positivity) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlo
  have hhi := Real.log_le_log hfp (Nat.floor_le (Real.exp_nonneg T))
  rw [Real.log_exp] at hhi
  exact ⟨hfloor, hlo, hhi⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogLogIntervalMass
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform harmonic mass bounds in the iterated-log coordinate

Only the upper half of the already recorded Mertens input is needed here.
The constant need not be sharp: a uniform density ceiling suffices for the
finite density-increment selection.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem prime_loglog_unit_mass_upper {C : ℝ} (hM : MertensEstimate C)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℝ) (ha : max C 0 ≤ a) :
    weightedIntervalMass P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
      a (a + 1) ≤ Real.exp 1 + 1 := by
  let S := P.filter (fun p : ℕ => a < Real.log (Real.log (p : ℝ)) ∧
    Real.log (Real.log (p : ℝ)) ≤ a + 1)
  let Q := ⌊Real.exp (Real.exp (a + 1))⌋₊
  have hQ : 1 ≤ Q := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp (Real.exp_nonneg _))
  have hsub : S ⊆ Nat.primesLE Q := by
    intro p hp
    obtain ⟨hp, hlo, hhi⟩ := Finset.mem_filter.mp hp
    have hprime := hP p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    have hlogup : Real.log p ≤ Real.exp (a + 1) := (Real.log_le_iff_le_exp hlog).mp hhi
    have hpup : (p : ℝ) ≤ Real.exp (Real.exp (a + 1)) :=
      (Real.log_le_iff_le_exp hp0).mp hlogup
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hpup, hprime⟩
  have hlogQ : Real.log (Q : ℝ) ≤ Real.exp (a + 1) := by
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    have h := Real.log_le_log hQpos (Nat.floor_le (Real.exp_nonneg (Real.exp (a + 1))))
    simpa only [Real.log_exp] using h
  have hweight : (∑ p ∈ S, Real.log (p : ℝ) / p) ≤ Real.exp (a + 1) + C := by
    apply le_trans _ ((hM.upper Q hQ).trans (by linarith : Real.log Q + C ≤ Real.exp (a + 1) + C))
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hmul : Real.exp a * (∑ p ∈ S, (p : ℝ)⁻¹) ≤
      ∑ p ∈ S, Real.log (p : ℝ) / p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hp, hlo, _⟩ := Finset.mem_filter.mp hp
    have hprime := hP p hp
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    have he : Real.exp a ≤ Real.log (p : ℝ) :=
      ((Real.lt_log_iff_exp_lt hlog).mp hlo).le
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (p : ℝ)⁻¹)
  have hC : C ≤ Real.exp a := by
    have hc := (le_max_left C 0).trans ha
    linarith [Real.add_one_le_exp a]
  change (∑ p ∈ S, (p : ℝ)⁻¹) ≤ _
  rw [Real.exp_add] at hweight
  nlinarith [Real.exp_pos a]

/-- This applies to every subset of the primes, uniformly in its choice. -/
theorem prime_loglog_interval_mass_upper {C : ℝ} (hM : MertensEstimate C)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a b : ℝ) (ha : max C 0 ≤ a) (hab : a ≤ b) :
    weightedIntervalMass P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
      a b ≤ (Real.exp 1 + 1) * (b - a + 1) := by
  let φ := weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
  have hmono : Monotone φ := weightedCDF_mono _ _ _ (by intros; positivity)
  have h := cdf_interval_upper φ hmono (max C 0) (Real.exp 1 + 1) (by positivity)
    (by
      intro u hu
      rw [weightedCDF_sub _ _ _ u (u + 1) (by linarith)]
      exact prime_loglog_unit_mass_upper hM P hP u hu) a b ha hab
  rwa [weightedCDF_sub _ _ _ a b hab] at h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeRichBlock
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A rich upper block with finitely many possible scales -/

namespace Ostmann

open scoped BigOperators

/-- The number of density increments depends on the initial density and
subdivision ratio, and is independent of the requested minimum block scale. -/
theorem exists_prime_rich_block {C : ℝ} (hMertens : MertensEstimate C)
    (M : ℕ) (hM : 0 < M) (d : ℝ) (hd : 0 < d) :
    ∃ H : ℕ, ∀ (K : ℕ), 1 ≤ K → ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ a : ℝ, max C 0 ≤ a →
      d * (5 * K * (M : ℝ) ^ H) ≤
        weightedIntervalMass P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
          a (a + 5 * K * (M : ℝ) ^ H) →
      ∃ (j : ℕ) (U : ℝ), j ≤ H ∧ a ≤ U ∧
        U + 5 * K * (M : ℝ) ^ j ≤ a + 5 * K * (M : ℝ) ^ H ∧
        ∀ u v : ℝ, U ≤ u → u ≤ v → v ≤ U + 5 * K * (M : ℝ) ^ j →
          4 * (5 * K * (M : ℝ) ^ j / M) ≤ v - u →
          (d / 4) * (v - u) ≤
            weightedIntervalMass P (fun p => Real.log (Real.log p))
              (fun p => (p : ℝ)⁻¹) u v := by
  let A := Real.exp 1 + 1
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hstep : 0 < d / (4 * M) := by positivity
  obtain ⟨H, hH⟩ := exists_nat_gt ((2 * A - d) / (d / (4 * M)))
  have hdepth : 2 * A < d + H * (d / (4 * M)) := by
    have h := (div_lt_iff₀ hstep).mp hH
    linarith
  refine ⟨H, ?_⟩
  intro K hK P hP a ha hroot
  let L := 5 * (K : ℝ) * (M : ℝ) ^ H
  let φ := weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hL : 0 < L := by dsimp [L]; positivity
  have hmono : Monotone φ := weightedCDF_mono _ _ _ (by intros; positivity)
  have hroot' : d ≤ (φ (a + L) - φ a) / L := by
    apply (le_div_iff₀ hL).mpr
    rw [weightedCDF_sub _ _ _ a (a + L) (by linarith)]
    exact hroot
  have hupper : ∀ w : List (Fin M), w.length ≤ H → intervalNodeDensity φ a L w ≤ 2 * A := by
    intro w hw
    have hwidth := intervalNode_width_pos hM a L hL w
    have hbound := intervalNode_bounds hM a L hL.le w
    have hwl := intervalNode_width_lower hM a L hL.le H w hw
    have he : L / (M : ℝ) ^ H = 5 * K := by dsimp [L]; field_simp
    rw [he] at hwl
    have hW1 : 1 ≤ (intervalNode a L w).2 := by
      have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    have hm := prime_loglog_interval_mass_upper hMertens P hP
      (intervalNode a L w).1 ((intervalNode a L w).1 + (intervalNode a L w).2)
      (ha.trans hbound.1) (by linarith)
    rw [intervalNodeDensity_weightedCDF hM P _ _ a L hL w]
    apply (div_le_iff₀ hwidth).mpr
    dsimp [A] at *
    nlinarith [Real.exp_pos 1]
  obtain ⟨w, hw, hgood⟩ := exists_rich_interval_node hM H φ a L d (2 * A)
    hL hd hroot' hupper hdepth
  let j := H - w.length
  have hpow : (M : ℝ) ^ H = (M : ℝ) ^ j * (M : ℝ) ^ w.length := by
    rw [← pow_add]
    congr 1
    dsimp [j]
    omega
  have hwidth : (intervalNode a L w).2 = 5 * K * (M : ℝ) ^ j := by
    rw [intervalNode_width hM]
    dsimp [L]
    rw [hpow]
    field_simp
  have hbound := intervalNode_bounds hM a L hL.le w
  refine ⟨j, (intervalNode a L w).1, Nat.sub_le _ _, hbound.1, ?_, ?_⟩
  · simpa only [hwidth] using hbound.2
  · intro u v hu huv hv hlong
    have hh := rich_interval_node_subinterval hM φ hmono a L (d / 2) hL (by positivity)
      w hgood u v hu huv (by rwa [hwidth]) (by rwa [hwidth])
    rw [weightedCDF_sub _ _ _ u v huv] at hh
    convert hh using 1 <;> first | rfl | ring

/-- The selected block comes from the original long prime interval; a
positive-density starting block is constructed by averaging. -/
theorem exists_rich_prime_subblock {C : ℝ} (hMertens : MertensEstimate C)
    (M : ℕ) (hM : 0 < M) (d : ℝ) (hd : 0 < d) :
    ∃ H : ℕ, ∀ (K : ℕ), 1 ≤ K → ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ a L : ℝ, max C 0 ≤ a → 0 ≤ L →
      2 * (Real.exp 1 + 1) * (5 * K * (M : ℝ) ^ H + 1) < d * L →
      d * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
        (fun p => (p : ℝ)⁻¹) a (a + L) →
      ∃ (j : ℕ) (U : ℝ), j ≤ H ∧ a ≤ U ∧
        U + 5 * K * (M : ℝ) ^ j ≤ a + L ∧
        ∀ u v : ℝ, U ≤ u → u ≤ v → v ≤ U + 5 * K * (M : ℝ) ^ j →
          4 * (5 * K * (M : ℝ) ^ j / M) ≤ v - u →
          (d / 8) * (v - u) ≤
            weightedIntervalMass P (fun p => Real.log (Real.log p))
              (fun p => (p : ℝ)⁻¹) u v := by
  obtain ⟨H, hH⟩ := exists_prime_rich_block hMertens M hM (d / 2) (by positivity)
  refine ⟨H, ?_⟩
  intro K hK P hP a L ha hL hlarge hroot
  let B := 5 * (K : ℝ) * (M : ℝ) ^ H
  let φ := weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
  have hB : 0 < B := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    dsimp [B]
    positivity
  have hroot' : d * L ≤ φ (a + L) - φ a := by
    rwa [weightedCDF_sub _ _ _ a (a + L) (by linarith)]
  obtain ⟨b, hab, hbL, hb⟩ := exists_dense_fixed_block φ a L B d (Real.exp 1 + 1)
    hL hB hd (by positivity)
    (by
      intro u v hu huv _
      rw [weightedCDF_sub _ _ _ u v huv]
      exact prime_loglog_interval_mass_upper hMertens P hP u v (ha.trans hu) huv)
    hroot' hlarge
  rw [weightedCDF_sub _ _ _ b (b + B) (by linarith)] at hb
  obtain ⟨j, U, hj, hbU, hUb, hgood⟩ := hH K hK P hP b (ha.trans hab) hb
  refine ⟨j, U, hj, hab.trans hbU, hUb.trans hbL, ?_⟩
  intro u v hu huv hv hlen
  have h := hgood u v hu huv hv hlen
  convert h using 1 <;> first | rfl | ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RichGridShell
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole rich unit shells on one fixed grid -/

namespace Ostmann

open scoped BigOperators

theorem exists_rich_grid_shell (φ : ℝ → ℝ) (hmono : Monotone φ)
    (U A d u v : ℝ) (hA : 0 < A) (hd : 0 ≤ d) (hUu : U ≤ u)
    (hlen : 4 ≤ v - u) (hlarge : 8 * A ≤ d * (v - u))
    (hunit : ∀ a, U ≤ a → φ (a + 1) - φ a ≤ A)
    (hmass : d * (v - u) ≤ φ v - φ u) :
    ∃ n : ℕ, u ≤ U + n ∧ U + n + 1 ≤ v ∧
      d / 2 ≤ φ (U + n + 1) - φ (U + n) := by
  let j := ⌈u - U⌉₊
  let l := ⌊v - U⌋₊
  have huv : u ≤ v := by linarith
  have huj : u ≤ U + (j : ℝ) := by have := Nat.le_ceil (u - U); linarith
  have hju : U + (j : ℝ) < u + 1 := by
    have := Nat.ceil_lt_add_one (sub_nonneg.mpr hUu)
    change (j : ℝ) < u - U + 1 at this
    linarith
  have hlv : U + (l : ℝ) ≤ v := by
    have := Nat.floor_le (show 0 ≤ v - U by linarith)
    change (l : ℝ) ≤ v - U at this
    linarith
  have hvl : v < U + (l : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (v - U)
    change v - U < (l : ℝ) + 1 at this
    linarith
  have hjl : j ≤ l := by
    by_contra! hbad
    have hbad' : (l : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr hbad)
    linarith
  have hleft : φ (U + j) - φ u ≤ A := by
    have h := hunit u hUu
    have hm := hmono hju.le
    linarith
  have hright : φ v - φ (U + l) ≤ A := by
    have h := hunit (U + l) (le_add_of_nonneg_right (Nat.cast_nonneg _))
    have hm := hmono hvl.le
    linarith
  have hN : ((l - j : ℕ) : ℝ) ≤ v - u := by rw [Nat.cast_sub hjl]; linarith
  by_contra! hn
  have hsmall (i : ℕ) (hi : i ∈ Finset.range (l - j)) :
      φ (U + ((j + i : ℕ) : ℝ) + 1) - φ (U + ((j + i : ℕ) : ℝ)) ≤ d / 2 := by
    have hi' := Finset.mem_range.mp hi
    have hij : (j : ℝ) ≤ (j + i : ℕ) := by exact_mod_cast (Nat.le_add_right j i)
    have hil : ((j + i : ℕ) : ℝ) + 1 ≤ l := by
      exact_mod_cast (show j + i + 1 ≤ l by omega)
    exact (hn (j + i) (by linarith) (by linarith)).le
  have hsum := Finset.sum_le_sum hsmall
  have he : (∑ i ∈ Finset.range (l - j),
      (φ (U + ((j + i : ℕ) : ℝ) + 1) - φ (U + ((j + i : ℕ) : ℝ)))) =
        φ (U + l) - φ (U + j) := by
    have ht := Finset.sum_range_sub (fun i : ℕ => φ (U + ((j + i : ℕ) : ℝ))) (l - j)
    simpa only [Nat.add_sub_of_le hjl, Nat.add_zero, Nat.cast_add,
      Nat.cast_one, ← add_assoc] using ht
  rw [he] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  nlinarith

/-- The upper-block selection in the character argument, including whole
rich unit shells from the single grid based at the selected left endpoint. -/
theorem exists_rich_prime_grid_block {C : ℝ} (hMertens : MertensEstimate C)
    (M : ℕ) (hM : 0 < M) (d ε : ℝ) (hd : 0 < d) (hε : 0 < ε)
    (hmesh : 20 ≤ ε * M) :
    ∃ H : ℕ, ∀ (K : ℕ), 1 ≤ K → 4 ≤ ε * K →
      64 * (Real.exp 1 + 1) ≤ d * ε * K →
      ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) →
      ∀ a L : ℝ, max C 0 ≤ a → 0 ≤ L →
      2 * (Real.exp 1 + 1) * (5 * K * (M : ℝ) ^ H + 1) < d * L →
      d * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
        (fun p => (p : ℝ)⁻¹) a (a + L) →
      ∃ (j : ℕ) (U : ℝ), j ≤ H ∧ a ≤ U ∧
        U + 5 * K * (M : ℝ) ^ j ≤ a + L ∧
        ∀ u v : ℝ, U ≤ u → v ≤ U + 5 * K * (M : ℝ) ^ j →
          ε * (K * (M : ℝ) ^ j) ≤ v - u →
          ∃ n : ℕ, u ≤ U + n ∧ U + n + 1 ≤ v ∧
            d / 16 ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
              (fun p => (p : ℝ)⁻¹) (U + n) (U + n + 1) := by
  obtain ⟨H, hH⟩ := exists_rich_prime_subblock hMertens M hM d hd
  refine ⟨H, ?_⟩
  intro K hK hKε hKA P hP a L ha hL hlarge hroot
  obtain ⟨j, U, hj, haU, hUL, hrich⟩ := hH K hK P hP a L ha hL hlarge hroot
  refine ⟨j, U, hj, haU, hUL, ?_⟩
  intro u v hUu hv hlen
  let k := (K : ℝ) * (M : ℝ) ^ j
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hk : (K : ℝ) ≤ k := by
    dsimp [k]
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ hM1)
  have hkpos : 0 < k := lt_of_lt_of_le (by exact_mod_cast (show 0 < K by omega)) hk
  have hlen4 : 4 ≤ v - u := hKε.trans ((mul_le_mul_of_nonneg_left hk hε.le).trans hlen)
  have hgrid : 4 * (5 * K * (M : ℝ) ^ j / M) ≤ v - u := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have h := mul_le_mul_of_nonneg_right hmesh hkpos.le
    have hdiv : 4 * (5 * k / M) ≤ ε * k := by
      rw [show 4 * (5 * k / M) = 20 * k / M by ring]
      apply (div_le_iff₀ hMr).mpr
      nlinarith only [h]
    convert hdiv.trans hlen using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [k]; ring)
  have hm := hrich u v hUu (by linarith) hv hgrid
  let φ := weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
  have hmono : Monotone φ := weightedCDF_mono _ _ _ (by intros; positivity)
  have hmass : (d / 8) * (v - u) ≤ φ v - φ u := by
    rwa [weightedCDF_sub _ _ _ u v (by linarith)]
  have hlarge' : 8 * (Real.exp 1 + 1) ≤ (d / 8) * (v - u) := by
    have h := mul_le_mul_of_nonneg_left hk (mul_nonneg hd.le hε.le)
    have h' := mul_le_mul_of_nonneg_left hlen hd.le
    nlinarith
  obtain ⟨n, hn, hnv, hnmass⟩ := exists_rich_grid_shell φ hmono U (Real.exp 1 + 1)
    (d / 8) u v (by positivity) (by positivity) hUu hlen4 hlarge'
    (by
      intro b hb
      rw [weightedCDF_sub _ _ _ b (b + 1) (by linarith)]
      exact prime_loglog_unit_mass_upper hMertens P hP b (ha.trans (haU.trans hb))) hmass
  refine ⟨n, hn, hnv, ?_⟩
  rw [weightedCDF_sub _ _ _ (U + n) (U + n + 1) (by linarith)] at hnmass
  convert hnmass using 1 <;> first | rfl | ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SeparatedMassIntervals
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three substantial intervals with a full grid cell between them -/

namespace Ostmann

open scoped BigOperators Classical

private theorem three_separated_of_card {q : ℕ} (S : Finset (Fin q)) (hS : 5 ≤ S.card) :
    ∃ i ∈ S, ∃ j ∈ S, ∃ k ∈ S, i.val + 1 < j.val ∧ j.val + 1 < k.val := by
  let f := S.orderEmbOfFin rfl
  let i₀ : Fin S.card := ⟨0, by omega⟩
  let i₁ : Fin S.card := ⟨1, by omega⟩
  let i₂ : Fin S.card := ⟨2, by omega⟩
  let i₃ : Fin S.card := ⟨3, by omega⟩
  let i₄ : Fin S.card := ⟨4, by omega⟩
  have h01 : (f i₀).val < (f i₁).val := f.strictMono (by norm_num [i₀, i₁, i₂, i₃, i₄])
  have h12 : (f i₁).val < (f i₂).val := f.strictMono (by norm_num [i₀, i₁, i₂, i₃, i₄])
  have h23 : (f i₂).val < (f i₃).val := f.strictMono (by norm_num [i₀, i₁, i₂, i₃, i₄])
  have h34 : (f i₃).val < (f i₄).val := f.strictMono (by norm_num [i₀, i₁, i₂, i₃, i₄])
  exact ⟨f i₀, S.orderEmbOfFin_mem rfl i₀, f i₂, S.orderEmbOfFin_mem rfl i₂,
    f i₄, S.orderEmbOfFin_mem rfl i₄, by omega, by omega⟩

theorem three_large_separated_weights {q : ℕ} (hq : 0 < q)
    (w : Fin q → ℝ) (T U : ℝ) (hU : 0 < U)
    (hsum : T ≤ ∑ i, w i) (hcap : ∀ i, w i ≤ U) (hsize : 10 * U ≤ T) :
    ∃ i j k : Fin q, i.val + 1 < j.val ∧ j.val + 1 < k.val ∧
      T / (2 * q) ≤ w i ∧ T / (2 * q) ≤ w j ∧ T / (2 * q) ≤ w k := by
  let θ := T / (2 * q)
  let S := Finset.univ.filter (fun i => θ ≤ w i)
  have hT : 0 < T := lt_of_lt_of_le (by positivity) hsize
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hbad : (∑ i ∈ Finset.univ.filter (fun i => ¬θ ≤ w i), w i) ≤ T / 2 := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => ¬θ ≤ w i), θ :=
        Finset.sum_le_sum (fun i hi => (lt_of_not_ge (Finset.mem_filter.mp hi).2).le)
      _ = ((Finset.univ.filter (fun i => ¬θ ≤ w i)).card : ℝ) * θ := by simp
      _ ≤ (q : ℝ) * θ := by
        apply mul_le_mul_of_nonneg_right _ hθ
        have hc := Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin q => ¬θ ≤ w i)
        simp only [Finset.card_univ, Fintype.card_fin] at hc
        exact_mod_cast hc
      _ = T / 2 := by dsimp [θ]; field_simp
  have hgood : T / 2 ≤ ∑ i ∈ S, w i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => θ ≤ w i) w
    linarith
  have hgoodcap : (∑ i ∈ S, w i) ≤ S.card * U := by
    calc
      _ ≤ ∑ _i ∈ S, U := Finset.sum_le_sum (fun i _ => hcap i)
      _ = _ := by simp
  have hcard : 5 ≤ S.card := by
    by_contra! h
    have hc : (S.card : ℝ) ≤ 4 := by exact_mod_cast (show S.card ≤ 4 by omega)
    nlinarith
  obtain ⟨i, hi, j, hj, k, hk, hij, hjk⟩ := three_separated_of_card S hcard
  exact ⟨i, j, k, hij, hjk, (Finset.mem_filter.mp hi).2,
    (Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hk).2⟩

theorem three_separated_mass_intervals (φ : ℝ → ℝ) (q : ℕ) (hq : 0 < q)
    (a L T A : ℝ) (hL : 0 < L) (hA : 0 < A)
    (hmass : T ≤ φ (a + L) - φ a)
    (hupper : ∀ u v, a ≤ u → u ≤ v → v ≤ a + L →
      φ v - φ u ≤ A * (v - u + 1))
    (hsize : 10 * (A * (L / q + 1)) ≤ T) :
    ∃ i j k : Fin q, i.val + 1 < j.val ∧ j.val + 1 < k.val ∧
      ∀ t ∈ ({i, j, k} : Finset (Fin q)),
        T / (2 * q) ≤ φ (a + ((t.val : ℝ) + 1) * (L / q)) -
          φ (a + (t.val : ℝ) * (L / q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : 0 < L / q := div_pos hL hqR
  let w := fun i : Fin q => φ (a + ((i.val : ℝ) + 1) * (L / q)) -
    φ (a + (i.val : ℝ) * (L / q))
  have hsum : (∑ i, w i) = φ (a + L) - φ a := by
    have h := Finset.sum_range_sub (fun i : ℕ => φ (a + (i : ℝ) * (L / q))) q
    rw [Finset.sum_range] at h
    have he : (q : ℝ) * (L / q) = L := by field_simp
    simpa only [w, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, he] using h
  have hcap : ∀ i, w i ≤ A * (L / q + 1) := by
    intro i
    have hi : (i.val : ℝ) + 1 ≤ q := by exact_mod_cast i.isLt
    have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    have hend : a + ((i.val : ℝ) + 1) * (L / q) ≤ a + L := by
      have h := mul_le_mul_of_nonneg_right hi hh.le
      have he : (q : ℝ) * (L / q) = L := by field_simp
      rw [he] at h
      linarith
    have h := hupper (a + (i.val : ℝ) * (L / q))
      (a + ((i.val : ℝ) + 1) * (L / q))
      (le_add_of_nonneg_right (mul_nonneg hi0 hh.le))
      (by nlinarith) hend
    convert h using 1 <;> first | rfl | ring
  obtain ⟨i, j, k, hij, hjk, hi, hj, hk⟩ := three_large_separated_weights hq w T
    (A * (L / q + 1)) (by positivity) (by rwa [hsum]) hcap hsize
  refine ⟨i, j, k, hij, hjk, ?_⟩
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact hi
  · exact hj
  · exact hk

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SeparatedPrimeBands
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separated lower, bulk and upper bands from positive prime mass -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem exists_three_prime_bands {C : ℝ} (hMertens : MertensEstimate C)
    (α β c : ℝ) (hα : 0 < α) (hαβ : α < β) (hc : 0 < c) :
    ∃ q : ℕ, 0 < q ∧ ∀ᶠ L : ℝ in atTop,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      c * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
        (fun p => (p : ℝ)⁻¹) (α * L) (β * L) →
      ∃ i j k : Fin q, i.val + 1 < j.val ∧ j.val + 1 < k.val ∧
        ∀ t ∈ ({i, j, k} : Finset (Fin q)),
          c * L / (2 * q) ≤
            weightedIntervalMass P (fun p => Real.log (Real.log p))
              (fun p => (p : ℝ)⁻¹)
              (α * L + (t.val : ℝ) * ((β - α) * L / q))
              (α * L + ((t.val : ℝ) + 1) * ((β - α) * L / q)) := by
  let A := Real.exp 1 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨q, hq⟩ := exists_nat_gt (20 * A * (β - α) / c)
  have hqposR : (0 : ℝ) < q := lt_trans (by positivity) hq
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hqbound : 20 * A * (β - α) ≤ c * q := by
    have h := (div_lt_iff₀ hc).mp hq
    nlinarith only [h]
  refine ⟨q, hqpos, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (max C 0 / α), eventually_ge_atTop (20 * A / c)] with L hL hLa hLA
  intro P hP hmass
  have ha : max C 0 ≤ α * L := by
    have h := (div_le_iff₀ hα).mp hLa
    nlinarith only [h]
  have hlength : 0 < (β - α) * L := mul_pos (sub_pos.mpr hαβ) hL
  have hroot : c * L ≤
      weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
        (α * L + (β - α) * L) -
      weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹) (α * L) := by
    rw [weightedCDF_sub _ _ _ _ _ (by nlinarith)]
    rw [show α * L + (β - α) * L = β * L by ring]
    exact hmass
  have hsize : 10 * (A * (((β - α) * L) / q + 1)) ≤ c * L := by
    have h1 := mul_le_mul_of_nonneg_right hqbound hL.le
    have h2 := (div_le_iff₀ hc).mp hLA
    apply (mul_le_mul_iff_left₀ hqposR).mp
    have he : 10 * (A * (((β - α) * L) / q + 1)) * q =
        10 * A * (β - α) * L + 10 * A * q := by field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right h2 hqposR.le]
  obtain ⟨i, j, k, hij, hjk, hm⟩ := three_separated_mass_intervals
    (weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹))
    q hqpos (α * L) ((β - α) * L) (c * L) A hlength hA hroot
    (by
      intro u v hu huv _
      rw [weightedCDF_sub _ _ _ u v huv]
      exact prime_loglog_interval_mass_upper hMertens P hP u v (ha.trans hu) huv) hsize
  refine ⟨i, j, k, hij, hjk, ?_⟩
  intro t ht
  have h := hm t ht
  rw [weightedCDF_sub _ _ _ _ _ (by
    have hq0 : 0 < ((β - α) * L) / q := div_pos hlength hqposR
    nlinarith)] at h
  exact h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterBandGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The three selected prime bands give all character separation parameters -/
namespace Ostmann

theorem characterBandPoint_strictMono (α β : ℝ) (q : ℕ) (hαβ : α < β) (hq : 0 < q) :
    StrictMono (characterBandPoint α β q) := by
  intro i j hij
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hijR : (i : ℝ) < j := by exact_mod_cast hij
  exact add_lt_add_right (mul_lt_mul_of_pos_right hijR (div_pos (sub_pos.mpr hαβ) hqR)) α

theorem characterBandPoint_bounds (α β : ℝ) (q i : ℕ)
    (hαβ : α < β) (hq : 0 < q) (hi : i ≤ q) :
    α ≤ characterBandPoint α β q i ∧ characterBandPoint α β q i ≤ β := by
  have hmono := (characterBandPoint_strictMono α β q hαβ hq).monotone
  have hzero : characterBandPoint α β q 0 = α := by simp [characterBandPoint]
  have hlast : characterBandPoint α β q q = β := by
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
    unfold characterBandPoint
    field_simp
    ring
  exact ⟨by simpa only [hzero] using hmono (Nat.zero_le i),
    by simpa only [hlast] using hmono hi⟩

/-- Midpoints of the unused partition gaps satisfy the strict margins required
by both the anchor and nonanchor energy comparisons. -/
theorem character_three_band_margins (α β : ℝ) (q : ℕ) (hα : 0 < α) (hαβ : α < β)
    (hq : 0 < q) (i j k : Fin q) (hij : i.val + 1 < j.val) (hjk : j.val + 1 < k.val) :
    let γs := characterBandPoint α β q (i.val + 1)
    let νw := characterBandPoint α β q j.val
    let γw := characterBandPoint α β q (j.val + 1)
    let νa := characterBandPoint α β q k.val
    let βw := (γs + νw) / 2
    let βa := (γw + νa) / 2
    0 < α / 2 ∧ α / 2 < βw ∧ γs < βw ∧ βw < νw ∧
      α / 2 < βa ∧ γw < βa ∧ βa < νa ∧
      0 ≤ γw ∧ γw ≤ β + 1 ∧ νa < β + 1 := by
  intro γs νw γw νa βw βa
  have hmono := characterBandPoint_strictMono α β q hαβ hq
  have hsmall : γs < νw := hmono hij
  have hlarge : γw < νa := hmono hjk
  have hγs := (characterBandPoint_bounds α β q (i.val + 1) hαβ hq (by omega)).1
  have hγw := characterBandPoint_bounds α β q (j.val + 1) hαβ hq (by omega)
  have hνa := (characterBandPoint_bounds α β q k.val hαβ hq (by omega)).2
  dsimp only [βw, βa]
  refine ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith [hγw.1],
    by linarith [hγw.2], by linarith⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogCellMeans
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prime log cells and their means -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem primeLogIndex_bounds (p : ℕ) (hp : p.Prime) :
    (primeLogIndex p : ℝ) < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ (primeLogIndex p : ℝ) + 1 := by
  have hx : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  let n := ⌈Real.log (p : ℝ)⌉₊
  have hn : 0 < n := by
    have h := Nat.le_ceil (Real.log (p : ℝ))
    by_contra! hz
    have he : n = 0 := Nat.eq_zero_of_le_zero hz
    change Real.log (p : ℝ) ≤ (n : ℝ) at h
    rw [he, Nat.cast_zero] at h
    linarith
  have heq : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n by omega)
  have hu := Nat.le_ceil (Real.log (p : ℝ))
  have hl := Nat.ceil_lt_add_one hx.le
  change (n : ℝ) < Real.log (p : ℝ) + 1 at hl
  change Real.log (p : ℝ) ≤ (n : ℝ) at hu
  change ((n - 1 : ℕ) : ℝ) < Real.log (p : ℝ) ∧
    Real.log (p : ℝ) ≤ ((n - 1 : ℕ) : ℝ) + 1
  constructor <;> linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeShellIndex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Whole unit shells fit the integer cell scale

Taking the floor of the lower exponential endpoint retains every prime in
the shell, including its two boundary cells.
-/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem prime_shell_log_bounds (u : ℝ) (p : ℕ) (hp : p.Prime)
    (hlo : u < Real.log (Real.log (p : ℝ)))
    (hhi : Real.log (Real.log (p : ℝ)) ≤ u + 1) :
    Real.exp u < Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ Real.exp 1 * Real.exp u := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  constructor
  · simpa only [Real.exp_log hlog] using Real.exp_lt_exp.mpr hlo
  · have h := Real.exp_le_exp.mpr hhi
    simpa only [Real.exp_log hlog, Real.exp_add, mul_comm] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterBandSelection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The lower shell, bulk band and rich upper block are selected together -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem exists_character_band_selection {C : ℝ} (hM : MertensEstimate C)
    (α β c : ℝ) (hα : 0 < α) (hαβ : α < β) (hc : 0 < c) :
    ∃ q : ℕ, 0 < q ∧ ∃ H : ℕ, ∀ K : ℕ, 1 ≤ K →
      4 ≤ (1 / 10000 : ℝ) * K →
      64 * (Real.exp 1 + 1) ≤ (c / (2 * (β - α))) * (1 / 10000 : ℝ) * K →
      ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      c * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
        (fun p => (p : ℝ)⁻¹) (α * L) (β * L) →
      let width := ((β - α) / q) * L
      ∃ i j k : Fin q, i.val + 1 < j.val ∧ j.val + 1 < k.val ∧
        c * L / (2 * q) ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
          (fun p => (p : ℝ)⁻¹) (characterBandPoint α β q j.val * L)
          (characterBandPoint α β q j.val * L + width) ∧
        ∃ us : ℝ, characterBandPoint α β q i.val * L ≤ us ∧
          us + 1 ≤ characterBandPoint α β q i.val * L + width ∧
          c / (32 * (β - α)) ≤ ∑ p ∈ loglogShell P us, (p : ℝ)⁻¹ ∧
        ∃ h : ℕ, h ≤ H ∧ ∃ U : ℝ,
          characterBandPoint α β q k.val * L ≤ U ∧
          U + 5 * (K * 200000 ^ h : ℕ) ≤ characterBandPoint α β q k.val * L + width ∧
          ∀ u v : ℝ, U ≤ u → v ≤ U + 5 * (K * 200000 ^ h : ℕ) →
            ((K * 200000 ^ h : ℕ) : ℝ) / 10000 ≤ v - u →
            ∃ t : ℕ, u ≤ U + t ∧ U + t + 1 ≤ v ∧
              c / (32 * (β - α)) ≤ ∑ p ∈ loglogShell P (U + t), (p : ℝ)⁻¹ := by
  obtain ⟨q, hq, hbands⟩ := exists_three_prime_bands hM α β c hα hαβ hc
  let d := c / (2 * (β - α))
  have hd : 0 < d := by dsimp [d]; positivity
  let A := Real.exp 1 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨H, hr⟩ := exists_rich_prime_grid_block hM 200000 (by norm_num)
    d (1 / 10000) hd (by norm_num) (by norm_num)
  refine ⟨q, hq, H, ?_⟩
  intro K hK hKε hKA
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hw : 0 < (β - α) / q := div_pos (sub_pos.mpr hαβ) hqR
  have hwidth := tendsto_id.const_mul_atTop hw
  have hstart := tendsto_id.const_mul_atTop hα
  filter_upwards [hbands, eventually_gt_atTop (0 : ℝ),
    hstart.eventually (eventually_ge_atTop (max C 0)),
    hwidth.eventually (eventually_ge_atTop 4),
    hwidth.eventually (eventually_ge_atTop (8 * A / d)),
    hwidth.eventually (eventually_gt_atTop (2 * A * (5 * K * (200000 : ℝ) ^ H + 1) / d))]
    with L hbands hL hstart hwidth4 hwidthmass hwidthlarge
  intro P hP hmass width
  obtain ⟨i, j, k, hij, hjk, hm⟩ := hbands P hP hmass
  have hwidth4' : 4 ≤ width := hwidth4
  have hwidth0 : 0 ≤ width := le_trans (by norm_num) hwidth4
  have hwidthmass' : 8 * A ≤ d * width := by
    have hh := (div_le_iff₀ hd).mp hwidthmass
    exact hh.trans_eq (mul_comm _ _)
  have hlarge : 2 * A * (5 * K * (200000 : ℝ) ^ H + 1) < d * width := by
    have hh := (div_lt_iff₀ hd).mp hwidthlarge
    exact hh.trans_eq (mul_comm _ _)
  have he : d * width = c * L / (2 * q) := by
    dsimp [d, width]
    field_simp [ne_of_gt (sub_pos.mpr hαβ), ne_of_gt hqR]
  have hcell (t : Fin q) (ht : t ∈ ({i, j, k} : Finset (Fin q))) :
      d * width ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
        (fun p => (p : ℝ)⁻¹) (characterBandPoint α β q t.val * L)
          (characterBandPoint α β q t.val * L + width) := by
    rw [he]
    convert hm t ht using 2 <;> first | (with_reducible_and_instances rfl) | (dsimp [characterBandPoint, width] <;> ring)
  have hbase (t : Fin q) : max C 0 ≤ characterBandPoint α β q t.val * L := by
    exact hstart.trans (mul_le_mul_of_nonneg_right
      (characterBandPoint_bounds α β q t.val hαβ hq (by omega)).1 hL.le)
  let ai := characterBandPoint α β q i.val * L
  let ak := characterBandPoint α β q k.val * L
  let φ := weightedCDF P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
  have hmono : Monotone φ := weightedCDF_mono _ _ _ (by intros; positivity)
  have hsmall : d * width ≤ φ (ai + width) - φ ai := by
    rw [weightedCDF_sub _ _ _ ai (ai + width) (by linarith only [hwidth0])]
    exact hcell i (by simp)
  obtain ⟨s, hslo, hshi, hsmass⟩ := exists_rich_grid_shell φ hmono ai A d ai (ai + width)
    hA hd.le le_rfl (by linarith only [hwidth4']) (by linarith only [hwidthmass'])
    (fun a ha => by
      rw [weightedCDF_sub _ _ _ a (a + 1) (by linarith)]
      exact prime_loglog_unit_mass_upper hM P hP a ((hbase i).trans ha))
    (by simpa only [add_sub_cancel_left] using hsmall)
  obtain ⟨h, U, hh, hUlo, hUhi, hrich⟩ := hr K hK hKε hKA P hP ak width (hbase k)
    hwidth0 hlarge (hcell k (by simp))
  have hcost : c / (32 * (β - α)) = d / 16 := by
    dsimp [d]
    field_simp [ne_of_gt (sub_pos.mpr hαβ)]
    ring
  refine ⟨i, j, k, hij, hjk, ?_, ai + s, hslo, hshi, ?_, h, hh, U, hUlo, ?_, ?_⟩
  · rw [← he]
    exact hcell j (by simp)
  · rw [weightedCDF_sub _ _ _ (ai + s) (ai + s + 1) (by linarith)] at hsmass
    rw [hcost]
    exact (by linarith only [hd] : d / 16 ≤ d / 2).trans hsmass
  · simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hUhi
  · intro u v hu hv hlen
    obtain ⟨t, htlo, hthi, htmass⟩ := hrich u v hu
      (by simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using hv)
      (by
        convert hlen using 1
        all_goals try with_reducible_and_instances rfl
        push_cast
        ring)
    refine ⟨t, htlo, hthi, ?_⟩
    rw [hcost]
    exact htmass

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

theorem primeSubsetPrior_mean (P Q : Finset ℕ) (hQP : Q ⊆ P) (F : ℕ → ℂ) :
    (∑ p : P, (primeSubsetPrior P Q p : ℂ) * F p) =
      (Complex.ofReal (∑ q ∈ Q, (q : ℝ)⁻¹))⁻¹ * ∑ q ∈ Q, ((q : ℝ)⁻¹ : ℂ) * F q := by
  unfold primeSubsetPrior
  simp only [apply_ite, Complex.ofReal_div, Complex.ofReal_zero, ite_mul, zero_mul]
  rw [Finset.sum_coe_sort P (fun p => if p ∈ Q then
    (((p : ℝ)⁻¹ : ℝ) : ℂ) / (∑ q ∈ Q, (q : ℝ)⁻¹ : ℝ) * F p else 0), ← Finset.sum_filter]
  have hf : P.filter (fun p => p ∈ Q) = Q := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hQP h, h⟩⟩
  rw [hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Complex.ofReal_inv]
  ring

theorem primeSubsetPrior_mean_positive (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hm : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹) (F : ℕ → ℂ) (δ : ℝ)
    (hb : δ * (∑ q ∈ Q, (q : ℝ)⁻¹) ≤ ∑ q ∈ Q, (q : ℝ)⁻¹ * (F q).re) :
    δ ≤ (∑ p : P, (primeSubsetPrior P Q p : ℂ) * F p).re := by
  rw [primeSubsetPrior_mean P Q hQP F]
  have h := (le_div_iff₀ hm).mpr hb
  simpa only [← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_sum, zero_mul, mul_zero, sub_zero, Complex.ofReal_mul,
    div_eq_mul_inv, mul_comm] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SignedQuadraticFrequency
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The signed Fourier series and its positive-frequency half -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap FourierTransform
open MeasureTheory

/-- Reality of the original physical cutoff supplies Hermitian symmetry of
its Fourier transform without any additional analytic input. -/
theorem fourier_real_conj (f : ℝ → ℂ) (hf : ∀ x, conj (f x) = f x) (ξ : ℝ) :
    𝓕 f (-ξ) = conj (𝓕 f ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, hf]
  congr 2
  push_cast
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PositiveFourierCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A positive band-limited Schwartz cutoff

A narrow real even smooth bump has a real Fourier transform bounded away from
zero on the unit interval. Squaring this transform gives the required cutoff;
its Fourier support is controlled by the convolution of the original bumps.
-/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform ComplexConjugate Convolution

private theorem narrowSchwartz_apply (x : ℝ) : narrowSchwartz x = (narrowBump x : ℂ) := rfl

private theorem narrowSchwartz_even (x : ℝ) : narrowSchwartz (-x) = narrowSchwartz x := by
  simp only [narrowSchwartz_apply, narrowBump.neg]

private theorem narrow_fourier_real (x : ℝ) :
    conj (𝓕 narrowSchwartz x) = 𝓕 narrowSchwartz x := by
  have hr := fourier_real_conj narrowSchwartz (by intro y; simp [narrowSchwartz_apply]) x
  change conj (𝓕 (narrowSchwartz : ℝ → ℂ) x) = 𝓕 (narrowSchwartz : ℝ → ℂ) x
  rw [← hr]
  have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
    (narrowSchwartz : ℝ → ℂ) x
  have hh : (narrowSchwartz : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = narrowSchwartz := by
    funext y
    exact narrowSchwartz_even y
  rw [hh] at he
  exact he.symm

private theorem narrow_fourier_lower (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y : ℝ, narrowBump y) / 2 ≤ (𝓕 narrowSchwartz x).re := by
  let phase : ℝ → ℂ := fun y => Complex.exp ((-2 * Real.pi * y * x : ℝ) * Complex.I)
  have hc : HasCompactSupport (fun y : ℝ => narrowSchwartz y) := by
    change HasCompactSupport (Complex.ofReal ∘ (narrowBump : ℝ → ℝ))
    exact narrowBump.hasCompactSupport.comp_left (show Complex.ofReal 0 = 0 by simp)
  have hi : Integrable (fun y : ℝ => phase y * narrowSchwartz y) :=
    (by fun_prop : Continuous (fun y : ℝ => phase y * narrowSchwartz y)).integrable_of_hasCompactSupport hc.mul_left
  have hu : Integrable (narrowBump : ℝ → ℝ) :=
    narrowBump.continuous.integrable_of_hasCompactSupport narrowBump.hasCompactSupport
  have hphase (y : ℝ) : (phase y * narrowSchwartz y).re =
      Real.cos (-2 * Real.pi * y * x) * narrowBump y := by
    simp only [phase, narrowSchwartz_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
  have hire := hi.re
  change Integrable (fun y => (phase y * narrowSchwartz y).re) at hire
  have hint : Integrable (fun y => Real.cos (-2 * Real.pi * y * x) * narrowBump y) := by
    simpa only [hphase] using hire
  have he : (𝓕 narrowSchwartz x).re = ∫ y : ℝ, Real.cos (-2 * Real.pi * y * x) * narrowBump y := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    change (∫ y : ℝ, phase y * narrowSchwartz y).re = _
    have hh := integral_re hi
    change (∫ y : ℝ, (phase y * narrowSchwartz y).re) = (∫ y : ℝ, phase y * narrowSchwartz y).re at hh
    rw [← hh]
    simp only [hphase]
  rw [he, div_eq_mul_inv, ← integral_mul_const]
  apply integral_mono (hu.mul_const _) hint
  · intro y
    by_cases hy : narrowBump y = 0
    · simp [hy]
    have hylt : |y| < 1 / 100 := by
      have hm : y ∈ Function.support narrowBump := hy
      rw [narrowBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hm
      exact hm
    have hxabs : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
    have hang : |(-2 * Real.pi * y * x)| ≤ 1 := by
      rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_pos Real.pi_pos]
      have hh := mul_le_mul (le_of_lt hylt) hxabs (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 1 / 100)
      nlinarith [Real.pi_lt_four, Real.pi_pos]
    have hcos : (1 / 2 : ℝ) ≤ Real.cos (-2 * Real.pi * y * x) := by
      have hs := (abs_le.mp hang)
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := -2 * Real.pi * y * x)]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_right hcos (narrowBump.nonneg' y)

private theorem narrow_integral_pos : 0 < ∫ y : ℝ, narrowBump y := by
  apply integral_pos_of_integrable_nonneg_nonzero narrowBump.continuous
    (narrowBump.continuous.integrable_of_hasCompactSupport narrowBump.hasCompactSupport)
    narrowBump.nonneg'
  have hh : narrowBump (0 : ℝ) = 1 := narrowBump.one_of_mem_closedBall (by
    simp only [Metric.mem_closedBall, dist_self]; exact narrowBump.rIn_pos.le)
  rw [hh]
  norm_num

private theorem schwartz_fourier_twice (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓕 (𝓕 f) x = f (-x) := by
  have hh := congrArg (fun g : 𝓢(ℝ, ℂ) => g (-x)) (show (𝓕⁻ (𝓕 f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = f from FourierTransform.fourierInv_fourier_eq f)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg] at hh
  exact hh

private theorem narrow_convolution_zero (x : ℝ) (hx : 1 ≤ |x|) :
    SchwartzMap.convolution (.mul ℂ ℂ) narrowSchwartz narrowSchwartz x = 0 := by
  rw [SchwartzMap.convolution_apply, convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : 1 / 100 ≤ |y|
  · have hz : narrowBump y = 0 := narrowBump.zero_of_le_dist (by simpa [Real.dist_eq, narrowBump] using hy)
    simp [narrowSchwartz_apply, hz]
  · have hxy : 1 / 100 ≤ |x - y| := by
      have hh := abs_add_le (x - y) y
      rw [sub_add_cancel] at hh
      linarith
    have hz : narrowBump (x - y) = 0 := narrowBump.zero_of_le_dist (by simpa [Real.dist_eq, narrowBump] using hxy)
    simp [narrowSchwartz_apply, hz]

/-- The cutoff needed by the original amplified moment argument exists. -/
theorem exists_positive_even_fourier_cutoff :
    ∃ (c : ℝ) (ψ : 𝓢(ℝ, ℂ)), 0 < c ∧
      (∀ x, conj (ψ x) = ψ x) ∧ (∀ x, 0 ≤ (ψ x).re) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, c ≤ (ψ x).re) ∧
      (∀ x : ℝ, (3 : ℝ) ^ 2 < |x| → 𝓕 ψ x = 0) ∧
      (∀ x : ℝ, 𝓕 ψ (-x) = 𝓕 ψ x) := by
  let f := 𝓕 narrowSchwartz
  let ψ := SchwartzMap.pairing (.mul ℂ ℂ) f f
  let c := ((∫ y : ℝ, narrowBump y) / 2) ^ 2
  have hfreal (x : ℝ) : (f x).im = 0 := by
    have hh := congrArg Complex.im (narrow_fourier_real x)
    simp only [Complex.conj_im] at hh
    change -(f x).im = (f x).im at hh
    linarith
  have hψ (x : ℝ) : ψ x = f x * f x := rfl
  have hcpos := narrow_integral_pos
  refine ⟨c, ψ, by dsimp [c]; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [hψ, map_mul] using congrArg (fun z : ℂ => z * z) (narrow_fourier_real x)
  · intro x
    rw [hψ, Complex.mul_re, hfreal]
    nlinarith
  · intro x hx
    rw [hψ, Complex.mul_re, hfreal]
    have hl := narrow_fourier_lower x hx
    change (∫ y : ℝ, narrowBump y) / 2 ≤ (f x).re at hl
    dsimp [c]
    nlinarith [narrow_integral_pos]
  · intro x hx
    have he : ψ = 𝓕 (SchwartzMap.convolution (.mul ℂ ℂ) narrowSchwartz narrowSchwartz) :=
      (SchwartzMap.fourier_convolution _ _ _).symm
    rw [he, schwartz_fourier_twice]
    exact narrow_convolution_zero (-x) (by rw [abs_neg]; linarith)

  · intro x
    have hfEven (y : ℝ) : f (-y) = f y := by
      have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
        (narrowSchwartz : ℝ → ℂ) y
      have hh : (narrowSchwartz : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = narrowSchwartz := by
        funext z
        exact narrowSchwartz_even z
      rw [hh] at he
      exact he.symm
    have hψEven : (ψ : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ = ψ := by
      funext y
      change f (-y) * f (-y) = f y * f y
      rw [hfEven]
    have he := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ))
      (ψ : ℝ → ℂ) x
    rw [hψEven] at he
    exact he.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TopWordBinScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top prime controls every nonempty bulk-word bin -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem eventual_bulk_word_small (α z : ℝ) (hα : 0 < α) (hz : 0 ≤ z) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ) (V U τ : ℝ),
      (m : ℝ) ≤ z * L → V + α * L ≤ U → Real.exp U ≤ τ →
      (m : ℝ) * Real.exp V ≤ τ := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 1 hα).const_mul_left z).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with L hbound hL m V U τ hm hVU hτ
  have hze : z * L ≤ Real.exp (α * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz hL),
      abs_of_pos (Real.exp_pos _), one_mul] using hbound
  calc
    (m : ℝ) * Real.exp V ≤ (z * L) * Real.exp V :=
      mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ ≤ Real.exp (α * L) * Real.exp V :=
      mul_le_mul_of_nonneg_right hze (Real.exp_pos _).le
    _ = Real.exp (V + α * L) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp U := Real.exp_le_exp.mpr hVU
    _ ≤ τ := hτ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterMeanRotation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One common rotation and the original, unrotated character priors -/
namespace Ostmann
open scoped Classical BigOperators

theorem quarterTurn_norm (q : Bool × Bool) : ‖quarterTurn q‖ = 1 := by
  rcases q with ⟨b, c⟩
  cases b <;> cases c <;> simp [quarterTurn]

theorem exists_positive_quarterTurn (z : ℂ) :
    ∃ q : Bool × Bool, ‖z‖ / 2 ≤ (quarterTurn q * z).re := by
  have hnorm := Complex.norm_le_abs_re_add_abs_im z
  by_cases hr : ‖z‖ / 2 ≤ |z.re|
  · by_cases hs : 0 ≤ z.re
    · refine ⟨(true, true), ?_⟩
      simpa [quarterTurn, abs_of_nonneg hs] using hr
    · refine ⟨(true, false), ?_⟩
      simpa [quarterTurn, abs_of_neg (lt_of_not_ge hs)] using hr
  · have hi : ‖z‖ / 2 ≤ |z.im| := by linarith
    by_cases hs : 0 ≤ z.im
    · refine ⟨(false, false), ?_⟩
      simpa [quarterTurn, Complex.mul_re, abs_of_nonneg hs] using hi
    · refine ⟨(false, true), ?_⟩
      simpa [quarterTurn, Complex.mul_re, abs_of_neg (lt_of_not_ge hs)] using hi

/-- A single quarter turn retains at least a quarter of the prime mass.
Thereafter the word and cell estimates can use the original characters. -/
theorem common_positive_character_rotation (P : Finset ℕ) (m : ℕ → ℂ) (δ : ℝ)
    (hm : ∀ p ∈ P, δ ≤ ‖m p‖) :
    ∃ ζ : ℂ, ∃ E : Finset ℕ, ‖ζ‖ = 1 ∧ E ⊆ P ∧
      (∑ p ∈ P, (p : ℝ)⁻¹) / 4 ≤ (∑ p ∈ E, (p : ℝ)⁻¹) ∧
      ∀ p ∈ E, δ / 2 ≤ (ζ * m p).re := by
  choose q hq using (fun p : ℕ => exists_positive_quarterTurn (m p))
  let mass : (Bool × Bool) → ℝ := fun a => ∑ p ∈ P.filter (fun p => q p = a), (p : ℝ)⁻¹
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ mass Finset.univ_nonempty
  refine ⟨quarterTurn a, P.filter (fun p => q p = a), quarterTurn_norm a,
    Finset.filter_subset _ _, ?_, ?_⟩
  · have hsum : (∑ a, mass a) = ∑ p ∈ P, (p : ℝ)⁻¹ := by
      simp only [mass, Finset.sum_filter]
      rw [Finset.sum_comm]
      simp
    have hbound : (∑ a, mass a) ≤ 4 * mass a := by
      calc
        _ ≤ ∑ _a : Bool × Bool, mass a := Finset.sum_le_sum (fun b hb => ha b hb)
        _ = _ := by simp
    change (∑ p ∈ P, (p : ℝ)⁻¹) / 4 ≤ mass a
    rw [hsum] at hbound
    linarith
  · intro p hp
    obtain ⟨hpP, hpq⟩ := Finset.mem_filter.mp hp
    have hh := hq p
    rw [hpq] at hh
    linarith [hm p hpP]

theorem norm_weighted_common_rotation {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (F : ι → ℂ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖∑ i, (w i : ℂ) * (ζ * F i)‖ = ‖∑ i, (w i : ℂ) * F i‖ := by
  have he : (∑ i, (w i : ℂ) * (ζ * F i)) = ζ * ∑ i, (w i : ℂ) * F i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, norm_mul, hζ, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CellRoleBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Absorption of the cell-role count

Section 4 fixes `ε = 1/10000`, bounds the number of selected cell roles by
`C (k+1) exp(2 ε k)`, and uses the scale `z = exp(3 ε k)`.  Their ratio tends
to zero, so every fixed positive proportion of `z` eventually absorbs the
role count. This is an elementary numerical step, with no published input.
-/

namespace Ostmann

open Filter
open scoped Topology

theorem cellRoleScale_pos (k : ℕ) : 0 < cellRoleScale k := Real.exp_pos _

theorem cellRoleCountBound_nonneg {C : ℝ} (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ cellRoleCountBound C k := by
  unfold cellRoleCountBound
  positivity

theorem cellRoleCountBound_div_scale (C : ℝ) (k : ℕ) :
    cellRoleCountBound C k / cellRoleScale k =
      C * (((k : ℝ) + 1) / Real.exp (cellRoleEpsilon * k)) := by
  unfold cellRoleCountBound cellRoleScale
  rw [show 3 * cellRoleEpsilon * (k : ℝ) =
    2 * cellRoleEpsilon * k + cellRoleEpsilon * k by ring, Real.exp_add]
  field_simp

/-- The manuscript's `n_max / z → 0`, with its fixed value of epsilon. -/
theorem tendsto_cellRoleCountBound_div_scale (C : ℝ) :
    Tendsto (fun k : ℕ => cellRoleCountBound C k / cellRoleScale k)
      atTop (𝓝 0) := by
  have hε : 0 < cellRoleEpsilon := by norm_num [cellRoleEpsilon]
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 1 hε).tendsto_div_nhds_zero
  have h0 := (isLittleO_pow_exp_pos_mul_atTop 0 hε).tendsto_div_nhds_zero
  have hreal : Tendsto (fun x : ℝ => C * ((x + 1) / Real.exp (cellRoleEpsilon * x)))
      atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, ← add_div, add_zero, mul_zero]
      using (h1.add h0).const_mul C
  have hnat := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, cellRoleCountBound_div_scale] using hnat

/-- Any prescribed positive budget eventually absorbs the entire role count. -/
theorem eventually_cellRoleCountBound_le (C b : ℝ) (hb : 0 < b) :
    ∀ᶠ k : ℕ in atTop, cellRoleCountBound C k ≤ b * cellRoleScale k := by
  filter_upwards [(tendsto_cellRoleCountBound_div_scale C).eventually_lt_const hb]
    with k hk
  exact ((div_lt_iff₀ (cellRoleScale_pos k)).mp hk).le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterDepthChoice
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One fixed depth meets the role-count and final entropy budgets -/

namespace Ostmann

theorem cellRoleEpsilon_margin : 0 < Real.log 2 - 60 * cellRoleEpsilon := by
  have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num [cellRoleEpsilon] at hh ⊢
  linarith

theorem log_cellRoleScale (k : ℕ) :
    Real.log (cellRoleScale k) = 3 * cellRoleEpsilon * k := by
  rw [cellRoleScale, Real.log_exp]

/-- The threshold can be chosen before the late-block density increment.
Every resulting depth above it meets both budgets with the same constants. -/
theorem character_depth_cutoff (C R b : ℝ) (hb : 0 < b) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ ∀ k : ℕ, K ≤ k →
      1 ≤ k ∧ 1 ≤ cellRoleScale k ∧
        C + 20 * Real.log (cellRoleScale k) ≤ (k : ℝ) * Real.log 2 - 1 ∧
        cellRoleCountBound R k ≤ b * cellRoleScale k := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((C + 1) / (Real.log 2 - 60 * cellRoleEpsilon))
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp (eventually_cellRoleCountBound_le R b hb)
  let K := max Kmin (max 1 (max N J))
  refine ⟨K, by omega, fun k hk => ?_⟩
  have hNk : (N : ℝ) ≤ k := by exact_mod_cast (show N ≤ k by omega)
  have hC : C + 1 < (N : ℝ) * (Real.log 2 - 60 * cellRoleEpsilon) :=
    (div_lt_iff₀ cellRoleEpsilon_margin).mp hN
  have hscale : 1 ≤ cellRoleScale k := by
    unfold cellRoleScale
    apply Real.one_le_exp_iff.mpr
    unfold cellRoleEpsilon
    positivity
  refine ⟨by omega, hscale, ?_, hJ k (by omega)⟩
  rw [log_cellRoleScale]
  have hm := mul_le_mul_of_nonneg_right hNk cellRoleEpsilon_margin.le
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectionBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single depth choice pays for all actual cell-selection codes -/
namespace Ostmann
open scoped Classical BigOperators

theorem character_selection_code_bound (c δ : ℝ) (k : ℕ) (hc : 0 < c) (hδ : 0 < δ) :
    ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤
      cellRoleCountBound (256 / (δ * c) + 3) k := by
  have hpos : 0 ≤ cellRoleCountBound (256 / (δ * c)) k :=
    cellRoleCountBound_nonneg (by positivity) k
  have hceil := Nat.ceil_lt_add_one hpos
  have hp : 1 ≤ Real.exp (2 * cellRoleEpsilon * k) :=
    Real.one_le_exp_iff.mpr (by unfold cellRoleEpsilon; positivity)
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ((k : ℝ) + 1) by positivity)
  have hk := Nat.cast_nonneg (α := ℝ) k
  change (characterTargetLabelBound c δ k : ℝ) < _ at hceil
  unfold cellRoleCountBound at hceil ⊢
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith only [hceil, hh, hk]

/-- This threshold precedes the density increment and is uniform over the
resulting depth, endpoint tests, target values and selected word lengths. -/
theorem character_selection_depth (c δ C b : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hb : 0 < b) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ ∀ k : ℕ, K ≤ k →
      1 ≤ k ∧ 1 ≤ cellRoleScale k ∧
      C + 20 * Real.log (cellRoleScale k) ≤ (k : ℝ) * Real.log 2 - 1 ∧
      ((characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) : ℝ) ≤ b * cellRoleScale k := by
  obtain ⟨K, hK, hdepth⟩ := character_depth_cutoff C (256 / (δ * c) + 3) b hb Kmin
  refine ⟨K, hK, ?_⟩
  intro k hk
  obtain ⟨hk1, hz, he, hcount⟩ := hdepth k hk
  exact ⟨hk1, hz, he, (character_selection_code_bound c δ k hc hδ).trans hcount⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCellCovering
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One fixed covering error for every selected character-cell list -/
namespace Ostmann
open scoped Classical BigOperators

theorem characterCellCoveringError_gt_one (c δ : ℝ) (k : ℕ) (hc : 0 < c) (hδ : 0 < δ) :
    1 < characterCellCoveringError c δ k := by
  unfold characterCellCoveringError
  have he : 0 < 64 / (δ * c) := by positivity
  have hn := Nat.cast_nonneg (α := ℝ) (characterTargetLabelBound c δ k)
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterConstructedRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected shells give the actual character prime ranges -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem prime_of_loglog_lower (p : ℕ) (hp : p.Prime) (a : ℝ)
    (ha : a ≤ Real.log (Real.log (p : ℝ))) : Real.exp (Real.exp a) ≤ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h₁ := Real.exp_le_exp.mpr ha
  rw [Real.exp_log (Real.log_pos hp1)] at h₁
  have h₂ := Real.exp_le_exp.mpr h₁
  rwa [Real.exp_log hp0] at h₂

theorem prime_of_loglog_upper (p : ℕ) (hp : p.Prime) (a : ℝ)
    (ha : Real.log (Real.log (p : ℝ)) ≤ a) : (p : ℝ) ≤ Real.exp (Real.exp a) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h₁ := Real.exp_le_exp.mpr ha
  rw [Real.exp_log (Real.log_pos hp1)] at h₁
  have h₂ := Real.exp_le_exp.mpr h₁
  rwa [Real.exp_log hp0] at h₂

theorem character_top_shell_log_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (u : ℝ) : ∀ p ∈ loglogShell P u,
      Real.exp u ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * Real.exp u := by
  intro p hp
  have hh := Finset.mem_filter.mp hp
  have hb := prime_shell_log_bounds u p (hP p hh.1) hh.2.1 hh.2.2
  refine ⟨hb.1.le, hb.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_d9]) (Real.exp_nonneg _)

theorem eventual_character_top_dominates_bulk (z γ ν : ℝ) (hz : 0 ≤ z) (hgap : γ < ν) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ) (u : ℝ), (m : ℝ) ≤ z * L → ν * L ≤ u →
      (m : ℝ) * Real.exp (γ * L) ≤ Real.exp u := by
  filter_upwards [eventual_bulk_word_small (ν - γ) z (by linarith) hz] with L hL
  intro m u hm hu
  exact hL m (γ * L) u (Real.exp u) hm (by linarith) le_rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterAmbientPrimeBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original prime band supplies its total mass and ambient ranges -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_character_prime_total {C : ℝ} (hM : MertensEstimate C)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α * L < Real.log (Real.log (p : ℝ)) ∧
        Real.log (Real.log (p : ℝ)) ≤ β * L) →
      (∑ p : P, (p : ℝ)⁻¹) ≤ (Real.exp 1 + 1) * (β - α + 1) * L := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_id.const_mul_atTop hα).eventually (eventually_ge_atTop (max C 0))]
    with L hL hbase P hP hrange
  have he : weightedIntervalMass P (fun p => Real.log (Real.log p))
      (fun p => (p : ℝ)⁻¹) (α * L) (β * L) = ∑ p : P, (p : ℝ)⁻¹ := by
    simp only [weightedIntervalMass]
    rw [Finset.filter_eq_self.mpr hrange]
    exact (Finset.sum_coe_sort P (fun p : ℕ => (p : ℝ)⁻¹)).symm
  have hh := prime_loglog_interval_mass_upper hM P hP (α * L) (β * L) hbase
    (mul_le_mul_of_nonneg_right hαβ.le (by linarith))
  rw [he] at hh
  have hp : 0 < Real.exp 1 + 1 := by positivity
  have hscale := mul_le_mul_of_nonneg_left hL hp.le
  nlinarith only [hh, hscale]

theorem character_ambient_prime_ranges (α β L : ℝ) (hα : 0 < α) (hL : 0 ≤ L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrange : ∀ p ∈ P, α * L < Real.log (Real.log (p : ℝ)) ∧
      Real.log (Real.log (p : ℝ)) ≤ β * L) :
    ∀ p ∈ P, Real.exp (Real.exp ((α / 2) * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp ((β + 1) * L)) := by
  intro p hp
  constructor
  · apply prime_of_loglog_lower p (hP p hp)
    exact (show (α / 2) * L ≤ α * L by nlinarith only [mul_nonneg hα.le hL]).trans
      (hrange p hp).1.le
  · apply prime_of_loglog_upper p (hP p hp)
    exact (hrange p hp).2.trans (by nlinarith only [hL])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterRoundedEndpoint
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integral endpoints with the original character product scale -/
namespace Ostmann
open scoped Classical

theorem characterEndpointFactor_pos (k : ℕ) : 0 < characterEndpointFactor k := by
  unfold characterEndpointFactor
  positivity

theorem character_rounded_endpoint_bounds (k : ℕ) (v U : ℝ) (hv : 2 ≤ v) (hUv : U + 1 ≤ v) :
    let X := characterRoundedEndpoint k v
    let τ := characterRoundedTau k v
    1 ≤ X ∧ (X : ℝ) = Real.exp (characterEndpointFactor k * τ) ∧
      2 ≤ τ ∧ (19 / 20 : ℝ) * Real.exp v ≤ τ ∧ τ ≤ Real.exp v ∧
      U ≤ Real.log τ ∧ Real.log τ ≤ v ∧
      Real.log (Real.log (X : ℝ)) ≤ v + Real.log (characterEndpointFactor k) := by
  intro X τ
  have hC := characterEndpointFactor_pos k
  have hCbig : 1000 ≤ characterEndpointFactor k := by
    have hp : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    unfold characterEndpointFactor
    linarith
  have he : 3 ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
  have hT : 1 ≤ characterEndpointFactor k * Real.exp v := by nlinarith
  have hf := floor_exp_log_bounds (characterEndpointFactor k * Real.exp v) hT
  have hXp : (0 : ℝ) < X := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hf.1
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have htlo : (19 / 20 : ℝ) * Real.exp v ≤ τ := by
    apply (le_div_iff₀ hC).mpr
    have hlow := hf.2.1
    change characterEndpointFactor k * Real.exp v - Real.log 2 ≤ Real.log (X : ℝ) at hlow
    nlinarith only [hlow, hCbig, he, hlog2]
  have hthi : τ ≤ Real.exp v := by
    apply (div_le_iff₀ hC).mpr
    exact hf.2.2.trans_eq (mul_comm _ _)
  have ht2 : 2 ≤ τ := by linarith
  have hτ : 0 < τ := by linarith
  have hidentity : characterEndpointFactor k * τ = Real.log (X : ℝ) := by
    dsimp [τ, characterRoundedTau, X]
    exact mul_div_cancel₀ _ hC.ne'
  have hU : U ≤ Real.log τ := by
    apply (Real.le_log_iff_exp_le hτ).mpr
    have hexp : Real.exp U * Real.exp 1 ≤ Real.exp v := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hUv
    have h2 : 2 * Real.exp U ≤ Real.exp U * Real.exp 1 := by
      nlinarith only [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 : ℝ)) (Real.exp_nonneg U)]
    nlinarith only [hexp, h2, htlo, Real.exp_nonneg v]
  refine ⟨hf.1, ?_, ht2, htlo, hthi, hU, ?_, ?_⟩
  · rw [hidentity, Real.exp_log hXp]
  · exact (Real.log_le_iff_le_exp hτ).mpr hthi
  · have hlogp : 0 < Real.log (X : ℝ) := by rw [← hidentity]; positivity
    apply (Real.log_le_iff_le_exp hlogp).mpr
    rw [Real.exp_add, Real.exp_log hC]
    exact hf.2.2.trans_eq (mul_comm _ _)

/-- The floor perturbation leaves every prime of the entire top shell in
its required original logarithmic word range. -/
theorem character_rounded_top_shell (k : ℕ) (v U : ℝ) (hv : 2 ≤ v) (hUv : U + 1 ≤ v)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∀ p ∈ loglogShell P v, characterRoundedTau k v ≤ Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ 3 * characterRoundedTau k v := by
  have hb := character_rounded_endpoint_bounds k v U hv hUv
  intro p hp
  have hpp := Finset.mem_filter.mp hp
  have hr := prime_shell_log_bounds v p (hP p hpp.1) hpp.2.1 hpp.2.2
  refine ⟨hb.2.2.2.2.1.trans hr.1.le, ?_⟩
  have he : Real.exp 1 ≤ (57 / 20 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_nonneg v)
  nlinarith only [hr.2, he', hb.2.2.2.1]

theorem character_rounded_anchor_pair (k : ℕ) (v U us : ℝ) (hv : 2 ≤ v)
    (hUv : U + 1 ≤ v) (hus : us + 2 ≤ v) :
    3 * Real.exp us + 3 * Real.exp v ≤ 4 * characterRoundedTau k v := by
  have hb := (character_rounded_endpoint_bounds k v U hv hUv).2.2.2.1
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he2 : 4 ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have he := Real.exp_le_exp.mpr hus
  rw [Real.exp_add] at he
  have hm := mul_le_mul_of_nonneg_left he2 (Real.exp_nonneg us)
  nlinarith only [he, hm, hb, Real.exp_nonneg v]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterIndexCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual prime log indices fit the fixed-cell selection budget -/
namespace Ostmann
open Filter

theorem primeLogIndex_le_characterIndexCutoff (β L : ℝ) (p : ℕ) (hp : p.Prime)
    (hbound : Real.log (Real.log (p : ℝ)) ≤ β * L) :
    primeLogIndex p ≤ characterIndexCutoff β L := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hh : Real.log (p : ℝ) ≤ Real.exp (β * L) :=
    (Real.log_le_iff_le_exp hlog).mp hbound
  have hindex : (primeLogIndex p : ℝ) ≤ characterIndexCutoff β L :=
    (primeLogIndex_bounds p hp).1.le.trans (hh.trans (Nat.le_ceil _))
  exact_mod_cast hindex

theorem eventual_character_index_cutoff (β : ℝ) (hβ : 0 < β) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, 5 * k ≤ characterIndexCutoff β L ∧
      ((characterIndexCutoff β L + 1 : ℕ) : ℝ) ≤ Real.exp ((β + 1) * L) := by
  have hlarge := (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hβ)).eventually
    (eventually_ge_atTop ((5 * k : ℕ) : ℝ))
  filter_upwards [hlarge, eventually_ge_atTop (max 0 (Real.log 3))] with L hlarge hL
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have he : 1 ≤ Real.exp (β * L) := Real.one_le_exp (mul_nonneg hβ.le hL0)
  have hthree : 3 ≤ Real.exp L := by
    have hh := Real.exp_le_exp.mpr ((le_max_right _ _).trans hL)
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3)] using hh
  constructor
  · have hh := hlarge.trans (Nat.le_ceil (Real.exp (β * L)))
    exact_mod_cast hh
  · have hceil := Nat.ceil_lt_add_one (Real.exp_nonneg (β * L))
    change (characterIndexCutoff β L : ℝ) < Real.exp (β * L) + 1 at hceil
    rw [show (β + 1) * L = β * L + L by ring, Real.exp_add]
    push_cast
    nlinarith only [hceil, he, mul_le_mul_of_nonneg_left hthree (Real.exp_nonneg (β * L))]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectedShellGeometry
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The chosen small shell and upper rich shell satisfy the actual cutoffs -/
namespace Ostmann
open Filter

theorem eventual_character_selected_shell_geometry (α β z : ℝ) (hα : 0 < α)
    (hαβ : α < β) (hz : 0 ≤ z) (q n : ℕ) (hq : 0 < q) (hn : 20000 ≤ n)
    (i j k : Fin q) (hij : i.val + 1 < j.val) (hjk : j.val + 1 < k.val) :
    let γs := characterBandPoint α β q (i.val + 1)
    let γw := characterBandPoint α β q (j.val + 1)
    let νa := characterBandPoint α β q k.val
    ∀ᶠ L : ℝ in atTop, ∀ us Ulate v : ℝ,
      characterBandPoint α β q i.val * L ≤ us → us + 1 ≤ γs * L →
      νa * L ≤ Ulate →
      Ulate + 5 * n ≤ characterBandPoint α β q (k.val + 1) * L →
      Ulate + (n : ℝ) / 10000 ≤ v → v + 1 ≤ Ulate + 2 * (n : ℝ) / 10000 →
      2 ≤ v ∧ us + 2 ≤ v ∧
      α * L ≤ us ∧ α * L ≤ v ∧ us ≤ β * L ∧ v ≤ β * L ∧
      α * L ≤ Ulate ∧ Ulate ≤ β * L ∧
      Ulate ≤ Real.log (characterRoundedTau n v) ∧
      Real.log (characterRoundedTau n v) ≤ Ulate + 2 * (n : ℝ) / 10000 ∧
      3 * Real.exp us + 3 * Real.exp v ≤ 4 * characterRoundedTau n v ∧
      ∀ m : ℕ, (m : ℝ) ≤ z * L → m * Real.exp (γw * L) ≤ characterRoundedTau n v := by
  intro γs γw νa
  have hmono := characterBandPoint_strictMono α β q hαβ hq
  have hgap : γs < νa := hmono (by omega)
  have hwgap : γw < νa := hmono hjk
  have hνapos : 0 < νa := hα.trans_le
    (characterBandPoint_bounds α β q k.val hαβ hq (by omega)).1
  have hUβ := (characterBandPoint_bounds α β q (k.val + 1) hαβ hq (by omega)).2
  have husα := (characterBandPoint_bounds α β q i.val hαβ hq (by omega)).1
  have hγsβ := (characterBandPoint_bounds α β q (i.val + 1) hαβ hq (by omega)).2
  have hνaα := (characterBandPoint_bounds α β q k.val hαβ hq (by omega)).1
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    (tendsto_id.const_mul_atTop hνapos).eventually (eventually_ge_atTop 2),
    (tendsto_id.const_mul_atTop (sub_pos.mpr hgap)).eventually (eventually_ge_atTop 2),
    eventual_character_top_dominates_bulk z γw νa hz hwgap] with L hL hvlarge hsep hbulk
  intro us Ulate v huslo hushi hUlo hUhi hvlo hvhi
  simp only [id_eq] at hvlarge hsep
  have hv2 : 2 ≤ v := by linarith only [hvlarge, hUlo, hvlo, hnR]
  have hUs : us + 2 ≤ v := by nlinarith only [hushi, hUlo, hvlo, hsep, hnR]
  have hUv : Ulate + 1 ≤ v := by linarith only [hvlo, hnR]
  have hdata := character_rounded_endpoint_bounds n v Ulate hv2 hUv
  have hUupper : Ulate ≤ β * L := by
    have hh := mul_le_mul_of_nonneg_right hUβ hL
    nlinarith only [hh, hUhi, hnR]
  have hvupper : v ≤ β * L := by
    have hh := mul_le_mul_of_nonneg_right hUβ hL
    nlinarith only [hh, hUhi, hvhi, hnR]
  have huslower : α * L ≤ us := (mul_le_mul_of_nonneg_right husα hL).trans huslo
  have hUlower : α * L ≤ Ulate := (mul_le_mul_of_nonneg_right hνaα hL).trans hUlo
  have hvlower : α * L ≤ v := by linarith only [hUlower, hvlo, hnR]
  have husupper : us ≤ β * L := by
    have hh := mul_le_mul_of_nonneg_right hγsβ hL
    linarith only [hh, hushi]
  have hτlo := hdata.2.2.2.2.2.1
  have hτhi := hdata.2.2.2.2.2.2.1
  refine ⟨hv2, hUs, huslower, hvlower, husupper, hvupper, hUlower, hUupper,
    hτlo, hτhi.trans (by linarith only [hvhi]),
    character_rounded_anchor_pair n v Ulate us hv2 hUv hUs, ?_⟩
  intro m hm
  have hτpos : 0 < characterRoundedTau n v := by linarith only [hdata.2.2.1]
  have hh := hbulk m (Real.log (characterRoundedTau n v)) hm (hUlo.trans hτlo)
  rwa [Real.exp_log hτpos] at hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialGapRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the initial gap without changing the endpoint rate -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem eventually_bulkCount_bounds (z : ℝ) (hz : 0 < z) :
    ∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 ≤ ⌊z * L⌋₊ ∧
      (⌊z * L⌋₊ : ℝ) ≤ z * L ∧ z * L ≤ 2 * ⌊z * L⌋₊ := by
  filter_upwards [eventually_ge_atTop (2 / z)] with L hL
  have h₂ : (2 : ℝ) ≤ z * L := by simpa only [mul_comm] using (div_le_iff₀ hz).mp hL
  have hLp : 0 < L := (div_pos (by norm_num : (0 : ℝ) < 2) hz).trans_le hL
  have hm : 1 ≤ ⌊z * L⌋₊ := (Nat.one_le_floor_iff (z * L)).mpr (by linarith)
  have hm' : (1 : ℝ) ≤ ⌊z * L⌋₊ := by exact_mod_cast hm
  exact ⟨hLp, hm, Nat.floor_le (by positivity), by linarith [Nat.lt_floor_add_one (z * L)]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterParameterChoice
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choose the character gap before the depth and the growing word length -/
namespace Ostmann

/-- The initial repeat loss and density-rescaled anchor energy require one
fixed gap constant. It does not depend on the later depth or selected cells. -/
theorem character_gap_choice (a Ctotal Aend Bword Cdy ε : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧
      2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
        (Aend + 2 * Bword + 1) + 2) ≤ B ∧
      2 * (Aend + 2 * Bword + 3) +
        (Cdy / a + max (Real.log 3) 0 + ε) + Real.log 2 + 6 ≤ B + 20 * Real.log a := by
  let Brepeat := 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
    (Aend + 2 * Bword + 1) + 2)
  let Banchor := 2 * (Aend + 2 * Bword + 3) +
    (Cdy / a + max (Real.log 3) 0 + ε) + Real.log 2 + 6 - 20 * Real.log a
  refine ⟨max 1 (max Brepeat Banchor), le_max_left _ _, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · have hh := (le_max_right Brepeat Banchor).trans (le_max_right 1 (max Brepeat Banchor))
    dsimp only [Banchor] at hh
    linarith

/-- The same depth threshold pays for every label, pivot normalizer and
nonbulk cost, while leaving the final permutation-entropy margin. -/
theorem character_depth_and_mass_budget (c δ Cmass Cfinal B B₁ : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (_hCmass : 0 ≤ Cmass) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ ∀ k : ℕ, K ≤ k →
      1 ≤ k ∧ 1 ≤ cellRoleScale k ∧
      Cfinal + (B + 20 * Real.log (cellRoleScale k) + 1) + 2 * B₁ + 1 ≤
        ((k - 1 : ℕ) : ℝ) * Real.log 2 - 1 ∧
      4 * Cmass *
        (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) ≤ cellRoleScale k := by
  let C := Cfinal + B + 2 * B₁ + 2 + Real.log 2
  let b := (4 * max Cmass 1)⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨K, hK, hh⟩ := character_selection_depth c δ C b hc hδ hb Kmin
  refine ⟨K, hK, fun k hk => ?_⟩
  obtain ⟨hk1, hz, hentropy, hcount⟩ := hh k hk
  refine ⟨hk1, hz, ?_, ?_⟩
  · have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk1, Nat.cast_one]
    rw [hkcast]
    dsimp only [C] at hentropy
    nlinarith only [hentropy]
  · have hmax : 0 < 4 * max Cmass 1 := by positivity
    have hcount' :
        (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) ≤
          cellRoleScale k / (4 * max Cmass 1) := by
      simpa only [b, div_eq_mul_inv, mul_comm] using hcount
    have hprod := (le_div_iff₀ hmax).mp hcount'
    have hcmax : 4 * Cmass ≤ 4 * max Cmass 1 := by
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
    have hnat : (0 : ℝ) ≤ (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) :=
      Nat.cast_nonneg _
    nlinarith only [hprod, mul_le_mul_of_nonneg_right hcmax hnat]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterLengthBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform rounded character lengths -/
namespace Ostmann
open Filter

theorem eventual_character_length_bounds (z : ℝ) (hz : 1 < z) :
    ∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 ≤ ⌊z * L⌋₊ ∧
      L ≤ (⌊z * L⌋₊ : ℝ) ∧ (⌊z * L⌋₊ : ℝ) ≤ z * L ∧
      z * L ≤ 2 * (⌊z * L⌋₊ : ℝ) := by
  filter_upwards [eventually_bulkCount_bounds z (by linarith),
    eventually_ge_atTop (1 / (z - 1))] with L hbounds hL
  refine ⟨hbounds.1, hbounds.2.1, ?_, hbounds.2.2.1, hbounds.2.2.2⟩
  have hz0 : 0 < z - 1 := by linarith
  have hh := (div_le_iff₀ hz0).mp hL
  have hf := Nat.lt_floor_add_one (z * L)
  nlinarith only [hh, hf]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterSelectionScales
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rates for the actual tail count and top-word bin count -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_character_tail_count_rate (a β D : ℝ) (ha : 0 < a) (hβ : 0 ≤ β) :
    ∀ᶠ L : ℝ in atTop, ∀ (m : ℕ) (T : ℝ) (E : Finset ℕ),
      L ≤ m → 0 < T → Real.log T ≤ β * L + D →
      a * Real.exp (T / 2) / T ^ 3 ≤ E.card →
      Real.sqrt (Real.exp T) * Real.exp (-(3 * β + 1) * m) ≤ E.card := by
  have he : ∀ᶠ L : ℝ in atTop, Real.exp (-L) ≤ a * Real.exp (-3 * D) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually_le_const (by positivity)
  filter_upwards [he] with L he m T E hLm hT hlog hE
  apply le_trans _ hE
  have hp : T ^ 3 ≤ Real.exp (3 * (β * L + D)) := by
    calc
      T ^ 3 = Real.exp (3 * Real.log T) := by
        rw [show (3 : ℝ) = (3 : ℕ) from rfl, Real.exp_nat_mul, Real.exp_log hT]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hcoef : 0 ≤ 3 * β + 1 := by linarith
  have hexp : Real.exp (-(3 * β + 1) * m) * T ^ 3 ≤ a := by
    calc
      _ ≤ Real.exp (-(3 * β + 1) * L) * Real.exp (3 * (β * L + D)) :=
        mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) hp (by positivity) (by positivity)
      _ = Real.exp (-L) * Real.exp (3 * D) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1; ring
      _ ≤ (a * Real.exp (-3 * D)) * Real.exp (3 * D) :=
        mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = a := by rw [mul_assoc, ← Real.exp_add]; simp
  have hs : Real.sqrt (Real.exp T) = Real.exp (T / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1; ring
  rw [hs]
  apply (le_div_iff₀ (pow_pos hT 3)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg (T / 2))]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CollisionTestTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision stability controls every chosen bounded residue test -/

namespace Ostmann

open scoped BigOperators Classical

theorem residueTestError_eq (S : Finset ℕ) (μ f : ℕ → ℝ) :
    residueTestError S μ f = ∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) * f r := by
  simp only [residueTestError, residueTestMean, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

theorem residueTestError_sq_le (S : Finset ℕ) (μ f : ℕ → ℝ) (p : ℕ)
    (hcard : S.card ≤ p) (hf : ∀ r ∈ S, |f r| ≤ 1) :
    residueTestError S μ f ^ 2 ≤ (p : ℝ) * ∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) ^ 2 := by
  rw [residueTestError_eq]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun r => μ r - 1 / (S.card : ℝ)) f
  have henergy : (∑ r ∈ S, f r ^ 2) ≤ (p : ℝ) := by
    calc
      _ ≤ ∑ _r ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun r hr => by
        have hh := hf r hr
        have ha := abs_nonneg (f r)
        nlinarith [sq_abs (f r)])
      _ = (S.card : ℝ) := by simp
      _ ≤ p := by exact_mod_cast hcard
  have hm := mul_le_mul_of_nonneg_left henergy
    (Finset.sum_nonneg (s := S) (fun r _ => sq_nonneg (μ r - 1 / (S.card : ℝ))))
  exact hCS.trans (by simpa only [mul_comm] using hm)

theorem collisionDefect_controls_tests (p : ℕ) (S T : Finset ℕ) (μ ν f g : ℕ → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty) (hcard : S.card + T.card ≤ p)
    (hf : ∀ r ∈ S, |f r| ≤ 1) (hg : ∀ r ∈ T, |g r| ≤ 1) :
    residueTestError S μ f ^ 2 + residueTestError T ν g ^ 2 ≤
      (p : ℝ) * collisionDefect p S T μ ν := by
  have hs := residueTestError_sq_le S μ f p (by omega) hf
  have ht := residueTestError_sq_le T ν g p (by omega) hg
  have hgap := four_div_le_inverse_add_inverse
    (by exact_mod_cast hS.card_pos : (0 : ℝ) < S.card)
    (by exact_mod_cast hT.card_pos : (0 : ℝ) < T.card)
    (by exact_mod_cast hcard : (S.card : ℝ) + T.card ≤ p)
  have hpgap := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (sub_nonneg.mpr hgap)
  unfold collisionDefect
  nlinarith only [hs, ht, hpgap]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TypicalEndpoints
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Few endpoints fail a positive prime test

The argument tests the uniform measure on the actual exceptional set. This
turns the collision estimate for every large subset into a cardinality bound.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem weighted_real_sum_sq {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, w i * f i) ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, w i * f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * f i)
  have h1 : (∑ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * f i)) =
      ∑ i ∈ S, w i * f i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hw i hi)]
  have h2 : (∑ i ∈ S, Real.sqrt (w i) ^ 2) = ∑ i ∈ S, w i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.sq_sqrt (hw i hi)
  have h3 : (∑ i ∈ S, (Real.sqrt (w i) * f i) ^ 2) = ∑ i ∈ S, w i * f i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rwa [h1, h2, h3] at h

theorem weighted_mean_commute (E P : Finset ℕ) (w : ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    (∑ p ∈ P, w p * residueTestMean E (fun a => f a p)) =
      residueTestMean E (fun a => ∑ p ∈ P, w p * f a p) := by
  unfold residueTestMean
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]

/-- No large subset can consist entirely of endpoints whose weighted mean
is less than half the positive reference mean. -/
theorem badEndpoints_card_lt (A P : Finset ℕ) (w g : ℕ → ℝ)
    (f : ℕ → ℕ → ℝ) (δ E : ℝ) (K : ℕ) (hK : 0 < K) (hδ : 0 < δ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hmass : 0 < ∑ p ∈ P, w p)
    (href : δ * (∑ p ∈ P, w p) ≤ ∑ p ∈ P, w p * g p)
    (hsmall : 4 * E < δ ^ 2 * ∑ p ∈ P, w p)
    (htest : ∀ B ⊆ A, K ≤ B.card →
      (∑ p ∈ P, w p * (residueTestMean B (fun a => f a p) - g p) ^ 2) ≤ E) :
    (badEndpoints A P w f δ).card < K := by
  by_contra! hbad
  let B := badEndpoints A P w f δ
  have hB : B.Nonempty := Finset.card_pos.mp (hK.trans_le hbad)
  have hBc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hsum : (∑ a ∈ B, ∑ p ∈ P, w p * f a p) <
      (B.card : ℝ) * ((δ / 2) * ∑ p ∈ P, w p) := by
    calc
      _ < ∑ _a ∈ B, ((δ / 2) * ∑ p ∈ P, w p) :=
        Finset.sum_lt_sum_of_nonempty hB (fun a ha => (Finset.mem_filter.mp ha).2)
      _ = _ := by simp
  have hmean : (∑ p ∈ P, w p * residueTestMean B (fun a => f a p)) <
      (δ / 2) * ∑ p ∈ P, w p := by
    rw [weighted_mean_commute, residueTestMean]
    exact (div_lt_iff₀ hBc).mpr (by nlinarith only [hsum])
  let e := fun p => residueTestMean B (fun a => f a p) - g p
  have he : (∑ p ∈ P, w p * e p) < -(δ / 2) * ∑ p ∈ P, w p := by
    simp only [e, mul_sub, Finset.sum_sub_distrib]
    linarith
  have hsquare := weighted_real_sum_sq P w e hw
  have htestB := htest B (Finset.filter_subset _ _) hbad
  have hupper := mul_le_mul_of_nonneg_left htestB hmass.le
  change (∑ p ∈ P, w p) * (∑ p ∈ P, w p * e p ^ 2) ≤ _ at hupper
  have hlo : (δ * (∑ p ∈ P, w p)) ^ 2 / 4 < (∑ p ∈ P, w p * e p) ^ 2 := by
    nlinarith [mul_pos hδ hmass]
  have hsmall' := mul_lt_mul_of_pos_left hsmall hmass
  nlinarith

/-- Finitely many prime tests hold simultaneously after deleting at most
the sum of their exceptional-set bounds. -/
theorem simultaneous_good_endpoints {ι : Type*} [DecidableEq ι]
    (E : Finset ℕ) (J : Finset ι) (bad : ι → Finset ℕ) (K : ℕ)
    (hbad : ∀ j ∈ J, (bad j).card ≤ K) :
    ∃ G ⊆ E, E.card ≤ G.card + J.card * K ∧
      ∀ a ∈ G, ∀ j ∈ J, a ∉ bad j := by
  let U := J.biUnion bad
  let G := E \ U
  have hU : U.card ≤ J.card * K := by
    calc
      _ ≤ ∑ j ∈ J, (bad j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ J, K := Finset.sum_le_sum hbad
      _ = _ := by simp
  refine ⟨G, Finset.sdiff_subset, ?_, ?_⟩
  · have hsplit := Finset.card_sdiff_add_card_inter E U
    have hinter : (E ∩ U).card ≤ U.card := Finset.card_le_card Finset.inter_subset_right
    dsimp [G]
    omega
  · intro a ha j hj hab
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_biUnion.mpr ⟨j, hj, hab⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_HarmonicTestTransfer
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic test errors from the full collision budget -/

namespace Ostmann

open scoped BigOperators Classical

theorem uniform_fiber_test_error (B S : Finset ℕ) (r : ℕ → ℕ) (f : ℕ → ℝ)
    (hr : ∀ a ∈ B, r a ∈ S) :
    residueTestError S (fiberMass B (fun _ => 1 / (B.card : ℝ)) r) f =
      residueTestMean B (fun a => f (r a)) - residueTestMean S f := by
  rw [residueTestError, sum_fiberMass_mul B S _ r f hr]
  simp only [residueTestMean, one_div, ← Finset.mul_sum]
  ring

/-- Passing from the `log(p)` collision budget to harmonic mass only loses
the reciprocal of the smallest `log(p)` in the tested set. -/
theorem harmonic_collision_test_errors (P R : Finset ℕ) (hPR : P ⊆ R)
    (S T : ℕ → Finset ℕ) (μ ν f : ℕ → ℕ → ℝ) (B E : ℝ) (hB : 0 < B)
    (hprime : ∀ p ∈ R, p.Prime)
    (hS : ∀ p ∈ R, (S p).Nonempty) (hT : ∀ p ∈ R, (T p).Nonempty)
    (hcard : ∀ p ∈ R, (S p).card + (T p).card ≤ p)
    (hf : ∀ p ∈ P, ∀ r ∈ S p, |f p r| ≤ 1)
    (hlog : ∀ p ∈ P, B ≤ Real.log (p : ℝ))
    (hbudget : (∑ p ∈ R, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ E) :
    (∑ p ∈ P, (p : ℝ)⁻¹ * residueTestError (S p) (μ p) (f p) ^ 2) ≤ E / B := by
  apply (le_div_iff₀ hB).mpr
  rw [mul_comm, Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpR := hPR hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hpR).pos
      have hh := collisionDefect_controls_tests p (S p) (T p) (μ p) (ν p) (f p)
        (fun _ => 0) (hS p hpR) (hT p hpR) (hcard p hpR) (hf p hp)
        (by intros; norm_num)
      have hz : residueTestError (T p) (ν p) (fun _ => 0) = 0 := by
        simp [residueTestError, residueTestMean]
      rw [hz, zero_pow (by decide : 2 ≠ 0), add_zero] at hh
      have herr : (p : ℝ)⁻¹ * residueTestError (S p) (μ p) (f p) ^ 2 ≤
          collisionDefect p (S p) (T p) (μ p) (ν p) := by
        apply (le_of_mul_le_mul_left _ hp0)
        calc
          _ = residueTestError (S p) (μ p) (f p) ^ 2 := by field_simp
          _ ≤ _ := hh
      calc
        _ ≤ Real.log (p : ℝ) * ((p : ℝ)⁻¹ * residueTestError (S p) (μ p) (f p) ^ 2) :=
          mul_le_mul_of_nonneg_right (hlog p hp) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left herr (hB.le.trans (hlog p hp))
    _ ≤ ∑ p ∈ R, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hPR
      intro p hp _
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (hprime p hp).one_le))
        (collisionDefect_nonneg _ _ _ _ (hS p hp) (hT p hp) (hcard p hp))
    _ ≤ E := hbudget

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_RootCollisions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collisions of uniform root populations

The root populations at the end of §3 occupy translated intervals. Their
collision upper bound depends on the diameter and their cardinality.
-/

namespace Ostmann

open scoped BigOperators

theorem sum_uniform_mass (s : Finset ℕ) (hs : s.Nonempty) :
    (∑ _a ∈ s, (1 / (s.card : ℝ))) = 1 := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_one_div_cancel hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailEndpointTests
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint exceptional set for an eventual prime decomposition -/

namespace Ostmann

open scoped BigOperators Classical

theorem uniform_subset_tail_collision_bound {A B : Set ℕ}
    (hA : A.Infinite) (hB : B.Infinite) (N X Q K : ℕ)
    (hX : 1 ≤ X) (hQ : 1 ≤ Q) (hK : 0 < K)
    (hdis : ∀ p ∈ Nat.primesLE Q, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (E D : Finset ℕ) (hE : K ≤ E.card) (hD : K ≤ D.card)
    (hEtail : ∀ a ∈ E, a ∈ A ∧ N + Q < a ∧ a ≤ X)
    (hDtail : ∀ b ∈ D, b ∈ B ∧ N + Q < b ∧ b ≤ X)
    (C : ℝ) (hM : MertensLowerBound C) :
    (∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) * tailCollisionDefect A N p E D
      (fun _ => 1 / (E.card : ℝ)) (fun _ => 1 / (D.card : ℝ))) ≤
      2 * Real.log X - 4 * Real.log Q + 4 * C + 2 * (1 / (K : ℝ)) * Real.log 4 * Q := by
  have hEne : E.Nonempty := Finset.card_pos.mp (hK.trans_le hE)
  have hDne : D.Nonempty := Finset.card_pos.mp (hK.trans_le hD)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  apply finite_measure_collision_stability (Nat.primesLE Q) E D
    (fun _ => 1 / (E.card : ℝ)) (fun _ => 1 / (D.card : ℝ))
    (tailSupport A N) (fun p => Finset.range p \ tailSupport A N p)
    (fun p a => a % p) negativeResidue X Q (1 / (K : ℝ)) (Real.log 4) C hX
    (fun p hp => Nat.prime_of_mem_primesLE hp)
    (fun a ha => (hEtail a ha).2.2) (fun b hb => (hDtail b hb).2.2)
    (by intros; positivity) (by intros; positivity)
    (sum_uniform_mass E hEne) (sum_uniform_mass D hDne)
    (fun _ _ => one_div_le_one_div_of_le hKr (by exact_mod_cast hE))
    (fun _ _ => one_div_le_one_div_of_le hKr (by exact_mod_cast hD))
    (fun p hp => tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos)
    (fun p hp => tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos (hdis p hp))
  · intro p hp a ha
    apply mod_mem_tailSupport (Nat.prime_of_mem_primesLE hp).pos (hEtail a ha).1
    have := Nat.le_of_mem_primesLE hp
    have := (hEtail a ha).2.1
    omega
  · intro p hp b hb
    apply negativeResidue_mem_complement (Nat.prime_of_mem_primesLE hp).pos (hdis p hp) (hDtail b hb).1
    have := Nat.le_of_mem_primesLE hp
    have := (hDtail b hb).2.1
    omega
  · intros; rfl
  · intro p hp a ha b hb
    exact negativeResidue_eq_iff (Nat.prime_of_mem_primesLE hp).pos
  · positivity
  · exact prime_log_weight_le Q
  · exact hM Q hQ

theorem few_bad_tail_endpoints {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N X Q K : ℕ) (hX : 1 ≤ X) (hQ : 1 ≤ Q) (hK : 0 < K)
    (hdis : ∀ p ∈ Nat.primesLE Q, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (E D P : Finset ℕ) (hD : K ≤ D.card)
    (hEtail : ∀ a ∈ E, a ∈ A ∧ N + Q < a ∧ a ≤ X)
    (hDtail : ∀ b ∈ D, b ∈ B ∧ N + Q < b ∧ b ≤ X)
    (hP : P ⊆ Nat.primesLE Q) (b δ C : ℝ) (hb : 0 < b) (hδ : 0 < δ)
    (hM : MertensLowerBound C) (hlog : ∀ p ∈ P, b ≤ Real.log (p : ℝ))
    (F : ℕ → ℕ → ℝ) (hF : ∀ p ∈ P, ∀ r ∈ tailSupport A N p, |F p r| ≤ 1)
    (hmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹)
    (href : δ * (∑ p ∈ P, (p : ℝ)⁻¹) ≤
      ∑ p ∈ P, (p : ℝ)⁻¹ * residueTestMean (tailSupport A N p) (F p))
    (hsmall : 4 * ((2 * Real.log X - 4 * Real.log Q + 4 * C +
      2 * (1 / (K : ℝ)) * Real.log 4 * Q) / b) < δ ^ 2 * ∑ p ∈ P, (p : ℝ)⁻¹) :
    (badEndpoints E P (fun p => (p : ℝ)⁻¹) (fun a p => F p (a % p)) δ).card < K := by
  apply badEndpoints_card_lt E P (fun p => (p : ℝ)⁻¹)
    (fun p => residueTestMean (tailSupport A N p) (F p)) (fun a p => F p (a % p)) δ _ K hK hδ
    (by intros; positivity) hmass href hsmall
  intro E' hE'E hE'
  have hEtail' : ∀ a ∈ E', a ∈ A ∧ N + Q < a ∧ a ≤ X := fun a ha => hEtail a (hE'E ha)
  have hbudget := uniform_subset_tail_collision_bound hA hB N X Q K hX hQ hK hdis
    E' D hE' hD hEtail' hDtail C hM
  have herr := harmonic_collision_test_errors P (Nat.primesLE Q) hP
    (tailSupport A N) (fun p => Finset.range p \ tailSupport A N p)
    (fun p => residueMass E' (fun _ => 1 / (E'.card : ℝ)) p)
    (fun p => fiberMass D (fun _ => 1 / (D.card : ℝ)) (negativeResidue p)) F b _ hb
    (fun p hp => Nat.prime_of_mem_primesLE hp)
    (fun p hp => tailSupport_nonempty hA N p (Nat.prime_of_mem_primesLE hp).pos)
    (fun p hp => tailSupport_complement_nonempty hB (Nat.prime_of_mem_primesLE hp).pos (hdis p hp))
    (fun p _ => (tailSupport_card_add_complement A N p).le) hF hlog hbudget
  apply le_trans (le_of_eq ?_) herr
  apply Finset.sum_congr rfl
  intro p hp
  congr 2
  symm
  apply uniform_fiber_test_error
  intro a ha
  apply mod_mem_tailSupport (Nat.prime_of_mem_primesLE (hP hp)).pos (hEtail' a ha).1
  have := Nat.le_of_mem_primesLE (hP hp)
  have := (hEtail' a ha).2.1
  omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandTails
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite tails of the two summands -/

namespace Ostmann

open scoped Classical

theorem summandPrefix_card_split (A : Set ℕ) (lo hi : ℕ) (hle : lo ≤ hi) :
    (summandPrefix A hi).card = (summandPrefix A lo).card + (summandTail A lo hi).card := by
  have hlo : (summandPrefix A hi).filter (fun n => n ≤ lo) = summandPrefix A lo := by
    ext n
    simp only [Finset.mem_filter, mem_summandPrefix]
    constructor
    · rintro ⟨⟨ha, _⟩, hn⟩; exact ⟨ha, hn⟩
    · rintro ⟨ha, hn⟩; exact ⟨⟨ha, hn.trans hle⟩, hn⟩
  have hhi : (summandPrefix A hi).filter (fun n => ¬ n ≤ lo) = summandTail A lo hi := by
    ext n
    simp only [Finset.mem_filter, mem_summandPrefix, mem_summandTail]
    constructor
    · rintro ⟨⟨ha, hh⟩, hn⟩; exact ⟨ha, Nat.lt_of_not_ge hn, hh⟩
    · rintro ⟨ha, hn, hh⟩; exact ⟨⟨ha, hh⟩, Nat.not_le_of_lt hn⟩
  have hh := Finset.card_filter_add_card_filter_not (s := summandPrefix A hi) (fun n => n ≤ lo)
  rw [hlo, hhi] at hh
  exact hh.symm

theorem positiveSummandTail_bounds (A : Set ℕ) (lo hi : ℕ) {x : ℤ}
    (hx : x ∈ positiveSummandTail A lo hi) : (lo : ℤ) < x ∧ x ≤ hi := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hnlo, hnhi⟩ := (mem_summandTail A lo hi n).mp hn
  exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩

theorem negativeSummandTail_bounds (B : Set ℕ) (lo hi : ℕ) {x : ℤ}
    (hx : x ∈ negativeSummandTail B lo hi) : -(hi : ℤ) ≤ x ∧ x < -(lo : ℤ) := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hnlo, hnhi⟩ := (mem_summandTail B lo hi n).mp hn
  constructor <;> omega

theorem EventuallyPrimeSumset.tail_prime_differences {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N : ℕ, ∀ lo hi : ℕ, N ≤ lo →
      ∀ x ∈ positiveSummandTail A lo hi, ∀ y ∈ negativeSummandTail B lo hi,
        (x - y).natAbs.Prime ∧ (lo : ℤ) < x - y := by
  obtain ⟨N, hN⟩ := h.prime_add
  refine ⟨N, ?_⟩
  intro lo hi hNlo x hx y hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
  obtain ⟨hbB, _, _⟩ := (mem_summandTail B lo hi b).mp hb
  have hab : (a : ℤ) - -(b : ℤ) = ((a + b : ℕ) : ℤ) := by push_cast; ring
  rw [hab, Int.natAbs_natCast]
  exact ⟨hN a haA b hbB (by omega), by exact_mod_cast (by omega : lo < a + b)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailCountingBudget
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the short initial segment preserves the square-root lower bound -/

namespace Ostmann

open Filter

theorem eventual_tail_counting_budget (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Set ℕ) (lo hi : ℕ), lo ≤ hi → 1 ≤ lo →
      (lo : ℝ) ≤ Real.exp (9 * L / 10) →
      a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix A hi).card →
      (summandPrefix A lo).card ≤ C * Real.sqrt (lo : ℝ) * Real.log (lo : ℝ) ^ 2 →
      (a / 2) * Real.exp (L / 2) / L ^ 3 ≤ (summandTail A lo hi).card := by
  have hp := ((isLittleO_pow_exp_pos_mul_atTop 5 (show (0 : ℝ) < 1 / 20 by norm_num)).const_mul_left
    (2 * C / a)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hp, eventually_ge_atTop (1 : ℝ)] with L hpoly hL A lo hi hlo h1 hupper hsize hsmall
  have hLp : 0 < L := by linarith
  have hloR : (1 : ℝ) ≤ lo := by exact_mod_cast h1
  have hloPos : (0 : ℝ) < lo := by linarith
  have hlog0 : 0 ≤ Real.log (lo : ℝ) := Real.log_nonneg hloR
  have hlog : Real.log (lo : ℝ) ≤ L := by
    have hh := Real.log_le_log hloPos hupper
    rw [Real.log_exp] at hh
    linarith
  have hsqrt : Real.sqrt (lo : ℝ) ≤ Real.exp (9 * L / 20) := by
    have hh := Real.sqrt_le_sqrt hupper
    have he : Real.exp (9 * L / 10) = (Real.exp (9 * L / 20)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rwa [he, Real.sqrt_sq (Real.exp_nonneg _)] at hh
  have hsmall' : (summandPrefix A lo).card ≤ C * Real.exp (9 * L / 20) * L ^ 2 := by
    apply hsmall.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hC)
      (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _) (by positivity)
  have hpoly' : (2 * C / a) * L ^ 5 ≤ Real.exp (L / 20) := by
    have he : Real.exp ((1 / 20 : ℝ) * L) = Real.exp (L / 20) := by congr 1; ring
    rw [he] at hpoly
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 * C / a) * L ^ 5),
      abs_of_pos (Real.exp_pos _), one_mul] using hpoly
  have hdiscard : C * Real.exp (9 * L / 20) * L ^ 2 ≤ (a / 2) * Real.exp (L / 2) / L ^ 3 := by
    apply (le_div_iff₀ (pow_pos hLp 3)).mpr
    have hh : C * L ^ 5 ≤ (a / 2) * Real.exp (L / 20) := by
      have hm := mul_le_mul_of_nonneg_right hpoly' (show 0 ≤ a / 2 by positivity)
      have hcancel : (2 * C / a) * L ^ 5 * (a / 2) = C * L ^ 5 := by
        calc
          _ = (C * L ^ 5) * (a * a⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ ha.ne', mul_one]
      rw [hcancel] at hm
      linarith only [hm]
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg (9 * L / 20))
    have he : Real.exp (9 * L / 20) * Real.exp (L / 20) = Real.exp (L / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    calc
      _ = Real.exp (9 * L / 20) * (C * L ^ 5) := by ring
      _ ≤ Real.exp (9 * L / 20) * ((a / 2) * Real.exp (L / 20)) := hm
      _ = _ := by rw [mul_left_comm, he]
  have hsplit : (summandPrefix A hi).card =
      (summandPrefix A lo).card + (summandTail A lo hi).card := summandPrefix_card_split A lo hi hlo
  have hsplitR : ((summandPrefix A hi).card : ℝ) =
      (summandPrefix A lo).card + (summandTail A lo hi).card := by exact_mod_cast hsplit
  have hh := hsmall'.trans hdiscard
  ring_nf at hh hsize ⊢
  linarith only [hh, hsize, hsplitR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_LargeSummandTails
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large actual tails from the published summand counting bounds -/

namespace Ostmann

open Filter
open scoped Classical

theorem exists_large_summand_tails (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ L : ℝ in atTop, ∀ N : ℕ, (N : ℝ) = Real.exp L →
      a * Real.exp (L / 2) / L ^ 3 ≤ (positiveSummandTail A (summandTailCutoff L) N).card ∧
      a * Real.exp (L / 2) / L ^ 3 ≤ (negativeSummandTail B (summandTailCutoff L) N).card ∧
      (∀ x ∈ positiveSummandTail A (summandTailCutoff L) N,
        0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ N) ∧
      (∀ y ∈ negativeSummandTail B (summandTailCutoff L) N,
        -(N : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ 0) ∧
      (∀ x ∈ positiveSummandTail A (summandTailCutoff L) N,
        ∀ y ∈ negativeSummandTail B (summandTailCutoff L) N,
        (x - y).natAbs.Prime ∧ Real.exp (9 * L / 10) < ((x - y).natAbs : ℝ)) := by
  obtain ⟨a, C, ha, hC, N₀, hcounts⟩ := hsize A B hA hB h
  obtain ⟨N₁, hprime⟩ := h.tail_prime_differences
  let K := max N₀ (max N₁ 2)
  refine ⟨a / 2, by positivity, ?_⟩
  filter_upwards [eventual_tail_counting_budget a C ha hC.le,
    eventually_ge_atTop (2 * ((K : ℝ) + 2))] with L hbudget hL N hN
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hLpos : 0 < L := by linarith
  have hL0 : 0 ≤ L := hLpos.le
  have hKexp : (K : ℝ) ≤ Real.exp (9 * L / 10) := by
    have he := Real.add_one_le_exp (9 * L / 10)
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    linarith
  have hKcut : K ≤ summandTailCutoff L := Nat.le_floor hKexp
  have hcutupper : (summandTailCutoff L : ℝ) ≤ Real.exp (9 * L / 10) :=
    Nat.floor_le (Real.exp_nonneg _)
  have hcutN : summandTailCutoff L ≤ N := by
    have he : Real.exp (9 * L / 10) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
    have hh := hcutupper.trans he
    rw [← hN] at hh
    exact_mod_cast hh
  have hN₀cut : N₀ ≤ summandTailCutoff L := (le_max_left _ _).trans hKcut
  have hN₁cut : N₁ ≤ summandTailCutoff L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hKcut)
  have h2cut : 2 ≤ summandTailCutoff L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hKcut)
  have hcntN := hcounts N (hN₀cut.trans hcutN) (h2cut.trans hcutN)
  have hcntCut := hcounts (summandTailCutoff L) hN₀cut h2cut
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (L / 2) := by
    rw [hN]
    have he : Real.exp L = (Real.exp (L / 2)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
    rw [he, Real.sqrt_sq (Real.exp_nonneg _)]
  have hlog : Real.log (N : ℝ) = L := by rw [hN, Real.log_exp]
  have hsa : a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix A N).card := by
    simpa only [hsqrt, hlog] using hcntN.1
  have hsb : a * Real.exp (L / 2) / L ^ 3 ≤ (summandPrefix B N).card := by
    simpa only [hsqrt, hlog] using hcntN.2.2.1
  have htailA := hbudget A (summandTailCutoff L) N hcutN (by omega) hcutupper hsa hcntCut.2.1
  have htailB := hbudget B (summandTailCutoff L) N hcutN (by omega) hcutupper hsb hcntCut.2.2.2
  refine ⟨by simpa only [positiveSummandTail_card] using htailA,
    by simpa only [negativeSummandTail_card] using htailB, ?_, ?_, ?_⟩
  · intro x hx
    have hb := positiveSummandTail_bounds A _ _ hx
    have hx0 : (0 : ℤ) ≤ x := by omega
    exact ⟨by exact_mod_cast hx0, by exact_mod_cast hb.2⟩
  · intro y hy
    have hb := negativeSummandTail_bounds B _ _ hy
    have hy0 : y ≤ (0 : ℤ) := by omega
    exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hy0⟩
  · intro x hx y hy
    have hp := hprime (summandTailCutoff L) N hN₁cut x hx y hy
    refine ⟨hp.1, ?_⟩
    have hd : 0 ≤ x - y := by omega
    have he : ((x - y).natAbs : ℤ) = x - y := by rw [Int.natCast_natAbs, abs_of_nonneg hd]
    have hn : summandTailCutoff L < (x - y).natAbs := by omega
    exact (Nat.floor_lt (Real.exp_nonneg _)).mp hn

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailCollisionCutoff
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-root prime cutoff and its logarithmic collision budget -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem tailCollisionCutoff_bounds (L : ℝ) (hL : 1 ≤ L)
    (hr : 2 ≤ Real.exp (L / 2) / L ^ 5) :
    1 ≤ tailCollisionCutoff L ∧
    (tailCollisionCutoff L : ℝ) ≤ Real.exp (L / 2) / L ^ 5 ∧
    L / 2 - 5 * Real.log L - Real.log 2 ≤ Real.log (tailCollisionCutoff L : ℝ) := by
  have hLp : 0 < L := by linarith
  have hrp : 0 < Real.exp (L / 2) / L ^ 5 := by positivity
  have hQ : 1 ≤ tailCollisionCutoff L := (Nat.one_le_floor_iff _).mpr (show (1 : ℝ) ≤ _ by linarith)
  have hhalf : (Real.exp (L / 2) / L ^ 5) / 2 ≤ (tailCollisionCutoff L : ℝ) := by
    have hh := Nat.sub_one_lt_floor (Real.exp (L / 2) / L ^ 5)
    change Real.exp (L / 2) / L ^ 5 - 1 < (tailCollisionCutoff L : ℝ) at hh
    linarith
  refine ⟨hQ, Nat.floor_le hrp.le, ?_⟩
  have hh := Real.log_le_log (show 0 < (Real.exp (L / 2) / L ^ 5) / 2 by positivity) hhalf
  rw [Real.log_div (ne_of_gt hrp) (by norm_num),
    Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 5 hLp.ne'),
    Real.log_exp, Real.log_pow] at hh
  exact hh

theorem eventual_tailCollisionCutoff (N : ℕ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ 2 ≤ Real.exp (L / 2) / L ^ 5 ∧
      N + tailCollisionCutoff L ≤ summandTailCutoff L := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 5 (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul_left 2).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (3 * ((N : ℝ) + 3))] with L hb hL
  have hL1 : 1 ≤ L := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hLp : 0 < L := by linarith
  have hpoly : 2 * L ^ 5 ≤ Real.exp (L / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * L ^ 5),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  have hr : 2 ≤ Real.exp (L / 2) / L ^ 5 := (le_div_iff₀ (pow_pos hLp 5)).mpr hpoly
  have hQ := (tailCollisionCutoff_bounds L hL1 hr).2.1
  have hQ' : (tailCollisionCutoff L : ℝ) ≤ Real.exp (L / 2) := hQ.trans
    (div_le_self (Real.exp_nonneg _) (one_le_pow₀ hL1))
  have he : (1 : ℝ) ≤ Real.exp (L / 2) := Real.one_le_exp (by positivity)
  have hN : (N : ℝ) + 3 ≤ Real.exp (2 * L / 5) := by
    have := Real.add_one_le_exp (2 * L / 5)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (L / 2))
  have hexp : Real.exp (L / 2) * Real.exp (2 * L / 5) = Real.exp (9 * L / 10) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at hmul
  have hN0 : 0 ≤ (N : ℝ) + 2 := by positivity
  have hprod := mul_nonneg (sub_nonneg.mpr he) hN0
  have hfloor := Nat.sub_one_lt_floor (Real.exp (9 * L / 10))
  change Real.exp (9 * L / 10) - 1 < (summandTailCutoff L : ℝ) at hfloor
  have hfinal : (N : ℝ) + tailCollisionCutoff L ≤ (summandTailCutoff L : ℝ) := by
    nlinarith only [hmul, hprod, hfloor, hQ']
  exact ⟨hL1, hr, by exact_mod_cast hfinal⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_EndpointTestScale
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cutoff used to test all large endpoint subsets -/

namespace Ostmann

open Filter

theorem endpointTestCutoff_bounds (t : ℝ) (ht : 1 ≤ t)
    (hr : 2 ≤ Real.exp (t / 2) / t ^ 12) :
    1 ≤ endpointTestCutoff t ∧
      (endpointTestCutoff t : ℝ) ≤ Real.exp (t / 2) / t ^ 12 ∧
      t / 2 - 12 * Real.log t - Real.log 2 ≤ Real.log (endpointTestCutoff t : ℝ) := by
  have htp : 0 < t := by linarith
  have hrp : 0 < Real.exp (t / 2) / t ^ 12 := by positivity
  have hQ : 1 ≤ endpointTestCutoff t := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hhalf : (Real.exp (t / 2) / t ^ 12) / 2 ≤ (endpointTestCutoff t : ℝ) := by
    have h := Nat.sub_one_lt_floor (Real.exp (t / 2) / t ^ 12)
    change Real.exp (t / 2) / t ^ 12 - 1 < (endpointTestCutoff t : ℝ) at h
    linarith
  refine ⟨hQ, Nat.floor_le hrp.le, ?_⟩
  have h := Real.log_le_log (by positivity : 0 < (Real.exp (t / 2) / t ^ 12) / 2) hhalf
  rw [Real.log_div hrp.ne' (by norm_num),
    Real.log_div (Real.exp_ne_zero _) (pow_ne_zero 12 htp.ne'), Real.log_exp, Real.log_pow] at h
  exact h

theorem endpointTestThreshold_bounds (t : ℝ) (ht : 0 < t) :
    1 ≤ endpointTestThreshold t ∧
      Real.exp (t / 2) / t ^ 10 ≤ (endpointTestThreshold t : ℝ) ∧
      (endpointTestThreshold t : ℝ) < Real.exp (t / 2) / t ^ 10 + 1 := by
  have hr : 0 < Real.exp (t / 2) / t ^ 10 := by positivity
  exact ⟨Nat.one_le_ceil_iff.mpr hr, Nat.le_ceil _, Nat.ceil_lt_add_one hr.le⟩

theorem endpoint_test_collision_budget_le (t C : ℝ) (X : ℕ) (ht : 1 ≤ t)
    (hr : 2 ≤ Real.exp (t / 2) / t ^ 12) (hX : Real.log (X : ℝ) ≤ t) :
    2 * Real.log X - 4 * Real.log (endpointTestCutoff t : ℝ) + 4 * C +
      2 * (1 / (endpointTestThreshold t : ℝ)) * Real.log 4 * endpointTestCutoff t ≤
        48 * Real.log t + 4 * C + 4 * Real.log 2 + 2 * Real.log 4 := by
  have htp : 0 < t := by linarith
  have hQ := endpointTestCutoff_bounds t ht hr
  have hK := endpointTestThreshold_bounds t htp
  have hKp : (0 : ℝ) < endpointTestThreshold t := by exact_mod_cast (show 0 < endpointTestThreshold t by omega)
  have hQK : (endpointTestCutoff t : ℝ) / endpointTestThreshold t ≤ 1 := by
    calc
      _ ≤ (Real.exp (t / 2) / t ^ 12) / endpointTestThreshold t :=
        div_le_div_of_nonneg_right hQ.2.1 hKp.le
      _ ≤ (Real.exp (t / 2) / t ^ 12) / (Real.exp (t / 2) / t ^ 10) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hK.2.1
      _ = 1 / t ^ 2 := by field_simp
      _ ≤ 1 := (div_le_one (by positivity : 0 < t ^ 2)).mpr (one_le_pow₀ ht)
  have herr := mul_le_mul_of_nonneg_left hQK (show 0 ≤ 2 * Real.log 4 by positivity)
  have he : 2 * Real.log 4 * ((endpointTestCutoff t : ℝ) / endpointTestThreshold t) =
      2 * (1 / (endpointTestThreshold t : ℝ)) * Real.log 4 * endpointTestCutoff t := by ring
  rw [he] at herr
  linarith [hQ.2.2]

theorem eventual_endpointTestCutoff :
    ∀ᶠ t : ℝ in atTop, 1 ≤ t ∧ 2 ≤ Real.exp (t / 2) / t ^ 12 := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 12 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left 2).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with t hb ht
  have htp : 0 < t := by linarith
  have hpow : 2 * t ^ 12 ≤ Real.exp (t / 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * t ^ 12),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  exact ⟨ht, (le_div_iff₀ (pow_pos htp 12)).mpr hpow⟩

theorem endpointTestCutoff_le_tailCollisionCutoff (t : ℝ) (ht : 1 ≤ t) :
    endpointTestCutoff t ≤ tailCollisionCutoff t := by
  apply Nat.floor_mono
  have htp : 0 < t := by linarith
  apply div_le_div_of_nonneg_left (Real.exp_nonneg _) (pow_pos htp 5)
  exact pow_le_pow_right₀ ht (by decide : 5 ≤ 12)

theorem eventual_endpointTestCutoff_quarter :
    ∀ᶠ t : ℝ in atTop, Real.exp (t / 4) ≤ (endpointTestCutoff t : ℝ) := by
  have hb := ((isLittleO_pow_exp_pos_mul_atTop 12 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul_left 2).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb, eventual_endpointTestCutoff] with t hb ht
  have htp : 0 < t := by linarith [ht.1]
  have hpow : 2 * t ^ 12 ≤ Real.exp (t / 4) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ) * t ^ 12),
      abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hb
  have hexp : Real.exp (t / 4) * Real.exp (t / 4) = Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg (t / 4))
  rw [hexp] at hmul
  have hratio : 2 * Real.exp (t / 4) ≤ Real.exp (t / 2) / t ^ 12 := by
    apply (le_div_iff₀ (pow_pos htp 12)).mpr
    nlinarith only [hmul]
  have hf := Nat.sub_one_lt_floor (Real.exp (t / 2) / t ^ 12)
  change Real.exp (t / 2) / t ^ 12 - 1 < (endpointTestCutoff t : ℝ) at hf
  have hone : 1 ≤ Real.exp (t / 4) := Real.one_le_exp (by positivity)
  linarith

theorem eventual_endpoint_test_error_small (α β D C δ c : ℝ)
    (hα : 0 < α) (hδ : 0 < δ) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ t : ℝ, Real.log t ≤ β * L + D →
      4 * ((48 * Real.log t + 4 * C + 4 * Real.log 2 + 2 * Real.log 4) /
        Real.exp (α * L)) < δ ^ 2 * c := by
  have hlin : Tendsto (fun L : ℝ => L * Real.exp (-α * L)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 α hα
  have hconst : Tendsto (fun L : ℝ => Real.exp (-α * L)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 α hα
  have hbound : Tendsto (fun L : ℝ =>
      4 * ((48 * (β * L + D) + 4 * C + 4 * Real.log 2 + 2 * Real.log 4) /
        Real.exp (α * L))) atTop (nhds 0) := by
    have h := (hlin.const_mul (192 * β)).add
      (hconst.const_mul (192 * D + 16 * C + 16 * Real.log 2 + 8 * Real.log 4))
    simp only [mul_zero, add_zero] at h
    apply h.congr
    intro L
    rw [div_eq_mul_inv, ← Real.exp_neg]
    simp only [neg_mul]
    ring
  filter_upwards [hbound.eventually_lt_const (by positivity : (0 : ℝ) < δ ^ 2 * c)] with L hL t ht
  apply lt_of_le_of_lt _ hL
  gcongr

theorem eventual_endpoint_test_threshold_negligible (a : ℝ) (ha : 0 < a) (J : ℕ) :
    ∀ᶠ t : ℝ in atTop,
      (J : ℝ) * endpointTestThreshold t ≤ (a / 2) * Real.exp (t / 2) / t ^ 3 := by
  have hpow : Tendsto (fun t : ℝ => t ^ 7) atTop atTop := tendsto_pow_atTop (by decide)
  have hpoly := ((isLittleO_pow_exp_pos_mul_atTop 3 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left
    (4 * J / a)).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hpow.eventually_ge_atTop (4 * J / a), hpoly,
    eventually_ge_atTop (1 : ℝ)] with t ht hpoly ht1
  have htp : 0 < t := by linarith
  have hK := (endpointTestThreshold_bounds t htp).2.2.le
  have h1 : (J : ℝ) * (Real.exp (t / 2) / t ^ 10) ≤
      (a / 4) * Real.exp (t / 2) / t ^ 3 := by
    have hJa : (J : ℝ) ≤ (a / 4) * t ^ 7 := by
      have h := (div_le_iff₀ ha).mp ht
      nlinarith only [h]
    have h := mul_le_mul_of_nonneg_right hJa (by positivity : 0 ≤ Real.exp (t / 2) / t ^ 10)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  have h2 : (J : ℝ) ≤ (a / 4) * Real.exp (t / 2) / t ^ 3 := by
    have h : (4 * J / a) * t ^ 3 ≤ Real.exp (t / 2) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (4 * (J : ℝ) / a) * t ^ 3),
        abs_of_pos (Real.exp_pos _), one_mul, one_div_mul_eq_div] using hpoly
    apply (le_div_iff₀ (pow_pos htp 3)).mpr
    have h' := mul_le_mul_of_nonneg_right h (show 0 ≤ a / 4 by positivity)
    have he : ((4 * J / a) * t ^ 3) * (a / 4) = (J : ℝ) * t ^ 3 := by field_simp
    rw [he] at h'
    nlinarith only [h']
  have h := mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg (α := ℝ) J)
  rw [mul_add, mul_one] at h
  have he : (a / 2) * Real.exp (t / 2) / t ^ 3 =
      2 * ((a / 4) * Real.exp (t / 2) / t ^ 3) := by ring
  rw [he]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SimultaneousTailTests
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneously typical endpoints for a finite family of prime sets -/

namespace Ostmann

open scoped BigOperators Classical

theorem simultaneous_tail_tests {ι : Type*} [DecidableEq ι]
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N X Q K : ℕ) (hX : 1 ≤ X) (hQ : 1 ≤ Q) (hK : 0 < K)
    (hdis : ∀ p ∈ Nat.primesLE Q, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (E D : Finset ℕ) (hD : K ≤ D.card)
    (hEtail : ∀ a ∈ E, a ∈ A ∧ N + Q < a ∧ a ≤ X)
    (hDtail : ∀ b ∈ D, b ∈ B ∧ N + Q < b ∧ b ≤ X)
    (J : Finset ι) (P : ι → Finset ℕ) (b δ c C : ℝ)
    (hb : 0 < b) (hδ : 0 < δ) (hc : 0 < c) (hM : MertensLowerBound C)
    (F : ℕ → ℕ → ℝ)
    (hP : ∀ j ∈ J, P j ⊆ Nat.primesLE Q)
    (hlog : ∀ j ∈ J, ∀ p ∈ P j, b ≤ Real.log (p : ℝ))
    (hF : ∀ j ∈ J, ∀ p ∈ P j, ∀ r ∈ tailSupport A N p, |F p r| ≤ 1)
    (hmass : ∀ j ∈ J, c ≤ ∑ p ∈ P j, (p : ℝ)⁻¹)
    (href : ∀ j ∈ J, δ * (∑ p ∈ P j, (p : ℝ)⁻¹) ≤
      ∑ p ∈ P j, (p : ℝ)⁻¹ * residueTestMean (tailSupport A N p) (F p))
    (hsmall : 4 * ((2 * Real.log X - 4 * Real.log Q + 4 * C +
      2 * (1 / (K : ℝ)) * Real.log 4 * Q) / b) < δ ^ 2 * c) :
    ∃ G ⊆ E, E.card ≤ G.card + J.card * K ∧
      ∀ a ∈ G, ∀ j ∈ J,
        (δ / 2) * (∑ p ∈ P j, (p : ℝ)⁻¹) ≤
          ∑ p ∈ P j, (p : ℝ)⁻¹ * F p (a % p) := by
  let bad := fun j => badEndpoints E (P j) (fun p => (p : ℝ)⁻¹)
    (fun a p => F p (a % p)) δ
  have hbad : ∀ j ∈ J, (bad j).card ≤ K := by
    intro j hj
    apply Nat.le_of_lt
    apply few_bad_tail_endpoints hA hB N X Q K hX hQ hK hdis E D (P j) hD hEtail hDtail
      (hP j hj) b δ C hb hδ hM (hlog j hj) F (hF j hj)
      (hc.trans_le (hmass j hj)) (href j hj)
    exact hsmall.trans_le (mul_le_mul_of_nonneg_left (hmass j hj) (sq_nonneg δ))
  obtain ⟨G, hGE, hGcard, hG⟩ := simultaneous_good_endpoints E J bad K hbad
  refine ⟨G, hGE, hGcard, ?_⟩
  intro a ha j hj
  have h := hG a ha j hj
  have haE := hGE ha
  simpa only [bad, badEndpoints, Finset.mem_filter, haE, true_and, not_lt] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TypicalTailAssembly
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large sets of endpoints passing every prescribed prime test -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem eventual_typical_tail_tests {ι : Type*} [DecidableEq ι]
    (hsize : PublishedSummandSizeBound) {C : ℝ} (hM : MertensLowerBound C)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (J : Finset ι) (α β D δ c : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∃ L₀ t₀ : ℝ, ∀ L t : ℝ, L₀ ≤ L → t₀ ≤ t →
      Real.log t ≤ β * L + D → ∀ X : ℕ, (X : ℝ) = Real.exp t →
      ∀ (P : ι → Finset ℕ) (F : ℕ → ℕ → ℝ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime ∧ (p : ℝ) ≤ Real.exp (t / 4) ∧
        Real.exp (α * L) ≤ Real.log (p : ℝ)) →
      (∀ j ∈ J, ∀ p ∈ P j, ∀ r ∈ tailSupport A N p, |F p r| ≤ 1) →
      (∀ j ∈ J, c ≤ ∑ p ∈ P j, (p : ℝ)⁻¹) →
      (∀ j ∈ J, δ * (∑ p ∈ P j, (p : ℝ)⁻¹) ≤
        ∑ p ∈ P j, (p : ℝ)⁻¹ * residueTestMean (tailSupport A N p) (F p)) →
      ∃ G ⊆ summandTail A (summandTailCutoff t) X,
        a * Real.exp (t / 2) / t ^ 3 ≤ (G.card : ℝ) ∧
        ∀ x ∈ G, ∀ j ∈ J, (δ / 2) * (∑ p ∈ P j, (p : ℝ)⁻¹) ≤
          ∑ p ∈ P j, (p : ℝ)⁻¹ * F p (x % p) := by
  obtain ⟨a, ha, hcounts⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventual_endpoint_test_error_small α β D C δ c hα hδ hc)
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (hcounts.and
    (eventual_endpointTestCutoff.and (eventual_endpointTestCutoff_quarter.and
      ((eventual_tailCollisionCutoff N).and
        ((eventual_endpoint_test_threshold_negligible a ha 1).and
          (eventual_endpoint_test_threshold_negligible a ha J.card))))))
  refine ⟨a / 2, by positivity, L₀, t₀, ?_⟩
  intro L t hL ht hlog X hX P F hP hF hmass href
  obtain ⟨hcounts, hcut, hquarter, htail, hKsmall, hJsmall⟩ := ht₀ t ht
  have htp : 0 < t := by linarith [hcut.1]
  obtain ⟨hEA, hDB, _⟩ := hcounts X hX
  simp only [positiveSummandTail_card] at hEA
  simp only [negativeSummandTail_card] at hDB
  let E := summandTail A (summandTailCutoff t) X
  let T := summandTail B (summandTailCutoff t) X
  let Q := endpointTestCutoff t
  let K := endpointTestThreshold t
  have hKpos : 0 < K := lt_of_lt_of_le (by decide : 0 < 1)
    (endpointTestThreshold_bounds t htp).1
  have hQpos : 1 ≤ Q := (endpointTestCutoff_bounds t hcut.1 hcut.2).1
  have hXpos : 1 ≤ X := by
    have hx := Real.one_le_exp htp.le
    rw [← hX] at hx
    exact_mod_cast hx
  have hTK : K ≤ T.card := by
    simp only [Nat.cast_one, one_mul] at hKsmall
    have hscale : (a / 2) * Real.exp (t / 2) / t ^ 3 ≤ a * Real.exp (t / 2) / t ^ 3 := by
      gcongr
      linarith
    have hk : (K : ℝ) ≤ T.card := hKsmall.trans (hscale.trans hDB)
    exact_mod_cast hk
  have hNQ : N + Q ≤ summandTailCutoff t :=
    (Nat.add_le_add_left (endpointTestCutoff_le_tailCollisionCutoff t hcut.1) N).trans htail.2.2
  have hEtail : ∀ x ∈ E, x ∈ A ∧ N + Q < x ∧ x ≤ X := by
    intro x hx
    obtain ⟨hxA, hxlo, hxX⟩ := (mem_summandTail A _ _ x).mp hx
    exact ⟨hxA, hNQ.trans_lt hxlo, hxX⟩
  have hTtail : ∀ x ∈ T, x ∈ B ∧ N + Q < x ∧ x ≤ X := by
    intro x hx
    obtain ⟨hxB, hxlo, hxX⟩ := (mem_summandTail B _ _ x).mp hx
    exact ⟨hxB, hNQ.trans_lt hxlo, hxX⟩
  have hPQ : ∀ j ∈ J, P j ⊆ Nat.primesLE Q := by
    intro j hj p hp
    exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast ((hP j hj p hp).2.1.trans hquarter),
      (hP j hj p hp).1⟩
  have hsmall : 4 * ((2 * Real.log X - 4 * Real.log Q + 4 * C +
      2 * (1 / (K : ℝ)) * Real.log 4 * Q) / Real.exp (α * L)) < δ ^ 2 * c := by
    have hbudget := endpoint_test_collision_budget_le t C X hcut.1 hcut.2
      (by rw [hX, Real.log_exp])
    have hb := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hbudget (Real.exp_nonneg (α * L))) (by norm_num : (0 : ℝ) ≤ 4)
    exact hb.trans_lt (hL₀ L hL t hlog)
  obtain ⟨G, hGE, hGcard, hGgood⟩ := simultaneous_tail_tests hA hB N X Q K hXpos hQpos hKpos
    (fun p hp => hN p (Nat.prime_of_mem_primesLE hp)) E T hTK hEtail hTtail J P
    (Real.exp (α * L)) δ c C (Real.exp_pos _) hδ hc hM F hPQ
    (fun j hj p hp => (hP j hj p hp).2.2) hF hmass href hsmall
  refine ⟨G, hGE, ?_, hGgood⟩
  have hcardR : (E.card : ℝ) ≤ (G.card : ℝ) + (J.card : ℝ) * K := by exact_mod_cast hGcard
  have hscale : a * Real.exp (t / 2) / t ^ 3 =
      2 * ((a / 2) * Real.exp (t / 2) / t ^ 3) := by ring
  rw [hscale] at hEA
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TypicalCharacterEndpoints
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual tail collision estimate supplies typical character endpoints -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem realTranslatedCharacterTest_bound
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (p r : ℕ) :
    |realTranslatedCharacterTest χ t ζ p r| ≤ 1 := by
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_mul, hζ, one_mul]
  exact (χ p).norm_le_one _

theorem realTranslatedCharacterTest_mod
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ζ : ℂ) (p r : ℕ) :
    realTranslatedCharacterTest χ t ζ p (r % p) = realTranslatedCharacterTest χ t ζ p r := by
  simp only [realTranslatedCharacterTest, ZMod.natCast_mod]

/-- This is the typical-endpoint step for every prescribed whole shell and
bulk interval. The reference mean is a literal average on the fixed tail. -/
theorem eventual_typical_character_tests {ι : Type*} [DecidableEq ι]
    (hsize : PublishedSummandSizeBound) {C : ℝ} (hM : MertensLowerBound C)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (J : Finset ι) (α β D δ c : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∃ L₀ t₀ : ℝ, ∀ L T : ℝ, L₀ ≤ L → t₀ ≤ T →
      Real.log T ≤ β * L + D → ∀ X : ℕ, (X : ℝ) = Real.exp T →
      ∀ (P : Finset ℕ) (R : ι → Finset ℕ)
        (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p) (ζ : ℂ),
      ‖ζ‖ = 1 → (∀ j ∈ J, R j ⊆ P) →
      (∀ j ∈ J, ∀ p ∈ R j, p.Prime ∧ (p : ℝ) ≤ Real.exp (T / 4) ∧
        Real.exp (α * L) ≤ Real.log (p : ℝ)) →
      (∀ j ∈ J, c ≤ ∑ p ∈ R j, (p : ℝ)⁻¹) →
      (∀ j ∈ J, ∀ p ∈ R j, δ ≤ residueTestMean (tailSupport A N p)
        (realTranslatedCharacterTest χ t ζ p)) →
      ∃ G ⊆ summandTail A (summandTailCutoff T) X,
        a * Real.exp (T / 2) / T ^ 3 ≤ (G.card : ℝ) ∧
        ∀ x ∈ G, ∀ j ∈ J,
          (δ / 2) * (∑ p ∈ R j, (p : ℝ)⁻¹) ≤
            ∑ p ∈ R j, (p : ℝ)⁻¹ * (ζ * χ p ((x : ZMod p) - t p)).re ∧
          δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P (R j) p : ℂ) * χ p ((x : ZMod p) - t p)‖ := by
  obtain ⟨a, ha, L₀, t₀, ht⟩ := eventual_typical_tail_tests hsize hM hA hB h N hN
    J α β D δ c hα hδ hc
  refine ⟨a, ha, L₀, t₀, ?_⟩
  intro L T hL hT hlog X hX P R χ t ζ hζ hRP hR hmass href
  obtain ⟨G, hG, hcard, hgood⟩ := ht L T hL hT hlog X hX R
    (realTranslatedCharacterTest χ t ζ) hR
    (fun _ _ p _ r _ => realTranslatedCharacterTest_bound χ t ζ hζ p r) hmass (by
      intro j hj
      calc
        δ * (∑ p ∈ R j, (p : ℝ)⁻¹) = ∑ p ∈ R j, (p : ℝ)⁻¹ * δ := by
          rw [← Finset.sum_mul]; exact mul_comm _ _
        _ ≤ _ := Finset.sum_le_sum (fun p hp =>
          mul_le_mul_of_nonneg_left (href j hj p hp) (by positivity)))
  refine ⟨G, hG, hcard, ?_⟩
  intro x hx j hj
  have hg := hgood x hx j hj
  simp_rw [realTranslatedCharacterTest_mod] at hg
  have hp := primeSubsetPrior_mean_positive P (R j) (hRP j hj)
    (hc.trans_le (hmass j hj)) (fun p => ζ * χ p ((x : ZMod p) - t p)) (δ / 2) hg
  exact ⟨hg, (hp.trans (Complex.re_le_norm _)).trans_eq
    (norm_weighted_common_rotation _ _ ζ hζ)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TypicalCharacterShells
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite test family covers precisely the needed character shells -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- Ineligible grid shells are represented by the bulk test. Thus the index
set is fixed before L, without asking for mass in empty or unusable shells. -/
theorem eventual_typical_character_shells
    (hsize : PublishedSummandSizeBound) {C : ℝ} (hM : MertensLowerBound C)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (k : ℕ) (α β D δ c : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∃ L₀ t₀ : ℝ, ∀ L T : ℝ, L₀ ≤ L → t₀ ≤ T →
      Real.log T ≤ β * L + D → ∀ X : ℕ, (X : ℝ) = Real.exp T →
      ∀ (P Ubulk T₀ : Finset ℕ) (Ulate : ℝ) (u : Fin k × Bool → ℝ)
        (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (center : ∀ p : ℕ, ZMod p) (ζ : ℂ),
      ‖ζ‖ = 1 → (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, Real.exp (α * L) ≤ Real.log (p : ℝ)) →
      Ubulk ⊆ P → T₀ ⊆ P →
      c ≤ ∑ p ∈ Ubulk, (p : ℝ)⁻¹ → c ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
      (∀ j, c ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
      (∀ p ∈ Ubulk, Real.log (p : ℝ) ≤ T / 4) →
      (∀ p ∈ T₀, Real.log (p : ℝ) ≤ T / 4) →
      (∀ j p, p ∈ loglogShell P (u j) → Real.log (p : ℝ) ≤ T / 4) →
      (∀ p ∈ P, δ ≤ residueTestMean (tailSupport A N p)
        (realTranslatedCharacterTest χ center ζ p)) →
      ∃ G ⊆ summandTail A (summandTailCutoff T) X,
        a * Real.exp (T / 2) / T ^ 3 ≤ (G.card : ℝ) ∧
        ∀ x ∈ G,
          (δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P Ubulk p : ℂ) *
            χ p ((x : ZMod p) - center p)‖) ∧
          (δ / 2 ≤ ‖∑ p : P, (primeSubsetPrior P T₀ p : ℂ) *
            χ p ((x : ZMod p) - center p)‖) ∧
          (∀ j, (δ / 2) * (∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) ≤
            ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹ * (ζ * χ p ((x : ZMod p) - center p)).re) ∧
          (∀ j : ℕ, j ≤ 5 * k →
            c ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ →
            (∀ p ∈ loglogShell P (Ulate + j), Real.log (p : ℝ) ≤ T / 4) →
            (δ / 2) * (∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) ≤
              ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹ *
                (ζ * χ p ((x : ZMod p) - center p)).re) := by
  obtain ⟨a, ha, L₀, t₀, ht⟩ := eventual_typical_character_tests hsize hM hA hB h N hN
    (Finset.univ : Finset (CharacterShellTestIndex k)) α β D δ c hα hδ hc
  refine ⟨a, ha, L₀, t₀, ?_⟩
  intro L T hL hT hlog X hX P Ubulk T₀ Ulate u χ center ζ hζ hP hmin hUP hTP
    hUmass hTmass humass hUcut hTcut hucut href
  let R := characterShellTests k P Ubulk T₀ Ulate T c u
  have hdata : ∀ j, R j ⊆ P ∧ c ≤ ∑ p ∈ R j, (p : ℝ)⁻¹ ∧
      ∀ p ∈ R j, Real.log (p : ℝ) ≤ T / 4 := by
    rintro (j | (j | b))
    · dsimp only [R, characterShellTests]
      split_ifs with hj
      · exact ⟨Finset.filter_subset _ _, hj.1, hj.2⟩
      · exact ⟨hUP, hUmass, hUcut⟩
    · exact ⟨Finset.filter_subset _ _, humass j, hucut j⟩
    · cases b
      · exact ⟨hUP, hUmass, hUcut⟩
      · exact ⟨hTP, hTmass, hTcut⟩
  obtain ⟨G, hG, hcard, hgood⟩ := ht L T hL hT hlog X hX P R χ center ζ hζ
    (fun j _ => (hdata j).1) (by
      intro j _ p hp
      have hpp := hP p ((hdata j).1 hp)
      refine ⟨hpp, ?_, hmin p ((hdata j).1 hp)⟩
      calc
        (p : ℝ) = Real.exp (Real.log (p : ℝ)) :=
          (Real.exp_log (by exact_mod_cast hpp.pos)).symm
        _ ≤ Real.exp (T / 4) := Real.exp_le_exp.mpr ((hdata j).2.2 p hp))
    (fun j _ => (hdata j).2.1) (fun j _ p hp => href p ((hdata j).1 hp))
  refine ⟨G, hG, hcard, ?_⟩
  intro x hx
  refine ⟨(hgood x hx (.inr (.inr false)) (Finset.mem_univ _)).2,
    (hgood x hx (.inr (.inr true)) (Finset.mem_univ _)).2,
    fun j => (hgood x hx (.inr (.inl j)) (Finset.mem_univ _)).1, ?_⟩
  intro j hj hmass hcut
  have hh := (hgood x hx (.inl ⟨j, Nat.lt_succ_of_le hj⟩) (Finset.mem_univ _)).1
  simpa only [R, characterShellTests, ite_eq_left (And.intro hmass hcut)] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTailShellContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual summand tails supply the endpoints in the character contradiction -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem PublishedProgressionInput.eventual_tail_character_shell_contradiction
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensLowerBound CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p)) (c₀ δ : ℝ) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ n : ℕ, 20000 ≤ n + 1 →
      C₀ ≤ Real.exp (((n + 1 : ℕ) : ℝ) / 10000) →
    ∀
    (a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε β Ccode A : ℝ)
    (_ha : 0 < a) (_hb : 0 < b) (_hz : 1 < z)
    (_hCmass : 0 < Cmass) (_hCtotal : 0 ≤ Ctotal) (_hc : 1 ≤ c)
    (_hs : 0 < s) (_hγ : 0 < γ) (_hH : 0 ≤ H) (_hα : 0 < α)
    (_hgapInitial : 2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
      (Aend + 2 * Bword + 1) + 2) ≤ B) (_hB : 0 ≤ B)
    (_hB₁ : 0 ≤ B₁) (_hB₁eq : B₁ = Aend + 2 * Bword + 3)
    (_hBstrong : 2 * B₁ + 5 ≤ B) (_hBpos : 1 ≤ B) (_ha1 : a ≤ 1)
    (_hβg : 0 < βg) (_hγw : 0 ≤ γw) (_hαw : α < βw) (_hsw : γs < βw)
    (_hαa : α < βa) (_hwa : γw < βa) (_hwg : γw ≤ βg)
    (_hβw : βw < νw) (_hβa : βa < νa) (_hε : 0 < ε)
    (_hbudgetAll : 4 * Cmass *
      (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) ≤ z)
    (_hgapFinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + ε) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a)
    (_hentropy : (βg + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + ε) +
      (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1)
    (_hβ : 0 ≤ β) (_hβgap : β < βg)
    (_hβmass : β + 1 ≤ Cmass)
    (_hcover : characterCellCoveringError c₀ δ (n + 1) ≤ c)
    (_hCcode : 0 ≤ Ccode) (_hArate : A + (β + 1) + 4 * Ccode + 4 ≤ Aend)
    (_hBrate : (β + 1) - 2 * Real.log δ ≤ Bword) (_hγδ : γ ≤ δ / 2)
    (_hAtail : 3 * β + 1 ≤ A) (_hcb : c₀ ≤ b)
    (ψ : 𝓢(ℝ, ℂ)) (_hψ : ∀ x, 0 ≤ (ψ x).re) (_hreal : ∀ x, (ψ x).im = 0)
    (_heven : ∀ v : ℝ, 𝓕 ψ (-v) = 𝓕 ψ v)
    (_hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (_hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0)
    (_hψlower : ∀ t ∈ Set.Icc (0 : ℝ) 1, s ≤ (ψ t).re),
    ∀ᶠ L : ℝ in atTop,
    let m := ⌊z * L⌋₊
    ∀ (Ulate τ bmax : ℝ) (P U T₀ : Finset ℕ) (_hP : ∀ p ∈ P, p.Prime)
      (Q : Fin (m + 1) → Finset ℕ) (D : ℕ),
    α * L ≤ Ulate → Ulate ≤ β * L → Ulate ≤ Real.log τ →
    Real.log τ ≤ Ulate + 2 * ((n + 1 : ℕ) : ℝ) / 10000 → 0 < τ → 2 ≤ τ →
    Q 0 = T₀ → (∀ i : Fin m, Q i.succ = U) → (∀ i, Q i ⊆ P) →
    a * L ≤ ∑ p ∈ U, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T₀, (p : ℝ)⁻¹ →
    (∑ p : P, (p : ℝ)⁻¹) ≤ Ctotal * L →
    (∀ p ∈ P, Real.exp (Real.exp (α * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (βg * L))) →
    (∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L))) →
    Disjoint U T₀ → (m : ℝ) * bmax ≤ τ →
    (∀ p ∈ T₀, τ ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 3 * τ) →
    (∀ p ∈ U, Real.log (p : ℝ) ≤ bmax) →
    ∀ (l h : ℝ),
    (∀ p ∈ U, l < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ h) →
    h ≤ Ulate →
    (D + 1 : ℕ) ≤ Real.exp (Ccode * L) → 5 * (n + 1) ≤ D →
    (∀ p ∈ P, primeLogIndex p ≤ D) →
    (∀ u v : ℝ, Ulate ≤ u → v ≤ Ulate + 5 * (n + 1) →
      ((n + 1 : ℕ) : ℝ) / 10000 ≤ v - u →
      ∃ j : ℕ, u ≤ Ulate + j ∧ Ulate + j + 1 ≤ v ∧
        c₀ ≤ ∑ p ∈ loglogShell P (Ulate + j), (p : ℝ)⁻¹) →
    ∀ u : Fin (n + 1) × Bool → ℝ,
    (∀ j, α * L ≤ u j ∧ u j ≤ β * L) → (∀ j, u j + 1 ≤ l ∨ h ≤ u j) →
    (∀ j, u (j, false) + 1 ≤ γs * L) → (∀ j, νa * L ≤ u (j, true)) →
    (∀ j, 3 * Real.exp (u (j, false)) + 3 * Real.exp (u (j, true)) ≤ 4 * τ) →
    (∀ j, c₀ ≤ ∑ p ∈ loglogShell P (u j), (p : ℝ)⁻¹) →
    ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
    ∀ (center : ∀ p : ℕ, ZMod p) (ζ : ℂ), ‖ζ‖ = 1 →
    ∀ X : ℕ, (X : ℝ) = Real.exp (1000 * (4 : ℝ) ^ (n + 1) * τ) →
    (∀ p ∈ P, 2 * δ ≤ residueTestMean (tailSupport Aset N₀ p)
      (realTranslatedCharacterTest χ center ζ p)) → False := by
  obtain ⟨C₀, hC₀, htested⟩ := P0.eventual_tested_character_shell_contradiction c₀ δ hc₀ hδ hδ1
  refine ⟨C₀, hC₀, ?_⟩
  intro n hn hC₀n a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K βg βw γs βa γw νw νa ε
    β Ccode A ha hb hz hCmass hCtotal hc hs hγ hH hα hgapInitial hB hB₁ hB₁eq hBstrong
    hBpos ha1 hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll hgapFinal hentropy
    hβ hβgap hβmass hcover hCcode hArate hBrate hγδ hAtail hcb ψ hψ hreal heven hψK hsupp hψlower
  let Ck : ℝ := 1000 * (4 : ℝ) ^ (n + 1)
  let Dlog : ℝ := Real.log Ck + 2 * ((n + 1 : ℕ) : ℝ) / 10000
  have hCk : 0 < Ck := by dsimp [Ck]; positivity
  obtain ⟨atail, hatail, L₀, t₀, htail⟩ := eventual_typical_character_shells hsize hM hAset hBset
    hsum N₀ hN₀ (n + 1) α β Dlog (2 * δ) c₀ hα (by positivity) hc₀
  have hcontra := htested n hn hC₀n a b z Cmass Ctotal Aend Bword B B₁ c s γ H α K
    βg βw γs βa γw νw νa ε β Ccode A ha hb hz hCmass hCtotal hc hs hγ hH hα hgapInitial hB
    hB₁ hB₁eq hBstrong hBpos ha1 hβg hγw hαw hsw hαa hwa hwg hβw hβa hε hbudgetAll
    hgapFinal hentropy hβ hβgap hβmass hcover hCcode hArate hBrate hγδ ψ hψ hreal heven hψK hsupp
  have htlarge : ∀ᶠ L : ℝ in atTop, t₀ ≤ Ck * Real.exp (α * L) :=
    ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hα)).const_mul_atTop hCk).eventually
      (eventually_ge_atTop t₀)
  have hbulklarge : ∀ᶠ L : ℝ in atTop, c₀ ≤ a * L :=
    (tendsto_id.const_mul_atTop ha).eventually (eventually_ge_atTop c₀)
  filter_upwards [hcontra, eventual_character_tail_count_rate atail β Dlog hatail hβ,
    eventual_character_length_bounds z hz, htlarge, hbulklarge, eventually_ge_atTop L₀]
    with L hcontra hrate hlength htlarge hbulklarge hL₀
  intro m Ulate τ bmax P U T₀ hP Q D hUL hUβ hUτ hτU hτ hτ2 hzero hsucc hQP hbulk htop
    htotal hPrange hUrange hUT hsizeτ htoplog hbulklog l h hUlog hUlate hD hkD hPD hrich
    u hu husep hsmall hbig huτ hmass χ hχ center ζ hζ X hX href
  let T : ℝ := Ck * τ
  have hT : 0 < T := mul_pos hCk hτ
  have hτlo : Real.exp (α * L) ≤ τ :=
    (Real.exp_le_exp.mpr (hUL.trans hUτ)).trans_eq (Real.exp_log hτ)
  have ht₀ : t₀ ≤ T := htlarge.trans (mul_le_mul_of_nonneg_left hτlo hCk.le)
  have hlogT : Real.log T ≤ β * L + Dlog := by
    rw [show T = Ck * τ from rfl, Real.log_mul hCk.ne' hτ.ne']
    dsimp only [Dlog]
    linarith only [hUβ, hτU]
  have hscale : 4 * τ ≤ T / 4 := by
    have hp : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hp hτ.le
    dsimp [T, Ck]
    nlinarith only [hh, hτ]
  have hUP : U ⊆ P := by
    have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 1) hlength.2.1
    simpa only [hsucc] using hQP (Fin.succ ⟨0, hmpos⟩)
  have hTP : T₀ ⊆ P := by simpa only [hzero] using hQP 0
  have hmin (p : ℕ) (hp : p ∈ P) : Real.exp (α * L) ≤ Real.log (p : ℝ) :=
    (Real.le_log_iff_exp_le (by exact_mod_cast (hP p hp).pos)).mpr (hPrange p hp).1
  have hUcut : ∀ p ∈ U, Real.log (p : ℝ) ≤ T / 4 := by
    intro p hp
    have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hP p (hUP hp)).one_le)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hlength.2.1
    have hh := mul_le_mul_of_nonneg_right hm1 hlog0
    have hh' := mul_le_mul_of_nonneg_left (hbulklog p hp) (Nat.cast_nonneg (α := ℝ) m)
    have hτp : Real.log (p : ℝ) ≤ τ := by nlinarith only [hh, hh', hsizeτ]
    exact hτp.trans (by linarith only [hscale, hτ])
  have hTcut : ∀ p ∈ T₀, Real.log (p : ℝ) ≤ T / 4 := by
    intro p hp
    exact (htoplog p hp).2.trans (by linarith only [hscale, hτ])
  have hucut : ∀ j p, p ∈ loglogShell P (u j) → Real.log (p : ℝ) ≤ T / 4 := by
    rintro ⟨j, b⟩ p hp
    have hh := (character_top_shell_log_bounds P hP (u (j, b)) p hp).2
    have ha' := huτ j
    cases b <;> apply hh.trans <;>
      linarith only [ha', hscale, Real.exp_pos (u (j, false)), Real.exp_pos (u (j, true))]
  obtain ⟨E, hEtail, hEcard, hgood⟩ := htail L T hL₀ ht₀ hlogT X hX P U T₀ Ulate u χ center ζ
    hζ hP hmin hUP hTP (hbulklarge.trans hbulk) (hcb.trans htop) hmass hUcut hTcut hucut href
  have hcount := hrate m T E hlength.2.2.1 hT hlogT hEcard
  have hEA : Real.sqrt (Real.exp T) * Real.exp (-A * m) ≤ E.card := by
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [hAtail, Nat.cast_nonneg (α := ℝ) m]))
      (Real.sqrt_nonneg _)).trans hcount
  have hsE : ∀ x ∈ E, s ≤ (ψ ((x : ℝ) / Real.exp T)).re := by
    intro x hx
    have hxX := ((mem_summandTail Aset _ _ x).mp (hEtail hx)).2.2
    have hxR : (x : ℝ) ≤ Real.exp T := by rw [← hX]; exact_mod_cast hxX
    exact hψlower _ ⟨div_nonneg (Nat.cast_nonneg x) (Real.exp_nonneg T),
      (div_le_one (Real.exp_pos T)).mpr hxR⟩
  have hgood' := hgood
  simp only [show 2 * δ / 2 = δ by ring] at hgood'
  apply hcontra Ulate τ bmax P U T₀ hP Q D hUL hUβ hUτ hτU hτ hτ2 hzero hsucc hQP hbulk htop
    htotal hPrange hUrange hUT hsizeτ htoplog hbulklog l h hUlog hUlate hD hkD hPD hrich u hu
    husep hsmall hbig huτ hmass χ hχ center ζ hζ E hEA hsE
  · intro x hx i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [hzero] using (hgood' x hx).2.1
    · simpa only [hsucc] using (hgood' x hx).1
  · exact fun x hx => (hgood' x hx).2.2.2
  · exact fun x hx => (hgood' x hx).2.2.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterConcreteBandContradiction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete separated prime bands instantiate the character contradiction -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform ComplexConjugate

theorem PublishedProgressionInput.concrete_character_band_contradiction
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (α β c₀ δ : ℝ) (hα : 0 < α) (hαβ : α < β) (hc₀ : 0 < c₀)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let Ctotal := (Real.exp 1 + 1) * (β - α + 1)
    let Aend := 8 * β + 10
    let Bword := β + 1 - 2 * Real.log δ
    let B₁ := Aend + 2 * Bword + 3
    let Cdy := β + Real.log ((Real.log 2)⁻¹ + 1)
    let Cfinal := β + 1 + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + 1
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (q n : ℕ), 0 < q → 20000 ≤ n + 1 →
      C₀ ≤ Real.exp (((n + 1 : ℕ) : ℝ) / 10000) →
      ∀ (i j k : Fin q), i.val + 1 < j.val → j.val + 1 < k.val →
      ∀ (a z B : ℝ), 0 < a → a ≤ 1 → 1 < z → 1 ≤ B → 2 * B₁ + 5 ≤ B →
      2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
        (Aend + 2 * Bword + 1) + 2) ≤ B →
      2 * B₁ + (Cdy / a + max (Real.log 3) 0 + 1) + Real.log 2 + 6 ≤ B + 20 * Real.log a →
      Cfinal + (B + 20 * Real.log z + 1) + 2 * B₁ + 1 ≤ (n : ℝ) * Real.log 2 - 1 →
      4 * (β + 1) * (characterTargetLabelBound c₀ δ (n + 1) + (n + 2) + (n + 2) : ℕ) ≤ z →
      ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α * L < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L) →
      let γs := characterBandPoint α β q (i.val + 1)
      let νw := characterBandPoint α β q j.val
      let γw := characterBandPoint α β q (j.val + 1)
      let νa := characterBandPoint α β q k.val
      a * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p)) (fun p => (p : ℝ)⁻¹)
        (νw * L) (γw * L) →
      ∀ us Ulate v : ℝ, characterBandPoint α β q i.val * L ≤ us → us + 1 ≤ γs * L →
      νa * L ≤ Ulate → Ulate + 5 * (n + 1) ≤ characterBandPoint α β q (k.val + 1) * L →
      Ulate + ((n + 1 : ℕ) : ℝ) / 10000 ≤ v → v + 1 ≤ Ulate + 2 * ((n + 1 : ℕ) : ℝ) / 10000 →
      c₀ ≤ ∑ p ∈ loglogShell P us, (p : ℝ)⁻¹ → c₀ ≤ ∑ p ∈ loglogShell P v, (p : ℝ)⁻¹ →
      (∀ x y : ℝ, Ulate ≤ x → y ≤ Ulate + 5 * (n + 1) →
        ((n + 1 : ℕ) : ℝ) / 10000 ≤ y - x →
        ∃ t : ℕ, x ≤ Ulate + t ∧ Ulate + t + 1 ≤ y ∧
          c₀ ≤ ∑ p ∈ loglogShell P (Ulate + t), (p : ℝ)⁻¹) →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (center : ∀ p : ℕ, ZMod p) (ζ : ℂ), ‖ζ‖ = 1 →
      (∀ p ∈ P, 2 * δ ≤ residueTestMean (tailSupport Aset N₀ p)
        (realTranslatedCharacterTest χ center ζ p)) → False := by
  intro Ctotal Aend Bword B₁ Cdy Cfinal
  obtain ⟨s, ψ, hs, hconj, hψ, hlower, hsupp, heven⟩ := exists_positive_even_fourier_cutoff
  have hreal (x) : (ψ x).im = 0 := by
    have hh := congrArg Complex.im (hconj x)
    simp only [Complex.conj_im] at hh
    linarith only [hh]
  let Kψ := SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ))
  have hψK : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp Kψ := by
    have hh := Real.add_one_le_exp Kψ
    linarith only [hh]
  obtain ⟨C₀, hC₀, htail⟩ := P0.eventual_tail_character_shell_contradiction
    hsize hM.lower hAset hBset hsum N₀ hN₀ c₀ δ hc₀ hδ hδ1
  refine ⟨C₀, hC₀, ?_⟩
  intro q n hq hn hC₀n i j k hij hjk a z B ha ha1 hz hB hstrong hrepeat hanchor hentropy hbudget
  let γs := characterBandPoint α β q (i.val + 1)
  let νw := characterBandPoint α β q j.val
  let γw := characterBandPoint α β q (j.val + 1)
  let νa := characterBandPoint α β q k.val
  let βw := (γs + νw) / 2
  let βa := (γw + νa) / 2
  have hmargins := character_three_band_margins α β q hα hαβ hq i j k hij hjk
  rcases hmargins with ⟨hαhalf, hαw, hsw, hβw, hαa, hwa, hβa, hγw0, hγwg, hνag⟩
  have hγwβ := (characterBandPoint_bounds α β q (j.val + 1) hαβ hq (by omega)).2
  have hβ : 0 < β := hα.trans hαβ
  have hword : 0 ≤ Bword := by
    have hh := Real.log_nonpos hδ.le hδ1
    dsimp only [Bword]
    linarith only [hh, hβ]
  have hB₁ : 0 ≤ B₁ := by dsimp only [B₁, Aend]; linarith only [hword, hβ]
  have hCtotal : 0 ≤ Ctotal := by dsimp [Ctotal]; positivity
  have hcover : 1 ≤ characterCellCoveringError c₀ δ (n + 1) :=
    (characterCellCoveringError_gt_one c₀ δ (n + 1) hc₀ hδ).le
  have hfinal : 2 * B₁ +
      ((γw + Real.log ((Real.log 2)⁻¹ + 1)) / a + max (Real.log 3) 0 + 1) +
      Real.log 2 + 6 ≤ B + 20 * Real.log a := by
    have hh := div_le_div_of_nonneg_right
      (show γw + Real.log ((Real.log 2)⁻¹ + 1) ≤ Cdy by dsimp [Cdy]; linarith only [hγwβ]) ha.le
    linarith only [hh, hanchor]
  have hcut := htail n hn hC₀n a c₀ z (β + 1) Ctotal Aend Bword B B₁
    (characterCellCoveringError c₀ δ (n + 1)) s (δ / 2) 9 (α / 2) Kψ
    (β + 1) βw γs βa γw νw νa 1 β (β + 1) (3 * β + 1)
    ha hc₀ hz (by linarith only [hβ]) hCtotal hcover hs (by positivity) (by norm_num)
    (by positivity) hrepeat (by linarith only [hB]) hB₁ rfl hstrong hB ha1
    (by linarith only [hβ]) hγw0 hαw hsw hαa hwa hγwg hβw hβa (by norm_num)
    hbudget hfinal hentropy hβ.le (lt_add_one β) le_rfl le_rfl (by linarith only [hβ])
    (by change 3 * β + 1 + (β + 1) + 4 * (β + 1) + 4 ≤ 8 * β + 10; linarith only [])
    le_rfl le_rfl le_rfl le_rfl
    ψ hψ hreal heven hψK (by simpa only [show (3 : ℝ) ^ 2 = 9 by norm_num] using hsupp) hlower
  have hgeom := eventual_character_selected_shell_geometry α β z hα hαβ (by linarith only [hz])
    q (n + 1) hq hn i j k hij hjk
  filter_upwards [hcut, hgeom, eventual_character_prime_total hM α β hα hαβ,
    eventual_character_index_cutoff β hβ (n + 1), eventually_ge_atTop (0 : ℝ)]
    with L hcut hgeom htotal hindex hL
  intro P hP hrange γs' νw' γw' νa' hbulk us Ulate v huslo hushi hUlo hUhi hvlo hvhi hsmallmass htopmass
    hrich χ hχ center ζ hζ href
  let m := ⌊z * L⌋₊
  let U : Finset ℕ := P.filter (fun p : ℕ => νw * L < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ γw * L)
  let T₀ := loglogShell P v
  let Q : Fin (m + 1) → Finset ℕ := Fin.cases T₀ (fun _ => U)
  let τ := characterRoundedTau (n + 1) v
  have hg := hgeom us Ulate v huslo hushi hUlo (by simpa only [Nat.cast_add, Nat.cast_one] using hUhi) hvlo hvhi
  rcases hg with ⟨hv2, husv, hαus, hαv, hβus, hβv, hαU, hβU, hUτ, hτU, hpair, hwordsize⟩
  have hround := character_rounded_endpoint_bounds (n + 1) v Ulate hv2 (by
    have hnR : (20000 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hn
    linarith only [hvlo, hnR])
  have hτpos : 0 < τ := by linarith only [hround.2.2.1]
  have hUP : U ⊆ P := Finset.filter_subset _ _
  have hTP : T₀ ⊆ P := Finset.filter_subset _ _
  have hUrange : ∀ p ∈ U, Real.exp (Real.exp (νw * L)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.exp (γw * L)) := by
    intro p hp
    have hh := Finset.mem_filter.mp hp
    exact ⟨prime_of_loglog_lower p (hP p hh.1) _ hh.2.1.le,
      prime_of_loglog_upper p (hP p hh.1) _ hh.2.2⟩
  have hUlog : ∀ p ∈ U, νw * L < Real.log (Real.log (p : ℝ)) ∧
      Real.log (Real.log (p : ℝ)) ≤ γw * L := fun _ hp => (Finset.mem_filter.mp hp).2
  have hUT : Disjoint U T₀ := by
    apply Finset.disjoint_left.mpr
    intro p hp ht
    have hu := (hUlog p hp).2
    have hv := (Finset.mem_filter.mp ht).2.1
    have hgap := (characterBandPoint_strictMono α β q hαβ hq hjk).le
    have hh := mul_le_mul_of_nonneg_right hgap hL
    linarith only [hu, hv, hh, hUlo, hvlo, Nat.cast_nonneg (α := ℝ) (n + 1)]
  have hQsub (i : Fin (m + 1)) : Q i ⊆ P := by exact Fin.cases hTP (fun _ => hUP) i
  have hbulklog (p : ℕ) (hp : p ∈ U) : Real.log (p : ℝ) ≤ Real.exp (γw * L) :=
    (Real.log_le_iff_le_exp (Real.log_pos (by exact_mod_cast (hP p (hUP hp)).one_lt))).mp (hUlog p hp).2
  let u : Fin (n + 1) × Bool → ℝ := fun j => if j.2 then v else us
  refine hcut Ulate τ (Real.exp (γw * L)) P U T₀ hP Q (characterIndexCutoff β L)
    (by nlinarith only [hαU, mul_nonneg hα.le hL])
    hβU hUτ hτU
    hτpos hround.2.2.1 rfl (fun _ => rfl) hQsub hbulk htopmass (htotal P hP hrange)
    (character_ambient_prime_ranges α β L hα hL P hP hrange) hUrange hUT
    (hwordsize _ (Nat.floor_le (by positivity)))
    (character_rounded_top_shell (n + 1) v Ulate hv2 (by
      have hnR : (20000 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hn
      linarith only [hvlo, hnR]) P hP) hbulklog
    (νw * L) (γw * L) hUlog (by
      have hh := mul_le_mul_of_nonneg_right (characterBandPoint_strictMono α β q hαβ hq hjk).le hL
      exact hh.trans hUlo)
    hindex.2 hindex.1 (fun p hp => primeLogIndex_le_characterIndexCutoff β L p (hP p hp) (hrange p hp).2)
    hrich u ?_ ?_ ?_ ?_ ?_ ?_ χ hχ center ζ hζ
    (characterRoundedEndpoint (n + 1) v) hround.2.1 href
  · rintro ⟨j, b⟩
    cases b <;> simp only [u, Bool.false_eq_true, ↓reduceIte]
    · constructor
      · nlinarith only [hαus, mul_nonneg hα.le hL]
      · exact hβus
    · constructor
      · nlinarith only [hαv, mul_nonneg hα.le hL]
      · exact hβv
  · rintro ⟨j, b⟩
    cases b
    · left
      change us + 1 ≤ νw * L
      exact hushi.trans (mul_le_mul_of_nonneg_right
        (characterBandPoint_strictMono α β q hαβ hq hij).le hL)
    · right
      change γw * L ≤ v
      have hh := mul_le_mul_of_nonneg_right (characterBandPoint_strictMono α β q hαβ hq hjk).le hL
      nlinarith only [hh, hUlo, hvlo, Nat.cast_nonneg (α := ℝ) (n + 1)]
  · exact fun _ => hushi
  · intro j
    change νa * L ≤ v
    nlinarith only [hUlo, hvlo, Nat.cast_nonneg (α := ℝ) (n + 1)]
  · exact fun _ => hpair
  · rintro ⟨j, b⟩
    cases b
    · exact hsmallmass
    · exact htopmass

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterDepthParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform depth choices for the actual character endpoint construction -/
namespace Ostmann
open Filter

/-- The same fixed gap also pays the explicit nonanchor comparison margin. -/
theorem character_strong_gap_choice (a Ctotal Aend Bword Cdy ε : ℝ) :
    ∃ B : ℝ, 1 ≤ B ∧ 2 * (Aend + 2 * Bword + 3) + 5 ≤ B ∧
      2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
        (Aend + 2 * Bword + 1) + 2) ≤ B ∧
      2 * (Aend + 2 * Bword + 3) +
        (Cdy / a + max (Real.log 3) 0 + ε) + Real.log 2 + 6 ≤ B + 20 * Real.log a := by
  obtain ⟨B, hB, hrepeat, hanchor⟩ := character_gap_choice a Ctotal Aend Bword Cdy ε
  let B' := max B (2 * (Aend + 2 * Bword + 3) + 5)
  have hBB : B ≤ B' := le_max_left _ _
  exact ⟨B', hB.trans hBB, le_max_right _ _, hrepeat.trans hBB, by linarith only [hanchor, hBB]⟩

/-- This cutoff includes the progression-input constant and strict `z > 1`;
all bounds hold for every later depth, before the rich block chooses one. -/
theorem character_complete_depth_cutoff (c δ Cmass Cfinal B B₁ C₀ : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (hCmass : 0 ≤ Cmass) (hC₀ : 0 < C₀) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ 20000 ≤ K ∧ ∀ k : ℕ, K ≤ k →
      1 < cellRoleScale k ∧ C₀ ≤ Real.exp ((k : ℝ) / 10000) ∧
      Cfinal + (B + 20 * Real.log (cellRoleScale k) + 1) + 2 * B₁ + 1 ≤
        ((k - 1 : ℕ) : ℝ) * Real.log 2 - 1 ∧
      4 * Cmass *
        (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) ≤ cellRoleScale k := by
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge (10000 * Real.log C₀)
  obtain ⟨K, hK, hdepth⟩ := character_depth_and_mass_budget c δ Cmass Cfinal B B₁ hc hδ hCmass
    (max Kmin (max 20000 K₀))
  refine ⟨K, (le_max_left _ _).trans hK,
    (le_max_left _ _).trans ((le_max_right _ _).trans hK), ?_⟩
  intro k hk
  obtain ⟨hk1, _, hentropy, hmass⟩ := hdepth k hk
  have hscale : 1 < cellRoleScale k := by
    apply Real.one_lt_exp_iff.mpr
    unfold cellRoleEpsilon
    have hkpos : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hk1
    positivity
  have hK₀k : K₀ ≤ k :=
    (le_max_right 20000 K₀).trans ((le_max_right Kmin _).trans (hK.trans hk))
  have hkR : (K₀ : ℝ) ≤ k := by exact_mod_cast hK₀k
  have hlog : Real.log C₀ ≤ (k : ℝ) / 10000 := by linarith only [hK₀, hkR]
  have hC : C₀ ≤ Real.exp ((k : ℝ) / 10000) :=
    (Real.log_le_iff_le_exp hC₀).mp hlog
  exact ⟨hscale, hC, hentropy, hmass⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFixedParameters
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One gap choice and one depth threshold for every selected prime band -/
namespace Ostmann

/-- All rates here precede the finite choice of the three bands and the rich
block depth. The number of cells affects only the later large-L threshold. -/
theorem exists_character_fixed_parameters (a β c δ Ctotal C₀ : ℝ)
    (hβ : 0 < β) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC₀ : 0 < C₀) (Kmin : ℕ) :
    let Aend := 8 * β + 10
    let Bword := β + 1 - 2 * Real.log δ
    let B₁ := Aend + 2 * Bword + 3
    let Cdy := β + Real.log ((Real.log 2)⁻¹ + 1)
    let Cfinal := β + 1 + Real.log ((Real.log 2)⁻¹ + 1) + max (Real.log 3) 0 + 1
    0 ≤ Bword ∧ 0 ≤ B₁ ∧ ∃ B : ℝ, 1 ≤ B ∧ 2 * B₁ + 5 ≤ B ∧
      2 * ((2 * Real.log (3 / a) + 3 + 2 * Ctotal) +
        (Aend + 2 * Bword + 1) + 2) ≤ B ∧
      2 * B₁ + (Cdy / a + max (Real.log 3) 0 + 1) + Real.log 2 + 6 ≤
        B + 20 * Real.log a ∧
      ∃ K : ℕ, Kmin ≤ K ∧ 20000 ≤ K ∧ ∀ k : ℕ, K ≤ k →
        1 < cellRoleScale k ∧ C₀ ≤ Real.exp ((k : ℝ) / 10000) ∧
        Cfinal + (B + 20 * Real.log (cellRoleScale k) + 1) + 2 * B₁ + 1 ≤
          ((k - 1 : ℕ) : ℝ) * Real.log 2 - 1 ∧
        4 * (β + 1) *
          (characterTargetLabelBound c δ k + (k + 1) + (k + 1) : ℕ) ≤ cellRoleScale k := by
  intro Aend Bword B₁ Cdy Cfinal
  have hlog : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hword : 0 ≤ Bword := by dsimp only [Bword]; linarith only [hβ, hlog]
  have hB₁ : 0 ≤ B₁ := by dsimp only [B₁, Aend]; linarith only [hβ, hword]
  obtain ⟨B, hB, hstrong, hrepeat, hanchor⟩ :=
    character_strong_gap_choice a Ctotal Aend Bword Cdy 1
  obtain ⟨K, hK, hKlarge, hdepth⟩ := character_complete_depth_cutoff
    c δ (β + 1) Cfinal B B₁ C₀ hc hδ (by linarith) hC₀ Kmin
  exact ⟨hword, hB₁, B, hB, hstrong, hrepeat, hanchor, K, hK, hKlarge, hdepth⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPositiveMassExclusion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive harmonic mass of uniformly biased higher-order characters is impossible -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem PublishedProgressionInput.eventual_positive_character_mass_exclusion
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (α β c δ : ℝ) (hα : 0 < α) (hαβ : α < β) (hc : 0 < c)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α * L < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L) →
      c * L ≤ ∑ p ∈ P, (p : ℝ)⁻¹ →
      ∀ (χ : ∀ p : ℕ, DirichletCharacter ℂ p), (∀ p ∈ P, χ p ^ 2 ≠ 1) →
      ∀ (center : ∀ p : ℕ, ZMod p) (ζ : ℂ), ‖ζ‖ = 1 →
      (∀ p ∈ P, 2 * δ ≤ residueTestMean (tailSupport Aset N₀ p)
        (realTranslatedCharacterTest χ center ζ p)) → False := by
  classical
  obtain ⟨q, hq, H, hselect⟩ := exists_character_band_selection hM α β c hα hαβ hc
  let c₀ := c / (32 * (β - α))
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  let a := min (c / (2 * q)) 1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have ha1 : a ≤ 1 := min_le_right _ _
  obtain ⟨C₀, hC₀, hconcrete⟩ := P0.concrete_character_band_contradiction
    hsize hM hAset hBset hsum N₀ hN₀ α β c₀ δ hα hαβ hc₀ hδ hδ1
  obtain ⟨Kmin, hKmin⟩ := exists_nat_ge
    (max 40000 (64 * (Real.exp 1 + 1) * 10000 / (c / (2 * (β - α)))))
  have hdensity : 0 < c / (2 * (β - α)) := by positivity
  have hβ : 0 < β := hα.trans hαβ
  obtain ⟨_, _, B, hB, hstrong, hrepeat, hanchor, K, hKminK, hKlarge, hdepth⟩ :=
    exists_character_fixed_parameters a β c₀ δ ((Real.exp 1 + 1) * (β - α + 1)) C₀
      hβ hc₀ hδ hδ1 hC₀ Kmin
  have hKminR : (Kmin : ℝ) ≤ K := by exact_mod_cast hKminK
  have hK40000 : (40000 : ℝ) ≤ K := (le_max_left _ _).trans (hKmin.trans hKminR)
  have hKε : 4 ≤ (1 / 10000 : ℝ) * K := by linarith only [hK40000]
  have hKmass : 64 * (Real.exp 1 + 1) ≤ (c / (2 * (β - α))) * (1 / 10000 : ℝ) * K := by
    have hh := (le_max_right _ _).trans (hKmin.trans hKminR)
    have hh' := (div_le_iff₀ hdensity).mp hh
    nlinarith only [hh']
  let Triple := {t : Fin q × Fin q × Fin q // t.1.val + 1 < t.2.1.val ∧ t.2.1.val + 1 < t.2.2.val}
  have hfinite (h : Fin (H + 1)) (t : Triple) := by
    let d := K * 200000 ^ h.val
    have hKd : K ≤ d := Nat.le_mul_of_pos_right K (pow_pos (by decide) _)
    have hd1 : 1 ≤ d := by omega
    have hdn : d - 1 + 1 = d := Nat.sub_add_cancel hd1
    obtain ⟨hz, hC, hentropy, hbudget⟩ := hdepth d hKd
    have hdlarge : 20000 ≤ d - 1 + 1 := by omega
    exact hconcrete q (d - 1) hq hdlarge (by simpa only [hdn] using hC)
      t.val.1 t.val.2.1 t.val.2.2 t.property.1 t.property.2
      a (cellRoleScale d) B ha ha1 hz hB hstrong hrepeat hanchor hentropy
      (by simpa only [hdn, show d - 1 + 2 = d + 1 by omega] using hbudget)
  have hall := eventually_all.mpr (fun h : Fin (H + 1) =>
    eventually_all.mpr (fun t : Triple => hfinite h t))
  filter_upwards [hall, hselect K (by omega) hKε hKmass, eventually_ge_atTop (0 : ℝ)]
    with L hall hselect hL
  intro P hP hrange hmass χ hχ center ζ hζ href
  have hmass' : c * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
      (fun p => (p : ℝ)⁻¹) (α * L) (β * L) := by
    convert hmass using 1
    all_goals try with_reducible_and_instances rfl
    unfold weightedIntervalMass
    rw [Finset.filter_eq_self.mpr hrange]
  obtain ⟨i, j, k, hij, hjk, hbulk, us, huslo, hushi, hsmall, h, hh, U, hUlo, hUhi, hrich⟩ :=
    hselect P hP hmass'
  let d := K * 200000 ^ h
  have hd1 : 1 ≤ d := by
    have hKd : K ≤ d := Nat.le_mul_of_pos_right K (pow_pos (by decide) _)
    omega
  have hdn : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨v, hvlo, hvhi, hvmass⟩ := hrich
    (U + (d : ℝ) / 10000) (U + 2 * (d : ℝ) / 10000)
    (by linarith only [hdpos]) (by linarith only [hdpos]) (by linarith only [])
  have hpoint (x : ℕ) : characterBandPoint α β q x * L + ((β - α) / q) * L =
      characterBandPoint α β q (x + 1) * L := by
    rw [characterBandPoint_succ]
    ring
  have hbulk' : a * L ≤ weightedIntervalMass P (fun p => Real.log (Real.log p))
      (fun p => (p : ℝ)⁻¹) (characterBandPoint α β q j.val * L)
        (characterBandPoint α β q (j.val + 1) * L) := by
    have hle := mul_le_mul_of_nonneg_right (min_le_left (c / (2 * q)) 1) hL
    have he : c / (2 * q) * L = c * L / (2 * q) := by ring
    rw [he] at hle
    exact hle.trans (by simpa only [hpoint] using hbulk)
  have hcut := hall ⟨h, by omega⟩ ⟨(i, j, k), hij, hjk⟩
  dsimp only [hfinite] at hcut
  have hdnK : K * 200000 ^ h - 1 + 1 = K * 200000 ^ h := hdn
  have hcastK : ((K * 200000 ^ h - 1 : ℕ) : ℝ) + 1 = (K * 200000 ^ h : ℕ) := by
    exact_mod_cast hdnK
  simp only [hdnK, hcastK] at hcut
  refine hcut P hP hrange hbulk' us U (U + v) huslo ?_ hUlo ?_ hvlo hvhi hsmall hvmass
    hrich χ hχ center ζ hζ href
  · simpa only [hpoint] using hushi
  · simpa only [hpoint] using hUhi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TailCharacterRotation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common rotation for the actual translated character averages -/
namespace Ostmann
open scoped Classical BigOperators

theorem realTranslatedCharacterTest_mean (A : Set ℕ) (N : ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (center : ∀ p : ℕ, ZMod p) (ζ : ℂ) (p : ℕ) :
    residueTestMean (tailSupport A N p) (realTranslatedCharacterTest χ center ζ p) =
      (ζ * translatedTailCharacterMean A N χ center p).re := by
  unfold residueTestMean realTranslatedCharacterTest translatedTailCharacterMean
  rw [← mul_div_assoc]
  simp_rw [Finset.mul_sum]
  rw [show ((tailSupport A N p).card : ℂ) = (((tailSupport A N p).card : ℝ) : ℂ) by simp,
    Complex.div_ofReal_re]
  simp only [Complex.re_sum]

theorem common_positive_tail_character_rotation (A : Set ℕ) (N : ℕ) (P : Finset ℕ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (center : ∀ p : ℕ, ZMod p) (δ : ℝ)
    (hm : ∀ p ∈ P, δ ≤ ‖translatedTailCharacterMean A N χ center p‖) :
    ∃ ζ : ℂ, ∃ E : Finset ℕ, ‖ζ‖ = 1 ∧ E ⊆ P ∧
      (∑ p ∈ P, (p : ℝ)⁻¹) / 4 ≤ ∑ p ∈ E, (p : ℝ)⁻¹ ∧
      ∀ p ∈ E, δ / 2 ≤ residueTestMean (tailSupport A N p)
        (realTranslatedCharacterTest χ center ζ p) := by
  obtain ⟨ζ, E, hζ, hEP, hmass, hmean⟩ := common_positive_character_rotation P
    (translatedTailCharacterMean A N χ center) δ hm
  exact ⟨ζ, E, hζ, hEP, hmass, fun p hp => by
    rw [realTranslatedCharacterTest_mean]
    exact hmean p hp⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterHigherBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform translated higher-order character bias of the actual residue supports -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem translatedResidueCharacterMean_norm_le_one (A : Set ℕ) (N p : ℕ)
    (χ : DirichletCharacter ℂ p) (t : ZMod p) :
    ‖translatedResidueCharacterMean A N p χ t‖ ≤ 1 := by
  unfold translatedResidueCharacterMean
  rw [norm_div, Complex.norm_natCast]
  have hs : ‖∑ r ∈ tailSupport A N p, χ ((r : ZMod p) - t)‖ ≤ (tailSupport A N p).card := by
    calc
      _ ≤ ∑ r ∈ tailSupport A N p, ‖χ ((r : ZMod p) - t)‖ := norm_sum_le _ _
      _ ≤ ∑ _r ∈ tailSupport A N p, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => χ.norm_le_one _)
      _ = _ := by simp
  exact (div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)).trans (div_self_le_one _)

theorem higherCharacterBias_nonneg (A : Set ℕ) (N p : ℕ) : 0 ≤ higherCharacterBias A N p := by
  apply le_csSup _ (Set.mem_insert 0 _)
  refine ⟨1, ?_⟩
  rintro r (rfl | ⟨χ, _, t, rfl⟩)
  · norm_num
  · exact translatedResidueCharacterMean_norm_le_one A N p χ t

theorem higherCharacterBias_le_one (A : Set ℕ) (N p : ℕ) : higherCharacterBias A N p ≤ 1 := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro r (rfl | ⟨χ, _, t, rfl⟩)
  · norm_num
  · exact translatedResidueCharacterMean_norm_le_one A N p χ t

theorem higherCharacterBias_witness (A : Set ℕ) (N p : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : δ < higherCharacterBias A N p) :
    ∃ χ : DirichletCharacter ℂ p, χ ^ 2 ≠ 1 ∧
      ∃ t : ZMod p, δ < ‖translatedResidueCharacterMean A N p χ t‖ := by
  obtain ⟨r, hr, hδr⟩ := exists_lt_of_lt_csSup (Set.insert_nonempty 0 _) h
  rcases hr with rfl | ⟨χ, hχ, t, rfl⟩
  · exact (not_lt_of_ge hδ hδr).elim
  · exact ⟨χ, hχ, t, hδr⟩

theorem PublishedProgressionInput.eventual_large_character_bias_mass
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (α β c δ : ℝ) (hα : 0 < α) (hαβ : α < β) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α * L < Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L) →
      (∀ p ∈ P, δ < higherCharacterBias Aset N₀ p) →
      (∑ p ∈ P, (p : ℝ)⁻¹) < c * L := by
  classical
  let ε := min (δ / 4) 1
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεδ : 2 * ε ≤ δ / 2 := by
    have hh := min_le_left (δ / 4) (1 : ℝ)
    change 2 * min (δ / 4) 1 ≤ δ / 2
    linarith only [hh]
  have hcut := P0.eventual_positive_character_mass_exclusion hsize hM hAset hBset hsum N₀ hN₀
    α β (c / 4) ε hα hαβ (by positivity) hε hε1
  filter_upwards [hcut] with L hcut P hP hrange hbias
  by_contra hm
  have hmass : c * L ≤ ∑ p ∈ P, (p : ℝ)⁻¹ := le_of_not_gt hm
  have hchoice : ∀ p : ℕ, ∃ χ : DirichletCharacter ℂ p, ∃ t : ZMod p,
      p ∈ P → χ ^ 2 ≠ 1 ∧ δ < ‖translatedResidueCharacterMean Aset N₀ p χ t‖ := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨χ, hχ, t, ht⟩ := higherCharacterBias_witness Aset N₀ p hδ.le (hbias p hp)
      exact ⟨χ, t, fun _ => ⟨hχ, ht⟩⟩
    · exact ⟨1, 0, fun hh => (hp hh).elim⟩
  choose χ center hchoice using hchoice
  obtain ⟨ζ, E, hζ, hEP, hEmass, href⟩ := common_positive_tail_character_rotation Aset N₀ P χ center δ
    (fun p hp => (hchoice p hp).2.le)
  apply hcut E (fun p hp => hP p (hEP hp)) (fun p hp => hrange p (hEP hp))
    (by nlinarith only [hmass, hEmass]) χ (fun p hp => (hchoice p (hEP hp)).1) center ζ hζ
  exact fun p hp => hεδ.trans (href p hp)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_HigherCharacterDecorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Proposition 4.1: maximal translated higher-order bias has harmonic mass o(L) -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

theorem mem_closedLogLogPrimeBand_iff (α β L : ℝ) (p : ℕ) :
    p ∈ closedLogLogPrimeBand α β L ↔ p.Prime ∧
      α * L ≤ Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L := by
  simp only [closedLogLogPrimeBand, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp, hprime⟩, hlo⟩
    refine ⟨hprime, hlo, ?_⟩
    have hpp : (p : ℝ) ≤ Real.exp (Real.exp (β * L)) :=
      (by exact_mod_cast hp : (p : ℝ) ≤ ⌊Real.exp (Real.exp (β * L))⌋₊).trans
        (Nat.floor_le (Real.exp_nonneg _))
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast hprime.one_lt
    apply (Real.log_le_iff_le_exp (Real.log_pos hp1)).mpr
    exact (Real.log_le_iff_le_exp hp0).mpr hpp
  · rintro ⟨hprime, hlo, hhi⟩
    exact ⟨⟨Nat.le_floor (prime_of_loglog_upper p hprime _ hhi), hprime⟩, hlo⟩

theorem PublishedProgressionInput.eventual_higher_character_mass_bound
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, α * L ≤ Real.log (Real.log (p : ℝ)) ∧ Real.log (Real.log (p : ℝ)) ≤ β * L) →
      (∑ p ∈ P, (p : ℝ)⁻¹ * higherCharacterBias Aset N₀ p) ≤ ε * L := by
  classical
  let C := (Real.exp 1 + 1) * (β - α / 2 + 1)
  have hαhalf : 0 < α / 2 := by positivity
  have hhalfβ : α / 2 < β := by linarith only [hα, hαβ]
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := ε / (2 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hexc := P0.eventual_large_character_bias_mass hsize hM hAset hBset hsum N₀ hN₀
    (α / 2) β (ε / 2) δ hαhalf hhalfβ (by positivity) hδ
  filter_upwards [hexc, eventual_character_prime_total hM (α / 2) β hαhalf hhalfβ,
    eventually_gt_atTop (0 : ℝ)] with L hexc htotal hL P hP hrange
  have hrange' (p : ℕ) (hp : p ∈ P) : (α / 2) * L < Real.log (Real.log (p : ℝ)) ∧
      Real.log (Real.log (p : ℝ)) ≤ β * L := by
    refine ⟨?_, (hrange p hp).2⟩
    have hh : (α / 2) * L < α * L := mul_lt_mul_of_pos_right (by linarith only [hα]) hL
    exact hh.trans_le (hrange p hp).1
  let E := P.filter (fun p => δ < higherCharacterBias Aset N₀ p)
  have hEmass : (∑ p ∈ E, (p : ℝ)⁻¹) < (ε / 2) * L :=
    hexc E (fun p hp => hP p (Finset.mem_filter.mp hp).1)
      (fun p hp => hrange' p (Finset.mem_filter.mp hp).1)
      (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hPmass : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ C * L := by
    have hh := htotal P hP hrange'
    rw [Finset.sum_coe_sort P (fun p : ℕ => (p : ℝ)⁻¹)] at hh
    exact hh
  have hpoint (p : ℕ) (hp : p ∈ P) :
      (p : ℝ)⁻¹ * higherCharacterBias Aset N₀ p ≤
        (p : ℝ)⁻¹ * δ + if p ∈ E then (p : ℝ)⁻¹ else 0 := by
    by_cases he : p ∈ E
    · rw [ite_eq_left he]
      have hh := mul_le_mul_of_nonneg_left (higherCharacterBias_le_one Aset N₀ p)
        (show 0 ≤ (p : ℝ)⁻¹ by positivity)
      have hpos : 0 ≤ (p : ℝ)⁻¹ * δ := by positivity
      simpa only [mul_one] using hh.trans (le_add_of_nonneg_left hpos)
    · rw [ite_eq_right he, add_zero]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_of_not_gt (fun hh => he (Finset.mem_filter.mpr ⟨hp, hh⟩))
  have hsum := Finset.sum_le_sum hpoint
  have hEsum : (∑ p ∈ P, if p ∈ E then (p : ℝ)⁻¹ else 0) = ∑ p ∈ E, (p : ℝ)⁻¹ := by
    rw [← Finset.sum_filter]
    congr 1
    ext p
    simp only [E, Finset.mem_filter, and_self_left]
  rw [Finset.sum_add_distrib, hEsum, ← Finset.sum_mul] at hsum
  have hδC : C * δ = ε / 2 := by dsimp [δ]; field_simp
  have hsmall := mul_le_mul_of_nonneg_right hPmass hδ.le
  have heq : C * L * δ = (ε / 2) * L := by rw [mul_right_comm, hδC]
  rw [heq] at hsmall
  linarith only [hsum, hsmall, hEmass]

/-- The manuscript's Proposition 4.1, with the maximum represented by the
supremum over all translated characters whose square is nonprincipal. -/
theorem PublishedProgressionInput.higher_character_decorrelation
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    (fun L => higherCharacterBandMass Aset N₀ α β L) =o[atTop] (fun L : ℝ => L) := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [P0.eventual_higher_character_mass_bound hsize hM hAset hBset hsum N₀ hN₀
    α β ε hα hαβ hε, eventually_ge_atTop (0 : ℝ)] with L hbound hL
  have hnonneg : 0 ≤ higherCharacterBandMass Aset N₀ α β L :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (by positivity) (higherCharacterBias_nonneg _ _ _))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs, abs_of_nonneg hL]
  exact hbound _ (fun p hp => ((mem_closedLogLogPrimeBand_iff α β L p).mp hp).1)
    (fun p hp => ((mem_closedLogLogPrimeBand_iff α β L p).mp hp).2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_MaximalQuadraticBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Maximizing translating residues and the little-o conclusion -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem maximalQuadraticBias_nonneg (S : Finset ℕ) (p : ℕ) : 0 ≤ maximalQuadraticBias S p :=
  abs_nonneg _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_ClosedQuadraticBand
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The closed prime band used in the manuscript's quadratic proposition -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem mem_closedLogPrimeBand_iff (T : ℝ) (p : ℕ) :
    p ∈ closedLogPrimeBand T ↔ p.Prime ∧ T ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 2 * T := by
  simp only [closedLogPrimeBand, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp, hprime⟩, hlo⟩
    refine ⟨hprime, hlo, (Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mpr ?_⟩
    exact (by exact_mod_cast hp : (p : ℝ) ≤ ⌊Real.exp (2 * T)⌋₊).trans (Nat.floor_le (Real.exp_nonneg _))
  · rintro ⟨hprime, hlo, hhi⟩
    exact ⟨⟨Nat.le_floor ((Real.log_le_iff_le_exp (by exact_mod_cast hprime.pos)).mp hhi), hprime⟩, hlo⟩

theorem closedQuadraticBandMass_nonneg (A : Set ℕ) (N : ℕ) (T : ℝ) :
    0 ≤ closedQuadraticBandMass A N T := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := ((mem_closedLogPrimeBand_iff T p).mp hp).1
  exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg _))
    (maximalQuadraticBias_nonneg _ _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DyadicHarmonicBias
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring quadratic smallness to harmonic prime intervals -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem harmonicQuadraticBias_nonneg (A : Set ℕ) (N p : ℕ) :
    0 ≤ harmonicQuadraticBias A N p := div_nonneg (maximalQuadraticBias_nonneg _ _) (Nat.cast_nonneg _)

theorem harmonicQuadratic_closedBand_le (A : Set ℕ) (N : ℕ) (T ε : ℝ)
    (hT : 0 < T) (hbound : closedQuadraticBandMass A N T ≤ ε * T) :
    (∑ p ∈ closedLogPrimeBand T, harmonicQuadraticBias A N p) ≤ ε := by
  have hterm (p : ℕ) (hp : p ∈ closedLogPrimeBand T) :
      harmonicQuadraticBias A N p ≤
        ((Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p) / T := by
    apply (le_div_iff₀ hT).mpr
    have hh := (mem_closedLogPrimeBand_iff T p).mp hp
    have hb := mul_le_mul_of_nonneg_right hh.2.1
      (harmonicQuadraticBias_nonneg A N p)
    dsimp [harmonicQuadraticBias] at *
    first | (convert hb using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hb.trans (le_of_eq (by ring)))
  calc
    _ ≤ ∑ p ∈ closedLogPrimeBand T,
        ((Real.log (p : ℝ) / p) * maximalQuadraticBias (tailSupport A N p) p) / T :=
      Finset.sum_le_sum hterm
    _ = closedQuadraticBandMass A N T / T := by rw [← Finset.sum_div]; rfl
    _ ≤ (ε * T) / T := div_le_div_of_nonneg_right hbound hT.le
    _ = ε := mul_div_cancel_right₀ ε hT.ne'

/-- Closed dyadic intervals cover the specified finite logarithmic range. -/
theorem exists_dyadic_cover (X u : ℝ) (n : ℕ) (hX : 0 < X) (hlo : X ≤ u)
    (hhi : u ≤ (2 : ℝ) ^ n * X) :
    ∃ j ≤ n, (2 : ℝ) ^ j * X ≤ u ∧ u ≤ 2 * ((2 : ℝ) ^ j * X) := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, by simpa using hlo, ?_⟩
    simp only [pow_zero, one_mul] at hhi ⊢
    linarith
  | succ n ih =>
    by_cases hh : u ≤ (2 : ℝ) ^ n * X
    · obtain ⟨j, hj, hju, huj⟩ := ih hh
      exact ⟨j, Nat.le_succ_of_le hj, hju, huj⟩
    · refine ⟨n, Nat.le_succ n, (not_le.mp hh).le, ?_⟩
      simpa only [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hhi

theorem harmonicQuadraticBandMass_dyadic_bound (A : Set ℕ) (N n : ℕ)
    (α β L ε : ℝ) (hcover : Real.exp (β * L) ≤ (2 : ℝ) ^ n * Real.exp (α * L))
    (hlocal : ∀ j ≤ n,
      closedQuadraticBandMass A N ((2 : ℝ) ^ j * Real.exp (α * L)) ≤
        ε * ((2 : ℝ) ^ j * Real.exp (α * L))) :
    harmonicQuadraticBandMass A N α β L ≤ ((n : ℝ) + 1) * ε := by
  let H := iteratedLogPrimeBand α β L
  let P := fun j : ℕ => closedLogPrimeBand ((2 : ℝ) ^ j * Real.exp (α * L))
  have hsub (p : ℕ) (hp : p ∈ H) : ∃ j ∈ Finset.range (n + 1), p ∈ P j := by
    obtain ⟨hpprime, hplo⟩ := Finset.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primesLE hpprime
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hpu : Real.log (p : ℝ) ≤ Real.exp (β * L) :=
      (Real.log_le_iff_le_exp hp0).mpr
        ((by exact_mod_cast Nat.le_of_mem_primesLE hpprime :
          (p : ℝ) ≤ ⌊Real.exp (Real.exp (β * L))⌋₊).trans (Nat.floor_le (Real.exp_nonneg _)))
    obtain ⟨j, hj, hjlo, hjhi⟩ := exists_dyadic_cover (Real.exp (α * L)) (Real.log (p : ℝ)) n
      (Real.exp_pos _) hplo (hpu.trans hcover)
    exact ⟨j, Finset.mem_range.mpr (by omega),
      (mem_closedLogPrimeBand_iff _ p).mpr ⟨hprime, hjlo, hjhi⟩⟩
  have hterm (p : ℕ) (hp : p ∈ H) : harmonicQuadraticBias A N p ≤
      ∑ j ∈ Finset.range (n + 1), if p ∈ P j then harmonicQuadraticBias A N p else 0 := by
    obtain ⟨j, hj, hpj⟩ := hsub p hp
    have hh := Finset.single_le_sum (s := Finset.range (n + 1))
      (f := fun j => if p ∈ P j then harmonicQuadraticBias A N p else 0)
      (fun i _ => by split <;> simp [harmonicQuadraticBias_nonneg]) hj
    simpa only [ite_eq_left hpj] using hh
  calc
    _ ≤ ∑ p ∈ H, ∑ j ∈ Finset.range (n + 1),
        if p ∈ P j then harmonicQuadraticBias A N p else 0 := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.range (n + 1), ∑ p ∈ H,
        if p ∈ P j then harmonicQuadraticBias A N p else 0 := Finset.sum_comm
    _ ≤ ∑ _j ∈ Finset.range (n + 1), ε := by
      apply Finset.sum_le_sum
      intro j hj
      have hsplit : (∑ p ∈ H, if p ∈ P j then harmonicQuadraticBias A N p else 0) =
          ∑ p ∈ H.filter (fun p => p ∈ P j), harmonicQuadraticBias A N p := by rw [Finset.sum_filter]
      rw [hsplit]
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (fun p hp => (Finset.mem_filter.mp hp).2)
        (fun p _ _ => harmonicQuadraticBias_nonneg A N p))
      exact harmonicQuadratic_closedBand_le A N _ ε (by positivity) (hlocal j (by simpa using hj))
    _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_HarmonicQuadraticSmallness
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The harmonic-band consequence of the quadratic proposition -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem mem_iteratedLogPrimeBand_iff (α β L : ℝ) (p : ℕ) :
    p ∈ iteratedLogPrimeBand α β L ↔
      p.Prime ∧ α * L ≤ Real.log (Real.log (p : ℝ)) ∧
        Real.log (Real.log (p : ℝ)) ≤ β * L := by
  simp only [iteratedLogPrimeBand, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp, hprime⟩, hlo⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    refine ⟨hprime, (Real.le_log_iff_exp_le hlog).mpr hlo, ?_⟩
    apply (Real.log_le_iff_le_exp hlog).mpr
    apply (Real.log_le_iff_le_exp hp0).mpr
    exact (by exact_mod_cast hp : (p : ℝ) ≤ ⌊Real.exp (Real.exp (β * L))⌋₊).trans (Nat.floor_le (Real.exp_nonneg _))
  · rintro ⟨hprime, hlo, hhi⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
    refine ⟨⟨Nat.le_floor ?_, hprime⟩, (Real.le_log_iff_exp_le hlog).mp hlo⟩
    exact (Real.log_le_iff_le_exp hp0).mp ((Real.log_le_iff_le_exp hlog).mp hhi)

theorem harmonicQuadraticBandMass_nonneg (A : Set ℕ) (N : ℕ) (α β L : ℝ) :
    0 ≤ harmonicQuadraticBandMass A N α β L :=
  Finset.sum_nonneg (fun p _ => harmonicQuadraticBias_nonneg A N p)

private theorem dyadic_shell_count (β L : ℝ) (hβ : 0 ≤ β) (hL : 1 ≤ L) :
    let n := ⌈β * L / Real.log 2⌉₊
    Real.exp (β * L) ≤ (2 : ℝ) ^ n ∧
      (n : ℝ) + 1 ≤ (β / Real.log 2 + 2) * L := by
  intro n
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hn : β * L / Real.log 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hu : (n : ℝ) < β * L / Real.log 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have he : Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  refine ⟨?_, ?_⟩
  · rw [← he]
    exact Real.exp_le_exp.mpr ((div_le_iff₀ hlog).mp hn)
  · have heq : β * L / Real.log 2 = (β / Real.log 2) * L := by ring
    rw [heq] at hu
    nlinarith

theorem harmonicQuadraticBandMass_isLittleO (A : Set ℕ) (N : ℕ) (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hsmall : (fun T => closedQuadraticBandMass A N T) =o[atTop] (fun T : ℝ => T)) :
    (fun L => harmonicQuadraticBandMass A N α β L) =o[atTop] (fun L : ℝ => L) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  let C := β / Real.log 2 + 2
  let ε := c / C
  have hC : 0 < C := by dsimp [C]; positivity
  have hε : 0 < ε := div_pos hc hC
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hsmall.bound hε)
  have hgrowth : Tendsto (fun L : ℝ => Real.exp (α * L)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hα)
  filter_upwards [hgrowth.eventually_ge_atTop T₀, eventually_ge_atTop (1 : ℝ)] with L hlarge hL
  let n := ⌈β * L / Real.log 2⌉₊
  obtain ⟨hexp, hcount⟩ := dyadic_shell_count β L hβ.le hL
  have hstart : 1 ≤ Real.exp (α * L) := Real.one_le_exp (by positivity)
  have hcover : Real.exp (β * L) ≤ (2 : ℝ) ^ n * Real.exp (α * L) :=
    hexp.trans (le_mul_of_one_le_right (by positivity) hstart)
  have hlocal : ∀ j ≤ n, closedQuadraticBandMass A N ((2 : ℝ) ^ j * Real.exp (α * L)) ≤
      ε * ((2 : ℝ) ^ j * Real.exp (α * L)) := by
    intro j _
    have hstartj : Real.exp (α * L) ≤ (2 : ℝ) ^ j * Real.exp (α * L) :=
      le_mul_of_one_le_left (Real.exp_nonneg _) (one_le_pow₀ (by norm_num))
    have hh := hT₀ _ (hlarge.trans hstartj)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (closedQuadraticBandMass_nonneg A N _),
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ j * Real.exp (α * L))] using hh
  have hmass := harmonicQuadraticBandMass_dyadic_bound A N n α β L ε hcover hlocal
  rw [Real.norm_eq_abs, abs_of_nonneg (harmonicQuadraticBandMass_nonneg A N α β L),
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ L)]
  apply hmass.trans
  calc
    _ ≤ (C * L) * ε := mul_le_mul_of_nonneg_right hcount hε.le
    _ = c * L := by dsimp [ε]; field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AllCharacterDecorrelation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining quadratic and higher-order translated decorrelation -/
namespace Ostmann
open Filter
open scoped Classical BigOperators Topology

theorem closedLogLogPrimeBand_eq_iterated (α β L : ℝ) :
    closedLogLogPrimeBand α β L = iteratedLogPrimeBand α β L := by
  ext p
  rw [mem_closedLogLogPrimeBand_iff, mem_iteratedLogPrimeBand_iff]

theorem tailCharacterBandMass_eq (A : Set ℕ) (N : ℕ) (α β L : ℝ) :
    tailCharacterBandMass A N α β L =
      harmonicQuadraticBandMass A N α β L + higherCharacterBandMass A N α β L := by
  simp only [tailCharacterBandMass, tailCharacterBias, mul_add, Finset.sum_add_distrib,
    harmonicQuadraticBandMass, harmonicQuadraticBias, higherCharacterBandMass,
    ← closedLogLogPrimeBand_eq_iterated, div_eq_mul_inv, mul_comm]

theorem PublishedProgressionInput.all_character_decorrelation_oai
    (P0 : PublishedProgressionInput)
    (hsize : PublishedSummandSizeBound) {CM : ℝ} (hM : MertensEstimate CM)
    {Aset Bset : Set ℕ} (hAset : Aset.Infinite) (hBset : Bset.Infinite)
    (hsum : EventuallyPrimeSumset Aset Bset) (N₀ : ℕ)
    (hN₀ : ∀ p, p.Prime → Disjoint (tailResidues Aset N₀ p) (negTailResidues Bset N₀ p))
    (hquad : (fun T => closedQuadraticBandMass Aset N₀ T) =o[atTop] (fun T : ℝ => T))
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    (fun L => tailCharacterBandMass Aset N₀ α β L) =o[atTop] (fun L : ℝ => L) := by
  have hh := (harmonicQuadraticBandMass_isLittleO Aset N₀ α β hα (hα.trans hαβ) hquad).add
    (P0.higher_character_decorrelation hsize hM hAset hBset hsum N₀ hN₀ α β hα hαβ)
  simpa only [← tailCharacterBandMass_eq] using hh

end Ostmann

end OAI
end

theorem solution : type_of% @OAI.Ostmann.PublishedProgressionInput.all_character_decorrelation_oai := @OAI.Ostmann.PublishedProgressionInput.all_character_decorrelation_oai
