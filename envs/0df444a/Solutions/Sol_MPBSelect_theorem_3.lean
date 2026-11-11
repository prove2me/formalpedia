-- Prove2me | solution 1 for MPBSelect.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T12:40:09.651689+00:00
-- url     : https://prove2.me/submissions/b828f4a7-22c5-40f2-994c-78b341677320

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_MPBSelect_Problem_IsOptimal
import Definitions.Def_MPBSelect_Problem_ZeroRatio
import Definitions.Def_MPBSelect_Problem_PairwiseBalance
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_MPBSelect_Problem_GlobalBalance
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Order.Filter.Finite

/-
Prove2Me S10: full proof of the unchanged MPBSelect.theorem_3 root.
All unpublished local helpers are inlined below; imported project modules are
published definitions only. The coordinate-removal construction in
optimal_zero_ratio is attributed at its declaration to shivm's prior proof.
-/


-- Inlined module: Solutions.P066Rates
section
namespace MPBSelect.S10Rates

variable {k B : ℕ} (P : Problem k B)

theorem W_one_le (i : Fin k) (b : Fin B) : 1 ≤ P.W i b := by
  unfold Problem.W
  split <;> exact le_max_right _ _

theorem W_pos (i : Fin k) (b : Fin B) : 0 < P.W i b :=
  lt_of_lt_of_le (by norm_num) (W_one_le P i b)

theorem G_nonneg (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B) :
    0 ≤ P.G α i b := by
  unfold Problem.G
  split_ifs with h
  · exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg (sq_nonneg _) h.1.le)
        (div_nonneg (sq_nonneg _) h.2.le)))
  · exact le_rfl

theorem G_pos_iff (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B)
    (hi : i ≠ P.ib b) :
    0 < P.G α i b ↔ 0 < α i b ∧ 0 < α (P.ib b) b := by
  constructor
  · intro hG
    by_contra h
    simp only [Problem.G, if_neg h, lt_self_iff_false] at hG
  · intro h
    rw [Problem.G, if_pos h]
    exact div_pos (sq_pos_of_pos (sub_pos.mpr (P.ib_spec b i hi)))
      (mul_pos (by norm_num) (add_pos
        (div_pos (sq_pos_of_pos (P.lam_pos i b)) h.1)
        (div_pos (sq_pos_of_pos (P.lam_pos (P.ib b) b)) h.2)))

theorem ldr_le (α : Fin k → Fin B → ℝ) (x : Fin k × Fin B) (hx : x ∈ P.Xi) :
    P.ldr α ≤ P.W x.1 x.2 * P.G α x.1 x.2 :=
  Finset.inf'_le _ hx

theorem le_ldr (α : Fin k → Fin B → ℝ) (t : ℝ)
    (h : ∀ x ∈ P.Xi, t ≤ P.W x.1 x.2 * P.G α x.1 x.2) : t ≤ P.ldr α :=
  Finset.le_inf' P.Xi_nonempty _ h

theorem ldr_nonneg (α : Fin k → Fin B → ℝ) : 0 ≤ P.ldr α := by
  apply le_ldr P α 0
  intro x _
  exact mul_nonneg (W_pos P x.1 x.2).le (G_nonneg P α x.1 x.2)

theorem ldr_pos_iff (α : Fin k → Fin B → ℝ) :
    0 < P.ldr α ↔ ∀ x ∈ P.Xi, 0 < α x.1 x.2 ∧ 0 < α (P.ib x.2) x.2 := by
  rw [Problem.ldr, Finset.lt_inf'_iff]
  constructor
  · intro h x hx
    have hi : x.1 ≠ P.ib x.2 := (Finset.mem_filter.mp hx).2.2
    exact (G_pos_iff P α x.1 x.2 hi).mp
      ((mul_pos_iff_of_pos_left (W_pos P x.1 x.2)).mp (h x hx))
  · intro h x hx
    have hi : x.1 ≠ P.ib x.2 := (Finset.mem_filter.mp hx).2.2
    exact mul_pos (W_pos P x.1 x.2) ((G_pos_iff P α x.1 x.2 hi).mpr (h x hx))

theorem G_smul (α : Fin k → Fin B → ℝ) {c : ℝ} (hc : 0 < c)
    (i : Fin k) (b : Fin B) :
    P.G (fun i b => c * α i b) i b = c * P.G α i b := by
  unfold Problem.G
  simp only [mul_pos_iff_of_pos_left hc]
  split_ifs with h
  · have hdiv (a x : ℝ) : a / (c * x) = (a / x) / c := by
      rw [mul_comm c x, div_mul_eq_div_div]
    simp only [hdiv]
    rw [← add_div, ← mul_div_assoc, div_div_eq_mul_div]
    ring
  · simp

theorem ldr_smul (α : Fin k → Fin B → ℝ) {c : ℝ} (hc : 0 < c) :
    P.ldr (fun i b => c * α i b) = c * P.ldr α := by
  apply le_antisymm
  · obtain ⟨x, hx, heq⟩ := Finset.exists_mem_eq_inf' P.Xi_nonempty
      (fun x => P.W x.1 x.2 * P.G α x.1 x.2)
    calc
      P.ldr (fun i b => c * α i b) ≤
          P.W x.1 x.2 * P.G (fun i b => c * α i b) x.1 x.2 := ldr_le P _ x hx
      _ = c * (P.W x.1 x.2 * P.G α x.1 x.2) := by rw [G_smul P α hc]; ring
      _ = c * P.ldr α := by rw [Problem.ldr, heq]
  · apply le_ldr P _ _
    intro x hx
    rw [G_smul P α hc]
    calc
      c * P.ldr α ≤ c * (P.W x.1 x.2 * P.G α x.1 x.2) :=
        mul_le_mul_of_nonneg_left (ldr_le P α x hx) hc.le
      _ = P.W x.1 x.2 * (c * P.G α x.1 x.2) := by ring

theorem G_congr (α β : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B)
    (hi : β i b = α i b) (hb : β (P.ib b) b = α (P.ib b) b) :
    P.G β i b = P.G α i b := by
  unfold Problem.G
  rw [hi, hb]

theorem normalize_feasible (β : Fin k → Fin B → ℝ)
    (hβ : ∀ i b, 0 ≤ β i b) (hs : 0 < ∑ i, ∑ b, β i b) :
    (fun i b => (∑ i, ∑ b, β i b)⁻¹ * β i b) ∈ feasibleSet k B := by
  constructor
  · simp_rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · intro i b
    exact mul_nonneg (inv_nonneg.mpr hs.le) (hβ i b)

/-- The uniform allocation has a strictly positive entry at every coordinate. -/
noncomputable def uniformAllocation : Fin k → Fin B → ℝ :=
  fun _ _ => ((k : ℝ) * (B : ℝ))⁻¹

include P

theorem k_pos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) P.two_le_k

theorem B_pos : 0 < B :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) P.Xi_nonempty.choose.2.isLt

theorem uniformAllocation_pos (i : Fin k) (b : Fin B) :
    0 < uniformAllocation (k := k) (B := B) i b := by
  apply inv_pos.mpr
  exact mul_pos (Nat.cast_pos.mpr (k_pos P)) (Nat.cast_pos.mpr (B_pos P))

theorem uniformAllocation_feasible :
    uniformAllocation (k := k) (B := B) ∈ feasibleSet k B := by
  constructor
  · simp only [uniformAllocation, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀]
    exact mul_ne_zero (ne_of_gt (Nat.cast_pos.mpr (k_pos P)))
      (ne_of_gt (Nat.cast_pos.mpr (B_pos P)))
  · intro i b
    exact (uniformAllocation_pos P i b).le

theorem uniform_ldr_pos :
    0 < P.ldr (uniformAllocation (k := k) (B := B)) := by
  apply (ldr_pos_iff P _).mpr
  intro x _
  exact ⟨uniformAllocation_pos P x.1 x.2, uniformAllocation_pos P (P.ib x.2) x.2⟩

theorem optimal_ldr_pos (α : Fin k → Fin B → ℝ) (hα : P.IsOptimal α) :
    0 < P.ldr α :=
  lt_of_lt_of_le (uniform_ldr_pos P) (hα.2 _ (uniformAllocation_feasible P))

theorem mass_pos_of_ldr_pos (β : Fin k → Fin B → ℝ)
    (hβ : ∀ i b, 0 ≤ β i b) (hL : 0 < P.ldr β) :
    0 < ∑ i, ∑ b, β i b := by
  obtain ⟨x, hx⟩ := P.Xi_nonempty
  have hp := ((ldr_pos_iff P β).mp hL x hx).1
  have h1 : β x.1 x.2 ≤ ∑ b, β x.1 b :=
    Finset.single_le_sum (fun b _ => hβ x.1 b) (Finset.mem_univ _)
  have h2 : (∑ b, β x.1 b) ≤ ∑ i, ∑ b, β i b :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun b _ => hβ i b))
      (Finset.mem_univ _)
  exact lt_of_lt_of_le hp (h1.trans h2)

/-- Any allocation meeting an optimal positive rate must use at least unit mass. -/
theorem lower_mass_contradiction (α : Fin k → Fin B → ℝ) (hα : P.IsOptimal α)
    (β : Fin k → Fin B → ℝ) (hβ : ∀ i b, 0 ≤ β i b)
    (hs : 0 < ∑ i, ∑ b, β i b) (hs1 : (∑ i, ∑ b, β i b) < 1)
    (hr : ∀ x ∈ P.Xi, P.ldr α ≤ P.W x.1 x.2 * P.G β x.1 x.2) : False := by
  have hL := optimal_ldr_pos P α hα
  have hβL := le_ldr P β (P.ldr α) hr
  have hc : 1 < (∑ i, ∑ b, β i b)⁻¹ := (one_lt_inv₀ hs).mpr hs1
  have hbetter := mul_lt_mul_of_pos_right hc hL
  rw [one_mul] at hbetter
  have hopt := hα.2 _ (normalize_feasible β hβ hs)
  rw [ldr_smul P β (inv_pos.mpr hs)] at hopt
  have hscale := mul_le_mul_of_nonneg_left hβL (inv_pos.mpr hs).le
  exact (not_lt_of_ge (hscale.trans hopt)) hbetter

theorem optimal_mass_le (α : Fin k → Fin B → ℝ) (hα : P.IsOptimal α)
    (β : Fin k → Fin B → ℝ) (hβ : ∀ i b, 0 ≤ β i b)
    (hr : ∀ x ∈ P.Xi, P.ldr α ≤ P.W x.1 x.2 * P.G β x.1 x.2) :
    1 ≤ ∑ i, ∑ b, β i b := by
  have hL : 0 < P.ldr β :=
    lt_of_lt_of_le (optimal_ldr_pos P α hα) (le_ldr P β (P.ldr α) hr)
  have hs := mass_pos_of_ldr_pos P β hβ hL
  by_contra h
  exact lower_mass_contradiction P α hα β hβ hs (lt_of_not_ge h) hr

/-- Coordinate-removal argument adapted from shivm's accepted Prove2Me submission
9cf946ae-6c20-4c58-ab53-cac83884d159. The normalization and rate lemmas above
supply its independently checked positivity and strict-improvement steps. -/
theorem optimal_zero_ratio (α : Fin k → Fin B → ℝ) (hα : P.IsOptimal α) :
    P.ZeroRatio α := by
  intro b0 hb0
  by_contra hne
  have hc : 0 < α P.istar b0 := lt_of_le_of_ne (hα.1.2 _ _) (Ne.symm hne)
  set c := α P.istar b0 with hcdef
  set β : Fin k → Fin B → ℝ :=
    fun i b => if i = P.istar ∧ b = b0 then 0 else α i b with hβ
  have hβeq : ∀ i b, β i b = α i b -
      (if i = P.istar then 1 else 0) * (if b = b0 then c else 0) := by
    intro i b
    simp only [hβ]
    by_cases h1 : i = P.istar <;> by_cases h2 : b = b0
    · subst h1; subst h2; simp [hcdef]
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]
  have hsum : ∑ i, ∑ b, β i b = 1 - c := by
    simp only [hβeq, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]
    rw [hα.1.1]
  have hβnn : ∀ i b, 0 ≤ β i b := by
    intro i b
    simp only [hβ]
    split_ifs
    · exact le_rfl
    · exact hα.1.2 i b
  have hr : ∀ x ∈ P.Xi, P.ldr α ≤ P.W x.1 x.2 * P.G β x.1 x.2 := by
    intro x hx
    have hxstar : x.1 ≠ P.istar := (Finset.mem_filter.mp hx).2.1
    have hG : P.G β x.1 x.2 = P.G α x.1 x.2 := by
      apply G_congr P α β
      · simp [hβ, hxstar]
      · simp only [hβ]
        rw [if_neg]
        rintro ⟨h1, h2⟩
        apply hb0
        rw [← h2]
        exact h1
    rw [hG]
    exact ldr_le P α x hx
  have hm := optimal_mass_le P α hα β hβnn hr
  rw [hsum] at hm
  linarith

end MPBSelect.S10Rates
end


-- Inlined module: Solutions.P066Pairwise
section
namespace MPBSelect.S10Necessity

open scoped BigOperators
open MPBSelect.S10Rates

variable {k B : ℕ} (P : Problem k B)

/-- Increasing sampling allocations cannot decrease any pairwise rate. -/
theorem G_mono (α β : Fin k → Fin B → ℝ)
    (h : ∀ i b, α i b ≤ β i b) (i : Fin k) (b : Fin B) :
    P.G α i b ≤ P.G β i b := by
  by_cases hα : 0 < α i b ∧ 0 < α (P.ib b) b
  · have hβ : 0 < β i b ∧ 0 < β (P.ib b) b :=
      ⟨lt_of_lt_of_le hα.1 (h i b), lt_of_lt_of_le hα.2 (h (P.ib b) b)⟩
    rw [Problem.G, if_pos hα, Problem.G, if_pos hβ]
    apply div_le_div_of_nonneg_left (sq_nonneg _)
    · exact mul_pos (by norm_num) (add_pos
        (div_pos (sq_pos_of_pos (P.lam_pos i b)) hβ.1)
        (div_pos (sq_pos_of_pos (P.lam_pos (P.ib b) b)) hβ.2))
    · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      exact add_le_add
        (div_le_div_of_nonneg_left (sq_nonneg _) hα.1 (h i b))
        (div_le_div_of_nonneg_left (sq_nonneg _) hα.2 (h (P.ib b) b))
  · have hzero : P.G α i b = 0 := by simp [Problem.G, hα]
    rw [hzero]
    exact G_nonneg P β i b

/-- Every active pair attains the optimal minimum rate. Otherwise its own
competitor allocation can be reduced, leaving all constraints above that minimum. -/
theorem optimal_rate_eq_ldr (α : Fin k → Fin B → ℝ) (hα : P.IsOptimal α)
    (x : Fin k × Fin B) (hx : x ∈ P.Xi) :
    P.W x.1 x.2 * P.G α x.1 x.2 = P.ldr α := by
  classical
  apply le_antisymm
  · by_contra hnot
    have hslack : P.ldr α < P.W x.1 x.2 * P.G α x.1 x.2 := lt_of_not_ge hnot
    rcases x with ⟨i0, b0⟩
    have hL : 0 < P.ldr α := optimal_ldr_pos P α hα
    have hpos : 0 < α i0 b0 := ((ldr_pos_iff P α).mp hL (i0, b0) hx).1
    have hi0 : i0 ≠ P.ib b0 := (Finset.mem_filter.mp hx).2.2
    let R := P.W i0 b0 * P.G α i0 b0
    have hR : 0 < R := lt_trans hL hslack
    let c : ℝ := P.ldr α / R
    have hc : 0 < c := div_pos hL hR
    have hc1 : c < 1 := (div_lt_one hR).mpr hslack
    have hcR : c * R = P.ldr α := div_mul_cancel₀ _ hR.ne'
    let β : Fin k → Fin B → ℝ :=
      fun i b => if i = i0 ∧ b = b0 then c * α i b else α i b
    have hβnn : ∀ i b, 0 ≤ β i b := by
      intro i b
      dsimp only [β]
      split_ifs
      · exact mul_nonneg hc.le (hα.1.2 i b)
      · exact hα.1.2 i b
    have hβle : ∀ i b, β i b ≤ α i b := by
      intro i b
      dsimp only [β]
      split_ifs
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1.le (hα.1.2 i b)
      · exact le_rfl
    have hscaled : ∀ i b, c * α i b ≤ β i b := by
      intro i b
      dsimp only [β]
      split_ifs
      · exact le_rfl
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1.le (hα.1.2 i b)
    have hstrict : β i0 b0 < α i0 b0 := by
      simp only [β, and_self, if_true]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hc1 hpos
    have hsumlt : (∑ i, ∑ b, β i b) < 1 := by
      rw [← hα.1.1]
      apply Finset.sum_lt_sum
      · intro i _
        exact Finset.sum_le_sum (fun b _ => hβle i b)
      · refine ⟨i0, Finset.mem_univ _, ?_⟩
        exact Finset.sum_lt_sum (fun b _ => hβle i0 b)
          ⟨b0, Finset.mem_univ _, hstrict⟩
    have hbest : ∀ b, β (P.ib b) b = α (P.ib b) b := by
      intro b
      have hne : ¬ (P.ib b = i0 ∧ b = b0) := by
        rintro ⟨hib, hb⟩
        subst b
        exact hi0 hib.symm
      simp only [β, if_neg hne]
    have hr : ∀ z ∈ P.Xi, P.ldr α ≤ P.W z.1 z.2 * P.G β z.1 z.2 := by
      intro z hz
      by_cases hz0 : z = (i0, b0)
      · subst z
        have hmono := G_mono P (fun i b => c * α i b) β hscaled i0 b0
        rw [G_smul P α hc] at hmono
        calc
          P.ldr α = c * R := hcR.symm
          _ = P.W i0 b0 * (c * P.G α i0 b0) := by dsimp [R]; ring
          _ ≤ P.W i0 b0 * P.G β i0 b0 :=
            mul_le_mul_of_nonneg_left hmono (W_pos P i0 b0).le
      · have hne : ¬ (z.1 = i0 ∧ z.2 = b0) := by
          rintro ⟨hi, hb⟩
          exact hz0 (Prod.ext hi hb)
        have hsame : P.G β z.1 z.2 = P.G α z.1 z.2 :=
          G_congr P α β z.1 z.2 (by simp only [β, if_neg hne]) (hbest z.2)
        rw [hsame]
        exact ldr_le P α z hz
    exact (not_lt_of_ge (optimal_mass_le P α hα β hβnn hr)) hsumlt
  · exact ldr_le P α x hx

/-- Optimal allocations satisfy pairwise balance across all active pairs. -/
theorem optimal_pairwise_balance (α : Fin k → Fin B → ℝ) (hα : P.IsOptimal α) :
    P.PairwiseBalance α := by
  intro x hx y hy
  exact (optimal_rate_eq_ldr P α hα x hx).trans (optimal_rate_eq_ldr P α hα y hy).symm

end MPBSelect.S10Necessity
end


-- Inlined module: Solutions.P066Coordinates
section
namespace MPBSelect.S10Coordinates

open scoped BigOperators

noncomputable section

variable {k B : ℕ} (P : Problem k B)

/-- The competitors that contribute a rate at one parameter. -/
def active (b : Fin B) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i ≠ P.ib b ∧ i ≠ P.istar)

/-- Variance of a sampling coordinate. -/
def variance (i : Fin k) (b : Fin B) : ℝ := P.lam i b ^ 2

/-- Positive numerator coefficient of a weighted active rate. -/
def coefficient (i : Fin k) (b : Fin B) : ℝ :=
  P.W i b * (P.y i b - P.y (P.ib b) b) ^ 2 / 2

/-- Denominator after multiplying a pairwise rate by both allocations. -/
def pairDenom (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B) : ℝ :=
  variance P i b * α (P.ib b) b + variance P (P.ib b) b * α i b

@[simp] theorem mem_active (i : Fin k) (b : Fin B) :
    i ∈ active P b ↔ i ≠ P.ib b ∧ i ≠ P.istar := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_active_iff_mem_Xi (i : Fin k) (b : Fin B) :
    i ∈ active P b ↔ (i, b) ∈ P.Xi := by
  simp only [mem_active, Problem.Xi, Finset.mem_filter, Finset.mem_univ,
    true_and, and_comm]

theorem variance_pos (i : Fin k) (b : Fin B) : 0 < variance P i b :=
  sq_pos_of_pos (P.lam_pos i b)

theorem coefficient_pos (i : Fin k) (b : Fin B) (hi : i ∈ active P b) :
    0 < coefficient P i b := by
  apply div_pos _ (by norm_num)
  exact mul_pos (S10Rates.W_pos P i b)
    (sq_pos_of_pos (sub_pos.mpr (P.ib_spec b i ((mem_active P i b).mp hi).1)))

theorem pairDenom_pos (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B)
    (hx : 0 < α i b) (hy : 0 < α (P.ib b) b) : 0 < pairDenom P α i b :=
  add_pos (mul_pos (variance_pos P i b) hy) (mul_pos (variance_pos P (P.ib b) b) hx)

/-- Clear the two allocation reciprocals in a weighted pairwise rate. -/
theorem harmonic_identity (w g A D x y : ℝ)
    (hA : 0 < A) (hD : 0 < D) (hx : 0 < x) (hy : 0 < y) :
    w * (g / (2 * (A / x + D / y))) =
      (w * g / 2) * x * y / (A * y + D * x) := by
  have hden : A * y + D * x ≠ 0 := ne_of_gt (add_pos (mul_pos hA hy) (mul_pos hD hx))
  have hden' : A * y + x * D ≠ 0 := by simpa only [mul_comm] using hden
  rw [div_add_div A D (ne_of_gt hx) (ne_of_gt hy)]
  field_simp [hden, hden', ne_of_gt hx, ne_of_gt hy]
  all_goals try field_simp [hden, hden', ne_of_gt hx, ne_of_gt hy]
  all_goals ring

theorem weighted_rate_fraction (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B)
    (hx : 0 < α i b) (hy : 0 < α (P.ib b) b) :
    P.W i b * P.G α i b =
      coefficient P i b * α i b * α (P.ib b) b / pairDenom P α i b := by
  rw [Problem.G, if_pos ⟨hx, hy⟩]
  exact harmonic_identity (P.W i b) ((P.y i b - P.y (P.ib b) b) ^ 2)
    (variance P i b) (variance P (P.ib b) b) (α i b) (α (P.ib b) b)
    (variance_pos P i b) (variance_pos P (P.ib b) b) hx hy

theorem target_eq_rate_iff (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B)
    (t : ℝ) (hx : 0 < α i b) (hy : 0 < α (P.ib b) b) :
    (t = P.W i b * P.G α i b) ↔
      t * pairDenom P α i b = coefficient P i b * α i b * α (P.ib b) b := by
  rw [weighted_rate_fraction P α i b hx hy]
  exact eq_div_iff (ne_of_gt (pairDenom_pos P α i b hx hy))

theorem target_le_rate_iff (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B)
    (t : ℝ) (hx : 0 < α i b) (hy : 0 < α (P.ib b) b) :
    (t ≤ P.W i b * P.G α i b) ↔
      t * pairDenom P α i b ≤ coefficient P i b * α i b * α (P.ib b) b := by
  rw [weighted_rate_fraction P α i b hx hy]
  exact le_div_iff₀ (pairDenom_pos P α i b hx hy)

theorem target_lt_rate_iff (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B)
    (t : ℝ) (hx : 0 < α i b) (hy : 0 < α (P.ib b) b) :
    (t < P.W i b * P.G α i b) ↔
      t * pairDenom P α i b < coefficient P i b * α i b * α (P.ib b) b := by
  rw [weighted_rate_fraction P α i b hx hy]
  exact lt_div_iff₀ (pairDenom_pos P α i b hx hy)

/-- Split a parameter block into its best coordinate, active competitors,
and the possibly unused most-probable-best coordinate. -/
theorem block_mass_decompose (α : Fin k → Fin B → ℝ) (b : Fin B) :
    (∑ i, α i b) = α (P.ib b) b + (∑ i ∈ active P b, α i b) +
      (if P.istar = P.ib b then 0 else α P.istar b) := by
  have hpoint (i : Fin k) : α i b =
      (if i = P.ib b then α i b else 0) +
      (if i ≠ P.ib b ∧ i ≠ P.istar then α i b else 0) +
      (if i = P.istar ∧ i ≠ P.ib b then α i b else 0) := by
    by_cases hi : i = P.ib b
    · simp [hi]
    · by_cases his : i = P.istar <;> simp_all
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
  simpa only [active, Finset.sum_filter, Finset.sum_add_distrib, ite_and,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, ite_not] using hsum

/-- ZeroRatio removes the unused coordinate from each block budget. -/
theorem block_mass (α : Fin k → Fin B → ℝ) (hzero : P.ZeroRatio α) (b : Fin B) :
    (∑ i, α i b) = α (P.ib b) b + ∑ i ∈ active P b, α i b := by
  rw [block_mass_decompose P α b]
  have hother : (if P.istar = P.ib b then 0 else α P.istar b) = 0 := by
    split_ifs with h
    · rfl
    · exact hzero b (Ne.symm h)
  rw [hother, add_zero]

/-- Every nonnegative block pays at least for its best and active coordinates. -/
theorem block_mass_le (α : Fin k → Fin B → ℝ) (hnonneg : ∀ i b, 0 ≤ α i b)
    (b : Fin B) :
    α (P.ib b) b + (∑ i ∈ active P b, α i b) ≤ ∑ i, α i b := by
  rw [block_mass_decompose P α b]
  split_ifs <;> linarith [hnonneg P.istar b]

/-- A block with no active rate has zero total budget under both balance conditions. -/
theorem block_mass_zero_of_active_empty (α : Fin k → Fin B → ℝ)
    (hglobal : P.GlobalBalance α) (hzero : P.ZeroRatio α) (b : Fin B)
    (hempty : active P b = ∅) : (∑ i, α i b) = 0 := by
  have hbest := hglobal b
  change α (P.ib b) b ^ 2 / variance P (P.ib b) b =
    ∑ i ∈ active P b, α i b ^ 2 / variance P i b at hbest
  rw [hempty, Finset.sum_empty] at hbest
  have hz : α (P.ib b) b = 0 := sq_eq_zero_iff.mp
    ((div_eq_zero_iff.mp hbest).resolve_right (ne_of_gt (variance_pos P (P.ib b) b)))
  rw [block_mass P α hzero b, hempty, Finset.sum_empty, hz, add_zero]

end

end MPBSelect.S10Coordinates
end


-- Inlined module: Solutions.P066ScalarCost
section
namespace MPBSelect.S10ScalarCost

open scoped BigOperators Topology

noncomputable section

/-- The supporting-line error for one normalized budget term is a square. -/
theorem tangent_identity (A B C z u : ℝ)
    (hz : C * z - B ≠ 0) (hu : C * u - B ≠ 0) :
    A * z / (C * z - B) - A * u / (C * u - B) +
        A * B / (C * u - B) ^ 2 * (z - u) =
      A * B * C * (z - u) ^ 2 / ((C * z - B) * (C * u - B) ^ 2) := by
  field_simp [hz, hu]
  field_simp [hz, hu]
  <;> ring

/-- Positive normalized budget terms lie above their tangent lines. -/
theorem tangent_lower_bound (A B C z u : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hz : 0 < C * z - B) (hu : 0 < C * u - B) :
    A * u / (C * u - B) - A * B / (C * u - B) ^ 2 * (z - u) ≤
      A * z / (C * z - B) := by
  have hidentity := tangent_identity A B C z u (ne_of_gt hz) (ne_of_gt hu)
  have hnonneg : 0 ≤
      A * B * C * (z - u) ^ 2 / ((C * z - B) * (C * u - B) ^ 2) := by
    positivity
  linarith


/-- The budget needed at one parameter, per unit of target rate. -/
def cost {ι : Type*} (I : Finset ι) (A : ι → ℝ) (B : ℝ) (C : ι → ℝ)
    (z : ℝ) : ℝ :=
  z + ∑ i ∈ I, A i * z / (C i * z - B)

/-- Summing the supporting lines gives a supporting line for the full cost. -/
theorem cost_tangent {ι : Type*} (I : Finset ι) (A : ι → ℝ) (B : ℝ)
    (C : ι → ℝ) (z u : ℝ)
    (hA : ∀ i ∈ I, 0 < A i) (hB : 0 < B) (hC : ∀ i ∈ I, 0 < C i)
    (hz : ∀ i ∈ I, 0 < C i * z - B)
    (hu : ∀ i ∈ I, 0 < C i * u - B) :
    cost I A B C u + (1 - ∑ i ∈ I, A i * B / (C i * u - B) ^ 2) * (z - u) ≤
      cost I A B C z := by
  have hsum := Finset.sum_le_sum (s := I) fun i hi =>
    tangent_lower_bound (A i) B (C i) z u (hA i hi) hB (hC i hi) (hz i hi) (hu i hi)
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
  unfold cost
  nlinarith [hsum]

/-- The global balance equation is sufficient for minimum required budget. -/
theorem cost_min_of_balance {ι : Type*} (I : Finset ι) (A : ι → ℝ) (B : ℝ)
    (C : ι → ℝ) (u : ℝ)
    (hA : ∀ i ∈ I, 0 < A i) (hB : 0 < B) (hC : ∀ i ∈ I, 0 < C i)
    (hu : ∀ i ∈ I, 0 < C i * u - B)
    (hbalance : ∑ i ∈ I, A i * B / (C i * u - B) ^ 2 = 1) :
    ∀ z : ℝ, (∀ i ∈ I, 0 < C i * z - B) → cost I A B C u ≤ cost I A B C z := by
  intro z hz
  simpa only [hbalance, sub_self, zero_mul, add_zero] using
    cost_tangent I A B C z u hA hB hC hz hu

/-- Derivative of one normalized budget term. -/
theorem hasDerivAt_term (A B C u : ℝ) (hu : C * u - B ≠ 0) :
    HasDerivAt (fun z : ℝ => A * z / (C * z - B))
      (- (A * B / (C * u - B) ^ 2)) u := by
  have hn : HasDerivAt (fun z : ℝ => A * z) A u := hasDerivAt_const_mul A
  have hd : HasDerivAt (fun z : ℝ => C * z - B) C u :=
    (hasDerivAt_const_mul C).sub_const B
  have hnum : A * (C * u - B) - A * u * C = -(A * B) := by ring
  simpa only [hnum, neg_div] using hn.fun_div hd hu

/-- The derivative is one minus the normalized global-balance sum. -/
theorem hasDerivAt_cost {ι : Type*} (I : Finset ι) (A : ι → ℝ) (B : ℝ)
    (C : ι → ℝ) (u : ℝ) (hu : ∀ i ∈ I, C i * u - B ≠ 0) :
    HasDerivAt (cost I A B C)
      (1 - ∑ i ∈ I, A i * B / (C i * u - B) ^ 2) u := by
  have hsum := HasDerivAt.fun_sum (u := I) fun i hi =>
    hasDerivAt_term (A i) B (C i) u (hu i hi)
  change HasDerivAt (fun z : ℝ => z + ∑ i ∈ I, A i * z / (C i * z - B))
    (1 - ∑ i ∈ I, A i * B / (C i * u - B) ^ 2) u
  convert! (hasDerivAt_id u).fun_add hsum using 1
  all_goals first | rfl | simp only [Finset.sum_neg_distrib, sub_eq_add_neg]

/-- Positive denominators remain positive near an interior parameter. -/
theorem eventually_cost_domain {ι : Type*} (I : Finset ι) (B : ℝ) (C : ι → ℝ)
    (u : ℝ) (hu : ∀ i ∈ I, 0 < C i * u - B) :
    ∀ᶠ z in 𝓝 u, ∀ i ∈ I, 0 < C i * z - B := by
  apply (Filter.eventually_all_finset I).2
  intro i hi
  have hc : ContinuousAt (fun z : ℝ => C i * z - B) u :=
    ((continuous_const.mul continuous_id).sub continuous_const).continuousAt
  exact hc.tendsto.eventually (eventually_gt_nhds (hu i hi))

/-- A minimum within the open denominator domain satisfies global balance. -/
theorem balance_of_cost_min {ι : Type*} (I : Finset ι) (A : ι → ℝ) (B : ℝ)
    (C : ι → ℝ) (u : ℝ) (hu : ∀ i ∈ I, 0 < C i * u - B)
    (hmin : ∀ z : ℝ, (∀ i ∈ I, 0 < C i * z - B) → cost I A B C u ≤ cost I A B C z) :
    ∑ i ∈ I, A i * B / (C i * u - B) ^ 2 = 1 := by
  have hlocal : IsLocalMin (cost I A B C) u :=
    (eventually_cost_domain I B C u hu).mono fun z hz => hmin z hz
  have hzero := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_cost I A B C u fun i hi => ne_of_gt (hu i hi))
  linarith

/-- Exact minimum-budget characterization, requiring no general KKT theorem. -/
theorem cost_min_iff_balance {ι : Type*} (I : Finset ι) (A : ι → ℝ) (B : ℝ)
    (C : ι → ℝ) (u : ℝ)
    (hA : ∀ i ∈ I, 0 < A i) (hB : 0 < B) (hC : ∀ i ∈ I, 0 < C i)
    (hu : ∀ i ∈ I, 0 < C i * u - B) :
    (∀ z : ℝ, (∀ i ∈ I, 0 < C i * z - B) → cost I A B C u ≤ cost I A B C z) ↔
      ∑ i ∈ I, A i * B / (C i * u - B) ^ 2 = 1 := by
  exact ⟨balance_of_cost_min I A B C u hu,
    cost_min_of_balance I A B C u hA hB hC hu⟩

end

end MPBSelect.S10ScalarCost
end


-- Inlined module: Solutions.P066CostBridges
section
namespace MPBSelect.S10ScalarCost

open scoped BigOperators

noncomputable section

/-- A positive equal-rate equation solves each competitor allocation in terms
of the best allocation divided by the common target rate. -/
theorem normalized_rate (A B C t x y : ℝ)
    (hA : 0 < A) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y)
    (hcross : t * (A * y + B * x) = C * x * y) :
    0 < C * (y / t) - B ∧ x = A * y / (C * (y / t) - B) := by
  have hprod : (C * (y / t) - B) * x = A * y := by
    field_simp [ne_of_gt ht]
    nlinarith [hcross]
  have hden : 0 < C * (y / t) - B := by
    have hpos : 0 < (C * (y / t) - B) * x := by
      rw [hprod]
      exact mul_pos hA hy
    exact pos_of_mul_pos_left hpos hx.le
  refine ⟨hden, (eq_div_iff (ne_of_gt hden)).2 ?_⟩
  simpa only [mul_comm] using hprod

/-- A rate at least the target rate gives a lower bound on the competitor
allocation in normalized coordinates. -/
theorem normalized_rate_lower_bound (A B C t x y : ℝ)
    (hA : 0 < A) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y)
    (hcross : t * (A * y + B * x) ≤ C * x * y) :
    0 < C * (y / t) - B ∧ A * y / (C * (y / t) - B) ≤ x := by
  have hprod : A * y ≤ (C * (y / t) - B) * x := by
    apply (mul_le_mul_iff_of_pos_left ht).mp
    calc
      t * (A * y) ≤ C * x * y - t * B * x := by nlinarith [hcross]
      _ = t * ((C * (y / t) - B) * x) := by
        field_simp [ne_of_gt ht]
        <;> ring
  have hden : 0 < C * (y / t) - B :=
    pos_of_mul_pos_left (lt_of_lt_of_le (mul_pos hA hy) hprod) hx.le
  refine ⟨hden, (div_le_iff₀ hden).2 ?_⟩
  simpa only [mul_comm] using hprod

/-- The square-ratio term in global balance is a fixed positive multiple
of the corresponding scalar stationarity term. -/
theorem square_ratio_identity (A B y d : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hd : d ≠ 0) :
    (A * y / d) ^ 2 / A = (y ^ 2 / B) * (A * B / d ^ 2) := by
  field_simp [hA, hB, hd]
  <;> ring

/-- Convert the original global-balance equation to stationarity of cost. -/
theorem allocation_balance_iff {ι : Type*} (I : Finset ι)
    (A : ι → ℝ) (B : ℝ) (C x : ι → ℝ) (y u : ℝ)
    (hA : ∀ i ∈ I, 0 < A i) (hB : 0 < B) (hy : 0 < y)
    (hden : ∀ i ∈ I, 0 < C i * u - B)
    (hformula : ∀ i ∈ I, x i = A i * y / (C i * u - B)) :
    (y ^ 2 / B = ∑ i ∈ I, x i ^ 2 / A i) ↔
      ∑ i ∈ I, A i * B / (C i * u - B) ^ 2 = 1 := by
  have hsum : (∑ i ∈ I, x i ^ 2 / A i) =
      (y ^ 2 / B) * ∑ i ∈ I, A i * B / (C i * u - B) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hformula i hi]
    exact square_ratio_identity (A i) B y (C i * u - B)
      (ne_of_gt (hA i hi)) (ne_of_gt hB) (ne_of_gt (hden i hi))
  rw [hsum]
  have hpositive : 0 < y ^ 2 / B := by positivity
  constructor
  · intro h
    apply mul_left_cancel₀ (ne_of_gt hpositive)
    simpa only [mul_one] using h.symm
  · intro h
    rw [h, mul_one]

/-- Equal-rate allocations use exactly target-rate times scalar cost. -/
theorem allocation_mass_eq_cost {ι : Type*} (I : Finset ι)
    (A : ι → ℝ) (B : ℝ) (C x : ι → ℝ) (t y u : ℝ)
    (hy : y = t * u)
    (hformula : ∀ i ∈ I, x i = A i * y / (C i * u - B)) :
    y + ∑ i ∈ I, x i = t * cost I A B C u := by
  simp only [cost, mul_add, Finset.mul_sum]
  rw [hy]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hformula i hi, hy]
  ring

/-- Any allocation meeting a target rate uses at least its normalized cost. -/
theorem scaled_cost_le_allocation_mass {ι : Type*} (I : Finset ι)
    (A : ι → ℝ) (B : ℝ) (C x : ι → ℝ) (t y u : ℝ)
    (hy : y = t * u)
    (hformula : ∀ i ∈ I, A i * y / (C i * u - B) ≤ x i) :
    t * cost I A B C u ≤ y + ∑ i ∈ I, x i := by
  have heq := allocation_mass_eq_cost I A B C
    (fun i => A i * y / (C i * u - B)) t y u hy (fun _ _ => rfl)
  rw [← heq]
  simpa only [add_comm] using add_le_add_left (Finset.sum_le_sum hformula) y

/-- Reconstructing allocations at any point of the cost domain keeps every
pairwise rate equal to the target rate. -/
theorem reconstructed_cross (A B C t u : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (ht : 0 < t)
    (hden : 0 < C * u - B) :
    let y := t * u
    let x := A * y / (C * u - B)
    0 < y ∧ 0 < x ∧ t * (A * y + B * x) = C * x * y := by
  dsimp only
  have hu : 0 < u := by nlinarith
  have hy : 0 < t * u := mul_pos ht hu
  refine ⟨hy, div_pos (mul_pos hA hy) hden, ?_⟩
  have hmul : (A * (t * u) / (C * u - B)) * (C * u - B) = A * (t * u) :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hmul_t := congrArg (fun r : ℝ => t * r) hmul
  nlinarith [hmul_t]


end

end MPBSelect.S10ScalarCost
end


-- Inlined module: Solutions.P066OptimalCoordinates
section
namespace MPBSelect.S10OptimalCoordinates

open S10Coordinates

variable {k B : ℕ} (P : Problem k B)

/-- An optimal allocation solves every active equal-rate constraint explicitly. -/
theorem optimal_normalized_data (α : Fin k → Fin B → ℝ) (hopt : P.IsOptimal α)
    (b : Fin B) :
    (∀ i ∈ active P b,
      0 < coefficient P i b * (α (P.ib b) b / P.ldr α) - variance P (P.ib b) b) ∧
    (∀ i ∈ active P b,
      α i b = variance P i b * α (P.ib b) b /
        (coefficient P i b * (α (P.ib b) b / P.ldr α) - variance P (P.ib b) b)) := by
  have ht := S10Rates.optimal_ldr_pos P α hopt
  have hpos := (S10Rates.ldr_pos_iff P α).mp ht
  have hdata : ∀ i ∈ active P b,
      0 < coefficient P i b * (α (P.ib b) b / P.ldr α) - variance P (P.ib b) b ∧
      α i b = variance P i b * α (P.ib b) b /
        (coefficient P i b * (α (P.ib b) b / P.ldr α) - variance P (P.ib b) b) := by
    intro i hi
    have hxi := (mem_active_iff_mem_Xi P i b).mp hi
    have hx := (hpos (i, b) hxi).1
    have hy := (hpos (i, b) hxi).2
    have heq := (S10Necessity.optimal_rate_eq_ldr P α hopt (i, b) hxi).symm
    have hcross := (target_eq_rate_iff P α i b (P.ldr α) hx hy).mp heq
    exact S10ScalarCost.normalized_rate
      (variance P i b) (variance P (P.ib b) b) (coefficient P i b)
      (P.ldr α) (α i b) (α (P.ib b) b)
      (variance_pos P i b) ht hx hy hcross
  exact ⟨fun i hi => (hdata i hi).1, fun i hi => (hdata i hi).2⟩

/-- The budget of an optimal block is its objective value times normalized cost.
The formula also holds when that block has no active competitors. -/
theorem optimal_block_mass_eq_cost (α : Fin k → Fin B → ℝ) (hopt : P.IsOptimal α)
    (b : Fin B) :
    (∑ i, α i b) = P.ldr α * S10ScalarCost.cost (active P b)
      (fun i => variance P i b) (variance P (P.ib b) b) (fun i => coefficient P i b)
      (α (P.ib b) b / P.ldr α) := by
  have ht := S10Rates.optimal_ldr_pos P α hopt
  have hy : α (P.ib b) b = P.ldr α * (α (P.ib b) b / P.ldr α) := by
    field_simp [ne_of_gt ht]
  rw [block_mass P α (S10Rates.optimal_zero_ratio P α hopt) b]
  exact S10ScalarCost.allocation_mass_eq_cost
    (active P b) (fun i => variance P i b) (variance P (P.ib b) b)
    (fun i => coefficient P i b) (fun i => α i b) (P.ldr α)
    (α (P.ib b) b) (α (P.ib b) b / P.ldr α) hy
    (optimal_normalized_data P α hopt b).2

end MPBSelect.S10OptimalCoordinates
end


-- Inlined module: Solutions.P066Reconstruct
section
namespace MPBSelect.S10Reconstruct

open scoped BigOperators
open S10Coordinates S10ScalarCost

noncomputable section

variable {k B : ℕ} (P : Problem k B)

/-- Rebuild one parameter block with common target rate `t` at a scalar
point `z` in the positive-denominator domain. -/
def reconstructBlock (b : Fin B) (t z : ℝ) (i : Fin k) : ℝ :=
  if i = P.ib b then t * z
  else if i = P.istar then 0
  else variance P i b * (t * z) /
    (coefficient P i b * z - variance P (P.ib b) b)

@[simp] theorem reconstruct_best (b : Fin B) (t z : ℝ) :
    reconstructBlock P b t z (P.ib b) = t * z := by
  simp [reconstructBlock]

theorem reconstruct_active (b : Fin B) (t z : ℝ) (i : Fin k)
    (hi : i ∈ active P b) :
    reconstructBlock P b t z i = variance P i b * (t * z) /
      (coefficient P i b * z - variance P (P.ib b) b) := by
  obtain ⟨hib, his⟩ := (mem_active P i b).mp hi
  simp [reconstructBlock, hib, his]

theorem reconstruct_zero (b : Fin B) (t z : ℝ)
    (hb : P.ib b ≠ P.istar) :
    reconstructBlock P b t z P.istar = 0 := by
  simp [reconstructBlock, Ne.symm hb]

/-- A nonempty active block has a strictly positive scalar domain. -/
theorem domain_pos (b : Fin B) (z : ℝ)
    (hne : (active P b).Nonempty)
    (hden : ∀ i ∈ active P b,
      0 < coefficient P i b * z - variance P (P.ib b) b) : 0 < z := by
  obtain ⟨i, hi⟩ := hne
  have hprod : 0 < coefficient P i b * z :=
    lt_trans (variance_pos P (P.ib b) b) (sub_pos.mp (hden i hi))
  exact pos_of_mul_pos_right hprod (coefficient_pos P i b hi).le

theorem reconstruct_nonneg (b : Fin B) (t z : ℝ) (ht : 0 < t)
    (hne : (active P b).Nonempty)
    (hden : ∀ i ∈ active P b,
      0 < coefficient P i b * z - variance P (P.ib b) b) :
    ∀ i, 0 ≤ reconstructBlock P b t z i := by
  have hy : 0 < t * z := mul_pos ht (domain_pos P b z hne hden)
  intro i
  by_cases hib : i = P.ib b
  · subst i
    simpa only [reconstruct_best] using hy.le
  by_cases his : i = P.istar
  · simp only [reconstructBlock, if_neg hib, if_pos his, le_refl]
  have hi : i ∈ active P b := (mem_active P i b).mpr ⟨hib, his⟩
  rw [reconstruct_active P b t z i hi]
  exact (div_pos (mul_pos (variance_pos P i b) hy) (hden i hi)).le

/-- Reconstruction uses exactly the target rate times normalized block cost. -/
theorem reconstruct_mass (b : Fin B) (t z : ℝ) :
    (∑ i, reconstructBlock P b t z i) =
      t * cost (active P b) (fun i => variance P i b)
        (variance P (P.ib b) b) (fun i => coefficient P i b) z := by
  have hmass := block_mass_decompose P (fun i _ => reconstructBlock P b t z i) b
  have hother : (if P.istar = P.ib b then 0 else
      reconstructBlock P b t z P.istar) = 0 := by
    split_ifs with h
    · rfl
    · exact reconstruct_zero P b t z (Ne.symm h)
  rw [hother, add_zero, reconstruct_best] at hmass
  rw [hmass]
  exact allocation_mass_eq_cost (active P b) (fun i => variance P i b)
    (variance P (P.ib b) b) (fun i => coefficient P i b)
    (reconstructBlock P b t z) t (t * z) z rfl
    (fun i hi => reconstruct_active P b t z i hi)

/-- Every active rate of the reconstructed block equals the target rate. -/
theorem reconstruct_rate (β : Fin k → Fin B → ℝ) (b : Fin B) (t z : ℝ)
    (ht : 0 < t)
    (hden : ∀ i ∈ active P b,
      0 < coefficient P i b * z - variance P (P.ib b) b)
    (hβ : ∀ i, β i b = reconstructBlock P b t z i)
    (i : Fin k) (hi : i ∈ active P b) :
    P.W i b * P.G β i b = t := by
  obtain ⟨hy, hx, hcross⟩ := reconstructed_cross
    (variance P i b) (variance P (P.ib b) b) (coefficient P i b) t z
    (variance_pos P i b) (variance_pos P (P.ib b) b)
    (coefficient_pos P i b hi) ht (hden i hi)
  have hyβ : 0 < β (P.ib b) b := by
    rw [hβ (P.ib b), reconstruct_best]
    exact hy
  have hxβ : 0 < β i b := by
    rw [hβ i, reconstruct_active P b t z i hi]
    exact hx
  apply Eq.symm
  apply (target_eq_rate_iff P β i b t hxβ hyβ).mpr
  rw [pairDenom, hβ i, hβ (P.ib b), reconstruct_best,
    reconstruct_active P b t z i hi]
  exact hcross

end

end MPBSelect.S10Reconstruct
end


-- Inlined module: Solutions.P066Inactive
section
namespace MPBSelect.S10Necessity

open scoped BigOperators
open MPBSelect.S10Rates MPBSelect.S10Coordinates

variable {k B : ℕ} (P : Problem k B)

/-- Replacing one parameter block changes the total mass by exactly the
new block mass minus the old block mass. -/
theorem replace_block_mass (α : Fin k → Fin B → ℝ) (b0 : Fin B) (v : Fin k → ℝ) :
    (∑ i, ∑ b, if b = b0 then v i else α i b) =
      (∑ i, ∑ b, α i b) - (∑ i, α i b0) + ∑ i, v i := by
  have hpoint (i : Fin k) (b : Fin B) :
      (if b = b0 then v i else α i b) =
        α i b + (if b = b0 then v i - α i b0 else 0) := by
    by_cases hb : b = b0
    · subst b
      simp
    · simp [hb]
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_sub_distrib]
  ring

/-- An optimal allocation spends no mass at a parameter that contributes no
active pair. Removing that entire block leaves every objective rate unchanged. -/
theorem optimal_unused_parameter_mass_zero (α : Fin k → Fin B → ℝ)
    (hα : P.IsOptimal α) (b0 : Fin B)
    (hno : ∀ i : Fin k, (i, b0) ∉ P.Xi) : (∑ i, α i b0) = 0 := by
  classical
  let β : Fin k → Fin B → ℝ := fun i b => if b = b0 then 0 else α i b
  have hβnn : ∀ i b, 0 ≤ β i b := by
    intro i b
    dsimp only [β]
    split_ifs
    · exact le_rfl
    · exact hα.1.2 i b
  have hr : ∀ x ∈ P.Xi, P.ldr α ≤ P.W x.1 x.2 * P.G β x.1 x.2 := by
    rintro ⟨i, b⟩ hx
    have hb : b ≠ b0 := by
      intro heq
      exact hno i (heq ▸ hx)
    have hsame : P.G β i b = P.G α i b :=
      G_congr P α β i b (by simp [β, hb]) (by simp [β, hb])
    rw [hsame]
    exact ldr_le P α (i, b) hx
  have hm := optimal_mass_le P α hα β hβnn hr
  have hmass : (∑ i, ∑ b, β i b) = 1 - ∑ i, α i b0 := by
    dsimp only [β]
    simpa only [hα.1.1, Finset.sum_const_zero, add_zero] using
      replace_block_mass α b0 (fun _ => 0)
  rw [hmass] at hm
  have hn : 0 ≤ ∑ i, α i b0 := Finset.sum_nonneg (fun i _ => hα.1.2 i b0)
  linarith

/-- The active-set formulation of the zero-mass conclusion for unused blocks. -/
theorem optimal_inactive_mass_zero (α : Fin k → Fin B → ℝ)
    (hα : P.IsOptimal α) (b : Fin B) (he : active P b = ∅) :
    (∑ i, α i b) = 0 := by
  apply optimal_unused_parameter_mass_zero P α hα b
  intro i hi
  have hmem := (mem_active_iff_mem_Xi P i b).mpr hi
  simpa [he] using hmem

/-- In particular, an inactive parameter has zero allocation at its conditional best. -/
theorem optimal_inactive_best_zero (α : Fin k → Fin B → ℝ)
    (hα : P.IsOptimal α) (b : Fin B) (he : active P b = ∅) :
    α (P.ib b) b = 0 := by
  apply le_antisymm _ (hα.1.2 _ _)
  calc
    α (P.ib b) b ≤ ∑ i, α i b :=
      Finset.single_le_sum (fun i _ => hα.1.2 i b) (Finset.mem_univ _)
    _ = 0 := optimal_inactive_mass_zero P α hα b he

end MPBSelect.S10Necessity
end


-- Inlined module: Solutions.P066GlobalNecessity
section
namespace MPBSelect.S10GlobalNecessity

open scoped BigOperators
open S10Rates S10Coordinates S10ScalarCost S10OptimalCoordinates S10Reconstruct S10Necessity

noncomputable section

variable {k B : ℕ} (P : Problem k B)

/-- An optimal allocation minimizes the scalar budget function of each active
parameter block. Otherwise, replacing that block would preserve all target rates
with total mass below one. -/
theorem optimal_cost_min (α : Fin k → Fin B → ℝ) (hopt : P.IsOptimal α)
    (b : Fin B) (hactive : (active P b).Nonempty) :
    ∀ z : ℝ, (∀ i ∈ active P b,
      0 < coefficient P i b * z - variance P (P.ib b) b) →
      cost (active P b) (fun i => variance P i b) (variance P (P.ib b) b)
        (fun i => coefficient P i b) (α (P.ib b) b / P.ldr α) ≤
      cost (active P b) (fun i => variance P i b) (variance P (P.ib b) b)
        (fun i => coefficient P i b) z := by
  classical
  intro z hz
  let t : ℝ := P.ldr α
  have ht : 0 < t := optimal_ldr_pos P α hopt
  let β : Fin k → Fin B → ℝ := fun i b' =>
    if b' = b then reconstructBlock P b t z i else α i b'
  have hβnn : ∀ i b', 0 ≤ β i b' := by
    intro i b'
    dsimp only [β]
    split_ifs
    · exact reconstruct_nonneg P b t z ht hactive hz i
    · exact hopt.1.2 i b'
  have hcolumn : ∀ i, β i b = reconstructBlock P b t z i := by
    intro i
    simp only [β, if_pos rfl]
  have hr : ∀ x ∈ P.Xi, P.ldr α ≤ P.W x.1 x.2 * P.G β x.1 x.2 := by
    rintro ⟨i, b'⟩ hx
    by_cases hb : b' = b
    · subst b'
      have hi : i ∈ active P b := (mem_active_iff_mem_Xi P i b).mpr hx
      exact (reconstruct_rate P β b t z ht hz hcolumn i hi).symm.le
    · have hsame : P.G β i b' = P.G α i b' := by
        simp only [Problem.G, β, if_neg hb]
      rw [hsame]
      exact ldr_le P α (i, b') hx
  have hmass := optimal_mass_le P α hopt β hβnn hr
  have hmass_eq : (∑ i, ∑ b', β i b') =
      1 - t * cost (active P b) (fun i => variance P i b)
        (variance P (P.ib b) b) (fun i => coefficient P i b)
        (α (P.ib b) b / P.ldr α) +
      t * cost (active P b) (fun i => variance P i b)
        (variance P (P.ib b) b) (fun i => coefficient P i b) z := by
    dsimp only [β]
    rw [replace_block_mass α b (reconstructBlock P b t z), hopt.1.1,
      optimal_block_mass_eq_cost P α hopt b, reconstruct_mass P b t z]
  rw [hmass_eq] at hmass
  have hscaled :
      t * cost (active P b) (fun i => variance P i b)
        (variance P (P.ib b) b) (fun i => coefficient P i b)
        (α (P.ib b) b / P.ldr α) ≤
      t * cost (active P b) (fun i => variance P i b)
        (variance P (P.ib b) b) (fun i => coefficient P i b) z := by
    linarith
  exact le_of_mul_le_mul_left hscaled ht

/-- Global balance at a parameter with at least one active competitor follows
from scalar budget stationarity. -/
theorem optimal_global_balance_at_active (α : Fin k → Fin B → ℝ)
    (hopt : P.IsOptimal α) (b : Fin B) (hactive : (active P b).Nonempty) :
    α (P.ib b) b ^ 2 / variance P (P.ib b) b =
      ∑ i ∈ active P b, α i b ^ 2 / variance P i b := by
  have ht := optimal_ldr_pos P α hopt
  obtain ⟨i, hi⟩ := hactive
  have hy : 0 < α (P.ib b) b :=
    ((ldr_pos_iff P α).mp ht (i, b) ((mem_active_iff_mem_Xi P i b).mp hi)).2
  have hdata := optimal_normalized_data P α hopt b
  have hstationary := balance_of_cost_min (active P b)
    (fun i => variance P i b) (variance P (P.ib b) b) (fun i => coefficient P i b)
    (α (P.ib b) b / P.ldr α) hdata.1
    (optimal_cost_min P α hopt b ⟨i, hi⟩)
  exact (allocation_balance_iff (active P b)
    (fun i => variance P i b) (variance P (P.ib b) b) (fun i => coefficient P i b)
    (fun i => α i b) (α (P.ib b) b) (α (P.ib b) b / P.ldr α)
    (fun i _ => variance_pos P i b) (variance_pos P (P.ib b) b) hy
    hdata.1 hdata.2).mpr hstationary

/-- Every optimum satisfies global balance, including empty active blocks. -/
theorem optimal_global_balance (α : Fin k → Fin B → ℝ) (hopt : P.IsOptimal α) :
    P.GlobalBalance α := by
  intro b
  change α (P.ib b) b ^ 2 / variance P (P.ib b) b =
    ∑ i ∈ active P b, α i b ^ 2 / variance P i b
  by_cases hactive : (active P b).Nonempty
  · exact optimal_global_balance_at_active P α hopt b hactive
  · have hempty : active P b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hactive
    have hzero := optimal_inactive_best_zero P α hopt b hempty
    simp only [hempty, Finset.sum_empty, hzero, zero_pow (by decide : 2 ≠ 0), zero_div]

end

end MPBSelect.S10GlobalNecessity
end


-- Inlined module: Solutions.P066BalancedPositive
section
open scoped BigOperators
open Finset

namespace MPBSelect.S10Balance

variable {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ)

/-- A feasible balanced allocation cannot spend all its budget on zero-rate coordinates. -/
theorem exists_positive_rate
    (hα : α ∈ feasibleSet k B) (hG : P.GlobalBalance α) (hZ : P.ZeroRatio α) :
    ∃ x ∈ P.Xi, 0 < P.W x.1 x.2 * P.G α x.1 x.2 := by
  classical
  have hsum : (0 : ℝ) < ∑ i, ∑ b, α i b := by rw [hα.1]; norm_num
  have hex : ∃ i, 0 < ∑ b, α i b := by
    by_contra hn
    push Not at hn
    have hz := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hn i)
    linarith
  obtain ⟨i, hi⟩ := hex
  have hexb : ∃ b, 0 < α i b := by
    by_contra hn
    push Not at hn
    have hz := Finset.sum_nonpos (s := Finset.univ) (fun b _ => hn b)
    linarith
  obtain ⟨b, hib⟩ := hexb
  by_cases hibest : i = P.ib b
  · have hab : 0 < α (P.ib b) b := by simpa [hibest] using hib
    have hs : 0 < ∑ j ∈ univ.filter (fun j : Fin k => j ≠ P.ib b ∧ j ≠ P.istar),
        α j b ^ 2 / P.lam j b ^ 2 := by
      rw [← hG b]
      exact div_pos (sq_pos_of_pos hab) (sq_pos_of_pos (P.lam_pos _ _))
    have hexj : ∃ j ∈ univ.filter (fun j : Fin k => j ≠ P.ib b ∧ j ≠ P.istar),
        0 < α j b ^ 2 / P.lam j b ^ 2 := by
      by_contra hn
      push Not at hn
      have hz := Finset.sum_nonpos hn
      linarith
    obtain ⟨j, hj, hjpos⟩ := hexj
    have hjmem := (Finset.mem_filter.mp hj).2
    have haj : 0 < α j b := by
      by_contra hn
      have hz : α j b = 0 := le_antisymm (le_of_not_gt hn) (hα.2 j b)
      simp [hz] at hjpos
    refine ⟨(j, b), ?_, ?_⟩
    · simpa [Problem.Xi] using And.intro hjmem.2 hjmem.1
    · exact mul_pos (S10Rates.W_pos P j b)
        ((S10Rates.G_pos_iff P α j b hjmem.1).mpr ⟨haj, hab⟩)
  · have histar : i ≠ P.istar := by
      intro heq
      subst i
      exact (ne_of_gt hib) (hZ b (Ne.symm hibest))
    have himem : i ∈ univ.filter (fun j : Fin k => j ≠ P.ib b ∧ j ≠ P.istar) := by
      simp [hibest, histar]
    have hterm : 0 < α i b ^ 2 / P.lam i b ^ 2 :=
      div_pos (sq_pos_of_pos hib) (sq_pos_of_pos (P.lam_pos _ _))
    have hbestterm : 0 < α (P.ib b) b ^ 2 / P.lam (P.ib b) b ^ 2 := by
      rw [hG b]
      exact lt_of_lt_of_le hterm (Finset.single_le_sum
        (f := fun j : Fin k => α j b ^ 2 / P.lam j b ^ 2)
        (fun j _ => div_nonneg (sq_nonneg (α j b)) (sq_nonneg (P.lam j b))) himem)
    have hab : 0 < α (P.ib b) b := by
      by_contra hn
      have hz : α (P.ib b) b = 0 := le_antisymm (le_of_not_gt hn) (hα.2 _ _)
      simp [hz] at hbestterm
    refine ⟨(i, b), ?_, ?_⟩
    · simp [Problem.Xi, histar, hibest]
    · exact mul_pos (S10Rates.W_pos P i b)
        ((S10Rates.G_pos_iff P α i b hibest).mpr ⟨hib, hab⟩)

/-- All active coordinates are positive under the three balance conditions. -/
theorem active_positive
    (hα : α ∈ feasibleSet k B) (hG : P.GlobalBalance α)
    (hP : P.PairwiseBalance α) (hZ : P.ZeroRatio α) :
    ∀ x ∈ P.Xi, 0 < α x.1 x.2 ∧ 0 < α (P.ib x.2) x.2 := by
  obtain ⟨y, hy, hypos⟩ := exists_positive_rate P α hα hG hZ
  intro x hx
  have hxpos : 0 < P.W x.1 x.2 * P.G α x.1 x.2 := by
    rw [hP x hx y hy]
    exact hypos
  have hGpos : 0 < P.G α x.1 x.2 :=
    (mul_pos_iff_of_pos_left (S10Rates.W_pos P _ _)).mp hxpos
  have hxi : x.1 ≠ P.ib x.2 := by
    have hx' : x.1 ≠ P.istar ∧ x.1 ≠ P.ib x.2 := by
      simpa only [Problem.Xi, mem_filter, mem_univ, true_and] using hx
    exact hx'.2
  exact (S10Rates.G_pos_iff P α _ _ hxi).mp hGpos


end MPBSelect.S10Balance
end


-- Inlined module: Solutions.P066Sufficiency
section
namespace MPBSelect.S10Sufficiency

open S10ScalarCost

/-- At equal rates, global balance gives the least budget in each parameter block. -/
theorem normalized_mass_compare {ι : Type*} (I : Finset ι)
    (A : ι → ℝ) (B : ℝ) (C x x' : ι → ℝ) (y y' t s : ℝ)
    (hA : ∀ i ∈ I, 0 < A i) (hB : 0 < B) (hC : ∀ i ∈ I, 0 < C i)
    (ht : 0 < t) (hs : 0 < s) (hy : 0 < y) (hy' : 0 < y')
    (hx : ∀ i ∈ I, 0 < x i) (hx' : ∀ i ∈ I, 0 < x' i)
    (heq : ∀ i ∈ I, t * (A i * y + B * x i) = C i * x i * y)
    (hle : ∀ i ∈ I, s * (A i * y' + B * x' i) ≤ C i * x' i * y')
    (hbalance : y ^ 2 / B = ∑ i ∈ I, x i ^ 2 / A i) :
    s * (y + ∑ i ∈ I, x i) ≤ t * (y' + ∑ i ∈ I, x' i) := by
  have hnorm := fun i hi => normalized_rate (A i) B (C i) t (x i) y
    (hA i hi) ht (hx i hi) hy (heq i hi)
  have hnorm' := fun i hi => normalized_rate_lower_bound (A i) B (C i) s (x' i) y'
    (hA i hi) hs (hx' i hi) hy' (hle i hi)
  have hstationary := (allocation_balance_iff I A B C x y (y / t) hA hB hy
    (fun i hi => (hnorm i hi).1) (fun i hi => (hnorm i hi).2)).mp hbalance
  have hcost := cost_min_of_balance I A B C (y / t) hA hB hC
    (fun i hi => (hnorm i hi).1) hstationary (y' / s)
    (fun i hi => (hnorm' i hi).1)
  have hy_eq : y = t * (y / t) := by field_simp [ne_of_gt ht]
  have hy'_eq : y' = s * (y' / s) := by field_simp [ne_of_gt hs]
  have hmass := allocation_mass_eq_cost I A B C x t y (y / t) hy_eq
    (fun i hi => (hnorm i hi).2)
  have hmass' := scaled_cost_le_allocation_mass I A B C x' s y' (y' / s) hy'_eq
    (fun i hi => (hnorm' i hi).2)
  calc
    s * (y + ∑ i ∈ I, x i) = t * (s * cost I A B C (y / t)) := by rw [hmass]; ring
    _ ≤ t * (s * cost I A B C (y' / s)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcost hs.le) ht.le
    _ ≤ t * (y' + ∑ i ∈ I, x' i) := mul_le_mul_of_nonneg_left hmass' ht.le

variable {k B : ℕ} (P : Problem k B)

/-- Pairwise balance identifies every active rate with the minimum objective. -/
theorem rate_eq_ldr (α : Fin k → Fin B → ℝ) (hP : P.PairwiseBalance α)
    (x : Fin k × Fin B) (hx : x ∈ P.Xi) :
    P.W x.1 x.2 * P.G α x.1 x.2 = P.ldr α := by
  obtain ⟨z, hz, heq⟩ := Finset.exists_mem_eq_inf' P.Xi_nonempty
    (fun z => P.W z.1 z.2 * P.G α z.1 z.2)
  exact (hP x hx z hz).trans heq.symm

/-- The three conditions give a feasible allocation with maximal minimum rate. -/
theorem balanced_isOptimal (α : Fin k → Fin B → ℝ)
    (hα : α ∈ feasibleSet k B) (hG : P.GlobalBalance α)
    (hP : P.PairwiseBalance α) (hZ : P.ZeroRatio α) : P.IsOptimal α := by
  classical
  refine ⟨hα, ?_⟩
  intro β hβ
  have hapos := S10Balance.active_positive P α hα hG hP hZ
  have ht : 0 < P.ldr α := (S10Rates.ldr_pos_iff P α).mpr hapos
  by_contra hnot
  have hst : P.ldr α < P.ldr β := lt_of_not_ge hnot
  have hs : 0 < P.ldr β := ht.trans hst
  have hbpos := (S10Rates.ldr_pos_iff P β).mp hs
  have hblock : ∀ b : Fin B,
      P.ldr β * (∑ i, α i b) ≤ P.ldr α * (∑ i, β i b) := by
    intro b
    by_cases hI : (S10Coordinates.active P b).Nonempty
    · obtain ⟨i0, hi0⟩ := hI
      have hx0 := (S10Coordinates.mem_active_iff_mem_Xi P i0 b).mp hi0
      have hy := (hapos (i0, b) hx0).2
      have hy' := (hbpos (i0, b) hx0).2
      have hx : ∀ i ∈ S10Coordinates.active P b, 0 < α i b := by
        intro i hi
        exact (hapos (i, b) ((S10Coordinates.mem_active_iff_mem_Xi P i b).mp hi)).1
      have hx' : ∀ i ∈ S10Coordinates.active P b, 0 < β i b := by
        intro i hi
        exact (hbpos (i, b) ((S10Coordinates.mem_active_iff_mem_Xi P i b).mp hi)).1
      have heq : ∀ i ∈ S10Coordinates.active P b,
          P.ldr α * (S10Coordinates.variance P i b * α (P.ib b) b +
            S10Coordinates.variance P (P.ib b) b * α i b) =
          S10Coordinates.coefficient P i b * α i b * α (P.ib b) b := by
        intro i hi
        apply (S10Coordinates.target_eq_rate_iff P α i b (P.ldr α) (hx i hi) hy).mp
        exact (rate_eq_ldr P α hP (i, b)
          ((S10Coordinates.mem_active_iff_mem_Xi P i b).mp hi)).symm
      have hle : ∀ i ∈ S10Coordinates.active P b,
          P.ldr β * (S10Coordinates.variance P i b * β (P.ib b) b +
            S10Coordinates.variance P (P.ib b) b * β i b) ≤
          S10Coordinates.coefficient P i b * β i b * β (P.ib b) b := by
        intro i hi
        apply (S10Coordinates.target_le_rate_iff P β i b (P.ldr β) (hx' i hi) hy').mp
        exact S10Rates.ldr_le P β (i, b)
          ((S10Coordinates.mem_active_iff_mem_Xi P i b).mp hi)
      have hbalance : α (P.ib b) b ^ 2 / S10Coordinates.variance P (P.ib b) b =
          ∑ i ∈ S10Coordinates.active P b, α i b ^ 2 / S10Coordinates.variance P i b :=
        hG b
      have hcomp := normalized_mass_compare (S10Coordinates.active P b)
        (fun i => S10Coordinates.variance P i b) (S10Coordinates.variance P (P.ib b) b)
        (fun i => S10Coordinates.coefficient P i b) (fun i => α i b) (fun i => β i b)
        (α (P.ib b) b) (β (P.ib b) b) (P.ldr α) (P.ldr β)
        (fun i _ => S10Coordinates.variance_pos P i b)
        (S10Coordinates.variance_pos P (P.ib b) b)
        (fun i hi => S10Coordinates.coefficient_pos P i b hi)
        ht hs hy hy' hx hx' heq hle hbalance
      rw [← S10Coordinates.block_mass P α hZ b] at hcomp
      exact hcomp.trans (mul_le_mul_of_nonneg_left
        (S10Coordinates.block_mass_le P β hβ.2 b) ht.le)
    · have hempty : S10Coordinates.active P b = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hI
      rw [S10Coordinates.block_mass_zero_of_active_empty P α hG hZ b hempty, mul_zero]
      exact mul_nonneg ht.le (Finset.sum_nonneg (fun i _ => hβ.2 i b))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hblock b)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hasum : (∑ b, ∑ i, α i b) = 1 := by rw [Finset.sum_comm]; exact hα.1
  have hbsum : (∑ b, ∑ i, β i b) = 1 := by rw [Finset.sum_comm]; exact hβ.1
  rw [hasum, hbsum, mul_one, mul_one] at hsum
  exact (not_le_of_gt hst) hsum

end MPBSelect.S10Sufficiency
end


open MPBSelect

/-- The original full root, with all quantifiers and boundary cases unchanged. -/
theorem solution {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ)
    (hα : α ∈ feasibleSet k B) :
    P.IsOptimal α ↔ P.GlobalBalance α ∧ P.PairwiseBalance α ∧ P.ZeroRatio α := by
  constructor
  · intro hopt
    exact ⟨S10GlobalNecessity.optimal_global_balance P α hopt,
      S10Necessity.optimal_pairwise_balance P α hopt,
      S10Rates.optimal_zero_ratio P α hopt⟩
  · rintro ⟨hG, hP, hZ⟩
    exact S10Sufficiency.balanced_isOptimal P α hα hG hP hZ

#print axioms solution
