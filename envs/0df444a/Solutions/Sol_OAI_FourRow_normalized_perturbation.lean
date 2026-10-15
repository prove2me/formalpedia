-- Prove2me | solution 1 for OAI.FourRow.normalized_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:58:18.334586+00:00
-- url     : https://prove2.me/submissions/7f20e770-ef98-4fc7-82a0-bb8b3a12a798

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Permanent/Perturbation.lean:L79-L119
-- (upload_full_project.md Phase 4): solution for node OAI.FourRow.normalized_perturbation. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_FourRowPermanent
import Definitions.Def_OAI_Combinatorics_Permanent_Stability

-- ---- inline helpers from OAI.Combinatorics.Permanent.Stability ----
namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

/- Quantitative exponent-two stability estimates. -/
theorem sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℝ) :
    ∑ σ, f σ = ∑ i : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (i, τ)) := by
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm f]
  exact Fintype.sum_prod_type _

theorem decompose4_two (i : Fin 4) (e : Equiv.Perm (Fin 3)) :
    Equiv.Perm.decomposeFin.symm (i, e) 2 = Equiv.swap 0 i (e 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e i 1

theorem decompose4_three (i : Fin 4) (e : Equiv.Perm (Fin 3)) :
    Equiv.Perm.decomposeFin.symm (i, e) 3 = Equiv.swap 0 i (e 2).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e i 2

theorem decompose3_two (i : Fin 3) (e : Equiv.Perm (Fin 2)) :
    Equiv.Perm.decomposeFin.symm (i, e) 2 = Equiv.swap 0 i (e 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e i 1

end FourRow
end

end OAI

-- ---- inline helpers from OAI.Combinatorics.Permanent.Norm ----
namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

/- Below-two control by the tangent bound for the exponential. -/
theorem normalized_entry_le (a : Site → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hq : rowSq a = 4) (j : Site) : a j ≤ 2 := by
  have h : a j ^ 2 ≤ 4 := by
    calc
      a j ^ 2 ≤ rowSq a :=
        Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ j)
      _ = 4 := hq
  exact (sq_le_sq₀ (ha j) (by norm_num : (0 : ℝ) ≤ 2)).mp (by norm_num; exact h)

end FourRow
end

end OAI

-- ---- inline helpers from OAI.Combinatorics.Permanent.Perturbation ----
namespace OAI

noncomputable section
namespace FourRow
open scoped BigOperators

/- Exact marginal cancellation controls all perturbations quadratically. -/
theorem abs_mul_le_half_sq (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (a + b)]
  · nlinarith [sq_nonneg (a - b)]

theorem pair_shift_sq_le (a b : ℝ) (hb0 : 0 ≤ 1 + b) (hb2 : 1 + b ≤ 2) :
    (a * (1 + b) + b) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2) := by
  have hb : (1 + b) ^ 2 ≤ 4 := by nlinarith
  nlinarith [sq_nonneg (a - b * (1 + b)),
    mul_nonneg (sq_nonneg a) (show 0 ≤ 4 - (1 + b) ^ 2 by linarith),
    mul_nonneg (sq_nonneg b) (show 0 ≤ 4 - (1 + b) ^ 2 by linarith)]

theorem product_remainder_bound (a : Site → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (ha2 : ∀ i, a i ≤ 2) :
    |(∏ i, a i) - 1 - ∑ i, (a i - 1)| ≤ 3 * ∑ i, (a i - 1) ^ 2 := by
  let g := fun i => a i - 1
  let A := g 0 * (1 + g 1) + g 1
  let B := g 2 * (1 + g 3) + g 3
  have hA : A ^ 2 ≤ 5 * (g 0 ^ 2 + g 1 ^ 2) :=
    pair_shift_sq_le _ _ (by dsimp [g]; linarith [ha0 1])
      (by dsimp [g]; linarith [ha2 1])
  have hB : B ^ 2 ≤ 5 * (g 2 ^ 2 + g 3 ^ 2) :=
    pair_shift_sq_le _ _ (by dsimp [g]; linarith [ha0 3])
      (by dsimp [g]; linarith [ha2 3])
  have hid : (∏ i, a i) - 1 - ∑ i, (a i - 1) = g 0 * g 1 + g 2 * g 3 + A * B := by
    simp only [Fin.prod_univ_four, Fin.sum_univ_four]
    dsimp [A, B, g]
    ring
  rw [hid]
  have ht : |g 0 * g 1 + g 2 * g 3 + A * B| ≤
      |g 0 * g 1| + |g 2 * g 3| + |A * B| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
  have h1 := abs_mul_le_half_sq (g 0) (g 1)
  have h2 := abs_mul_le_half_sq (g 2) (g 3)
  have h3 := abs_mul_le_half_sq A B
  change _ ≤ 3 * ∑ i, g i ^ 2
  simp only [Fin.sum_univ_four]
  linarith

theorem uniform_probability : IsProbability uniformLaw := by
  constructor
  · intro π; norm_num [uniformLaw]
  · norm_num [uniformLaw, Fintype.card_perm, Site, Nat.factorial]

theorem uniform_marginals : UniformMarginals uniformLaw := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [uniformLaw, sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique] <;>
    simp [decompose4_two, decompose4_three, decompose3_two, Equiv.swap_apply_def] <;> norm_num

theorem marginal_average (ν : Law) (hν : UniformMarginals ν) (i : Site)
    (a : Site → ℝ) : (∑ π, ν π * a (π i)) = (∑ j, a j) / 4 := by
  have hrepr (π : Perm) : ν π * a (π i) = ∑ j, (if π i = j then ν π else 0) * a j := by
    simp
  simp_rw [hrepr]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hν i]
  rw [← Finset.mul_sum]
  ring

theorem law_linear_expectation (ν : Law) (hp : IsProbability ν)
    (hm : UniformMarginals ν) (f : Functions) :
    (∑ π, ν π * (1 + ∑ i, (f i (π i) - 1))) =
      1 + ∑ i, (∑ j, (f i j - 1)) / 4 := by
  simp_rw [mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hp.2, Finset.sum_comm]
  exact congrArg (fun x => 1 + x) (Finset.sum_congr rfl (fun i _ => marginal_average ν hm i (fun j => f i j - 1)))

end FourRow
end

end OAI

-- ---- hoisted node ----
open OAI OAI.FourRow
open scoped BigOperators

theorem solution (ν : Law) (hp : IsProbability ν)
    (hm : UniformMarginals ν) (f : Functions) (hf : ∀ i j, 0 ≤ f i j)
    (hn : ∀ i, rowSq (f i) = 4) :
    permanentExpectation ν f ≤ permanentExpectation uniformLaw f +
      6 * totalVariation ν * totalDist f := by
  let R : Perm → ℝ := fun π => (∏ i, f i (π i)) - 1 - ∑ i, (f i (π i) - 1)
  have hR (π : Perm) : |R π| ≤ 3 * totalDist f := by
    have hpoint := product_remainder_bound (fun i => f i (π i))
      (fun i => hf i (π i)) (fun i => normalized_entry_le (f i) (hf i) (hn i) (π i))
    apply hpoint.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j _ => sq_nonneg (f i j - 1)) (Finset.mem_univ _)
  have heq : permanentExpectation ν f - permanentExpectation uniformLaw f =
      ∑ π, (ν π - uniformLaw π) * R π := by
    have hν := law_linear_expectation ν hp hm f
    have hu := law_linear_expectation uniformLaw uniform_probability uniform_marginals f
    dsimp [permanentExpectation]
    dsimp [R]
    have hid (π : Perm) :
        (ν π - uniformLaw π) * ((∏ i, f i (π i)) - 1 - ∑ i, (f i (π i) - 1)) =
        ν π * (∏ i, f i (π i)) - uniformLaw π * (∏ i, f i (π i)) -
        (ν π * (1 + ∑ i, (f i (π i) - 1)) -
          uniformLaw π * (1 + ∑ i, (f i (π i) - 1))) := by ring
    simp_rw [hid]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hν, hu]
    ring
  have hbound : (∑ π, (ν π - uniformLaw π) * R π) ≤
      (∑ π, |ν π - uniformLaw π|) * (3 * totalDist f) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro π _
    calc
      _ ≤ |(ν π - uniformLaw π) * R π| := le_abs_self _
      _ = |ν π - uniformLaw π| * |R π| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hR π) (abs_nonneg _)
  rw [← heq] at hbound
  change _ ≤ _ + 6 * ((∑ π, |ν π - 1 / 24|) / 2) * totalDist f
  dsimp [uniformLaw] at hbound
  linarith
