-- Prove2me | solution 1 for NonAbelianDMNRG.Recursion.eq_39_41_42
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:38:30.069122+00:00
-- url     : https://prove2.me/submissions/f425a784-5ae2-4db1-a839-8ef4f3be6eb0

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_NonAbelianDMNRG_Recursion_Multiplets
open Matrix
open scoped Kronecker

namespace Aux_NADMeq39
open NonAbelianDMNRG.Recursion

lemma key {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (A : Matrix a a ℂ) (B : Matrix b b ℂ) (hB : Bᴴ * B = 1) (R : Matrix (a × b) (a × b) ℂ) :
    WildeQIT.partialTraceRight ((A ⊗ₖ B) * R * (A ⊗ₖ B)ᴴ) =
      A * WildeQIT.partialTraceRight R * Aᴴ := by
  have hBe : ∀ q q' : b, ∑ k, star (B k q') * B k q = if q' = q then 1 else 0 := by
    intro q q'
    have := congrFun (congrFun hB q') q
    simpa [mul_apply, conjTranspose_apply, one_apply] using this
  ext i j
  simp only [WildeQIT.partialTraceRight, of_apply, mul_apply, kroneckerMap_apply,
    conjTranspose_apply, star_mul', Finset.sum_mul]
  calc ∑ k, ∑ y : a × b, ∑ x : a × b,
        A i x.1 * B k x.2 * R x y * (star (A j y.1) * star (B k y.2))
      = ∑ x : a × b, ∑ y : a × b,
          A i x.1 * R x y * star (A j y.1) * ∑ k, star (B k y.2) * B k x.2 := by
        rw [Finset.sum_comm]
        rw [Finset.sum_congr rfl (fun y _ => Finset.sum_comm)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        ring
    _ = ∑ x : a × b, ∑ y : a × b,
          A i x.1 * R x y * star (A j y.1) * (if y.2 = x.2 then 1 else 0) := by
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        rw [hBe]
    _ = ∑ x : a × b, ∑ y1 : a, A i x.1 * R x (y1, x.2) * star (A j y1) := by
        apply Finset.sum_congr rfl; intro x _
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl; intro y1 _
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq']
        simp
    _ = ∑ y1 : a, ∑ p : a, (A i p * ∑ q : b, R (p, q) (y1, q)) * star (A j y1) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_congr rfl (fun p _ => Finset.sum_comm)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro y1 _
        apply Finset.sum_congr rfl; intro p _
        rw [Finset.mul_sum, Finset.sum_mul]

lemma rep_unitary {G : Type} [Group G] {Lab : Type} {I : Type} [Fintype I] [DecidableEq I]
    (dim : Lab → ℕ) (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ) (Qi : I → Lab)
    (g : G) : (multipletRep dim π Qi g)ᴴ * multipletRep dim π Qi g = 1 := by
  unfold multipletRep
  rw [blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
  have : ∀ i, (π (Qi i) g : Matrix (Fin (dim (Qi i))) (Fin (dim (Qi i))) ℂ)ᴴ *
      (π (Qi i) g : Matrix (Fin (dim (Qi i))) (Fin (dim (Qi i))) ℂ) = 1 := by
    intro i
    exact Unitary.star_mul_self_of_mem (π (Qi i) g).2
  simp only [this]
  exact blockDiagonal'_one

lemma rep_unitary' {G : Type} [Group G] {Lab : Type} {I : Type} [Fintype I] [DecidableEq I]
    (dim : Lab → ℕ) (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ) (Qi : I → Lab)
    (g : G) : multipletRep dim π Qi g * (multipletRep dim π Qi g)ᴴ = 1 := by
  unfold multipletRep
  rw [blockDiagonal'_conjTranspose, ← blockDiagonal'_mul]
  have : ∀ i, (π (Qi i) g : Matrix (Fin (dim (Qi i))) (Fin (dim (Qi i))) ℂ) *
      (π (Qi i) g : Matrix (Fin (dim (Qi i))) (Fin (dim (Qi i))) ℂ)ᴴ = 1 := by
    intro i
    exact Unitary.mul_star_self_of_mem (π (Qi i) g).2
  simp only [this]
  exact blockDiagonal'_one

end Aux_NADMeq39

open NonAbelianDMNRG.Recursion Aux_NADMeq39 in
theorem solution {G : Type} [Group G] {Lab : Type} (dim : Lab → ℕ)
    (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ)
    {K Λ D : Type} [Fintype K] [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
    [Fintype D] [DecidableEq D]
    (Qu : K → Lab) (ql : Λ → Lab) (Qd : D → Lab) (w : D → ℝ)
    (R : Matrix (Multiplets dim Qu × Multiplets dim ql) (Multiplets dim Qu × Multiplets dim ql) ℂ)
    (hR : ∀ g : G, newRep dim π Qu ql g * R * (newRep dim π Qu ql g)ᴴ = R) :
    (∀ g : G, multipletRep dim π Qu g * WildeQIT.partialTraceRight R *
        (multipletRep dim π Qu g)ᴴ = WildeQIT.partialTraceRight R) ∧
    (∀ g : G, prevRep dim π Qd Qu g *
        truncatedOperator dim Qd Qu w (WildeQIT.partialTraceRight R) * (prevRep dim π Qd Qu g)ᴴ =
        truncatedOperator dim Qd Qu w (WildeQIT.partialTraceRight R)) := by
  have part1 : ∀ g : G, multipletRep dim π Qu g * WildeQIT.partialTraceRight R *
      (multipletRep dim π Qu g)ᴴ = WildeQIT.partialTraceRight R := by
    intro g
    rw [← key _ _ (rep_unitary dim π ql g) R]
    exact congrArg WildeQIT.partialTraceRight (hR g)
  refine ⟨part1, ?_⟩
  intro g
  unfold prevRep truncatedOperator
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, conjTranspose_zero]
  rw [part1 g]
  congr 1
  unfold multipletRep
  rw [blockDiagonal'_conjTranspose, ← blockDiagonal'_mul, ← blockDiagonal'_mul]
  congr 1
  funext d
  have hu : (π (Qd d) g : Matrix (Fin (dim (Qd d))) (Fin (dim (Qd d))) ℂ) *
      (π (Qd d) g : Matrix (Fin (dim (Qd d))) (Fin (dim (Qd d))) ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem (π (Qd d) g).2
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hu]
