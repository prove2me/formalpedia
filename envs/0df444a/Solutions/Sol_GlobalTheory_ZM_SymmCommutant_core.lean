-- Prove2me | solution 1 for GlobalTheory.ZM.SymmCommutant.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:53.229321+00:00
-- url     : https://prove2.me/submissions/7ccccaf9-1333-44b1-9b8d-f814134f12f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FinrankSymmCommutantKroneckerLe
import Theorems.Thm_GlobalTheory_ZM_SymmCommutant_entry_of_commute

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.SymmCommutant
open Matrix
namespace GlobalTheory.ZM.SymmCommutant
theorem _root_.solution {K : Type} [Field K] {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) K)
    (hA : A.IsSymm) (hBA : B * A = 1)
    (Θ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K) (hΘ : Θ.IsSymm)
    (H : ∀ v : Fin 8, Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) * Θ =
      Θ * (Matrix.kronecker (B * (Matrix.single (0 : Fin 8) v (1 : K)).transpose * A)
        (1 : Matrix (Fin h) (Fin h) K)).transpose) :
    (∀ a b i j, Θ (a, i) (b, j) =
      B a b * (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, i) (0, j)) ∧
    ∀ i j, (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, i) (0, j) =
      (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, j) (0, i) := by
  have hAB : A * B = 1 := mul_eq_one_comm.mp hBA
  have hBtA : Bᵀ * A = 1 := by
    have : (Aᵀ * B)ᵀ = 1 := by rw [hA.eq, hAB, Matrix.transpose_one]
    simpa [Matrix.transpose_mul] using this
  have kmul : ∀ X Y : Matrix (Fin 8) (Fin 8) K,
      Matrix.kronecker X (1 : Matrix (Fin h) (Fin h) K) *
        Matrix.kronecker Y (1 : Matrix (Fin h) (Fin h) K) =
      Matrix.kronecker (X * Y) (1 : Matrix (Fin h) (Fin h) K) := by
    intro X Y
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have ktr : ∀ X : Matrix (Fin 8) (Fin 8) K,
      (Matrix.kronecker X (1 : Matrix (Fin h) (Fin h) K))ᵀ =
      Matrix.kronecker Xᵀ (1 : Matrix (Fin h) (Fin h) K) := by
    intro X
    simp only [Matrix.kronecker]
    rw [← Matrix.kroneckerMap_transpose, Matrix.transpose_one]
  set Ψ := Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K) with hΨ
  have hc : ∀ v : Fin 8, Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) * Ψ =
      Ψ * Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) := by
    intro v
    rw [hΨ, ← Matrix.mul_assoc, H v, ktr, Matrix.mul_assoc, Matrix.mul_assoc Θ, kmul, kmul]
    congr 2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq,
      Matrix.mul_assoc, Matrix.mul_assoc, hBtA, Matrix.mul_one]
  have he := entry_of_commute Ψ hc
  have hΘΨ : Θ = Ψ * Matrix.kronecker B (1 : Matrix (Fin h) (Fin h) K) := by
    rw [hΨ, Matrix.mul_assoc, kmul, hAB]
    simp [Matrix.kronecker]
  have h1 : ∀ a b i j, Θ (a, i) (b, j) = B a b * Ψ (0, i) (0, j) := by
    intro a b i j
    have := congrFun (congrFun hΘΨ (a, i)) (b, j)
    rw [this, Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [he a]
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, mul_comm]
  refine ⟨h1, fun i j => ?_⟩
  have h00 : ∑ b, A 0 b * B b 0 = 1 := by
    have := congrFun (congrFun hAB 0) 0
    simpa [Matrix.mul_apply] using this
  calc Ψ (0, i) (0, j) = ∑ b, Θ (0, i) (b, j) * A b 0 := by
        rw [hΨ, Matrix.mul_apply, Fintype.sum_prod_type]
        simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
    _ = ∑ b, (A 0 b * B b 0) * Ψ (0, j) (0, i) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← hΘ.apply (0, i) (b, j), h1, hA.apply b 0]
        ring
    _ = Ψ (0, j) (0, i) := by rw [← Finset.sum_mul, h00, _root_.one_mul]
end GlobalTheory.ZM.SymmCommutant
