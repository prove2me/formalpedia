-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatrixLie.entry_hasDerivAt_exp_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:10:46.700797+00:00
-- url     : https://prove2.me/submissions/685437c2-c91a-43d8-abe8-c4069719d940

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurveStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtExpMulExpOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_MatrixLie_hasDerivAt_exp_mul_exp_of_finiteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace GlobalTheory.CompanionTheory.MatrixLie
private theorem hasDerivAt_zero_linear_exp_smul_mul_exp_smul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [FiniteDimensional ℝ A] (X Y : A) (ℓ : A →ₗ[ℝ] ℂ) :
    HasDerivAt (fun t : ℝ => ℓ (NormedSpace.exp (t • X) * NormedSpace.exp (t • Y))) (ℓ (X + Y)) 0 :=
  (LinearMap.toContinuousLinearMap ℓ).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_mul_exp_of_finiteDimensional X Y)
end GlobalTheory.CompanionTheory.MatrixLie
end
end

set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatrixLie
namespace GlobalTheory.CompanionTheory.MatrixLie
theorem _root_.solution {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ =>
      (NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y)) i j) ((X + Y) i j) 0 := by
  have hs : ∀ (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ), ((t : ℂ) • Z) = t • Z := by
    intro t Z
    ext a b
    simp [Complex.real_smul]
  simp only [hs]
  exact @hasDerivAt_zero_linear_exp_smul_mul_exp_smul (Matrix (Fin n) (Fin n) ℂ) Matrix.linftyOpNormedRing
    Matrix.linftyOpNormedAlgebra inferInstance X Y
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
end GlobalTheory.CompanionTheory.MatrixLie
