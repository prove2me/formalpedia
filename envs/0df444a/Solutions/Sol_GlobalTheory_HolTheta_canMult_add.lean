-- Prove2me | solution 1 for GlobalTheory.HolTheta.canMult_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:25:38.826016+00:00
-- url     : https://prove2.me/submissions/be6a2b60-8229-44d0-aeda-6ab4fb904f80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsThetaHolomorphic
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.HolTheta
open Matrix GlobalTheory.CanTh GlobalTheory.RiemannRel
variable {g : ℕ}
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
open Matrix
variable {g : ℕ}
namespace GlobalTheory.HolTheta
namespace _root_.GlobalTheory.HolTheta
theorem _root_.solution (a c : Fin g → ℝ) (m n m' n' : Fin g → ℤ) :
    _root_.GlobalTheory.CanTh.canMult a c (m + m') (n + n') = _root_.GlobalTheory.CanTh.canMult a c m n * _root_.GlobalTheory.CanTh.canMult a c m' n' * (-1) ^ (n ⬝ᵥ m' - m ⬝ᵥ n') := by
  have hneg : ∀ k : ℤ, ((-1 : ℂ)) ^ k = Complex.exp (k * (Real.pi * Complex.I)) := by
    intro k; rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  unfold _root_.GlobalTheory.CanTh.canMult
  rw [hneg, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m ⬝ᵥ n', ?_⟩
  have h1 : (fun i => ((m + m') i : ℝ)) = (fun i => (m i : ℝ)) + fun i => (m' i : ℝ) := by
    ext i; simp
  have h2 : (fun i => ((n + n') i : ℝ)) = (fun i => (n i : ℝ)) + fun i => (n' i : ℝ) := by
    ext i; simp
  simp only [h1, h2, dotProduct_add, add_dotProduct, dotProduct_comm n m']
  push_cast
  ring
end _root_.GlobalTheory.HolTheta
end GlobalTheory.HolTheta
