-- Prove2me | solution 1 for GlobalTheory.form_matrixUnits_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:57:38.216442+00:00
-- url     : https://prove2.me/submissions/9c1b2f68-9361-493c-9e4a-50cbb1cffe5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnimodularSymplecticCoordinatesAndLatticeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSiegelForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivPiRangeOfMatrixUnits
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {La : Type} [AddCommGroup La] (G : Matrix (Fin 8) (Fin 8) ℤ)
    (EF : LinearMap.BilinForm ℤ La) (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La)
    (hdet : G.det = 1)
    (hadj : ∀ a a', a.transpose * G = G * a' → ∀ x y, EF (r a x) y = EF x (r a' y)) (u v : Fin 8)
    (x y : La) : EF (r (Matrix.single u 0 1) x) (r (Matrix.single v 0 1) y) =
      G u v * EF x (r (G⁻¹ * Matrix.single 0 0 1) y) := by
  have hu : IsUnit G.det := by simp [hdet]
  rw [hadj _ (G⁻¹ * ((Matrix.single u 0 1).transpose * G))
    (by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]),
    ← Module.End.mul_apply, ← map_mul]
  have : G⁻¹ * ((Matrix.single u (0 : Fin 8) (1:ℤ)).transpose * G) * Matrix.single v (0 : Fin 8) (1:ℤ) =
      G u v • (G⁻¹ * Matrix.single 0 0 1) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_smul, Matrix.transpose_single, Matrix.single_mul_mul_single]
    simp
  rw [this, map_zsmul]
  simp
end GlobalTheory
