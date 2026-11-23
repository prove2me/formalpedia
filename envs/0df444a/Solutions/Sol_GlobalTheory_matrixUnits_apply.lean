-- Prove2me | solution 1 for GlobalTheory.matrixUnits_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:38.089667+00:00
-- url     : https://prove2.me/submissions/1e25e29c-6a40-471c-9136-bf395205141a

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
theorem _root_.solution {La : Type} [AddCommGroup La]
    (r : Matrix (Fin 8) (Fin 8) ℤ →+* Module.End ℤ La) :
    (∀ u v x, r (Matrix.single 0 u 1) (r (Matrix.single v 0 1) x) =
      if u = v then r (Matrix.single 0 0 1) x else 0) ∧
    (∀ x, ∑ u, r (Matrix.single u 0 1) (r (Matrix.single 0 u 1) x) = x) ∧
    (∀ x, r (Matrix.single 0 0 1) (r (Matrix.single 0 0 1) x) = r (Matrix.single 0 0 1) x) := by
  refine ⟨fun u v x => ?_, fun x => ?_, fun x => ?_⟩
  · rw [← Module.End.mul_apply, ← map_mul]
    split_ifs with huv
    · subst huv; simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ huv]; simp
  · have : (∑ u : Fin 8, Matrix.single u 0 (1:ℤ) * Matrix.single (0 : Fin 8) u (1:ℤ)) = 1 := by
      ext i j
      simp only [Matrix.single_mul_single_same, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, mul_one]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij]
        refine Finset.sum_eq_zero fun u _ => if_neg ?_
        rintro ⟨rfl, rfl⟩; exact hij rfl
    simp only [← Module.End.mul_apply, ← map_mul]
    rw [← LinearMap.sum_apply, ← map_sum, this]; simp
  · rw [← Module.End.mul_apply, ← map_mul]; simp
end GlobalTheory
