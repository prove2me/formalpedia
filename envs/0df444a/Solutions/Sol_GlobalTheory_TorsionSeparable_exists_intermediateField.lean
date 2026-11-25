-- Prove2me | solution 1 for GlobalTheory.TorsionSeparable.exists_intermediateField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:46.776523+00:00
-- url     : https://prove2.me/submissions/fe8a622e-c03e-4d61-81b8-6c57f156f8ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteSeparablePoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntermediateFieldOfPowEqOne
import Theorems.Thm_GlobalTheory_FiniteSeparablePoints_exists_finite_separable_point
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionSeparable
namespace GlobalTheory.TorsionSeparable
theorem _root_.solution {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) [FormallyUnramified p] [LocallyOfFiniteType p]
    (a : Spec (CommRingCat.of Ω) ⟶ X)
    (ha : a ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :
    ∃ K : IntermediateField k Ω, FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
      ∃ b : Spec (CommRingCat.of K) ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ b = a := by
  first
  | (rename_i h_2 h_3 h_4 h_7 h_8; revert k Ω h_2 h_3 h_4 X p h_7 h_8 a ha; exact @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point)
  | exact @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point
  | exact _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point
  | (apply _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteSeparablePoints.exists_finite_separable_point ..)
end GlobalTheory.TorsionSeparable
