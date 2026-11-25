-- Prove2me | solution 1 for GlobalTheory.adjProd_ulift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:06:55.324811+00:00
-- url     : https://prove2.me/submissions/e395672f-d17f-481c-8c61-aac8cb10488c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GrpPullbackSquareProductLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {σ : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G σ φ)
namespace GlobalTheory
theorem _root_.solution {U : Type} [CommGroup U] (g : ULift.{0} (Fin 3) → U) :
    ∏ i, g i ^ lawε i = g ⟨0⟩ * (g ⟨1⟩)⁻¹ * (g ⟨2⟩)⁻¹ := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Fin 3) ≃ Fin 3) _ (fun i => g ⟨i⟩ ^ lawε ⟨i⟩)
    (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (-1 : ℤ) = _
  rw [zpow_one, zpow_neg_one, zpow_neg_one]
end GlobalTheory
