-- Prove2me | solution 1 for GlobalTheory.bxFibre_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:43:45.503826+00:00
-- url     : https://prove2.me/submissions/0c68862b-772e-4199-934b-86c92c4e033c

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsFibreProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y : Scheme.{0}} {P Q : Type} [CommRing P] [IsLocalRing P] [CommRing Q]
    [IsLocalRing Q] (f : P →+* Q) [IsLocalHom f] (x : Spec (CommRingCat.of P) ⟶ Y) :
    (Spec.map (CommRingCat.ofHom f) ≫ x) (closedPoint Q) = x (closedPoint P) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg (fun y => x y) ?_)
  exact IsLocalRing.comap_closedPoint f
end GlobalTheory
