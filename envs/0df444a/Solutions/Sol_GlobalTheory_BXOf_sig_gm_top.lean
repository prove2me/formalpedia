-- Prove2me | solution 1 for GlobalTheory.BXOf.sig_gm_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:14:31.814805+00:00
-- url     : https://prove2.me/submissions/3bbcd817-9114-4ae0-9d89-a9cf83ee290f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawCommutativityValue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val


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
noncomputable section
open GlobalTheory GlobalTheory.BXOf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {X Y : Scheme.{0}}
namespace GlobalTheory.BXOf
theorem _root_.solution (f : R →+* S) (a : Γ(Spec (CommRingCat.of R), ⊤)ˣ) :
    (sig S (gm (Spec.map (CommRingCat.ofHom f)) (closedPoint S) ⊤ a)).val =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a.val) := by
  have e1 := congrArg (fun q => q.hom (((Spec.map (CommRingCat.ofHom f)).app ⊤).hom a.val))
    (germ_stalkClosedPointIso_hom (CommRingCat.of S))
  have e2 := congrArg (fun q => q.hom a.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  refine Eq.trans ?_ (e1.trans e2)
  exact congrArg (stalkClosedPointIso (CommRingCat.of S)).hom.hom (gm_val _ _ ⊤ trivial a)
end GlobalTheory.BXOf
