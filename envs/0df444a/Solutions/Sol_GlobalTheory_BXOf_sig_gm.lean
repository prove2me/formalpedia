-- Prove2me | solution 1 for GlobalTheory.BXOf.sig_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:44:35.673266+00:00
-- url     : https://prove2.me/submissions/e3747549-b7ae-484a-a2cb-37f89a5d2442

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
import Theorems.Thm_GlobalTheory_BXOf_sig_gm_top
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
theorem _root_.solution (f : R →+* S) (r : Spec (CommRingCat.of R) ⟶ X) {U : X.Opens} (h : r (closedPoint R) ∈ U)
    (a : Γ(X, U)ˣ) :
    (sig S (gm (Spec.map (CommRingCat.ofHom f) ≫ r) (closedPoint S) U a)).val =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (res (top_le_of_mem r h) (pullU r U a)).val) := by
  rw [← sig_gm_top]
  exact congrArg (fun u => (sig S u).val)
    ((gm_res (Spec.map (CommRingCat.ofHom f)) (closedPoint S) (top_le_of_mem r h) trivial _).trans
      (gm_pull (Spec.map (CommRingCat.ofHom f)) r (closedPoint S) U (top_le_of_mem r h trivial) a)).symm
end GlobalTheory.BXOf
