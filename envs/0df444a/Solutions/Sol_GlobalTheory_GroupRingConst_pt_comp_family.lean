-- Prove2me | solution 1 for GlobalTheory.GroupRingConst.pt_comp_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:22:19.999233+00:00
-- url     : https://prove2.me/submissions/f26fddac-5e6c-4b27-8623-be8717912b9d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Theorems.Thm_GlobalTheory_GroupRingConst_pt_single
import Theorems.Thm_GlobalTheory_GroupRingConst_powChar_apply
import Theorems.Thm_GlobalTheory_GroupRingConst_family_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val


attribute [local simp] GlobalTheory.GroupRingConst.pt_single
attribute [local simp] GlobalTheory.GroupRingConst.powChar_apply

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GroupRingConst
namespace GlobalTheory.GroupRingConst
theorem _root_.solution {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X]
    (r : R →+* F) (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) (u : Fˣ) :
    (pt (RingHom.id F) (zpowersHom Fˣ u)).comp (family r c l) = pt r (c * powChar l u) := by
  refine AddMonoidAlgebra.ringHom_ext (fun x => ?_) (fun a => ?_) <;>
    (rw [RingHom.comp_apply, family_single, pt_single, pt_single]
     simp [powChar_apply])
end GlobalTheory.GroupRingConst
