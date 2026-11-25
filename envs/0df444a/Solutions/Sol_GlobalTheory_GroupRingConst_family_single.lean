-- Prove2me | solution 1 for GlobalTheory.GroupRingConst.family_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:31.396417+00:00
-- url     : https://prove2.me/submissions/afaa4989-2074-4dcf-ae04-dbcd229bbae3

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
import Theorems.Thm_GlobalTheory_restrictPoints_val
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
theorem _root_.solution {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) (a : X) (x : R) :
    family r c l (AddMonoidAlgebra.single a x) =
      AddMonoidAlgebra.single (l a) (r x * (c (Multiplicative.ofAdd a) : F)) := by
  simp [family, AddMonoidAlgebra.liftNCRingHom, AddMonoidAlgebra.liftNC_single,
    AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.of_apply, _root_.mul_assoc]
end GlobalTheory.GroupRingConst
