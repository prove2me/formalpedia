-- Prove2me | solution 1 for GroundTheory.ProfCoh.h2IntRepAddEquiv_H2_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:52.227726+00:00
-- url     : https://prove2.me/submissions/a1641fcd-75fd-4396-9d45-ef59c009d571

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_OrderScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
variable {G M : Type} [Group G] [CommGroup M] (φ : G →* Monoid.End M)
namespace GroundTheory.ProfCoh
theorem _root_.solution (x : cocycles₂ (Rep.of (intRepOfMonoidEnd.{0} φ))) :
    h2IntRepAddEquiv φ ((H2π _).hom x) = (H2π _).hom (cocycles₂IntRepAddEquiv φ x) := by
  have h1 : (QuotientAddGroup.quotientKerEquivOfSurjective
      (H2π (Rep.of (intRepOfMonoidEnd.{0} φ))).hom.toAddMonoidHom
      (h2π_intRepOfMonoidEnd_surjective φ)).symm ((H2π _).hom x) = (QuotientAddGroup.mk x : _ ⧸ _) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [h2IntRepAddEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply, h1]
  rfl
end GroundTheory.ProfCoh
