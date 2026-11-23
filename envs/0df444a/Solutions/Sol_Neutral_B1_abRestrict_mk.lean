-- Prove2me | solution 1 for Neutral.B1.abRestrict_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:59.269933+00:00
-- url     : https://prove2.me/submissions/36655552-4b76-495c-9360-45abc9f44e92

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Topology
open Neutral Neutral.B1
variable (F : Type*) [Field F]
namespace Neutral.B1
theorem _root_.solution (L : IntermediateField F (AlgebraicClosure F)) (h : IsFiniteAbelian F L)
    (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    haveI := h.isGalois
    abRestrict F L h (toAb F g) = AlgEquiv.restrictNormalHom L g := by
  unfold abRestrict toAb
  exact QuotientGroup.lift_mk' _ _ _
end Neutral.B1
