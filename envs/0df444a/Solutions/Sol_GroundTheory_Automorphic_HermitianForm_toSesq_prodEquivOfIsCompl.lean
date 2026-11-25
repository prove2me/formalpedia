-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.toSesq_prodEquivOfIsCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:31.269678+00:00
-- url     : https://prove2.me/submissions/d3e43ef4-c6c1-4a3d-8d14-64292d0be69b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) {W W' : Submodule E V}
    (hW : h.IsOrthoCompl W W') (p q : W × W') :
    h.toSesq (Submodule.prodEquivOfIsCompl W W' hW.1 p)
      (Submodule.prodEquivOfIsCompl W W' hW.1 q) =
      h.toSesq p.1 q.1 + h.toSesq p.2 q.2 := by
  rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add, map_add,
    LinearMap.add_apply, LinearMap.add_apply, hW.2 _ p.1.2 _ q.2.2,
    h.toSesq_eq_zero_comm.1 (hW.2 _ q.1.2 _ p.2.2)]
  ring
end GroundTheory.Automorphic.HermitianForm
