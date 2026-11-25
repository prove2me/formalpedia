-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.toSesq_quasiReflection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:31.918522+00:00
-- url     : https://prove2.me/submissions/b82f3b01-8fda-494a-b535-842ab2f78354

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_quasiReflection_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_left
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) {w : V} {c : E}
    (hc : c + conj F E c = c * conj F E c * h.toSesq w w) (z z' : V) :
    h.toSesq (h.quasiReflection w c z) (h.quasiReflection w c z') = h.toSesq z z' := by
  simp only [quasiReflection_apply, map_sub, LinearMap.sub_apply, h.toSesq_smul_left,
    h.toSesq_smul_right, map_mul, h.conj_toSesq]
  linear_combination (-(h.toSesq z w * h.toSesq w z')) * hc
end GroundTheory.Automorphic.HermitianForm
