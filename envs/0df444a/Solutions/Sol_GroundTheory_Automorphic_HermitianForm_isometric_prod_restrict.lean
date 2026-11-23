-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.isometric_prod_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:54.860629+00:00
-- url     : https://prove2.me/submissions/549fed8e-cb82-40c4-9ce0-46f9082f8e1b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj


attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) (W W' : Submodule E V)
    (hW : h.IsOrthoCompl W W') :
    Isometric ((h.restrict W W' hW).prod (h.restrict W' W hW.symm)) h := by
  refine ⟨Submodule.prodEquivOfIsCompl W W' hW.1, fun p q => ?_⟩
  simp only [Submodule.coe_prodEquivOfIsCompl', prod_apply, restrict_apply, map_add,
    LinearMap.add_apply]
  rw [hW.2 _ p.1.2 _ q.2.2, h.toSesq_eq_zero_comm.1 (hW.2 _ q.1.2 _ p.2.2)]
  ring
end GroundTheory.Automorphic.HermitianForm
