-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.toSesq_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:06.561359+00:00
-- url     : https://prove2.me/submissions/52e3b67a-ed63-408e-b36b-bb7be6ef844e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal

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
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution (h : HermitianForm F E V) (c : E) (x y : V) :
    h.toSesq (c • x) y = conj F E c * h.toSesq x y := by
  rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, conjHom_apply]
end GroundTheory.Automorphic.HermitianForm
