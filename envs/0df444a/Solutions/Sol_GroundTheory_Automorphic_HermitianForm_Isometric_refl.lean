-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.Isometric.refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:07.910885+00:00
-- url     : https://prove2.me/submissions/5c351561-a3d7-4bac-bb4a-d7930c6ed17f

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
open GroundTheory.Automorphic.HermitianForm.Isometric
namespace GroundTheory.Automorphic.HermitianForm.Isometric
theorem _root_.solution (h : HermitianForm F E V) : Isometric h h := ⟨LinearEquiv.refl E V, fun _ _ => rfl⟩
end GroundTheory.Automorphic.HermitianForm.Isometric
