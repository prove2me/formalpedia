-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.Isometric.finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:49.365289+00:00
-- url     : https://prove2.me/submissions/167c1286-8990-41a0-bafd-1c0eb30b1226

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
theorem _root_.solution {h : HermitianForm F E V} {h' : HermitianForm F E V'} (H : Isometric h h') :
    finrank E V = finrank E V' := by
  obtain ⟨e, -⟩ := H
  exact e.finrank_eq
end GroundTheory.Automorphic.HermitianForm.Isometric
