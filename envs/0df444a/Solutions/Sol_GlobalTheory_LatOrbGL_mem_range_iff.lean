-- Prove2me | solution 1 for GlobalTheory.LatOrbGL.mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:21.666828+00:00
-- url     : https://prove2.me/submissions/45ec4074-7b2f-4efa-ab85-36257164e71b

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGLintIffMatrixImageStandardLatticeEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrbGL
variable {K : Type} [Field K] (V : ValuationSubring K)
namespace GlobalTheory.LatOrbGL
theorem _root_.solution (x : K) : x ∈ (algebraMap V K).range ↔ x ∈ V := by
  constructor
  · rintro ⟨a, rfl⟩; exact a.2
  · intro h; exact ⟨⟨x, h⟩, rfl⟩
end GlobalTheory.LatOrbGL
