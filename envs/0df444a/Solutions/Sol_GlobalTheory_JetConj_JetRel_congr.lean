-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:38.1628+00:00
-- url     : https://prove2.me/submissions/8a3a8937-4236-4dc4-ab28-cfef362b9c6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace JetRel
theorem _root_.solution (H : JetRel S f f') (h1 : f =ᶠ[𝓝 0] g) (h2 : f' =ᶠ[𝓝 0] g') : JetRel S g g' := by
  obtain ⟨hf, hf', hd⟩ := H
  refine ⟨hf.congr h1, hf'.congr h2, fun n => ?_⟩
  rw [← h1.iteratedDeriv_eq n, ← h2.iteratedDeriv_eq n]
  exact hd n
end JetRel
end GlobalTheory.JetConj
