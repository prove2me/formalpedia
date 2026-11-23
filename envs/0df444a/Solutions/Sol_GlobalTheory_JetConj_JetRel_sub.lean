-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:37.201507+00:00
-- url     : https://prove2.me/submissions/dacaee7e-6b78-402b-9528-50ab434f662a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Theorems.Thm_GlobalTheory_JetConj_pair_sub

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
theorem _root_.solution (H : JetRel S f f') (K : JetRel S g g') :
    JetRel S (fun z => f z - g z) (fun z => f' z - g' z) := by
  obtain ⟨hf, hf', hdf⟩ := H
  obtain ⟨hg, hg', hdg⟩ := K
  refine ⟨by fun_prop, by fun_prop, fun n => ?_⟩
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, iteratedDeriv_fun_sub hf'.contDiffAt hg'.contDiffAt]
  exact pair_sub (hdf n) (hdg n)
end JetRel
end GlobalTheory.JetConj
