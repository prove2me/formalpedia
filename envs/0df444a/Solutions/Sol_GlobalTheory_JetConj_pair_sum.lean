-- Prove2me | solution 1 for GlobalTheory.JetConj.pair_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:29.078995+00:00
-- url     : https://prove2.me/submissions/21fdd71c-c75a-47e0-89e3-1b943e0e8baf

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {a b : ι → ℂ} (h : ∀ i ∈ s, (a i, b i) ∈ S) :
    (∑ i ∈ s, a i, ∑ i ∈ s, b i) ∈ S := by
  have hs : (∑ i ∈ s, ((a i, b i) : ℂ × ℂ)) ∈ S := sum_mem h
  convert hs using 1
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]
end GlobalTheory.JetConj
