-- Prove2me | solution 1 for GlobalTheory.pderivIter_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:16.488534+00:00
-- url     : https://prove2.me/submissions/4da97d38-d91b-4000-8373-63a37dcc71e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Theorems.Thm_GlobalTheory_pderivList_replicate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
namespace GlobalTheory
theorem _root_.solution (k : ι) (n : ℕ) (F : (ι → 𝕜) → V) (z : ι → 𝕜) :
    pderivIter (Finsupp.single k n) F z
      = iteratedDeriv n (fun t => F (Function.update z k t)) (z k) := by
  rw [← pderivList_replicate, pderivIter, Finsupp.toMultiset_single]
  congr 1
  rw [← List.perm_replicate, ← Multiset.coe_eq_coe, Multiset.coe_toList,
    Multiset.nsmul_singleton, Multiset.coe_replicate]
end GlobalTheory
