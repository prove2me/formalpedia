-- Prove2me | solution 1 for GlobalTheory.pderivList_replicate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:54.823795+00:00
-- url     : https://prove2.me/submissions/18308d0a-ca5a-4f56-ab01-8bd8cee23969

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Theorems.Thm_GlobalTheory_update_eq_add_smul_single
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_replicate
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero



set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
namespace GlobalTheory
theorem _root_.solution (k : ι) (n : ℕ) (F : (ι → 𝕜) → V) (z : ι → 𝕜) :
    pderivList (List.replicate n k) F z
      = iteratedDeriv n (fun t => F (Function.update z k t)) (z k) := by
  have h := lineDerivList_replicate n (Pi.single k (1 : 𝕜) : ι → 𝕜) F z (0 : 𝕜)
  rw [zero_smul, add_zero] at h
  rw [pderivList, List.map_replicate, h]
  simp only [update_eq_add_smul_single]
  rw [iteratedDeriv_comp_sub_const (f := fun s : 𝕜 => F (z + s • (Pi.single k 1 : ι → 𝕜)))]
  simp
end GlobalTheory
