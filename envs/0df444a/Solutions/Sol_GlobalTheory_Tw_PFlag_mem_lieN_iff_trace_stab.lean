-- Prove2me | solution 1 for GlobalTheory.Tw.PFlag.mem_lieN_iff_trace_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:34:48.832917+00:00
-- url     : https://prove2.me/submissions/6cedef2b-65c9-4f85-a7fc-e4d43c78f169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars
import Theorems.Thm_GlobalTheory_Tw_PFlag_mem_stab_iff
import Theorems.Thm_GlobalTheory_Tw_PFlag_mem_lieN_iff_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
open GlobalTheory.Tw.PFlag
variable {n : ℕ} {k : Type} [Field k] {F : PFlag n k}
namespace GlobalTheory.Tw.PFlag
theorem _root_.solution [Infinite k] {X : Matrix (Fin n) (Fin n) k} :
    X ∈ F.lieN ↔ ∀ g ∈ F.stab, (X * g.val).trace = 0 := by
  rw [mem_lieN_iff_trace]
  refine ⟨fun h g hg => h _ hg.1, fun h Y hY => ?_⟩
  obtain ⟨c, hc⟩ := (Matrix.finite_spectrum Y).exists_notMem
  obtain ⟨u, hu⟩ := spectrum.notMem_iff.1 hc
  have h1 := h u (mem_stab_iff.2 (by
    rw [hu, Algebra.algebraMap_eq_smul_one]; exact sub_mem (F.lieQ.smul_mem c one_mem_lieQ) hY))
  have h2 := h 1 (one_mem _)
  rw [hu, Algebra.algebraMap_eq_smul_one, mul_sub, trace_sub, Matrix.mul_smul, trace_smul] at h1
  rw [Units.val_one] at h2
  rwa [h2, smul_zero, zero_sub, neg_eq_zero] at h1
end GlobalTheory.Tw.PFlag
