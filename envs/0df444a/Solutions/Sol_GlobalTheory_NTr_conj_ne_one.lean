-- Prove2me | solution 1 for GlobalTheory.NTr.conj_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:50.242829+00:00
-- url     : https://prove2.me/submissions/c080c5c0-d08c-4f26-8a64-98b84914c3f9

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
import Theorems.Thm_GlobalTheory_NTr_conj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
namespace GlobalTheory.NTr
theorem _root_.solution : conj F E ≠ 1 := by
  intro h
  obtain ⟨y, hy⟩ := hU.star_ne
  apply hy
  have := congrArg (fun σ : E ≃ₐ[F] E => σ y) h
  simpa [conj_apply] using this
end GlobalTheory.NTr
