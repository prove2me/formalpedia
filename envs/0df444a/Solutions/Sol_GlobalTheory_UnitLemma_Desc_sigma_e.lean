-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.sigma_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:59:06.700809+00:00
-- url     : https://prove2.me/submissions/5dfe0e94-4741-419e-85c9-c23a3aa42b07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ} (B : InvAlg K)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (i : ι) : B.σ (e i) = e i := by
  obtain ⟨f, -, -, -, h1, h2⟩ := h.2 i
  by_cases hi : i ∈ S
  · rw [(h1 hi).1, (h1 hi).2]
  · rw [(h2 hi).2, map_add, B.σ_σ, add_comm]
end GlobalTheory.UnitLemma.Desc
