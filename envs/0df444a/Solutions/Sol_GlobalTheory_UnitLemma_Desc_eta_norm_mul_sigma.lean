-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.eta_norm_mul_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:27.386131+00:00
-- url     : https://prove2.me/submissions/00497c89-307c-4c92-9017-8cee5dfac8aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_c
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_norm_sigma
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_norm_ne_zero_of_isUnit
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_mul
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_sq


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
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {v : B.A} (hv : IsUnit v) : K.eta (Algebra.norm K.E (v * B.σ v)) = 1 := by
  rw [map_mul, norm_sigma, eta_mul (norm_ne_zero_of_isUnit B hv)
    ((map_ne_zero K.c).2 (norm_ne_zero_of_isUnit B hv)), eta_c, eta_sq]
end GlobalTheory.UnitLemma.Desc
