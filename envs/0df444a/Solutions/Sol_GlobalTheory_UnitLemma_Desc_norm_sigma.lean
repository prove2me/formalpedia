-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.norm_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:59:06.033033+00:00
-- url     : https://prove2.me/submissions/dc6f738f-5949-4250-817a-3b551e26a743

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
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution (u : B.A) : Algebra.norm K.E (B.σ u) = K.c (Algebra.norm K.E u) := by
  have h := Algebra.norm_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) u
  rw [h, RingEquiv.apply_symm_apply]
end GlobalTheory.UnitLemma.Desc
