-- Prove2me | solution 1 for GlobalTheory.DetBound.cmType_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:10:55.170865+00:00
-- url     : https://prove2.me/submissions/5da28f1f-1fa0-4875-a93a-1655eef89c52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
namespace GlobalTheory.DetBound
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] {I : Type}
    {φ : I → E →+* K} (hφ : IsCMTypeIn φ) : Function.Injective φ := by
  intro i j h
  obtain ⟨k, _, hk⟩ := hφ (φ i)
  exact (hk i (Or.inl rfl)).trans (hk j (Or.inl h)).symm
end GlobalTheory.DetBound
