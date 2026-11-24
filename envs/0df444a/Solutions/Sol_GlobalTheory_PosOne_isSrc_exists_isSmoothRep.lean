-- Prove2me | solution 1 for GlobalTheory.PosOne.isSrc_exists_isSmoothRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:14.425646+00:00
-- url     : https://prove2.me/submissions/f9634333-b83b-4273-bd20-9a28abda6dae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsWeilSourceActionAndSmooth
import Theorems.Thm_GlobalTheory_SplitWeil_om_isSmoothRepresentation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
noncomputable section
open GlobalTheory GlobalTheory.PosOne
open GlobalTheory.PosOne.SrcAction
namespace GlobalTheory.PosOne
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)), (∃ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ') ∧ ∀ ρ' : Representation ℂ (GL a k) (SB (Matrix b a k)), IsSrc μ ρ' → IsSmoothRep ρ' := by
  intro k _ _ _ _ _ _ a b _ _ _ _ μ hμ
  refine ⟨⟨srcRep μ, fun g Φ => rfl⟩, fun ρ' hρ' Φ => ?_⟩
  have hO := (om_isSmoothRepresentation k a b μ hμ).2.2.2.2 Φ.1 Φ.2
  have hc : Continuous fun g : GL a k => ((g, 1) : GL a k × GL b k) :=
    continuous_id.prodMk continuous_const
  convert hO.preimage hc using 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [← hρ' g Φ]
  exact Subtype.ext_iff
end GlobalTheory.PosOne
