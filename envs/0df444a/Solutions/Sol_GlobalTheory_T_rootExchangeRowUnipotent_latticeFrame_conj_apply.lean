-- Prove2me | solution 1 for GlobalTheory.T.rootExchangeRowUnipotent_latticeFrame_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:23:11.182093+00:00
-- url     : https://prove2.me/submissions/5362098e-a586-404e-9b6c-299f940bd821

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentLatticeFrameConjApply
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentLatticeFrameConjApplyStatement
import Theorems.Thm_GlobalTheory_typeFrame_conj_symm_rowE_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (ϖ : kˣ) (j c l : ℕ) (h : j + c = l) (p : ℕ) (hp : p < c) (u : XIx κ t j → k) (a b : Ix (κ ⊕ Fin l) t j), ((typeFrame ϖ (stdOrd κ t j c h)).conj.symm (rowE c (p + 1) u)).val a b = (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b + if a = Sum.inl (Sum.inr ⟨p, by omega⟩) then Sum.elim (fun y => ((ϖ : k) ^ (p + 1))⁻¹ * u y) (fun _ => 0) (stdOrd κ t j c h b) else 0 := by
  first | exact @GlobalTheory.typeFrame_conj_symm_rowE_apply | exact GlobalTheory.typeFrame_conj_symm_rowE_apply | (intros; apply GlobalTheory.typeFrame_conj_symm_rowE_apply <;> assumption)
end _root_.GlobalTheory.T
