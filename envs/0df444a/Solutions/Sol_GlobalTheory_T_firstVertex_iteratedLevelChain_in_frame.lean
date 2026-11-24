-- Prove2me | solution 1 for GlobalTheory.T.firstVertex_iteratedLevelChain_in_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:49.694968+00:00
-- url     : https://prove2.me/submissions/4985b0d8-be61-454a-8adc-322ff630f54f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexIteratedLevelChainInFrame
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexIteratedLevelChainInFrameStatement
import Theorems.Thm_GlobalTheory_FirstVertexFrame_firstVertex_typeChain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (s : ℕ) (t : Type) [Fintype t] [DecidableEq t] (κ : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin (s + 1))), ((∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ γ : GL (Fin κ) k, u * embX (s + 1) γ ∈ P.J → ∃ gb, Reduces γ gb ∧ IsUpperUnip Fin.val gb.val) ∧ (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), Reduces γ gb → IsUpperUnip Fin.val gb.val → ∃ hm : embX (s + 1) γ ∈ P.J, (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val γ.val)) ∧ ∀ u ∈ N k (Fin κ) (s + 1) 1, ∀ hm : u ∈ P.J, (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum u)) → ∀ (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (c : ℕ) (H : 0 + c = s + 1), (prX (Cgrp ((typeChain t ϖ P μ hμ).lev 0 c H).J 1) : Set (GL (XIx (Fin κ) t 0) k)) = colGroup k κ t ∧ (∀ γ ∈ colGroup k κ t, ∃ hm : embX c γ ∈ ((typeChain t ϖ P μ hμ).lev 0 c H).J, (((typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨_, hm⟩ : ℂ) = colChar ψ ϖ γ) ∧ ∀ u ∈ N k (XIx (Fin κ) t 0) c 1, ∀ hm : u ∈ ((typeChain t ϖ P μ hμ).lev 0 c H).J, (((typeChain t ϖ P μ hμ).lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u) := by
  first | exact @GlobalTheory.FirstVertexFrame.firstVertex_typeChain | exact GlobalTheory.FirstVertexFrame.firstVertex_typeChain | (intros; apply GlobalTheory.FirstVertexFrame.firstVertex_typeChain <;> assumption)
end _root_.GlobalTheory.T
