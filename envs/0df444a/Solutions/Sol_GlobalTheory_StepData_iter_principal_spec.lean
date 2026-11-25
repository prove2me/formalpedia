-- Prove2me | solution 1 for GlobalTheory.StepData.iter_principal_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:15:36.036476+00:00
-- url     : https://prove2.me/submissions/82055ddf-657b-4d1b-83f0-1faf84e4597c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IterPrincipalSpec
import Theorems.Thm_GlobalTheory_StepData_mem_iter_principal
import Theorems.Thm_GlobalTheory_StepData_lam_iter_principal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.StepData ValuativeRel Matrix
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, GlobalTheory.SplitWeil.IsTame (μ j)) (j : ℕ), (∀ g : GL (Ix r t j) k, g ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ g ∈ GlobalTheory.SplitWeil.KO k (Ix r t j) ∧ (∀ a b : Ix r t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧ MaxM (g.val.toBlocks₁₁ - 1)) ∧ ∀ (g : ((TypeDatum.principal k r).iter t μ hμ j).J) (d : Fin j → kˣ), (∀ c, (d c : k) = (Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val c).det) → ((TypeDatum.principal k r).iter t μ hμ j).lam g = ∏ c : Fin j, μ (c.val + 1) (d c) :=
  fun μ hμ j => ⟨fun g => mem_iter_principal μ hμ j g, fun g d hd => lam_iter_principal μ hμ j g d hd⟩
end GlobalTheory.StepData
