-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.fibChar_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:44:31.37617+00:00
-- url     : https://prove2.me/submissions/9f3dcb68-251a-4360-9b7f-16940f166384

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OmegaEquivInducedFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]
namespace GlobalTheory.CompanionTheory.ThetaGLLen
theorem _root_.solution (e : c ⊕ d ≃ b) (μ : kˣ →* ℂˣ) (γ : GL a k) :
    fibChar a c d μ (γ, 1, 1) = omChar a b μ (γ, 1) := by
  have hb : ((Fintype.card c : ℂ) + Fintype.card d) / 2 = (Fintype.card b : ℂ) / 2 := by
    rw [← Fintype.card_congr e, Fintype.card_sum]; push_cast; ring
  simp [fibChar, omChar, hb]
end GlobalTheory.CompanionTheory.ThetaGLLen
