-- Prove2me | solution 1 for GlobalTheory.T.coinvariants_finite_of_smooth_levi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:19.462797+00:00
-- url     : https://prove2.me/submissions/f883396b-296b-405e-a3fa-d1ea4a9f3ae4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLeviStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_hasFiniteLength_coinv_indSnd
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], InductionFiniteLength k → ∀ (Γ W b c d : Type) [Group Γ] [AddCommGroup W] [Module ℂ W] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (τ : Representation ℂ (Γ × (GL c k × GL d k)) W), IsSmooth (τ.comp (MonoidHom.inr Γ (GL c k × GL d k))) → ∀ ψ : Γ →* ℂˣ, Module.Finite ℂ (W ⧸ twRel (τ.comp (MonoidHom.inl Γ (GL c k × GL d k))) ψ) → HasFiniteLength (coinv (indSnd e τ) ψ) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd | exact GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.hasFiniteLength_coinv_indSnd <;> assumption)
end _root_.GlobalTheory.T
