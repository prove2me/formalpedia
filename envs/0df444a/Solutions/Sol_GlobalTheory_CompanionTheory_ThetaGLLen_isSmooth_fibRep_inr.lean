-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:57:45.915143+00:00
-- url     : https://prove2.me/submissions/86fba286-6389-4919-94a7-e078faa36442

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmooth
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_isSmooth_fibRep_levi
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ThetaGLLen
namespace GlobalTheory.CompanionTheory.ThetaGLLen
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  intro k _ _ _ _ a c d _ _ _ _ _ _ μ hμ κ
  exact isSmooth_fibRep_levi a c d μ hμ κ
end GlobalTheory.CompanionTheory.ThetaGLLen
