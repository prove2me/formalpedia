-- Prove2me | solution 1 for GlobalTheory.T.fibre_representation_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:18.712921+00:00
-- url     : https://prove2.me/submissions/0702e28b-fc8c-4902-b58a-5f1b14a99a46

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmooth
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmoothStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_isSmooth_fibRep_inr
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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | exact GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.isSmooth_fibRep_inr <;> assumption)
end _root_.GlobalTheory.T
