-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ThetaGLLen.isSmoothChar_fibChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:27.81092+00:00
-- url     : https://prove2.me/submissions/29824433-a026-4ad8-8f24-f00096cc7d5b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmooth
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_of_isUnram
import Theorems.Thm_GlobalTheory_SmGL_isUnram_absPow


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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
namespace GlobalTheory.CompanionTheory.ThetaGLLen
theorem _root_.solution {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) :
    IsSmoothChar (fibChar (k := k) a c d μ) := by
  have hA : ∀ s : ℂ, IsSmoothChar (absPow k s) := fun s => isSmoothChar_of_isUnram (isUnram_absPow k s)
  refine IsSmoothChar.mul (IsSmoothChar.mul ?_ ?_) ?_
  · exact (IsSmoothChar.detChar (hμ.inv.mul (hA _))).comp _ continuous_fst
  · exact (IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_fst.comp continuous_snd)
  · exact (IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_snd.comp continuous_snd)
end GlobalTheory.CompanionTheory.ThetaGLLen
