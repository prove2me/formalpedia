-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothLog.exists_log_banach
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:12.46547+00:00
-- url     : https://prove2.me/submissions/a553c3fb-0793-4c57-807a-6e52d5d15b9a

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLog
import Theorems.Thm_CompanionTheory_D_Upq_expPartialHomeomorph_symm_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothLog
namespace GlobalTheory.CompanionTheory.SmoothLog
theorem _root_.solution (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    ∃ (U : Set A) (L : A → A), IsOpen U ∧ (1 : A) ∈ U ∧ ContDiffOn ℝ ∞ L U ∧ L 1 = 0 ∧
      (∀ g ∈ U, NormedSpace.exp (L g) = g) ∧
      (∀ᶠ X in 𝓝 (0 : A), L (NormedSpace.exp X) = X) := by
  let e := CompanionTheory.D.Upq.expPartialHomeomorph ℝ A
  refine ⟨e.target, e.symm, e.open_target, CompanionTheory.D.Upq.one_mem_expPartialHomeomorph_target ℝ A,
    CompanionTheory.D.Upq.contDiffOn_expPartialHomeomorph_symm ℝ A,
    CompanionTheory.D.Upq.expPartialHomeomorph_symm_one ℝ A, fun g hg => e.right_inv hg, ?_⟩
  filter_upwards [e.open_source.mem_nhds (CompanionTheory.D.Upq.zero_mem_expPartialHomeomorph_source ℝ A)]
    with X hX using e.left_inv hX
end GlobalTheory.CompanionTheory.SmoothLog
