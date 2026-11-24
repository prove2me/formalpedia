-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.continuous_blkEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:38:48.278358+00:00
-- url     : https://prove2.me/submissions/b2e900c1-74c2-4a68-9814-1afe93f31f4c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianHaarBlockDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
theorem _root_.solution (n : ℕ) : Continuous (blkEquiv n).symm := by
  have h : ∀ i j : Fin (n + 1), Continuous fun b : hermC (n + 1) =>
      (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j := fun i j =>
    (continuous_apply_apply i j).comp continuous_subtype_val
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    exact h _ _
  · exact continuous_pi fun i => h _ _
  · exact Complex.continuous_re.comp (h _ _)
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
