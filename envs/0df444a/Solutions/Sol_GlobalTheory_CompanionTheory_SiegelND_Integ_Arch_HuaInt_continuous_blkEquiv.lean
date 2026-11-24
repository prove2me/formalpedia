-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.continuous_blkEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:38:42.188024+00:00
-- url     : https://prove2.me/submissions/c597bcba-fec1-46ca-9db9-d932d7a37e2f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianHaarBlockDecomposition
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_continuous_blkM


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
theorem _root_.solution (n : ℕ) : Continuous (blkEquiv n) := by
  refine Continuous.subtype_mk (f := fun x : hermC n × (Fin n → ℂ) × ℝ =>
    blkM (x.1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) ?_ _
  exact continuous_blkM.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
