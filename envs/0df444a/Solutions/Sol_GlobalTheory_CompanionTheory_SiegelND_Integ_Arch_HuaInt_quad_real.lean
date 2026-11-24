-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.quad_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:38:56.537292+00:00
-- url     : https://prove2.me/submissions/b3cb5e39-fbd0-44b9-be84-59f1d0c5feb7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetWBlockMatrixFormula

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
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
theorem _root_.solution {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) = star v ⬝ᵥ (b *ᵥ v) := by
  have h : star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, hb.eq, Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_re.1 h
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
