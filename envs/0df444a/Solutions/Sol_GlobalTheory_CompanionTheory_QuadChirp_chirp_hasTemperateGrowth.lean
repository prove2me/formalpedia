-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuadChirp.chirp_hasTemperateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:21.592005+00:00
-- url     : https://prove2.me/submissions/8a580098-ecb1-427a-81da-5ab0fef1e4e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzQuadraticPhaseMultiplication
import Theorems.Thm_GlobalTheory_CompanionTheory_QuadChirp_ofReal_re_trace
import Theorems.Thm_GlobalTheory_CompanionTheory_QuadChirp_trace_hasTemperateGrowth
import Theorems.Thm_GlobalTheory_Published_Metaplectic_eChar_apply
import Theorems.Thm_GlobalTheory_Published_Metaplectic_hasTemperateGrowth_eChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuadChirp
namespace GlobalTheory.CompanionTheory.QuadChirp
theorem _root_.solution {m n : ℕ} (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
        Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) := by
  have hre : Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ =>
      k * (Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))).re) :=
    (Function.HasTemperateGrowth.const k).mul
      (Complex.reCLM.hasTemperateGrowth.comp (GlobalTheory.CompanionTheory.QuadChirp.trace_hasTemperateGrowth b))
  have hcomp := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp hre
  convert hcomp using 1
  funext u
  rw [Function.comp_apply, GlobalTheory.Published.Metaplectic.eChar_apply]
  congr 1
  have hT := GlobalTheory.CompanionTheory.QuadChirp.ofReal_re_trace b hb (Matrix.of u)
  rw [Complex.ofReal_mul]
  conv_lhs => rw [← hT]
  ring
end GlobalTheory.CompanionTheory.QuadChirp
