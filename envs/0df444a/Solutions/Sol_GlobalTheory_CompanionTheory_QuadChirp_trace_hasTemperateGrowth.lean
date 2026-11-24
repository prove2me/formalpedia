-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuadChirp.trace_hasTemperateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:27.994853+00:00
-- url     : https://prove2.me/submissions/2476bddf-1030-4df7-8544-0905776f3326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzQuadraticPhaseMultiplication
import Theorems.Thm_GlobalTheory_CompanionTheory_QuadChirp_coord_hasTemperateGrowth
import Theorems.Thm_GlobalTheory_CompanionTheory_QuadChirp_conj_coord_hasTemperateGrowth

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
theorem _root_.solution {m n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) :
    Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) := by
  have heq : (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) =
      fun u => ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m, b i j * (star (u l j) * u l i) := by
    funext u
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Finset.mul_sum]
  rw [heq]
  refine Function.HasTemperateGrowth.sum fun i _ => Function.HasTemperateGrowth.sum fun j _ =>
    Function.HasTemperateGrowth.sum fun l _ => ?_
  exact (Function.HasTemperateGrowth.const (b i j)).mul
    ((GlobalTheory.CompanionTheory.QuadChirp.conj_coord_hasTemperateGrowth l j).mul (GlobalTheory.CompanionTheory.QuadChirp.coord_hasTemperateGrowth l i))
end GlobalTheory.CompanionTheory.QuadChirp
