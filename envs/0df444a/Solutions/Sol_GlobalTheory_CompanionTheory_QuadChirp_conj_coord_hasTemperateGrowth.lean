-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuadChirp.conj_coord_hasTemperateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:48.17533+00:00
-- url     : https://prove2.me/submissions/757e162b-5765-456d-b13b-ea98f3134e4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzQuadraticPhaseMultiplication

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
theorem _root_.solution {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u l i)) :=
  ((Complex.conjCLE.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth
end GlobalTheory.CompanionTheory.QuadChirp
