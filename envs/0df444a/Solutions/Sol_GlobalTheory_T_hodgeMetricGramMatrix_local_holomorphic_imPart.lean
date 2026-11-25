-- Prove2me | solution 1 for GlobalTheory.T.hodgeMetricGramMatrix_local_holomorphic_imPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:57:43.656036+00:00
-- url     : https://prove2.me/submissions/23e7ec53-eb8d-4c21-a4f0-55d10a7a1b9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPartStatement
import Theorems.Thm_GlobalTheory_HodgeGramLocal_hodgeGram_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), IsPeriodChart rk τ₀ B → ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧ (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) • ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) + ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) • ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧ ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by
  first | exact @GlobalTheory.HodgeGramLocal.hodgeGram_local | exact GlobalTheory.HodgeGramLocal.hodgeGram_local | (intros; apply GlobalTheory.HodgeGramLocal.hodgeGram_local <;> assumption)
end _root_.GlobalTheory.T
