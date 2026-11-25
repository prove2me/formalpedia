-- Prove2me | solution 1 for GlobalTheory.T.hilbertEisensteinSeries_ringEquiv_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:18:32.769158+00:00
-- url     : https://prove2.me/submissions/356b6f86-960c-426c-8812-047c622a925b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesRingEquivConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesRingEquivConjStatement
import Theorems.Thm_GlobalTheory_HilbFam_hser_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (Emb F)) (κ : Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → 0 < N → IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → HasLevel N (split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (PowerSeries.coeff n (hser k N 𝔞 a x κ c)) = PowerSeries.coeff n (hser k N 𝔞 a (m * x) (fun j ↦ κ (π.symm j)) (fun n ↦ g (c n))) := by
  first | exact @GlobalTheory.HilbFam.hser_conj | exact GlobalTheory.HilbFam.hser_conj | (intros; apply GlobalTheory.HilbFam.hser_conj <;> assumption)
end _root_.GlobalTheory.T
