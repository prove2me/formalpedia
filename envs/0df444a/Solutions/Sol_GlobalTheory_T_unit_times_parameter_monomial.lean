-- Prove2me | solution 1 for GlobalTheory.T.unit_times_parameter_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:05.059581+00:00
-- url     : https://prove2.me/submissions/c5484756-d50e-4a26-85d5-5315412eed61

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_UnitTimesParameterMonomial
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_UnitTimesParameterMonomialStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_exponent_eq_order_polynomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (r : Fin e → MvPolynomial (Fin m) ℂ) (Jf : Finset (Fin e)) (g : MvPolynomial (Fin m) ℂ) (u : (locRing I t)ˣ) (mm : Fin e → ℕ), (∀ h ∈ I, eval t h = 0) → IsRegularLocalRing (locRing I t) → ringKrullDim (locRing I t) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) = Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) → algebraMap _ (locRing I t) g = u * ∏ i ∈ Jf, algebraMap _ (locRing I t) (r i) ^ mm i → ∀ i ∈ Jf, ∀ n : ℕ, (∃ s ∉ SncRes.Par.chPrime I t (r i), s * g ∈ SncRes.Par.chPrime I t (r i) ^ n ⊔ I) ↔ n ≤ mm i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial <;> assumption)
end _root_.GlobalTheory.T
