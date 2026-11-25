-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.le_of_mul_pow_mem_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:13.209293+00:00
-- url     : https://prove2.me/submissions/8bd15b24-1ae8-47a4-974c-d64efe434e23

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_UnitTimesParameterMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] {p a : O} (hp : Prime p)
    (ha : ¬ p ∣ a) {k n : ℕ} (h : a * p ^ k ∈ Ideal.span {p} ^ n) : n ≤ k := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  by_contra hlt
  have hlt' : k + 1 ≤ n := by omega
  have h1 : p ^ (k + 1) ∣ a * p ^ k := (pow_dvd_pow p hlt').trans h
  rw [pow_succ, mul_comm a, mul_comm (p ^ k) p, mul_comm p] at h1
  exact ha ((mul_dvd_mul_iff_left (pow_ne_zero k hp.ne_zero)).mp (by simpa [mul_comm] using h1))
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
