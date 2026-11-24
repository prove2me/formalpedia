-- Prove2me | solution 1 for GlobalTheory.Chow.injective_of_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:50.347962+00:00
-- url     : https://prove2.me/submissions/01c571f4-f211-400f-ae28-d46773305eae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.Chow
theorem _root_.solution {R S V : Type*} [CommRing R] [CommRing S]
    (ψ : MvPolynomial V R →+* MvPolynomial V S) (hX : ∀ v, ψ (X v) = X v)
    (h : ∀ r, constantCoeff (ψ (C r)) = 0 → r = 0) : Function.Injective ψ := by
  classical
  rw [injective_iff_map_eq_zero]
  intro P hP
  by_contra hne
  obtain ⟨a, ha, hmin⟩ := P.support.exists_minimal (support_nonempty.2 hne)
  have hmon (b : V →₀ ℕ) (r : R) : ψ (monomial b r) = ψ (C r) * monomial b 1 := by
    rw [monomial_eq, monomial_eq, map_mul, C_1, one_mul, map_finsuppProd]
    simp [hX]
  have : coeff a (ψ P) = constantCoeff (ψ (C (coeff a P))) := by
    conv_lhs => rw [P.as_sum, map_sum, coeff_sum]
    rw [Finset.sum_eq_single a]
    · rw [hmon, coeff_mul_monomial', if_pos le_rfl, tsub_self, mul_one, constantCoeff_eq]
    · intro b hb hba
      rw [hmon, coeff_mul_monomial', if_neg]
      exact fun hle => hba (le_antisymm hle (hmin hb hle))
    · exact fun h => absurd ha h
  rw [hP, coeff_zero] at this
  exact mem_support_iff.1 ha (h _ this.symm)
end GlobalTheory.Chow
