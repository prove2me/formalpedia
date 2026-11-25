-- Prove2me | solution 1 for GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:06.366204+00:00
-- url     : https://prove2.me/submissions/de6f657b-190e-4fa7-8dbc-e2054db1181c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSurjectiveValuationIsIntegralIffNonneg
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_FormalIsogeny_isDiscreteValuationRing_integralClosure
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution (K : UQ) (L : Type) [Field L] [Algebra K.E L]
    [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L] :
    ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧
      ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by
  haveI hdvr := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure K.O K.E L
  haveI hfr := integralClosure.isFractionRing_of_finite_extension (A := K.O) K.E L
  set R := integralClosure K.O L
  let P := IsDiscreteValuationRing.maximalIdeal R
  let u : Lˣ →* Multiplicative ℤ := WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (P.valuation L).toMonoidWithZeroHom.toMonoidHom)
  have hu : ∀ x : Lˣ, ((u x : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = P.valuation L x := by
    intro x
    simp [u, WithZero.coe_unitsWithZeroEquiv_eq_units_val]
  have key : ∀ x : L, x ≠ 0 → (IsIntegral K.O x ↔ P.valuation L x ≤ 1) := by
    intro x hx
    rw [← mem_integralClosure_iff]
    constructor
    · intro h
      have : x = algebraMap R L ⟨x, h⟩ := rfl
      rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    · intro h
      rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
      · rw [← hr]; exact r.2
      · by_cases hrm : r ∈ IsLocalRing.maximalIdeal R
        · exfalso
          have h1 : P.valuation L (algebraMap R L r) < 1 :=
            (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem P r).2 hrm
          rw [hr] at h1
          have h2 : P.valuation L x * P.valuation L x⁻¹ = 1 := by
            rw [← map_mul, mul_inv_cancel₀ hx, map_one]
          have h3 : P.valuation L x * P.valuation L x⁻¹ < 1 :=
            lt_of_le_of_lt (mul_le_of_le_one_left' h) h1
          exact (ne_of_lt h3) h2
        · have hru : IsUnit r := by
            by_contra hh; exact hrm ((IsLocalRing.mem_maximalIdeal r).2 hh)
          obtain ⟨s, hs⟩ := hru
          have : x = algebraMap R L (s⁻¹ : Rˣ) := by
            have e1 : algebraMap R L (s : R) * algebraMap R L ((s⁻¹ : Rˣ) : R) = 1 := by
              rw [← map_mul, Units.mul_inv, map_one]
            rw [hs, hr] at e1
            exact (inv_mul_eq_one₀ hx).1 e1
          rw [this]; exact ((s⁻¹ : Rˣ) : R).2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : algebraMap R L π ≠ 0 := by
    intro h
    exact hπ.ne_zero ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective R L) _ h)
  let πL : Lˣ := Units.mk0 _ hπ0
  have huπ : u πL = Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [hu]
    change P.valuation L (algebraMap R L π) = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_singleton P hπ.ne_zero hπ.maximalIdeal_eq]
    rfl
  refine ⟨u⁻¹, ?_, ?_⟩
  · intro n
    refine ⟨πL ^ (Multiplicative.toAdd n), ?_⟩
    rw [map_zpow, MonoidHom.inv_apply, huπ, ← ofAdd_neg, neg_neg, ← ofAdd_zsmul, smul_eq_mul, mul_one]
    rfl
  · intro x
    rw [key _ x.ne_zero, ← hu, MonoidHom.inv_apply, toAdd_inv, neg_nonneg, ← WithZero.coe_one,
      WithZero.coe_le_coe, ← Multiplicative.toAdd_le, toAdd_one]
end GlobalTheory.UnitLemma
