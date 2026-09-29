-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e02f3d66-c54e-5ec4-b796-31f921c9d105

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot_of_isPrecomplete
import Theorems.Thm_PowerSeries_prime_X_sq_sub_C_X_mul_X_add_C_C
import Theorems.Thm_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete

set_option autoImplicit false

namespace IsPrecomplete p2m_export "IsPrecomplete" "prec'" end IsPrecomplete
p2m_open_scoped "IsPrecomplete" in

theorem IsPrecomplete.pow_of_isPrecomplete {R : Type*} [CommRing R] (I : Ideal R) [h : IsPrecomplete I R]
    (e : ℕ) (he : 1 ≤ e) : IsPrecomplete (I ^ e) R := by
  refine ⟨fun {f} hf => ?_⟩
  have hf' : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n hmn
    have := hf hmn
    refine SModEq.mono ?_ this
    apply Submodule.smul_mono_left
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by nlinarith)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' f hf'
  refine ⟨L, fun n => ?_⟩
  have h1 : f n ≡ f (e * n) [SMOD (I ^ e) ^ n • (⊤ : Submodule R R)] := hf (by nlinarith)
  have h2 : f (e * n) ≡ L [SMOD I ^ (e * n) • (⊤ : Submodule R R)] := hL (e * n)
  rw [← pow_mul] at h1 ⊢
  exact h1.trans h2

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    IsDomain (UVCrossingModel W (ϖ ^ e)) ∧ IsLocalRing (UVCrossingModel W (ϖ ^ e)) ∧
      IsIntegrallyClosed (UVCrossingModel W (ϖ ^ e)) := by
  have hmW : IsLocalRing.maximalIdeal W = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖu : ¬IsUnit ϖ := hϖ.not_isUnit
  set c : W := ϖ ^ e with hc
  have hcu : ¬IsUnit c := by
    rw [hc]; exact fun h => hϖu (isUnit_pow_iff (by omega) |>.mp h)
  have hc0 : c ≠ 0 := pow_ne_zero e hϖ.ne_zero
  haveI : IsPrecomplete (Ideal.span {c}) W := by
    have : Ideal.span {c} = (IsLocalRing.maximalIdeal W) ^ e := by
      rw [hmW, Ideal.span_singleton_pow]
    rw [this]
    exact IsPrecomplete.pow_of_isPrecomplete _ e he
  obtain ⟨eqv, -, -⟩ := exists_ringEquiv_adjoinRoot_of_isPrecomplete c hc0 hcu
  have hprime := PowerSeries.prime_X_sq_sub_C_X_mul_X_add_C_C (D := W) hc0 hcu
  haveI hdomA := AdjoinRoot.isDomain_of_prime hprime
  haveI hicA := PowerSeries.isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow ϖ hϖ e he
  exact ⟨MulEquiv.isDomain _ eqv.toMulEquiv, isLocalRing_of_not_isUnit hcu, IsIntegrallyClosed.of_equiv eqv.symm⟩

end S_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete (solution)
