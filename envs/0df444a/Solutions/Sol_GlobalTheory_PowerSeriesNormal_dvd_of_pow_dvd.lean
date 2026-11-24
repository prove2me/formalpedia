-- Prove2me | solution 1 for GlobalTheory.PowerSeriesNormal.dvd_of_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:31.162665+00:00
-- url     : https://prove2.me/submissions/8a27b2f1-81e6-43a4-96b2-b8c2782cbcd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegrallyClosedPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PowerSeriesNormal
open PowerSeries
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.PowerSeriesNormal
theorem _root_.solution [IsNoetherianRing R] [IsIntegrallyClosed R] {f g h : R} (hg : g ≠ 0)
    (hh : h ≠ 0) (H : ∀ n : ℕ, g ^ n ∣ h * f ^ n) : g ∣ f := by
  classical
  let K := FractionRing R
  have hinj := IsFractionRing.injective R K
  have hgK : algebraMap R K g ≠ 0 := (map_ne_zero_iff _ hinj).2 hg
  have hhK : algebraMap R K h ≠ 0 := (map_ne_zero_iff _ hinj).2 hh
  set x : K := algebraMap R K f / algebraMap R K g with hx
  let M : Submodule R K := Submodule.span R {(algebraMap R K h)⁻¹}
  have hpow : ∀ n : ℕ, x ^ n ∈ M := by
    intro n
    obtain ⟨c, hc⟩ := H n
    have : x ^ n = c • (algebraMap R K h)⁻¹ := by
      rw [Algebra.smul_def, hx, div_pow, eq_mul_inv_iff_mul_eq₀ hhK, div_mul_eq_mul_div,
        div_eq_iff (pow_ne_zero _ hgK)]
      have := congrArg (algebraMap R K) hc
      simp only [map_mul, map_pow] at this
      linear_combination this
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin R {x}) ≤ M := by
    intro y hy
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    change Polynomial.aeval x p ∈ M
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpow i)
  have : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M (Submodule.fg_span_singleton _)
  have := isNoetherian_of_le hle
  have hint : IsIntegral R x :=
    isIntegral_of_submodule_noetherian _ this x (Algebra.subset_adjoin rfl)
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).1 inferInstance hint
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, hx, mul_comm]
  exact (div_mul_cancel₀ _ hgK).symm
end GlobalTheory.PowerSeriesNormal
