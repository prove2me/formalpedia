-- Prove2me | solution 1 for NumberField.PlaceTransport.exists_pow_smul_eq_of_forall_mem_zpowers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c3fdba6c-aa1c-57ab-bbdb-0d80f854c4b9

import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceTransport_exists_pow_smul_eq_of_forall_mem_zpowers

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField.PlaceTransport Pointwise

namespace S3tAux

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem smul_asIdeal_pointwise (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).asIdeal = σ • w.asIdeal := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, Ideal.pointwise_smul_def]
  rfl

end S3tAux

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (w w' : v.Extension (𝓞 L)) :
    ∃ n : ℕ, (σ ^ n) • w.1 = w'.1 := by
  classical
  haveI : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  haveI hP : w.1.asIdeal.IsPrime := w.1.isPrime
  haveI hQ : w'.1.asIdeal.IsPrime := w'.1.isPrime
  haveI hPl : w.1.asIdeal.LiesOver v.asIdeal :=
    ⟨by rw [← HeightOneSpectrum.under_asIdeal (𝓞 K) w.1, w.2]⟩
  haveI hQl : w'.1.asIdeal.LiesOver v.asIdeal :=
    ⟨by rw [← HeightOneSpectrum.under_asIdeal (𝓞 K) w'.1, w'.2]⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.1.asIdeal w'.1.asIdeal (L ≃ₐ[K] L)
  have hτw : τ • w.1 = w'.1 := HeightOneSpectrum.ext (by rw [S3tAux.smul_asIdeal_pointwise, hτ])
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
  refine ⟨(k % (orderOf σ : ℤ)).toNat, ?_⟩
  have hpos : (0 : ℤ) < (orderOf σ : ℤ) := by exact_mod_cast (orderOf_pos σ)
  have hk : σ ^ ((k % (orderOf σ : ℤ)).toNat) = σ ^ k := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne'), zpow_mod_orderOf]
  rw [hk]
  exact hτw

end S_NumberField_PlaceTransport_exists_pow_smul_eq_of_forall_mem_zpowers
end P2MW
export P2MW.S_NumberField_PlaceTransport_exists_pow_smul_eq_of_forall_mem_zpowers (solution)
