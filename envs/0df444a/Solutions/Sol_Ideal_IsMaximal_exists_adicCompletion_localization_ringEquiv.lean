-- Prove2me | solution 1 for Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/40dde146-8c85-599b-a2c8-e0b34c55616d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv

set_option autoImplicit false

universe u

namespace AdicIso

open Ideal Ideal.Quotient AdicCompletion

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hle a

theorem exists_ringEquiv (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (x : R ⧸ I ^ n),
      e m (Ideal.Quotient.factorPow I hle x) = Ideal.Quotient.factorPow J hle (e n x)) :
    ∃ E : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ (n : ℕ) (x : AdicCompletion I R), AdicCompletion.evalₐ J n (E x) = e n (AdicCompletion.evalₐ I n x) := by
  have he' : ∀ {m n : ℕ} (hle : m ≤ n) (y : S ⧸ J ^ n),
      (e m).symm (Ideal.Quotient.factorPow J hle y) = Ideal.Quotient.factorPow I hle ((e n).symm y) := by
    intro m n hle y
    apply (e m).injective
    rw [RingEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply]
  let F : AdicCompletion I R →+* AdicCompletion J S :=
    AdicCompletion.liftRingHom J (fun n => (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom) (by
      intro m n hle
      ext x
      show Ideal.Quotient.factorPow J hle (e n (AdicCompletion.evalₐ I n x)) = e m (AdicCompletion.evalₐ I m x)
      rw [← he, factorPow_evalₐ])
  let G : AdicCompletion J S →+* AdicCompletion I R :=
    AdicCompletion.liftRingHom I (fun n => (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom) (by
      intro m n hle
      ext y
      show Ideal.Quotient.factorPow I hle ((e n).symm (AdicCompletion.evalₐ J n y)) =
        (e m).symm (AdicCompletion.evalₐ J m y)
      rw [← he', factorPow_evalₐ])
  have hF : ∀ n x, AdicCompletion.evalₐ J n (F x) = e n (AdicCompletion.evalₐ I n x) :=
    fun n x => AdicCompletion.evalₐ_liftRingHom J _ _ n x
  have hG : ∀ n y, AdicCompletion.evalₐ I n (G y) = (e n).symm (AdicCompletion.evalₐ J n y) :=
    fun n y => AdicCompletion.evalₐ_liftRingHom I _ _ n y
  refine ⟨RingEquiv.ofRingHom F G (RingHom.ext fun y => ?_) (RingHom.ext fun x => ?_), hF⟩
  · apply AdicCompletion.ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hF, hG, RingEquiv.apply_symm_apply, RingHom.id_apply]
  · apply AdicCompletion.ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hG, hF, RingEquiv.symm_apply_apply, RingHom.id_apply]

theorem apply_of_eq_of (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n) (E : AdicCompletion I R ≃+* AdicCompletion J S)
    (hE : ∀ (n : ℕ) (x : AdicCompletion I R), AdicCompletion.evalₐ J n (E x) = e n (AdicCompletion.evalₐ I n x))
    (θ : R → S) (hθ : ∀ (n : ℕ) (r : R), e n (Ideal.Quotient.mk (I ^ n) r) = Ideal.Quotient.mk (J ^ n) (θ r)) (r : R) :
    E (AdicCompletion.of I R r) = AdicCompletion.of J S (θ r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [hE, AdicCompletion.evalₐ_of, hθ, AdicCompletion.evalₐ_of]

end AdicIso

open AdicIso in
theorem solution
    {C : Type u} [CommRing C] (𝔪 : Ideal C) [𝔪.IsMaximal] :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) (Localization.AtPrime 𝔪) ≃+*
        AdicCompletion 𝔪 C,
      ∀ c : C, e (algebraMap (Localization.AtPrime 𝔪) _ (algebraMap C (Localization.AtPrime 𝔪) c)) =
        algebraMap C (AdicCompletion 𝔪 C) c := by
  classical
  have hmap : ∀ n : ℕ, (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪)) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) ^ n := by
    intro n
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]

  have hunit : ∀ (n : ℕ) (s : C), s ∉ 𝔪 → IsUnit (Ideal.Quotient.mk (𝔪 ^ n) s) := by
    intro n s hs
    obtain ⟨y, i, hi, hyi⟩ := (‹𝔪.IsMaximal›).exists_inv hs
    have hnil : IsNilpotent (Ideal.Quotient.mk (𝔪 ^ n) i) :=
      ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi n⟩
    have h1 : Ideal.Quotient.mk (𝔪 ^ n) y * Ideal.Quotient.mk (𝔪 ^ n) s = 1 - Ideal.Quotient.mk (𝔪 ^ n) i := by
      rw [← map_mul, eq_sub_of_add_eq hyi, map_sub, map_one]
    exact isUnit_of_mul_isUnit_right (h1 ▸ hnil.isUnit_one_sub)
  have hU : ∀ n : ℕ, Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl ≤ IsUnit.submonoid (C ⧸ 𝔪 ^ n) := by
    intro n x hx
    rw [Algebra.algebraMapSubmonoid, Submonoid.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact hunit n s hs

  let d : ∀ n : ℕ, C ⧸ 𝔪 ^ n ≃+* Localization.AtPrime 𝔪 ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) ^ n :=
    fun n =>
      (IsLocalization.atUnits (C ⧸ 𝔪 ^ n) (Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl)
          (S := Localization.AtPrime 𝔪 ⧸ (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪))) (hU n)).toRingEquiv.trans
        (Ideal.quotEquivOfEq (hmap n))
  have hd_mk : ∀ (n : ℕ) (c : C), d n (Ideal.Quotient.mk (𝔪 ^ n) c) =
      Ideal.Quotient.mk _ (algebraMap C (Localization.AtPrime 𝔪) c) := by
    intro n c
    have h := (IsLocalization.atUnits (C ⧸ 𝔪 ^ n) (Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl)
      (S := Localization.AtPrime 𝔪 ⧸ (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪))) (hU n)).commutes
      (Ideal.Quotient.mk (𝔪 ^ n) c)
    rw [Algebra.algebraMap_self, RingHom.id_apply, Ideal.Quotient.algebraMap_quotient_map_quotient] at h
    show Ideal.quotEquivOfEq (hmap n)
      (IsLocalization.atUnits (C ⧸ 𝔪 ^ n) (Algebra.algebraMapSubmonoid (C ⧸ 𝔪 ^ n) 𝔪.primeCompl)
        (S := Localization.AtPrime 𝔪 ⧸ (𝔪 ^ n).map (algebraMap C (Localization.AtPrime 𝔪))) (hU n)
        (Ideal.Quotient.mk (𝔪 ^ n) c)) = _
    rw [h, Ideal.quotEquivOfEq_mk]
  have hd : ∀ {m n : ℕ} (hle : m ≤ n) (x : C ⧸ 𝔪 ^ n),
      d m (Ideal.Quotient.factorPow 𝔪 hle x) = Ideal.Quotient.factorPow _ hle (d n x) := by
    intro m n hle x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.factor_mk, hd_mk, hd_mk, Ideal.Quotient.factor_mk]
  obtain ⟨E, hE⟩ := exists_ringEquiv 𝔪 (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) d hd
  refine ⟨E.symm, fun c => ?_⟩
  apply E.injective
  rw [RingEquiv.apply_symm_apply, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply]
  exact (apply_of_eq_of _ _ d E hE (algebraMap C (Localization.AtPrime 𝔪)) hd_mk c).symm

end S_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv
end P2MW
export P2MW.S_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv (solution)
