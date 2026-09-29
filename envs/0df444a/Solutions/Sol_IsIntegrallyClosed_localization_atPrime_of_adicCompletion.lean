-- Prove2me | solution 1 for IsIntegrallyClosed.localization_atPrime_of_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/214e19c1-8b3b-559a-8835-cbd0a6dbabef

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_localization_atPrime_of_adicCompletion

set_option autoImplicit false

open IsLocalRing Polynomial

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] (𝔪 : Ideal R) [𝔪.IsMaximal]
    [IsDomain (AdicCompletion 𝔪 R)] [IsIntegrallyClosed (AdicCompletion 𝔪 R)] :
    IsIntegrallyClosed (Localization.AtPrime 𝔪) := by
  classical
  have hfg : 𝔪.FG := IsNoetherian.noetherian _

  set J : Ideal (AdicCompletion 𝔪 R) := 𝔪.map (algebraMap R (AdicCompletion 𝔪 R)) with hJ
  have hker1 : ∀ x : (AdicCompletion 𝔪 R), AdicCompletion.evalₐ 𝔪 1 x = 0 ↔ x ∈ J := by
    intro x
    rw [hJ]
    have h1 : x ∈ 𝔪.map (algebraMap R (AdicCompletion 𝔪 R)) ↔ x ∈ ((𝔪 ^ 1) • ⊤ : Submodule R (AdicCompletion 𝔪 R)) := by
      rw [pow_one, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    rw [h1, AdicCompletion.pow_smul_top_eq_ker_eval hfg, LinearMap.mem_ker]
    constructor
    · intro h0
      rw [← AdicCompletion.factor_evalₐ_eq_eval 𝔪 x (le_of_eq (by rw [smul_eq_mul, Ideal.mul_top])), h0, map_zero]
    · intro h0
      rw [← AdicCompletion.factor_eval_eq_evalₐ 𝔪 x (le_of_eq (by rw [smul_eq_mul, Ideal.mul_top])), h0, map_zero]
  haveI : (𝔪 ^ 1).IsMaximal := by rw [pow_one]; infer_instance
  have hJker : J = RingHom.ker (AdicCompletion.evalₐ 𝔪 1).toRingHom := by
    ext x; rw [RingHom.mem_ker]; exact (hker1 x).symm
  haveI hJmax : J.IsMaximal := by
    letI : Field (R ⧸ 𝔪 ^ 1) := Ideal.Quotient.field (𝔪 ^ 1)
    rw [hJker]
    exact RingHom.ker_isMaximal_of_surjective _ (AdicCompletion.surjective_evalₐ 𝔪 1)
  haveI : IsAdicComplete J (AdicCompletion 𝔪 R) :=
    (IsAdicComplete.map_algebraMap_iff (I := 𝔪) (S := AdicCompletion 𝔪 R) (M := AdicCompletion 𝔪 R)).mpr (AdicCompletion.isAdicComplete hfg)
  haveI hRhloc : IsLocalRing (AdicCompletion 𝔪 R) := isLocalRing_of_isAdicComplete_maximal J
  have hmaxRh : maximalIdeal (AdicCompletion 𝔪 R) = J := (IsLocalRing.eq_maximalIdeal hJmax).symm
  have hunit : ∀ s ∈ 𝔪.primeCompl, IsUnit (algebraMap R (AdicCompletion 𝔪 R) s) := by
    intro s hs
    by_contra hnu
    have h1 : algebraMap R (AdicCompletion 𝔪 R) s ∈ J := hmaxRh ▸ (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← hker1, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, Algebra.algebraMap_self, RingHom.id_apply,
      Ideal.Quotient.eq_zero_iff_mem, pow_one] at h1
    exact hs h1

  let j : (Localization.AtPrime 𝔪) →+* (AdicCompletion 𝔪 R) := IsLocalization.lift (M := 𝔪.primeCompl) (g := algebraMap R (AdicCompletion 𝔪 R)) (fun y => hunit y y.2)
  have hj : ∀ r : R, j (algebraMap R (Localization.AtPrime 𝔪) r) = algebraMap R (AdicCompletion 𝔪 R) r := fun r => IsLocalization.lift_eq _ r
  letI algSRh : Algebra (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R) := j.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R) := IsScalarTower.of_algebraMap_eq fun r => (hj r).symm
  haveI : Module.Flat (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R) := (Module.flat_iff_of_isLocalization (Localization.AtPrime 𝔪) 𝔪.primeCompl (AdicCompletion 𝔪 R)).mpr inferInstance
  haveI : IsLocalHom (algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R)) := by
    constructor
    intro x hx
    by_contra hnu
    have hxm : x ∈ maximalIdeal (Localization.AtPrime 𝔪) := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← Localization.AtPrime.map_eq_maximalIdeal] at hxm
    have : algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R) x ∈ (𝔪.map (algebraMap R (Localization.AtPrime 𝔪))).map (algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R)) := Ideal.mem_map_of_mem _ hxm
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, ← hJ, ← hmaxRh] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this hx
  haveI : Module.FaithfullyFlat (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hcontr : ∀ I : Ideal (Localization.AtPrime 𝔪), (I.map (algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R))).comap (algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R)) = I :=
    fun I => Ideal.comap_map_eq_self_of_faithfullyFlat I
  have hjinj : Function.Injective (algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R)) := FaithfulSMul.algebraMap_injective (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R)

  have hjR : ∀ r : R, algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R) (algebraMap R (Localization.AtPrime 𝔪) r) =
      algebraMap R (AdicCompletion 𝔪 R) r := hj
  refine (isIntegrallyClosed_iff (FractionRing R)).mpr fun {x} hx => ?_

  have hRinj : Function.Injective (algebraMap R (AdicCompletion 𝔪 R)) := by
    intro a b hab
    have := hjinj (a₁ := algebraMap R _ a) (a₂ := algebraMap R _ b) (by rw [hjR, hjR]; exact hab)
    exact IsLocalization.injective (Localization.AtPrime 𝔪) 𝔪.primeCompl_le_nonZeroDivisors this
  have hunits : ∀ y : nonZeroDivisors R, IsUnit (((algebraMap (AdicCompletion 𝔪 R) (FractionRing (AdicCompletion 𝔪 R))).comp
      (algebraMap R (AdicCompletion 𝔪 R))) y) := by
    intro y
    apply IsUnit.mk0
    rw [RingHom.comp_apply, map_ne_zero_iff _ (IsFractionRing.injective (AdicCompletion 𝔪 R) (FractionRing (AdicCompletion 𝔪 R))),
      map_ne_zero_iff _ hRinj]
    exact nonZeroDivisors.ne_zero y.2
  let jK : FractionRing R →+* FractionRing (AdicCompletion 𝔪 R) :=
    IsLocalization.lift (M := nonZeroDivisors R)
      (g := (algebraMap (AdicCompletion 𝔪 R) (FractionRing (AdicCompletion 𝔪 R))).comp (algebraMap R (AdicCompletion 𝔪 R))) hunits
  have hjKR : ∀ r : R, jK (algebraMap R (FractionRing R) r) =
      algebraMap (AdicCompletion 𝔪 R) (FractionRing (AdicCompletion 𝔪 R)) (algebraMap R (AdicCompletion 𝔪 R) r) :=
    fun r => IsLocalization.lift_eq _ r
  have hcomm : (algebraMap (AdicCompletion 𝔪 R) (FractionRing (AdicCompletion 𝔪 R))).comp
      (algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R)) = jK.comp (algebraMap (Localization.AtPrime 𝔪) (FractionRing R)) := by
    apply IsLocalization.ringHom_ext 𝔪.primeCompl
    ext r
    simp only [RingHom.comp_apply]
    rw [hjR, ← IsScalarTower.algebraMap_apply R (Localization.AtPrime 𝔪) (FractionRing R), hjKR]
  have hjK : ∀ s : Localization.AtPrime 𝔪, jK (algebraMap (Localization.AtPrime 𝔪) (FractionRing R) s) =
      algebraMap (AdicCompletion 𝔪 R) (FractionRing (AdicCompletion 𝔪 R)) (algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R) s) :=
    fun s => (congrArg (fun φ : Localization.AtPrime 𝔪 →+* _ => φ s) hcomm).symm

  have hint : IsIntegral (AdicCompletion 𝔪 R) (jK x) := by
    obtain ⟨p, hpm, hpx⟩ := hx
    refine ⟨p.map (algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R)), hpm.map _, ?_⟩
    rw [← aeval_def] at hpx ⊢
    rw [← map_aeval_eq_aeval_map hcomm, hpx, map_zero]
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing (AdicCompletion 𝔪 R))).mp inferInstance hint

  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Localization.AtPrime 𝔪) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hjb0 : algebraMap (AdicCompletion 𝔪 R) (FractionRing (AdicCompletion 𝔪 R)) (algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R) b) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective (AdicCompletion 𝔪 R) (FractionRing (AdicCompletion 𝔪 R))), map_ne_zero_iff _ hjinj]
    exact hb0
  have hca : c * algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R) b = algebraMap (Localization.AtPrime 𝔪) (AdicCompletion 𝔪 R) a := by
    apply IsFractionRing.injective (AdicCompletion 𝔪 R) (FractionRing (AdicCompletion 𝔪 R))
    rw [map_mul, hc, map_div₀, hjK, hjK, div_mul_cancel₀ _ hjb0]
  have hab : a ∈ Ideal.span {b} := by
    rw [← hcontr (Ideal.span {b}), Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨c, by rw [mul_comm, hca]⟩
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hab
  refine ⟨d, ?_⟩
  rw [eq_div_iff ((map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime 𝔪) (FractionRing R))).mpr hb0), ← map_mul, hd]

end S_IsIntegrallyClosed_localization_atPrime_of_adicCompletion
end P2MW
export P2MW.S_IsIntegrallyClosed_localization_atPrime_of_adicCompletion (solution)
