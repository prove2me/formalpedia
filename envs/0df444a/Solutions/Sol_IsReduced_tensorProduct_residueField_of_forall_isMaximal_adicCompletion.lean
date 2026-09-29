-- Prove2me | solution 1 for IsReduced.tensorProduct_residueField_of_forall_isMaximal_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/382655d0-395f-53d8-b788-45163862c5c1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsReduced_tensorProduct_residueField_of_forall_isMaximal_adicCompletion

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem Ws33.RFF.mem_map_of_one_tmul_eq_zero {A : Type} [CommRing A] [IsLocalRing A]
    {B : Type} [CommRing B] [Algebra A B] (b : B)
    (hb : ((1 : ResidueField A) ⊗ₜ[A] b : ResidueField A ⊗[A] B) = 0) :
    b ∈ (maximalIdeal A).map (algebraMap A B) := by
  classical
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)
  have h1 : e (Ideal.Quotient.mk _ b) = (1 : ResidueField A) ⊗ₜ[A] b := Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk B (maximalIdeal A) b
  have h2 : (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)) b) = 0 := by
    apply e.injective
    rw [h1, map_zero]
    exact hb
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A]
    {C : Type} [CommRing C] [Algebra A C] [IsNoetherianRing C]
    (h : ∀ x : Ideal C, x.IsMaximal →
      (maximalIdeal A).map (algebraMap A C) ≤ x →
      IsReduced (ResidueField A ⊗[A] AdicCompletion x C)) :
    IsReduced (ResidueField A ⊗[A] C) := by
  classical
  let ι : C →+* ResidueField A ⊗[A] C := (Algebra.TensorProduct.includeRight : C →ₐ[A] ResidueField A ⊗[A] C).toRingHom
  have hιapp : ∀ c : C, ι c = (1 : ResidueField A) ⊗ₜ[A] c := fun c => rfl
  set K : Ideal C := (maximalIdeal A).map (algebraMap A C) with hK

  have hι : Function.Surjective ι := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul k c =>
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective k
      refine ⟨a • c, ?_⟩
      rw [hιapp, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      rfl
    | add x y hx hy =>
      obtain ⟨cx, rfl⟩ := hx; obtain ⟨cy, rfl⟩ := hy
      exact ⟨cx + cy, map_add _ _ _⟩
  have hιA : ∀ a ∈ maximalIdeal A, ι (algebraMap A C a) = 0 := by
    intro a ha
    rw [hιapp, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    change IsLocalRing.residue A a ⊗ₜ[A] (1 : C) = 0
    rw [(IsLocalRing.residue_eq_zero_iff a).mpr ha, TensorProduct.zero_tmul]
  have hKι : K.map ι = ⊥ := by
    rw [hK, Ideal.map_map, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    exact hιA a ha
  haveI hNS : IsNoetherianRing (ResidueField A ⊗[A] C) := isNoetherianRing_of_surjective C _ ι hι

  refine ⟨fun s hs => ?_⟩
  obtain ⟨c, rfl⟩ := hι s
  obtain ⟨n, hn⟩ := hs

  have hcnK : c ^ n ∈ K := by
    have : ι (c ^ n) = 0 := by rw [map_pow]; exact hn
    exact Ws33.RFF.mem_map_of_one_tmul_eq_zero (c ^ n) this

  have hmem : ∀ (𝔫 : Ideal (ResidueField A ⊗[A] C)), 𝔫.IsMaximal → ∀ m : ℕ, ι c ∈ 𝔫 ^ m := by
    intro 𝔫 h𝔫 m
    haveI := h𝔫
    set x : Ideal C := 𝔫.comap ι with hxdef
    have hx : x.IsMaximal := Ideal.comap_isMaximal_of_surjective ι hι
    have hxA : (maximalIdeal A).map (algebraMap A C) ≤ x := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      show ι (algebraMap A C a) ∈ 𝔫
      rw [hιA a ha]; exact 𝔫.zero_mem

    let Cx := AdicCompletion x C
    let θ : C →+* ResidueField A ⊗[A] Cx :=
      (Algebra.TensorProduct.includeRight : Cx →ₐ[A] ResidueField A ⊗[A] Cx).toRingHom.comp (algebraMap C Cx)
    have hθapp : ∀ c' : C, θ c' = (1 : ResidueField A) ⊗ₜ[A] (algebraMap C Cx c') := fun c' => rfl
    have hθA : ∀ a ∈ maximalIdeal A, θ (algebraMap A C a) = 0 := by
      intro a ha
      rw [hθapp, ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      change IsLocalRing.residue A a ⊗ₜ[A] (1 : Cx) = 0
      rw [(IsLocalRing.residue_eq_zero_iff a).mpr ha, TensorProduct.zero_tmul]
    have hθK : K ≤ RingHom.ker θ := by
      rw [hK, Ideal.map_le_iff_le_comap]
      intro a ha
      exact hθA a ha

    have hθc : θ c = 0 := by
      haveI := h x hx hxA
      have : IsNilpotent (θ c) := ⟨n, by rw [← map_pow]; exact hθK hcnK⟩
      exact this.eq_zero

    have hcompA : (algebraMap C Cx).comp (algebraMap A C) = algebraMap A Cx := RingHom.ext fun a => rfl
    have hcx : algebraMap C Cx c ∈ K.map (algebraMap C Cx) := by
      have := Ws33.RFF.mem_map_of_one_tmul_eq_zero (algebraMap C Cx c) (by rw [← hθapp]; exact hθc)
      rw [hK, Ideal.map_map, hcompA]; exact this

    have hcm : c ∈ K ⊔ x ^ m := by
      have h1 : (AdicCompletion.evalₐ x m).toRingHom (algebraMap C Cx c) ∈
          (K.map (algebraMap C Cx)).map (AdicCompletion.evalₐ x m).toRingHom :=
        Ideal.mem_map_of_mem _ hcx
      have hcomp : (AdicCompletion.evalₐ x m).toRingHom.comp (algebraMap C Cx) = Ideal.Quotient.mk (x ^ m) := by
        ext c'
        show AdicCompletion.evalₐ x m (AdicCompletion.of x C (algebraMap C C c')) = Ideal.Quotient.mk (x ^ m) c'
        rw [AdicCompletion.evalₐ_of]
        rfl
      rw [Ideal.map_map, hcomp, show (AdicCompletion.evalₐ x m).toRingHom (algebraMap C Cx c) = Ideal.Quotient.mk (x ^ m) c from
        RingHom.congr_fun hcomp c] at h1
      obtain ⟨k, hk, hkc⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
      have hck : c - k ∈ x ^ m := by
        rw [← Ideal.Quotient.eq, eq_comm]; exact hkc
      have : c = k + (c - k) := by ring
      rw [this]
      exact Submodule.add_mem_sup hk hck

    have : ι c ∈ (K ⊔ x ^ m).map ι := Ideal.mem_map_of_mem _ hcm
    rwa [Ideal.map_sup, hKι, bot_sup_eq, Ideal.map_pow, Ideal.map_comap_of_surjective ι hι] at this

  apply eq_zero_of_localization
  intro 𝔫 h𝔫
  haveI := h𝔫
  have hall : ∀ m : ℕ, algebraMap _ (Localization.AtPrime 𝔫) (ι c) ∈ (maximalIdeal (Localization.AtPrime 𝔫)) ^ m := by
    intro m
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hmem 𝔫 h𝔫 m)
  have hinf : algebraMap _ (Localization.AtPrime 𝔫) (ι c) ∈ ⨅ m : ℕ, (maximalIdeal (Localization.AtPrime 𝔫)) ^ m :=
    Ideal.mem_iInf.mpr hall
  haveI : IsNoetherianRing (Localization.AtPrime 𝔫) := IsLocalization.isNoetherianRing 𝔫.primeCompl _ hNS
  have hbot : ⨅ m : ℕ, (maximalIdeal (Localization.AtPrime 𝔫)) ^ m = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (R := Localization.AtPrime 𝔫) (I := maximalIdeal (Localization.AtPrime 𝔫))
      (maximalIdeal.isMaximal _).ne_top
  rw [hbot, Ideal.mem_bot] at hinf
  exact hinf

end S_IsReduced_tensorProduct_residueField_of_forall_isMaximal_adicCompletion
end P2MW
export P2MW.S_IsReduced_tensorProduct_residueField_of_forall_isMaximal_adicCompletion (solution)
