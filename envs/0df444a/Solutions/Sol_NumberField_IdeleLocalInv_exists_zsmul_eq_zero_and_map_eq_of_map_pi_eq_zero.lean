-- Prove2me | solution 1 for NumberField.IdeleLocalInv.exists_zsmul_eq_zero_and_map_eq_of_map_pi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/73b8c00c-eee9-5a3b-a30a-0f12b6c12016

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_IdeleLocalInvariant
import Theorems.Thm_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective
import Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleLocalInv_exists_zsmul_eq_zero_and_map_eq_of_map_pi_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    [MulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K)]
    (hact : ∀ (g : K ≃ₐ[E] K) (c : IdeleClassGroup (𝓞 K) K), g • c = D.classAct g c)

    [MulDistribMulAction (K ≃ₐ[E] K) Kˣ]
    (hactF : ∀ (g : (K ≃ₐ[E] K)) (a : Kˣ), ((g • a : Kˣ) : K) = g (a : K))
    (j : (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) ⟶ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ))
    (hj : ∀ a : Kˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a))
    (π : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (IdeleClassGroup (𝓞 K) K))
    (hπ : ∀ y : (AdeleRing (𝓞 K) K)ˣ, π.hom (Additive.ofMul y) = Additive.ofMul (QuotientGroup.mk y : IdeleClassGroup (𝓞 K) K))
    (p : ℕ) [Fact p.Prime]
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2) (k : ℕ) (hx : (p ^ k : ℤ) • x = 0)
    (hπx : (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) π 2).hom x = 0) :
    ∃ (y : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) 2) (k' : ℕ), (p ^ k' : ℤ) • y = 0 ∧
      (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) j 2).hom y = x := by
  classical
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  haveI : Finite (K ≃ₐ[E] K) := inferInstance
  have hp : p.Prime := Fact.out

  have hjinj : Function.Injective j.hom := by
    intro a b h
    have h' : j.hom (Additive.ofMul (Additive.toMul a)) = j.hom (Additive.ofMul (Additive.toMul b)) := h
    rw [hj, hj] at h'
    have h2 := Additive.ofMul.injective h'
    exact Additive.toMul.injective (Units.map_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 K) (K := K)) h2)
  have hπsurj : Function.Surjective π.hom := by
    intro c
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul c)
    refine ⟨Additive.ofMul y, ?_⟩
    rw [hπ, hy]
    rfl
  have hexact : ∀ y : (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ).V, π.hom y = 0 ↔ y ∈ Set.range j.hom := by
    intro y
    have hy : π.hom y = Additive.ofMul (QuotientGroup.mk (Additive.toMul y) : IdeleClassGroup (𝓞 K) K) := hπ (Additive.toMul y)
    rw [hy]
    constructor
    · intro h0
      have h1 : (QuotientGroup.mk (Additive.toMul y) : IdeleClassGroup (𝓞 K) K) = 1 := Additive.ofMul.injective h0
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨a, ha⟩ := h1
      refine ⟨Additive.ofMul a, ?_⟩
      rw [hj, ha]
      rfl
    · rintro ⟨b, rfl⟩
      have h1 : (QuotientGroup.mk (Additive.toMul (j.hom b)) : IdeleClassGroup (𝓞 K) K) = 1 := by
        rw [QuotientGroup.eq_one_iff]
        refine ⟨Additive.toMul b, ?_⟩
        exact (congrArg Additive.toMul (hj (Additive.toMul b))).symm
      rw [h1]
      rfl
  obtain ⟨y₀, hy₀⟩ := groupCohomology.exists_map_eq_of_map_eq_zero_of_injective_of_surjective j π hjinj hπsurj hexact 2 x hπx

  haveI : (⊥ : Subgroup (K ≃ₐ[E] K)).FiniteIndex := Subgroup.finiteIndex_of_finite
  obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul (⊥ : Subgroup (K ≃ₐ[E] K))
    (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) 2
  have hkill : (Nat.card (K ≃ₐ[E] K) : ℤ) • y₀ = 0 := by
    have hZ := isZero_groupCohomology_succ_of_subsingleton
      (Rep.res (⊥ : Subgroup (K ≃ₐ[E] K)).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ)) 1
    have h0 : (groupCohomology.map (⊥ : Subgroup (K ≃ₐ[E] K)).subtype (𝟙 (Rep.res (⊥ : Subgroup (K ≃ₐ[E] K)).subtype
        (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ))) 2).hom y₀ = 0 := by
      have := congrArg (fun T => (ModuleCat.Hom.hom T) ((groupCohomology.map (⊥ : Subgroup (K ≃ₐ[E] K)).subtype
        (𝟙 (Rep.res (⊥ : Subgroup (K ≃ₐ[E] K)).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ))) 2).hom y₀)) (hZ.eq_of_src (𝟙 _) 0)
      simpa using this
    have h1 := hcor y₀
    rw [h0, map_zero, Subgroup.index_bot] at h1
    rw [natCast_zsmul]
    exact h1.symm

  have hN0 : Nat.card (K ≃ₐ[E] K) ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p hp.one_lt.ne'
  have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm))
  obtain ⟨u, w, huw⟩ := hcop
  refine ⟨(w * m) • y₀, a, ?_, ?_⟩
  · rw [smul_smul, show (p ^ a : ℤ) * (w * m) = w * (Nat.card (K ≃ₐ[E] K) : ℤ) by rw [hN]; push_cast; ring, ← smul_smul, hkill, zsmul_zero]
  · rw [map_zsmul, hy₀]
    have huw' : u * (p ^ k : ℤ) + w * (m : ℤ) = 1 := by push_cast at huw; exact huw
    have h2 : (u * (p ^ k : ℤ)) • x = 0 := by rw [← smul_smul, hx, zsmul_zero]
    calc (w * (m : ℤ)) • x = (u * (p ^ k : ℤ)) • x + (w * (m : ℤ)) • x := by rw [h2, zero_add]
      _ = (u * (p ^ k : ℤ) + w * (m : ℤ)) • x := (add_zsmul _ _ _).symm
      _ = x := by rw [huw', one_zsmul]

end S_NumberField_IdeleLocalInv_exists_zsmul_eq_zero_and_map_eq_of_map_pi_eq_zero
end P2MW
export P2MW.S_NumberField_IdeleLocalInv_exists_zsmul_eq_zero_and_map_eq_of_map_pi_eq_zero (solution)
