-- Prove2me | solution 1 for NumberField.LevelArith.exists_ringEquiv_monoidHom_equiv_heightOneSpectrum_levelField_of_le_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d9b84bc3-b9d6-52de-aad4-9da466f43ef7

import Mathlib
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_PlaceDecompositionAction

import Theorems.Thm_NumberField_LevelArith_levelGal_surjective_and_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_ringEquiv_monoidHom_equiv_heightOneSpectrum_levelField_of_le_le

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open IsDedekindDomain NumberField NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

namespace Rebundle

noncomputable section

open scoped Pointwise

section Setup

variable (L L₁ F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL₁ : L ≤ L₁) (hL₁F : L₁ ≤ F) (hLF : L ≤ F)

set_option quotPrecheck false in
local notation "K" => ↥(levelField L F hLF)
set_option quotPrecheck false in
local notation "K₁" => ↥(levelField L₁ F hL₁F)
set_option quotPrecheck false in
local notation "G" => (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))
set_option quotPrecheck false in
local notation "G₁" => (↥(levelField L₁ F hL₁F) ≃ₐ[↥L₁] ↥(levelField L₁ F hL₁F))

def θ : K₁ ≃+* K := (levelFieldEquiv L₁ F hL₁F).symm.trans (levelFieldEquiv L F hLF)

@[scoped simp] theorem coe_θ (x : K₁) : ((θ L L₁ F hL₁F hLF x : K) : AlgebraicClosure ℚ) = x := rfl

@[scoped simp] theorem coe_θ_symm (y : K) : (((θ L L₁ F hL₁F hLF).symm y : K₁) : AlgebraicClosure ℚ) = y := rfl

theorem θ_symm_algebraMap (c : ↥L) :
    (θ L L₁ F hL₁F hLF).symm (algebraMap ↥L K c) = algebraMap ↥L₁ K₁ ⟨c, hLL₁ c.2⟩ :=
  Subtype.ext rfl

def ιFun (σ : G₁) : G :=
  AlgEquiv.ofRingEquiv (f := ((θ L L₁ F hL₁F hLF).symm.trans σ.toRingEquiv).trans (θ L L₁ F hL₁F hLF))
    (fun c => by
      change θ L L₁ F hL₁F hLF (σ ((θ L L₁ F hL₁F hLF).symm (algebraMap ↥L K c))) = algebraMap ↥L K c
      rw [θ_symm_algebraMap L L₁ F hLL₁ hL₁F hLF, AlgEquiv.commutes]
      exact Subtype.ext rfl)

theorem ιFun_apply (σ : G₁) (x : K) :
    ιFun L L₁ F hLL₁ hL₁F hLF σ x = θ L L₁ F hL₁F hLF (σ ((θ L L₁ F hL₁F hLF).symm x)) := rfl

def ι : G₁ →* G where
  toFun := ιFun L L₁ F hLL₁ hL₁F hLF
  map_one' := AlgEquiv.ext fun x => by
    rw [ιFun_apply, AlgEquiv.one_apply, AlgEquiv.one_apply, RingEquiv.apply_symm_apply]
  map_mul' σ τ := AlgEquiv.ext fun x => by
    rw [AlgEquiv.mul_apply, ιFun_apply, ιFun_apply, ιFun_apply, AlgEquiv.mul_apply,
      RingEquiv.symm_apply_apply]

theorem ι_apply (σ : G₁) (x : K) :
    ι L L₁ F hLL₁ hL₁F hLF σ x = θ L L₁ F hL₁F hLF (σ ((θ L L₁ F hL₁F hLF).symm x)) := rfl

theorem ι_injective : Function.Injective (ι L L₁ F hLL₁ hL₁F hLF) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  have := AlgEquiv.congr_fun h (θ L L₁ F hL₁F hLF x)
  rw [ι_apply, ι_apply, RingEquiv.symm_apply_apply] at this
  exact (θ L L₁ F hL₁F hLF).injective this

theorem mem_range_ι_iff (τ : G) :
    τ ∈ (ι L L₁ F hLL₁ hL₁F hLF).range ↔
      ∀ y : ↥L₁, τ (θ L L₁ F hL₁F hLF (algebraMap ↥L₁ K₁ y)) = θ L L₁ F hL₁F hLF (algebraMap ↥L₁ K₁ y) := by
  constructor
  · rintro ⟨σ, rfl⟩ y
    rw [ι_apply, RingEquiv.symm_apply_apply, AlgEquiv.commutes]
  · intro hτ
    refine ⟨AlgEquiv.ofRingEquiv
      (f := ((θ L L₁ F hL₁F hLF).trans τ.toRingEquiv).trans (θ L L₁ F hL₁F hLF).symm) (fun y => ?_), ?_⟩
    · change (θ L L₁ F hL₁F hLF).symm (τ (θ L L₁ F hL₁F hLF (algebraMap ↥L₁ K₁ y))) = algebraMap ↥L₁ K₁ y
      rw [hτ, RingEquiv.symm_apply_apply]
    · apply AlgEquiv.ext
      intro x
      rw [ι_apply]
      change θ L L₁ F hL₁F hLF ((θ L L₁ F hL₁F hLF).symm (τ (θ L L₁ F hL₁F hLF ((θ L L₁ F hL₁F hLF).symm x)))) = τ x
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

abbrev Θ : 𝓞 K₁ ≃+* 𝓞 K := NumberField.RingOfIntegers.mapRingEquiv (θ L L₁ F hL₁F hLF)

def e : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁) ≃ IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  toFun w₁ := IsDedekindDomain.HeightOneSpectrum.comap ((Θ L L₁ F hL₁F hLF).symm : 𝓞 K →+* 𝓞 K₁)
    (Θ L L₁ F hL₁F hLF).symm.surjective w₁
  invFun w := IsDedekindDomain.HeightOneSpectrum.comap ((Θ L L₁ F hL₁F hLF) : 𝓞 K₁ →+* 𝓞 K)
    (Θ L L₁ F hL₁F hLF).surjective w
  left_inv w₁ := IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => by
    simp only [IsDedekindDomain.HeightOneSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe,
      RingEquiv.symm_apply_apply])
  right_inv w := IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => by
    simp only [IsDedekindDomain.HeightOneSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe,
      RingEquiv.apply_symm_apply])

theorem mem_e_asIdeal_iff (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) (y : 𝓞 K) :
    y ∈ (e L L₁ F hL₁F hLF w₁).asIdeal ↔ (Θ L L₁ F hL₁F hLF).symm y ∈ w₁.asIdeal := Iff.rfl

theorem Θ_mem_e_asIdeal_iff (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) (x : 𝓞 K₁) :
    Θ L L₁ F hL₁F hLF x ∈ (e L L₁ F hL₁F hLF w₁).asIdeal ↔ x ∈ w₁.asIdeal := by
  rw [mem_e_asIdeal_iff, RingEquiv.symm_apply_apply]

theorem e_asIdeal_eq_map (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) :
    (e L L₁ F hL₁F hLF w₁).asIdeal = w₁.asIdeal.map ((Θ L L₁ F hL₁F hLF : 𝓞 K₁ ≃+* 𝓞 K) : 𝓞 K₁ →+* 𝓞 K) := by
  rw [Ideal.map_comap_of_equiv]
  rfl

theorem Θ_mem_e_asIdeal_pow_iff (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) (x : 𝓞 K₁) (n : ℕ) :
    Θ L L₁ F hL₁F hLF x ∈ (e L L₁ F hL₁F hLF w₁).asIdeal ^ n ↔ x ∈ w₁.asIdeal ^ n := by
  rw [e_asIdeal_eq_map, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap,
    RingEquiv.symm_apply_apply]

private theorem _root_.Rebundle.mem_placesOverPrimes_iff (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) (S : Set Nat.Primes) :
    w₁ ∈ NumberField.LevelArith.placesOverPrimes K₁ S ↔
      e L L₁ F hL₁F hLF w₁ ∈ NumberField.LevelArith.placesOverPrimes K S := by
  simp only [NumberField.LevelArith.mem_placesOverPrimes_iff]
  refine exists_congr fun q => and_congr_right fun _ => ?_
  rw [← Θ_mem_e_asIdeal_iff L L₁ F hL₁F hLF w₁, map_natCast]

p2m_export "Rebundle" "mem_placesOverPrimes_iff"

section Val

variable [FiniteDimensional ℚ ↥F]

theorem intValuation_e (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) (r : 𝓞 K₁) :
    (e L L₁ F hL₁F hLF w₁).intValuation (Θ L L₁ F hL₁F hLF r) = w₁.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [map_zero, Valuation.map_zero, Valuation.map_zero]
  · have hr' : Θ L L₁ F hL₁F hLF r ≠ 0 := (map_ne_zero_iff _ (Θ L L₁ F hL₁F hLF).injective).mpr hr
    apply le_antisymm
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, w₁.intValuation r = WithZero.exp (-(n : ℤ)) := ⟨_, w₁.intValuation_if_neg hr⟩
      rw [hn, IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, Θ_mem_e_asIdeal_pow_iff,
        ← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (e L L₁ F hL₁F hLF w₁).intValuation (Θ L L₁ F hL₁F hLF r) = WithZero.exp (-(n : ℤ)) :=
        ⟨_, (e L L₁ F hL₁F hLF w₁).intValuation_if_neg hr'⟩
      rw [hn, IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, ← Θ_mem_e_asIdeal_pow_iff L L₁ F hL₁F hLF,
        ← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]

theorem valuation_e (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) (x : K₁) :
    (e L L₁ F hL₁F hLF w₁).valuation K (θ L L₁ F hL₁F hLF x) = w₁.valuation K₁ x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K₁) x
  have h1 : ∀ c : 𝓞 K₁, θ L L₁ F hL₁F hLF (algebraMap (𝓞 K₁) K₁ c) = algebraMap (𝓞 K) K (Θ L L₁ F hL₁F hLF c) :=
    fun c => rfl
  rw [map_div₀, map_div₀, map_div₀, h1, h1, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, intValuation_e, intValuation_e]

theorem mem_decomp_iff_forall {E M : Type} [Field E] [Field M] [NumberField M] [Algebra E M]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) (σ : M ≃ₐ[E] M) :
    σ ∈ NumberField.PlaceDecomp.decomp E M w ↔ ∀ x : M, (w.valuation M (σ.symm x) ≤ 1 ↔ w.valuation M x ≤ 1) := by
  rw [NumberField.PlaceDecomp.decomp, ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff,
    SetLike.ext_iff]
  refine forall_congr' fun x => ?_
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Valuation.mem_valuationSubring_iff,
    Valuation.mem_valuationSubring_iff]
  rfl

theorem ι_mem_decomp_iff (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) (σ : G₁) :
    ι L L₁ F hLL₁ hL₁F hLF σ ∈ NumberField.PlaceDecomp.decomp ↥L K (e L L₁ F hL₁F hLF w₁) ↔
      σ ∈ NumberField.PlaceDecomp.decomp ↥L₁ K₁ w₁ := by
  rw [mem_decomp_iff_forall, mem_decomp_iff_forall, (θ L L₁ F hL₁F hLF).surjective.forall]
  refine forall_congr' fun x => ?_
  have hs : (ι L L₁ F hLL₁ hL₁F hLF σ).symm (θ L L₁ F hL₁F hLF x) = θ L L₁ F hL₁F hLF (σ.symm x) := by
    rw [AlgEquiv.symm_apply_eq, ι_apply, RingEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply]
  rw [hs, valuation_e, valuation_e]

theorem map_decomp (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) :
    (NumberField.PlaceDecomp.decomp ↥L₁ K₁ w₁).map (ι L L₁ F hLL₁ hL₁F hLF) =
      (ι L L₁ F hLL₁ hL₁F hLF).range ⊓ NumberField.PlaceDecomp.decomp ↥L K (e L L₁ F hL₁F hLF w₁) := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, rfl⟩, (ι_mem_decomp_iff L L₁ F hLL₁ hL₁F hLF w₁ σ).2 hσ⟩
  · rintro ⟨⟨σ, rfl⟩, hτ⟩
    exact ⟨σ, (ι_mem_decomp_iff L L₁ F hLL₁ hL₁F hLF w₁ σ).1 hτ, rfl⟩

end Val

section Level

theorem ι_levelGal [IsGalois ↥L ↥(levelField L F hLF)] [IsGalois ↥L₁ ↥(levelField L₁ F hL₁F)]
    (γ : ↥L₁.fixingSubgroup) :
    ι L L₁ F hLL₁ hL₁F hLF (levelGal L₁ F hL₁F γ) =
      levelGal L F hLF ⟨(γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        IntermediateField.fixingSubgroup_antitone hLL₁ γ.2⟩ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [ι_apply, coe_θ, levelGal_apply_coe, coe_θ_symm, levelGal_apply_coe]

theorem range_ι [FiniteDimensional ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)] [IsGalois ↥L₁ ↥(levelField L₁ F hL₁F)] :
    (ι L L₁ F hLL₁ hL₁F hLF).range = (L₁.fixingSubgroup.comap L.fixingSubgroup.subtype).map (levelGal L F hLF) := by
  obtain ⟨hsurj, -⟩ := NumberField.LevelArith.levelGal_surjective_and_ker L₁ F hL₁F
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    obtain ⟨γ, rfl⟩ := hsurj σ
    exact ⟨⟨(γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hLL₁ γ.2⟩,
      γ.2, (ι_levelGal L L₁ F hLL₁ hL₁F hLF γ).symm⟩
  · rintro ⟨δ, hδ, rfl⟩
    exact ⟨levelGal L₁ F hL₁F ⟨(δ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), hδ⟩,
      ι_levelGal L L₁ F hLL₁ hL₁F hLF ⟨(δ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), hδ⟩⟩

theorem finrank_rat_levelField (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hMF : M ≤ F) :
    Module.finrank ℚ ↥(levelField M F hMF) = Module.finrank ℚ ↥F :=
  (LinearEquiv.finrank_eq
    ((levelFieldEquiv M F hMF).toAddEquiv.toLinearEquiv fun c x => map_rat_smul _ c x)).symm

theorem finrank_mul_finrank_levelField (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hMF : M ≤ F) :
    Module.finrank ℚ ↥M * Module.finrank ↥M ↥(levelField M F hMF) = Module.finrank ℚ ↥F := by
  rw [Module.finrank_mul_finrank ℚ ↥M ↥(levelField M F hMF), finrank_rat_levelField F M hMF]

theorem natCard_gal [FiniteDimensional ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)] :
    Nat.card G = Module.finrank ↥L K := by
  haveI : FiniteDimensional ↥L K := Module.Finite.of_restrictScalars_finite ℚ ↥L K
  exact IsGalois.card_aut_eq_finrank ↥L K

theorem index_range_ι [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)]
    [IsGalois ↥L₁ ↥(levelField L₁ F hL₁F)] :
    (ι L L₁ F hLL₁ hL₁F hLF).range.index = Module.finrank ↥L ↥(levelField L L₁ hLL₁) := by
  have t1 := finrank_mul_finrank_levelField F L hLF
  have t2 := finrank_mul_finrank_levelField F L₁ hL₁F
  have t3 := finrank_mul_finrank_levelField L₁ L hLL₁
  have hG : Nat.card G = Module.finrank ↥L K := natCard_gal L F hLF
  have hG₁ : Nat.card G₁ = Module.finrank ↥L₁ K₁ := natCard_gal L₁ F hL₁F
  have hR : Nat.card ↥(ι L L₁ F hLL₁ hL₁F hLF).range = Nat.card G₁ :=
    (Nat.card_congr (MonoidHom.ofInjective (ι_injective L L₁ F hLL₁ hL₁F hLF)).toEquiv).symm
  have hci := (ι L L₁ F hLL₁ hL₁F hLF).range.card_mul_index
  rw [hR, hG₁, hG] at hci
  have hL0 : 0 < Module.finrank ℚ ↥L := Module.finrank_pos
  have hd0 : 0 < Module.finrank ↥L₁ K₁ := by
    haveI : FiniteDimensional ↥L₁ K₁ := Module.Finite.of_restrictScalars_finite ℚ ↥L₁ K₁
    exact Module.finrank_pos
  have key : Module.finrank ↥L K = Module.finrank ↥L ↥(levelField L L₁ hLL₁) * Module.finrank ↥L₁ K₁ := by
    apply Nat.eq_of_mul_eq_mul_left hL0
    rw [t1, ← mul_assoc, t3, t2]
  rw [key, mul_comm] at hci
  exact Nat.eq_of_mul_eq_mul_right hd0 hci

end Level

end Setup

end

end Rebundle
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_ringEquiv_monoidHom_equiv_heightOneSpectrum_levelField_of_le_le.Rebundle"

theorem solution
    (L L₁ F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLL₁ : L ≤ L₁) (hL₁F : L₁ ≤ F) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥L₁] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F]
    [IsGalois ↥L ↥(levelField L F hLF)] [IsGalois ↥L₁ ↥(levelField L₁ F hL₁F)] :
    ∃ (θ : ↥(levelField L₁ F hL₁F) ≃+* ↥(levelField L F hLF))
      (ι : (↥(levelField L₁ F hL₁F) ≃ₐ[↥L₁] ↥(levelField L₁ F hL₁F)) →* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)))
      (e : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L₁ F hL₁F)) ≃
        IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L F hLF))),
      (∀ x : ↥(levelField L₁ F hL₁F), ((θ x : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ)) ∧
      Function.Injective ι ∧
      (∀ (σ : ↥(levelField L₁ F hL₁F) ≃ₐ[↥L₁] ↥(levelField L₁ F hL₁F)) (x : ↥(levelField L F hLF)), ι σ x = θ (σ (θ.symm x))) ∧
      (∀ τ : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF),
        τ ∈ ι.range ↔ ∀ y : ↥L₁, τ (θ (algebraMap ↥L₁ ↥(levelField L₁ F hL₁F) y)) = θ (algebraMap ↥L₁ ↥(levelField L₁ F hL₁F) y)) ∧
      ι.range.index = Module.finrank ↥L ↥(levelField L L₁ hLL₁) ∧
      (∀ γ : ↥L₁.fixingSubgroup, ι (levelGal L₁ F hL₁F γ) =
        levelGal L F hLF ⟨(γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), IntermediateField.fixingSubgroup_antitone hLL₁ γ.2⟩) ∧
      ι.range = (L₁.fixingSubgroup.comap L.fixingSubgroup.subtype).map (levelGal L F hLF) ∧
      (∀ (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L₁ F hL₁F))) (x : 𝓞 ↥(levelField L₁ F hL₁F)),
        NumberField.RingOfIntegers.mapRingEquiv θ x ∈ (e w₁).asIdeal ↔ x ∈ w₁.asIdeal) ∧
      (∀ (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L₁ F hL₁F))) (x : ↥(levelField L₁ F hL₁F)),
        (e w₁).valuation ↥(levelField L F hLF) (θ x) = w₁.valuation ↥(levelField L₁ F hL₁F) x) ∧
      (∀ w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L₁ F hL₁F)),
        (NumberField.PlaceDecomp.decomp ↥L₁ ↥(levelField L₁ F hL₁F) w₁).map ι =
          ι.range ⊓ NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (e w₁)) ∧
      (∀ (w₁ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(levelField L₁ F hL₁F))) (S : Set Nat.Primes),
        w₁ ∈ NumberField.LevelArith.placesOverPrimes ↥(levelField L₁ F hL₁F) S ↔
          e w₁ ∈ NumberField.LevelArith.placesOverPrimes ↥(levelField L F hLF) S) := by
  refine ⟨Rebundle.θ L L₁ F hL₁F hLF, Rebundle.ι L L₁ F hLL₁ hL₁F hLF, Rebundle.e L L₁ F hL₁F hLF,
    Rebundle.coe_θ L L₁ F hL₁F hLF, Rebundle.ι_injective L L₁ F hLL₁ hL₁F hLF,
    Rebundle.ι_apply L L₁ F hLL₁ hL₁F hLF, Rebundle.mem_range_ι_iff L L₁ F hLL₁ hL₁F hLF,
    Rebundle.index_range_ι L L₁ F hLL₁ hL₁F hLF, Rebundle.ι_levelGal L L₁ F hLL₁ hL₁F hLF,
    Rebundle.range_ι L L₁ F hLL₁ hL₁F hLF, Rebundle.Θ_mem_e_asIdeal_iff L L₁ F hL₁F hLF,
    Rebundle.valuation_e L L₁ F hL₁F hLF, Rebundle.map_decomp L L₁ F hLL₁ hL₁F hLF,
    Rebundle.mem_placesOverPrimes_iff L L₁ F hL₁F hLF⟩

end S_NumberField_LevelArith_exists_ringEquiv_monoidHom_equiv_heightOneSpectrum_levelField_of_le_le
end P2MW
export P2MW.S_NumberField_LevelArith_exists_ringEquiv_monoidHom_equiv_heightOneSpectrum_levelField_of_le_le (solution)
