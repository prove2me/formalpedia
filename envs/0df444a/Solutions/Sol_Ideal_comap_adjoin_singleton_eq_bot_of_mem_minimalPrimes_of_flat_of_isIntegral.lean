-- Prove2me | solution 1 for Ideal.comap_adjoin_singleton_eq_bot_of_mem_minimalPrimes_of_flat_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6982544e-1a99-5823-93ae-ad53e1492a60

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_comap_adjoin_singleton_eq_bot_of_mem_minimalPrimes_of_flat_of_isIntegral

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (A : Type) [CommRing A] [IsDomain A] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L]
    (B : Type) [CommRing B] [Algebra A B] [Module.Flat A B] (x : B)
    (hint : Algebra.IsIntegral ↥(Algebra.adjoin A ({x} : Set B)) B)
    (hni : ∀ 𝔓 ∈ (⊥ : Ideal (L ⊗[A] B)).minimalPrimes, ¬ 𝔓.IsMaximal) :
    ∀ 𝔭 ∈ (⊥ : Ideal B).minimalPrimes,
      Ideal.comap (algebraMap ↥(Algebra.adjoin A ({x} : Set B)) B) 𝔭 = ⊥ := by
  classical
  intro 𝔭 h𝔭

  set P : Subalgebra A B := Algebra.adjoin A ({x} : Set B) with hP

  letI : Algebra B (L ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (L ⊗[A] B) :=
    IsLocalization.tensorRight L (nonZeroDivisors A)
  have hM : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro b ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    have hreg : IsSMulRegular B a := Module.Flat.isSMulRegular_of_nonZeroDivisors ha
    apply hreg
    show a • c = a • (0 : B)
    rw [Algebra.smul_def, mul_comm, hc, smul_zero]
  have hinj : Function.Injective (algebraMap B (L ⊗[A] B)) := IsLocalization.injective (L ⊗[A] B) hM

  have hcomap : (⊥ : Ideal (L ⊗[A] B)).comap (algebraMap B (L ⊗[A] B)) = ⊥ := by
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have h𝔭' : 𝔭 ∈ ((⊥ : Ideal (L ⊗[A] B)).comap (algebraMap B (L ⊗[A] B))).minimalPrimes := by rwa [hcomap]
  rw [IsLocalization.minimalPrimes_comap (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (L ⊗[A] B)] at h𝔭'
  obtain ⟨𝔓, h𝔓, h𝔓𝔭⟩ := h𝔭'
  haveI h𝔓p : 𝔓.IsPrime := h𝔓.1.1

  let xT : L ⊗[A] B := algebraMap B (L ⊗[A] B) x
  let θ : Polynomial L →ₐ[L] L ⊗[A] B := Polynomial.aeval xT
  letI algT : Algebra (Polynomial L) (L ⊗[A] B) := θ.toRingHom.toAlgebra
  letI algB : Algebra (Polynomial A) B := (Polynomial.aeval x).toRingHom.toAlgebra
  have hsq : (algebraMap (Polynomial L) (L ⊗[A] B)).comp (Polynomial.mapRingHom (algebraMap A L)) =
      (algebraMap B (L ⊗[A] B)).comp (algebraMap (Polynomial A) B) := by
    apply Polynomial.ringHom_ext
    · intro a
      show θ (Polynomial.map (algebraMap A L) (Polynomial.C a)) = algebraMap B (L ⊗[A] B) (Polynomial.aeval x (Polynomial.C a))
      rw [Polynomial.map_C, Polynomial.aeval_C, Polynomial.aeval_C, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    · show θ (Polynomial.map (algebraMap A L) Polynomial.X) = algebraMap B (L ⊗[A] B) (Polynomial.aeval x Polynomial.X)
      rw [Polynomial.map_X, Polynomial.aeval_X, Polynomial.aeval_X]

  have hPr : ∀ f : Polynomial A, Polynomial.aeval x f ∈ P := fun f => by
    rw [hP, Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨f, rfl⟩
  let π : Polynomial A →+* ↥P := ((Polynomial.aeval x).codRestrict P hPr).toRingHom
  have hsurj : Function.Surjective π := by
    rintro ⟨y, hy⟩
    rw [hP, Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, rfl⟩ := hy
    exact ⟨f, rfl⟩
  have hπB : (algebraMap ↥P B).comp π = algebraMap (Polynomial A) B := RingHom.ext (fun f => rfl)

  have hintB : ∀ b : B, IsIntegral (Polynomial A) b := by
    intro b
    have hb : IsIntegral ↥P b := hint.isIntegral b
    obtain ⟨p, hpm, hpb⟩ := hb
    obtain ⟨Q, hQp, -, hQm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic (Polynomial.mem_lifts_of_surjective hsurj p) hpm
    refine ⟨Q, hQm, ?_⟩
    rw [← hπB, ← Polynomial.eval₂_map, hQp]
    exact hpb

  haveI hintT : Algebra.IsIntegral (Polynomial L) (L ⊗[A] B) := by
    refine ⟨fun t => ?_⟩
    induction t using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul l b =>
        have e : l ⊗ₜ[A] b = algebraMap L (L ⊗[A] B) l * algebraMap B (L ⊗[A] B) b := by
          show l ⊗ₜ[A] b = (l ⊗ₜ[A] (1 : B)) * ((1 : L) ⊗ₜ[A] b)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [e]
        refine IsIntegral.mul ?_ (IsIntegral.map_of_comp_eq (Polynomial.mapRingHom (algebraMap A L)) (algebraMap B (L ⊗[A] B)) hsq (hintB b))
        have e2 : algebraMap L (L ⊗[A] B) l = algebraMap (Polynomial L) (L ⊗[A] B) (Polynomial.C l) := by
          show algebraMap L (L ⊗[A] B) l = θ (Polynomial.C l)
          rw [Polynomial.aeval_C]
        rw [e2]; exact isIntegral_algebraMap
    | add s t hs ht => exact hs.add ht

  rw [eq_bot_iff]
  intro y hy
  rw [Ideal.mem_comap] at hy
  rw [Ideal.mem_bot]
  by_contra hy0
  obtain ⟨f, hf⟩ := hsurj y
  have hfy : Polynomial.aeval x f = (y : B) := by
    have := congrArg (fun z : ↥P => (z : B)) hf
    exact this
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hy0
    apply Subtype.ext
    rw [← hfy, map_zero]; rfl
  have hfL0 : Polynomial.map (algebraMap A L) f ≠ 0 := fun h =>
    hf0 (Polynomial.map_injective (algebraMap A L) (IsFractionRing.injective A L) (by rw [h, Polynomial.map_zero]))
  have hmem : algebraMap (Polynomial L) (L ⊗[A] B) (Polynomial.map (algebraMap A L) f) ∈ 𝔓 := by
    have := congrArg (fun g : Polynomial A →+* L ⊗[A] B => g f) hsq
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom] at this
    rw [this, ← Ideal.mem_comap, h𝔓𝔭]
    show Polynomial.aeval x f ∈ 𝔭
    rw [hfy]; exact hy
  have h𝔮 : (𝔓.comap (algebraMap (Polynomial L) (L ⊗[A] B))) ≠ ⊥ := by
    intro h
    have : Polynomial.map (algebraMap A L) f ∈ (𝔓.comap (algebraMap (Polynomial L) (L ⊗[A] B))) := Ideal.mem_comap.mpr hmem
    rw [h, Ideal.mem_bot] at this
    exact hfL0 this
  haveI : (𝔓.comap (algebraMap (Polynomial L) (L ⊗[A] B))).IsPrime := Ideal.comap_isPrime _ 𝔓
  have hmax : 𝔓.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔓 (IsPrime.to_maximal_ideal h𝔮)
  exact hni 𝔓 h𝔓 hmax

end S_Ideal_comap_adjoin_singleton_eq_bot_of_mem_minimalPrimes_of_flat_of_isIntegral
end P2MW
export P2MW.S_Ideal_comap_adjoin_singleton_eq_bot_of_mem_minimalPrimes_of_flat_of_isIntegral (solution)
