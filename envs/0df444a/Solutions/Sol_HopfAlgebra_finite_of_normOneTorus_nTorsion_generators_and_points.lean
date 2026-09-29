-- Prove2me | solution 1 for HopfAlgebra.finite_of_normOneTorus_nTorsion_generators_and_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/68ef8a1e-0fe2-5434-a93b-3d45fe6ded9a

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finite_of_normOneTorus_nTorsion_generators_and_points

set_option maxHeartbeats 8000000

open scoped TensorProduct

theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (hnsq : ¬ IsSquare c)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (A : Type) [CommRing A] [HopfAlgebra K A] (u' v' : A)
    (hgen : Algebra.adjoin K {u', v'} = ⊤)
    (hrel : u' ^ 2 - algebraMap K A c * v' ^ 2 = 1)
    (hn : ∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1)
    (hlift : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      (w + z * δ) ^ n = 1 →
      ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) :
    Module.Finite K A := by
  classical

  haveI hft : Algebra.FiniteType K A :=
    ⟨⟨{u', v'}, by rw [Finset.coe_insert, Finset.coe_singleton]; exact hgen⟩⟩

  haveI hred : IsReduced A := HopfAlgebra.isReduced_of_finiteType_of_charZero K A

  have hδne : δ ≠ 0 := fun h => hc ((algebraMap K (AlgebraicClosure K)).injective
    (by rw [← hδ, h, mul_zero, map_zero]))
  have h2ne : (2 : AlgebraicClosure K) ≠ 0 := two_ne_zero
  have hrel_φ : ∀ (φ : A →ₐ[K] AlgebraicClosure K),
      φ u' ^ 2 - algebraMap K (AlgebraicClosure K) c * φ v' ^ 2 = 1 := fun φ => by
    have := congrArg φ hrel
    simp only [map_sub, map_mul, map_pow, map_one, AlgHom.commutes] at this
    exact this
  let raw : (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun f => f u' + f v' * δ
  have hprod : ∀ f, raw f * (f u' - f v' * δ) = 1 := fun f => by
    show (f u' + f v' * δ) * (f u' - f v' * δ) = 1
    have h1 := hrel_φ f
    linear_combination h1 - f v' ^ 2 * hδ
  have hraw_ne : ∀ f, raw f ≠ 0 := fun f h => by
    have := hprod f; rw [h, zero_mul] at this; exact one_ne_zero this.symm
  have hraw_inj : Function.Injective raw := by
    intro f g h
    have hrawc : f u' - f v' * δ = g u' - g v' * δ :=
      mul_left_cancel₀ (hraw_ne g) ((h ▸ hprod f).trans (hprod g).symm)
    have hu : f u' = g u' := by
      have heq : 2 * f u' = 2 * g u' := by
        have h' := congrArg₂ (· + ·) h hrawc
        simp only [raw] at h'; linear_combination h'
      exact mul_left_cancel₀ h2ne heq
    have hv : f v' = g v' := by
      have h2δ : (2 : AlgebraicClosure K) * δ ≠ 0 := mul_ne_zero h2ne hδne
      have heq : (2 * δ) * f v' = (2 * δ) * g v' := by
        have h' := congrArg₂ (· - ·) h hrawc
        simp only [raw] at h'; linear_combination h'
      exact mul_left_cancel₀ h2δ heq
    obtain ⟨f₀, _, huniq⟩ := hlift (f u') (f v') (hrel_φ f) (hn f)
    exact (huniq f ⟨rfl, rfl⟩).trans (huniq g ⟨hu.symm, hv.symm⟩).symm
  haveI hFinHom : Finite (A →ₐ[K] AlgebraicClosure K) := by
    let toR : (A →ₐ[K] AlgebraicClosure K) → rootsOfUnity n (AlgebraicClosure K) :=
      fun f => ⟨Units.mk0 _ (hraw_ne f), by
        rw [mem_rootsOfUnity]; ext; push_cast; exact hn f⟩
    have htoR_inj : Function.Injective toR := by
      intro f g h
      have h1 : (Units.mk0 (raw f) (hraw_ne f) : AlgebraicClosure K)
              = (Units.mk0 (raw g) (hraw_ne g) : AlgebraicClosure K) :=
        congrArg (fun x : (AlgebraicClosure K)ˣ => (x : AlgebraicClosure K))
          (Subtype.ext_iff.mp h)
      simp only [Units.val_mk0] at h1
      exact hraw_inj h1
    exact Finite.of_injective toR htoR_inj

  have hmax_to_hom : ∀ m : Ideal A, m.IsMaximal →
      ∃ f : A →ₐ[K] AlgebraicClosure K, RingHom.ker f = m := by
    intro m hm
    haveI : m.IsMaximal := hm
    letI : Field (A ⧸ m) := Ideal.Quotient.field m
    haveI : Algebra.FiniteType K (A ⧸ m) :=
      Algebra.FiniteType.of_surjective
        (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
    haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
    haveI : Algebra.IsAlgebraic K (A ⧸ m) := Algebra.IsAlgebraic.of_finite K (A ⧸ m)
    let e : (A ⧸ m) →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
    refine ⟨e.comp (Ideal.Quotient.mkₐ K m), le_antisymm ?_ ?_⟩
    · intro a ha
      rw [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply] at ha
      have hinje : Function.Injective e := RingHom.injective e.toRingHom
      have : Ideal.Quotient.mkₐ K m a = 0 := hinje (by rw [ha, map_zero])
      exact (Ideal.Quotient.eq_zero_iff_mem).mp this
    · intro a ha
      rw [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply]
      have : Ideal.Quotient.mkₐ K m a = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr ha
      rw [this, map_zero]

  haveI hFinMax : Finite {m : Ideal A // m.IsMaximal} := by
    choose φ hφ using fun m : {m : Ideal A // m.IsMaximal} => hmax_to_hom m.1 m.2
    exact Finite.of_injective φ
      (fun m₁ m₂ h => Subtype.ext (by rw [← hφ m₁, ← hφ m₂, h]))

  haveI hjacA : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K) (B := A)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out' ⊥ (Ideal.isRadical_bot_iff.mpr hred)

  let ψ : A →ₐ[K] (∀ m : {m : Ideal A // m.IsMaximal}, A ⧸ m.1) :=
    Pi.algHom K _ (fun m => Ideal.Quotient.mkₐ K m.1)
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hall : ∀ m : {m : Ideal A // m.IsMaximal}, a ∈ m.1 := fun m => by
      have := congrFun ha m
      simp only [ψ, Pi.algHom_apply, Pi.zero_apply] at this
      exact (Ideal.Quotient.eq_zero_iff_mem).mp this
    have hmem : a ∈ (⊥ : Ideal A).jacobson := by
      unfold Ideal.jacobson
      refine Ideal.mem_sInf.mpr ?_
      rintro J ⟨-, hJmax⟩
      exact hall ⟨J, hJmax⟩
    rw [hjac] at hmem
    exact hmem
  haveI : ∀ m : {m : Ideal A // m.IsMaximal}, Module.Finite K (A ⧸ m.1) := fun m => by
    haveI : m.1.IsMaximal := m.2
    letI : Field (A ⧸ m.1) := Ideal.Quotient.field m.1
    haveI : Algebra.FiniteType K (A ⧸ m.1) :=
      Algebra.FiniteType.of_surjective
        (Ideal.Quotient.mkₐ K m.1) (Ideal.Quotient.mkₐ_surjective K m.1)
    exact finite_of_finite_type_of_isJacobsonRing K (A ⧸ m.1)
  haveI : Module.Finite K (∀ m : {m : Ideal A // m.IsMaximal}, A ⧸ m.1) := Module.Finite.pi
  exact Module.Finite.of_injective ψ.toLinearMap hψinj

end S_HopfAlgebra_finite_of_normOneTorus_nTorsion_generators_and_points
end P2MW
export P2MW.S_HopfAlgebra_finite_of_normOneTorus_nTorsion_generators_and_points (solution)
