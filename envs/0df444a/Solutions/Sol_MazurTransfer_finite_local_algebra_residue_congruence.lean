-- Prove2me | solution 1 for MazurTransfer.finite_local_algebra_residue_congruence
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T09:47:46.532282+00:00
-- url     : https://prove2.me/submissions/3acf0604-2e78-43b1-abeb-192286e5e07a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a finite local algebra over a local base has the same
residue kernel for any map killing a generator of the base maximal ideal.
A chosen augmentation then controls reduction of every algebra point.
Named downstream consumer: PadicConnectedHopfInertiaFixedPoints, reducing
an actual connected Hopf point to its counit before the inertia argument.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.FiniteLocalAlgebraResidueCongruence
variable {R A : Type*} [CommRing R] [IsLocalRing R]
  [CommRing A] [Algebra R A] [Module.Finite R A] [IsLocalRing A]
variable (t : R) (hmax : IsLocalRing.maximalIdeal R = Ideal.span {t})
include hmax

theorem kernel_eq_maximalIdeal_of_uniformizer
    {K : Type*} [CommRing K] [IsDomain K] (φ : A →+* K)
    (ht : φ (algebraMap R A t) = 0) :
    RingHom.ker φ = IsLocalRing.maximalIdeal A := by
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : IsLocalRing.maximalIdeal R ≤ (RingHom.ker φ).comap (algebraMap R A) := by
    rw [hmax, Ideal.span_le, Set.singleton_subset_iff]
    exact ht
  have hne : (RingHom.ker φ).comap (algebraMap R A) ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have hcomap : ((RingHom.ker φ).comap (algebraMap R A)).IsMaximal := by
    rw [← (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne hle]
    exact IsLocalRing.maximalIdeal.isMaximal R
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) _ hcomap)

theorem value_sub_augmentation_mem_maximalIdeal
    {B : Type*} [CommRing B] [IsLocalRing B] [Algebra R B]
    (ε : A →ₐ[R] R) (f : A →ₐ[R] B)
    (ht : algebraMap R B t ∈ IsLocalRing.maximalIdeal B) (a : A) :
    f a - algebraMap R B (ε a) ∈ IsLocalRing.maximalIdeal B := by
  let φ₁ : A →+* IsLocalRing.ResidueField B := (IsLocalRing.residue B).comp f.toRingHom
  let φ₂ : A →+* IsLocalRing.ResidueField B :=
    ((IsLocalRing.residue B).comp (algebraMap R B)).comp ε.toRingHom
  have h₁ : φ₁ (algebraMap R A t) = 0 := by
    change IsLocalRing.residue B (f (algebraMap R A t)) = 0
    rw [f.commutes]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ht
  have h₂ : φ₂ (algebraMap R A t) = 0 := by
    change IsLocalRing.residue B (algebraMap R B (ε (algebraMap R A t))) = 0
    rw [ε.commutes, Algebra.algebraMap_self_apply]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ht
  have hk : RingHom.ker φ₁ = RingHom.ker φ₂ :=
    (kernel_eq_maximalIdeal_of_uniformizer t hmax φ₁ h₁).trans
      (kernel_eq_maximalIdeal_of_uniformizer t hmax φ₂ h₂).symm
  have hx : a - algebraMap R A (ε a) ∈ RingHom.ker φ₂ := by
    change φ₂ (a - algebraMap R A (ε a)) = 0
    simp [φ₂]
  rw [← hk] at hx
  change IsLocalRing.residue B (f (a - algebraMap R A (ε a))) = 0 at hx
  rw [map_sub, f.commutes] at hx
  exact (IsLocalRing.residue_eq_zero_iff _).mp hx

end MazurTransfer.FiniteLocalAlgebraResidueCongruence
end

theorem solution {R A B : Type*} [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra R B]
    (t : R) (hmax : IsLocalRing.maximalIdeal R = Ideal.span {t})
    (ε : A →ₐ[R] R) (f : A →ₐ[R] B)
    (ht : algebraMap R B t ∈ IsLocalRing.maximalIdeal B) (a : A) :
    f a - algebraMap R B (ε a) ∈ IsLocalRing.maximalIdeal B := by
  exact MazurTransfer.FiniteLocalAlgebraResidueCongruence.value_sub_augmentation_mem_maximalIdeal
    t hmax ε f ht a
#print axioms solution
