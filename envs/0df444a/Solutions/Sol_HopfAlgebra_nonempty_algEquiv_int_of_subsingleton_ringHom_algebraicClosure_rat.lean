-- Prove2me | solution 1 for HopfAlgebra.nonempty_algEquiv_int_of_subsingleton_ringHom_algebraicClosure_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/45b25a75-ef07-55e4-a9fd-aa0abb0a3872

import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_nonempty_algEquiv_int_of_subsingleton_ringHom_algebraicClosure_rat

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace CARTDEngine

theorem htf_flat {R : Type*} [CommRing R] [Algebra ℤ R] (hfl : Module.Flat ℤ R) :
    ∀ s : ℤ, s ≠ 0 → ∀ y : R, (s : R) * y = 0 → y = 0 := by
  have hflat : @Module.Flat ℤ R _ _ (AddCommGroup.toIntModule R) := by
    convert hfl
  intro s hs y hy
  have hreg := @Module.Flat.isSMulRegular_of_nonZeroDivisors ℤ R _ _
    (AddCommGroup.toIntModule R) s (mem_nonZeroDivisors_of_ne_zero hs) hflat
  refine hreg ?_
  change s • y = s • (0 : R)
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_zero, hy]

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem isNilpotent_of_forall_ringHom_apply_eq_zero
    {R : Type*} [CommRing R] [Algebra ℤ R] [hft : Algebra.FiniteType ℤ R]
    (htf : ∀ s : ℤ, s ≠ 0 → ∀ y : R, (s : R) * y = 0 → y = 0)
    (x : R) (hvan : ∀ g : R →+* AlgebraicClosure ℚ, g x = 0) : IsNilpotent x := by
  classical
  obtain ⟨n, F, hF⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  set Fr : MvPolynomial (Fin n) ℤ →+* R := (F : MvPolynomial (Fin n) ℤ →+* R) with hFrdef
  have hFr : Function.Surjective Fr := hF
  obtain ⟨P, hP⟩ := hFr x
  set J : Ideal (MvPolynomial (Fin n) ℤ) := RingHom.ker Fr with hJdef
  set ι : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℚ :=
    algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) with hιdef
  set I : Ideal (MvPolynomial (Fin n) ℚ) := J.map ι with hIdef
  have hA : ι P ∈ MvPolynomial.vanishingIdeal ℚ
      (MvPolynomial.zeroLocus (AlgebraicClosure ℚ) I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro v hv
    rw [MvPolynomial.mem_zeroLocus_iff] at hv
    set ev : MvPolynomial (Fin n) ℤ →+* AlgebraicClosure ℚ :=
      (MvPolynomial.aeval v : MvPolynomial (Fin n) ℚ →ₐ[ℚ] AlgebraicClosure ℚ).toRingHom.comp ι
      with hevdef
    have hJ : ∀ a ∈ J, ev a = 0 := fun a ha => hv (ι a) (Ideal.mem_map_of_mem ι ha)
    set gv : R →+* AlgebraicClosure ℚ := (Ideal.Quotient.lift J ev hJ).comp
      (RingHom.quotientKerEquivOfSurjective hFr).symm.toRingHom with hgvdef
    have hgv : ∀ a, gv (Fr a) = ev a := by
      intro a
      rw [hgvdef, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    calc (MvPolynomial.aeval v) (ι P) = ev P := rfl
      _ = gv (Fr P) := (hgv P).symm
      _ = gv x := by rw [hP]
      _ = 0 := hvan gv
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hA
  obtain ⟨k, hk⟩ := hA
  rw [← map_pow] at hk
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, has⟩ := (IsLocalization.mem_map_algebraMap_iff
    ((nonZeroDivisors ℤ).map (MvPolynomial.C : ℤ →+* MvPolynomial (Fin n) ℤ))
    (MvPolynomial (Fin n) ℚ)).1 hk
  obtain ⟨s0, hs0, rfl⟩ := Submonoid.mem_map.1 hs
  have hinj : Function.Injective ι := by
    rw [hιdef, MvPolynomial.algebraMap_def]
    exact MvPolynomial.map_injective _ ((algebraMap ℤ ℚ).injective_int)
  have hPk : P ^ k * MvPolynomial.C s0 = a := by
    apply hinj
    rw [map_mul]
    exact has
  have hJmem : P ^ k * MvPolynomial.C s0 ∈ J := hPk ▸ ha
  have h0 : Fr (P ^ k * MvPolynomial.C s0) = 0 := hJmem
  have hC : Fr (MvPolynomial.C s0) = (s0 : R) := by
    rw [hFrdef, AlgHom.coe_toRingHom, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, eq_intCast]
  rw [map_mul, map_pow, hP, hC, mul_comm] at h0
  exact ⟨k, htf s0 (nonZeroDivisors.ne_zero hs0) _ h0⟩

theorem includeRight_injective {R : Type*} [CommRing R] [Algebra ℤ R]
    (hfl : Module.Flat ℤ R) :
    Function.Injective (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := R)) := by
  letI _instMod : Module ℤ R := Algebra.toModule
  haveI : Module.Flat ℤ R := by
    convert hfl
    exact Subsingleton.elim _ _
  have hcast : Function.Injective (Algebra.linearMap ℤ ℚ) := by
    intro a b h
    have h' : (a : ℚ) = (b : ℚ) := by
      simpa [Algebra.linearMap_apply] using h
    exact_mod_cast h'
  have hr : Function.Injective (LinearMap.rTensor R (Algebra.linearMap ℤ ℚ)) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R) _ hcast
  intro a b hab
  have key : ∀ z : R, Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := R) z =
      (LinearMap.rTensor R (Algebra.linearMap ℤ ℚ)) ((TensorProduct.lid ℤ R).symm z) := by
    intro z
    simp [Algebra.TensorProduct.includeRight_apply, TensorProduct.lid_symm_apply,
      LinearMap.rTensor_tmul, Algebra.linearMap_apply]
  rw [key a, key b] at hab
  exact (TensorProduct.lid ℤ R).symm.injective (hr hab)

end CARTDEngine

theorem solution
    (R : Type) [CommRing R] [HopfAlgebra ℤ R] [Module.Flat ℤ R] [Algebra.FiniteType ℤ R]
    (huniq : ∀ f g : R →+* AlgebraicClosure ℚ, f = g) :
    Nonempty (R ≃ₐ[ℤ] ℤ) := by

  have hnil : ∀ x : R, Bialgebra.counitAlgHom ℤ R x = 0 → IsNilpotent x := by
    intro x hx
    refine CARTDEngine.isNilpotent_of_forall_ringHom_apply_eq_zero
      (CARTDEngine.htf_flat ‹Module.Flat ℤ R›) x ?_
    intro g
    have hg : g = (algebraMap ℤ (AlgebraicClosure ℚ)).comp
        (Bialgebra.counitAlgHom ℤ R).toRingHom := huniq _ _
    rw [hg]
    show algebraMap ℤ (AlgebraicClosure ℚ) (Bialgebra.counitAlgHom ℤ R x) = 0
    rw [hx, map_zero]

  have hinjR := CARTDEngine.includeRight_injective (R := R) ‹Module.Flat ℤ R›

  letI _instMod : Module ℤ R := Algebra.toModule
  haveI : Algebra.FiniteType ℚ (ℚ ⊗[ℤ] R) := inferInstance

  haveI hred : IsReduced (ℚ ⊗[ℤ] R) :=
    HopfAlgebra.isReduced_of_finiteType_of_charZero ℚ (ℚ ⊗[ℤ] R)

  have hker : ∀ x : R, Bialgebra.counitAlgHom ℤ R x = 0 → x = 0 := by
    intro x hx
    have h1 : IsNilpotent (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := R) x) :=
      (hnil x hx).map (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := R))
    apply hinjR
    rw [h1.eq_zero, map_zero]

  have hinj : Function.Injective (Bialgebra.counitAlgHom ℤ R) := by
    intro a b hab
    have h0 : Bialgebra.counitAlgHom ℤ R (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hker _ h0)
  have hsurj : Function.Surjective (Bialgebra.counitAlgHom ℤ R) := fun n =>
    ⟨algebraMap ℤ R n, (Bialgebra.counitAlgHom ℤ R).commutes n⟩
  exact ⟨AlgEquiv.ofBijective (Bialgebra.counitAlgHom ℤ R) ⟨hinj, hsurj⟩⟩

end

end S_HopfAlgebra_nonempty_algEquiv_int_of_subsingleton_ringHom_algebraicClosure_rat
end P2MW
export P2MW.S_HopfAlgebra_nonempty_algEquiv_int_of_subsingleton_ringHom_algebraicClosure_rat (solution)
