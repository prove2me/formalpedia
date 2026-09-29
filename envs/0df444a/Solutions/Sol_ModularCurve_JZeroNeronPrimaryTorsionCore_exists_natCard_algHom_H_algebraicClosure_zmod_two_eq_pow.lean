-- Prove2me | solution 1 for ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b9c98835-54a2-55d4-80d9-74c602f8cc63

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow
open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring

set_option autoImplicit false

noncomputable section

namespace H34DN

section TF
variable (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ)

theorem htf : ∀ s : ℤ, s ≠ 0 → ∀ y : C.H m, (s : C.H m) * y = 0 → y = 0 := by
  have hflat : @Module.Flat ℤ (C.H m) _ _ (AddCommGroup.toIntModule (C.H m)) := by
    convert C.instFlat_H m
  intro s hs y hy
  have hreg := @Module.Flat.isSMulRegular_of_nonZeroDivisors ℤ (C.H m) _ _
    (AddCommGroup.toIntModule (C.H m)) s (mem_nonZeroDivisors_of_ne_zero hs) hflat
  refine hreg ?_
  change s • y = s • (0 : C.H m)
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_zero, hy]

end TF

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

section Conv
variable (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ)

def Dmap (n : ℕ) : C.H m →ₐ[ℤ] C.H m :=
  ((WithConv.toConv (AlgHom.id ℤ (C.H m))) ^ n).ofConv

theorem comp_convOne {K : Type*} [CommRing K] [Algebra ℤ K] (φ : C.H m →ₐ[ℤ] K) :
    φ.comp ((1 : WithConv (C.H m →ₐ[ℤ] C.H m)).ofConv)
      = (1 : WithConv (C.H m →ₐ[ℤ] K)).ofConv := by
  rw [AlgHom.convOne_def, AlgHom.convOne_def, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    ← AlgHom.comp_assoc]
  congr 1
  ext

theorem toConv_pow_eq {K : Type*} [CommRing K] [Algebra ℤ K] (φ : C.H m →ₐ[ℤ] K) (n : ℕ) :
    (WithConv.toConv φ) ^ n = WithConv.toConv (φ.comp (Dmap p A hA C m n)) := by
  induction n with
  | zero =>
      simp only [Dmap, pow_zero]
      rw [comp_convOne p A hA C m φ, WithConv.toConv_ofConv]
  | succ n ih =>
      simp only [Dmap] at ih ⊢
      rw [pow_succ, pow_succ, ih]
      rw [AlgHom.comp_convMul_distrib φ
        ((WithConv.toConv (AlgHom.id ℤ (C.H m))) ^ n) (WithConv.toConv (AlgHom.id ℤ (C.H m)))]
      rw [WithConv.toConv_ofConv, WithConv.ofConv_toConv, AlgHom.comp_id]

theorem two_pow_nsmul_eq_zero (x : JZero p)
    (hx : x ∈ eisensteinPrimaryTorsionBar p 2 m) :
    (2 ^ m) • x = 0 := by
  have h1 : ((2 : ℤ) ^ m) • x = 0 := hx.1
  rw [← natCast_zsmul]
  exact_mod_cast h1

theorem qbar_point_pow_eq_one (φ : WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ)) :
    φ ^ (2 ^ m) = 1 := by
  classical
  set E := C.genericPoints m with hEdef
  have hadd := C.genericConv m
  have h1 : E 1 = 0 := by
    have h := hadd 1 1
    rw [one_mul] at h
    have h' : E 1 + 0 = E 1 + E 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have hpow : ∀ (n : ℕ) (ψ : WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ)),
      E (ψ ^ n) = n • E ψ := by
    intro n ψ
    induction n with
    | zero => rw [pow_zero, h1, zero_nsmul]
    | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]
  have htor : (2 ^ m) • E φ = 0 := by
    have hmem := (E φ).2
    have hc : ((2 ^ m) • ((E φ : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p)) = 0 :=
      two_pow_nsmul_eq_zero p m ((E φ : ↥(eisensteinPrimaryTorsionBar p 2 m)) : JZero p) hmem
    apply Subtype.ext
    push_cast
    exact hc
  have : E (φ ^ (2 ^ m)) = E 1 := by rw [hpow, htor, h1]
  exact E.injective this

theorem dmap_sub_counit_nilpotent (x : C.H m) :
    IsNilpotent (Dmap p A hA C m (2 ^ m) x
      - algebraMap ℤ (C.H m) (Bialgebra.counitAlgHom ℤ (C.H m) x)) := by
  classical
  apply isNilpotent_of_forall_ringHom_apply_eq_zero (htf p A hA C m)
  intro g
  set φ : C.H m →ₐ[ℤ] AlgebraicClosure ℚ :=
    { g with commutes' := fun r => by rw [eq_intCast, eq_intCast]; exact map_intCast g r }
    with hφdef
  have hφ : WithConv.toConv (φ.comp (Dmap p A hA C m (2 ^ m)))
      = (1 : WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ)) := by
    rw [← toConv_pow_eq p A hA C m φ (2 ^ m)]
    exact qbar_point_pow_eq_one p A hA C m (WithConv.toConv φ)
  have hφ' : φ.comp (Dmap p A hA C m (2 ^ m))
      = (1 : WithConv (C.H m →ₐ[ℤ] AlgebraicClosure ℚ)).ofConv := by
    rw [← hφ, WithConv.ofConv_toConv]
  have hpt : φ (Dmap p A hA C m (2 ^ m) x)
      = algebraMap ℤ (AlgebraicClosure ℚ) (Bialgebra.counitAlgHom ℤ (C.H m) x) := by
    have h := congrArg (fun f : C.H m →ₐ[ℤ] AlgebraicClosure ℚ => f x) hφ'
    simp only [AlgHom.comp_apply] at h
    rw [h, AlgHom.convOne_def, WithConv.ofConv_toConv, AlgHom.comp_apply, Algebra.ofId_apply]
  have hgφ : g (Dmap p A hA C m (2 ^ m) x) = φ (Dmap p A hA C m (2 ^ m) x) := rfl
  have hint : g (algebraMap ℤ (C.H m) (Bialgebra.counitAlgHom ℤ (C.H m) x))
      = algebraMap ℤ (AlgebraicClosure ℚ) (Bialgebra.counitAlgHom ℤ (C.H m) x) := by
    rw [eq_intCast (algebraMap ℤ (C.H m)), map_intCast,
      eq_intCast (algebraMap ℤ (AlgebraicClosure ℚ))]
  rw [map_sub, hgφ, hpt, hint, sub_self]

theorem field_point_pow_eq_one {L : Type*} [Field L] [Algebra ℤ L]
    (ψ : WithConv (C.H m →ₐ[ℤ] L)) : ψ ^ (2 ^ m) = 1 := by
  classical
  have hψpt : ∀ x : C.H m, ψ.ofConv (Dmap p A hA C m (2 ^ m) x)
      = algebraMap ℤ L (Bialgebra.counitAlgHom ℤ (C.H m) x) := by
    intro x
    have hnil := dmap_sub_counit_nilpotent p A hA C m x
    have h0 : ψ.ofConv (Dmap p A hA C m (2 ^ m) x
        - algebraMap ℤ (C.H m) (Bialgebra.counitAlgHom ℤ (C.H m) x)) = 0 :=
      (hnil.map (ψ.ofConv : C.H m →+* L)).eq_zero
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    exact ψ.ofConv.commutes (Bialgebra.counitAlgHom ℤ (C.H m) x)
  have hcomp : ψ.ofConv.comp (Dmap p A hA C m (2 ^ m))
      = (1 : WithConv (C.H m →ₐ[ℤ] L)).ofConv := by
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply, hψpt x, AlgHom.convOne_def, WithConv.ofConv_toConv,
      AlgHom.comp_apply, Algebra.ofId_apply]
  calc ψ ^ (2 ^ m) = (WithConv.toConv ψ.ofConv) ^ (2 ^ m) := by rw [WithConv.toConv_ofConv]
    _ = WithConv.toConv (ψ.ofConv.comp (Dmap p A hA C m (2 ^ m))) :=
        toConv_pow_eq p A hA C m ψ.ofConv (2 ^ m)
    _ = WithConv.toConv ((1 : WithConv (C.H m →ₐ[ℤ] L)).ofConv) := by rw [hcomp]
    _ = 1 := WithConv.toConv_ofConv _

end Conv

section F
open scoped TensorProduct
p2m_open "Polynomial AlgebraicGeometry.Polynomial"
variable (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ)

omit [Fact p.Prime] in
theorem exists_prime_ne : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p := by
  by_cases h : p = 2
  · exact ⟨3, Nat.prime_three, by omega⟩
  · exact ⟨2, Nat.prime_two, fun h2 => h h2.symm⟩

theorem finite_ratBaseChange : Module.Finite ℚ (ℚ ⊗[ℤ] C.H m) := by
  obtain ⟨ℓ, hℓ, hℓp⟩ := exists_prime_ne p
  haveI := C.ff_finite m ℓ hℓ hℓp
  exact Module.Finite.equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ (GaloisRep.ratLocalizedAt ℓ) ℚ ℚ (C.H m))

theorem tmul_one_injective : Function.Injective (fun h : C.H m => (1 : ℚ) ⊗ₜ[ℤ] h) := by
  haveI hflat : @Module.Flat ℤ (C.H m) _ _ (AddCommGroup.toIntModule (C.H m)) := by
    convert C.instFlat_H m
  have hf : Function.Injective (Algebra.linearMap ℤ ℚ) := by
    rw [Algebra.coe_linearMap]
    exact (algebraMap ℤ ℚ).injective_int
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := C.H m)
    (Algebra.linearMap ℤ ℚ) hf
  intro x y hxy
  have h1 : ((Algebra.linearMap ℤ ℚ).rTensor (C.H m)) ((1 : ℤ) ⊗ₜ[ℤ] x)
      = ((Algebra.linearMap ℤ ℚ).rTensor (C.H m)) ((1 : ℤ) ⊗ₜ[ℤ] y) := by
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact hxy
  have h2 := hinj h1
  have h3 := congrArg (TensorProduct.lid ℤ (C.H m)) h2
  rw [TensorProduct.lid_tmul, TensorProduct.lid_tmul, one_smul, one_smul] at h3
  exact h3

theorem exists_int_poly_aeval_eq_zero (y : C.H m) :
    ∃ P : ℤ[X], P ≠ 0 ∧ aeval y P = 0 := by
  classical
  haveI := finite_ratBaseChange p A hA C m
  set f : C.H m →ₗ[ℤ] C.H m := (AddMonoidHom.mulLeft y).toIntLinearMap with hfdef
  set T : Module.End ℚ (ℚ ⊗[ℤ] C.H m) := f.baseChange ℚ with hTdef
  have hT : ∀ (a : ℚ) (h : C.H m), T (a ⊗ₜ[ℤ] h) = a ⊗ₜ[ℤ] (y * h) := by
    intro a h
    rw [hTdef, LinearMap.baseChange_tmul]
    rfl
  have hTpow : ∀ (n : ℕ) (h : C.H m),
      (T ^ n) ((1 : ℚ) ⊗ₜ[ℤ] h) = (1 : ℚ) ⊗ₜ[ℤ] (y ^ n * h) := by
    intro n
    induction n with
    | zero => intro h; rw [pow_zero, pow_zero, one_mul, Module.End.one_apply]
    | succ n ih => intro h; rw [pow_succ, Module.End.mul_apply, hT, ih, pow_succ, mul_assoc]
  have bridge : ∀ (c : ℤ) (z : C.H m),
      ((c : ℚ)) ⊗ₜ[ℤ] z = (1 : ℚ) ⊗ₜ[ℤ] ((c : C.H m) * z) := by
    intro c z
    rw [← zsmul_eq_mul, TensorProduct.tmul_smul, ← Int.smul_one_eq_cast, TensorProduct.smul_tmul']
  have key : ∀ R : ℤ[X],
      (eval₂ ((algebraMap ℚ (Module.End ℚ (ℚ ⊗[ℤ] C.H m))).comp (algebraMap ℤ ℚ)) T R)
          ((1 : ℚ) ⊗ₜ[ℤ] (1 : C.H m))
        = (1 : ℚ) ⊗ₜ[ℤ] (eval₂ (Int.castRingHom (C.H m)) y R) := by
    intro R
    induction R using Polynomial.induction_on' with
    | add R₁ R₂ h₁ h₂ =>
        rw [eval₂_add, eval₂_add, LinearMap.add_apply, h₁, h₂, TensorProduct.tmul_add]
    | monomial n c =>
        rw [eval₂_monomial, eval₂_monomial, Module.End.mul_apply, hTpow, mul_one,
          RingHom.comp_apply, Module.algebraMap_end_apply, TensorProduct.smul_tmul', smul_eq_mul,
          mul_one, eq_intCast]
        exact bridge c (y ^ n)
  obtain ⟨Q, hQm, hQT⟩ := LinearMap.exists_monic_and_aeval_eq_zero (R := ℚ) T
  have hQT' : eval₂ (algebraMap ℚ (Module.End ℚ (ℚ ⊗[ℤ] C.H m))) T Q = 0 := by
    rwa [aeval_def] at hQT
  obtain ⟨b, -, hbQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) Q
  have hmapP : (IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q).map (algebraMap ℤ ℚ)
      = Polynomial.C (b : ℚ) * Q := by
    rw [hbQ]
    ext n
    rw [Polynomial.coeff_smul, Polynomial.coeff_C_mul, zsmul_eq_mul]
  have hP : eval₂ ((algebraMap ℚ (Module.End ℚ (ℚ ⊗[ℤ] C.H m))).comp (algebraMap ℤ ℚ)) T
      (IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q) = 0 := by
    rw [← eval₂_map, hmapP,
      eval₂_mul_noncomm _ _ (fun k => Algebra.commute_algebraMap_left (Q.coeff k) T),
      hQT', mul_zero]
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q, ?_, ?_⟩
  · intro hP0
    exact hQm.ne_zero ((IsFractionRing.integerNormalization_eq_zero_iff (A := ℤ) (K := ℚ)).mp hP0)
  · have h0 := congrArg (fun E : Module.End ℚ (ℚ ⊗[ℤ] C.H m) => E ((1 : ℚ) ⊗ₜ[ℤ] (1 : C.H m))) hP
    try simp only [] at h0
    rw [key, LinearMap.zero_apply] at h0
    have h1 : eval₂ (Int.castRingHom (C.H m)) y
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) Q) = 0 := by
      apply tmul_one_injective p A hA C m
      show (1 : ℚ) ⊗ₜ[ℤ] _ = (1 : ℚ) ⊗ₜ[ℤ] (0 : C.H m)
      rw [TensorProduct.tmul_zero]
      exact h0
    rwa [aeval_def, show algebraMap ℤ (C.H m) = Int.castRingHom (C.H m) from RingHom.ext_int _ _]

theorem exists_poly_map_ne_zero (y : C.H m) :
    ∃ Q : ℤ[X], Q.map (algebraMap ℤ (AlgebraicClosure (ZMod 2))) ≠ 0 ∧ aeval y Q = 0 := by
  obtain ⟨P, hP0, hPy⟩ := exists_int_poly_aeval_eq_zero p A hA C m y
  refine ⟨P.primPart, ?_, ?_⟩
  · intro hmap
    have hdvd : ∀ n : ℕ, (2 : ℤ) ∣ P.primPart.coeff n := by
      intro n
      have hc : (algebraMap ℤ (AlgebraicClosure (ZMod 2))) (P.primPart.coeff n) = 0 := by
        rw [← Polynomial.coeff_map, hmap, Polynomial.coeff_zero]
      rw [eq_intCast] at hc
      exact_mod_cast (CharP.intCast_eq_zero_iff (AlgebraicClosure (ZMod 2)) 2 _).mp hc
    have hC : (Polynomial.C (2 : ℤ)) ∣ P.primPart := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd
    have hu : IsUnit (2 : ℤ) :=
      (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp P.isPrimitive_primPart) 2 hC
    rcases Int.isUnit_iff.mp hu with h | h <;> omega
  · have h := hPy
    rw [P.eq_C_content_mul_primPart, map_mul, Polynomial.aeval_C,
      show algebraMap ℤ (C.H m) = Int.castRingHom (C.H m) from RingHom.ext_int _ _] at h
    exact htf p A hA C m P.content (fun hc => hP0 (Polynomial.content_eq_zero_iff.mp hc)) _ h

theorem finite_points : Finite (C.H m →ₐ[ℤ] AlgebraicClosure (ZMod 2)) := by
  classical
  obtain ⟨s, hs⟩ := (C.instFiniteType_H m).out
  choose Q hQmap hQy using exists_poly_map_ne_zero p A hA C m
  let ev : (C.H m →ₐ[ℤ] AlgebraicClosure (ZMod 2)) →
      (∀ y : ↥s, ↥((Q y.1).rootSet (AlgebraicClosure (ZMod 2)))) :=
    fun ψ y => ⟨ψ y.1, by
      rw [Polynomial.mem_rootSet']
      exact ⟨hQmap y.1, by rw [Polynomial.aeval_algHom_apply, hQy, map_zero]⟩⟩
  refine Finite.of_injective ev ?_
  intro ψ₁ ψ₂ h
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro y hy
  exact congrArg
    (fun g : (∀ y : ↥s, ↥((Q y.1).rootSet (AlgebraicClosure (ZMod 2)))) =>
      ((g ⟨y, hy⟩ : ↥((Q y).rootSet (AlgebraicClosure (ZMod 2)))) : AlgebraicClosure (ZMod 2))) h

end F

section Endgame
variable (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ)

theorem card_solution {L : Type*} [Field L] [Algebra ℤ L]
    (hT : ∀ ψ : WithConv (C.H m →ₐ[ℤ] L), ψ ^ (2 ^ m) = 1)
    (hF : Finite (C.H m →ₐ[ℤ] L)) :
    ∃ a : ℕ, Nat.card (C.H m →ₐ[ℤ] L) = 2 ^ a := by
  classical
  have _ := hF
  haveI hfW : Finite (WithConv (C.H m →ₐ[ℤ] L)) :=
    Finite.of_equiv _ (WithConv.equiv (C.H m →ₐ[ℤ] L)).symm
  have hcard : Nat.card (C.H m →ₐ[ℤ] L)
      = Nat.card (WithConv (C.H m →ₐ[ℤ] L)) :=
    (Nat.card_congr (WithConv.equiv (C.H m →ₐ[ℤ] L))).symm
  letI : Group (WithConv (C.H m →ₐ[ℤ] L)) :=
    { (inferInstance : Monoid (WithConv (C.H m →ₐ[ℤ] L))) with
      inv := fun x => x ^ (2 ^ m - 1)
      inv_mul_cancel := fun x => by
        show x ^ (2 ^ m - 1) * x = 1
        rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
        exact hT x }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 (WithConv (C.H m →ₐ[ℤ] L)) := fun g => ⟨m, hT g⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  exact ⟨n, hcard.trans hn⟩

end Endgame

end H34DN

end

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p 2 A hA) (m : ℕ) :
    ∃ a : ℕ, Nat.card (C.H m →ₐ[ℤ] AlgebraicClosure (ZMod 2)) = 2 ^ a :=
  H34DN.card_solution p A hA C m
    (fun ψ => H34DN.field_point_pow_eq_one p A hA C m ψ)
    (H34DN.finite_points p A hA C m)

end S_ModularCurve_JZeroNeronPrimaryTorsionCore_exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow
end P2MW
export P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_exists_natCard_algHom_H_algebraicClosure_zmod_two_eq_pow (solution)
