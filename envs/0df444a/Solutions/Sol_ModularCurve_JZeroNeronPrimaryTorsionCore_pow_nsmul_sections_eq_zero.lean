-- Prove2me | solution 1 for ModularCurve.JZeroNeronPrimaryTorsionCore.pow_nsmul_sections_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ec1b851d-8876-5aee-9103-3e4cdc940992

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace ModularCurve
p2m_export "ModularCurve" "eisensteinPrimaryTorsionBar JZeroNeronPrimaryTorsionCore JZero"
p2m_open "ModularCurve"
namespace JZeroNeronPrimaryTorsionCoreTorsion

section SEP

variable {R : Type*} [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω]
  [IsScalarTower R K Ω] {H : Type*} [CommRing H] [Algebra R H]

theorem eq_zero_of_algebraMap_mul_eq_zero [Module.Flat R H]
    (s : R) (hs : s ≠ 0) (y : H) (hy : algebraMap R H s * y = 0) : y = 0 := by
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := H)
    (mem_nonZeroDivisors_of_ne_zero hs)
  refine hreg ?_
  change s • y = s • (0 : H)
  rw [smul_zero, Algebra.smul_def, hy]

attribute [local instance] MvPolynomial.algebraMvPolynomial

include K in

theorem isNilpotent_of_forall_algHom_apply_eq_zero [hft : Algebra.FiniteType R H]
    (htf : ∀ s : R, s ≠ 0 → ∀ y : H, algebraMap R H s * y = 0 → y = 0)
    (x : H) (hvan : ∀ g : H →ₐ[R] Ω, g x = 0) : IsNilpotent x := by
  classical
  obtain ⟨n, F, hF⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  obtain ⟨P, hP⟩ := hF x
  set J : Ideal (MvPolynomial (Fin n) R) := RingHom.ker F with hJdef
  set ι : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) K :=
    algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) K) with hιdef
  set I : Ideal (MvPolynomial (Fin n) K) := J.map ι with hIdef
  have hev : ∀ (v : Fin n → Ω) (a : MvPolynomial (Fin n) R),
      MvPolynomial.aeval v (ι a) = MvPolynomial.aeval (R := R) v a := by
    intro v a
    rw [hιdef, MvPolynomial.algebraMap_def]
    exact MvPolynomial.aeval_map_algebraMap K v a
  have hA : ι P ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus Ω I) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro v hv
    rw [MvPolynomial.mem_zeroLocus_iff] at hv
    have hJ : ∀ a ∈ J, MvPolynomial.aeval (R := R) v a = 0 := fun a ha => by
      rw [← hev]; exact hv (ι a) (Ideal.mem_map_of_mem ι ha)
    set e := Ideal.quotientKerAlgEquivOfSurjective hF with hedef
    set gv : H →ₐ[R] Ω :=
      (Ideal.Quotient.liftₐ J (MvPolynomial.aeval v) hJ).comp (e.symm : H →ₐ[R] _) with hgvdef
    have hgv : ∀ a, gv (F a) = MvPolynomial.aeval (R := R) v a := by
      intro a
      have he : e.symm (F a) = Ideal.Quotient.mk J a := by
        apply e.injective
        rw [AlgEquiv.apply_symm_apply, hedef, Ideal.quotientKerAlgEquivOfSurjective_apply]
        exact (RingHom.kerLift_mk _ _).symm
      rw [hgvdef, AlgHom.comp_apply, AlgEquiv.coe_algHom, he, Ideal.Quotient.liftₐ_apply,
        Ideal.Quotient.lift_mk]
      rfl
    calc MvPolynomial.aeval v (ι P) = MvPolynomial.aeval (R := R) v P := hev v P
      _ = gv (F P) := (hgv P).symm
      _ = gv x := by rw [hP]
      _ = 0 := hvan gv
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hA
  obtain ⟨k, hk⟩ := hA
  rw [← map_pow] at hk
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, has⟩ := (IsLocalization.mem_map_algebraMap_iff
    ((nonZeroDivisors R).map (MvPolynomial.C : R →+* MvPolynomial (Fin n) R))
    (MvPolynomial (Fin n) K)).1 hk
  obtain ⟨s0, hs0, rfl⟩ := Submonoid.mem_map.1 hs
  have hinj : Function.Injective ι := by
    rw [hιdef, MvPolynomial.algebraMap_def]
    exact MvPolynomial.map_injective _ (IsFractionRing.injective R K)
  have hPk : P ^ k * MvPolynomial.C s0 = a := by
    apply hinj
    rw [map_mul]
    exact has
  have hJmem : P ^ k * MvPolynomial.C s0 ∈ J := hPk ▸ ha
  have h0 : F (P ^ k * MvPolynomial.C s0) = 0 := hJmem
  have hC : F (MvPolynomial.C s0) = algebraMap R H s0 := by
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rw [map_mul, map_pow, hP, hC, mul_comm] at h0
  exact ⟨k, htf s0 (nonZeroDivisors.ne_zero hs0) _ h0⟩

end SEP

section Engine

variable (R : Type*) [CommRing R] (H : Type*) [CommRing H] [Bialgebra R H]

def Dmap (n : ℕ) : H →ₐ[R] H :=
  ((WithConv.toConv (AlgHom.id R H)) ^ n).ofConv

variable {R H}

theorem comp_convOne {L : Type*} [CommRing L] [Algebra R L] (φ : H →ₐ[R] L) :
    φ.comp ((1 : WithConv (H →ₐ[R] H)).ofConv) = (1 : WithConv (H →ₐ[R] L)).ofConv := by
  rw [AlgHom.convOne_def, AlgHom.convOne_def, WithConv.ofConv_toConv, WithConv.ofConv_toConv,
    ← AlgHom.comp_assoc]
  congr 1
  ext

theorem toConv_pow_eq {L : Type*} [CommRing L] [Algebra R L] (φ : H →ₐ[R] L) (n : ℕ) :
    (WithConv.toConv φ) ^ n = WithConv.toConv (φ.comp (Dmap R H n)) := by
  induction n with
  | zero =>
      simp only [Dmap, pow_zero]
      rw [comp_convOne φ, WithConv.toConv_ofConv]
  | succ n ih =>
      simp only [Dmap] at ih ⊢
      rw [pow_succ, pow_succ, ih]
      rw [AlgHom.comp_convMul_distrib φ
        ((WithConv.toConv (AlgHom.id R H)) ^ n) (WithConv.toConv (AlgHom.id R H))]
      rw [WithConv.toConv_ofConv, WithConv.ofConv_toConv, AlgHom.comp_id]

theorem dmap_sub_counit_nilpotent {Ω : Type*} [CommRing Ω] [Algebra R Ω] {n : ℕ}
    (hsep : ∀ x : H, (∀ g : H →ₐ[R] Ω, g x = 0) → IsNilpotent x)
    (hΩ : ∀ φ : WithConv (H →ₐ[R] Ω), φ ^ n = 1) (x : H) :
    IsNilpotent (Dmap R H n x - algebraMap R H (Bialgebra.counitAlgHom R H x)) := by
  classical
  apply hsep
  intro φ
  have hφ : WithConv.toConv (φ.comp (Dmap R H n)) = (1 : WithConv (H →ₐ[R] Ω)) := by
    rw [← toConv_pow_eq φ n]
    exact hΩ (WithConv.toConv φ)
  have hφ' : φ.comp (Dmap R H n) = (1 : WithConv (H →ₐ[R] Ω)).ofConv := by
    rw [← hφ, WithConv.ofConv_toConv]
  have hpt : φ (Dmap R H n x) = algebraMap R Ω (Bialgebra.counitAlgHom R H x) := by
    have h := congrArg (fun f : H →ₐ[R] Ω => f x) hφ'
    simp only [AlgHom.comp_apply] at h
    rw [h, AlgHom.convOne_def, WithConv.ofConv_toConv, AlgHom.comp_apply, Algebra.ofId_apply]
  rw [map_sub, hpt, AlgHom.commutes, sub_self]

theorem withConv_pow_eq_one_of_nilpotent {L : Type*} [Field L] [Algebra R L] {n : ℕ}
    (hnil : ∀ x : H, IsNilpotent (Dmap R H n x - algebraMap R H (Bialgebra.counitAlgHom R H x)))
    (ψ : WithConv (H →ₐ[R] L)) : ψ ^ n = 1 := by
  classical
  have hψpt : ∀ x : H, ψ.ofConv (Dmap R H n x)
      = algebraMap R L (Bialgebra.counitAlgHom R H x) := by
    intro x
    have h0 : ψ.ofConv (Dmap R H n x - algebraMap R H (Bialgebra.counitAlgHom R H x)) = 0 :=
      ((hnil x).map (ψ.ofConv : H →+* L)).eq_zero
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    exact ψ.ofConv.commutes (Bialgebra.counitAlgHom R H x)
  have hcomp : ψ.ofConv.comp (Dmap R H n) = (1 : WithConv (H →ₐ[R] L)).ofConv := by
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply, hψpt x, AlgHom.convOne_def, WithConv.ofConv_toConv,
      AlgHom.comp_apply, Algebra.ofId_apply]
  calc ψ ^ n = (WithConv.toConv ψ.ofConv) ^ n := by rw [WithConv.toConv_ofConv]
    _ = WithConv.toConv (ψ.ofConv.comp (Dmap R H n)) := toConv_pow_eq ψ.ofConv n
    _ = WithConv.toConv ((1 : WithConv (H →ₐ[R] L)).ofConv) := by rw [hcomp]
    _ = 1 := WithConv.toConv_ofConv _

end Engine

theorem withConv_pow_eq_one_of_dmap_eq {R : Type*} [CommRing R] {H : Type*} [CommRing H]
    [Bialgebra R H] {L : Type*} [CommRing L] [Algebra R L] {n : ℕ}
    (hD : ∀ x : H, Dmap R H n x = algebraMap R H (Bialgebra.counitAlgHom R H x))
    (ψ : WithConv (H →ₐ[R] L)) : ψ ^ n = 1 := by
  have hcomp : ψ.ofConv.comp (Dmap R H n) = (1 : WithConv (H →ₐ[R] L)).ofConv := by
    apply AlgHom.ext
    intro x
    rw [AlgHom.comp_apply, hD x, AlgHom.commutes, AlgHom.convOne_def, WithConv.ofConv_toConv,
      AlgHom.comp_apply, Algebra.ofId_apply]
  calc ψ ^ n = (WithConv.toConv ψ.ofConv) ^ n := by rw [WithConv.toConv_ofConv]
    _ = WithConv.toConv (ψ.ofConv.comp (Dmap R H n)) := toConv_pow_eq ψ.ofConv n
    _ = WithConv.toConv ((1 : WithConv (H →ₐ[R] L)).ofConv) := by rw [hcomp]
    _ = 1 := WithConv.toConv_ofConv _

section Core

variable {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    (C : JZeroNeronPrimaryTorsionCore p q A hA)

local notation "ℚbar" => AlgebraicClosure ℚ

scoped instance (priority := 10000) instAlgebraH (m : ℕ) : Algebra ℤ (C.H m) :=
  (C.instHopfAlgebra_H m).toAlgebra

scoped instance (priority := 10000) instModuleH (m : ℕ) : Module ℤ (C.H m) :=
  (instAlgebraH C m).toModule

def FlatInt (M : Type) [AddCommGroup M] (i : Module ℤ M) : Prop :=
  by letI : Module ℤ M := i; exact Module.Flat ℤ M

omit [Fact p.Prime] hq in
lemma flatInt_iff (M : Type) [AddCommGroup M] (i₁ i₂ : Module ℤ M) :
    FlatInt M i₁ ↔ FlatInt M i₂ := by
  rw [Subsingleton.elim i₁ i₂]

scoped instance instFlatH (m : ℕ) : Module.Flat ℤ (C.H m) := by
  have h : FlatInt (C.H m) _ := C.instFlat_H m
  exact (flatInt_iff (C.H m) _ (instModuleH C m)).mp h

scoped instance (priority := 10000) instModuleIntQbar : Module ℤ ℚbar := Algebra.toModule

scoped instance instIsScalarTowerIntQbarQbar :
    @IsScalarTower ℤ ℚbar ℚbar Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.right

scoped instance instIsScalarTowerIntRatQbar :
    @IsScalarTower ℤ ℚ ℚbar Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

example (m : ℕ) : CommRing (ℚbar ⊗[ℤ] C.H m) := inferInstance
example (m : ℕ) : HopfAlgebra ℚbar (ℚbar ⊗[ℤ] C.H m) := inferInstance
example (m : ℕ) : Algebra.FiniteType ℚbar (ℚbar ⊗[ℤ] C.H m) := inferInstance

theorem tmul_one_injective (m : ℕ) :
    Function.Injective (fun h : C.H m => (1 : ℚbar) ⊗ₜ[ℤ] h) := by
  have hf : Function.Injective (Algebra.linearMap ℤ ℚbar) := by
    rw [Algebra.coe_linearMap]
    exact (algebraMap ℤ ℚbar).injective_int
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := C.H m)
    (Algebra.linearMap ℤ ℚbar) hf
  intro x y hxy
  have h1 : ((Algebra.linearMap ℤ ℚbar).rTensor (C.H m)) ((1 : ℤ) ⊗ₜ[ℤ] x)
      = ((Algebra.linearMap ℤ ℚbar).rTensor (C.H m)) ((1 : ℤ) ⊗ₜ[ℤ] y) := by
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one]
    exact hxy
  have h2 := hinj h1
  have h3 := congrArg (TensorProduct.lid ℤ (C.H m)) h2
  rw [TensorProduct.lid_tmul, TensorProduct.lid_tmul] at h3
  simpa using h3

scoped instance instIsReducedQbar (m : ℕ) : _root_.IsReduced (ℚbar ⊗[ℤ] C.H m) :=
  HopfAlgebra.isReduced_of_finiteType_of_charZero ℚbar (ℚbar ⊗[ℤ] C.H m)

scoped instance instIsReducedH (m : ℕ) : _root_.IsReduced (C.H m) :=
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : C.H m →ₐ[ℤ] ℚbar ⊗[ℤ] C.H m)
    (fun x y hxy => tmul_one_injective C m hxy)

omit hq in

theorem pow_nsmul_eq_zero (m : ℕ) (x : JZero p) (hx : x ∈ eisensteinPrimaryTorsionBar p q m) :
    (q ^ m) • x = 0 := by
  have h1 : ((q : ℤ) ^ m) • x = 0 := hx.1
  rw [← natCast_zsmul, Nat.cast_pow]
  exact h1

theorem qbar_point_pow_eq_one (m : ℕ) (φ : WithConv (C.H m →ₐ[ℤ] ℚbar)) : φ ^ (q ^ m) = 1 := by
  classical
  set E := C.genericPoints m with hEdef
  have hadd : ∀ f g, E (f * g) = E f + E g := C.genericConv m
  have h1 : E 1 = 0 := by
    have h := hadd 1 1
    rw [one_mul] at h
    have h' : E 1 + 0 = E 1 + E 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have hpow : ∀ (n : ℕ) (ψ : WithConv (C.H m →ₐ[ℤ] ℚbar)), E (ψ ^ n) = n • E ψ := by
    intro n ψ
    induction n with
    | zero => rw [pow_zero, h1, zero_nsmul]
    | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]
  have htor : (q ^ m) • E φ = 0 := by
    have hc : ((q ^ m) • ((E φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)) = 0 :=
      pow_nsmul_eq_zero m ((E φ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p) (E φ).2
    apply Subtype.ext
    push_cast
    exact hc
  have : E (φ ^ (q ^ m)) = E 1 := by rw [hpow, htor, h1]
  exact E.injective this

theorem dmap_eq (m : ℕ) (x : C.H m) :
    Dmap ℤ (C.H m) (q ^ m) x = algebraMap ℤ (C.H m) (Bialgebra.counitAlgHom ℤ (C.H m) x) := by
  have hnil : IsNilpotent (Dmap ℤ (C.H m) (q ^ m) x
      - algebraMap ℤ (C.H m) (Bialgebra.counitAlgHom ℤ (C.H m) x)) := by
    refine dmap_sub_counit_nilpotent (Ω := ℚbar) ?_ (qbar_point_pow_eq_one C m) x
    intro y hy
    exact isNilpotent_of_forall_algHom_apply_eq_zero ℚ ℚbar
      (eq_zero_of_algebraMap_mul_eq_zero (R := ℤ) (H := C.H m)) y hy
  exact sub_eq_zero.mp hnil.eq_zero

theorem point_pow_eq_one (m : ℕ) {L : Type*} [CommRing L] [Algebra ℤ L]
    (ψ : WithConv (C.H m →ₐ[ℤ] L)) : ψ ^ (q ^ m) = 1 :=
  withConv_pow_eq_one_of_dmap_eq (dmap_eq C m) ψ

theorem pow_nsmul_sections_eq_zero (m : ℕ) (U : specInt.Fppf) (s : (C.𝒥 m).1.obj (op U)) :
    (q ^ m) • s = 0 := by
  apply (C.sectionsEquiv m U).injective
  rw [map_nsmul, map_zero]
  apply Additive.toMul.injective
  rw [toMul_nsmul, toMul_zero]
  exact point_pow_eq_one C m _

end Core

end JZeroNeronPrimaryTorsionCoreTorsion
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero.ModularCurve.JZeroNeronPrimaryTorsionCoreTorsion"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero.ModularCurve.JZeroNeronPrimaryTorsionCoreTorsion P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero.ModularCurve.JZeroNeronPrimaryTorsionCoreTorsion P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero.ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (U : specInt.Fppf) (s : (C.𝒥 m).1.obj (Opposite.op U)) :
    q ^ m • s = 0 :=
  JZeroNeronPrimaryTorsionCoreTorsion.pow_nsmul_sections_eq_zero C m U s

end S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero
end P2MW
export P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionCore_pow_nsmul_sections_eq_zero (solution)
