-- Prove2me | solution 1 for HopfAlgebra.exists_isIdempotentElem_mem_hopfKer_mul_eq_of_finitePartIdempotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2852ec5c-bedf-5580-99b9-e002c09bb428

import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_Algebra_Etale_of_isReduced_of_perfectField
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_Algebra_Etale_algHom_ext_of_forall_comp_eq
import Theorems.Thm_HopfAlgebra_isUnit_withConv_algHom
import Theorems.Thm_HopfAlgebra_comul_finitePartIdempotent_mul
import Theorems.Thm_HopfAlgebra_counit_finitePartIdempotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_isIdempotentElem_mem_hopfKer_mul_eq_of_finitePartIdempotent

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open WithConv

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction coaction_apply hopfKer mem_hopfKer_iff coaction_eq_of_mem isReduced_of_finiteType_of_charZero isUnit_withConv_algHom comul_finitePartIdempotent_mul counit_finitePartIdempotent"
namespace OrbitIdempotent
p2m_open "HopfAlgebra"

variable {R : Type} [CommRing R] [IsDomain R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]

section sep
variable {A : Type} [CommRing A] [HopfAlgebra R A] [Module.Flat R A] [Module.Finite K (K ⊗[R] A)]

omit [IsDomain R] [CharZero K] [Module.Finite K (K ⊗[R] A)] in
theorem includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A) := by
  have h1 : Function.Injective ((Algebra.linearMap R K).rTensor A) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective R K)
  intro a b hab
  have : (Algebra.linearMap R K).rTensor A ((TensorProduct.lid R A).symm a) =
      (Algebra.linearMap R K).rTensor A ((TensorProduct.lid R A).symm b) := by
    simpa [LinearMap.rTensor_tmul] using hab
  exact (TensorProduct.lid R A).symm.injective (h1 this)

omit [IsDomain R] [Module.Flat R A] in

theorem etale_baseChange : Algebra.Etale K (K ⊗[R] A) := by
  haveI : IsReduced (K ⊗[R] A) := HopfAlgebra.isReduced_of_finiteType_of_charZero K (K ⊗[R] A)
  exact Algebra.Etale.of_isReduced_of_perfectField K (K ⊗[R] A)

omit [IsDomain R] in

theorem eq_of_forall_algHom_apply_eq (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    [Algebra R Ω] [IsScalarTower R K Ω]
    {x y : A} (h : ∀ ψ : A →ₐ[R] Ω, ψ x = ψ y) : x = y := by
  haveI := etale_baseChange (R := R) (K := K) (A := A)
  apply includeRight_injective (R := R) (K := K)
  set x' : K ⊗[R] A := (1 : K) ⊗ₜ[R] x
  set y' : K ⊗[R] A := (1 : K) ⊗ₜ[R] y
  have key : (Polynomial.aeval x' : Polynomial K →ₐ[K] K ⊗[R] A) = Polynomial.aeval y' := by
    apply Algebra.Etale.algHom_ext_of_forall_comp_eq (Ω := Ω)
    intro χ
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X]
    exact h ((χ.restrictScalars R).comp (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A))
  have := congrArg (fun φ : Polynomial K →ₐ[K] K ⊗[R] A => φ Polynomial.X) key
  simpa [x', y'] using this

end sep

end HopfAlgebra.OrbitIdempotent

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction coaction_apply hopfKer mem_hopfKer_iff coaction_eq_of_mem isReduced_of_finiteType_of_charZero isUnit_withConv_algHom comul_finitePartIdempotent_mul counit_finitePartIdempotent"
namespace OrbitIdempotent
p2m_open "HopfAlgebra"

variable {R : Type} [CommRing R] [IsDomain R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
  {H : Type} [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
  {H' : Type} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra R Ω] [IsScalarTower R K Ω]

omit [IsDomain R] [Module.Flat R H] [Module.Flat R H'] [IsAlgClosed Ω] [IsScalarTower R K Ω] in

theorem lift_coaction (qc : H →ₐc[R] H') (ψ : H →ₐ[R] Ω) (χ : H' →ₐ[R] Ω) (b : H) :
    Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _) (HopfAlgebra.coaction qc b) =
      (toConv ψ * toConv (χ.comp (qc : H →ₐ[R] H'))) b := by
  rw [AlgHom.convMul_apply, ofConv_toConv, ofConv_toConv, HopfAlgebra.coaction_apply]
  have key : (Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)).comp
      (Algebra.TensorProduct.map (AlgHom.id R H) (qc : H →ₐ[R] H')) =
      Algebra.TensorProduct.lift ψ (χ.comp (qc : H →ₐ[R] H')) (fun _ _ => Commute.all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp
  exact congrArg (fun g : H ⊗[R] H →ₐ[R] Ω => g (Coalgebra.comul (R := R) b)) key

omit [IsDomain R] [Module.Flat R H] [Module.Flat R H'] [IsAlgClosed Ω] [IsScalarTower R K Ω] in
theorem lift_tmul_one (ψ : H →ₐ[R] Ω) (χ : H' →ₐ[R] Ω) (b : H) :
    Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _) (b ⊗ₜ[R] (1 : H')) = ψ b := by
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]

omit [IsDomain R] [Module.Flat R H] [Module.Flat R H'] [IsAlgClosed Ω] [IsScalarTower R K Ω] in

theorem convMul_apply_eq_of_mem_hopfKer (qc : H →ₐc[R] H') {b : H} (hb : b ∈ HopfAlgebra.hopfKer qc)
    (ψ : H →ₐ[R] Ω) (χ : H' →ₐ[R] Ω) :
    (toConv ψ * toConv (χ.comp (qc : H →ₐ[R] H'))) b = ψ b := by
  rw [← lift_coaction, HopfAlgebra.coaction_eq_of_mem qc hb, lift_tmul_one]

theorem moduleFinite_baseChange_tensor [Module.Finite K (K ⊗[R] H)] [Module.Finite K (K ⊗[R] H')] :
    Module.Finite K (K ⊗[R] (H ⊗[R] H')) := by
  let f₁ : K ⊗[R] H →ₐ[K] K ⊗[R] (H ⊗[R] H') :=
    Algebra.TensorProduct.map (AlgHom.id K K) (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H')
  let f₂ : K ⊗[R] H' →ₐ[K] K ⊗[R] (H ⊗[R] H') :=
    Algebra.TensorProduct.map (AlgHom.id K K) (Algebra.TensorProduct.includeRight : H' →ₐ[R] H ⊗[R] H')
  let φ : (K ⊗[R] H) ⊗[K] (K ⊗[R] H') →ₐ[K] K ⊗[R] (H ⊗[R] H') :=
    Algebra.TensorProduct.lift f₁ f₂ (fun a b => Commute.all (f₁ a) (f₂ b))
  have hφ : Function.Surjective φ := by
    intro z
    induction z with
    | zero => exact ⟨0, map_zero φ⟩
    | tmul k x =>
      induction x with
      | zero => exact ⟨0, by rw [TensorProduct.tmul_zero, map_zero]⟩
      | tmul h h' =>
        refine ⟨(k ⊗ₜ[R] h) ⊗ₜ[K] ((1 : K) ⊗ₜ[R] h'), ?_⟩
        simp [φ, f₁, f₂, Algebra.TensorProduct.lift_tmul]
      | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
        exact ⟨a + b, by rw [map_add, ha, hb, TensorProduct.tmul_add]⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  exact Module.Finite.of_surjective φ.toLinearMap hφ

omit [IsDomain R] [Module.Flat R H] in
theorem moduleFinite_baseChange_of_surjective [Module.Finite K (K ⊗[R] H)] (qc : H →ₐc[R] H')
    (hqc : Function.Surjective qc) : Module.Finite K (K ⊗[R] H') :=
  Module.Finite.of_surjective ((qc : H →ₗ[R] H').baseChange K) (LinearMap.lTensor_surjective K hqc)

theorem mem_hopfKer_iff_forall_points [Module.Finite K (K ⊗[R] H)] (qc : H →ₐc[R] H')
    (hqc : Function.Surjective qc) (b : H) :
    b ∈ HopfAlgebra.hopfKer qc ↔
      ∀ (ψ : H →ₐ[R] Ω) (χ : H' →ₐ[R] Ω), (toConv ψ * toConv (χ.comp (qc : H →ₐ[R] H'))) b = ψ b := by
  refine ⟨fun hb ψ χ => convMul_apply_eq_of_mem_hopfKer qc hb ψ χ, fun h => ?_⟩
  haveI := moduleFinite_baseChange_of_surjective (K := K) qc hqc
  haveI := moduleFinite_baseChange_tensor (R := R) (K := K) (H := H) (H' := H')
  rw [HopfAlgebra.mem_hopfKer_iff]
  apply eq_of_forall_algHom_apply_eq (R := R) (K := K) (A := H ⊗[R] H') Ω
  intro φ
  have hφ : φ = Algebra.TensorProduct.lift (φ.comp Algebra.TensorProduct.includeLeft)
      ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight) (fun _ _ => Commute.all _ _) := by
    apply Algebra.TensorProduct.ext'
    intro a c
    simp [Algebra.TensorProduct.lift_tmul, ← map_mul]
  rw [hφ, lift_coaction, lift_tmul_one]
  exact h _ _

end HopfAlgebra.OrbitIdempotent

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction coaction_apply hopfKer mem_hopfKer_iff coaction_eq_of_mem isReduced_of_finiteType_of_charZero isUnit_withConv_algHom comul_finitePartIdempotent_mul counit_finitePartIdempotent"
namespace OrbitIdempotent
p2m_open "HopfAlgebra"

variable {R : Type} [CommRing R]
  {H : Type} [CommRing H] [HopfAlgebra R H]
  {Ω : Type} [Field Ω] [Algebra R Ω]

theorem apply_eq_zero_or_one {e : H} (he : IsIdempotentElem e) (ψ : H →ₐ[R] Ω) : ψ e = 0 ∨ ψ e = 1 :=
  IsIdempotentElem.iff_eq_zero_or_one.mp (he.map ψ)

theorem apply_eq_zero_iff {e : H} (he : IsIdempotentElem e) (ψ : H →ₐ[R] Ω) : ψ e = 0 ↔ ψ e ≠ 1 := by
  rcases apply_eq_zero_or_one he ψ with h | h
  · simp [h]
  · simp [h]

theorem convMul_apply_eq_right {e : H} (hsub : Coalgebra.comul (R := R) e * (e ⊗ₜ[R] 1) = e ⊗ₜ[R] e)
    (ψ φ : H →ₐ[R] Ω) (hψ : ψ e = 1) : (toConv ψ * toConv φ) e = φ e := by
  have h := congrArg (Algebra.TensorProduct.lift ψ φ (fun _ _ => Commute.all _ _)) hsub
  rw [map_mul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, mul_one, hψ,
    mul_one, one_mul, ← ofConv_toConv ψ, ← ofConv_toConv φ, ← AlgHom.convMul_apply] at h
  simpa using h

theorem convMul_apply_eq_left {e : H} (hsub : Coalgebra.comul (R := R) e * (1 ⊗ₜ[R] e) = e ⊗ₜ[R] e)
    (φ ψ : H →ₐ[R] Ω) (hψ : ψ e = 1) : (toConv φ * toConv ψ) e = φ e := by
  have h := congrArg (Algebra.TensorProduct.lift φ ψ (fun _ _ => Commute.all _ _)) hsub
  rw [map_mul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, one_mul, hψ,
    mul_one, mul_one, ← ofConv_toConv φ, ← ofConv_toConv ψ, ← AlgHom.convMul_apply] at h
  simpa using h

theorem convOne_apply_eq_one {e : H} (hcou : Coalgebra.counit (R := R) e = 1) :
    (1 : WithConv (H →ₐ[R] Ω)) e = 1 := by
  rw [AlgHom.convOne_apply, hcou, map_one]

theorem inv_apply_eq_one {e : H} (hsub : Coalgebra.comul (R := R) e * (1 ⊗ₜ[R] e) = e ⊗ₜ[R] e)
    (hcou : Coalgebra.counit (R := R) e = 1) (u : (WithConv (H →ₐ[R] Ω))ˣ) (hu : (u : WithConv (H →ₐ[R] Ω)) e = 1) :
    ((u⁻¹ : (WithConv (H →ₐ[R] Ω))ˣ) : WithConv (H →ₐ[R] Ω)) e = 1 := by
  have h := convMul_apply_eq_left (Ω := Ω) hsub ((u⁻¹ : (WithConv (H →ₐ[R] Ω))ˣ) : WithConv (H →ₐ[R] Ω)).ofConv
    (u : WithConv (H →ₐ[R] Ω)).ofConv hu
  rw [toConv_ofConv, toConv_ofConv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    convOne_apply_eq_one hcou] at h
  exact h.symm

end HopfAlgebra.OrbitIdempotent

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction coaction_apply hopfKer mem_hopfKer_iff coaction_eq_of_mem isReduced_of_finiteType_of_charZero isUnit_withConv_algHom comul_finitePartIdempotent_mul counit_finitePartIdempotent"
namespace OrbitIdempotent
p2m_open "HopfAlgebra"

variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsFractionRing R K] in

theorem isUnit_algebraMap_of_map_maximalIdeal_eq_top {A : Type} [CommRing A] [Algebra R A]
    (hgen : Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) = ⊤) {r : R} (hr : r ≠ 0) :
    IsUnit (algebraMap R A r) := by
  by_cases hm : IsLocalRing.maximalIdeal R = ⊥
  ·
    have hu : IsUnit r := by
      by_contra h
      have : r ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal r).mpr h
      rw [hm, Ideal.mem_bot] at this
      exact hr this
    exact hu.map _
  · haveI : IsDiscreteValuationRing R := { not_a_field' := hm }
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hϖu : IsUnit (algebraMap R A ϖ) := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span, Set.image_singleton,
        Ideal.span_singleton_eq_top] at hgen
      exact hgen
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr hϖ
    have h := congrArg (algebraMap R A) hu
    rw [map_mul, map_pow] at h
    exact isUnit_of_mul_isUnit_left (h ▸ hϖu.pow n)

@[reducible] noncomputable def algebraOfMapMaximalIdealEqTop {A : Type} [CommRing A] [Algebra R A]
    (hgen : Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) = ⊤) : Algebra K A :=
  (IsLocalization.lift (M := nonZeroDivisors R) (S := K) (g := algebraMap R A)
    (fun y => isUnit_algebraMap_of_map_maximalIdeal_eq_top hgen (nonZeroDivisors.ne_zero y.2))).toAlgebra

theorem isScalarTower_algebraOfMapMaximalIdealEqTop {A : Type} [CommRing A] [Algebra R A]
    (hgen : Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) = ⊤) :
    letI := algebraOfMapMaximalIdealEqTop (K := K) hgen
    IsScalarTower R K A := by
  letI := algebraOfMapMaximalIdealEqTop (K := K) hgen
  exact IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq (M := nonZeroDivisors R) _ r).symm)

theorem moduleFinite_of_surjective {H : Type} [CommRing H] [Algebra R H] [Module.Finite K (K ⊗[R] H)]
    {A : Type} [CommRing A] [Algebra R A] [Algebra K A] [IsScalarTower R K A]
    (g : H →ₐ[R] A) (hg : Function.Surjective g) : Module.Finite K A := by
  let φ : K ⊗[R] H →ₐ[K] A := Algebra.TensorProduct.lift (Algebra.ofId K A) g (fun _ _ => Commute.all _ _)
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨h, rfl⟩ := hg a
    exact ⟨1 ⊗ₜ[R] h, by simp [φ, Algebra.TensorProduct.lift_tmul]⟩
  exact Module.Finite.of_surjective φ.toLinearMap hφ

end HopfAlgebra.OrbitIdempotent

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction coaction_apply hopfKer mem_hopfKer_iff coaction_eq_of_mem isReduced_of_finiteType_of_charZero isUnit_withConv_algHom comul_finitePartIdempotent_mul counit_finitePartIdempotent"
namespace OrbitIdempotent
p2m_open "HopfAlgebra"

section transport
variable {R : Type} [CommRing R] [IsDomain R]
  (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type} [CommRing A] [Algebra R A]
  {Ω : Type} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]

omit [IsDomain R] in
include K in
theorem algebraMap_injective_of_tower : Function.Injective (algebraMap R Ω) := by
  rw [IsScalarTower.algebraMap_eq R K Ω]
  exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)

theorem quotient_lift_injective (ψ : A →ₐ[R] Ω) (I : Ideal A) (hI : RingHom.ker ψ = I) :
    ∃ ψbar : A ⧸ I →ₐ[R] Ω, Function.Injective ψbar ∧ ∀ a, ψbar (Ideal.Quotient.mk I a) = ψ a := by
  subst hI
  refine ⟨Ideal.Quotient.liftₐ _ ψ (fun a ha => ha), ?_, fun a => rfl⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

include K in

theorem isUnit_algebraMap_fractionRing (ψ : A →ₐ[R] Ω) (I : Ideal A) [I.IsPrime] (hI : RingHom.ker ψ = I)
    (y : nonZeroDivisors R) : IsUnit (algebraMap R (FractionRing (A ⧸ I)) y) := by
  obtain ⟨ψbar, hinj, -⟩ := quotient_lift_injective ψ I hI
  apply IsUnit.mk0
  intro h0
  rw [IsScalarTower.algebraMap_apply R (A ⧸ I) (FractionRing (A ⧸ I)), IsFractionRing.to_map_eq_zero_iff] at h0
  have h2 := congrArg ψbar h0
  rw [map_zero, AlgHom.commutes] at h2
  exact nonZeroDivisors.ne_zero y.2 (algebraMap_injective_of_tower K (h2.trans (map_zero _).symm))

theorem exists_extend (I : Ideal A) [I.IsPrime]
    [Algebra K (FractionRing (A ⧸ I))] [IsScalarTower R K (FractionRing (A ⧸ I))]
    (ψ : A →ₐ[R] Ω) (hI : RingHom.ker ψ = I) :
    ∃ Ψ : FractionRing (A ⧸ I) →ₐ[K] Ω,
      ∀ a, Ψ (algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) (Ideal.Quotient.mk I a)) = ψ a := by
  classical
  obtain ⟨ψbar, hinj, hψbar⟩ := quotient_lift_injective ψ I hI
  let Ψ₀ : FractionRing (A ⧸ I) →ₐ[R] Ω := IsFractionRing.liftAlgHom hinj
  have hΨ₀ : ∀ d : A ⧸ I, Ψ₀ (algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) d) = ψbar d := fun d => by
    simp [Ψ₀]
  have hK : ∀ k : K, Ψ₀ (algebraMap K (FractionRing (A ⧸ I)) k) = algebraMap K Ω k := by
    intro k
    have : ((Ψ₀ : FractionRing (A ⧸ I) →+* Ω).comp (algebraMap K (FractionRing (A ⧸ I)))) = algebraMap K Ω := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors R)
      ext r
      rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R K (FractionRing (A ⧸ I)),
        AlgHom.coe_toRingHom, AlgHom.commutes, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R K Ω]
    exact congrArg (fun g : K →+* Ω => g k) this
  let Ψ : FractionRing (A ⧸ I) →ₐ[K] Ω := { (Ψ₀ : FractionRing (A ⧸ I) →+* Ω) with commutes' := hK }
  refine ⟨Ψ, fun a => ?_⟩
  change Ψ₀ (algebraMap (A ⧸ I) (FractionRing (A ⧸ I)) (Ideal.Quotient.mk I a)) = ψ a
  rw [hΨ₀, hψbar]

variable [Normal K Ω]

theorem exists_algHom_comp_eq_of_ker_eq (ψ ψ' : A →ₐ[R] Ω) (hker : RingHom.ker ψ = RingHom.ker ψ') :
    ∃ σ : Ω →ₐ[K] Ω, ∀ a, σ (ψ a) = ψ' a := by
  classical
  set I := RingHom.ker ψ
  haveI : I.IsPrime := RingHom.ker_isPrime _
  letI : Algebra K (FractionRing (A ⧸ I)) :=
    (IsLocalization.lift (M := nonZeroDivisors R) (S := K) (isUnit_algebraMap_fractionRing K ψ I rfl)).toAlgebra
  haveI : IsScalarTower R K (FractionRing (A ⧸ I)) :=
    IsScalarTower.of_algebraMap_eq (fun r => (IsLocalization.lift_eq (M := nonZeroDivisors R) _ r).symm)
  obtain ⟨Ψ, hΨ⟩ := exists_extend K I ψ rfl
  obtain ⟨Ψ', hΨ'⟩ := exists_extend K I ψ' hker.symm
  letI : Algebra (FractionRing (A ⧸ I)) Ω := (Ψ : FractionRing (A ⧸ I) →+* Ω).toAlgebra
  haveI : IsScalarTower K (FractionRing (A ⧸ I)) Ω :=
    IsScalarTower.of_algebraMap_eq (fun k => (Ψ.commutes k).symm)
  refine ⟨Ψ'.liftNormal Ω, fun a => ?_⟩
  rw [← hΨ a, ← hΨ' a]
  exact AlgHom.liftNormal_commutes Ψ' Ω _

end transport

end HopfAlgebra.OrbitIdempotent

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction coaction_apply hopfKer mem_hopfKer_iff coaction_eq_of_mem isReduced_of_finiteType_of_charZero isUnit_withConv_algHom comul_finitePartIdempotent_mul counit_finitePartIdempotent"
namespace OrbitIdempotent
p2m_open "HopfAlgebra"

section clopen
variable {H : Type} [CommRing H]

theorem isClopen_basicOpen_union {e : H} (he : IsIdempotentElem e)
    {A : Type} [CommRing A] [Algebra H A] [IsLocalization.Away (1 - e) A] [IsArtinianRing A]
    (T : Set (PrimeSpectrum H)) (hT : T ⊆ PrimeSpectrum.zeroLocus {e}) :
    IsClopen ((PrimeSpectrum.basicOpen e : Set (PrimeSpectrum H)) ∪ T) := by
  classical
  have he' : IsIdempotentElem (1 - e) := he.one_sub

  have hrange : Set.range (PrimeSpectrum.comap (algebraMap H A)) = PrimeSpectrum.zeroLocus {e} := by
    rw [PrimeSpectrum.localization_away_comap_range A (1 - e),
      PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem (1 - e) he', sub_sub_cancel]
  have hemb := PrimeSpectrum.localization_away_isOpenEmbedding A (1 - e)

  haveI : DiscreteTopology (PrimeSpectrum A) :=
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩

  have hTopen : IsOpen T := by
    have : T = PrimeSpectrum.comap (algebraMap H A) '' (PrimeSpectrum.comap (algebraMap H A) ⁻¹' T) := by
      rw [Set.image_preimage_eq_inter_range, hrange, Set.inter_eq_left.mpr hT]
    rw [this]
    exact hemb.isOpenMap _ (isOpen_discrete _)

  have hTfin : T.Finite := by
    refine Set.Finite.subset ?_ (hT.trans hrange.symm.subset)
    exact Set.finite_range _
  have hTclosed : IsClosed T := by
    rw [← Set.biUnion_of_singleton T]
    refine hTfin.isClosed_biUnion fun x hx => ?_
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap H A)) := hrange ▸ hT hx
    rw [PrimeSpectrum.comap_asIdeal]
    haveI : y.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime y.asIdeal
    exact Ideal.comap_isMaximal_of_surjective _
      (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (1 - e) he')

  have hD : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum H)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  exact ⟨hD.1.union hTclosed, hD.2.union hTopen⟩

end clopen

end HopfAlgebra.OrbitIdempotent

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk coaction coaction_apply hopfKer mem_hopfKer_iff coaction_eq_of_mem isReduced_of_finiteType_of_charZero isUnit_withConv_algHom comul_finitePartIdempotent_mul counit_finitePartIdempotent"
namespace OrbitIdempotent
p2m_open "HopfAlgebra"

theorem eq_of_zero_or_one {Ω : Type} [Field Ω] {a b : Ω} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (h : a = 1 ↔ b = 1) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact absurd (h.mpr rfl) zero_ne_one
  · exact (absurd (h.mp rfl) zero_ne_one)
  · rfl

end HopfAlgebra.OrbitIdempotent

open HopfAlgebra.OrbitIdempotent in

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Algebra.FiniteType R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H] [Module.Finite K (TensorProduct R K H)]
    (H' : Type) [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤)
    (e' : H') (he' : IsIdempotentElem e') (hfin' : Module.Finite R (Localization.Away e'))
    (hgen' : Ideal.map (algebraMap R (Localization.Away (1 - e'))) (IsLocalRing.maximalIdeal R) = ⊤)
    (hee' : qc e = e') :
    ∃ f : H, IsIdempotentElem f ∧ f ∈ HopfAlgebra.hopfKer qc ∧ f * e = e ∧
      ∀ b ∈ HopfAlgebra.hopfKer qc, b * e = 0 → b * f = 0 := by
  classical

  obtain ⟨hsub₁, hsub₂⟩ := HopfAlgebra.comul_finitePartIdempotent_mul R H e he hfin hgen
  have hcou := HopfAlgebra.counit_finitePartIdempotent R H e he hgen

  let Ω : Type := AlgebraicClosure K

  let A : Type := Localization.Away (1 - e)
  letI : Algebra K A := algebraOfMapMaximalIdealEqTop (K := K) hgen
  haveI : IsScalarTower R K A := isScalarTower_algebraOfMapMaximalIdealEqTop (K := K) hgen
  haveI : Module.Finite K (K ⊗[R] H) := ‹Module.Finite K (TensorProduct R K H)›
  haveI : Module.Finite K A := moduleFinite_of_surjective (K := K) (IsScalarTower.toAlgHom R H A)
    (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (1 - e) he.one_sub)
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A

  let P : PrimeSpectrum H → Prop := fun p =>
    ∃ (ψ : H →ₐ[R] Ω) (ν : H' →ₐ[R] Ω), RingHom.ker ψ = p.asIdeal ∧
      (toConv ψ * toConv (ν.comp (qc : H →ₐ[R] H'))) e = 1
  let T : Set (PrimeSpectrum H) := {p | e ∈ p.asIdeal ∧ P p}
  have hT : T ⊆ PrimeSpectrum.zeroLocus {e} := fun p hp => by
    simpa [PrimeSpectrum.mem_zeroLocus] using hp.1
  have hU := isClopen_basicOpen_union he (A := A) T hT
  obtain ⟨f, ⟨hf, hfU⟩, huniq⟩ := PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen hU

  have hker : ∀ (ψ : H →ₐ[R] Ω) (x : H), IsIdempotentElem x →
      (ψ x = 1 ↔ (⟨RingHom.ker ψ, RingHom.ker_isPrime _⟩ : PrimeSpectrum H) ∈ PrimeSpectrum.basicOpen x) := by
    intro ψ x hx
    rw [PrimeSpectrum.mem_basicOpen]
    change ψ x = 1 ↔ x ∉ RingHom.ker ψ
    rw [RingHom.mem_ker, apply_eq_zero_iff hx, not_not]

  let ν₀ : H' →ₐ[R] Ω := (Algebra.ofId R Ω).comp (Bialgebra.counitAlgHom R H')
  have hν₀ : toConv (ν₀.comp (qc : H →ₐ[R] H')) = (1 : WithConv (H →ₐ[R] Ω)) := by
    rw [AlgHom.convOne_def]
    congr 1
    change ((Algebra.ofId R Ω).comp (Bialgebra.counitAlgHom R H')).comp (qc : H →ₐ[R] H') = _
    rw [AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]

  have horbit : ∀ ψ : H →ₐ[R] Ω,
      ψ f = 1 ↔ ∃ ν : H' →ₐ[R] Ω, (toConv ψ * toConv (ν.comp (qc : H →ₐ[R] H'))) e = 1 := by
    intro ψ
    rw [hker ψ f hf, ← SetLike.mem_coe, ← hfU]
    constructor
    · rintro (h | ⟨-, ψ₀, ν₀', hk, h0⟩)
      ·
        refine ⟨ν₀, ?_⟩
        rw [hν₀, mul_one, ofConv_toConv]
        exact (hker ψ e he).mpr h
      ·
        obtain ⟨σ, hσ⟩ := exists_algHom_comp_eq_of_ker_eq K ψ₀ ψ hk
        refine ⟨(σ.restrictScalars R).comp ν₀', ?_⟩
        have hψ : (σ.restrictScalars R).comp ψ₀ = ψ := AlgHom.ext hσ
        have key := AlgHom.comp_convMul_distrib (σ.restrictScalars R) (toConv ψ₀)
          (toConv (ν₀'.comp (qc : H →ₐ[R] H')))
        rw [ofConv_toConv, ofConv_toConv, hψ] at key
        rw [AlgHom.comp_assoc, ← key, AlgHom.comp_apply, h0, map_one]
    · rintro ⟨ν, hν⟩
      rcases apply_eq_zero_or_one he ψ with h0 | h1
      · right
        refine ⟨?_, ψ, ν, rfl, hν⟩
        change e ∈ RingHom.ker ψ
        exact h0
      · left
        exact (hker ψ e he).mp h1
  refine ⟨f, hf, ?_, ?_, ?_⟩
  ·
    rw [mem_hopfKer_iff_forall_points (K := K) (Ω := Ω) qc hqc]
    intro ψ χ
    set φ : H →ₐ[R] Ω := (toConv ψ * toConv (χ.comp (qc : H →ₐ[R] H'))).ofConv with hφ
    change φ f = ψ f
    apply eq_of_zero_or_one (apply_eq_zero_or_one hf φ) (apply_eq_zero_or_one hf ψ)
    rw [horbit, horbit]
    obtain ⟨u, hu⟩ := HopfAlgebra.isUnit_withConv_algHom (toConv χ : WithConv (H' →ₐ[R] Ω))
    constructor
    · rintro ⟨ν, hν⟩
      refine ⟨(toConv χ * toConv ν).ofConv, ?_⟩
      rw [AlgHom.convMul_comp_bialgHom_distrib, ofConv_toConv, ofConv_toConv, toConv_ofConv, ← mul_assoc]
      rw [hφ, toConv_ofConv] at hν
      exact hν
    · rintro ⟨ν', hν'⟩
      refine ⟨((↑u⁻¹ : WithConv (H' →ₐ[R] Ω)) * toConv ν').ofConv, ?_⟩
      rw [hφ, toConv_ofConv, AlgHom.convMul_comp_bialgHom_distrib, ofConv_toConv, toConv_ofConv, mul_assoc,
        ← mul_assoc (toConv (χ.comp (qc : H →ₐ[R] H')))]

      have hcancel : toConv (χ.comp (qc : H →ₐ[R] H')) *
          toConv (((↑u⁻¹ : WithConv (H' →ₐ[R] Ω)).ofConv).comp (qc : H →ₐ[R] H')) = 1 := by
        have := AlgHom.convMul_comp_bialgHom_distrib (toConv χ) (↑u⁻¹ : WithConv (H' →ₐ[R] Ω)) qc
        rw [ofConv_toConv] at this
        rw [← toConv_ofConv (toConv (χ.comp _) * _), ← this, ← hu, ← Units.val_mul, mul_inv_cancel,
          Units.val_one]
        exact hν₀
      rw [hcancel, one_mul]
      exact hν'
  ·
    have hDe : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum H)) :=
      PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
    obtain ⟨e₀, -, huniq₀⟩ := PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen hDe
    have h1 : f * e = e₀ := huniq₀ (f * e) ⟨hf.mul he, ?_⟩
    · have h2 : e = e₀ := huniq₀ e ⟨he, rfl⟩
      rw [h1, ← h2]
    · rw [PrimeSpectrum.basicOpen_mul, TopologicalSpace.Opens.coe_inf, ← hfU, Set.union_inter_cancel_left]
  ·
    intro b hb hbe
    apply eq_of_forall_algHom_apply_eq (R := R) (K := K) (A := H) Ω
    intro ψ
    rw [map_zero, map_mul]
    rcases apply_eq_zero_or_one hf ψ with h0 | h1
    · rw [h0, mul_zero]
    · obtain ⟨ν, hν⟩ := (horbit ψ).mp h1
      have hinv := convMul_apply_eq_of_mem_hopfKer (Ω := Ω) qc hb ψ ν
      set φ : H →ₐ[R] Ω := (toConv ψ * toConv (ν.comp (qc : H →ₐ[R] H'))).ofConv
      have : φ b = 0 := by
        have h := congrArg φ hbe
        rw [map_mul, map_zero] at h
        change φ e = 1 at hν
        rwa [hν, mul_one] at h
      change φ b = ψ b at hinv
      rw [← hinv, this, zero_mul]

end S_HopfAlgebra_exists_isIdempotentElem_mem_hopfKer_mul_eq_of_finitePartIdempotent
end P2MW
export P2MW.S_HopfAlgebra_exists_isIdempotentElem_mem_hopfKer_mul_eq_of_finitePartIdempotent (solution)
