-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/db7d2a8e-4b39-5e7d-9f56-606b9436d42e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_isFractionRing_tensorProduct_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_flat_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_Algebra_Smooth_isIntegrallyClosed_of_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth_of_isIntegrallyClosed

set_option autoImplicit false

open scoped TensorProduct
p2m_open "AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel ModularCurve P2MW.S_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth_of_isIntegrallyClosed.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange isFractionRing_tensorProduct_laurentBaseChange baseChangeHom baseChangeHom_tmul baseChangeHom_injective baseChangeHom_mem"
namespace ChartBaseChangeAux
p2m_open "ModularCurve"

section ClearDenominators

open Polynomial

attribute [local instance] Polynomial.algebra

theorem exists_int_mul_isIntegral_adjoin_int {F : Type*} [Field F] [CharZero F] (x z : F)
    (hz : IsIntegral ↥(Algebra.adjoin ℚ ({x} : Set F)) z) :
    ∃ n : ℤ, n ≠ 0 ∧ IsIntegral ↥(Algebra.adjoin ℤ ({x} : Set F)) ((n : F) * z) := by
  classical

  letI algZ : Algebra ℤ[X] F := (aeval (R := ℤ) x).toRingHom.toAlgebra
  letI algQ : Algebra ℚ[X] F := (aeval (R := ℚ) x).toRingHom.toAlgebra
  have hZ : ∀ P : ℤ[X], algebraMap ℤ[X] F P = aeval x P := fun _ => rfl
  have hQ : ∀ P : ℚ[X], algebraMap ℚ[X] F P = aeval x P := fun _ => rfl
  haveI : IsScalarTower ℤ[X] ℚ[X] F := by
    refine IsScalarTower.of_algebraMap_eq fun P => ?_
    rw [hZ, hQ, Polynomial.algebraMap_def, coe_mapRingHom, aeval_map_algebraMap]
  haveI : IsLocalization ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X])) ℚ[X] :=
    Polynomial.isLocalization (nonZeroDivisors ℤ) ℚ

  have hzQ : IsIntegral ℚ[X] z := by
    obtain ⟨P, hPm, hPz⟩ := hz

    let π : ℚ[X] →+* ↥(Algebra.adjoin ℚ ({x} : Set F)) :=
      ((aeval (R := ℚ) x).codRestrict (Algebra.adjoin ℚ ({x} : Set F))
        (fun Q => by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨Q, rfl⟩)).toRingHom
    have hπ : Function.Surjective π := by
      rintro ⟨c, hc⟩
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
      obtain ⟨Q, rfl⟩ := hc
      exact ⟨Q, rfl⟩
    obtain ⟨Q, hQP, -, hQm⟩ := lifts_and_degree_eq_and_monic (map_surjective π hπ P) hPm
    refine ⟨Q, hQm, ?_⟩
    have hcomp : (algebraMap ↥(Algebra.adjoin ℚ ({x} : Set F)) F).comp π = algebraMap ℚ[X] F := by
      ext Q
      · simp [π, hQ]
      · simp [π, hQ]
    rw [← hcomp, ← eval₂_map, hQP]
    exact hPz
  obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    ((nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X])) z hzQ
  obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.mp hm
  refine ⟨n, nonZeroDivisors.ne_zero hn, ?_⟩
  have hsmul : (⟨C n, hm⟩ : (nonZeroDivisors ℤ).map (C : ℤ →+* ℤ[X])) • z = (n : F) * z := by
    change algebraMap ℤ[X] F (C n) * z = _
    rw [hZ, aeval_C]
    simp
  rw [hsmul] at hint

  let φ : ℤ[X] →+* ↥(Algebra.adjoin ℤ ({x} : Set F)) :=
    ((aeval (R := ℤ) x).codRestrict (Algebra.adjoin ℤ ({x} : Set F))
      (fun Q => by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨Q, rfl⟩)).toRingHom
  refine hint.map_of_comp_eq φ (RingHom.id F) ?_
  ext Q
  · simp [φ, hZ]
  · simp [φ, hZ]

end ClearDenominators

theorem eq_zero_of_sum_single_mul_coeffEmb_eq_zero (L : Type) [Field L] [CharZero L]
    {ι : Type} (s : Finset ι) (a : ι → L) (ha : LinearIndependent ℚ a)
    (f : ι → LaurentSeries ℚ) (h : ∑ i ∈ s, HahnSeries.single 0 (a i) * coeffEmb L (f i) = 0) :
    ∀ i ∈ s, f i = 0 := by
  intro i hi
  ext k
  have hk : (∑ i ∈ s, HahnSeries.single 0 (a i) * coeffEmb L (f i)).coeff k = 0 := by rw [h]; rfl
  rw [HahnSeries.coeff_sum] at hk
  simp only [HahnSeries.coeff_single_zero_mul, coeffEmb_coeff] at hk
  have hk' : ∑ j ∈ s, ((f j).coeff k) • a j = 0 := by
    rw [← hk]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have := linearIndependent_iff'.mp ha s (fun j => (f j).coeff k) hk' i hi
  simpa using this

noncomputable def coeffEmbK (L : Type) [Field L] [CharZero L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) : ↥F₀ →+* ↥(laurentBaseChange L F₀) where
  toFun f := ⟨coeffEmb L ((f : ↥F₀) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L f.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' b c := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' b c := Subtype.ext (by simp)

theorem coe_coeffEmbK (L : Type) [Field L] [CharZero L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (f : ↥F₀) :
    ((coeffEmbK L F₀ f : ↥(laurentBaseChange L F₀)) : LaurentSeries L) = coeffEmb L (f : LaurentSeries ℚ) :=
  rfl

set_option maxHeartbeats 160000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem mem_of_eval₂_coeffEmbK_eq_zero (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (Bq : Subalgebra ℚ ↥F₀)
    (hclosed : ∀ z : ↥F₀, IsIntegral ↥Bq z → z ∈ Bq)
    (D : Subring ↥(laurentBaseChange L F₀))
    (hDL : ∀ c : L, algebraMap L ↥(laurentBaseChange L F₀) c ∈ D)
    (hDB : ∀ β : ↥F₀, β ∈ Bq → coeffEmbK L F₀ β ∈ D)
    (y : ↥(laurentBaseChange L F₀)) (P : Polynomial ↥Bq) (hPm : P.Monic)
    (hPy : Polynomial.eval₂ ((coeffEmbK L F₀).comp (algebraMap ↥Bq ↥F₀)) y P = 0) :
    y ∈ D := by
  classical

  letI iA1 : Algebra ↥Bq ↥F₀ := inferInstance
  letI iM1 : Module ↥Bq ↥F₀ := inferInstance
  letI iA2 : Algebra ↥Bq (↥Bq ⊗[ℚ] L) := inferInstance
  letI iM2 : Module ↥Bq (↥Bq ⊗[ℚ] L) := inferInstance
  letI iR3 : CommRing ((↥Bq ⊗[ℚ] L) ⊗[↥Bq] ↥F₀) := inferInstance
  letI iA3 : Algebra (↥Bq ⊗[ℚ] L) ((↥Bq ⊗[ℚ] L) ⊗[↥Bq] ↥F₀) := inferInstance
  letI iA3' : Algebra ↥Bq ((↥Bq ⊗[ℚ] L) ⊗[↥Bq] ↥F₀) := inferInstance
  letI iM3 : Module ↥Bq ((↥Bq ⊗[ℚ] L) ⊗[↥Bq] ↥F₀) := inferInstance

  haveI : Algebra.IsSeparable ℚ L := Algebra.IsSeparable.of_integral ℚ L
  haveI : Algebra.FormallyEtale ℚ L := Algebra.FormallyEtale.of_isSeparable ℚ L
  haveI : Algebra.FinitePresentation ℚ L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.Smooth ℚ L := ⟨inferInstance, inferInstance⟩

  letI algBqK : Algebra ↥Bq ↥(laurentBaseChange L F₀) := ((coeffEmbK L F₀).comp (algebraMap ↥Bq ↥F₀)).toAlgebra
  haveI : IsScalarTower ℚ ↥Bq ↥(laurentBaseChange L F₀) :=
    IsScalarTower.of_algebraMap_eq fun q => RingHom.congr_fun
      (Subsingleton.elim (algebraMap ℚ ↥(laurentBaseChange L F₀)) ((algebraMap ↥Bq ↥(laurentBaseChange L F₀)).comp (algebraMap ℚ ↥Bq))) q
  let gL : L →ₐ[ℚ] ↥(laurentBaseChange L F₀) :=
    { algebraMap L ↥(laurentBaseChange L F₀) with
      commutes' := fun q => RingHom.congr_fun
        (Subsingleton.elim ((algebraMap L ↥(laurentBaseChange L F₀)).comp (algebraMap ℚ L)) (algebraMap ℚ ↥(laurentBaseChange L F₀))) q }

  obtain ⟨ΘS, hΘS⟩ : ∃ ΘS : ↥Bq ⊗[ℚ] L →ₐ[↥Bq] ↥(laurentBaseChange L F₀), ∀ (β : ↥Bq) (c : L),
      ΘS (β ⊗ₜ c) = coeffEmbK L F₀ (β : ↥F₀) * algebraMap L ↥(laurentBaseChange L F₀) c :=
    ⟨Algebra.TensorProduct.lift (Algebra.ofId _ _) gL (fun _ _ => Commute.all _ _),
      fun β c => by rw [Algebra.TensorProduct.lift_tmul]; rfl⟩

  let GF : ↥F₀ →ₐ[↥Bq] ↥(laurentBaseChange L F₀) := { coeffEmbK L F₀ with commutes' := fun _ => rfl }

  obtain ⟨Θ₂, hΘ₂⟩ : ∃ Θ₂ : (↥Bq ⊗[ℚ] L) ⊗[↥Bq] ↥F₀ →ₐ[↥Bq] ↥(laurentBaseChange L F₀),
      ∀ (s : ↥Bq ⊗[ℚ] L) (f : ↥F₀), Θ₂ (s ⊗ₜ f) = ΘS s * coeffEmbK L F₀ f :=
    ⟨Algebra.TensorProduct.lift ΘS GF (fun _ _ => Commute.all _ _),
      fun s f => by rw [Algebra.TensorProduct.lift_tmul]; rfl⟩

  have hΘ₂inj : Function.Injective Θ₂ := by
    let bL := Module.finBasis ℚ L
    let bS := Algebra.TensorProduct.basis ↥Bq bL
    have hbS : ∀ i, bS i = 1 ⊗ₜ bL i := fun i => Algebra.TensorProduct.basis_apply bL i
    let eT : (↥Bq ⊗[ℚ] L) ⊗[↥Bq] ↥F₀ ≃ₗ[↥Bq] (Fin (Module.finrank ℚ L) →₀ ↥F₀) :=
      (TensorProduct.congr bS.repr (LinearEquiv.refl _ ↥F₀)).trans
        (TensorProduct.finsuppScalarLeft _ ↥F₀ _)
    have heT : ∀ (i) (c : ↥F₀), eT.symm (Finsupp.single i c) = bS i ⊗ₜ c := by
      intro i c
      simp [eT, TensorProduct.finsuppScalarLeft_symm_apply_single]
    rw [injective_iff_map_eq_zero]
    intro t ht
    set c := eT t with hc
    have ht' : t = c.sum fun i ci => bS i ⊗ₜ ci := by
      conv_lhs => rw [← eT.symm_apply_apply t, ← hc, ← Finsupp.sum_single c]
      rw [map_finsuppSum]
      exact Finsupp.sum_congr fun i _ => heT i (c i)
    have hsum : ∑ i ∈ c.support, HahnSeries.single 0 (bL i) *
        coeffEmb L (((c i : ↥F₀)) : LaurentSeries ℚ) = 0 := by
      have h1 : Θ₂ t = ∑ i ∈ c.support, Θ₂ (bS i ⊗ₜ c i) := by rw [ht', Finsupp.sum, map_sum]
      have h0 : algebraMap ↥(laurentBaseChange L F₀) (LaurentSeries L) (Θ₂ t) = 0 := by rw [ht, map_zero]
      rw [h1, map_sum] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hΘ₂, hbS, hΘS, OneMemClass.coe_one, map_one, one_mul, map_mul,
        ← IsScalarTower.algebraMap_apply L ↥(laurentBaseChange L F₀) (LaurentSeries L),
        ModularCurve.algebraMap_laurentSeries_eq_single]
      rfl
    have hzero := eq_zero_of_sum_single_mul_coeffEmb_eq_zero L c.support
      (fun i => bL i) bL.linearIndependent (fun i => (((c i : ↥F₀)) : LaurentSeries ℚ)) hsum
    have hc0 : c = 0 := by
      refine Finsupp.ext fun i => ?_
      by_cases hi : i ∈ c.support
      · exact Subtype.ext (hzero i hi)
      · exact Finsupp.notMem_support_iff.mp hi
    rw [ht', hc0, Finsupp.sum_zero_index]

  obtain ⟨n, c, f, hf, hy⟩ :=
    ModularCurve.exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange L F₀ (y : LaurentSeries L) y.2
  let w : (↥Bq ⊗[ℚ] L) ⊗[↥Bq] ↥F₀ := ∑ i, ((1 : ↥Bq) ⊗ₜ[ℚ] c i) ⊗ₜ (⟨f i, hf i⟩ : ↥F₀)
  have hw : Θ₂ w = y := by
    apply Subtype.ext
    change ((Θ₂ w : ↥(laurentBaseChange L F₀)) : LaurentSeries L) = (y : LaurentSeries L)
    rw [hy, map_sum]
    change algebraMap ↥(laurentBaseChange L F₀) (LaurentSeries L) (∑ i, _) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ₂, hΘS, OneMemClass.coe_one, map_one, one_mul, map_mul,
      ← IsScalarTower.algebraMap_apply L ↥(laurentBaseChange L F₀) (LaurentSeries L),
      ModularCurve.algebraMap_laurentSeries_eq_single]
    rfl

  have hcompΘ : (Θ₂ : _ →+* ↥(laurentBaseChange L F₀)).comp ((algebraMap (↥Bq ⊗[ℚ] L) ((↥Bq ⊗[ℚ] L) ⊗[↥Bq] ↥F₀)).comp
      (algebraMap ↥Bq (↥Bq ⊗[ℚ] L))) = (coeffEmbK L F₀).comp (algebraMap ↥Bq ↥F₀) := by
    refine RingHom.ext fun β => ?_
    show Θ₂ (algebraMap _ _ (algebraMap _ _ β)) = coeffEmbK L F₀ (β : ↥F₀)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
    change Θ₂ ((β ⊗ₜ[ℚ] (1 : L)) ⊗ₜ[↥Bq] (1 : ↥F₀)) = _
    rw [hΘ₂, hΘS, map_one, mul_one, map_one, mul_one]
  have hwint : IsIntegral (↥Bq ⊗[ℚ] L) w := by
    refine ⟨P.map (algebraMap _ _), hPm.map _, hΘ₂inj ?_⟩
    rw [Polynomial.eval₂_map, map_zero, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂, hcompΘ]
    change Polynomial.eval₂ _ (Θ₂ w) P = 0
    rw [hw]
    exact hPy

  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := ↥Bq) (S := ↥Bq ⊗[ℚ] L) (B := ↥F₀)).2 ⟨w, hwint⟩
  have htw : Algebra.TensorProduct.map (AlgHom.id _ _) (integralClosure _ _).val t = w :=
    congrArg Subtype.val ht

  rw [← hw, ← htw]
  clear ht htw
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem D
  | tmul s z =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hΘ₂]
    refine mul_mem ?_ (hDB _ (hclosed _ z.2))
    induction s using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem D
    | tmul β c' => rw [hΘS]; exact mul_mem (hDB _ β.2) (hDL c')
    | add s₁ s₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add]; exact add_mem h₁ h₂

end ModularCurve.ChartBaseChangeAux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (x : ↥F₀)
    [Algebra.IsAlgebraic ↥(IntermediateField.adjoin ℚ ({x} : Set ↥F₀)) ↥F₀]
    (hsm : Algebra.Smooth ↥(GaloisRep.ratLocalizedAt p)
      ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ ({x} : Set ↥F₀)))
    (L : Type) [Field L] [CharZero L]
    (K' : IntermediateField L (LaurentSeries L)) (hK' : K' = ModularCurve.laurentBaseChange L F₀)
    (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra A L] [IsFractionRing A L]
    [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (x' : ↥K') (hx' : ((x' : LaurentSeries L)) = ModularCurve.coeffEmb L ((x : ↥F₀) : LaurentSeries ℚ)) :
    ∃ e : A ⊗[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ ({x} : Set ↥F₀)) ≃ₐ[A]
        ↥(TwoChartIntegralModel.chartAlg A ↥K' ({x'} : Set ↥K')),
      ∀ b : ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ ({x} : Set ↥F₀)),
        (((e (1 ⊗ₜ b) : ↥K') : LaurentSeries L)) =
          ModularCurve.coeffEmb L (((b : ↥F₀) : LaurentSeries ℚ)) := by
  have hp : p.Prime := Fact.out
  subst hK'

  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  have hloc := GaloisRep.isLocalization_ratLocalizedAt hp
  have hext : ∀ {T : Type} [CommRing T] (f g : ↥(GaloisRep.ratLocalizedAt p) →+* T), f = g := by
    intro T _ f g
    exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (Subsingleton.elim _ _)

  letI algRK : Algebra ↥(GaloisRep.ratLocalizedAt p) ↥(laurentBaseChange L F₀) :=
    ((algebraMap A ↥(laurentBaseChange L F₀)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) A)).toAlgebra
  haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A ↥(laurentBaseChange L F₀) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl

  set B := TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ ({x} : Set ↥F₀) with hB

  let G₀ : ↥F₀ →+* ↥(laurentBaseChange L F₀) := ChartBaseChangeAux.coeffEmbK L F₀
  have hG₀ : ∀ f : ↥F₀, ((G₀ f : ↥(laurentBaseChange L F₀)) : LaurentSeries L) = coeffEmb L (f : LaurentSeries ℚ) :=
    fun _ => rfl
  have hG₀R : G₀.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀) =
      algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(laurentBaseChange L F₀) := hext _ _
  have hG₀x : G₀ x = x' := Subtype.ext (by rw [hG₀, hx'])
  let g₀ : ↥B →+* ↥(laurentBaseChange L F₀) := G₀.comp B.val.toRingHom
  have hgcomm : g₀.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥B) =
      algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(laurentBaseChange L F₀) := hext _ _
  have hg₀ : ∀ b : ↥B, g₀ b = G₀ (b : ↥F₀) := fun _ => rfl
  let g : ↥B →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(laurentBaseChange L F₀) :=
    { g₀ with commutes' := fun r => RingHom.congr_fun hgcomm r }
  let ψ : A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B →ₐ[A] ↥(laurentBaseChange L F₀) :=
    Algebra.TensorProduct.lift (Algebra.ofId A _) g (fun _ _ => Commute.all _ _)
  have hψ : ∀ (a : A) (b : ↥B), ψ (a ⊗ₜ b) = algebraMap A _ a * g b := fun a b =>
    Algebra.TensorProduct.lift_tmul _ _ _ a b

  have hinj : Function.Injective ψ := by
    haveI hRdvr := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp
    haveI hRfrac := GaloisRep.isFractionRing_ratLocalizedAt p
    have hAinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

    have hRQ : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) := IsFractionRing.injective _ _
    have hRF₀ : Function.Injective (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀) := by
      rw [hext (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀) ((algebraMap ℚ ↥F₀).comp (algebraMap _ ℚ))]
      exact (algebraMap ℚ ↥F₀).injective.comp hRQ
    haveI : Module.Flat ↥(GaloisRep.ratLocalizedAt p) ↥B := TwoChartIntegralModel.flat_chartAlg hRF₀ ({x} : Set ↥F₀)
    haveI : Module.Flat ↥(GaloisRep.ratLocalizedAt p) ℚ := IsLocalization.flat ℚ (nonZeroDivisors ↥(GaloisRep.ratLocalizedAt p))
    haveI : Module.Flat ↥(GaloisRep.ratLocalizedAt p) L := Module.Flat.trans ↥(GaloisRep.ratLocalizedAt p) ℚ L

    haveI hcompat : TensorProduct.CompatibleSMul ↥(GaloisRep.ratLocalizedAt p) ℚ L ↥F₀ := by
      refine ⟨fun c m n => ?_⟩
      obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := ↥(GaloisRep.ratLocalizedAt p)) c
      have hs0 : algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      have hsm : ∀ (M : Type) [AddCommGroup M] [Module ℚ M] [Module ↥(GaloisRep.ratLocalizedAt p) M]
          [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ M] (m : M),
          (s : ↥(GaloisRep.ratLocalizedAt p)) • ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ s)⁻¹ • m) = m := by
        intro M _ _ _ _ m
        rw [← IsScalarTower.algebraMap_smul ℚ s, smul_smul, mul_inv_cancel₀ hs0, one_smul]
      calc ((algebraMap _ ℚ r / algebraMap _ ℚ s) • m) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] n
          = ((r : ↥(GaloisRep.ratLocalizedAt p)) • ((algebraMap _ ℚ s)⁻¹ • m)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] n := by
            rw [div_eq_mul_inv, mul_comm, ← smul_smul, IsScalarTower.algebraMap_smul, smul_comm]
        _ = ((algebraMap _ ℚ s)⁻¹ • m) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] ((r : ↥(GaloisRep.ratLocalizedAt p)) • n) := by
            rw [TensorProduct.smul_tmul]
        _ = ((algebraMap _ ℚ s)⁻¹ • m) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)]
              ((s : ↥(GaloisRep.ratLocalizedAt p)) • ((algebraMap _ ℚ s)⁻¹ • ((r : ↥(GaloisRep.ratLocalizedAt p)) • n))) := by
            rw [hsm ↥F₀]
        _ = ((s : ↥(GaloisRep.ratLocalizedAt p)) • ((algebraMap _ ℚ s)⁻¹ • m)) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)]
              ((algebraMap _ ℚ s)⁻¹ • ((r : ↥(GaloisRep.ratLocalizedAt p)) • n)) := by
            rw [← TensorProduct.smul_tmul]
        _ = m ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] ((algebraMap _ ℚ r / algebraMap _ ℚ s) • n) := by
            rw [hsm L, ← IsScalarTower.algebraMap_smul ℚ r, smul_smul, div_eq_mul_inv, mul_comm]

    let ιₗ : A →ₗ[↥(GaloisRep.ratLocalizedAt p)] L := (IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) A L).toLinearMap
    let vₗ : ↥B →ₗ[↥(GaloisRep.ratLocalizedAt p)] ↥F₀ := B.val.toLinearMap
    let f₁ := ιₗ.rTensor ↥B
    let f₂ := vₗ.lTensor L
    let f₃ := TensorProduct.equivOfCompatibleSMul ℚ ↥(GaloisRep.ratLocalizedAt p) ↥(GaloisRep.ratLocalizedAt p) L ↥F₀
    have hf₁ : Function.Injective f₁ := Module.Flat.rTensor_preserves_injective_linearMap ιₗ hAinj
    have hf₂ : Function.Injective f₂ := Module.Flat.lTensor_preserves_injective_linearMap vₗ Subtype.val_injective
    have hF : ∀ t, (((ψ t) : ↥(laurentBaseChange L F₀)) : LaurentSeries L) = baseChangeHom L F₀ (f₃ (f₂ (f₁ t))) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero, ZeroMemClass.coe_zero]
      | tmul a b =>
        rw [hψ, MulMemClass.coe_mul, IsScalarTower.algebraMap_apply A L ↥(laurentBaseChange L F₀),
          show ((algebraMap L ↥(laurentBaseChange L F₀) (algebraMap A L a) : ↥(laurentBaseChange L F₀)) : LaurentSeries L) =
            algebraMap L (LaurentSeries L) (algebraMap A L a) from rfl]
        show _ = baseChangeHom L F₀ (f₃ (f₂ (ιₗ.rTensor ↥B (a ⊗ₜ b))))
        rw [LinearMap.rTensor_tmul]
        show _ = baseChangeHom L F₀ (f₃ (vₗ.lTensor L (ιₗ a ⊗ₜ b)))
        rw [LinearMap.lTensor_tmul]
        show _ = baseChangeHom L F₀ (ιₗ a ⊗ₜ vₗ b)
        rw [baseChangeHom_tmul]
        rfl
      | add s t hs ht => simp only [map_add, AddMemClass.coe_add, hs, ht]
    rw [injective_iff_map_eq_zero]
    intro t ht
    have h1 : baseChangeHom L F₀ (f₃ (f₂ (f₁ t))) = 0 := by rw [← hF, ht]; rfl
    rw [← map_zero (baseChangeHom L F₀)] at h1
    have h2 := baseChangeHom_injective L F₀ h1
    rw [← map_zero f₃] at h2
    have h3 := f₃.injective h2
    rw [← map_zero f₂] at h3
    have h4 := hf₂ h3
    rw [← map_zero f₁] at h4
    exact hf₁ h4

  have hle : ψ.range ≤ (TwoChartIntegralModel.chartAlg A ↥(laurentBaseChange L F₀) ({x'} : Set _)) := by

    set C := Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({x} : Set ↥F₀) with hC
    set C' := Algebra.adjoin A ({x'} : Set ↥(laurentBaseChange L F₀)) with hC'
    have hCC' : C.toSubring.map G₀ ≤ C'.toSubring := by
      rw [Subring.map_le_iff_le_comap]

      have h1 : ∀ r : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀ r ∈ C'.toSubring.comap G₀ := by
        intro r
        change G₀ (algebraMap _ _ r) ∈ C'
        have : G₀ (algebraMap _ _ r) = algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(laurentBaseChange L F₀) r :=
          RingHom.congr_fun hG₀R r
        rw [this, IsScalarTower.algebraMap_apply ↥(GaloisRep.ratLocalizedAt p) A ↥(laurentBaseChange L F₀)]
        exact Subalgebra.algebraMap_mem C' _
      let D : Subalgebra ↥(GaloisRep.ratLocalizedAt p) ↥F₀ :=
        { C'.toSubring.comap G₀ with
          algebraMap_mem' := h1 }
      have hxD : x ∈ D := by change G₀ x ∈ C'; rw [hG₀x]; exact Algebra.subset_adjoin rfl
      have hCD : C ≤ D := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxD)
      intro c hc
      exact hCD hc

    have hint : ∀ b : ↥B, IsIntegral C' ((g₀ b : ↥(laurentBaseChange L F₀))) := by
      intro b
      have hb : IsIntegral C ((b : ↥F₀)) := (mem_chartAlg_iff _ _).mp b.2
      let φ : C →+* C' := (Subring.inclusion hCC').comp ((G₀.restrict C.toSubring (C.toSubring.map G₀)
        fun c hc => Subring.mem_map.mpr ⟨c, hc, rfl⟩))
      refine hb.map_of_comp_eq φ G₀ ?_
      ext c; rfl
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a b =>
      change ψ (a ⊗ₜ b) ∈ _
      rw [hψ]
      refine mul_mem (Subalgebra.algebraMap_mem _ a) ?_
      exact (mem_chartAlg_iff _ _).mpr (hint b)
    | add s t hs ht => rw [map_add]; exact add_mem hs ht

  have hge : (TwoChartIntegralModel.chartAlg A ↥(laurentBaseChange L F₀) ({x'} : Set _)) ≤ ψ.range := by
    intro y hy
    classical
    haveI hRfrac' := GaloisRep.isFractionRing_ratLocalizedAt p

    have hx'r : x' ∈ ψ.range := by
      refine ⟨(1 : A) ⊗ₜ (⟨x, subset_chartAlg _ _ _ rfl⟩ : ↥B), ?_⟩
      change ψ ((1 : A) ⊗ₜ (⟨x, subset_chartAlg _ _ _ rfl⟩ : ↥B)) = x'
      rw [hψ, map_one, one_mul]
      exact hG₀x
    have hC'le : Algebra.adjoin A ({x'} : Set ↥(laurentBaseChange L F₀)) ≤ ψ.range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx'r)
    have hy1 : IsIntegral ↥ψ.range y :=
      ((mem_chartAlg_iff _ _).mp hy).map_of_comp_eq (Subalgebra.inclusion hC'le).toRingHom
        (RingHom.id _) (by ext; rfl)

    haveI hTdom : IsDomain (A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B) :=
      Function.Injective.isDomain ψ.toRingHom hinj
    have hIC : IsIntegrallyClosed (A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B) :=
      Algebra.Smooth.isIntegrallyClosed_of_isDomain A (A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B)

    letI algTK : Algebra (A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B) ↥(laurentBaseChange L F₀) := ψ.toRingHom.toAlgebra
    have halgTK : ∀ t, algebraMap (A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B) ↥(laurentBaseChange L F₀) t = ψ t :=
      fun _ => rfl
    have hψne : ∀ {t : A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B}, ψ t ≠ 0 → t ≠ 0 := by
      intro t h h0; exact h (by rw [h0, map_zero])
    have hAK : ∀ {a : A}, a ≠ 0 → algebraMap A ↥(laurentBaseChange L F₀) a ≠ 0 := by
      intro a ha
      rw [IsScalarTower.algebraMap_apply A L ↥(laurentBaseChange L F₀)]
      exact (map_ne_zero_iff _ (algebraMap L ↥(laurentBaseChange L F₀)).injective).mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr ha)
    have hG₀inj : Function.Injective G₀ := G₀.injective
    have hgK : ∀ {b : ↥B}, b ≠ 0 → g b ≠ 0 := by
      intro b hb
      change G₀ (b : ↥F₀) ≠ 0
      have hb' : ((b : ↥B) : ↥F₀) ≠ 0 := fun h => hb (Subtype.ext (by rw [h]; rfl))
      exact (map_ne_zero_iff G₀ hG₀inj).mpr hb'
    haveI hBfrac : IsFractionRing ↥B ↥F₀ :=
      TwoChartIntegralModel.isFractionRing_chartAlg ↥(GaloisRep.ratLocalizedAt p) ℚ ↥F₀ ({x} : Set ↥F₀)
    letI algLF : Algebra (L ⊗[ℚ] ↥F₀) ↥(laurentBaseChange L F₀) :=
      ((baseChangeHom L F₀).codRestrict (laurentBaseChange L F₀).toSubalgebra (baseChangeHom_mem L F₀)).toRingHom.toAlgebra
    haveI hLFfrac : IsFractionRing (L ⊗[ℚ] ↥F₀) ↥(laurentBaseChange L F₀) :=
      ModularCurve.isFractionRing_tensorProduct_laurentBaseChange L F₀
    have halgLF : ∀ u : L ⊗[ℚ] ↥F₀,
        ((algebraMap (L ⊗[ℚ] ↥F₀) ↥(laurentBaseChange L F₀) u : ↥(laurentBaseChange L F₀)) : LaurentSeries L) =
          baseChangeHom L F₀ u := fun _ => rfl

    have hP : ∀ u : L ⊗[ℚ] ↥F₀, ∃ t s : A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B, ψ s ≠ 0 ∧
        algebraMap (L ⊗[ℚ] ↥F₀) ↥(laurentBaseChange L F₀) u * ψ s = ψ t := by
      intro u
      induction u using TensorProduct.induction_on with
      | zero => exact ⟨0, 1, by rw [map_one]; exact one_ne_zero, by rw [map_zero, map_zero, zero_mul]⟩
      | tmul l f =>
        obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) l
        obtain ⟨b, e, he, rfl⟩ := IsFractionRing.div_surjective (A := ↥B) f
        have hd0 : (d : A) ≠ 0 := nonZeroDivisors.ne_zero hd
        have he0 : (e : ↥B) ≠ 0 := nonZeroDivisors.ne_zero he
        refine ⟨a ⊗ₜ b, (d : A) ⊗ₜ (e : ↥B), ?_, ?_⟩
        · rw [hψ]; exact mul_ne_zero (hAK hd0) (hgK he0)
        · apply Subtype.ext
          rw [MulMemClass.coe_mul, halgLF, baseChangeHom_tmul, hψ, hψ, MulMemClass.coe_mul, MulMemClass.coe_mul,
            IsScalarTower.algebraMap_apply A L ↥(laurentBaseChange L F₀),
            IsScalarTower.algebraMap_apply A L ↥(laurentBaseChange L F₀)]
          change algebraMap L (LaurentSeries L) (algebraMap A L a / algebraMap A L ↑d) *
              coeffEmb L (((algebraMap (↥B) (↥F₀) b / algebraMap (↥B) (↥F₀) ↑e : ↥F₀) : LaurentSeries ℚ)) *
              (algebraMap L (LaurentSeries L) (algebraMap A L ↑d) * coeffEmb L (((e : ↥B) : ↥F₀) : LaurentSeries ℚ)) =
            algebraMap L (LaurentSeries L) (algebraMap A L a) * coeffEmb L (((b : ↥B) : ↥F₀) : LaurentSeries ℚ)
          have hdL : algebraMap L (LaurentSeries L) (algebraMap A L ↑d) ≠ 0 :=
            (map_ne_zero_iff _ (algebraMap L (LaurentSeries L)).injective).mpr
              ((map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr hd0)
          have heL : coeffEmb L (((e : ↥B) : ↥F₀) : LaurentSeries ℚ) ≠ 0 := by
            rw [← hG₀]; exact Subtype.coe_injective.ne (hgK he0)
          rw [map_div₀, show (((algebraMap (↥B) (↥F₀) b / algebraMap (↥B) (↥F₀) ↑e : ↥F₀)) : LaurentSeries ℚ) =
              (((b : ↥B) : ↥F₀) : LaurentSeries ℚ) / (((e : ↥B) : ↥F₀) : LaurentSeries ℚ) from rfl, map_div₀]
          field_simp
      | add u u' hu hu' =>
        obtain ⟨t, s, hs, h⟩ := hu
        obtain ⟨t', s', hs', h'⟩ := hu'
        refine ⟨t * s' + t' * s, s * s', by rw [map_mul]; exact mul_ne_zero hs hs', ?_⟩
        rw [map_add, map_add, map_mul, map_mul, map_mul, add_mul, ← mul_assoc, h, mul_comm (ψ s) (ψ s'), ← mul_assoc, h']
    haveI hfracT : IsFractionRing (A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B) ↥(laurentBaseChange L F₀) := by
      refine ⟨fun s => ?_, fun z => ?_, fun {t t'} h => ⟨1, by simpa using hinj h⟩⟩
      · exact isUnit_iff_ne_zero.mpr fun h0 => nonZeroDivisors.ne_zero s.2 (hinj (by rw [map_zero]; exact h0))
      · obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := L ⊗[ℚ] ↥F₀) z
        obtain ⟨t, s, hs, h⟩ := hP u
        obtain ⟨t', s', hs', h'⟩ := hP (v : L ⊗[ℚ] ↥F₀)
        have hv0 : algebraMap (L ⊗[ℚ] ↥F₀) ↥(laurentBaseChange L F₀) v ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hv
        have ht' : ψ t' ≠ 0 := by rw [← h']; exact mul_ne_zero hv0 hs'
        refine ⟨(t * s', ⟨s * t', mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (hψne hs) (hψne ht'))⟩), ?_⟩
        show _ * ψ (s * t') = ψ (t * s')
        rw [map_mul, map_mul, ← h, ← h', div_mul_eq_mul_div, div_eq_iff hv0]
        ring

    have hyT : IsIntegral (A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B) y := by
      let eR := AlgEquiv.ofInjective ψ hinj
      have := hy1.map_of_comp_eq (eR.symm.toAlgHom.toRingHom) (RingHom.id _) (RingHom.ext fun z => by
        show ψ (eR.symm z) = (z : ↥(laurentBaseChange L F₀))
        rw [← AlgEquiv.ofInjective_apply ψ hinj (eR.symm z), AlgEquiv.apply_symm_apply])
      exact this
    obtain ⟨t, ht⟩ := (isIntegrallyClosed_iff ↥(laurentBaseChange L F₀)).mp hIC hyT
    exact ⟨t, ht⟩

  have hrange : ψ.range = TwoChartIntegralModel.chartAlg A ↥(laurentBaseChange L F₀) ({x'} : Set _) :=
    le_antisymm hle hge
  let e₁ := AlgEquiv.ofInjective ψ hinj
  let e₂ : ↥ψ.range ≃ₐ[A] ↥(TwoChartIntegralModel.chartAlg A ↥(laurentBaseChange L F₀) ({x'} : Set _)) :=
    Subalgebra.equivOfEq _ _ hrange
  refine ⟨e₁.trans e₂, fun b => ?_⟩
  change (((ψ (1 ⊗ₜ b)) : ↥(laurentBaseChange L F₀)) : LaurentSeries L) = _
  rw [hψ, map_one, one_mul]
  rfl

end S_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth_of_isIntegrallyClosed
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth_of_isIntegrallyClosed (solution)
