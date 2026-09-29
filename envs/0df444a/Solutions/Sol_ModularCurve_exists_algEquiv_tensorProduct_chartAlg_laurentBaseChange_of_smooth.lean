-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/54904944-6359-5c80-b198-e78bdae06120

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth

set_option autoImplicit false

open scoped TensorProduct
p2m_open "AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel ModularCurve P2MW.S_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange exists_sum_single_mul_coeffEmb_of_mem_laurentBaseChange"
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

set_option maxHeartbeats 160000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (x : ↥F₀)
    (hsm : Algebra.Smooth ↥(GaloisRep.ratLocalizedAt p)
      ↥(TwoChartIntegralModel.chartAlg ↥(GaloisRep.ratLocalizedAt p) ↥F₀ ({x} : Set ↥F₀)))
    (L : Type) [Field L] [CharZero L] [FiniteDimensional ℚ L]
    (K' : IntermediateField L (LaurentSeries L)) (hK' : K' = ModularCurve.laurentBaseChange L F₀)
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra ↥(GaloisRep.ratLocalizedAt p) A] [IsScalarTower ↥(GaloisRep.ratLocalizedAt p) A L]
    (hA : ∀ y : L, IsIntegral ↥(GaloisRep.ratLocalizedAt p) y ↔ ∃ a : A, algebraMap A L a = y)
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
    haveI : IsIntegralClosure A ↥(GaloisRep.ratLocalizedAt p) L :=
      ⟨hAinj, fun {y} => hA y⟩
    haveI : Algebra.IsSeparable ℚ L := Algebra.IsSeparable.of_integral ℚ L
    haveI : Module.Free ↥(GaloisRep.ratLocalizedAt p) A :=
      IsIntegralClosure.module_free ↥(GaloisRep.ratLocalizedAt p) ℚ L A
    let bA := Module.Free.chooseBasis ↥(GaloisRep.ratLocalizedAt p) A

    have hli : LinearIndependent ℚ (fun i => algebraMap A L (bA i)) := by
      rw [← LinearIndependent.iff_fractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ]
      exact bA.linearIndependent.map' ((Algebra.linearMap A L).restrictScalars ↥(GaloisRep.ratLocalizedAt p))
        (LinearMap.ker_eq_bot.mpr hAinj)

    let eT : A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B ≃ₗ[↥(GaloisRep.ratLocalizedAt p)] (_ →₀ ↥B) :=
      (TensorProduct.congr bA.repr (LinearEquiv.refl _ ↥B)).trans
        (TensorProduct.finsuppScalarLeft ↥(GaloisRep.ratLocalizedAt p) ↥B _)
    have heT : ∀ (i) (c : ↥B), eT.symm (Finsupp.single i c) = bA i ⊗ₜ c := by
      intro i c
      simp [eT, TensorProduct.finsuppScalarLeft_symm_apply_single]
    rw [injective_iff_map_eq_zero]
    intro t ht

    set c := eT t with hc
    have ht' : t = c.sum fun i ci => bA i ⊗ₜ ci := by
      conv_lhs => rw [← eT.symm_apply_apply t, ← hc, ← Finsupp.sum_single c]
      rw [map_finsuppSum]
      exact Finsupp.sum_congr fun i _ => heT i (c i)
    have hsum : ∑ i ∈ c.support, HahnSeries.single 0 (algebraMap A L (bA i)) *
        coeffEmb L (((c i : ↥B) : ↥F₀) : LaurentSeries ℚ) = 0 := by
      have h0 := congrArg (algebraMap ↥(laurentBaseChange L F₀) (LaurentSeries L)) ht
      rw [map_zero, ht', Finsupp.sum, map_sum, map_sum] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hψ, map_mul, IsScalarTower.algebraMap_apply A L ↥(laurentBaseChange L F₀),
        ← IsScalarTower.algebraMap_apply L ↥(laurentBaseChange L F₀) (LaurentSeries L),
        ModularCurve.algebraMap_laurentSeries_eq_single]
      rfl
    have hzero := ModularCurve.ChartBaseChangeAux.eq_zero_of_sum_single_mul_coeffEmb_eq_zero L c.support
      (fun i => algebraMap A L (bA i)) hli (fun i => (((c i : ↥B) : ↥F₀) : LaurentSeries ℚ)) hsum
    have hc0 : c = 0 := by
      refine Finsupp.ext fun i => ?_
      by_cases hi : i ∈ c.support
      · have := hzero i hi
        exact Subtype.ext (Subtype.ext this)
      · exact Finsupp.notMem_support_iff.mp hi
    rw [ht', hc0, Finsupp.sum_zero_index]

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
    haveI hAIC : IsIntegralClosure A ↥(GaloisRep.ratLocalizedAt p) L :=
      ⟨IsFractionRing.injective A L, fun {y} => hA y⟩

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

    letI algBK : Algebra ↥B ↥(laurentBaseChange L F₀) := g.toRingHom.toAlgebra
    have halgBK : ∀ b : ↥B, algebraMap ↥B ↥(laurentBaseChange L F₀) b = g b := fun _ => rfl
    haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ↥B ↥(laurentBaseChange L F₀) :=
      IsScalarTower.of_algebraMap_eq fun r => RingHom.congr_fun
        (hext (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(laurentBaseChange L F₀))
          (g.toRingHom.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥B))) r
    letI algBr : Algebra ↥B ↥ψ.range :=
      (ψ.rangeRestrict.toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          ↥B →ₐ[↥(GaloisRep.ratLocalizedAt p)] A ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥B).toRingHom).toAlgebra
    haveI : IsScalarTower ↥B ↥ψ.range ↥(laurentBaseChange L F₀) :=
      IsScalarTower.of_algebraMap_eq fun b => by
        change g b = ((ψ ((1 : A) ⊗ₜ b) : ↥(laurentBaseChange L F₀)))
        rw [hψ, map_one, one_mul]
    have hAint : ∀ a : A, IsIntegral ↥B (algebraMap A ↥(laurentBaseChange L F₀) a) := by
      intro a
      have h1 : IsIntegral ↥(GaloisRep.ratLocalizedAt p) a := IsIntegralClosure.isIntegral _ L a
      have h2 : IsIntegral ↥(GaloisRep.ratLocalizedAt p) (algebraMap A ↥(laurentBaseChange L F₀) a) :=
        h1.map (IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) A ↥(laurentBaseChange L F₀))
      exact h2.tower_top
    haveI : Algebra.IsIntegral ↥B ↥ψ.range := by
      refine ⟨fun z => ?_⟩
      refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥B ↥ψ.range ↥(laurentBaseChange L F₀))
        Subtype.val_injective).mp ?_
      change IsIntegral ↥B (z : ↥(laurentBaseChange L F₀))
      obtain ⟨t, ht⟩ := z.2
      have hzt : (z : ↥(laurentBaseChange L F₀)) = ψ t := ht.symm
      rw [hzt]
      clear hzt ht
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact isIntegral_zero
      | tmul a b =>
        rw [hψ]
        exact (hAint a).mul (isIntegral_algebraMap (x := b))
      | add s t hs ht' => rw [map_add]; exact hs.add ht'
    have hyB : IsIntegral ↥B y := isIntegral_trans y hy1
    obtain ⟨P, hPm, hPy⟩ := hyB

    haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) L ↥(laurentBaseChange L F₀) :=
      IsScalarTower.of_algebraMap_eq fun r => RingHom.congr_fun
        (hext (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(laurentBaseChange L F₀))
          ((algebraMap L ↥(laurentBaseChange L F₀)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) L))) r
    let Θ₁ : ↥B ⊗[↥(GaloisRep.ratLocalizedAt p)] L →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(laurentBaseChange L F₀) :=
      Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) L _)
        (fun _ _ => Commute.all _ _)
    have hΘ₁ : ∀ (b : ↥B) (c : L), Θ₁ (b ⊗ₜ c) = g b * algebraMap L _ c := fun b c =>
      Algebra.TensorProduct.lift_tmul _ _ _ b c

    have hΘ₁inj : Function.Injective Θ₁ := by
      let m : ↥B ⊗[↥(GaloisRep.ratLocalizedAt p)] A →ₐ[↥(GaloisRep.ratLocalizedAt p)]
          ↥B ⊗[↥(GaloisRep.ratLocalizedAt p)] L :=
        Algebra.TensorProduct.map (AlgHom.id _ ↥B) (IsScalarTower.toAlgHom ↥(GaloisRep.ratLocalizedAt p) A L)
      have hm : ∀ (b : ↥B) (a : A), m (b ⊗ₜ a) = b ⊗ₜ algebraMap A L a := fun _ _ => rfl
      have hdec : ∀ t : ↥B ⊗[↥(GaloisRep.ratLocalizedAt p)] L, ∃ a : A, a ≠ 0 ∧
          ∃ u, t = ((1 : ↥B) ⊗ₜ (algebraMap A L a)⁻¹) * m u := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => exact ⟨1, one_ne_zero, 0, by rw [map_zero, mul_zero]⟩
        | tmul b c =>
          obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) c
          refine ⟨d, nonZeroDivisors.ne_zero hd, b ⊗ₜ a, ?_⟩
          rw [hm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, div_eq_mul_inv, mul_comm]
        | add s t hs ht =>
          obtain ⟨a, ha, u, rfl⟩ := hs
          obtain ⟨a', ha', u', rfl⟩ := ht
          have haL : algebraMap A L a ≠ 0 :=
            (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr ha
          have haL' : algebraMap A L a' ≠ 0 :=
            (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr ha'
          refine ⟨a * a', mul_ne_zero ha ha', ((1 : ↥B) ⊗ₜ a') * u + ((1 : ↥B) ⊗ₜ a) * u', ?_⟩
          have e1 : (algebraMap A L (a * a'))⁻¹ * algebraMap A L a' = (algebraMap A L a)⁻¹ := by
            rw [map_mul]; field_simp
          have e2 : (algebraMap A L (a * a'))⁻¹ * algebraMap A L a = (algebraMap A L a')⁻¹ := by
            rw [map_mul]; field_simp
          rw [map_add, map_mul m, map_mul m, hm, hm, mul_add, ← mul_assoc, ← mul_assoc,
            Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, e1, e2]
      have hΘm : ∀ u, Θ₁ (m u) = ψ (Algebra.TensorProduct.comm _ _ _ u) := by
        intro u
        induction u using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul b a =>
          rw [hm, hΘ₁, Algebra.TensorProduct.comm_tmul, hψ,
            ← IsScalarTower.algebraMap_apply A L ↥(laurentBaseChange L F₀), mul_comm]
        | add s t hs ht => simp only [map_add, hs, ht]
      rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨a, ha, u, rfl⟩ := hdec t
      have haL : algebraMap A L a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A L)).mpr ha
      rw [map_mul, hΘ₁, map_one, one_mul, mul_eq_zero] at ht
      rcases ht with h0 | h0
      · exact absurd h0 (by rw [map_inv₀]; exact inv_ne_zero ((map_ne_zero_iff _
          (algebraMap L ↥(laurentBaseChange L F₀)).injective).mpr haL))
      · rw [hΘm] at h0
        have hu : Algebra.TensorProduct.comm _ _ _ u = 0 := hinj (by rw [h0, map_zero])
        rw [(map_eq_zero_iff _ (Algebra.TensorProduct.comm _ _ _).injective).mp hu, map_zero, mul_zero]

    have hDL : ∀ c : L, algebraMap L ↥(laurentBaseChange L F₀) c ∈ Θ₁.range.toSubring := fun c =>
      ⟨(1 : ↥B) ⊗ₜ c, by change Θ₁ ((1 : ↥B) ⊗ₜ c) = _; rw [hΘ₁, map_one, one_mul]⟩
    have hRQ : ∀ z : ↥F₀, z ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({x} : Set ↥F₀) →
        z ∈ Algebra.adjoin ℚ ({x} : Set ↥F₀) := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz => exact Algebra.subset_adjoin hz
      | algebraMap r =>
        have : algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀ r =
            algebraMap ℚ ↥F₀ ((GaloisRep.ratLocalizedAt p).subtype r) :=
          RingHom.congr_fun (hext (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥F₀)
            ((algebraMap ℚ ↥F₀).comp (GaloisRep.ratLocalizedAt p).subtype)) r
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      | add z w _ _ hz hw => exact add_mem hz hw
      | mul z w _ _ hz hw => exact mul_mem hz hw
    have hZR : ∀ z : ↥F₀, z ∈ Algebra.adjoin ℤ ({x} : Set ↥F₀) →
        z ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({x} : Set ↥F₀) := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz => exact Algebra.subset_adjoin hz
      | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
      | add z w _ _ hz hw => exact add_mem hz hw
      | mul z w _ _ hz hw => exact mul_mem hz hw
    have hBBq : ∀ b : ↥F₀, b ∈ B → b ∈ chartAlg ℚ ↥F₀ ({x} : Set ↥F₀) := by
      intro b hb
      rw [mem_chartAlg_iff] at hb ⊢
      let φ : ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({x} : Set ↥F₀)) →+*
          ↥(Algebra.adjoin ℚ ({x} : Set ↥F₀)) :=
        { toFun := fun z => ⟨z, hRQ z z.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      exact hb.map_of_comp_eq φ (RingHom.id _) (by ext; rfl)
    have hDB : ∀ β : ↥F₀, β ∈ chartAlg ℚ ↥F₀ ({x} : Set ↥F₀) →
        ChartBaseChangeAux.coeffEmbK L F₀ β ∈ Θ₁.range.toSubring := by
      intro β hβ
      obtain ⟨n, hn, hint⟩ := ChartBaseChangeAux.exists_int_mul_isIntegral_adjoin_int x β
        ((mem_chartAlg_iff _ _).mp hβ)
      have hmem : (n : ↥F₀) * β ∈ B := by
        rw [mem_chartAlg_iff]
        let φ : ↥(Algebra.adjoin ℤ ({x} : Set ↥F₀)) →+*
            ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({x} : Set ↥F₀)) :=
          { toFun := fun z => ⟨z, hZR z z.2⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
        exact hint.map_of_comp_eq φ (RingHom.id _) (by ext; rfl)
      have hnK : ((n : ℤ) : ↥(laurentBaseChange L F₀)) ≠ 0 := Int.cast_ne_zero.mpr hn
      refine ⟨(⟨(n : ↥F₀) * β, hmem⟩ : ↥B) ⊗ₜ ((n : L)⁻¹), ?_⟩
      change Θ₁ ((⟨(n : ↥F₀) * β, hmem⟩ : ↥B) ⊗ₜ ((n : L)⁻¹)) = _
      rw [hΘ₁, map_inv₀, map_intCast]
      change G₀ ((n : ↥F₀) * β) * _ = _
      rw [map_mul, map_intCast, mul_comm, ← mul_assoc, inv_mul_cancel₀ hnK, one_mul]

    let φq : ↥B →+* ↥(chartAlg ℚ ↥F₀ ({x} : Set ↥F₀)) :=
      { toFun := fun b => ⟨b, hBBq b b.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hφq : ((ChartBaseChangeAux.coeffEmbK L F₀).comp
        (algebraMap ↥(chartAlg ℚ ↥F₀ ({x} : Set ↥F₀)) ↥F₀)).comp φq =
        algebraMap ↥B ↥(laurentBaseChange L F₀) := RingHom.ext fun _ => rfl
    have hclosed : ∀ z : ↥F₀, IsIntegral ↥(chartAlg ℚ ↥F₀ ({x} : Set ↥F₀)) z →
        z ∈ chartAlg ℚ ↥F₀ ({x} : Set ↥F₀) := by
      intro z hz
      letI : Algebra ↥(Algebra.adjoin ℚ ({x} : Set ↥F₀)) ↥(chartAlg ℚ ↥F₀ ({x} : Set ↥F₀)) :=
        (Subalgebra.inclusion (adjoin_le_chartAlg ℚ ↥F₀ ({x} : Set ↥F₀))).toRingHom.toAlgebra
      haveI : IsScalarTower ↥(Algebra.adjoin ℚ ({x} : Set ↥F₀)) ↥(chartAlg ℚ ↥F₀ ({x} : Set ↥F₀)) ↥F₀ :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      haveI : Algebra.IsIntegral ↥(Algebra.adjoin ℚ ({x} : Set ↥F₀)) ↥(chartAlg ℚ ↥F₀ ({x} : Set ↥F₀)) :=
        ⟨fun b => (isIntegral_algHom_iff
          (IsScalarTower.toAlgHom ↥(Algebra.adjoin ℚ ({x} : Set ↥F₀)) ↥(chartAlg ℚ ↥F₀ ({x} : Set ↥F₀)) ↥F₀)
          Subtype.val_injective).mp b.2⟩
      exact isIntegral_trans z hz
    have hyD : y ∈ Θ₁.range.toSubring :=
      ChartBaseChangeAux.mem_of_eval₂_coeffEmbK_eq_zero L F₀ (chartAlg ℚ ↥F₀ ({x} : Set ↥F₀)) hclosed
        Θ₁.range.toSubring hDL hDB y (P.map φq) (hPm.map _)
        (by rw [Polynomial.eval₂_map, hφq]; exact hPy)
    obtain ⟨v, hv⟩ : y ∈ Θ₁.range := hyD
    have hv' : Θ₁ v = y := hv

    have hcomp1 : (Θ₁ : _ →+* ↥(laurentBaseChange L F₀)).comp
        (algebraMap ↥B (↥B ⊗[↥(GaloisRep.ratLocalizedAt p)] L)) = algebraMap ↥B ↥(laurentBaseChange L F₀) := by
      refine RingHom.ext fun b => ?_
      show Θ₁ (algebraMap ↥B (↥B ⊗[↥(GaloisRep.ratLocalizedAt p)] L) b) = g b
      rw [Algebra.TensorProduct.algebraMap_apply]
      change Θ₁ (b ⊗ₜ (1 : L)) = g b
      rw [hΘ₁, map_one, mul_one]
    have hvint : IsIntegral ↥B v := by
      refine ⟨P, hPm, hΘ₁inj ?_⟩
      rw [map_zero, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂, hcomp1]
      change Polynomial.eval₂ _ (Θ₁ v) P = 0
      rw [hv']
      exact hPy

    obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := ↥(GaloisRep.ratLocalizedAt p)) (S := ↥B) (B := L)).2 ⟨v, hvint⟩
    have htv : Algebra.TensorProduct.map (AlgHom.id _ _) (integralClosure _ _).val t = v :=
      congrArg Subtype.val ht
    rw [← hv', ← htv]
    clear ht htv hv hv'
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | tmul b c =>
      obtain ⟨a, ha⟩ := (hA (c : L)).mp c.2
      refine ⟨a ⊗ₜ b, ?_⟩
      change ψ (a ⊗ₜ b) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.val_apply, hΘ₁, hψ, ← ha,
        ← IsScalarTower.algebraMap_apply A L ↥(laurentBaseChange L F₀), mul_comm]
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add]; exact add_mem h₁ h₂

  have hrange : ψ.range = TwoChartIntegralModel.chartAlg A ↥(laurentBaseChange L F₀) ({x'} : Set _) :=
    le_antisymm hle hge
  let e₁ := AlgEquiv.ofInjective ψ hinj
  let e₂ : ↥ψ.range ≃ₐ[A] ↥(TwoChartIntegralModel.chartAlg A ↥(laurentBaseChange L F₀) ({x'} : Set _)) :=
    Subalgebra.equivOfEq _ _ hrange
  refine ⟨e₁.trans e₂, fun b => ?_⟩
  change (((ψ (1 ⊗ₜ b)) : ↥(laurentBaseChange L F₀)) : LaurentSeries L) = _
  rw [hψ, map_one, one_mul]
  rfl

end S_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_tensorProduct_chartAlg_laurentBaseChange_of_smooth (solution)
