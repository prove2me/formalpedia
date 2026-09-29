-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.cuspLawInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/167428f3-7b0f-5373-9bcb-8bbc41f01588

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_isInftySide_cuspInftyBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_sum_ord_isInftySide_eq_order_sub_order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace CuspLawE

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section Generic

theorem coeff_order_ne_zero' {Γ R : Type*} [PartialOrder Γ] [Zero R] [Zero Γ] {x : HahnSeries Γ R}
    (hx : x ≠ 0) : x.coeff x.order ≠ 0 := fun h => hx (HahnSeries.coeff_order_eq_zero.mp h)

theorem order_coeffMap_of_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (y : LaurentSeries R) : (coeffMap f y).order = y.order := by
  by_cases hy : y = 0
  · subst hy; simp
  have h1 : (coeffMap f y).coeff y.order ≠ 0 := by
    rw [coeffMap_coeff]
    exact (map_ne_zero_iff f hf).mpr (coeff_order_ne_zero' hy)
  have hne : coeffMap f y ≠ 0 := fun h0 => h1 (by rw [h0, HahnSeries.coeff_zero])
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  have h2 := coeff_order_ne_zero' hne
  rw [coeffMap_coeff, HahnSeries.coeff_eq_zero_of_lt_order h, map_zero] at h2
  exact h2 rfl

theorem coeffMap_ne_zero_of_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) {y : LaurentSeries R} (hy : y ≠ 0) : coeffMap f y ≠ 0 := by
  intro h0
  have h1 : (coeffMap f y).coeff y.order = 0 := by rw [h0, HahnSeries.coeff_zero]
  rw [coeffMap_coeff, map_eq_zero_iff f hf] at h1
  exact coeff_order_ne_zero' hy h1

theorem order_smul_of_ne_zero {L : Type*} [Field L] {c : L} (hc : c ≠ 0) (x : LaurentSeries L) :
    (c • x).order = x.order := by
  by_cases hx : x = 0
  · subst hx; simp
  have hcx : c • x ≠ 0 := smul_ne_zero hc hx
  have h1 : (c • x).coeff x.order ≠ 0 := by
    rw [HahnSeries.coeff_smul, smul_eq_mul]
    exact mul_ne_zero hc (coeff_order_ne_zero' hx)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra! h
  have h2 := coeff_order_ne_zero' hcx
  rw [HahnSeries.coeff_smul, HahnSeries.coeff_eq_zero_of_lt_order h, smul_zero] at h2
  exact h2 rfl

theorem order_C {L : Type*} [Field L] (c : L) : (HahnSeries.C c : LaurentSeries L).order = 0 := by
  by_cases hc : c = 0
  · subst hc; simp
  · rw [HahnSeries.C_apply, HahnSeries.order_single hc]

theorem order_mul_eq {L : Type*} [Field L] {x y : LaurentSeries L} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).order = x.order + y.order := HahnSeries.order_mul hx hy

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.ord_algebraMap' (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  by_cases hc : c = 0
  · subst hc; simp
  have hmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
    rw [← map_inv₀]; exact v.algebraMap_mem' c⁻¹
  have hu : IsUnit (⟨algebraMap K F c, hmem⟩ : v.toValuationSubring) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(algebraMap K F c)⁻¹, hmem'⟩, ?_⟩
    apply Subtype.ext
    show algebraMap K F c * (algebraMap K F c)⁻¹ = 1
    exact mul_inv_cancel₀ ((map_ne_zero _).mpr hc)
  exact v.ord_coe_unit hu.unit

theorem Place.ord_smul' (v : Place K F) {c : K} (hc : c ≠ 0) {x : F} (hx : x ≠ 0) :
    v.ord (c • x) = v.ord x := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hx, Place.ord_algebraMap', zero_add]

theorem Place.ord_div' (v : Place K F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    v.ord (x / y) = v.ord x - v.ord y := by
  rw [div_eq_mul_inv, v.ord_mul hx (inv_ne_zero hy), v.ord_inv]; ring

theorem inv_mem_of_isUnit {O : ValuationSubring F} {x : F} (hx : x ∈ O)
    (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    intro h0
    have : (u : O) = 0 := by rw [hu]; exact Subtype.ext h0
    exact u.ne_zero this
  have h1 : ((u⁻¹ : Oˣ) : O) * ⟨x, hx⟩ = 1 := by rw [← hu, Units.inv_mul]
  have h2 : (((u⁻¹ : Oˣ) : O) : F) * x = 1 := by
    have := congrArg (Subtype.val) h1
    simpa using this
  have h3 : (((u⁻¹ : Oˣ) : O) : F) = x⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [← h3]; exact ((u⁻¹ : Oˣ) : O).2

theorem Finsupp.mapDomain_apply_of_forall_eq {α β M : Type*} [AddCommMonoid M]
    (f : α → β) (x : α →₀ M) (b : β) (h : ∀ a ∈ x.support, f a = b) :
    Finsupp.mapDomain f x b = ∑ a ∈ x.support, x a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [h a ha, Finsupp.single_eq_same]

end Generic

end CuspLawE

namespace CuspLawE

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section Presentation

variable {q : ℕ} [Fact q.Prime]

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldBar (1 * q))

omit [Fact q.Prime] in

theorem adjoin_coeffEmb_image_adjoin (L : Type*) [Field L] [Algebra ℚ L] (S : Set (LaurentSeries ℚ)) :
    IntermediateField.adjoin L (coeffEmb L '' (IntermediateField.adjoin ℚ S : Set (LaurentSeries ℚ)))
      = IntermediateField.adjoin L (coeffEmb L '' S) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩
    | algebraMap c =>
      rw [ModularCurve.algebraMap_apply_eq_single, coeffEmb, coeffMap_single,
        ← algebraMap_laurentSeries_eq_single]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  · exact IntermediateField.adjoin.mono L _ _ (Set.image_mono (IntermediateField.subset_adjoin ℚ S))

theorem modularFunctionFieldBar_le_adjoin_pair :
    modularFunctionFieldBar (1 * q) ≤ IntermediateField.adjoin ℚbar
      {coeffEmb ℚbar jq, coeffEmb ℚbar (qExpand ℚ (1 * q) jq)} := by
  show laurentBaseChange ℚbar (modularFunctionFieldFull (1 * q)) ≤ _
  rw [laurentBaseChange, modularFunctionFieldFull, adjoin_coeffEmb_image_adjoin, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, ⟨d, hne, hdN, rfl⟩, rfl⟩
  haveI := hne
  have hq : q.Prime := Fact.out
  rw [Nat.one_mul] at hdN
  rcases (Nat.dvd_prime hq).mp hdN with rfl | rfl
  · rw [qExpand_one_apply]
    exact IntermediateField.subset_adjoin ℚbar _ (Set.mem_insert _ _)
  · rw [show qExpand ℚ d jq = qExpand ℚ (1 * d) jq from (qExpand_congr (Nat.one_mul d) jq).symm]
    exact IntermediateField.subset_adjoin ℚbar _ (Set.mem_insert_of_mem _ rfl)

theorem coeffEmb_jq_ne_coeffEmb_qExpand :
    coeffEmb ℚbar jq ≠ coeffEmb ℚbar (qExpand ℚ (1 * q) jq) := by
  intro h
  have h1 := congrArg (fun f : LaurentSeries ℚbar => f.coeff (-1)) h
  simp only [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h1
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  rw [qExpand_coeff_of_not_dvd (R := ℚ) (N := 1 * q) (f := jq) (by
      rw [Nat.one_mul]; intro ⟨c, hc⟩
      have : (q : ℤ) ∣ 1 := ⟨-c, by linarith⟩
      have := Int.eq_one_of_dvd_one (by positivity) this
      omega), map_zero] at h1
  exact one_ne_zero h1

theorem jFun_ne_zero : (jFun (q := q)) ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : FF => (f : LaurentSeries ℚbar).coeff (-1)) h
  simp only [jFun, coeffEmb_coeff, coeff_jq_neg_one, map_one, ZeroMemClass.coe_zero,
    HahnSeries.coeff_zero] at h1
  exact one_ne_zero h1

theorem exists_pow_mul_aeval_mem {σ : Type*} (g : σ → FF)
    (hg : ∀ i, g i = jFun (q := q) ∨ g i = jqFun (q := q)) (p : MvPolynomial σ ℚbar) :
    ∃ M : ℕ, (jFun (q := q))⁻¹ ^ M * MvPolynomial.aeval g p ∈
      Algebra.adjoin ℚbar ({(jFun (q := q))⁻¹, tInfty (q := q)} : Set FF) := by
  have hw : (jFun (q := q))⁻¹ ∈ Algebra.adjoin ℚbar ({(jFun (q := q))⁻¹, tInfty (q := q)} : Set FF) :=
    Algebra.subset_adjoin (Set.mem_insert _ _)
  have ht : tInfty (q := q) ∈ Algebra.adjoin ℚbar ({(jFun (q := q))⁻¹, tInfty (q := q)} : Set FF) :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨0, ?_⟩
      rw [pow_zero, one_mul ((MvPolynomial.aeval g) (MvPolynomial.C a)), MvPolynomial.algHom_C]
      exact Subalgebra.algebraMap_mem _ a
  | add p p' hp hp' =>
      obtain ⟨M, hM⟩ := hp
      obtain ⟨M', hM'⟩ := hp'
      refine ⟨M + M', ?_⟩
      have e : (jFun (q := q))⁻¹ ^ (M + M') * MvPolynomial.aeval g (p + p')
          = (jFun (q := q))⁻¹ ^ M' * ((jFun (q := q))⁻¹ ^ M * MvPolynomial.aeval g p)
            + (jFun (q := q))⁻¹ ^ M * ((jFun (q := q))⁻¹ ^ M' * MvPolynomial.aeval g p') := by
        rw [map_add]; ring
      rw [e]
      exact add_mem (mul_mem (pow_mem hw _) hM) (mul_mem (pow_mem hw _) hM')
  | mul_X p i hp =>
      obtain ⟨M, hM⟩ := hp
      rcases hg i with hi | hi
      · refine ⟨M + 1, ?_⟩
        have e : (jFun (q := q))⁻¹ ^ (M + 1) * MvPolynomial.aeval g (p * MvPolynomial.X i)
            = (jFun (q := q))⁻¹ ^ M * MvPolynomial.aeval g p := by
          rw [map_mul, MvPolynomial.aeval_X, hi, pow_succ]
          field_simp [jFun_ne_zero (q := q)]
        rw [e]; exact hM
      · refine ⟨M + 1 * q, ?_⟩
        have e : (jFun (q := q))⁻¹ ^ (M + 1 * q) * MvPolynomial.aeval g (p * MvPolynomial.X i)
            = ((jFun (q := q))⁻¹ ^ M * MvPolynomial.aeval g p) * tInfty (q := q) := by
          rw [map_mul, MvPolynomial.aeval_X, hi, pow_add, tInfty, div_eq_mul_inv, ← inv_pow]
          ring
        rw [e]; exact mul_mem hM ht

theorem exists_eq_div_adjoin (f : FF) (hf : f ≠ 0) :
    ∃ a b : FF, a ∈ Algebra.adjoin ℚbar ({(jFun (q := q))⁻¹, tInfty (q := q)} : Set FF) ∧
      b ∈ Algebra.adjoin ℚbar ({(jFun (q := q))⁻¹, tInfty (q := q)} : Set FF) ∧
      a ≠ 0 ∧ b ≠ 0 ∧ f = a / b := by
  classical
  set J := coeffEmb ℚbar jq with hJ
  set Jq := coeffEmb ℚbar (qExpand ℚ (1 * q) jq) with hJq
  have hfm : (f : LaurentSeries ℚbar) ∈ IntermediateField.adjoin ℚbar ({J, Jq} : Set (LaurentSeries ℚbar)) :=
    modularFunctionFieldBar_le_adjoin_pair f.2
  rw [IntermediateField.mem_adjoin_iff] at hfm
  obtain ⟨r, s, hrs⟩ := hfm

  let g : (({J, Jq} : Set (LaurentSeries ℚbar))) → FF :=
    fun x => if (x : LaurentSeries ℚbar) = J then jFun (q := q) else jqFun (q := q)
  have hg : ∀ x, g x = jFun (q := q) ∨ g x = jqFun (q := q) := by
    intro x; by_cases h : (x : LaurentSeries ℚbar) = J
    · left; simp only [g, if_pos h]
    · right; simp only [g, if_neg h]
  have hgval : ∀ x : ({J, Jq} : Set (LaurentSeries ℚbar)),
      (x : LaurentSeries ℚbar) = ((g x : FF) : LaurentSeries ℚbar) := by
    rintro ⟨x, hxm⟩
    rcases hxm with rfl | hxm
    · simp only [g, if_pos rfl]; rfl
    · rw [Set.mem_singleton_iff] at hxm
      subst hxm
      have hne := coeffEmb_jq_ne_coeffEmb_qExpand (q := q)
      simp only [g]
      rw [if_neg (Ne.symm hne)]
      rfl
  have hval : ∀ t : MvPolynomial ({J, Jq} : Set (LaurentSeries ℚbar)) ℚbar,
      MvPolynomial.aeval (fun x : ({J, Jq} : Set (LaurentSeries ℚbar)) => (x : LaurentSeries ℚbar)) t =
        ((MvPolynomial.aeval g t : FF) : LaurentSeries ℚbar) := by
    intro t
    have : (fun x : ({J, Jq} : Set (LaurentSeries ℚbar)) => (x : LaurentSeries ℚbar)) =
        fun x => ((modularFunctionFieldBar (1 * q)).val) (g x) := by
      funext x; exact hgval x
    rw [this, ← MvPolynomial.comp_aeval]
    rfl
  have hf' : f = MvPolynomial.aeval g r / MvPolynomial.aeval g s := by
    apply Subtype.val_injective
    rw [hrs, hval r, hval s]
    push_cast
    rfl
  obtain ⟨M, hM⟩ := exists_pow_mul_aeval_mem g hg r
  obtain ⟨M', hM'⟩ := exists_pow_mul_aeval_mem g hg s
  have hw : (jFun (q := q))⁻¹ ∈ Algebra.adjoin ℚbar ({(jFun (q := q))⁻¹, tInfty (q := q)} : Set FF) :=
    Algebra.subset_adjoin (Set.mem_insert _ _)
  have hwne : (jFun (q := q))⁻¹ ≠ 0 := inv_ne_zero jFun_ne_zero
  have hr0 : MvPolynomial.aeval g r ≠ 0 := by
    intro h0; rw [h0, zero_div] at hf'; exact hf hf'
  have hs0 : MvPolynomial.aeval g s ≠ 0 := by
    intro h0; rw [h0, div_zero] at hf'; exact hf hf'
  refine ⟨(jFun (q := q))⁻¹ ^ (M + M') * MvPolynomial.aeval g r,
    (jFun (q := q))⁻¹ ^ (M + M') * MvPolynomial.aeval g s, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_add, mul_comm (_ ^ M), mul_assoc]
    exact mul_mem (pow_mem hw _) hM
  · rw [pow_add, mul_assoc]
    exact mul_mem (pow_mem hw _) hM'
  · exact mul_ne_zero (pow_ne_zero _ hwne) hr0
  · exact mul_ne_zero (pow_ne_zero _ hwne) hs0
  · rw [hf', mul_div_mul_left _ _ (pow_ne_zero _ hwne)]

end Presentation

end CuspLawE

namespace CuspLawE

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section Main

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)

local notation "ℚbar" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FF" => ↥(modularFunctionFieldBar (1 * q))

theorem smul_coe_mem (c : ℚbar) (x : FF) :
    c • (x : LaurentSeries ℚbar) ∈ modularFunctionFieldBar (1 * q) := by
  rw [← HahnSeries.C_mul_eq_smul, HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]
  exact mul_mem (IntermediateField.algebraMap_mem _ c) x.2

open Classical in

theorem cuspLaw_core
    (f : FF) (h₁ : f ∈ R.R₁.integers) (hf : R.R₁.residue ⟨f, h₁⟩ ≠ 0)
    (D : Divisor ℚbar FF) (hD : ∀ W, D W = W.ord f) :
    Finsupp.mapDomain P.redFst (D.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))) =
      (P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨f, h₁⟩) := by
  classical
  have hf0 : f ≠ 0 := by
    intro h0; apply hf
    have : (⟨f, h₁⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  obtain ⟨a, b, ha, hb, ha0, hb0, hfab⟩ := exists_eq_div_adjoin f hf0
  obtain ⟨c₁, y₁, S₁, hc₁, hy₁, hyb₁, hS₁, hsum₁⟩ :=
    ModularCurve.PlaceSpecialization.exists_sum_ord_isInftySide_eq_order_sub_order P a ha0 ha
  obtain ⟨c₂, y₂, S₂, hc₂, hy₂, hyb₂, hS₂, hsum₂⟩ :=
    ModularCurve.PlaceSpecialization.exists_sum_ord_isInftySide_eq_order_sub_order P b hb0 hb

  have hG₁mem : coeffMap A.subtype y₁ ∈ modularFunctionFieldBar (1 * q) := by
    rw [hy₁]; exact smul_coe_mem c₁ a
  have hG₂mem : coeffMap A.subtype y₂ ∈ modularFunctionFieldBar (1 * q) := by
    rw [hy₂]; exact smul_coe_mem c₂ b
  obtain ⟨hG₁int, hG₁res⟩ := R.residue₁_coeffMap y₁ hG₁mem
  obtain ⟨hG₂int, hG₂res⟩ := R.residue₁_coeffMap y₂ hG₂mem
  set G₁ : FF := ⟨coeffMap A.subtype y₁, hG₁mem⟩ with hG₁def
  set G₂ : FF := ⟨coeffMap A.subtype y₂, hG₂mem⟩ with hG₂def
  have hCalg : ∀ c : ℚbar, ((algebraMap ℚbar FF c : FF) : LaurentSeries ℚbar) = HahnSeries.C c := by
    intro c
    show algebraMap ℚbar (LaurentSeries ℚbar) c = HahnSeries.C c
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  have hG₁ : G₁ = algebraMap ℚbar FF c₁ * a := by
    apply Subtype.ext
    show coeffMap A.subtype y₁ = ((algebraMap ℚbar FF c₁ : FF) : LaurentSeries ℚbar) * (a : LaurentSeries ℚbar)
    rw [hy₁, hCalg, HahnSeries.C_mul_eq_smul]
  have hG₂ : G₂ = algebraMap ℚbar FF c₂ * b := by
    apply Subtype.ext
    show coeffMap A.subtype y₂ = ((algebraMap ℚbar FF c₂ : FF) : LaurentSeries ℚbar) * (b : LaurentSeries ℚbar)
    rw [hy₂, hCalg, HahnSeries.C_mul_eq_smul]
  have halg₁ : algebraMap ℚbar FF c₁ ≠ 0 := (map_ne_zero _).mpr hc₁
  have halg₂ : algebraMap ℚbar FF c₂ ≠ 0 := (map_ne_zero _).mpr hc₂
  have hG₁0 : G₁ ≠ 0 := by rw [hG₁]; exact mul_ne_zero halg₁ ha0
  have hG₂0 : G₂ ≠ 0 := by rw [hG₂]; exact mul_ne_zero halg₂ hb0

  have hres_ne₁ : R.R₁.residue ⟨G₁, hG₁int⟩ ≠ 0 := by
    intro h0; apply hyb₁; rw [← hG₁res, h0]; rfl
  have hres_ne₂ : R.R₁.residue ⟨G₂, hG₂int⟩ ≠ 0 := by
    intro h0; apply hyb₂; rw [← hG₂res, h0]; rfl
  have hG₁unit : IsUnit (⟨G₁, hG₁int⟩ : R.R₁.integers) := R.R₁.isUnit_of_residue_ne_zero hres_ne₁

  have hu_eq : algebraMap ℚbar FF (c₂ / c₁) = f * G₂ * G₁⁻¹ := by
    rw [hfab, hG₁, hG₂, map_div₀]
    field_simp
  have hu_mem : algebraMap ℚbar FF (c₂ / c₁) ∈ R.R₁.integers := by
    rw [hu_eq]
    exact mul_mem (mul_mem h₁ hG₂int) (inv_mem_of_isUnit hG₁int hG₁unit)
  have hu_A : c₂ / c₁ ∈ A := (R.R₁.algebraMap_mem_iff _).mp hu_mem

  have hprod : (⟨f, h₁⟩ : R.R₁.integers) * ⟨G₂, hG₂int⟩
      = ⟨algebraMap ℚbar FF (c₂ / c₁), hu_mem⟩ * ⟨G₁, hG₁int⟩ := by
    apply Subtype.ext
    show f * G₂ = algebraMap ℚbar FF (c₂ / c₁) * G₁
    rw [hu_eq, mul_assoc, inv_mul_cancel₀ hG₁0, mul_one]
  have hres_alg : R.R₁.residue ⟨algebraMap ℚbar FF (c₂ / c₁), hu_mem⟩
      = algebraMap (ResidueField A) _ (IsLocalRing.residue A ⟨c₂ / c₁, hu_A⟩) :=
    R.R₁.residue_algebraMap ⟨c₂ / c₁, hu_A⟩
  have hres := congrArg R.R₁.residue hprod
  rw [map_mul, map_mul, hres_alg] at hres

  have hresL := congrArg (fun z : modularFunctionFieldFullC (ResidueField A) 1 =>
    (z : LaurentSeries (ResidueField A))) hres
  simp only [IntermediateField.coe_mul] at hresL
  rw [hG₁res, hG₂res] at hresL
  have hCk : ∀ r : ResidueField A,
      ((algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) r :
        modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = HahnSeries.C r := by
    intro r
    show algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) r = HahnSeries.C r
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  rw [hCk] at hresL

  have hresf0 : ((R.R₁.residue ⟨f, h₁⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)) ≠ 0 := by
    intro h0; apply hf; exact_mod_cast h0
  have hCne : (HahnSeries.C (IsLocalRing.residue A ⟨c₂ / c₁, hu_A⟩) :
      LaurentSeries (ResidueField A)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hresL
    exact mul_ne_zero hresf0 hyb₂ hresL
  have hord_res : ((R.R₁.residue ⟨f, h₁⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
      LaurentSeries (ResidueField A)).order
        = (coeffMap (IsLocalRing.residue A) y₁).order - (coeffMap (IsLocalRing.residue A) y₂).order := by
    have h := congrArg HahnSeries.order hresL
    rw [order_mul_eq hresf0 hyb₂, order_mul_eq hCne hyb₁, order_C, zero_add] at h
    omega

  have hRHS : (P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨f, h₁⟩)
      = (coeffMap (IsLocalRing.residue A) y₁).order - (coeffMap (IsLocalRing.residue A) y₂).order := by
    rw [ModularCurve.PlaceSpecialization.redFst_cuspInftyBar P,
      ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_eq_order,
      LevelOneProlongationPair.residue₁_apply, R.ι_coe,
      order_coeffMap_of_injective R.redBar R.redBar.injective, hord_res]

  have hred : ∀ W, P.IsInftySide W → P.redFst W = P.redFst (cuspInftyBar (1 * q)) := by
    intro W hW
    rw [ModularCurve.PlaceSpecialization.redFst_eq_placeInfty_of_forall_ord_le_zero P W hW.1,
      ModularCurve.PlaceSpecialization.redFst_cuspInftyBar P]
  have hE : ∀ W, (D.filter P.IsInftySide) W = if P.IsInftySide W then W.ord f else 0 := by
    intro W; rw [Finsupp.filter_apply, hD]
  have hsupp : ∀ W, W ∈ (D.filter P.IsInftySide).support → P.IsInftySide W ∧ W.ord f ≠ 0 := by
    intro W hW
    rw [Finsupp.mem_support_iff, hE] at hW
    by_cases h : P.IsInftySide W
    · rw [if_pos h] at hW; exact ⟨h, hW⟩
    · rw [if_neg h] at hW; exact absurd rfl hW
  rw [Finsupp.mapDomain_apply_of_forall_eq P.redFst (D.filter P.IsInftySide) _
    (fun W hW => hred W (hsupp W hW).1)]

  set U : Finset (Place ℚbar FF) := insert (cuspInftyBar (1 * q)) (S₁ ∪ S₂) with hU
  have hUside : ∀ W ∈ U, P.IsInftySide W := by
    intro W hW
    rw [Finset.mem_insert, Finset.mem_union] at hW
    rcases hW with rfl | hW | hW
    · exact ModularCurve.isInftySide_cuspInftyBar P
    · exact ((hS₁ W).mp hW).1
    · exact ((hS₂ W).mp hW).1
  have hordf : ∀ W : Place ℚbar FF, W.ord f = W.ord a - W.ord b := by
    intro W; rw [hfab, Place.ord_div' W ha0 hb0]
  have hsub : (D.filter P.IsInftySide).support ⊆ U := by
    intro W hW
    obtain ⟨hside, hne⟩ := hsupp W hW
    rw [Finset.mem_insert, Finset.mem_union]
    by_cases hWc : W = cuspInftyBar (1 * q)
    · exact Or.inl hWc
    · right
      rw [hordf] at hne
      by_cases ha' : W.ord a = 0
      · have hb' : W.ord b ≠ 0 := by intro hb'; exact hne (by rw [ha', hb', sub_zero])
        exact Or.inr ((hS₂ W).mpr ⟨hside, hWc, hb'⟩)
      · exact Or.inl ((hS₁ W).mpr ⟨hside, hWc, ha'⟩)
  have hLHS1 : ∑ W ∈ (D.filter P.IsInftySide).support, (D.filter P.IsInftySide) W
      = ∑ W ∈ U, W.ord f := by
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun W hW => ?_
      rw [hE, if_pos (hsupp W hW).1]
    · intro W hWU hWn
      rw [Finsupp.mem_support_iff, not_not, hE, if_pos (hUside W hWU)] at hWn
      exact hWn

  have hnotin : cuspInftyBar (1 * q) ∉ S₁ ∪ S₂ := by
    rw [Finset.mem_union, not_or]
    exact ⟨fun h => ((hS₁ _).mp h).2.1 rfl, fun h => ((hS₂ _).mp h).2.1 rfl⟩
  have hord_a_cusp : (cuspInftyBar (1 * q)).ord a = y₁.order := by
    rw [ModularCurve.ord_cuspInftyBar, ← order_smul_of_ne_zero hc₁, ← hy₁,
      order_coeffMap_of_injective A.subtype Subtype.val_injective]
  have hord_b_cusp : (cuspInftyBar (1 * q)).ord b = y₂.order := by
    rw [ModularCurve.ord_cuspInftyBar, ← order_smul_of_ne_zero hc₂, ← hy₂,
      order_coeffMap_of_injective A.subtype Subtype.val_injective]
  have hsum_a : ∑ W ∈ U, W.ord a = (coeffMap (IsLocalRing.residue A) y₁).order := by
    rw [hU, Finset.sum_insert hnotin, hord_a_cusp,
      ← Finset.sum_subset Finset.subset_union_left, hsum₁]
    · ring
    · intro W hW hW1
      rw [Finset.mem_union] at hW
      rcases hW with hW | hW
      · exact absurd hW hW1
      · obtain ⟨hside, hne, -⟩ := (hS₂ W).mp hW
        by_contra h
        exact hW1 ((hS₁ W).mpr ⟨hside, hne, h⟩)
  have hsum_b : ∑ W ∈ U, W.ord b = (coeffMap (IsLocalRing.residue A) y₂).order := by
    rw [hU, Finset.sum_insert hnotin, hord_b_cusp,
      ← Finset.sum_subset Finset.subset_union_right, hsum₂]
    · ring
    · intro W hW hW2
      rw [Finset.mem_union] at hW
      rcases hW with hW | hW
      · obtain ⟨hside, hne, -⟩ := (hS₁ W).mp hW
        by_contra h
        exact hW2 ((hS₂ W).mpr ⟨hside, hne, h⟩)
      · exact absurd hW hW2
  rw [hLHS1, hRHS, Finset.sum_congr rfl (fun W _ => hordf W), Finset.sum_sub_distrib, hsum_a, hsum_b]

theorem cuspLawInfty : R.CuspLawInfty := by
  intro f h₁ h₂ hr₁ hr₂ D hD
  exact cuspLaw_core R f h₁ hr₁ D hD

end Main

end CuspLawE

open AlgebraicCurve IsLocalRing ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair) :
    R.CuspLawInfty := by
  exact CuspLawE.cuspLawInfty R

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty (solution)
