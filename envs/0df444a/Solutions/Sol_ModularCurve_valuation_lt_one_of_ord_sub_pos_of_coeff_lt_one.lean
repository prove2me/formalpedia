-- Prove2me | solution 1 for ModularCurve.valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ae8ece42-0ff8-5a99-a328-4089be558283

import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_CharPReduction
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_CharPReduction_mem_modularLocalized_of_eval2_monic
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPModel_exists_eq_const_mul_of_modularRedLocHom_eq_zero
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_exists_ord_sub_pos_of_integral_affineBaseFin
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false

noncomputable section

namespace ValLtOneS8da

p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_jq ModularCurve.CharPModel ModularCurve.CharPReduction AlgebraicCurve Polynomial"

abbrev FF (N : ℕ) [NeZero N] :
    IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)

variable (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c)
      = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_apply_eq_single, algebraMap_laurentSeries_eq_single]
  exact coeffMap_single _ _ _

omit [NeZero N] in
theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L :=
  map_jqModC (algebraMap ℚ L)

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext j
  by_cases hj : (n : ℤ) ∣ j
  · obtain ⟨m, rfl⟩ := hj
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hj, qExpand_coeff_of_not_dvd n _ hj,
      map_zero]

theorem coeffEmb_qExpand_jq (L : Type*) [Field L] [Algebra ℚ L] :
    coeffEmb L (qExpand ℚ N jq) = jqNModC L N := by
  show coeffMap (algebraMap ℚ L) (qExpand ℚ N jq) = qExpand L N (jqModC L)
  rw [coeffMap_qExpand, ← coeffEmb_jq]
  rfl

theorem modularFunctionFieldFull_le : modularFunctionFieldFull N ≤ modularFunctionField N := by
  rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hd, hdvd, rfl⟩
  exact functionFieldGeneration N d hdvd hd

theorem ff_le_modularFunctionFieldC :
    (FF N : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
      ≤ modularFunctionFieldC (AlgebraicClosure ℚ) N := by
  rw [FF, laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hxN : x ∈ modularFunctionField N := modularFunctionFieldFull_le N hx
  have key : (modularFunctionField N).toSubfield ≤
      (modularFunctionFieldC (AlgebraicClosure ℚ) N).toSubfield.comap
        (coeffEmb (AlgebraicClosure ℚ)) := by
    show Subfield.closure _ ≤ _
    rw [Subfield.closure_le]
    rintro y (⟨c, rfl⟩ | rfl | rfl) <;>
      rw [SetLike.mem_coe, Subfield.mem_comap, IntermediateField.mem_toSubfield]
    · rw [coeffEmb_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    · rw [coeffEmb_jq]
      exact jqModC_mem _ N
    · rw [coeffEmb_qExpand_jq]
      exact jqNModC_mem _ N
  exact key hxN

theorem coe_mem_modularFunctionFieldC (x : FF N) :
    (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldC (AlgebraicClosure ℚ) N :=
  ff_le_modularFunctionFieldC N x.2

variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem coe_jBar :
    ((jBar N : FF N) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) :=
  coeffEmb_jq _

omit [NeZero N] in
theorem coe_constantsHom (a : A) :
    ((constantsHom N A a : FF N) : LaurentSeries (AlgebraicClosure ℚ))
      = constSeries A.toSubring ⟨a, a.2⟩ :=
  rfl

theorem const_mem_affineBaseFin (a : A) : constantsHom N A a ∈ affineBaseFin N A :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem jBar_mem_affineBaseFin : jBar N ∈ affineBaseFin N A :=
  Subring.subset_closure (Or.inr rfl)

theorem coe_mem_modularRing_of_mem_affineBaseFin {x : FF N} (hx : x ∈ affineBaseFin N A) :
    (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularRing N A.toSubring := by
  have : affineBaseFin N A ≤ (modularRing N A.toSubring).comap
      (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))) := by
    rw [affineBaseFin, Subring.closure_le]
    rintro y (⟨a, rfl⟩ | rfl) <;> rw [SetLike.mem_coe, Subring.mem_comap]
    · show ((constantsHom N A a : FF N) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ modularRing N A.toSubring
      rw [coe_constantsHom]
      exact constSeries_mem_modularRing N A.toSubring _
    · show ((jBar N : FF N) : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularRing N A.toSubring
      rw [coe_jBar]
      exact jqModC_mem_modularRing N A.toSubring
  exact this hx

def basePoly : Polynomial A →+* affineBaseFin N A :=
  eval₂RingHom ((constantsHom N A).codRestrict (affineBaseFin N A) (const_mem_affineBaseFin N A))
    ⟨jBar N, jBar_mem_affineBaseFin N A⟩

theorem algebraMap_comp_subtype_comp_basePoly :
    ((algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).comp
        (affineBaseFin N A).subtype).comp (basePoly N A)
      = eval₂RingHom
          ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
          (jqModC (AlgebraicClosure ℚ)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, basePoly, coe_eval₂RingHom, eval₂_C]
    rfl
  · simp only [RingHom.comp_apply, basePoly, coe_eval₂RingHom, eval₂_X]
    exact coe_jBar N

theorem basePoly_surjective : Function.Surjective (basePoly N A) := by
  intro x
  have hle : affineBaseFin N A ≤ ((basePoly N A).range).map (affineBaseFin N A).subtype := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨a, rfl⟩ | rfl)
    · refine ⟨basePoly N A (C a), ⟨C a, rfl⟩, ?_⟩
      show ((Polynomial.eval₂ _ _ (C a) : affineBaseFin N A) : FF N) = constantsHom N A a
      rw [eval₂_C]; rfl
    · refine ⟨basePoly N A X, ⟨X, rfl⟩, ?_⟩
      show ((Polynomial.eval₂ _ _ X : affineBaseFin N A) : FF N) = (jBar N : FF N)
      rw [eval₂_X]
  obtain ⟨y, ⟨p, rfl⟩, hy⟩ := hle x.2
  exact ⟨p, Subtype.ext hy⟩

theorem exists_bivariate {b : FF N}
    (hb : ∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin N A).subtype b p = 0) :
    ∃ P : Polynomial (Polynomial A), P.Monic ∧
      Polynomial.eval₂ (eval₂RingHom
        ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
        (jqModC (AlgebraicClosure ℚ))) (b : LaurentSeries (AlgebraicClosure ℚ)) P = 0 := by
  obtain ⟨p, hpm, hpe⟩ := hb
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ (basePoly_surjective N A) p)) hpm
  refine ⟨P, hPm, ?_⟩
  have h := congrArg (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))) hpe
  rw [map_zero, hom_eval₂, ← hPmap, eval₂_map, algebraMap_comp_subtype_comp_basePoly] at h
  exact h

theorem integral_of_bivariate {b : FF N}
    (hP : ∃ P : Polynomial (Polynomial A), P.Monic ∧
      Polynomial.eval₂ (eval₂RingHom
        ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
        (jqModC (AlgebraicClosure ℚ))) (b : LaurentSeries (AlgebraicClosure ℚ)) P = 0) :
    ∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin N A).subtype b p = 0 := by
  obtain ⟨P, hPm, hPe⟩ := hP
  refine ⟨P.map (basePoly N A), hPm.map _, ?_⟩
  apply (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).injective
  rw [map_zero, hom_eval₂, eval₂_map, algebraMap_comp_subtype_comp_basePoly]
  exact hPe

variable {k : Type*} [Field k] (red : A →+* k)

abbrev redS : A.toSubring →+* k := red

abbrev O : Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
  modularLocalized N A.toSubring (redS A red)

def finToO : affineBaseFin N A →+* O N A red :=
  ((algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).comp
      (affineBaseFin N A).subtype).codRestrict (O N A red) fun x =>
    subring_le_localizedAtKer _ _ _ _ (coe_mem_modularRing_of_mem_affineBaseFin N A x.2)

theorem coe_mem_O_of_integral (data : ModularPolynomialData N)
    (hdeg : (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank
      (modularFunctionFieldC k N) = dedekindPsi N)
    {b : FF N}
    (hb : ∃ p : Polynomial (affineBaseFin N A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin N A).subtype b p = 0) :
    (b : LaurentSeries (AlgebraicClosure ℚ)) ∈ O N A red := by
  obtain ⟨p, hp, hev⟩ := hb
  refine mem_modularLocalized_of_eval2_monic A (redS A red) N data hdeg
    (coe_mem_modularFunctionFieldC N b) (hp.map (finToO N A red)) ?_
  rw [eval₂_map]
  have : (O N A red).subtype.comp (finToO N A red)
      = (algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ))).comp
          (affineBaseFin N A).subtype :=
    RingHom.ext fun _ => rfl
  rw [this, show ((b : FF N) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (FF N) (LaurentSeries (AlgebraicClosure ℚ)) b from rfl,
    ← hom_eval₂, hev, map_zero]

theorem eq_zero_of_algebraMap_mem_nonunits (w : Place (AlgebraicClosure ℚ) (FF N))
    {c : AlgebraicClosure ℚ}
    (hc : algebraMap (AlgebraicClosure ℚ) (FF N) c ∈ w.toValuationSubring.nonunits) :
    c = 0 := by
  by_contra h
  rw [ValuationSubring.mem_nonunits_iff] at hc
  set x : FF N := algebraMap (AlgebraicClosure ℚ) (FF N) c with hx
  have hx0 : x ≠ 0 := (_root_.map_ne_zero _).2 h
  have h1 : w.toValuationSubring.valuation x⁻¹ ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff, hx, ← map_inv₀]
    exact w.algebraMap_mem' _
  have hprod : w.toValuationSubring.valuation x * w.toValuationSubring.valuation x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hx0, map_one]
  have hle : w.toValuationSubring.valuation x * w.toValuationSubring.valuation x⁻¹
      ≤ w.toValuationSubring.valuation x * 1 :=
    mul_le_mul' le_rfl h1
  rw [hprod, mul_one] at hle
  exact absurd hc (not_lt.2 hle)

theorem main
    (M ℓ : ℕ) [NeZero M] [Fact ℓ.Prime]
    (hℓA : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1) (hlM : ¬ ℓ ∣ M)
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)))
    (a₀ : A)
    (hj : 0 < w.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full M (jq_mem M))⟩
      - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
        (a₀ : AlgebraicClosure ℚ)))
    (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
    (hb : ∃ p : Polynomial (affineBaseFin M A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin M A).subtype b p = 0)
    (hcoeff : ∀ n : ℤ,
      A.valuation ((b : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1)
    (a : A)
    (hval : (b - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
      (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits) :
    A.valuation (a : AlgebraicClosure ℚ) < 1 := by
  classical

  have hcast : (((ℓ : ℕ) : A) : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) :=
    map_natCast A.subtype ℓ
  have hℓmax : ((ℓ : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff, hcast]
    exact hℓA
  haveI : CharP (IsLocalRing.ResidueField A) ℓ :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : ℓ.Prime)).2 (by
      rw [← map_natCast (IsLocalRing.residue A) ℓ]
      exact (IsLocalRing.residue_eq_zero_iff _).2 hℓmax)

  obtain ⟨data⟩ := nonempty_modularPolynomialData M
  have hdeg := relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
    (IsLocalRing.ResidueField A) M ℓ hlM

  have hbO : (b : LaurentSeries (AlgebraicClosure ℚ)) ∈ O M A (IsLocalRing.residue A) :=
    coe_mem_O_of_integral M A (IsLocalRing.residue A) data hdeg hb
  have hbint : (b : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring := fun n =>
    (A.valuation_le_one_iff _).1 (le_of_lt (hcoeff n))
  have hker : modularRedLocHom M A.toSubring (redS A (IsLocalRing.residue A))
      ⟨(b : LaurentSeries (AlgebraicClosure ℚ)), hbO⟩ = 0 := by
    rw [modularRedLocHom_eq_coeffRed A.toSubring (redS A (IsLocalRing.residue A)) M ⟨_, hbO⟩
      hbint]
    ext n
    rw [coeffRed_coeff, HahnSeries.coeff_zero]
    show IsLocalRing.residue A ⟨(b : LaurentSeries (AlgebraicClosure ℚ)).coeff n, hbint n⟩ = 0
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact hcoeff n

  obtain ⟨m, hm0, f', hf'int, hbf⟩ :=
    exists_eq_const_mul_of_modularRedLocHom_eq_zero M A (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A) data hdeg ⟨(b : LaurentSeries (AlgebraicClosure ℚ)), hbO⟩
      (exists_bivariate M A hb) hker
  have hm_max : m ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.residue_eq_zero_iff _).1 hm0
  have hbf' : (b : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
          (m : AlgebraicClosure ℚ) * (f' : LaurentSeries (AlgebraicClosure ℚ)) := hbf
  by_cases hm : (m : AlgebraicClosure ℚ) = 0
  ·
    have hb0 : b = 0 := by
      apply (algebraMap (FF M) (LaurentSeries (AlgebraicClosure ℚ))).injective
      show (b : LaurentSeries (AlgebraicClosure ℚ)) = ((0 : FF M) : LaurentSeries (AlgebraicClosure ℚ))
      rw [hbf', hm, map_zero, zero_mul, ZeroMemClass.coe_zero]
    rw [hb0, zero_sub] at hval
    have hneg : algebraMap (AlgebraicClosure ℚ) (FF M) (a : AlgebraicClosure ℚ)
        ∈ w.toValuationSubring.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff] at hval ⊢
      rwa [Valuation.map_neg] at hval
    rw [eq_zero_of_algebraMap_mem_nonunits M w hneg, map_zero]
    exact zero_lt_one
  ·
    set cm : FF M := algebraMap (AlgebraicClosure ℚ) (FF M) (m : AlgebraicClosure ℚ) with hcm
    have hcm0 : cm ≠ 0 := (_root_.map_ne_zero _).2 hm
    have hcmL : (cm : LaurentSeries (AlgebraicClosure ℚ))
        = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
            (m : AlgebraicClosure ℚ) := rfl
    have hcmL0 : algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
        (m : AlgebraicClosure ℚ) ≠ 0 := (_root_.map_ne_zero _).2 hm
    set g : FF M := cm⁻¹ * b with hg
    have hg_coe : (g : LaurentSeries (AlgebraicClosure ℚ))
        = (f' : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [hg, IntermediateField.coe_mul, IntermediateField.coe_inv, hcmL, hbf', ← mul_assoc,
        inv_mul_cancel₀ hcmL0, one_mul]
    have hbg : b = cm * g := by
      rw [hg, mul_inv_cancel_left₀ hcm0]
    have hgint : ∃ p : Polynomial (affineBaseFin M A), p.Monic ∧
        Polynomial.eval₂ (affineBaseFin M A).subtype g p = 0 :=
      integral_of_bivariate M A (hg_coe ▸ hf'int)
    obtain ⟨a', ha'⟩ :=
      ModularCurve.exists_ord_sub_pos_of_integral_affineBaseFin A M w g hgint a₀ hj

    have hkey : algebraMap (AlgebraicClosure ℚ) (FF M)
        ((a : AlgebraicClosure ℚ) - m * a') ∈ w.toValuationSubring.nonunits := by
      have hrw : algebraMap (AlgebraicClosure ℚ) (FF M) ((a : AlgebraicClosure ℚ) - m * a')
          = cm * (g - algebraMap (AlgebraicClosure ℚ) (FF M) (a' : AlgebraicClosure ℚ))
            - (b - algebraMap (AlgebraicClosure ℚ) (FF M) (a : AlgebraicClosure ℚ)) := by
        rw [map_sub, map_mul, hbg, ← hcm]
        ring
      rw [hrw, ValuationSubring.mem_nonunits_iff]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
      · rw [Valuation.map_mul]
        have hcm1 : w.toValuationSubring.valuation cm ≤ 1 :=
          (w.toValuationSubring.valuation_le_one_iff _).2 (w.algebraMap_mem' _)
        calc w.toValuationSubring.valuation cm * w.toValuationSubring.valuation
              (g - algebraMap (AlgebraicClosure ℚ) (FF M) (a' : AlgebraicClosure ℚ))
            ≤ 1 * w.toValuationSubring.valuation
              (g - algebraMap (AlgebraicClosure ℚ) (FF M) (a' : AlgebraicClosure ℚ)) :=
              mul_le_mul' hcm1 le_rfl
          _ < 1 := by
              rw [one_mul]
              exact (ValuationSubring.mem_nonunits_iff _).1 ha'
      · exact (ValuationSubring.mem_nonunits_iff _).1 hval
    have h0 := eq_zero_of_algebraMap_mem_nonunits M w hkey
    have hama : a = m * a' := by
      apply Subtype.ext
      push_cast
      exact sub_eq_zero.1 h0

    rw [← ValuationSubring.valuation_lt_one_iff, hama]
    exact Ideal.mul_mem_right _ _ hm_max

end ValLtOneS8da

p2m_open "ModularCurve~coeffMap_qExpand~coeffEmb_jq" in open  AlgebraicCurve ModularCurve.CharPModel in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M ℓ : ℕ) [NeZero M] [Fact ℓ.Prime]
    (hℓA : A.valuation ((ℓ : ℕ) : AlgebraicClosure ℚ) < 1) (hlM : ¬ ℓ ∣ M)
    (w : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)))
    (a₀ : A)
    (hj : 0 < w.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full M (jq_mem M))⟩
      - algebraMap (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
        (a₀ : AlgebraicClosure ℚ)))
    (b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
    (hb : ∃ p : Polynomial (affineBaseFin M A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin M A).subtype b p = 0)
    (hcoeff : ∀ n : ℤ,
      A.valuation ((b : LaurentSeries (AlgebraicClosure ℚ)).coeff n) < 1)
    (a : A)
    (hval : (b - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M))
      (a : AlgebraicClosure ℚ)) ∈ w.toValuationSubring.nonunits) :
    A.valuation (a : AlgebraicClosure ℚ) < 1 :=
  ValLtOneS8da.main A M ℓ hℓA hlM w a₀ hj b hb hcoeff a hval

end
end S_ModularCurve_valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one
end P2MW
export P2MW.S_ModularCurve_valuation_lt_one_of_ord_sub_pos_of_coeff_lt_one (solution)
