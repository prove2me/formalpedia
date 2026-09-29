-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_eq_ord_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/97141b0c-e77d-5817-9e28-cd05e53e598f

import Mathlib
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Theorems.Thm_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piFin_eq_coeffRed
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piInf_eq_coeffRed_of_cuspChart
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseInf
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_j
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_j_pole
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_finChart_mem_nonunits_iff
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_eq_ord_coeffMap
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000

open AlgebraicCurve

noncomputable section

namespace P2mSolD260

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem placeOrdNonnegOfMem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem placeMemOfOrdNonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem placeMemIffOrdNonneg (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨placeOrdNonnegOfMem v, placeMemOfOrdNonneg v hf⟩

theorem mem_of_mem_nonunits (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring.nonunits) :
    f ∈ v.toValuationSubring :=
  v.toValuationSubring.nonunits_subset hf

theorem nonunits_iff_maximal (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    f ∈ v.toValuationSubring.nonunits ↔
      (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
  ValuationSubring.coe_mem_nonunits_iff (a := (⟨f, hf⟩ : v.toValuationSubring))

theorem nonunits_add (v : Place K F) {f g : F} (hf : f ∈ v.toValuationSubring.nonunits)
    (hg : g ∈ v.toValuationSubring.nonunits) : f + g ∈ v.toValuationSubring.nonunits := by
  have hf' := mem_of_mem_nonunits v hf
  have hg' := mem_of_mem_nonunits v hg
  have h := Ideal.add_mem _ ((nonunits_iff_maximal v hf').mp hf) ((nonunits_iff_maximal v hg').mp hg)
  exact (nonunits_iff_maximal v (add_mem hf' hg')).mpr h

theorem nonunits_neg (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring.nonunits) :
    -f ∈ v.toValuationSubring.nonunits := by
  have hf' := mem_of_mem_nonunits v hf
  have h := neg_mem ((nonunits_iff_maximal v hf').mp hf)
  exact (nonunits_iff_maximal v (neg_mem hf')).mpr h

theorem nonunits_sub (v : Place K F) {f g : F} (hf : f ∈ v.toValuationSubring.nonunits)
    (hg : g ∈ v.toValuationSubring.nonunits) : f - g ∈ v.toValuationSubring.nonunits := by
  rw [sub_eq_add_neg]; exact nonunits_add v hf (nonunits_neg v hg)

theorem nonunits_mul_left (v : Place K F) {f g : F} (hg : g ∈ v.toValuationSubring)
    (hf : f ∈ v.toValuationSubring.nonunits) : g * f ∈ v.toValuationSubring.nonunits := by
  have hf' := mem_of_mem_nonunits v hf
  have h := Ideal.mul_mem_left _ (⟨g, hg⟩ : v.toValuationSubring)
    ((nonunits_iff_maximal v hf').mp hf)
  exact (nonunits_iff_maximal v (mul_mem hg hf')).mpr h

theorem nonunits_iff_ord_pos (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring.nonunits ↔ 0 < v.ord f := by
  constructor
  · intro h
    have hf' := mem_of_mem_nonunits v h
    rcases (Place.mk_mem_maximalIdeal_iff v hf').mp ((nonunits_iff_maximal v hf').mp h) with h0 | h0
    · exact absurd h0 hf
    · exact h0
  · intro h
    have hf' : f ∈ v.toValuationSubring := (placeMemIffOrdNonneg v hf).mpr h.le
    exact (nonunits_iff_maximal v hf').mpr ((Place.mk_mem_maximalIdeal_iff v hf').mpr (Or.inr h))

theorem one_not_mem_nonunits (v : Place K F) : (1 : F) ∉ v.toValuationSubring.nonunits := by
  intro h
  have := (nonunits_iff_maximal v (one_mem _)).mp h
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

theorem algebraMap_not_mem_nonunits (v : Place K F) {c : K} (hc : c ≠ 0) :
    algebraMap K F c ∉ v.toValuationSubring.nonunits := by
  intro h
  have h' : algebraMap K F c⁻¹ * algebraMap K F c ∈ v.toValuationSubring.nonunits :=
    nonunits_mul_left v (v.algebraMap_mem' _) h
  rw [← map_mul, inv_mul_cancel₀ hc, map_one] at h'
  exact one_not_mem_nonunits v h'

theorem algebraMap_mem_nonunits_iff (v : Place K F) (c : K) :
    algebraMap K F c ∈ v.toValuationSubring.nonunits ↔ c = 0 := by
  constructor
  · intro h; by_contra hc; exact algebraMap_not_mem_nonunits v hc h
  · rintro rfl
    rw [map_zero]
    exact zero_mem _

theorem inv_mem_nonunits_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    f⁻¹ ∈ v.toValuationSubring.nonunits :=
  (ValuationSubring.inv_mem_nonunits_iff _).mpr (Or.inr hf)

theorem not_mem_of_inv_mem_nonunits (v : Place K F) {f : F} (hf : f ≠ 0)
    (h : f⁻¹ ∈ v.toValuationSubring.nonunits) : f ∉ v.toValuationSubring := by
  rcases (ValuationSubring.inv_mem_nonunits_iff _).mp h with h | h
  · exact absurd h hf
  · exact h

theorem exists_sub_algebraMap_mem_nonunits (v : Place K F)
    (hsurj : Function.Surjective (algebraMap K v.ResidueField)) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    ∃ c : K, f - algebraMap K F c ∈ v.toValuationSubring.nonunits := by
  obtain ⟨c, hc⟩ := hsurj (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩)
  refine ⟨c, ?_⟩
  have hmem : f - algebraMap K F c ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' c)
  refine (nonunits_iff_maximal v hmem).mpr ?_
  rw [← IsLocalRing.residue_eq_zero_iff]
  have : (⟨f - algebraMap K F c, hmem⟩ : v.toValuationSubring) =
      ⟨f, hf⟩ - algebraMap K v.toValuationSubring c := Subtype.ext (by simp)
  rw [this, map_sub, sub_eq_zero, ← hc]
  exact IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c

end PlaceFacts

section Prolongation

variable {L : Type*} [Field L] (A : ValuationSubring L)
  {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

def Compat (R : RegularProlongation A F Fbar) (x : R.integers) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) : Prop :=
  ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
    ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
      R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
        Q.toValuationSubring.nonunits

variable {A}

theorem isIntegral_adjoin_self (x : F) : IsIntegral (Algebra.adjoin L {x}) x := by
  have : x = algebraMap (Algebra.adjoin L {x}) F ⟨x, Algebra.self_mem_adjoin_singleton L x⟩ := rfl
  rw [this]; exact isIntegral_algebraMap

theorem isIntegral_adjoin_algebraMap (x : F) (c : L) :
    IsIntegral (Algebra.adjoin L {x}) (algebraMap L F c) := by
  have : algebraMap L F c = algebraMap (Algebra.adjoin L {x}) F
      ⟨algebraMap L F c, Subalgebra.algebraMap_mem _ c⟩ := rfl
  rw [this]; exact isIntegral_algebraMap

theorem residue_algebraMap' (R : RegularProlongation A F Fbar) (a : A)
    (h : algebraMap L F (a : L) ∈ R.integers) :
    R.residue ⟨algebraMap L F (a : L), h⟩ =
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

theorem residue_eq_zero_of_mem_nonunits {a : A} (ha : (a : L) ∈ A.nonunits) :
    IsLocalRing.residue A a = 0 :=
  (IsLocalRing.residue_eq_zero_iff _).mpr (ValuationSubring.coe_mem_nonunits_iff.mp ha)

theorem coe_mem_nonunits_of_residue_eq_zero {a : A} (ha : IsLocalRing.residue A a = 0) :
    (a : L) ∈ A.nonunits :=
  ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp ha)

theorem residue_mem_of_compat (R : RegularProlongation A F Fbar) (x : R.integers) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hDP : Compat A R x P Q)
    (hP : ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) :
    R.residue x ∈ Q.toValuationSubring := by
  obtain ⟨a, ha⟩ := hP
  have h := mem_of_mem_nonunits Q (hDP x (isIntegral_adjoin_self (x : F)) a ha)
  have := add_mem h (Q.algebraMap_mem' (IsLocalRing.residue A a))
  simpa using this

theorem exists_sub_mem_nonunits_of_compat [IsAlgClosed L] [IsCurveOver L F]
    (R : RegularProlongation A F Fbar) (x : R.integers) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hDP : Compat A R x P Q)
    (h : R.integers) (hh : IsIntegral (Algebra.adjoin L {(x : F)}) (h : F))
    (hhP : (h : F) ∈ P.toValuationSubring) :
    ∃ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits := by
  have hsurj : Function.Surjective (algebraMap L P.ResidueField) :=
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField P).mp
      (IsCurveOver.deg_eq_one_of_isAlgClosed P)
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_nonunits P hsurj hhP
  by_cases hcA : c ∈ A
  · exact ⟨⟨c, hcA⟩, hc⟩
  exfalso
  have hc0 : c ≠ 0 := by rintro rfl; exact hcA A.zero_mem
  have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  set a' : A := ⟨c⁻¹, hcinv⟩ with ha'
  have ha'0 : IsLocalRing.residue A a' = 0 :=
    residue_eq_zero_of_mem_nonunits ((ValuationSubring.inv_mem_nonunits_iff _).mpr (Or.inr hcA))
  have hcF : algebraMap L F c⁻¹ ∈ R.integers := (R.algebraMap_mem_iff a').mpr a'.2
  set h' : R.integers := ⟨algebraMap L F c⁻¹, hcF⟩ * h with hh'def
  have hh' : IsIntegral (Algebra.adjoin L {(x : F)}) (h' : F) :=
    (isIntegral_adjoin_algebraMap (x : F) c⁻¹).mul hh
  have hval : (h' : F) - algebraMap L F ((1 : A) : L) ∈ P.toValuationSubring.nonunits := by
    have : (h' : F) - algebraMap L F ((1 : A) : L) =
        algebraMap L F c⁻¹ * ((h : F) - algebraMap L F c) := by
      simp only [hh'def, OneMemClass.coe_one, map_one, mul_sub, ← map_mul, inv_mul_cancel₀ hc0]
      rfl
    rw [this]
    exact nonunits_mul_left P (P.algebraMap_mem' _) hc
  have hres := hDP h' hh' 1 hval
  have hres0 : R.residue h' = 0 := by
    rw [hh'def, map_mul, residue_algebraMap' R a' hcF, ha'0, map_zero, zero_mul]
  rw [hres0, map_one, map_one, zero_sub] at hres
  exact one_not_mem_nonunits Q (by simpa using nonunits_neg Q hres)

theorem exists_sub_mem_nonunits_of_residue_mem_nonunits [IsAlgClosed L] [IsCurveOver L F]
    (R : RegularProlongation A F Fbar) (x : R.integers) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hDP : Compat A R x P Q)
    (h : R.integers) (hh : IsIntegral (Algebra.adjoin L {(x : F)}) (h : F))
    (hhP : (h : F) ∈ P.toValuationSubring)
    (hres : R.residue h ∈ Q.toValuationSubring.nonunits) :
    ∃ a : A, IsLocalRing.residue A a = 0 ∧
      (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits := by
  obtain ⟨a, ha⟩ := exists_sub_mem_nonunits_of_compat R x P Q hDP h hh hhP
  refine ⟨a, ?_, ha⟩
  have h1 := hDP h hh a ha
  have h2 := nonunits_sub Q hres h1
  rw [sub_sub_cancel] at h2
  exact (algebraMap_mem_nonunits_iff Q _).mp h2

theorem residue_mem_nonunits_of_sub_mem_nonunits
    (R : RegularProlongation A F Fbar) (x : R.integers) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hDP : Compat A R x P Q)
    (h : R.integers) (hh : IsIntegral (Algebra.adjoin L {(x : F)}) (h : F))
    (a : A) (ha0 : IsLocalRing.residue A a = 0)
    (ha : (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) :
    R.residue h ∈ Q.toValuationSubring.nonunits := by
  simpa [ha0] using hDP h hh a ha

end Prolongation

section ModularSetup

open ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction

theorem transport_prolongation (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (E₁ E₂ : IntermediateField (IsLocalRing.ResidueField A)
      (LaurentSeries (IsLocalRing.ResidueField A)))
    (h : E₁ = E₂)
    (hex : ∃ R : RegularProlongation A (modularFunctionFieldBar N) E₁,
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : E₁) : LaurentSeries (IsLocalRing.ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y) :
    ∃ R : RegularProlongation A (modularFunctionFieldBar N) E₂,
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : E₂) : LaurentSeries (IsLocalRing.ResidueField A)) =
            coeffMap (IsLocalRing.residue A) y := by
  subst h; exact hex

theorem transport_finrank {k : Type*} [Field k] (E₁ E₂ : IntermediateField k (LaurentSeries k))
    (h : E₁ = E₂) (x : LaurentSeries k) (hx₁ : x ∈ E₁) (hx₂ : x ∈ E₂) :
    Module.finrank (IntermediateField.adjoin k ({⟨x, hx₁⟩} : Set E₁)) E₁ =
      Module.finrank (IntermediateField.adjoin k ({⟨x, hx₂⟩} : Set E₂)) E₂ := by
  subst h; rfl

def pack (A : ValuationSubring (AlgebraicClosure ℚ)) (x : integralCoeffs A.toSubring) :
    LaurentSeries A where
  coeff n := ⟨(x : LaurentSeries (AlgebraicClosure ℚ)).coeff n, x.2 n⟩
  isPWO_support' := (x : LaurentSeries (AlgebraicClosure ℚ)).isPWO_support.mono
    (fun _ hn h => hn (Subtype.ext h))

theorem coeffMap_subtype_pack (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : integralCoeffs A.toSubring) :
    coeffMap A.subtype (pack A x) = (x : LaurentSeries (AlgebraicClosure ℚ)) := by
  ext n; rfl

theorem coeffRed_eq_coeffMap_pack (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*}
    [CommRing k] (red : A →+* k) (x : integralCoeffs A.toSubring) :
    coeffRed A.toSubring red x = coeffMap red (pack A x) := by
  ext n; rfl

theorem liesOverPrime_of_charP (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ)
    [CharP (IsLocalRing.ResidueField A) ℓ] : A.LiesOverPrime ℓ := by
  have h : IsLocalRing.residue A (ℓ : A) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero _ ℓ
  have := coe_mem_nonunits_of_residue_eq_zero h
  simp at this
  exact this

theorem exists_prolongation (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (IsLocalRing.ResidueField A) ℓ]
    (hℓN : ¬ ℓ ∣ N) :
    ∃ R : RegularProlongation A (modularFunctionFieldBar N)
        (modularFunctionFieldC (IsLocalRing.ResidueField A) N),
      ∀ (g : modularFunctionFieldBar N)
        (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring),
        ∃ hint : g ∈ R.integers,
          ((R.residue ⟨g, hint⟩ : modularFunctionFieldC (IsLocalRing.ResidueField A) N) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            coeffRed A.toSubring (IsLocalRing.residue A) ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hg⟩ := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hCF := modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos
    (IsLocalRing.ResidueField A) ℓ N hℓN
  obtain ⟨R, hR⟩ := transport_prolongation N A _ _ hCF.symm
    (exists_regularProlongation_modularFunctionFieldBar N hℓN A (liesOverPrime_of_charP A ℓ))
  refine ⟨R, fun g hg => ?_⟩
  obtain ⟨gv, gp⟩ := g
  have hgv : gv = coeffMap A.subtype (pack A ⟨gv, hg⟩) := (coeffMap_subtype_pack A ⟨gv, hg⟩).symm
  obtain ⟨hint, hres⟩ := hR (pack A ⟨gv, hg⟩) (hgv ▸ gp)
  have hint' : (⟨gv, gp⟩ : modularFunctionFieldBar N) ∈ R.integers := by
    convert hint using 2
  refine ⟨hint', ?_⟩
  rw [coeffRed_eq_coeffMap_pack, ← hres]
  congr 3

end ModularSetup

section Charts

open ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isIntegral_of_subalgebra_le {S₁ S₂ : Subalgebra K F} (hle : S₁ ≤ S₂) {h : F}
    (hh : IsIntegral S₁ h) : IsIntegral S₂ h := by
  obtain ⟨p, hp, he⟩ := hh
  have hcomp : (algebraMap S₂ F).comp (Subalgebra.inclusion hle).toRingHom = algebraMap S₁ F :=
    RingHom.ext fun _ => rfl
  refine ⟨p.map (Subalgebra.inclusion hle).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]; exact he

theorem isIntegral_subalgebra_of_eval₂_subtype (B : Subring F) (S : Subalgebra K F)
    (hle : ∀ x ∈ B, x ∈ S) {b : F}
    (hb : ∃ p : Polynomial B, p.Monic ∧ Polynomial.eval₂ B.subtype b p = 0) :
    IsIntegral S b := by
  obtain ⟨p, hp, he⟩ := hb
  set φ : B →+* S := B.subtype.codRestrict S (fun x => hle x x.2)
  have hcomp : (algebraMap S F).comp φ = B.subtype := RingHom.ext fun _ => rfl
  refine ⟨p.map φ, hp.map φ, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]; exact he

theorem exists_eval₂_of_isIntegral_of_le (S : Subalgebra K F) (B : Subring F)
    (hle : ∀ x ∈ S, x ∈ B) {h : F} (hh : IsIntegral S h) :
    ∃ p : Polynomial B, p.Monic ∧ Polynomial.eval₂ B.subtype h p = 0 := by
  obtain ⟨p, hp, he⟩ := hh
  set φ : S →+* B := (algebraMap S F).codRestrict B (fun x => hle x x.2)
  have hcomp : B.subtype.comp φ = algebraMap S F := RingHom.ext fun _ => rfl
  exact ⟨p.map φ, hp.map φ, by rw [Polynomial.eval₂_map, hcomp]; exact he⟩

theorem IntermediateField.adjoin_simple_inv_eq' (x : F) :
    IntermediateField.adjoin K ({x⁻¹} : Set F) = IntermediateField.adjoin K {x} := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (inv_mem (IntermediateField.mem_adjoin_simple_self K x))
  · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
    have := inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
    rwa [inv_inv] at this

theorem finrank_congr_intermediateField {E₁ E₂ : IntermediateField K F} (h : E₁ = E₂) :
    Module.finrank E₁ F = Module.finrank E₂ F := by
  subst h; rfl

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
  [CharP (IsLocalRing.ResidueField A) ℓ]
  (R : RegularProlongation A (modularFunctionFieldBar N)
    (modularFunctionFieldC (IsLocalRing.ResidueField A) N))

def QExp : Prop :=
  ∀ (g : modularFunctionFieldBar N)
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ integralCoeffs A.toSubring),
    ∃ hint : g ∈ R.integers,
      ((R.residue ⟨g, hint⟩ : modularFunctionFieldC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        coeffRed A.toSubring (IsLocalRing.residue A) ⟨(g : LaurentSeries (AlgebraicClosure ℚ)), hg⟩

variable {N ℓ A R}

theorem residue_BFin (fm : FibreModel N A ℓ (IsLocalRing.ResidueField A) (IsLocalRing.residue A)) (hR : QExp N A R) (b : fm.BFin) :
    ∃ hint : (b : modularFunctionFieldBar N) ∈ R.integers, R.residue ⟨b, hint⟩ = fm.piFin b := by
  have hmem := mem_integralCoeffs_of_integral_affineBaseFin A N b (fm.integralFin b)
  obtain ⟨hint, hres⟩ := hR b hmem
  exact ⟨hint, Subtype.ext (hres.trans
    (FibreModel.coe_piFin_eq_coeffRed N A ℓ (IsLocalRing.ResidueField A) (IsLocalRing.residue A)
      fm b hmem).symm)⟩

theorem residue_BInf (fm : FibreModel N A ℓ (IsLocalRing.ResidueField A) (IsLocalRing.residue A)) (hR : QExp N A R) (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A))
        (RatFunc (IsLocalRing.ResidueField A)))).Separable)
    (b : fm.BInf) :
    ∃ hint : (b : modularFunctionFieldBar N) ∈ R.integers, R.residue ⟨b, hint⟩ = fm.piInf b := by
  have hmem := mem_integralCoeffs_of_integral_affineBaseInf A N b (fm.integralInf b)
  obtain ⟨hint, hres⟩ := hR b hmem
  exact ⟨hint, Subtype.ext (hres.trans
    (FibreModel.coe_piInf_eq_coeffRed_of_cuspChart N A ℓ (IsLocalRing.ResidueField A) (IsLocalRing.residue A)
      fm cc (dataAll N (dvd_refl N)) hsep b hmem).symm)⟩

theorem affineBaseFin_le_adjoin :
    ∀ x ∈ affineBaseFin N A, x ∈ Algebra.adjoin (AlgebraicClosure ℚ)
      ({(CharPModel.jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)) := by
  intro x hx
  have hle : affineBaseFin N A ≤ (Algebra.adjoin (AlgebraicClosure ℚ)
      ({(CharPModel.jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))).toSubring := by
    refine Subring.closure_le.mpr ?_
    rintro y (⟨a, rfl⟩ | rfl)
    · exact Subalgebra.algebraMap_mem _ (a : AlgebraicClosure ℚ)
    · exact Algebra.self_mem_adjoin_singleton _ _
  exact hle hx

theorem affineBaseInf_le_adjoin :
    ∀ x ∈ affineBaseInf N A, x ∈ Algebra.adjoin (AlgebraicClosure ℚ)
      ({((CharPModel.jBar N : modularFunctionFieldBar N))⁻¹} : Set (modularFunctionFieldBar N)) := by
  intro x hx
  have hle : affineBaseInf N A ≤ (Algebra.adjoin (AlgebraicClosure ℚ)
      ({((CharPModel.jBar N : modularFunctionFieldBar N))⁻¹} : Set (modularFunctionFieldBar N))).toSubring := by
    refine Subring.closure_le.mpr ?_
    rintro y (⟨a, rfl⟩ | rfl)
    · exact Subalgebra.algebraMap_mem _ (a : AlgebraicClosure ℚ)
    · exact Algebra.self_mem_adjoin_singleton _ _
  exact hle hx

theorem isIntegral_BFin (fm : FibreModel N A ℓ (IsLocalRing.ResidueField A) (IsLocalRing.residue A)) (b : fm.BFin) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      ({(CharPModel.jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
      (b : modularFunctionFieldBar N) :=
  isIntegral_subalgebra_of_eval₂_subtype (affineBaseFin N A) _ (affineBaseFin_le_adjoin (N := N)
    (A := A)) (fm.integralFin b)

theorem isIntegral_BInf (fm : FibreModel N A ℓ (IsLocalRing.ResidueField A) (IsLocalRing.residue A)) (b : fm.BInf) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      ({((CharPModel.jBar N : modularFunctionFieldBar N))⁻¹} : Set (modularFunctionFieldBar N)))
      (b : modularFunctionFieldBar N) :=
  isIntegral_subalgebra_of_eval₂_subtype (affineBaseInf N A) _ (affineBaseInf_le_adjoin (N := N)
    (A := A)) (fm.integralInf b)

theorem adjoin_le_piFin_range (fm : FibreModel N A ℓ (IsLocalRing.ResidueField A) (IsLocalRing.residue A)) :
    ∀ x ∈ Algebra.adjoin (IsLocalRing.ResidueField A)
      ({(⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem (IsLocalRing.ResidueField A) N⟩ :
        modularFunctionFieldC (IsLocalRing.ResidueField A) N)} :
        Set (modularFunctionFieldC (IsLocalRing.ResidueField A) N)),
      x ∈ fm.piFin.range := by
  intro x hx
  rw [Algebra.mem_adjoin_iff] at hx
  refine Subring.closure_le.mpr ?_ hx
  rintro y (⟨r, rfl⟩ | rfl)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact RingHom.mem_range.mpr ⟨⟨constantsHom N A a, fm.constFin_mem a⟩, fm.piFin_const a⟩
  · exact RingHom.mem_range.mpr ⟨⟨CharPModel.jBar N, fm.jBar_mem⟩, fm.piFin_j⟩

theorem adjoin_le_piInf_range (fm : FibreModel N A ℓ (IsLocalRing.ResidueField A) (IsLocalRing.residue A)) :
    ∀ x ∈ Algebra.adjoin (IsLocalRing.ResidueField A)
      ({(⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem (IsLocalRing.ResidueField A) N⟩ :
        modularFunctionFieldC (IsLocalRing.ResidueField A) N)⁻¹} :
        Set (modularFunctionFieldC (IsLocalRing.ResidueField A) N)),
      x ∈ fm.piInf.range := by
  intro x hx
  rw [Algebra.mem_adjoin_iff] at hx
  refine Subring.closure_le.mpr ?_ hx
  rintro y (⟨r, rfl⟩ | rfl)
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact RingHom.mem_range.mpr ⟨⟨constantsHom N A a, fm.constInf_mem a⟩, fm.piInf_const a⟩
  · exact RingHom.mem_range.mpr ⟨⟨(CharPModel.jBar N)⁻¹, fm.jInvBar_mem⟩, fm.piInf_jInv⟩

theorem hchart_fin (fm : FibreModel N A ℓ (IsLocalRing.ResidueField A) (IsLocalRing.residue A)) (hR : QExp N A R)
    (h : modularFunctionFieldC (IsLocalRing.ResidueField A) N)
    (hh : IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A)
      ({(⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem (IsLocalRing.ResidueField A) N⟩ :
        modularFunctionFieldC (IsLocalRing.ResidueField A) N)} :
        Set (modularFunctionFieldC (IsLocalRing.ResidueField A) N))) h) :
    ∃ f : R.integers, IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
        ({(CharPModel.jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
        (f : modularFunctionFieldBar N) ∧ R.residue f = h := by
  obtain ⟨b, hb⟩ := RingHom.mem_range.mp (fm.intClosed_piFin h
    (exists_eval₂_of_isIntegral_of_le _ fm.piFin.range (adjoin_le_piFin_range fm) hh))
  obtain ⟨hint, hres⟩ := residue_BFin fm hR b
  exact ⟨⟨b, hint⟩, isIntegral_BFin fm b, hres.trans hb⟩

theorem hchart_inf (fm : FibreModel N A ℓ (IsLocalRing.ResidueField A) (IsLocalRing.residue A)) (hR : QExp N A R) (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A))
        (RatFunc (IsLocalRing.ResidueField A)))).Separable)
    (h : modularFunctionFieldC (IsLocalRing.ResidueField A) N)
    (hh : IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A)
      ({(⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem (IsLocalRing.ResidueField A) N⟩ :
        modularFunctionFieldC (IsLocalRing.ResidueField A) N)⁻¹} :
        Set (modularFunctionFieldC (IsLocalRing.ResidueField A) N))) h) :
    ∃ f : R.integers, IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
        ({((CharPModel.jBar N : modularFunctionFieldBar N))⁻¹} : Set (modularFunctionFieldBar N)))
        (f : modularFunctionFieldBar N) ∧ R.residue f = h := by
  obtain ⟨b, hb⟩ := RingHom.mem_range.mp (fm.intClosed_piInf h
    (exists_eval₂_of_isIntegral_of_le _ fm.piInf.range (adjoin_le_piInf_range fm) hh))
  obtain ⟨hint, hres⟩ := residue_BInf fm hR cc dataAll hsep b
  exact ⟨⟨b, hint⟩, isIntegral_BInf fm b, hres.trans hb⟩

end Charts

section Core

open ModularCurve ModularCurve.CharPModel ModularCurve.CharPReduction

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "kk[" A "]" => IsLocalRing.ResidueField A
local notation "FF[" N "]" => modularFunctionFieldBar N
local notation "CC[" A "," N "]" => modularFunctionFieldC (IsLocalRing.ResidueField A) N
local notation "jB[" N "]" => (CharPModel.jBar N : modularFunctionFieldBar N)
set_option quotPrecheck false in
local notation "jC[" A "," N "]" =>
  (⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem (IsLocalRing.ResidueField A) N⟩ :
    modularFunctionFieldC (IsLocalRing.ResidueField A) N)

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (IsLocalRing.ResidueField A) ℓ]
  {R : RegularProlongation A (modularFunctionFieldBar N)
    (modularFunctionFieldC (IsLocalRing.ResidueField A) N)}

theorem transcendental_jC : Transcendental kk[A] jC[A,N] := by
  have hinj : Function.Injective (algebraMap CC[A,N] (LaurentSeries kk[A])) :=
    Subtype.val_injective
  exact (transcendental_algebraMap_iff hinj).mp (by exact transcendental_jqModC kk[A])

theorem transcendental_jC_inv : Transcendental kk[A] (jC[A,N])⁻¹ :=
  fun h => transcendental_jC (IsAlgebraic.inv_iff.mp h)

theorem jC_sub_algebraMap_ne_zero (c : kk[A]) : jC[A,N] - algebraMap kk[A] CC[A,N] c ≠ 0 := by
  intro h
  exact transcendental_jC (N := N) (A := A) (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap c)

variable (hℓN : ¬ ℓ ∣ N)
include hℓN

omit [NeZero N] [Fact ℓ.Prime] in
theorem natCast_N_ne_zero : (N : kk[A]) ≠ 0 := fun h =>
  hℓN ((CharP.cast_eq_zero_iff kk[A] ℓ N).mp h)

theorem finrank_adjoin_jC :
    Module.finrank (IntermediateField.adjoin kk[A] ({jC[A,N]} : Set CC[A,N])) CC[A,N] =
      dedekindPsi N := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have hCF := modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos kk[A] ℓ N hℓN
  exact (transport_finrank _ _ hCF (jqModC kk[A]) (jqModC_mem kk[A] N)
    (jqModC_mem_full kk[A] N)).trans
    (finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi kk[A] N (natCast_N_ne_zero hℓN))

theorem finrank_adjoin_jC_inv :
    Module.finrank (IntermediateField.adjoin kk[A] ({(jC[A,N])⁻¹} : Set CC[A,N])) CC[A,N] =
      dedekindPsi N :=
  (finrank_congr_intermediateField (IntermediateField.adjoin_simple_inv_eq' _)).trans
    (finrank_adjoin_jC hℓN)

omit hℓN in
theorem finrank_adjoin_jB :
    Module.finrank (IntermediateField.adjoin ℚ̄ ({jB[N]} : Set FF[N])) FF[N] = dedekindPsi N :=
  CompEq.finrank_adjoin_jBar_eq_dedekindPsi N

omit hℓN in
theorem finrank_adjoin_jB_inv :
    Module.finrank (IntermediateField.adjoin ℚ̄ ({(jB[N])⁻¹} : Set FF[N])) FF[N] = dedekindPsi N :=
  (finrank_congr_intermediateField (IntermediateField.adjoin_simple_inv_eq' _)).trans
    finrank_adjoin_jB

omit hℓN in

theorem jB_sub_ne_zero (hintj : jB[N] ∈ R.integers) (hresj : R.residue ⟨jB[N], hintj⟩ = jC[A,N])
    (a : A) : jB[N] - algebraMap ℚ̄ FF[N] (a : ℚ̄) ≠ 0 := by
  intro h
  have heq : jB[N] = algebraMap ℚ̄ FF[N] (a : ℚ̄) := sub_eq_zero.mp h
  have hmem : algebraMap ℚ̄ FF[N] (a : ℚ̄) ∈ R.integers := heq ▸ hintj
  have h1 : R.residue ⟨jB[N], hintj⟩ = R.residue ⟨algebraMap ℚ̄ FF[N] (a : ℚ̄), hmem⟩ := by
    congr 1; exact Subtype.ext heq
  rw [hresj, residue_algebraMap' R a hmem] at h1
  exact transcendental_jC (N := N) (A := A) (h1 ▸ isAlgebraic_algebraMap _)

omit hℓN in
theorem jB_inv_sub_ne_zero (hinti : (jB[N])⁻¹ ∈ R.integers)
    (hresi : R.residue ⟨(jB[N])⁻¹, hinti⟩ = (jC[A,N])⁻¹)
    (a : A) : (jB[N])⁻¹ - algebraMap ℚ̄ FF[N] (a : ℚ̄) ≠ 0 := by
  intro h
  have heq : (jB[N])⁻¹ = algebraMap ℚ̄ FF[N] (a : ℚ̄) := sub_eq_zero.mp h
  have hmem : algebraMap ℚ̄ FF[N] (a : ℚ̄) ∈ R.integers := heq ▸ hinti
  have h1 : R.residue ⟨(jB[N])⁻¹, hinti⟩ = R.residue ⟨algebraMap ℚ̄ FF[N] (a : ℚ̄), hmem⟩ := by
    congr 1; exact Subtype.ext heq
  rw [hresi, residue_algebraMap' R a hmem] at h1
  exact transcendental_jC_inv (N := N) (A := A) (h1 ▸ isAlgebraic_algebraMap _)

theorem data_fin (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A)) (hR : QExp N A R)
    (hintj : jB[N] ∈ R.integers) (hresj : R.residue ⟨jB[N], hintj⟩ = jC[A,N]) :
    Transcendental kk[A] (R.residue ⟨jB[N], hintj⟩) ∧
    0 < Module.finrank (IntermediateField.adjoin kk[A]
      ({R.residue ⟨jB[N], hintj⟩} : Set CC[A,N])) CC[A,N] ∧
    Module.finrank (IntermediateField.adjoin ℚ̄
        ({((⟨jB[N], hintj⟩ : R.integers) : FF[N])} : Set FF[N])) FF[N] =
      Module.finrank (IntermediateField.adjoin kk[A]
        ({R.residue ⟨jB[N], hintj⟩} : Set CC[A,N])) CC[A,N] ∧
    ∀ h : CC[A,N], IsIntegral (Algebra.adjoin kk[A] {R.residue ⟨jB[N], hintj⟩}) h →
      ∃ f : R.integers, IsIntegral (Algebra.adjoin ℚ̄ {((⟨jB[N], hintj⟩ : R.integers) : FF[N])})
        (f : FF[N]) ∧ R.residue f = h := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hresj]; exact transcendental_jC
  · rw [hresj, finrank_adjoin_jC hℓN]; exact dedekindPsi_pos N (NeZero.ne N)
  · rw [hresj, finrank_adjoin_jC hℓN]; exact finrank_adjoin_jB
  · rw [hresj]; exact fun h hh => hchart_fin fm hR h hh

theorem engine_fin (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A)) (hR : QExp N A R)
    (hintj : jB[N] ∈ R.integers) (hresj : R.residue ⟨jB[N], hintj⟩ = jC[A,N])
    (P : Place ℚ̄ FF[N])
    (hP : ∃ a : A, jB[N] - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits) :
    ∃! Q : Place kk[A] CC[A,N], Compat A R ⟨jB[N], hintj⟩ P Q := by
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI : IsCurveOver kk[A] CC[A,N] := isCurveOver_modularFunctionFieldC_of_perfectField _ N
  haveI : IsCurveOver ℚ̄ FF[N] := isCurveOver_modularFunctionFieldBar N
  obtain ⟨hx, hfin, hdeg, hchart⟩ := data_fin hℓN fm hR hintj hresj
  exact R.existsUnique_place_forall_residue_sub_mem_nonunits A ⟨jB[N], hintj⟩ hx hfin hdeg hchart P hP

theorem sum_fin (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A)) (hR : QExp N A R)
    (hintj : jB[N] ∈ R.integers) (hresj : R.residue ⟨jB[N], hintj⟩ = jC[A,N])
    (f : R.integers) (hf : R.residue f ≠ 0)
    (Q : Place kk[A] CC[A,N]) (hQ : jC[A,N] ∈ Q.toValuationSubring)
    (D : Divisor ℚ̄ FF[N]) (hD : ∀ P, D P = P.ord (f : FF[N]))
    (T : Finset (Place ℚ̄ FF[N]))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧
      (∃ a : A, jB[N] - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits) ∧
      Compat A R ⟨jB[N], hintj⟩ P Q)) :
    ∑ P ∈ T, D P = Q.ord (R.residue f) := by
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI : IsCurveOver kk[A] CC[A,N] := isCurveOver_modularFunctionFieldC_of_perfectField _ N
  haveI : IsCurveOver ℚ̄ FF[N] := isCurveOver_modularFunctionFieldBar N
  obtain ⟨hx, hfin, hdeg, hchart⟩ := data_fin hℓN fm hR hintj hresj
  have hQ' : R.residue ⟨jB[N], hintj⟩ ∈ Q.toValuationSubring := by rw [hresj]; exact hQ
  exact R.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective A ⟨jB[N], hintj⟩ hx hfin
    hdeg hchart f hf Q hQ' D hD T hT

theorem data_inf (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A)) (hR : QExp N A R)
    (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom kk[A]))).map
      (algebraMap (Polynomial kk[A]) (RatFunc kk[A]))).Separable)
    (hinti : (jB[N])⁻¹ ∈ R.integers) (hresi : R.residue ⟨(jB[N])⁻¹, hinti⟩ = (jC[A,N])⁻¹) :
    Transcendental kk[A] (R.residue ⟨(jB[N])⁻¹, hinti⟩) ∧
    0 < Module.finrank (IntermediateField.adjoin kk[A]
      ({R.residue ⟨(jB[N])⁻¹, hinti⟩} : Set CC[A,N])) CC[A,N] ∧
    Module.finrank (IntermediateField.adjoin ℚ̄
        ({((⟨(jB[N])⁻¹, hinti⟩ : R.integers) : FF[N])} : Set FF[N])) FF[N] =
      Module.finrank (IntermediateField.adjoin kk[A]
        ({R.residue ⟨(jB[N])⁻¹, hinti⟩} : Set CC[A,N])) CC[A,N] ∧
    ∀ h : CC[A,N], IsIntegral (Algebra.adjoin kk[A] {R.residue ⟨(jB[N])⁻¹, hinti⟩}) h →
      ∃ f : R.integers,
        IsIntegral (Algebra.adjoin ℚ̄ {((⟨(jB[N])⁻¹, hinti⟩ : R.integers) : FF[N])})
          (f : FF[N]) ∧ R.residue f = h := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hresi]; exact transcendental_jC_inv
  · rw [hresi, finrank_adjoin_jC_inv hℓN]; exact dedekindPsi_pos N (NeZero.ne N)
  · rw [hresi, finrank_adjoin_jC_inv hℓN]; exact finrank_adjoin_jB_inv
  · rw [hresi]; exact fun h hh => hchart_inf fm hR cc dataAll hsep h hh

theorem engine_inf (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A)) (hR : QExp N A R)
    (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom kk[A]))).map
      (algebraMap (Polynomial kk[A]) (RatFunc kk[A]))).Separable)
    (hinti : (jB[N])⁻¹ ∈ R.integers) (hresi : R.residue ⟨(jB[N])⁻¹, hinti⟩ = (jC[A,N])⁻¹)
    (P : Place ℚ̄ FF[N])
    (hP : ∃ a : A, (jB[N])⁻¹ - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits) :
    ∃! Q : Place kk[A] CC[A,N], Compat A R ⟨(jB[N])⁻¹, hinti⟩ P Q := by
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI : IsCurveOver kk[A] CC[A,N] := isCurveOver_modularFunctionFieldC_of_perfectField _ N
  haveI : IsCurveOver ℚ̄ FF[N] := isCurveOver_modularFunctionFieldBar N
  obtain ⟨hx, hfin, hdeg, hchart⟩ := data_inf hℓN fm hR cc dataAll hsep hinti hresi
  exact R.existsUnique_place_forall_residue_sub_mem_nonunits A ⟨(jB[N])⁻¹, hinti⟩ hx hfin hdeg
    hchart P hP

theorem sum_inf (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A)) (hR : QExp N A R)
    (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom kk[A]))).map
      (algebraMap (Polynomial kk[A]) (RatFunc kk[A]))).Separable)
    (hinti : (jB[N])⁻¹ ∈ R.integers) (hresi : R.residue ⟨(jB[N])⁻¹, hinti⟩ = (jC[A,N])⁻¹)
    (f : R.integers) (hf : R.residue f ≠ 0)
    (Q : Place kk[A] CC[A,N]) (hQ : (jC[A,N])⁻¹ ∈ Q.toValuationSubring)
    (D : Divisor ℚ̄ FF[N]) (hD : ∀ P, D P = P.ord (f : FF[N]))
    (T : Finset (Place ℚ̄ FF[N]))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧
      (∃ a : A, (jB[N])⁻¹ - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits) ∧
      Compat A R ⟨(jB[N])⁻¹, hinti⟩ P Q)) :
    ∑ P ∈ T, D P = Q.ord (R.residue f) := by
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI : IsCurveOver kk[A] CC[A,N] := isCurveOver_modularFunctionFieldC_of_perfectField _ N
  haveI : IsCurveOver ℚ̄ FF[N] := isCurveOver_modularFunctionFieldBar N
  obtain ⟨hx, hfin, hdeg, hchart⟩ := data_inf hℓN fm hR cc dataAll hsep hinti hresi
  have hQ' : R.residue ⟨(jB[N])⁻¹, hinti⟩ ∈ Q.toValuationSubring := by rw [hresi]; exact hQ
  exact R.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective A ⟨(jB[N])⁻¹, hinti⟩ hx
    hfin hdeg hchart f hf Q hQ' D hD T hT

omit [CharP (IsLocalRing.ResidueField A) ℓ] hℓN in

theorem jB_mem_of_chart {P : Place ℚ̄ FF[N]}
    (hP : ∃ a : A, jB[N] - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits) :
    jB[N] ∈ P.toValuationSubring := by
  obtain ⟨a, ha⟩ := hP
  have := add_mem (mem_of_mem_nonunits P ha) (P.algebraMap_mem' (a : ℚ̄))
  simpa using this

omit [CharP (IsLocalRing.ResidueField A) ℓ] hℓN in
theorem jB_inv_mem_of_chart {P : Place ℚ̄ FF[N]}
    (hP : ∃ a : A, (jB[N])⁻¹ - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits) :
    (jB[N])⁻¹ ∈ P.toValuationSubring := by
  obtain ⟨a, ha⟩ := hP
  have := add_mem (mem_of_mem_nonunits P ha) (P.algebraMap_mem' (a : ℚ̄))
  simpa using this

theorem compat_spPlace_fin (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A)) (hR : QExp N A R)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom kk[A]))).map
      (algebraMap (Polynomial kk[A]) (RatFunc kk[A]))).Separable)
    (hintj : jB[N] ∈ R.integers) (hresj : R.residue ⟨jB[N], hintj⟩ = jC[A,N])
    (P : Place ℚ̄ FF[N])
    (hP : ∃ a : A, jB[N] - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits) :
    Compat A R ⟨jB[N], hintj⟩ P (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P) ∧
      ∀ Q, Compat A R ⟨jB[N], hintj⟩ P Q →
        Q = fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P := by
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI : IsCurveOver ℚ̄ FF[N] := isCurveOver_modularFunctionFieldBar N
  obtain ⟨Qs, hQs, huniq⟩ := engine_fin hℓN fm hR hintj hresj P hP
  obtain ⟨a₀, ha₀⟩ := hP
  have hpos : 0 < P.ord (jB[N] - algebraMap ℚ̄ FF[N] (a₀ : ℚ̄)) :=
    (nonunits_iff_ord_pos P (jB_sub_ne_zero hintj hresj a₀)).mp ha₀
  have hjP : jB[N] ∈ P.toValuationSubring := jB_mem_of_chart ⟨a₀, ha₀⟩

  have hj₁ : jC[A,N] ∈ Qs.toValuationSubring :=
    hresj ▸ residue_mem_of_compat R ⟨jB[N], hintj⟩ P Qs hQs ⟨a₀, ha₀⟩

  have hj₂ : jC[A,N] ∈ (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P).toValuationSubring := by
    have h2 := FibreModel.spPlace_d0_j N A ℓ kk[A] (IsLocalRing.residue A) fm
      Ideal.Quotient.mk_surjective dataAll hsep P a₀ hpos
    have hmem : jC[A,N] - algebraMap kk[A] CC[A,N] (IsLocalRing.residue A a₀) ∈
        (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P).toValuationSubring :=
      (placeMemIffOrdNonneg _ (jC_sub_algebraMap_ne_zero _)).mpr h2.le
    have := add_mem hmem ((fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P).algebraMap_mem'
      (IsLocalRing.residue A a₀))
    simpa using this
  have hFin : ∀ b : fm.BFin, (fm.piFin b : CC[A,N]) ∈ Qs.toValuationSubring.nonunits ↔
      (fm.piFin b : CC[A,N]) ∈
        (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P).toValuationSubring.nonunits := by
    intro b
    rw [fm.piFin_mem_spPlace_nonunits_iff Ideal.Quotient.mk_surjective dataAll hsep P a₀ hpos b]
    obtain ⟨hintb, hresb⟩ := residue_BFin fm hR b
    rw [← hresb]
    constructor
    · intro hres
      have hbP : (b : FF[N]) ∈ P.toValuationSubring :=
        Place.mem_toValuationSubring_of_isIntegral_adjoin P hjP (isIntegral_BFin fm b)
      obtain ⟨a', ha'0, ha'⟩ := exists_sub_mem_nonunits_of_residue_mem_nonunits R ⟨jB[N], hintj⟩
        P Qs hQs ⟨b, hintb⟩ (isIntegral_BFin fm b) hbP hres
      exact ⟨a', (IsLocalRing.residue_eq_zero_iff _).mp ha'0, ha'⟩
    · rintro ⟨a', ha'm, ha'⟩
      exact residue_mem_nonunits_of_sub_mem_nonunits R ⟨jB[N], hintj⟩ P Qs hQs ⟨b, hintb⟩
        (isIntegral_BFin fm b) a' ((IsLocalRing.residue_eq_zero_iff _).mpr ha'm) ha'
  have hEq : Qs = fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P :=
    FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff N ℓ A kk[A] (IsLocalRing.residue A) fm
      Ideal.Quotient.mk_surjective dataAll hsep Qs _ hj₁ hj₂ hFin
  exact ⟨hEq ▸ hQs, fun Q hQ => (huniq Q hQ).trans hEq⟩

theorem compat_spPlace_inf (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A)) (hR : QExp N A R)
    (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom kk[A]))).map
      (algebraMap (Polynomial kk[A]) (RatFunc kk[A]))).Separable)
    (hinti : (jB[N])⁻¹ ∈ R.integers) (hresi : R.residue ⟨(jB[N])⁻¹, hinti⟩ = (jC[A,N])⁻¹)
    (hintj : jB[N] ∈ R.integers) (hresj : R.residue ⟨jB[N], hintj⟩ = jC[A,N])
    (P : Place ℚ̄ FF[N])
    (hpole : ∀ a : A, P.ord (jB[N] - algebraMap ℚ̄ FF[N] (a : ℚ̄)) ≤ 0) :
    (∃ a : A, (jB[N])⁻¹ - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits) ∧
    Compat A R ⟨(jB[N])⁻¹, hinti⟩ P (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P) ∧
      ∀ Q, Compat A R ⟨(jB[N])⁻¹, hinti⟩ P Q →
        Q = fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P := by
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI : IsCurveOver ℚ̄ FF[N] := isCurveOver_modularFunctionFieldBar N

  have hsurj := (Place.deg_eq_one_iff_surjective_algebraMap_residueField P).mp
    (IsCurveOver.deg_eq_one_of_isAlgClosed P)
  have hinvP : (jB[N])⁻¹ ∈ P.toValuationSubring := by
    by_contra hnot
    have h1 : jB[N] ∈ P.toValuationSubring.nonunits := by
      have := inv_mem_nonunits_of_not_mem P hnot
      rwa [inv_inv] at this
    have h3 := (nonunits_iff_ord_pos P (jB_sub_ne_zero hintj hresj (0 : A))).mp
      (by simpa using h1)
    exact absurd (hpole 0) (not_le.mpr h3)
  have hP : ∃ a : A, (jB[N])⁻¹ - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits := by
    obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_nonunits P hsurj hinvP
    by_cases hcA : c ∈ A
    · exact ⟨⟨c, hcA⟩, hc⟩
    · exfalso

      have hc0 : c ≠ 0 := by rintro rfl; exact hcA A.zero_mem
      have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
      have hc0' : algebraMap ℚ̄ FF[N] c ≠ 0 := (map_ne_zero _).mpr hc0
      have hjP : jB[N] ∈ P.toValuationSubring := by
        by_contra hnot
        have h1 := inv_mem_nonunits_of_not_mem P hnot
        have h2 : algebraMap ℚ̄ FF[N] c ∈ P.toValuationSubring.nonunits := by
          have := nonunits_sub P h1 hc
          rwa [sub_sub_cancel] at this
        exact hc0 ((algebraMap_mem_nonunits_iff P c).mp h2)
      have hj0 : jB[N] ≠ 0 := by
        intro h0
        have h2 : algebraMap ℚ̄ FF[N] c ∈ P.toValuationSubring.nonunits := by
          have := nonunits_neg P hc
          rwa [h0, inv_zero, zero_sub, neg_neg] at this
        exact hc0 ((algebraMap_mem_nonunits_iff P c).mp h2)
      have hkey : jB[N] - algebraMap ℚ̄ FF[N] c⁻¹ =
          (-(jB[N] * algebraMap ℚ̄ FF[N] c⁻¹)) * ((jB[N])⁻¹ - algebraMap ℚ̄ FF[N] c) := by
        rw [map_inv₀]
        calc jB[N] - (algebraMap ℚ̄ FF[N] c)⁻¹
            = -(algebraMap ℚ̄ FF[N] c)⁻¹ * 1 + jB[N] * 1 := by ring
          _ = -(algebraMap ℚ̄ FF[N] c)⁻¹ * (jB[N] * (jB[N])⁻¹) +
                jB[N] * ((algebraMap ℚ̄ FF[N] c)⁻¹ * algebraMap ℚ̄ FF[N] c) := by
              rw [mul_inv_cancel₀ hj0, inv_mul_cancel₀ hc0']
          _ = _ := by ring
      have hmem : jB[N] - algebraMap ℚ̄ FF[N] ((⟨c⁻¹, hcinv⟩ : A) : ℚ̄) ∈
          P.toValuationSubring.nonunits := by
        show jB[N] - algebraMap ℚ̄ FF[N] c⁻¹ ∈ _
        rw [hkey]
        exact nonunits_mul_left P (neg_mem (mul_mem hjP (P.algebraMap_mem' _))) hc
      have h3 := (nonunits_iff_ord_pos P (jB_sub_ne_zero hintj hresj ⟨c⁻¹, hcinv⟩)).mp hmem
      exact absurd (hpole ⟨c⁻¹, hcinv⟩) (not_le.mpr h3)
  obtain ⟨Qs, hQs, huniq⟩ := engine_inf hℓN fm hR cc dataAll hsep hinti hresi P hP
  have hj₁ : (jC[A,N])⁻¹ ∈ Qs.toValuationSubring :=
    hresi ▸ residue_mem_of_compat R ⟨(jB[N])⁻¹, hinti⟩ P Qs hQs hP
  have hj₂ : (jC[A,N])⁻¹ ∈
      (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P).toValuationSubring :=
    fm.jLineInv_mem_spPlace Ideal.Quotient.mk_surjective dataAll hsep P hpole
  have hInf : ∀ b : fm.BInf, (fm.piInf b : CC[A,N]) ∈ Qs.toValuationSubring.nonunits ↔
      (fm.piInf b : CC[A,N]) ∈
        (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P).toValuationSubring.nonunits := by
    intro b
    rw [fm.piInf_mem_spPlace_nonunits_iff Ideal.Quotient.mk_surjective dataAll hsep P hpole b]
    obtain ⟨hintb, hresb⟩ := residue_BInf fm hR cc dataAll hsep b
    rw [← hresb]
    constructor
    · intro hres
      have hbP : (b : FF[N]) ∈ P.toValuationSubring :=
        Place.mem_toValuationSubring_of_isIntegral_adjoin P hinvP (isIntegral_BInf fm b)
      obtain ⟨a', ha'0, ha'⟩ := exists_sub_mem_nonunits_of_residue_mem_nonunits R
        ⟨(jB[N])⁻¹, hinti⟩ P Qs hQs ⟨b, hintb⟩ (isIntegral_BInf fm b) hbP hres
      exact ⟨a', (IsLocalRing.residue_eq_zero_iff _).mp ha'0, ha'⟩
    · rintro ⟨a', ha'm, ha'⟩
      exact residue_mem_nonunits_of_sub_mem_nonunits R ⟨(jB[N])⁻¹, hinti⟩ P Qs hQs ⟨b, hintb⟩
        (isIntegral_BInf fm b) a' ((IsLocalRing.residue_eq_zero_iff _).mpr ha'm) ha'
  have hEq : Qs = fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P :=
    FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff N ℓ A kk[A] (IsLocalRing.residue A) fm
      Ideal.Quotient.mk_surjective dataAll hsep Qs _ hj₁ hj₂ hInf
  exact ⟨hP, hEq ▸ hQs, fun Q hQ => (huniq Q hQ).trans hEq⟩

omit [Fact ℓ.Prime] [CharP (IsLocalRing.ResidueField A) ℓ] hℓN in
theorem jC_ne_zero : jC[A,N] ≠ 0 := fun h =>
  transcendental_jC (N := N) (A := A) (h ▸ isAlgebraic_zero)

omit hℓN in
theorem jB_ne_zero (hintj : jB[N] ∈ R.integers) (hresj : R.residue ⟨jB[N], hintj⟩ = jC[A,N]) :
    jB[N] ≠ 0 := by
  simpa using jB_sub_ne_zero hintj hresj (0 : A)

omit hℓN in

theorem fin_chart_of_spPlace_eq (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom kk[A]))).map
      (algebraMap (Polynomial kk[A]) (RatFunc kk[A]))).Separable)
    (hintj : jB[N] ∈ R.integers) (hresj : R.residue ⟨jB[N], hintj⟩ = jC[A,N])
    (P : Place ℚ̄ FF[N]) (Q : Place kk[A] CC[A,N]) (hQj : jC[A,N] ∈ Q.toValuationSubring)
    (hPQ : fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P = Q) :
    ∃ a : A, jB[N] - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits := by
  by_contra hno
  push Not at hno
  have hpole : ∀ a : A, P.ord (jB[N] - algebraMap ℚ̄ FF[N] (a : ℚ̄)) ≤ 0 := fun a =>
    not_lt.mp fun h => hno a ((nonunits_iff_ord_pos P (jB_sub_ne_zero hintj hresj a)).mpr h)
  have h := FibreModel.spPlace_d0_j_pole N A ℓ kk[A] (IsLocalRing.residue A) fm
    Ideal.Quotient.mk_surjective dataAll hsep P hpole
  rw [hPQ] at h
  have h0 : 0 ≤ Q.ord jC[A,N] := (placeMemIffOrdNonneg Q jC_ne_zero).mp hQj
  omega

omit hℓN in

theorem pole_chart_of_spPlace_eq (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom kk[A]))).map
      (algebraMap (Polynomial kk[A]) (RatFunc kk[A]))).Separable)
    (P : Place ℚ̄ FF[N]) (Q : Place kk[A] CC[A,N]) (hQj : jC[A,N] ∉ Q.toValuationSubring)
    (hPQ : fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P = Q) :
    ∀ a : A, P.ord (jB[N] - algebraMap ℚ̄ FF[N] (a : ℚ̄)) ≤ 0 := by
  intro a
  by_contra hlt
  push Not at hlt
  have h2 := FibreModel.spPlace_d0_j N A ℓ kk[A] (IsLocalRing.residue A) fm
    Ideal.Quotient.mk_surjective dataAll hsep P a hlt
  have hmem : jC[A,N] - algebraMap kk[A] CC[A,N] (IsLocalRing.residue A a) ∈
      (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P).toValuationSubring :=
    (placeMemIffOrdNonneg _ (jC_sub_algebraMap_ne_zero _)).mpr h2.le
  have := add_mem hmem ((fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep P).algebraMap_mem'
    (IsLocalRing.residue A a))
  rw [sub_add_cancel, hPQ] at this
  exact hQj this

omit hℓN in

theorem pole_of_compat_inf
    (hinti : (jB[N])⁻¹ ∈ R.integers) (hresi : R.residue ⟨(jB[N])⁻¹, hinti⟩ = (jC[A,N])⁻¹)
    (hintj : jB[N] ∈ R.integers) (hresj : R.residue ⟨jB[N], hintj⟩ = jC[A,N])
    (P : Place ℚ̄ FF[N]) (Q : Place kk[A] CC[A,N])
    (hQi : (jC[A,N])⁻¹ ∈ Q.toValuationSubring.nonunits)
    (hP : ∃ a : A, (jB[N])⁻¹ - algebraMap ℚ̄ FF[N] a ∈ P.toValuationSubring.nonunits)
    (hc : Compat A R ⟨(jB[N])⁻¹, hinti⟩ P Q) :
    ∀ a : A, P.ord (jB[N] - algebraMap ℚ̄ FF[N] (a : ℚ̄)) ≤ 0 := by
  intro a'
  by_contra hlt
  push Not at hlt
  have ha' : jB[N] - algebraMap ℚ̄ FF[N] (a' : ℚ̄) ∈ P.toValuationSubring.nonunits :=
    (nonunits_iff_ord_pos P (jB_sub_ne_zero hintj hresj a')).mpr hlt
  obtain ⟨a, ha⟩ := hP
  have hres : R.residue ⟨(jB[N])⁻¹, hinti⟩ -
      algebraMap kk[A] CC[A,N] (IsLocalRing.residue A a) ∈ Q.toValuationSubring.nonunits :=
    hc ⟨(jB[N])⁻¹, hinti⟩ (isIntegral_adjoin_self _) a ha
  rw [hresi] at hres
  have hra : algebraMap kk[A] CC[A,N] (IsLocalRing.residue A a) ∈
      Q.toValuationSubring.nonunits := by
    have := nonunits_sub Q hQi hres
    rwa [sub_sub_cancel] at this
  have hra0 : IsLocalRing.residue A a = 0 := (algebraMap_mem_nonunits_iff Q _).mp hra
  have hjiP : (jB[N])⁻¹ ∈ P.toValuationSubring := jB_inv_mem_of_chart ⟨a, ha⟩
  have hj0 := jB_ne_zero hintj hresj
  have hkey : (jB[N] - algebraMap ℚ̄ FF[N] (a' : ℚ̄)) * (jB[N])⁻¹ +
      algebraMap ℚ̄ FF[N] (a' : ℚ̄) * ((jB[N])⁻¹ - algebraMap ℚ̄ FF[N] (a : ℚ̄)) =
        algebraMap ℚ̄ FF[N] (1 - (a' : ℚ̄) * a) := by
    rw [map_sub, map_one, map_mul, ← mul_inv_cancel₀ hj0]; ring
  have hmem : algebraMap ℚ̄ FF[N] (1 - (a' : ℚ̄) * a) ∈ P.toValuationSubring.nonunits := by
    rw [← hkey]
    refine nonunits_add P ?_ (nonunits_mul_left P (P.algebraMap_mem' _) ha)
    rw [mul_comm]
    exact nonunits_mul_left P hjiP ha'
  have h10 : (1 : ℚ̄) - a' * a = 0 := (algebraMap_mem_nonunits_iff P _).mp hmem
  have hA : (1 : A) - a' * a = 0 := Subtype.ext (by simpa using h10)
  have := congrArg (IsLocalRing.residue A) hA
  rw [map_sub, map_one, map_mul, hra0, mul_zero, sub_zero, map_zero] at this
  exact one_ne_zero this

omit [NeZero N] [Fact ℓ.Prime] [CharP (IsLocalRing.ResidueField A) ℓ] hℓN in

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (f : α → β) (D : α →₀ ℤ)
    (b : β) : Finsupp.mapDomain f D b = ∑ a ∈ D.support.filter (fun a => f a = b), D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finsupp.single_apply]

theorem final (fm : FibreModel N A ℓ kk[A] (IsLocalRing.residue A)) (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom kk[A]))).map
      (algebraMap (Polynomial kk[A]) (RatFunc kk[A]))).Separable)
    (hR : QExp N A R)
    (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF[N])
    (hyk : coeffMap (IsLocalRing.residue A) y ∈ CC[A,N])
    (hne : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (D : Divisor ℚ̄ FF[N]) (hD : ∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : FF[N]))
    (Q : Place kk[A] CC[A,N]) :
    Finsupp.mapDomain (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep) D Q =
      Q.ord (⟨coeffMap (IsLocalRing.residue A) y, hyk⟩ : CC[A,N]) := by
  classical

  obtain ⟨hintj, hresj⟩ := residue_BFin fm hR ⟨jB[N], fm.jBar_mem⟩
  have hresj' : R.residue ⟨jB[N], hintj⟩ = jC[A,N] := hresj.trans fm.piFin_j
  obtain ⟨hinti, hresi⟩ := residue_BInf fm hR cc dataAll hsep ⟨(jB[N])⁻¹, fm.jInvBar_mem⟩
  have hresi' : R.residue ⟨(jB[N])⁻¹, hinti⟩ = (jC[A,N])⁻¹ := hresi.trans fm.piInf_jInv

  have hg : ((⟨coeffMap A.subtype y, hy⟩ : FF[N]) : LaurentSeries ℚ̄) ∈
      integralCoeffs A.toSubring := fun n => (y.coeff n).2
  obtain ⟨hintf, hresf⟩ := hR ⟨coeffMap A.subtype y, hy⟩ hg
  have hresf' : R.residue ⟨⟨coeffMap A.subtype y, hy⟩, hintf⟩ =
      (⟨coeffMap (IsLocalRing.residue A) y, hyk⟩ : CC[A,N]) := by
    apply Subtype.ext
    rw [hresf]
    ext n
    rfl
  have hf : R.residue ⟨⟨coeffMap A.subtype y, hy⟩, hintf⟩ ≠ 0 := by
    rw [hresf']
    intro h
    exact hne (by simpa using congrArg Subtype.val h)
  have hD' : ∀ P, D P = P.ord (((⟨⟨coeffMap A.subtype y, hy⟩, hintf⟩ : R.integers)) : FF[N]) :=
    hD
  rw [mapDomain_apply_eq_sum, ← hresf']
  by_cases hQj : jC[A,N] ∈ Q.toValuationSubring
  ·
    refine sum_fin hℓN fm hR hintj hresj' _ hf Q hQj D hD' _ (fun P => ?_)
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨hDP, hPQ⟩
      have hP := fin_chart_of_spPlace_eq fm dataAll hsep hintj hresj' P Q hQj hPQ
      exact ⟨hDP, hP, hPQ ▸ (compat_spPlace_fin hℓN fm hR dataAll hsep hintj hresj' P hP).1⟩
    · rintro ⟨hDP, hP, hc⟩
      exact ⟨hDP, ((compat_spPlace_fin hℓN fm hR dataAll hsep hintj hresj' P hP).2 Q hc).symm⟩
  ·
    have hQi : (jC[A,N])⁻¹ ∈ Q.toValuationSubring.nonunits := inv_mem_nonunits_of_not_mem Q hQj
    refine sum_inf hℓN fm hR cc dataAll hsep hinti hresi' _ hf Q (mem_of_mem_nonunits Q hQi) D
      hD' _ (fun P => ?_)
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨hDP, hPQ⟩
      have hpole := pole_chart_of_spPlace_eq fm dataAll hsep P Q hQj hPQ
      obtain ⟨hP, hc, -⟩ :=
        compat_spPlace_inf hℓN fm hR cc dataAll hsep hinti hresi' hintj hresj' P hpole
      exact ⟨hDP, hP, hPQ ▸ hc⟩
    · rintro ⟨hDP, hP, hc⟩
      have hpole := pole_of_compat_inf hinti hresi' hintj hresj' P Q hQi hP hc
      exact ⟨hDP, ((compat_spPlace_inf hℓN fm hR cc dataAll hsep hinti hresi' hintj hresj' P
        hpole).2.2 Q hc).symm⟩

end Core

end P2mSolD260

end

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (hℓN : ¬ ℓ ∣ N)
    (fm : ModularCurve.CharPModel.FibreModel N A ℓ (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A))
    (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A)) (RatFunc (IsLocalRing.ResidueField A)))).Separable)
    (y : LaurentSeries A)
    (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar N)
    (hyk : ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
      ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N)
    (hne : ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0)
    (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N))
    (hD : ∀ P, D P = P.ord (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
      ModularCurve.modularFunctionFieldBar N))
    (Q : AlgebraicCurve.Place (IsLocalRing.ResidueField A)
      (ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N)) :
    Finsupp.mapDomain (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep) D Q =
      Q.ord (⟨ModularCurve.coeffMap (IsLocalRing.residue A) y, hyk⟩ :
        ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField A) N) := by
  obtain ⟨R, hR⟩ := P2mSolD260.exists_prolongation N ℓ A hℓN
  exact P2mSolD260.final hℓN fm cc dataAll hsep hR y hy hyk hne D hD Q

end S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_eq_ord_coeffMap
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_eq_ord_coeffMap (solution)
