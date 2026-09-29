-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integralOverPoleChart_of_mem_integers_of_forall_inv_mem_imp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/16291985-2a0a-5585-81dd-b6c1703291a4

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHCuspChartSet
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_iff_gauss
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_monic_coeff_natDegree_le_of_forall_valuationSubring
import Theorems.Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_mem_toValuationSubring
import Theorems.Thm_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integralOverPoleChart_of_mem_integers_of_forall_inv_mem_imp_mem
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

namespace GaussCuspH

namespace GaussPoles
open Polynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_monic_eval_eq_zero (V : ValuationSubring F) {Q : F[X]} (hQ : Q.Monic)
    (hc : ∀ i, Q.coeff i ∈ V) {u : F} (hu : Q.eval u = 0) : u ∈ V := by
  by_contra hnot
  have hinv : u⁻¹ ∈ V := (V.mem_or_inv_mem u).resolve_left hnot
  have hu0 : u ≠ 0 := fun h => hnot (h ▸ zero_mem V)
  have hQ0 : Q.natDegree ≠ 0 := fun h0 => by
    have hc : Q.coeff 0 = 1 := by
      have := hQ.coeff_natDegree
      rwa [h0] at this
    have h1 : Q = 1 := by
      rw [eq_C_of_natDegree_eq_zero h0, hc, C_1]
    rw [h1, eval_one] at hu
    exact one_ne_zero hu
  obtain ⟨n, hn⟩ : ∃ n, Q.natDegree = n + 1 := Nat.exists_eq_add_one_of_ne_zero hQ0
  rw [eval_eq_sum_range, hn, Finset.sum_range_succ, ← hn, hQ.coeff_natDegree, one_mul, hn] at hu

  have key : u = -(∑ i ∈ Finset.range (n + 1), Q.coeff i * u⁻¹ ^ (n - i)) := by
    have h2 : u ^ (n + 1) = -(∑ i ∈ Finset.range (n + 1), Q.coeff i * u ^ i) :=
      eq_neg_of_add_eq_zero_right hu
    have h3 : u = u ^ (n + 1) * u⁻¹ ^ n := by
      rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ hu0, one_pow, mul_one]
    conv_lhs => rw [h3]
    rw [h2, neg_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [mul_assoc]
    congr 1
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi'
    rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu0, one_pow, one_mul]
  apply hnot
  rw [key]
  exact neg_mem (sum_mem fun i _ => mul_mem (hc i) (pow_mem hinv _))

theorem mem_of_mem_adjoin (V : ValuationSubring F) (hK : ∀ a : K, algebraMap K F a ∈ V) {x : F}
    (hx : x ∈ V) {c : F} (hc : c ∈ Algebra.adjoin K ({x} : Set F)) : c ∈ V := by
  let S : Subalgebra K F :=
    { V.toSubring.toSubsemiring with
      algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({x} : Set F) ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hx)
  exact hle hc

theorem exists_forall_mul_inv_pow_mem {x : F} {c : F} (hc : c ∈ Algebra.adjoin K ({x} : Set F)) :
    ∃ d : ℕ, ∀ V : ValuationSubring F, (∀ a : K, algebraMap K F a ∈ V) → x ∉ V →
      ∀ e : ℕ, d ≤ e → c * x⁻¹ ^ e ∈ V := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hc
  obtain ⟨q, rfl⟩ := hc
  refine ⟨q.natDegree, fun V hK hxV e hde => ?_⟩
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ zero_mem V)
  have hxinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  rw [aeval_eq_sum_range, Finset.sum_mul]
  refine sum_mem fun i hi => ?_
  have hi' : i ≤ e := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hde
  obtain ⟨d', hd'⟩ := Nat.exists_eq_add_of_le hi'
  rw [Algebra.smul_def, mul_assoc, hd', pow_add, ← mul_assoc (x ^ i), ← mul_pow, mul_inv_cancel₀ hx0, one_pow,
    one_mul]
  exact mul_mem (hK _) (pow_mem hxinv _)

variable (K) in

theorem forall_mem_and_exists_forall_mul_inv_pow_mem {x t : F}
    (ht : IsIntegral (Algebra.adjoin K ({x} : Set F)) t) :
    (∀ V : ValuationSubring F, (∀ a : K, algebraMap K F a ∈ V) → x ∈ V → t ∈ V) ∧
    ∃ m : ℕ, ∀ V : ValuationSubring F, (∀ a : K, algebraMap K F a ∈ V) → x ∉ V → t * (x ^ m)⁻¹ ∈ V := by
  obtain ⟨p, hpm, hpe⟩ := ht

  set P : F[X] := p.map (algebraMap (Algebra.adjoin K ({x} : Set F)) F) with hP_def
  have hPm : P.Monic := hpm.map _
  have hPe : P.eval t = 0 := by rw [hP_def, eval_map]; exact hpe
  have hPc : ∀ i, P.coeff i ∈ Algebra.adjoin K ({x} : Set F) := by
    intro i
    rw [hP_def, coeff_map]
    exact (p.coeff i).2
  refine ⟨fun V hK hxV => mem_of_monic_eval_eq_zero V hPm (fun i => mem_of_mem_adjoin V hK hxV (hPc i)) hPe, ?_⟩

  choose dOf hdOf using fun i => exists_forall_mul_inv_pow_mem (K := K) (hPc i)
  refine ⟨(Finset.range (P.natDegree + 1)).sup dOf, fun V hK hxV => ?_⟩
  set m : ℕ := (Finset.range (P.natDegree + 1)).sup dOf with hm_def
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ zero_mem V)
  have hxinv : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV

  have hroot : (P.scaleRoots (x⁻¹ ^ m)).eval (x⁻¹ ^ m * t) = 0 := by
    have h := scaleRoots_eval₂_eq_zero (RingHom.id F) (s := x⁻¹ ^ m) (by rw [eval₂_id]; exact hPe)
    rw [eval₂_id] at h
    simpa using h
  have hcoeff : ∀ i, (P.scaleRoots (x⁻¹ ^ m)).coeff i ∈ V := by
    intro i
    rw [coeff_scaleRoots, ← pow_mul]
    by_cases hi : i ≤ P.natDegree
    · rcases eq_or_lt_of_le hi with rfl | hlt
      · rw [Nat.sub_self, mul_zero, pow_zero, mul_one, hPm.coeff_natDegree]
        exact one_mem V
      · apply hdOf i V hK hxV
        have h1 : dOf i ≤ m := Finset.le_sup (f := dOf) (Finset.mem_range.mpr (Nat.lt_succ_of_lt hlt))
        have h2 : 1 ≤ P.natDegree - i := Nat.sub_pos_of_lt hlt
        calc dOf i ≤ m := h1
          _ = m * 1 := (mul_one m).symm
          _ ≤ m * (P.natDegree - i) := Nat.mul_le_mul_left m h2
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), zero_mul]
      exact zero_mem V
  have hmem := mem_of_monic_eval_eq_zero V ((monic_scaleRoots_iff (x⁻¹ ^ m)).mpr hPm) hcoeff hroot
  rw [inv_pow, mul_comm] at hmem
  exact hmem

end GaussPoles

section Generic

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem inv_mem_integers (R : RegularProlongation A F Fb) {x : F} (hx : x ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨x, hx⟩)) : x⁻¹ ∈ R.integers := by
  have hne : R.residue ⟨x, hx⟩ ≠ 0 := fun h0 => htr (by rw [h0]; exact isAlgebraic_zero)
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hne
  have hmul : x * (((u⁻¹ : R.integersˣ) : R.integers) : F) = 1 := by
    have h1 := u.mul_inv
    rw [hu] at h1
    exact congrArg Subtype.val h1
  rw [← eq_inv_of_mul_eq_one_right hmul]
  exact ((u⁻¹ : R.integersˣ) : R.integers).2

theorem residue_inv (R : RegularProlongation A F Fb) {x : F} (hx : x ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨x, hx⟩)) :
    R.residue ⟨x⁻¹, inv_mem_integers R hx htr⟩ = (R.residue ⟨x, hx⟩)⁻¹ := by
  have hne : R.residue ⟨x, hx⟩ ≠ 0 := fun h0 => htr (by rw [h0]; exact isAlgebraic_zero)
  have hx0 : x ≠ 0 := by
    intro h0
    apply hne
    have h1 : (⟨x, hx⟩ : R.integers) = 0 := Subtype.ext h0
    rw [h1, map_zero]
  have hprod : (⟨x, hx⟩ : R.integers) * ⟨x⁻¹, inv_mem_integers R hx htr⟩ = 1 :=
    Subtype.ext (mul_inv_cancel₀ hx0)
  have h2 := congrArg R.residue hprod
  rw [map_mul, map_one] at h2
  exact eq_inv_of_mul_eq_one_right h2

theorem transcendental_residue_inv (R : RegularProlongation A F Fb) {x : F} (hx : x ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨x, hx⟩)) :
    Transcendental (ResidueField A) (R.residue ⟨x⁻¹, inv_mem_integers R hx htr⟩) := by
  rw [residue_inv R hx htr]
  exact fun h => htr (IsAlgebraic.inv_iff.mp h)

theorem adjoin_inv_eq {K E : Type*} [Field K] [Field E] [Algebra K E] (x : E) :
    IntermediateField.adjoin K ({x⁻¹} : Set E) = IntermediateField.adjoin K ({x} : Set E) := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (inv_mem (IntermediateField.mem_adjoin_simple_self K x))
  · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
    have h := inv_mem (IntermediateField.mem_adjoin_simple_self K x⁻¹)
    rwa [inv_inv] at h

theorem exists_monic_eval₂_inv_eq_zero (R : RegularProlongation A F Fb) {x : F} (hxO : x ∈ R.integers)
    (htr : Transcendental (ResidueField A) (R.residue ⟨x, hxO⟩))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue ⟨x, hxO⟩} : Set Fb)) Fb)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({x} : Set F)) F =
      Module.finrank (IntermediateField.adjoin (ResidueField A) ({R.residue ⟨x, hxO⟩} : Set Fb)) Fb)
    (t : F) (htO : t ∈ R.integers) (hint : IsIntegral (Algebra.adjoin L ({x⁻¹} : Set F)) t) :
    ∃ P : Polynomial (Polynomial A), P.Monic ∧
      P.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) x⁻¹) t = 0 := by

  have hxI : x⁻¹ ∈ R.integers := inv_mem_integers R hxO htr
  have hresI : R.residue ⟨x⁻¹, hxI⟩ = (R.residue ⟨x, hxO⟩)⁻¹ := residue_inv R hxO htr
  have htrI : Transcendental (ResidueField A) (R.residue ⟨x⁻¹, hxI⟩) := transcendental_residue_inv R hxO htr
  have hfinI : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue ⟨x⁻¹, hxI⟩} : Set Fb)) Fb := by
    rw [hresI, adjoin_inv_eq]
    exact hfin
  have hdegI : Module.finrank (IntermediateField.adjoin L ({((⟨x⁻¹, hxI⟩ : R.integers) : F)} : Set F)) F =
      Module.finrank (IntermediateField.adjoin (ResidueField A) ({R.residue ⟨x⁻¹, hxI⟩} : Set Fb)) Fb := by
    rw [show ((⟨x⁻¹, hxI⟩ : R.integers) : F) = x⁻¹ from rfl, adjoin_inv_eq, hresI, adjoin_inv_eq]
    exact hdeg

  obtain ⟨h1, m, h2⟩ := GaussPoles.forall_mem_and_exists_forall_mul_inv_pow_mem L hint

  have h3 : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L ({((⟨x⁻¹, hxI⟩ : R.integers) : F)} : Set F) →
        (e ∈ V ↔ e ∈ R.integers)) → t ∈ V := by
    intro V hV
    rw [RegularProlongation.eq_integers_of_forall_mem_adjoin_iff A R ⟨x⁻¹, hxI⟩ htrI hfinI hdegI V hV]
    exact htO
  obtain ⟨P, hPm, -, hP0⟩ :=
    RegularProlongation.exists_monic_coeff_natDegree_le_of_forall_valuationSubring A R ⟨x⁻¹, hxI⟩ htrI t m
      h1 h2 h3
  exact ⟨P, hPm, hP0⟩

theorem isIntegral_adjoin_of_exists_monic (y t : F)
    (h : ∃ P : Polynomial (Polynomial A), P.Monic ∧
      P.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) y) t = 0) :
    letI : Algebra ↥A F := ((algebraMap L F).comp A.subtype).toAlgebra
    IsIntegral ↥(Algebra.adjoin ↥A ({y} : Set F)) t := by
  letI : Algebra ↥A F := ((algebraMap L F).comp A.subtype).toAlgebra
  obtain ⟨P, hPm, hP0⟩ := h
  set B : Subalgebra ↥A F := Algebra.adjoin ↥A ({y} : Set F) with hB
  have hyB : y ∈ B := Algebra.self_mem_adjoin_singleton ↥A y
  let φ : Polynomial ↥A →+* ↥B := Polynomial.eval₂RingHom (algebraMap ↥A ↥B) ⟨y, hyB⟩
  have hφ : (B.val : ↥B →+* F).comp φ = Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) y := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rfl
    · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  refine ⟨P.map φ, hPm.map _, ?_⟩
  rw [Polynomial.eval₂_map, show (algebraMap ↥B F) = (B.val : ↥B →+* F) from rfl, hφ]
  exact hP0

end Generic

section Served

set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_gauss (N : ℕ) (H : Subgroup (ZMod N)ˣ) (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ∃ R : RegularProlongation A ↥(xHFunctionFieldBar N H)
        ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H)),
      (∀ f : ↥(xHFunctionFieldBar N H), f ∈ R.integers ↔
          ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
            (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar N H),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar N H)) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H))) :
              LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y :=
  ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) A
    (CohCarrier.GammaH N H) (translation_mem_GammaH N H)

set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_jBar (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ∃ x : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H)),
      (x : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) ∧
      Transcendental (ResidueField ↥A) x ∧
      FiniteDimensional
        (IntermediateField.adjoin (ResidueField ↥A)
          ({x} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H))))
        ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H)) ∧
      ∀ (y : ↥(xHFunctionFieldBar N H)),
        (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
        Module.finrank
            (IntermediateField.adjoin (ResidueField ↥A)
              ({x} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H))))
            ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H)) ≤
          Module.finrank
            (IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥(xHFunctionFieldBar N H)))
            ↥(xHFunctionFieldBar N H) :=
  haveI : (CohCarrier.GammaH N H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH N H)
  ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
    (AlgebraicClosure ℚ) A (CohCarrier.GammaH N H) (translation_mem_GammaH N H)

set_option synthInstance.maxHeartbeats 1600000 in

theorem finrank_le (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (x : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H)))
    (y : ↥(xHFunctionFieldBar N H))
    (hx : (x : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set ↥(xHFunctionFieldBar N H)))
        ↥(xHFunctionFieldBar N H) ≤
      Module.finrank
        (IntermediateField.adjoin (ResidueField ↥A)
          ({x} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H))))
        ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H)) :=
  ModularCurve.finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd N H hℓN A hA x y hx hy

end Served

section Main

variable {L : Type*}

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem main (p N : ℕ) [Fact p.Prime] [NeZero N] (H : Subgroup (ZMod N)ˣ) (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (x' : ↥(xHFunctionFieldBar N H))
    (hx' : (x' : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (ψ : ↥(xHFunctionFieldBar N H))
    (hψ : ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      (ψ : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar N H),
      x'⁻¹ ∈ u₀.toValuationSubring → ψ ∈ u₀.toValuationSubring) :
    ∃ P : Polynomial (Polynomial ↥A), P.Monic ∧
      P.eval₂ (Polynomial.eval₂RingHom
        ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar N H)).comp A.subtype) x'⁻¹) ψ = 0 := by

  obtain ⟨R, hRiff, hRspec⟩ := exists_gauss N H A

  have hψO : ψ ∈ R.integers := (hRiff ψ).mpr hψ

  have hser : coeffMap A.subtype (jqModC ↥A) = (x' : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hx']
    exact map_jqModC A.subtype
  have hmem : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar N H := by
    rw [hser]; exact x'.2
  obtain ⟨hint0, hres0⟩ := hRspec (jqModC ↥A) hmem
  have hxeq : (⟨coeffMap A.subtype (jqModC ↥A), hmem⟩ : ↥(xHFunctionFieldBar N H)) = x' :=
    Subtype.ext hser
  have hjO : x' ∈ R.integers := by rw [← hxeq]; exact hint0
  have hresx : ((R.residue ⟨x', hjO⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H))) :
      LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
    have h1 : (⟨x', hjO⟩ : R.integers) = ⟨⟨coeffMap A.subtype (jqModC ↥A), hmem⟩, hint0⟩ :=
      Subtype.ext hxeq.symm
    rw [h1, hres0]
    exact map_jqModC (IsLocalRing.residue ↥A)

  obtain ⟨xb, hxb, hxbtr, hxbfd, hxble⟩ := exists_jBar N H A
  have hres_eq : R.residue ⟨x', hjO⟩ = xb := Subtype.ext (hresx.trans hxb.symm)
  have htr : Transcendental (ResidueField ↥A) (R.residue ⟨x', hjO⟩) := by
    rw [hres_eq]; exact hxbtr
  haveI := hxbfd
  have hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField ↥A)
        ({R.residue ⟨x', hjO⟩} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H))))
      ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H)) := by
    rw [hres_eq]; exact Module.finrank_pos
  have hdeg : Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'} : Set ↥(xHFunctionFieldBar N H)))
        ↥(xHFunctionFieldBar N H) =
      Module.finrank
        (IntermediateField.adjoin (ResidueField ↥A)
          ({R.residue ⟨x', hjO⟩} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H))))
        ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H)) := by
    rw [hres_eq]
    exact le_antisymm (finrank_le N H hpN A hA xb x' hxb hx') (hxble x' hx')

  have hdegI : Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'⁻¹} : Set ↥(xHFunctionFieldBar N H)))
        ↥(xHFunctionFieldBar N H) =
      Module.finrank
        (IntermediateField.adjoin (ResidueField ↥A)
          ({R.residue ⟨x', hjO⟩} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H))))
        ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH N H)) := by
    rw [adjoin_inv_eq]; exact hdeg
  haveI : FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'⁻¹} : Set ↥(xHFunctionFieldBar N H)))
      ↥(xHFunctionFieldBar N H) :=
    Module.finite_of_finrank_pos (by rw [hdegI]; exact hfin)
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x'⁻¹} : Set ↥(xHFunctionFieldBar N H)))
      ↥(xHFunctionFieldBar N H) :=
    Algebra.IsSeparable.of_integral _ _
  have hint : IsIntegral
      (Algebra.adjoin (AlgebraicClosure ℚ) ({x'⁻¹} : Set ↥(xHFunctionFieldBar N H))) ψ :=
    isIntegral_adjoin_of_forall_mem_toValuationSubring x'⁻¹ x'⁻¹ ψ hreg

  exact exists_monic_eval₂_inv_eq_zero R hjO htr hfin hdeg ψ hψO hint

end Main

end GaussCuspH

open GaussCuspH in
set_option linter.unusedVariables false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (ψ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hψ : α ψ ∈ Rpd.R₁.integers)
    (hreg : ∀ u₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), x'⁻¹ ∈ u₀.toValuationSubring → ψ ∈ u₀.toValuationSubring) :
    ψ ∈ (JHPlaceSpecialization.integralOverPoleChart (p := p) A x') := by

  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    have hM : p * (M / p) = M := Nat.mul_div_cancel' hpM
    rw [pow_two, ← hM]
    exact Nat.mul_dvd_mul_left p h

  have hψ' := (JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss p M H hpM hpM2 hHp A hA θ Psp
    Rpd (α ψ)).mp hψ
  obtain ⟨xs, ys, hys, hxy⟩ := hψ'
  rw [hα_coe] at hxy

  have hmain := GaussCuspH.main p (M / p) (infSubgroup p M H hpM) hpN A hA x' hx' ψ ⟨xs, ys, hys, hxy⟩ hreg

  letI : Algebra ↥A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))).comp
      A.subtype).toAlgebra
  show IsIntegral
    ↥(Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))) ψ
  exact isIntegral_adjoin_of_exists_monic x'⁻¹ ψ hmain

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integralOverPoleChart_of_mem_integers_of_forall_inv_mem_imp_mem
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integralOverPoleChart_of_mem_integers_of_forall_inv_mem_imp_mem (solution)
