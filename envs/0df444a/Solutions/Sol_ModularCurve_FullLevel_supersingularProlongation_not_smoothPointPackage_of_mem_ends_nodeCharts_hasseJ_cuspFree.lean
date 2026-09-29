-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_not_smoothPointPackage_of_mem_ends_nodeCharts_hasseJ_cuspFree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/abb94367-e5b1-5514-b148-080dc72aeb1e

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_FullLevel_supersingularProlongation_exists_annulusPair_of_nodePresentation
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_FullLevel_not_smoothPointPackage_of_annulusPair_attached_igusaEnd_of_testFunction_fullLevel
import Theorems.Thm_ModularCurve_FullLevel_ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_not_smoothPointPackage_of_mem_ends_nodeCharts_hasseJ_cuspFree
p2m_attr_erase "instance" "AlgebraicCurve.GaussReduction.isLocalHom_constToGauss AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instTopologicallyFGOfFiniteType AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace Ws33
namespace Strip

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) (hne : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hunit : IsUnit (⟨f, hf⟩ : ↥v.toValuationSubring) := by
    by_contra hnu
    apply hne
    have hmax : (⟨f, hf⟩ : ↥v.toValuationSubring) ∈ maximalIdeal ↥v.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h0 : IsLocalRing.residue ↥v.toValuationSubring ⟨f, hf⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmax
    rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]
  obtain ⟨w, hw⟩ := hunit
  rw [show f = ((w : ↥v.toValuationSubring) : F) from congrArg Subtype.val hw.symm]
  exact v.ord_coe_unit w

theorem evalAt_sub_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply Place.algebraMap_residueField_injective v
  rw [map_sub, Place.algebraMap_evalAt v hv hf, Place.algebraMap_evalAt v hv hg,
    Place.algebraMap_evalAt v hv (sub_mem hf hg), ← map_sub]
  rfl

theorem ord_finset_prod (v : Place K F) {ι : Type*} (s : Finset ι) (g : ι → F) (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Place.ord_mul _ (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

theorem prod_mem_valuationSubring (v : Place K F) {ι : Type*} (s : Finset ι) (g : ι → F)
    (hg : ∀ i ∈ s, g i ∈ v.toValuationSubring) : (∏ i ∈ s, g i) ∈ v.toValuationSubring := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [one_mem]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact mul_mem (hg a (Finset.mem_insert_self a s)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem evalAt_finset_prod_of_mem (v : Place K F) (hv : v.IsRational) {ι : Type*} (s : Finset ι) (g : ι → F)
    (hg : ∀ i ∈ s, g i ∈ v.toValuationSubring) : v.evalAt (∏ i ∈ s, g i) = ∏ i ∈ s, v.evalAt (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Place.evalAt_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      v.evalAt_mul_of_mem hv (hg a (Finset.mem_insert_self a s))
        (prod_mem_valuationSubring v s g fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

theorem evalAt_pow_of_mem (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp [Place.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul_of_mem hv (pow_mem hf n) hf, ih]

end PlaceLemmas

section Annulus

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable (An : Annulus A F)

theorem isRational {P : Place L F} (hP : P ∈ An.dom) : P.IsRational := (An.mem_dom P hP).1
theorem param_mem {P : Place L F} (hP : P ∈ An.dom) : An.param ∈ P.toValuationSubring := (An.mem_dom P hP).2.1
theorem evalAt_param_mem {P : Place L F} (hP : P ∈ An.dom) : P.evalAt An.param ∈ A :=
  (An.mem_dom P hP).2.2.1.elim fun h _ => h
theorem evalAt_param_mem_maximalIdeal {P : Place L F} (hP : P ∈ An.dom) :
    (⟨P.evalAt An.param, evalAt_param_mem An hP⟩ : ↥A) ∈ maximalIdeal ↥A := by
  obtain ⟨h, hm⟩ := (An.mem_dom P hP).2.2.1; exact hm
theorem evalAt_param_ne_zero {P : Place L F} (hP : P ∈ An.dom) : P.evalAt An.param ≠ 0 := (An.mem_dom P hP).2.2.2.1
theorem exists_modulus_eq {P : Place L F} (hP : P ∈ An.dom) :
    ∃ m ∈ maximalIdeal ↥A, ((An.modulus : ↥A) : L) = P.evalAt An.param * m := (An.mem_dom P hP).2.2.2.2

theorem valuation_evalAt_param_lt_one {P : Place L F} (hP : P ∈ An.dom) : A.valuation (P.evalAt An.param) < 1 :=
  (A.valuation_lt_one_iff ⟨_, evalAt_param_mem An hP⟩).mp (evalAt_param_mem_maximalIdeal An hP)

theorem eq_of_evalAt_param_eq {P Q : Place L F} (hP : P ∈ An.dom) (hQ : Q ∈ An.dom)
    (h : P.evalAt An.param = Q.evalAt An.param) : P = Q := by
  obtain ⟨R, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨Q.evalAt An.param, evalAt_param_mem An hQ⟩
    (evalAt_param_mem_maximalIdeal An hQ) (evalAt_param_ne_zero An hQ) (exists_modulus_eq An hQ)
  exact (huniq P ⟨hP, h⟩).trans (huniq Q ⟨hQ, rfl⟩).symm

noncomputable def w (Q : Place L F) : F := An.param - algebraMap L F (Q.evalAt An.param)

theorem w_def (Q : Place L F) : w An Q = An.param - algebraMap L F (Q.evalAt An.param) := rfl

theorem ord_w_self {Q : Place L F} (hQ : Q ∈ An.dom) : Q.ord (w An Q) = 1 := An.ord_param_sub Q hQ

theorem w_ne_zero {Q : Place L F} (hQ : Q ∈ An.dom) : w An Q ≠ 0 := by
  intro h; have := ord_w_self An hQ; rw [h, Place.ord_zero] at this; exact zero_ne_one this

theorem w_mem {P : Place L F} (hP : P ∈ An.dom) (Q : Place L F) : w An Q ∈ P.toValuationSubring :=
  sub_mem (param_mem An hP) (P.algebraMap_mem' _)

theorem evalAt_w {P : Place L F} (hP : P ∈ An.dom) (Q : Place L F) :
    P.evalAt (w An Q) = P.evalAt An.param - Q.evalAt An.param := by
  rw [w_def, evalAt_sub_of_mem P (isRational An hP) (param_mem An hP) (P.algebraMap_mem' _), Place.evalAt_algebraMap_eq]

theorem ord_w_of_ne {P Q : Place L F} (hP : P ∈ An.dom) (hQ : Q ∈ An.dom) (hPQ : P ≠ Q) : P.ord (w An Q) = 0 := by
  apply ord_eq_zero_of_evalAt_ne_zero P (w_mem An hP Q)
  rw [evalAt_w An hP, sub_ne_zero]
  exact fun h => hPQ (eq_of_evalAt_param_eq An hP hQ h)

theorem valuation_evalAt_w {P Q : Place L F} (hP : P ∈ An.dom)
    (hne : A.valuation (P.evalAt An.param) ≠ A.valuation (Q.evalAt An.param)) :
    A.valuation (P.evalAt (w An Q)) = max (A.valuation (P.evalAt An.param)) (A.valuation (Q.evalAt An.param)) := by
  rw [evalAt_w An hP, sub_eq_add_neg, Valuation.map_add_of_distinct_val _ (by rwa [Valuation.map_neg]),
    Valuation.map_neg]

theorem prod_w_zpow_ne_zero (Z : Finset (Place L F)) (hZ : ∀ Q ∈ Z, Q ∈ An.dom) (n : Place L F → ℤ) :
    (∏ Q ∈ Z, w An Q ^ n Q) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun Q hQ => zpow_ne_zero _ (w_ne_zero An (hZ Q hQ))

theorem ord_prod_w_zpow_of_mem (Z : Finset (Place L F)) (hZ : ∀ Q ∈ Z, Q ∈ An.dom) (n : Place L F → ℤ)
    {P : Place L F} (hP : P ∈ An.dom) (hPZ : P ∈ Z) :
    P.ord (∏ Q ∈ Z, w An Q ^ n Q) = n P := by
  classical
  rw [ord_finset_prod P Z _ (fun Q hQ => zpow_ne_zero _ (w_ne_zero An (hZ Q hQ)))]
  simp_rw [Place.ord_zpow]
  rw [Finset.sum_eq_single_of_mem P hPZ (fun Q hQ hQP => by
    rw [ord_w_of_ne An hP (hZ Q hQ) (Ne.symm hQP), mul_zero]), ord_w_self An hP, mul_one]

theorem ord_prod_w_zpow_of_not_mem (Z : Finset (Place L F)) (hZ : ∀ Q ∈ Z, Q ∈ An.dom) (n : Place L F → ℤ)
    {P : Place L F} (hP : P ∈ An.dom) (hPZ : P ∉ Z) :
    P.ord (∏ Q ∈ Z, w An Q ^ n Q) = 0 := by
  classical
  rw [ord_finset_prod P Z _ (fun Q hQ => zpow_ne_zero _ (w_ne_zero An (hZ Q hQ)))]
  simp_rw [Place.ord_zpow]
  exact Finset.sum_eq_zero fun Q hQ => by
    rw [ord_w_of_ne An hP (hZ Q hQ) (fun h => hPZ (h ▸ hQ)), mul_zero]

theorem exists_finset_ord_ne_zero [HasPrincipalDivisors L F] (f : F) (hf : f ≠ 0) :
    ∃ Z : Finset (Place L F), (∀ Q ∈ Z, Q ∈ An.dom) ∧ ∀ P ∈ An.dom, (P ∈ Z ↔ P.ord f ≠ 0) := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf
  refine ⟨D.support.filter (fun Q => Q ∈ An.dom), fun Q hQ => (Finset.mem_filter.mp hQ).2, fun P hP => ?_⟩
  rw [Finset.mem_filter, Finsupp.mem_support_iff, hD]
  exact ⟨fun h => h.1, fun h => ⟨h, hP⟩⟩

theorem ord_mul_inv_prod_w_zpow_eq_zero (f : F) (hf : f ≠ 0) (Z : Finset (Place L F)) (hZ : ∀ Q ∈ Z, Q ∈ An.dom)
    (hZf : ∀ P ∈ An.dom, (P ∈ Z ↔ P.ord f ≠ 0)) {P : Place L F} (hP : P ∈ An.dom) :
    P.ord (f * (∏ Q ∈ Z, w An Q ^ Q.ord f)⁻¹) = 0 := by
  classical
  rw [Place.ord_mul _ hf (inv_ne_zero (prod_w_zpow_ne_zero An Z hZ _)), Place.ord_inv]
  by_cases hPZ : P ∈ Z
  · rw [ord_prod_w_zpow_of_mem An Z hZ (fun Q => Q.ord f) hP hPZ]; ring
  · rw [ord_prod_w_zpow_of_not_mem An Z hZ (fun Q => Q.ord f) hP hPZ]
    have := (not_iff_not.mpr ((hZf P hP))).mp hPZ
    push Not at this
    rw [this]; ring

theorem exists_outer [IsAlgClosed L] (S : Finset (Place L F)) (hS : ∀ Q ∈ S, Q ∈ An.dom)
    {P₀ : Place L F} (hP₀ : P₀ ∈ An.dom) :
    ∃ Ps ∈ An.dom, A.valuation (P₀.evalAt An.param) < A.valuation (Ps.evalAt An.param) ∧
      ∀ Q ∈ S, A.valuation (Q.evalAt An.param) < A.valuation (Ps.evalAt An.param) := by
  classical
  set v := A.valuation with hv
  set Z₀ : Finset (Place L F) := insert P₀ S with hZ₀
  have hZ₀dom : ∀ Q ∈ Z₀, Q ∈ An.dom := by
    intro Q hQ; rcases Finset.mem_insert.mp hQ with rfl | hQ
    · exact hP₀
    · exact hS Q hQ
  obtain ⟨Qm, hQm, hmax⟩ := Finset.exists_max_image Z₀ (fun Q => v (Q.evalAt An.param)) ⟨P₀, Finset.mem_insert_self _ _⟩
  have hQmdom := hZ₀dom Qm hQm
  set b : L := Qm.evalAt An.param with hb
  obtain ⟨cs, hcs⟩ := IsAlgClosed.exists_eq_mul_self b
  have hb0 : b ≠ 0 := evalAt_param_ne_zero An hQmdom
  have hvb1 : v b < 1 := valuation_evalAt_param_lt_one An hQmdom
  have hcs0 : cs ≠ 0 := by rintro rfl; exact hb0 (by rw [hcs, mul_zero])
  have hvcs0 : v cs ≠ 0 := (Valuation.ne_zero_iff _).mpr hcs0
  have hvcs1 : v cs < 1 := by
    by_contra hge; push Not at hge
    have : 1 ≤ v b := by rw [hcs, map_mul]; exact one_le_mul hge hge
    exact absurd hvb1 (not_lt.mpr this)
  have hvb_lt : v b < v cs := by
    rw [hcs, map_mul]
    calc v cs * v cs < 1 * v cs := mul_lt_mul_of_pos_right hvcs1 (lt_of_le_of_ne zero_le' hvcs0.symm)
      _ = v cs := one_mul _
  have hcsA : cs ∈ A := (A.valuation_le_one_iff cs).mp hvcs1.le
  have hcsm : (⟨cs, hcsA⟩ : ↥A) ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff ⟨cs, hcsA⟩).mpr hvcs1
  have hcsadm : ∃ m ∈ maximalIdeal ↥A, ((An.modulus : ↥A) : L) = cs * m := by
    obtain ⟨m₀, hm₀, hmod⟩ := exists_modulus_eq An hQmdom
    refine ⟨⟨cs, hcsA⟩ * m₀, Ideal.mul_mem_left _ _ hm₀, ?_⟩
    rw [hmod, ← hb, hcs]; push_cast; ring
  obtain ⟨Ps, ⟨hPs, hPsv⟩, -⟩ := An.existsUnique_evalAt_eq ⟨cs, hcsA⟩ hcsm hcs0 hcsadm
  have hPsv' : Ps.evalAt An.param = cs := hPsv
  refine ⟨Ps, hPs, ?_, fun Q hQ => ?_⟩
  · rw [hPsv']; exact lt_of_le_of_lt (hmax P₀ (Finset.mem_insert_self _ _)) hvb_lt
  · rw [hPsv']; exact lt_of_le_of_lt (hmax Q (Finset.mem_insert_of_mem hQ)) hvb_lt

theorem valuation_evalAt_prod_w_pow (Z : Finset (Place L F)) (n : Place L F → ℕ)
    {P : Place L F} (hP : P ∈ An.dom)
    (hout : ∀ Q ∈ Z, A.valuation (Q.evalAt An.param) < A.valuation (P.evalAt An.param)) :
    A.valuation (P.evalAt (∏ Q ∈ Z, w An Q ^ n Q)) = A.valuation (P.evalAt An.param) ^ (∑ Q ∈ Z, n Q) := by
  classical
  rw [evalAt_finset_prod_of_mem P (isRational An hP) Z _ (fun Q hQ => pow_mem (w_mem An hP Q) _), map_prod,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun Q hQ => ?_
  rw [evalAt_pow_of_mem P (isRational An hP) (w_mem An hP Q), map_pow, valuation_evalAt_w An hP (ne_of_gt (hout Q hQ)),
    max_eq_left (hout Q hQ).le]

variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar] (C : RegularProlongation A F Fbar)

theorem w_mem_integers (hz : An.param ∈ C.integers) {Q : Place L F} (hQ : Q ∈ An.dom) : w An Q ∈ C.integers :=
  sub_mem hz ((C.algebraMap_mem_iff _).mpr (evalAt_param_mem An hQ))

theorem residue_w (hz : An.param ∈ C.integers) {Q : Place L F} (hQ : Q ∈ An.dom) :
    C.residue ⟨w An Q, w_mem_integers An C hz hQ⟩ = C.residue ⟨An.param, hz⟩ := by
  have hsplit : (⟨w An Q, w_mem_integers An C hz hQ⟩ : ↥C.integers) = ⟨An.param, hz⟩ -
      ⟨algebraMap L F ((⟨Q.evalAt An.param, evalAt_param_mem An hQ⟩ : ↥A) : L),
        (C.algebraMap_mem_iff _).mpr (evalAt_param_mem An hQ)⟩ := Subtype.ext rfl
  rw [hsplit, map_sub, C.residue_algebraMap ⟨Q.evalAt An.param, evalAt_param_mem An hQ⟩,
    (IsLocalRing.residue_eq_zero_iff _).mpr (evalAt_param_mem_maximalIdeal An hQ), map_zero, sub_zero]

theorem isUnit_w (hz : An.param ∈ C.integers) (hzres : C.residue ⟨An.param, hz⟩ ≠ 0) {Q : Place L F}
    (hQ : Q ∈ An.dom) : IsUnit (⟨w An Q, w_mem_integers An C hz hQ⟩ : ↥C.integers) := by
  by_contra hnu
  apply hzres
  rw [← residue_w An C hz hQ]
  have : (⟨w An Q, w_mem_integers An C hz hQ⟩ : ↥C.integers) ∈ maximalIdeal ↥C.integers :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnu
  rw [← C.ker_residue] at this
  exact this

end Annulus

end Ws33.Strip

open Ws33.Strip

namespace Ws33
namespace ZC

theorem zpow_eq_zpow_imp_eq_zero {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {s t : Γ} (hs : s ≠ 0)
    (hst : s < t) {e : ℤ} (h : s ^ e = t ^ e) : e = 0 := by
  rcases lt_trichotomy e 0 with he | he | he
  · exfalso
    have ht : t ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hst)
    have h' : t ^ (-e) = s ^ (-e) := by rw [zpow_neg, zpow_neg, h]
    have hlt : s ^ (-e) < t ^ (-e) := zpow_lt_zpow_left₀ (by omega) zero_le' hst
    exact absurd h' (ne_of_gt hlt)
  · exact he
  · exfalso
    have hlt : s ^ e < t ^ e := zpow_lt_zpow_left₀ he zero_le' hst
    exact absurd h (ne_of_lt hlt)

section Ann

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable (An : Annulus A F)

theorem exists_mem_dom [IsAlgClosed L] (hμ : ((An.modulus : ↥A) : L) ≠ 0) : ∃ P, P ∈ An.dom := by
  set v := A.valuation with hv
  obtain ⟨cs, hcs⟩ := IsAlgClosed.exists_eq_mul_self ((An.modulus : ↥A) : L)
  have hvμ1 : v ((An.modulus : ↥A) : L) < 1 := (A.valuation_lt_one_iff An.modulus).mp An.modulus_mem
  have hcs0 : cs ≠ 0 := by rintro rfl; exact hμ (by rw [hcs, mul_zero])
  have hvcs0 : v cs ≠ 0 := (Valuation.ne_zero_iff _).mpr hcs0
  have hvcs1 : v cs < 1 := by
    by_contra hge; push Not at hge
    have : 1 ≤ v ((An.modulus : ↥A) : L) := by rw [hcs, map_mul]; exact one_le_mul hge hge
    exact absurd hvμ1 (not_lt.mpr this)
  have hcsA : cs ∈ A := (A.valuation_le_one_iff cs).mp hvcs1.le
  have hcsm : (⟨cs, hcsA⟩ : ↥A) ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff ⟨cs, hcsA⟩).mpr hvcs1
  obtain ⟨P, ⟨hP, -⟩, -⟩ := An.existsUnique_evalAt_eq ⟨cs, hcsA⟩ hcsm hcs0 ⟨⟨cs, hcsA⟩, hcsm, by rw [hcs]⟩
  exact ⟨P, hP⟩

theorem valuation_evalAt_prod_w_pow_inner (Z : Finset (Place L F)) (n : Place L F → ℕ)
    {P : Place L F} (hP : P ∈ An.dom)
    (hin : ∀ Q ∈ Z, A.valuation (P.evalAt An.param) < A.valuation (Q.evalAt An.param)) :
    A.valuation (P.evalAt (∏ Q ∈ Z, w An Q ^ n Q)) = ∏ Q ∈ Z, A.valuation (Q.evalAt An.param) ^ n Q := by
  classical
  rw [evalAt_finset_prod_of_mem P (isRational An hP) Z _ (fun Q hQ => pow_mem (w_mem An hP Q) _), map_prod]
  refine Finset.prod_congr rfl fun Q hQ => ?_
  rw [evalAt_pow_of_mem P (isRational An hP) (w_mem An hP Q), map_pow, valuation_evalAt_w An hP (ne_of_lt (hin Q hQ)),
    max_eq_right (hin Q hQ).le]

end Ann

section Chart

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]

theorem strip_identity (An : Annulus A F) (C : RegularProlongation A F Fbar) (x : Place (ResidueField ↥A) Fbar)
    (hz : An.param ∈ C.integers) (hz1 : x.ord (C.residue ⟨An.param, hz⟩) = 1)
    (hlaw : ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom, ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x.ord (C.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (f : F) (hf0 : f ≠ 0) (c : L) (hc0 : c ≠ 0)
    (hc : c • f ∈ C.integers) (hcu : C.residue ⟨c • f, hc⟩ ≠ 0)
    (Z : Finset (Place L F)) (hZ : ∀ Q ∈ Z, Q ∈ An.dom) (hZf : ∀ P ∈ An.dom, (P ∈ Z ↔ P.ord f ≠ 0))
    {P : Place L F} (hP : P ∈ An.dom) (hPZ : P ∉ Z) :
    A.valuation (P.evalAt An.param) ^ (x.ord (C.residue ⟨c • f, hc⟩) - ∑ Q ∈ Z, Q.ord f) *
        A.valuation (P.evalAt (∏ Q ∈ Z, w An Q ^ (Q.ord f).toNat)) =
      A.valuation c * A.valuation (P.evalAt f) * A.valuation (P.evalAt (∏ Q ∈ Z, w An Q ^ (-(Q.ord f)).toNat)) := by
  classical
  set z := An.param with hzdef
  set v := A.valuation with hv
  set a : ℤ := x.ord (C.residue ⟨c • f, hc⟩) with ha
  have hzres : C.residue ⟨z, hz⟩ ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hz1; exact zero_ne_one hz1

  set np : Place L F → ℕ := fun Q => (Q.ord f).toNat with hnp
  set nm : Place L F → ℕ := fun Q => (-(Q.ord f)).toNat with hnm
  have hnpm : ∀ Q, ((np Q : ℕ) : ℤ) - ((nm Q : ℕ) : ℤ) = Q.ord f := fun Q => by
    simp only [hnp, hnm]; omega

  set hp : F := ∏ Q ∈ Z, w An Q ^ np Q with hhp
  set hm : F := ∏ Q ∈ Z, w An Q ^ nm Q with hhm
  set wC : Place L F → ↥C.integers := fun Q => if hQ : Q ∈ An.dom then ⟨w An Q, w_mem_integers An C hz hQ⟩ else 1
    with hwCdef
  have hwC_eq : ∀ Q (hQ : Q ∈ An.dom), wC Q = ⟨w An Q, w_mem_integers An C hz hQ⟩ := fun Q hQ => by
    simp [hwCdef, hQ]
  set hpC : ↥C.integers := ∏ Q ∈ Z, (wC Q) ^ np Q with hhpC
  set hmC : ↥C.integers := ∏ Q ∈ Z, (wC Q) ^ nm Q with hhmC
  have hhpC_coe : (hpC : F) = hp := by
    rw [hhpC, hhp]; push_cast
    exact Finset.prod_congr rfl fun Q hQ => by rw [hwC_eq Q (hZ Q hQ)]
  have hhmC_coe : (hmC : F) = hm := by
    rw [hhmC, hhm]; push_cast
    exact Finset.prod_congr rfl fun Q hQ => by rw [hwC_eq Q (hZ Q hQ)]
  set Np : ℕ := ∑ Q ∈ Z, np Q with hNp
  set Nm : ℕ := ∑ Q ∈ Z, nm Q with hNm
  have hN : ((Np : ℕ) : ℤ) - ((Nm : ℕ) : ℤ) = ∑ Q ∈ Z, Q.ord f := by
    rw [hNp, hNm]; push_cast; rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun Q _ => hnpm Q
  have hres_prod : ∀ (n : Place L F → ℕ), C.residue (∏ Q ∈ Z, (wC Q) ^ n Q) = C.residue ⟨z, hz⟩ ^ (∑ Q ∈ Z, n Q) := by
    intro n
    rw [map_prod]
    simp_rw [map_pow]
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun Q hQ => by rw [hwC_eq Q (hZ Q hQ), residue_w An C hz (hZ Q hQ)]
  have hhpres : C.residue hpC = C.residue ⟨z, hz⟩ ^ Np := hres_prod np
  have hhmres : C.residue hmC = C.residue ⟨z, hz⟩ ^ Nm := hres_prod nm
  have hhpres0 : C.residue hpC ≠ 0 := by rw [hhpres]; exact pow_ne_zero _ hzres
  have hhmres0 : C.residue hmC ≠ 0 := by rw [hhmres]; exact pow_ne_zero _ hzres
  have hpunit : IsUnit hpC := by
    by_contra hnu
    apply hhpres0
    have : hpC ∈ maximalIdeal ↥C.integers := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← C.ker_residue] at this
    exact this
  obtain ⟨uC, huC⟩ := hpunit
  have hp0 : hp ≠ 0 := Finset.prod_ne_zero_iff.mpr fun Q hQ => pow_ne_zero _ (w_ne_zero An (hZ Q hQ))
  have hm0 : hm ≠ 0 := Finset.prod_ne_zero_iff.mpr fun Q hQ => pow_ne_zero _ (w_ne_zero An (hZ Q hQ))
  have hcf0 : c • f ≠ 0 := smul_ne_zero hc0 hf0

  set gC : ↥C.integers := ⟨c • f, hc⟩ * hmC * ((uC⁻¹ : (↥C.integers)ˣ) : ↥C.integers) with hgC
  set g : F := (gC : F) with hgdef
  have hginv : ((uC⁻¹ : (↥C.integers)ˣ) : ↥C.integers) * hpC = 1 := by rw [← huC]; exact uC.inv_mul
  have hg_mul : g * hp = c • f * hm := by
    have := congrArg Subtype.val (show gC * hpC = ⟨c • f, hc⟩ * hmC by
      rw [hgC, mul_assoc, hginv, mul_one])
    simpa [hhpC_coe, hhmC_coe] using this
  have hgres_mul : C.residue gC * C.residue hpC = C.residue ⟨c • f, hc⟩ * C.residue hmC := by
    rw [← map_mul, ← map_mul, hgC, mul_assoc, hginv, mul_one]
  have hgres0 : C.residue gC ≠ 0 := by
    intro h0
    have := hgres_mul
    rw [h0, zero_mul] at this
    exact mul_ne_zero hcu hhmres0 this.symm
  have hordg : x.ord (C.residue gC) = a - ∑ Q ∈ Z, Q.ord f := by
    have := congrArg x.ord hgres_mul
    rw [Place.ord_mul _ hgres0 hhpres0, Place.ord_mul _ hcu hhmres0, hhpres, hhmres, ← zpow_natCast, ← zpow_natCast,
      Place.ord_zpow, Place.ord_zpow, hz1, mul_one, mul_one] at this
    rw [← hN]; omega
  have hg0 : g ≠ 0 := by
    intro h; apply hgres0
    have : gC = 0 := Subtype.ext h
    rw [this, map_zero]

  have hordcf : ∀ Q : Place L F, Q.ord (c • f) = Q.ord f := by
    intro Q
    rw [Algebra.smul_def, Place.ord_mul _ ((map_ne_zero _).mpr hc0) hf0,
      ord_eq_zero_of_evalAt_ne_zero Q (Q.algebraMap_mem' c) (by rw [Place.evalAt_algebraMap_eq]; exact hc0), zero_add]
  have hord_pow : ∀ (n : Place L F → ℕ) (Q : Place L F), Q ∈ An.dom →
      Q.ord (∏ R ∈ Z, w An R ^ n R) = if Q ∈ Z then ((n Q : ℕ) : ℤ) else 0 := by
    intro n Q hQ
    have : (∏ R ∈ Z, w An R ^ n R) = ∏ R ∈ Z, w An R ^ ((n R : ℕ) : ℤ) :=
      Finset.prod_congr rfl fun R _ => (zpow_natCast _ _).symm
    rw [this]
    split_ifs with hQZ
    · exact ord_prod_w_zpow_of_mem An Z hZ _ hQ hQZ
    · exact ord_prod_w_zpow_of_not_mem An Z hZ _ hQ hQZ
  have hgord : ∀ Q ∈ An.dom, Q.ord g = 0 := by
    intro Q hQ
    have := congrArg Q.ord hg_mul
    rw [Place.ord_mul _ hg0 hp0, Place.ord_mul _ hcf0 hm0, hordcf, hhp, hhm, hord_pow np Q hQ, hord_pow nm Q hQ] at this
    by_cases hQZ : Q ∈ Z
    · rw [if_pos hQZ, if_pos hQZ] at this
      have := hnpm Q; omega
    · rw [if_neg hQZ, if_neg hQZ] at this
      have h0 : Q.ord f = 0 := by
        have := (not_iff_not.mpr (hZf Q hQ)).mp hQZ
        push Not at this; exact this
      omega

  have law := hlaw g gC.2 (by rw [show (⟨g, gC.2⟩ : ↥C.integers) = gC from Subtype.ext rfl]; exact hgres0) hgord P hP
  obtain ⟨hmemA, hunit⟩ := law
  have hvg : v (P.evalAt g) * v (P.evalAt z) ^ (-(a - ∑ Q ∈ Z, Q.ord f)) = 1 := by
    have e1 := (A.valuation_eq_one_iff _).mp hunit
    change v (P.evalAt g * P.evalAt z ^ (-x.ord (C.residue ⟨g, gC.2⟩))) = 1 at e1
    have hsub : (⟨g, gC.2⟩ : ↥C.integers) = gC := Subtype.ext rfl
    rw [hsub, hordg, map_mul, map_zpow₀] at e1
    exact e1

  have hrat := isRational An hP
  have hfP : f ∈ P.toValuationSubring := by
    refine P.mem_toValuationSubring_of_ord_nonneg_alt hf0 (le_of_eq ?_)
    have := (not_iff_not.mpr (hZf P hP)).mp hPZ
    push Not at this; exact this.symm
  have hgP : g ∈ P.toValuationSubring := P.mem_toValuationSubring_of_ord_nonneg_alt hg0 (hgord P hP).ge
  have hhpP : hp ∈ P.toValuationSubring := prod_mem_valuationSubring P Z _ (fun Q hQ => pow_mem (w_mem An hP Q) _)
  have hhmP : hm ∈ P.toValuationSubring := prod_mem_valuationSubring P Z _ (fun Q hQ => pow_mem (w_mem An hP Q) _)
  have hcP : algebraMap L F c ∈ P.toValuationSubring := P.algebraMap_mem' c
  have heval : P.evalAt g * P.evalAt hp = c * P.evalAt f * P.evalAt hm := by
    rw [← P.evalAt_mul_of_mem hrat hgP hhpP, hg_mul, Algebra.smul_def,
      P.evalAt_mul_of_mem hrat (mul_mem hcP hfP) hhmP, P.evalAt_mul_of_mem hrat hcP hfP, Place.evalAt_algebraMap_eq]
  have hvz0 : v (P.evalAt z) ≠ 0 := (Valuation.ne_zero_iff _).mpr (evalAt_param_ne_zero An hP)

  have hvgeq : v (P.evalAt g) = v (P.evalAt z) ^ (a - ∑ Q ∈ Z, Q.ord f) := by
    have := hvg
    rw [zpow_neg] at this
    rw [← mul_inv_cancel₀ (zpow_ne_zero (a - ∑ Q ∈ Z, Q.ord f) hvz0)] at this
    exact mul_right_cancel₀ (inv_ne_zero (zpow_ne_zero _ hvz0)) this
  have := congrArg v heval
  rw [map_mul, map_mul, map_mul, hvgeq] at this
  rw [hhp, hhm] at this
  exact this

end Chart

end Ws33.ZC

namespace Ws33
namespace ZC

theorem key_algebra {Γ : Type*} [CommGroupWithZero Γ] (t μ c c' Φ Kp Km : Γ) (ht : t ≠ 0) (hc : c ≠ 0)
    (a a' N : ℤ) (Np Nm : ℕ) (hN : ((Np : ℕ) : ℤ) - ((Nm : ℕ) : ℤ) = N)
    (E1 : t ^ (a - N) * t ^ Np = c * Φ * t ^ Nm)
    (E2 : (μ * t⁻¹) ^ (a' - N) * Kp = c' * Φ * Km) :
    t ^ (a + a' - N) * (c' * Km) = c * μ ^ (a' - N) * Kp := by

  have hF : c * Φ = t ^ a := by
    have h1 : t ^ (a - N) * t ^ Np = t ^ (a - N + Np) := by
      rw [← zpow_natCast, ← zpow_add₀ ht]
    have h2 : c * Φ = t ^ (a - N + Np) * (t ^ (Nm : ℕ))⁻¹ := by
      rw [← h1, E1, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht), mul_one]
    rw [h2, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ ht]
    congr 1
    omega

  have h3 : (μ * t⁻¹) ^ (a' - N) = μ ^ (a' - N) * t ^ (-(a' - N)) := by
    rw [mul_zpow, inv_zpow', ]
  rw [h3] at E2

  have h4 : c * (μ ^ (a' - N) * t ^ (-(a' - N)) * Kp) = c' * t ^ a * Km := by
    rw [E2, ← hF]; simp only [mul_comm, mul_left_comm, mul_assoc]

  have h5 : t ^ (a' - N) * t ^ (-(a' - N)) = 1 := by
    rw [← zpow_add₀ ht, add_neg_cancel, zpow_zero]
  have h6 : t ^ (a + a' - N) = t ^ a * t ^ (a' - N) := by
    rw [← zpow_add₀ ht]; congr 1; omega
  calc t ^ (a + a' - N) * (c' * Km) = t ^ (a' - N) * (c' * t ^ a * Km) := by
        rw [h6]; simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = t ^ (a' - N) * (c * (μ ^ (a' - N) * t ^ (-(a' - N)) * Kp)) := by rw [h4]
    _ = c * μ ^ (a' - N) * Kp * (t ^ (a' - N) * t ^ (-(a' - N))) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = c * μ ^ (a' - N) * Kp := by rw [h5, mul_one]

end Ws33.ZC

open Ws33.ZC in

theorem Ws33.ZC.sum_eq_ord_add_ord
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar] [Field Fbar'] [Algebra (ResidueField ↥A) Fbar']
    (C : RegularProlongation A F Fbar) (x : Place (ResidueField ↥A) Fbar)
    (C' : RegularProlongation A F Fbar') (x' : Place (ResidueField ↥A) Fbar')
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hμ : ((An.modulus : ↥A) : L) ≠ 0)
    (hrec : An'.param * An.param = algebraMap L F ((An.modulus : ↥A) : L))
    (hz : An.param ∈ C.integers) (hz1 : x.ord (C.residue ⟨An.param, hz⟩) = 1)
    (hlaw : ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord f = 0) →
      ∀ P ∈ An.dom, ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(x.ord (C.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (hz' : An'.param ∈ C'.integers) (hz1' : x'.ord (C'.residue ⟨An'.param, hz'⟩) = 1)
    (hlaw' : ∀ (f : F) (hf : f ∈ C'.integers), C'.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord f = 0) →
      ∀ P ∈ An'.dom, ∃ h : P.evalAt f * (P.evalAt An'.param) ^ (-(x'.ord (C'.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (f : F) (hf : f ∈ C.integers) (hfu : C.residue ⟨f, hf⟩ ≠ 0)
    (c' : L) (hc' : c' • f ∈ C'.integers) (hc'u : C'.residue ⟨c' • f, hc'⟩ ≠ 0) :
    ∀ D : Divisor L F, (∀ P ∈ An.dom, D P = P.ord f) → (∀ P, P ∉ An.dom → D P = 0) →
      D.sum (fun _ n => n) = x.ord (C.residue ⟨f, hf⟩) + x'.ord (C'.residue ⟨c' • f, hc'⟩) := by
  classical
  intro D hD hD0
  set v := A.valuation with hv
  have h1 : (1 : L) • f ∈ C.integers := by rw [one_smul]; exact hf
  have h1res : C.residue ⟨(1 : L) • f, h1⟩ = C.residue ⟨f, hf⟩ := congrArg C.residue (Subtype.ext (one_smul _ _))
  have h1u : C.residue ⟨(1 : L) • f, h1⟩ ≠ 0 := by rw [h1res]; exact hfu
  set a : ℤ := x.ord (C.residue ⟨f, hf⟩) with ha
  set a' : ℤ := x'.ord (C'.residue ⟨c' • f, hc'⟩) with ha'

  have hc'0 : c' ≠ 0 := by
    intro h; apply hc'u
    have : (⟨c' • f, hc'⟩ : ↥C'.integers) = 0 := Subtype.ext (by simp [h])
    rw [this, map_zero]
  have hf0 : f ≠ 0 := by
    intro h; apply hfu
    have : (⟨f, hf⟩ : ↥C.integers) = 0 := Subtype.ext h
    rw [this, map_zero]

  set Z : Finset (Place L F) := D.support with hZdef
  have hZ : ∀ Q ∈ Z, Q ∈ An.dom := fun Q hQ => by
    by_contra h; exact (Finsupp.mem_support_iff.mp hQ) (hD0 Q h)
  have hZf : ∀ P ∈ An.dom, (P ∈ Z ↔ P.ord f ≠ 0) := fun P hP => by
    rw [hZdef, Finsupp.mem_support_iff, hD P hP]
  have hZ' : ∀ Q ∈ Z, Q ∈ An'.dom := fun Q hQ => by rw [hdom]; exact hZ Q hQ
  have hZf' : ∀ P ∈ An'.dom, (P ∈ Z ↔ P.ord f ≠ 0) := fun P hP => hZf P (by rw [← hdom]; exact hP)
  have hsum : D.sum (fun _ n => n) = ∑ Q ∈ Z, Q.ord f := by
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun Q hQ => hD Q (hZ Q hQ)
  rw [hsum]
  set N : ℤ := ∑ Q ∈ Z, Q.ord f with hNdef
  set np : Place L F → ℕ := fun Q => (Q.ord f).toNat with hnp
  set nm : Place L F → ℕ := fun Q => (-(Q.ord f)).toNat with hnm
  have hN : ((∑ Q ∈ Z, np Q : ℕ) : ℤ) - ((∑ Q ∈ Z, nm Q : ℕ) : ℤ) = N := by
    push_cast; rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun Q _ => by simp only [hnp, hnm]; omega

  obtain ⟨P₀, hP₀⟩ := exists_mem_dom An hμ
  obtain ⟨P₁, hP₁, -, hout₁⟩ := exists_outer An Z hZ hP₀
  obtain ⟨P₂, hP₂, h12, hout₂⟩ := exists_outer An Z hZ hP₁

  have hzz' : ∀ P ∈ An.dom, v (P.evalAt An'.param) * v (P.evalAt An.param) = v ((An.modulus : ↥A) : L) := by
    intro P hP
    have hP' : P ∈ An'.dom := by rw [hdom]; exact hP
    rw [← map_mul, ← P.evalAt_mul_of_mem (isRational An hP) (param_mem An' hP') (param_mem An hP), hrec,
      Place.evalAt_algebraMap_eq]
  have hvμ0 : v ((An.modulus : ↥A) : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr hμ

  have key : ∀ P ∈ An.dom, (∀ Q ∈ Z, v (Q.evalAt An.param) < v (P.evalAt An.param)) →
      v (P.evalAt An.param) ^ (a + a' - N) * (v c' * ∏ Q ∈ Z, v (Q.evalAt An'.param) ^ nm Q) =
        1 * v ((An.modulus : ↥A) : L) ^ (a' - N) * ∏ Q ∈ Z, v (Q.evalAt An'.param) ^ np Q := by
    intro P hP hout
    have hP' : P ∈ An'.dom := by rw [hdom]; exact hP
    have hPZ : P ∉ Z := fun h => lt_irrefl _ (hout P h)
    have ht0 : v (P.evalAt An.param) ≠ 0 := (Valuation.ne_zero_iff _).mpr (evalAt_param_ne_zero An hP)

    have E1 := strip_identity An C x hz hz1 hlaw f hf0 1 one_ne_zero h1 h1u Z hZ hZf hP hPZ
    rw [h1res, map_one] at E1
    rw [valuation_evalAt_prod_w_pow An Z np hP hout, valuation_evalAt_prod_w_pow An Z nm hP hout] at E1

    have hz'P : v (P.evalAt An'.param) = v ((An.modulus : ↥A) : L) * (v (P.evalAt An.param))⁻¹ := by
      rw [← hzz' P hP, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    have hin : ∀ Q ∈ Z, v (P.evalAt An'.param) < v (Q.evalAt An'.param) := by
      intro Q hQ
      have hQ0 : v (Q.evalAt An.param) ≠ 0 := (Valuation.ne_zero_iff _).mpr (evalAt_param_ne_zero An (hZ Q hQ))
      have hz'Q : v (Q.evalAt An'.param) = v ((An.modulus : ↥A) : L) * (v (Q.evalAt An.param))⁻¹ := by
        rw [← hzz' Q (hZ Q hQ), mul_assoc, mul_inv_cancel₀ hQ0, mul_one]
      rw [hz'P, hz'Q]
      exact mul_lt_mul_of_pos_left (inv_strictAnti₀ (lt_of_le_of_ne zero_le' hQ0.symm) (hout Q hQ))
        (lt_of_le_of_ne zero_le' hvμ0.symm)
    have E2 := strip_identity An' C' x' hz' hz1' hlaw' f hf0 c' hc'0 hc' hc'u Z hZ' hZf' hP' hPZ
    rw [valuation_evalAt_prod_w_pow_inner An' Z np hP' hin, valuation_evalAt_prod_w_pow_inner An' Z nm hP' hin,
      hz'P] at E2
    exact key_algebra _ _ _ _ _ _ _ ht0 one_ne_zero a a' N _ _ hN E1 E2
  have k1 := key P₁ hP₁ hout₁
  have k2 := key P₂ hP₂ hout₂
  have hB : (v c' * ∏ Q ∈ Z, v (Q.evalAt An'.param) ^ nm Q) ≠ 0 := by
    refine mul_ne_zero ((Valuation.ne_zero_iff _).mpr hc'0) (Finset.prod_ne_zero_iff.mpr fun Q hQ => pow_ne_zero _ ?_)
    exact (Valuation.ne_zero_iff _).mpr (evalAt_param_ne_zero An' (hZ' Q hQ))
  have heq : v (P₁.evalAt An.param) ^ (a + a' - N) = v (P₂.evalAt An.param) ^ (a + a' - N) :=
    mul_right_cancel₀ hB (k1.trans k2.symm)
  have he : a + a' - N = 0 :=
    zpow_eq_zpow_imp_eq_zero ((Valuation.ne_zero_iff _).mpr (evalAt_param_ne_zero An hP₁)) h12 heq
  omega

namespace Ws33
namespace B00

open AlgebraicCurve IsLocalRing

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_add_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply Place.algebraMap_residueField_injective v
  rw [map_add, Place.algebraMap_evalAt v hv hf, Place.algebraMap_evalAt v hv hg,
    Place.algebraMap_evalAt v hv (add_mem hf hg), ← map_add]
  rfl

theorem evalAt_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) : v.evalAt f = 0 := by
  rw [Place.evalAt, dif_neg hf]

theorem single_zero_eq_algebraMap {L : Type*} [Field L] (x : L) :
    HahnSeries.single (0 : ℤ) x = algebraMap L (LaurentSeries L) x := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

end Ws33.B00

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open Ws33.Strip Ws33.ZC Ws33.B00 in
open scoped Classical in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (N : Finset (Place (ResidueField ↥A) FSS))
    (Sx : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
    (φx : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥A →+* ↥(Sx Q)))
    (χ₀x : (Q : Place (ResidueField ↥A) FSS) → (↥(Sx Q) →+* ResidueField ↥A))
    (Dx : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (h0 : (∃ t : FSS, Transcendental (ResidueField A) t))
    (h1 : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))))
    (h2 : (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers))
    (hcard : N.card = q + 1)
    (hpkg : (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

          (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ Sx Q) ∧
          (φx Q).FormallySmooth ∧ (φx Q).FormallyUnramified ∧
          (∀ a : ↥A, ((φx Q (Polynomial.C a) : ↥(Sx Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
          (∀ a : ↥A, χ₀x Q (φx Q (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
          χ₀x Q (φx Q Polynomial.X) = 0 ∧
          (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
            ∃! χ : ↥(Sx Q) →+* ↥A, (∀ a : ↥A, χ (φx Q (Polynomial.C a)) = a) ∧
              (∀ f : ↥(Sx Q), IsLocalRing.residue ↥A (χ f) = χ₀x Q f) ∧ χ (φx Q Polynomial.X) = c) ∧
          (∀ f : ↥(Sx Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
            IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
              algebraMap (ResidueField ↥A) Q.ResidueField (χ₀x Q f)) ∧
          (∃ hR : ((φx Q Polynomial.X : ↥(Sx Q)) : ↥(fieldBar q M')) ∈ R.integers,
            Q.ord (R.residue ⟨((φx Q Polynomial.X : ↥(Sx Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
          (∀ P, P ∈ Dx Q ↔ (P.IsRational ∧ (∀ f : ↥(Sx Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
            (∀ f : ↥(Sx Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀x Q f = 0))) ∧
          (∀ χ : ↥(Sx Q) →+* ↥A, (∀ a : ↥A, χ (φx Q (Polynomial.C a)) = a) →
            (∀ f : ↥(Sx Q), IsLocalRing.residue ↥A (χ f) = χ₀x Q f) →
            ∃! P, P ∈ Dx Q ∧ ∀ f : ↥(Sx Q), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
          (∀ P ∈ Dx Q, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
            ∃ g h : ↥(Sx Q), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ Dx Q, P.ord f = 0) →
            ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(Sx Q))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(Sx Q)) : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ Dx Q, f ∈ P.toValuationSubring) → f ∈ Sx Q)))
    (hdisj : (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ P, P ∈ Dx Q → P ∈ Dx Q' → Q = Q'))
    (hcusp : (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : fieldBar q M')))
    (heqv : (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
            ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
          ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
            (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
            (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q))))

    (hK : (∃ An : Place (ResidueField ↥A) FSS → Annulus A ↥(fieldBar q M'),
          (∀ x ∈ N,
            (∃ hz : (An x).param ∈ R.integers, x.ord (R.residue ⟨(An x).param, hz⟩) = 1 ∧
              ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers), R.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ (An x).dom, P.ord f = 0) →
                ∀ P ∈ (An x).dom,
                  ∃ h : P.evalAt f * (P.evalAt (An x).param) ^ (-(x.ord (R.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
            ((An x).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
            (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P, P ∈ (An x).dom → P ∉ Dx Q) ∧
            (∀ P ∈ (An x).dom, (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
                (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                  0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
                (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                  ∀ a : A, IsLocalRing.residue A a =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                    ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                      (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A))) ∧
          (∀ x x' : Place (ResidueField ↥A) FSS, x ∈ N → x' ∈ N → ∀ P, P ∈ (An x).dom → P ∈ (An x').dom → x = x') ∧
          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers), ∀ x ∈ N,
              AlgebraicCurve.RegularProlongation.smulDisc τ (An x).dom = (An (R.resAut τ hτ • x)).dom) ∧

          (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              (∀ P' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                0 ≤ P'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                  ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P'.ord (f : ↥(modularFunctionFieldBar M'))) →
              (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                ∀ a : A, IsLocalRing.residue A a =
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                  ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                    (⟨_, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) →
            (∃ Q, Q ∉ N ∧ P ∈ Dx Q) ∨ ∃ x, x ∈ N ∧ P ∈ (An x).dom) ∧

          (∀ x ∈ N, ∀ x' ∈ N, x ≠ x' →
            ∃ (g : ↥(fieldBar q M')) (hg : g ∈ R.integers), R.residue ⟨g, hg⟩ ≠ 0 ∧ x.ord (R.residue ⟨g, hg⟩) ≠ 0 ∧
              (∀ P ∈ (An x).dom, P.ord g = 0) ∧
              (∀ P ∈ (An x').dom, g ∈ P.toValuationSubring ∧ ∃ h : P.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A))) ∧

          (∃
          (FIx : Place (ResidueField A) FSS → Type) (_ : ∀ x, Field (FIx x)) (_ : ∀ x, Algebra (ResidueField A) (FIx x))
          (Rx : ∀ x : Place (ResidueField A) FSS, RegularProlongation A (fieldBar q M') (FIx x))
          (bx : ∀ x : Place (ResidueField A) FSS, Place (ResidueField A) (FIx x))

          (Λ : Type) (C' : Λ → Subring (AlgebraicClosure ℚ)) (hC'A : ∀ (l : Λ) (c : AlgebraicClosure ℚ), c ∈ C' l → c ∈ A)
          (_ : ∀ l, IsDomain ↥(C' l)) (_ : ∀ l, IsDiscreteValuationRing ↥(C' l))
          (ϖ' : ∀ l, ↥(C' l)) (l₀ : Λ)
          (Wc : Λ → Type) (_ : ∀ l, CommRing (Wc l)) (_ : ∀ l, IsDomain (Wc l)) (_ : ∀ l, IsDiscreteValuationRing (Wc l))
          (_ : ∀ l, IsAdicComplete (maximalIdeal (Wc l)) (Wc l))
          (πW : ∀ l, Wc l) (E : Λ → ℕ) (E₀ : ℕ)

          (S : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
          (𝒩 : Place (ResidueField A) FSS → Subring (fieldBar q M'))
          (𝒩₀ : Place (ResidueField A) FSS → Λ → Subring (fieldBar q M'))
          (hloc : ∀ nd l, IsLocalRing ↥(𝒩₀ nd l)) (hnoe : ∀ nd l, IsNoetherianRing ↥(𝒩₀ nd l))
          (cx cy cu : Place (ResidueField A) FSS → fieldBar q M'),

          (∀ (l : Λ) (d : ↥(C' l)), IsLocalRing.residue A ⟨(d : AlgebraicClosure ℚ), hC'A l d d.2⟩ = 0 ↔ ∃ d' : ↥(C' l), d = ϖ' l * d') ∧
          (∀ l, C' l₀ ≤ C' l) ∧
          ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ≠ 0 ∧
          (∀ a : AlgebraicClosure ℚ, a ∈ A → IsAlgebraic ↥(C' l₀) a) ∧
          (∀ l, Irreducible (πW l)) ∧ (∀ l, 1 ≤ E l) ∧

          (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
            τ ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) = ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ)) ∧

          (∃ w : ℕ, 1 ≤ w ∧ ∃ v : (↥A)ˣ,
            (⟨((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ), hC'A l₀ _ (ϖ' l₀).2⟩ : ↥A) ^ E₀ = (v : ↥A) * ⟨π, hπP⟩ ^ w) ∧

          (∀ nd ∈ N,

            (bx nd).IsRational ∧ nd.IsRational ∧ (∀ P ∈ S nd, P.IsRational) ∧

            (∀ f : fieldBar q M', f ∈ 𝒩 nd ↔ f ∈ (Rx nd).integers ∧ f ∈ R.integers ∧ ∀ P ∈ S nd, f ∈ P.toValuationSubring) ∧
            (∀ f ∈ 𝒩 nd, ∀ P ∈ S nd, P.evalAt f ∈ A) ∧

            cx nd * cy nd = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ * cu nd ∧
            (∀ h₁ : cx nd ∈ (Rx nd).integers, (Rx nd).residue ⟨cx nd, h₁⟩ = 0) ∧
            (∀ h₂ : cx nd ∈ R.integers, nd.ord (R.residue ⟨cx nd, h₂⟩) = 1) ∧
            (∀ h₂ : cy nd ∈ R.integers, R.residue ⟨cy nd, h₂⟩ = 0) ∧
            (∀ h₁ : cy nd ∈ (Rx nd).integers, (bx nd).ord ((Rx nd).residue ⟨cy nd, h₁⟩) = 1) ∧

            (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
              let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S nd ↔ g • P ∈ S nd) ∧ g • cx nd = cx nd ∧ g • cy nd = cy nd) ∧

            (∀ f : fieldBar q M', ∃ (l : Λ) (a b : ↥(𝒩₀ nd l)), (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = (a : fieldBar q M')) ∧

            (∀ f : fieldBar q M', ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd l₀)) (b : ↥(𝒩₀ nd l₀)),
              (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = ∑ i, c i • ((a i : ↥(𝒩₀ nd l₀)) : fieldBar q M')) ∧

            (∀ l, letI : IsLocalRing ↥(𝒩₀ nd l) := hloc nd l;
              𝒩₀ nd l₀ ≤ 𝒩₀ nd l ∧ 𝒩₀ nd l ≤ 𝒩 nd ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ S nd ↔
                (∀ f : fieldBar q M', f ∈ 𝒩₀ nd l → f ∈ P.toValuationSubring) ∧
                (∀ f : ↥(𝒩₀ nd l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
              (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀ nd l) ∧
              (∀ g : ↥(𝒩₀ nd l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
              (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd l)), LinearIndependent ↥(C' l) c →
                ∑ i, c i • ((a i : ↥(𝒩₀ nd l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧

              (∃ Bx : Subring (fieldBar q M'),
                (∀ f : fieldBar q M', f ∈ Bx → f ∈ 𝒩₀ nd l) ∧
                cx nd ∈ Bx ∧ cy nd ∈ Bx ∧ cu nd ∈ Bx ∧
                (∀ f : fieldBar q M', f ∈ 𝒩₀ nd l ↔ ∃ g h : fieldBar q M', g ∈ Bx ∧ h ∈ Bx ∧
                  (∀ hh : h ∈ 𝒩₀ nd l, IsUnit (⟨h, hh⟩ : ↥(𝒩₀ nd l))) ∧ f * h = g) ∧
                (∃ T : Finset (fieldBar q M'), Bx = Subring.closure
                  ({f : fieldBar q M' | ∃ c : AlgebraicClosure ℚ, c ∈ C' l ∧ f = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c} ∪
                    (↑T : Set (fieldBar q M'))))) ∧
              cx nd ∈ 𝒩₀ nd l ∧ cy nd ∈ 𝒩₀ nd l ∧ (∃ hu : cu nd ∈ 𝒩₀ nd l, IsUnit (⟨cu nd, hu⟩ : ↥(𝒩₀ nd l))) ∧
              ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l))
                (ι : AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l) ≃+* UVCrossingModel (Wc l) (πW l ^ E l)),
                (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l,
                  σ (πW l) = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ o : Wc l, ι (σ o) = const (πW l ^ E l) o) ∧
                (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l),
                  ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₁ : f.1 ∈ (Rx nd).integers), (Rx nd).residue ⟨f.1, h₁⟩ ≠ 0 →
                  (bx nd).ord ((Rx nd).residue ⟨f.1, h₁⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
                      ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * V (πW l ^ E l) ^ n ∈
                        Ideal.span {const (πW l ^ E l) (πW l), U (πW l ^ E l)}) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
                  nd.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
                      ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * U (πW l ^ E l) ^ n ∈
                        Ideal.span {const (πW l ^ E l) (πW l), V (πW l ^ E l)}))) ∧

          (∃ (hJK : ModularCurve.jqNModC (AlgebraicClosure ℚ) q ∈ fieldBar q M') (a₀ : AlgebraicClosure ℚ) (ha₀ : a₀ ∈ A)
             (hR : (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀ ∈ R.integers),
            R.residue ⟨_, hR⟩ = 0 ∧
            (IsLocalRing.residue ↥A ⟨a₀, ha₀⟩) ^ q = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField ↥A) M') ∧
            ∃ (c' : AlgebraicClosure ℚ) (htc : c' • ((⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀) ∈ R.integers),
              R.residue ⟨_, htc⟩ ≠ 0 ∧
              ∀ nd ∈ N, ∃ hC : ((⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) -
                algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀) ∈ (Rx nd).integers,
                (Rx nd).residue ⟨_, hC⟩ ≠ 0 ∧
                nd.ord (R.residue ⟨_, htc⟩) = -((bx nd).ord ((Rx nd).residue ⟨_, hC⟩))) ∧

          (∀ nd ∈ N, ∀ nd' ∈ N, ∀ P, P ∈ S nd → P ∈ S nd' → nd = nd') ∧

          (∀ nd ∈ N, ∀ P ∈ S nd, ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
            (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
              0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
            (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
              ∀ a : A, residue A a =
                  (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧

          (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∃ τN : Place (ResidueField A) FSS → Place (ResidueField A) FSS,
            ∀ nd ∈ N, τN nd ∈ N ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), (levelAutBar q M' ζ' γ) • P ∈ S nd ↔ P ∈ S (τN nd)) ∧
              ((Rx nd).integers).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = (Rx (τN nd)).integers) ∧

          (∀ τ ∈ Subgroup.closure {τ : (fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] (fieldBar q M') |
                ∃ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ' γ},
            ∀ (hτ : ∀ f : fieldBar q M', τ f ∈ R.integers ↔ f ∈ R.integers), ∀ nd ∈ N,
              R.resAut τ hτ • nd ∈ N ∧
              AlgebraicCurve.RegularProlongation.smulDisc τ (S nd) = S (R.resAut τ hτ • nd)) ∧

          (∀ nd ∈ N, S nd = (An nd).dom) ∧

          (∀ nd ∈ N, ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers →
            (IntermediateField.inclusion hle f : ↥(fieldBar q M')) ∈ (Rx nd).integers) ∧

          (∀ nd ∈ N, ∃ j : modularFunctionFieldC (ResidueField A) M' →+* FIx nd,
            (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
              ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ (Rx nd).integers,
                (Rx nd).residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
            ∀ g : modularFunctionFieldC (ResidueField A) M',
              g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
                j g ∈ (bx nd).toValuationSubring)))) :
    (∀ Q ∈ N, ∀ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
          (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          ¬ (
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S) ∧
            (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧
            (∀ a : ↥A, ((φ (Polynomial.C a) : ↥(S)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φ Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S)) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) ∧

          (∀ P ∈ D, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))))) := by
  classical
  intro x hx S φ χ₀ D hpc
  obtain ⟨An, hA1, hA2, hA3, hA4, hA5, hnodes⟩ := hK
  obtain ⟨FIx, iF, iA, Rx, bx, Λ, C', hC'A, iD, iDVR, ϖ', l₀, Wc, iCR, iDom, iDVR2, iAdic, πW, E, E₀,
      Snd, 𝒩, 𝒩₀, hloc, hnoe, cx, cy, cu, n1, n2, n3, n4, n5, n6, n7, n8, n9₂, hHasse, n10, n11, n12, n13, nTIE, n14, n15⟩ := hnodes

  have n9 :
          (∀ nd ∈ N,

            (bx nd).IsRational ∧ nd.IsRational ∧ (∀ P ∈ Snd nd, P.IsRational) ∧

            (∀ f : fieldBar q M', f ∈ 𝒩 nd ↔ f ∈ (Rx nd).integers ∧ f ∈ R.integers ∧ ∀ P ∈ Snd nd, f ∈ P.toValuationSubring) ∧
            (∀ f ∈ 𝒩 nd, ∀ P ∈ Snd nd, P.evalAt f ∈ A) ∧

            cx nd * cy nd = algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l₀ : ↥(C' l₀)) : AlgebraicClosure ℚ) ^ E₀ * cu nd ∧
            (∀ h₁ : cx nd ∈ (Rx nd).integers, (Rx nd).residue ⟨cx nd, h₁⟩ = 0) ∧
            (∀ h₂ : cx nd ∈ R.integers, nd.ord (R.residue ⟨cx nd, h₂⟩) = 1) ∧
            (∀ h₂ : cy nd ∈ R.integers, R.residue ⟨cy nd, h₂⟩ = 0) ∧
            (∀ h₁ : cy nd ∈ (Rx nd).integers, (bx nd).ord ((Rx nd).residue ⟨cy nd, h₁⟩) = 1) ∧

            (∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
              let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ Snd nd ↔ g • P ∈ Snd nd) ∧ g • cx nd = cx nd ∧ g • cy nd = cy nd) ∧

            (∀ f : fieldBar q M', ∃ (l : Λ) (a b : ↥(𝒩₀ nd l)), (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = (a : fieldBar q M')) ∧

            (∀ f : fieldBar q M', ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd l₀)) (b : ↥(𝒩₀ nd l₀)),
              (b : fieldBar q M') ≠ 0 ∧ f * (b : fieldBar q M') = ∑ i, c i • ((a i : ↥(𝒩₀ nd l₀)) : fieldBar q M')) ∧

            (∀ l, letI : IsLocalRing ↥(𝒩₀ nd l) := hloc nd l;
              𝒩₀ nd l₀ ≤ 𝒩₀ nd l ∧ 𝒩₀ nd l ≤ 𝒩 nd ∧
              (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ Snd nd ↔
                (∀ f : fieldBar q M', f ∈ 𝒩₀ nd l → f ∈ P.toValuationSubring) ∧
                (∀ f : ↥(𝒩₀ nd l), ¬ IsUnit f → ∃ h : P.evalAt (f : fieldBar q M') ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A)) ∧
              (∀ c : AlgebraicClosure ℚ, c ∈ C' l → algebraMap (AlgebraicClosure ℚ) (fieldBar q M') c ∈ 𝒩₀ nd l) ∧
              (∀ g : ↥(𝒩₀ nd l), ∃ (o : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (o : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l), ¬ IsUnit (g - ⟨_, h⟩)) ∧
              (∀ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (a : Fin n → ↥(𝒩₀ nd l)), LinearIndependent ↥(C' l) c →
                ∑ i, c i • ((a i : ↥(𝒩₀ nd l)) : fieldBar q M') = 0 → ∀ i, a i = 0) ∧
              cx nd ∈ 𝒩₀ nd l ∧ cy nd ∈ 𝒩₀ nd l ∧ (∃ hu : cu nd ∈ 𝒩₀ nd l, IsUnit (⟨cu nd, hu⟩ : ↥(𝒩₀ nd l))) ∧
              ∃ (σ : Wc l →+* AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l))
                (ι : AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l) ≃+* UVCrossingModel (Wc l) (πW l ^ E l)),
                (∀ h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') ((ϖ' l : ↥(C' l)) : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l,
                  σ (πW l) = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ o : Wc l, ι (σ o) = const (πW l ^ E l) o) ∧
                (∀ (c : ↥(C' l)) (h : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (c : AlgebraicClosure ℚ) ∈ 𝒩₀ nd l),
                  ∃ o : Wc l, σ o = algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) ⟨_, h⟩) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₁ : f.1 ∈ (Rx nd).integers), (Rx nd).residue ⟨f.1, h₁⟩ ≠ 0 →
                  (bx nd).ord ((Rx nd).residue ⟨f.1, h₁⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
                      ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * V (πW l ^ E l) ^ n ∈
                        Ideal.span {const (πW l ^ E l) (πW l), U (πW l ^ E l)}) ∧
                (∀ (f : ↥(𝒩₀ nd l)) (n : ℕ) (h₂ : f.1 ∈ R.integers), R.residue ⟨f.1, h₂⟩ ≠ 0 →
                  nd.ord (R.residue ⟨f.1, h₂⟩) = (n : ℤ) →
                    ∃ γ : UVCrossingModel (Wc l) (πW l ^ E l), IsUnit γ ∧
                      ι (algebraMap ↥(𝒩₀ nd l) (AdicCompletion (maximalIdeal ↥(𝒩₀ nd l)) ↥(𝒩₀ nd l)) f) - γ * U (πW l ^ E l) ^ n ∈
                        Ideal.span {const (πW l ^ E l) (πW l), V (πW l ^ E l)}))) := by
    intro nd hnd
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, pl⟩ := n9₂ nd hnd
    refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, fun l => ?_⟩
    obtain ⟨P1, P2, P3, P4, P5, P6, NC, P7, P8, P9, P10⟩ := pl l
    exact ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9, P10⟩
  have hnodes15 := And.intro n1 (And.intro n2 (And.intro n3 (And.intro n4 (And.intro n5 (And.intro n6 (And.intro n7
    (And.intro n8 (And.intro n9 (And.intro n10 (And.intro n11 (And.intro n12 (And.intro n13 (And.intro n14 n15)))))))))))))
  have hpairs := ModularCurve.FullLevel.supersingularProlongation_exists_annulusPair_of_nodePresentation
    q hq M' hqM' A hA W hW hle R₀ hR₀ s π hπ hπP FSS R N FIx Rx bx Λ C' hC'A ϖ' l₀ Wc πW E E₀ Snd 𝒩 𝒩₀ hloc hnoe cx cy cu hnodes15
  obtain ⟨AnP, AnP', hdomS, hdom, hmod, hmodϖ, hm0, hparam, hrec, hfar, hnear, hrad, hm𝔪⟩ := hpairs x hx
  have htube := fun P (hP : P ∈ AnP.dom) => n11 x hx P ((hdomS P).mp hP)

  obtain ⟨hJK, a₀, ha₀, hR0, hres0, hpow, c', htc, htcu, hHall⟩ := hHasse
  obtain ⟨hC, hCres, hord⟩ := hHall x hx
  set J : ↥(fieldBar q M') := (⟨ModularCurve.jqNModC (AlgebraicClosure ℚ) q, hJK⟩ : ↥(fieldBar q M')) with hJdef
  have hJ : ((J : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) q := rfl
  set t : ↥(fieldBar q M') := (J : ↥(fieldBar q M')) - algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') a₀ with htdef
  have hJ0 : (J : ↥(fieldBar q M')) ≠ 0 := by
    intro h
    have : ((J : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [h]; rfl
    rw [hJ] at this
    exact jqNModC_ne_zero (AlgebraicClosure ℚ) q this
  have ht0 : t ≠ 0 := by
    intro h; apply hCres
    have : (⟨t, hC⟩ : ↥(Rx x).integers) = 0 := Subtype.ext h
    rw [this, map_zero]
  have hunitC : IsUnit (⟨t, hC⟩ : ↥(Rx x).integers) := (Rx x).isUnit_of_residue_ne_zero hCres
  have htC' : t⁻¹ ∈ (Rx x).integers := by
    obtain ⟨w, hw⟩ := hunitC.exists_right_inv
    have hw' : (t : ↥(fieldBar q M')) * (w : ↥(fieldBar q M')) = 1 := by
      have := congrArg Subtype.val hw; simpa using this
    rw [← eq_inv_of_mul_eq_one_right hw']; exact w.2
  have hJreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'),
      0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) → 0 ≤ P.ord (J : ↥(fieldBar q M')) :=
    fun P hP => ModularCurve.FullLevel.ord_nonneg_of_ord_jBar_nonneg_of_coe_eq_jqNModC q M' hle J hJ P hP

  have hcoeffj : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    ext k
    rw [coeffMap_coeff, coeffEmb_coeff, ← jqModC_rat, jqModC_eq_map_intCast ↥A, jqModC_eq_map_intCast ℚ,
      HahnSeries.map_coeff, HahnSeries.map_coeff]
    simp
  have hjM : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [hcoeffj]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  have hjeq : (⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) = (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) :=
    Subtype.ext hcoeffj
  obtain ⟨hjR, hjres⟩ := hR₀ (jqModC ↥A) hjM
  have hs : IsSupersingularPlace q M' (ResidueField ↥A) (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) :=
    (mem_ssPlaces_iff q M' (ResidueField ↥A)).mp ((hW _).mp s.2)
  have hsrat : (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).IsRational := hs.1
  have hcen := hs.isCentreOf_evalAt
  have hresj : R₀.residue ⟨_, hjR⟩ = jGeomGen (ResidueField ↥A) M' := by
    apply Subtype.ext
    rw [hjres, coe_jGeomGen]
    ext k
    rw [coeffMap_coeff, jqModC_eq_map_intCast (ResidueField ↥A), jqModC_eq_map_intCast ↥A,
      HahnSeries.map_coeff, HahnSeries.map_coeff]
    simp
  have hjs : (R₀.residue ⟨_, hjR⟩ : modularFunctionFieldC (ResidueField A) M') ∈
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring := by
    rw [hresj]; exact hcen.jGeomGen_mem
  have hjA0 : (⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) ≠ 0 := by
    intro h
    have h1 : R₀.residue ⟨_, hjR⟩ = 0 := by
      have : (⟨(⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')), hjR⟩ : ↥R₀.integers) = 0 := Subtype.ext h
      rw [this, map_zero]
    rw [hresj] at h1
    have := jGeomGen_sub_algebraMap_ne_zero (ResidueField ↥A) M' 0
    rw [h1, map_zero, sub_zero] at this
    exact this rfl
  have hcuspj : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord ((⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) := by
    intro P h; rw [hjeq]; exact h
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨_, hjR⟩))

  have hreg : ∀ P ∈ AnP.dom, (t : ↥(fieldBar q M')) ∈ P.toValuationSubring := by
    intro P hP
    have hjP : (IntermediateField.inclusion hle (⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ P.toValuationSubring := by
      by_contra hnot

      obtain ⟨h₁, hm₁⟩ := htube P hP (⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) hjR hcuspj hjs a ha
      have e₁ : P.evalAt (IntermediateField.inclusion hle (⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) = 0 := evalAt_of_not_mem P hnot

      have hf1 : (⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1 ∈ R₀.integers := add_mem hjR (one_mem _)
      have hcusp1 : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord ((⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1 : ↥(modularFunctionFieldBar M')) := by
        intro Q hQ
        exact Q.ord_nonneg_of_mem (add_mem (Q.mem_of_ord_nonneg hjA0 (hcuspj Q hQ)) (one_mem _))
      have hres1 : R₀.residue ⟨(⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1, hf1⟩ = R₀.residue ⟨(⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')), hjR⟩ + 1 := by
        rw [← map_one R₀.residue, ← map_add]; rfl
      have hmem1 : (R₀.residue ⟨(⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1, hf1⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring := by
        rw [hres1]; exact add_mem hjs (one_mem _)
      have heval1 : IsLocalRing.residue ↥A (a + 1) =
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨(⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1, hf1⟩) := by
        rw [map_add, map_one, hres1, evalAt_add_of_mem _ hsrat hjs (one_mem _), Place.evalAt_one]
        exact congrArg (· + 1) ha
      obtain ⟨h₂, hm₂⟩ := htube P hP ((⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1) hf1 hcusp1 hmem1 (a + 1) heval1
      have hnot1 : (IntermediateField.inclusion hle ((⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1) : ↥(fieldBar q M')) ∉ P.toValuationSubring := by
        intro hin; apply hnot
        have : (IntermediateField.inclusion hle (⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) = IntermediateField.inclusion hle ((⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1) - 1 := by
          rw [map_add, map_one, add_sub_cancel_right]
        rw [this]; exact sub_mem hin (one_mem _)
      have e₂ : P.evalAt (IntermediateField.inclusion hle ((⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1) : ↥(fieldBar q M')) = 0 := evalAt_of_not_mem P hnot1
      have k₁ : (⟨P.evalAt (IntermediateField.inclusion hle (⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) - ((a : ↥A) : AlgebraicClosure ℚ), h₁⟩ : ↥A) = -a :=
        Subtype.ext (by
          show P.evalAt (IntermediateField.inclusion hle (⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) - ((a : ↥A) : AlgebraicClosure ℚ) = ((-a : ↥A) : AlgebraicClosure ℚ)
          rw [e₁]; simp)
      have k₂ : (⟨P.evalAt (IntermediateField.inclusion hle ((⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1) : ↥(fieldBar q M')) - (((a + 1) : ↥A) : AlgebraicClosure ℚ), h₂⟩ : ↥A) = -(a + 1) :=
        Subtype.ext (by
          show P.evalAt (IntermediateField.inclusion hle ((⟨coeffMap A.subtype (jqModC ↥A), hjM⟩ : ↥(modularFunctionFieldBar M')) + 1) : ↥(fieldBar q M')) - (((a + 1) : ↥A) : AlgebraicClosure ℚ) = ((-(a + 1) : ↥A) : AlgebraicClosure ℚ)
          rw [e₂]; simp)
      rw [k₁] at hm₁
      rw [k₂] at hm₂
      have : (1 : ↥A) ∈ maximalIdeal ↥A := by
        have := (maximalIdeal ↥A).sub_mem hm₁ hm₂
        simpa using this
      exact (maximalIdeal.isMaximal ↥A).ne_top ((Ideal.eq_top_iff_one _).mpr this)
    have hjP' : 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) := by
      rw [← hjeq]; exact P.ord_nonneg_of_mem hjP
    have hJP : (J : ↥(fieldBar q M')) ∈ P.toValuationSubring := P.mem_of_ord_nonneg hJ0 (hJreg P hjP')
    exact sub_mem hJP (P.algebraMap_mem' _)

  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(fieldBar q M') :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')).1
  obtain ⟨hz, hz1, hlaw⟩ := hfar
  obtain ⟨hz', hz1', hlaw'⟩ := hnear
  have hmass := Ws33.ZC.sum_eq_ord_add_ord A (Rx x) (bx x) R x AnP AnP' hdom hm0 hrec
    hz hz1 hlaw hz' hz1' hlaw' t hC hCres c' htc htcu
  have hord0 : ∀ P ∈ AnP.dom, P.ord (t : ↥(fieldBar q M')) = 0 := by
    obtain ⟨D₀, hD₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (t : ↥(fieldBar q M')) ht0
    set D : Divisor (AlgebraicClosure ℚ) ↥(fieldBar q M') := D₀.filter (fun P => P ∈ AnP.dom) with hDdef
    have hDdom : ∀ P ∈ AnP.dom, D P = P.ord (t : ↥(fieldBar q M')) := by
      intro P hP; rw [hDdef, Finsupp.filter_apply_pos _ _ hP, hD₀]
    have hDoff : ∀ P, P ∉ AnP.dom → D P = 0 := fun P hP => by rw [hDdef, Finsupp.filter_apply_neg _ _ hP]
    have hsum := hmass D hDdom hDoff
    have hord' : x.ord (R.residue ⟨c' • t, htc⟩) = -((bx x).ord ((Rx x).residue ⟨t, hC⟩)) := hord
    rw [hord', add_neg_cancel] at hsum
    have hnn : ∀ P ∈ D.support, 0 ≤ D P := by
      intro P _
      by_cases hP : P ∈ AnP.dom
      · rw [hDdom P hP]; exact P.ord_nonneg_of_mem (hreg P hP)
      · rw [hDoff P hP]
    have hall : ∀ P ∈ D.support, D P = 0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
    intro P hP
    rw [← hDdom P hP]
    by_contra hne0
    exact hne0 (hall P (Finsupp.mem_support_iff.mpr hne0))
  have hgcF : ∀ P' : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'),
      0 ≤ P'.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) → 0 ≤ P'.ord t := by
    intro P hP
    exact P.ord_nonneg_of_mem (sub_mem (P.mem_of_ord_nonneg hJ0 (hJreg P hP)) (P.algebraMap_mem' _))
  exact ModularCurve.FullLevel.not_smoothPointPackage_of_annulusPair_attached_igusaEnd_of_testFunction_fullLevel
    q hq M' hqM' A hA W hW hle R₀ hR₀ s FSS R x (FIx x) (Rx x) (bx x) AnP AnP' hdom hmod hm0 hm𝔪 hrec ⟨hz, hz1, hlaw⟩ ⟨hz', hz1', hlaw'⟩ hrad
    htube t ht0 hgcF hR0 hres0 hC htC' hord0 S φ χ₀ D hpc

end S_ModularCurve_FullLevel_supersingularProlongation_not_smoothPointPackage_of_mem_ends_nodeCharts_hasseJ_cuspFree
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_not_smoothPointPackage_of_mem_ends_nodeCharts_hasseJ_cuspFree (solution)
