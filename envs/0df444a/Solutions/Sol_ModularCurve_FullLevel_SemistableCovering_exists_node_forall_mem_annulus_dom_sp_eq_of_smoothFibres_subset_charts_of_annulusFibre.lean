-- Prove2me | solution 1 for ModularCurve.FullLevel.SemistableCovering.exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/b9ff4c70-a5a7-5aaa-8b67-06bd803e9fe7

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_SemistableCovering_exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CategoryTheory AlgebraicGeometry

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace Ws33
namespace Reads

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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
      Place.ord_mul _ (hg a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
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
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

theorem evalAt_pow_of_mem (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp [Place.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul_of_mem hv (pow_mem hf n) hf, ih]

end Ws33.Reads

open Ws33.Reads in

theorem Ws33.residue_mem_of_attached_of_forall_mem_evalAt
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (ResidueField ↥A) Fbar)
    (hz : An.param ∈ C.integers) (hz1 : x.ord (C.residue ⟨An.param, hz⟩) = 1)
    (hlaw : ∀ (g : F) (hg : g ∈ C.integers), C.residue ⟨g, hg⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) →
      ∀ P ∈ An.dom, ∃ h : P.evalAt g * (P.evalAt An.param) ^ (-(x.ord (C.residue ⟨g, hg⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (hne : ∃ P, P ∈ An.dom)
    (f : F) (hf : f ∈ C.integers)
    (hO : ∀ P ∈ An.dom, f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A) :
    C.residue ⟨f, hf⟩ ∈ x.toValuationSubring := by
  classical
  obtain ⟨P₀, hP₀⟩ := hne
  set z := An.param with hzdef
  set v := A.valuation with hv
  have hzres : C.residue ⟨z, hz⟩ ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hz1; exact zero_ne_one hz1
  by_contra hnot
  have hfres : C.residue ⟨f, hf⟩ ≠ 0 := fun h => hnot (by rw [h]; exact zero_mem _)
  have hneg : x.ord (C.residue ⟨f, hf⟩) < 0 := by
    by_contra hge; push_neg at hge
    exact hnot (x.mem_toValuationSubring_of_ord_nonneg_alt hfres hge)
  have hf0 : f ≠ 0 := by
    intro h; apply hfres
    have : (⟨f, hf⟩ : ↥C.integers) = 0 := Subtype.ext h
    rw [this, map_zero]

  have hrat : ∀ P ∈ An.dom, P.IsRational := fun P hP => (An.mem_dom P hP).1
  have hzP : ∀ P ∈ An.dom, z ∈ P.toValuationSubring := fun P hP => (An.mem_dom P hP).2.1
  have hzPA : ∀ P ∈ An.dom, P.evalAt z ∈ A := fun P hP => (An.mem_dom P hP).2.2.1.elim fun h _ => h
  have hzPm : ∀ P (hP : P ∈ An.dom), (⟨P.evalAt z, hzPA P hP⟩ : ↥A) ∈ maximalIdeal ↥A := fun P hP => by
    obtain ⟨h, hm⟩ := (An.mem_dom P hP).2.2.1; exact hm
  have hzP0 : ∀ P ∈ An.dom, P.evalAt z ≠ 0 := fun P hP => (An.mem_dom P hP).2.2.2.1
  have hzadm : ∀ P ∈ An.dom, ∃ m ∈ maximalIdeal ↥A, ((An.modulus : ↥A) : L) = P.evalAt z * m :=
    fun P hP => (An.mem_dom P hP).2.2.2.2

  have hzinj : ∀ P ∈ An.dom, ∀ Q ∈ An.dom, P.evalAt z = Q.evalAt z → P = Q := by
    intro P hP Q hQ hPQ
    obtain ⟨R, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨Q.evalAt z, hzPA Q hQ⟩ (hzPm Q hQ) (hzP0 Q hQ) (hzadm Q hQ)
    exact (huniq P ⟨hP, hPQ⟩).trans (huniq Q ⟨hQ, rfl⟩).symm

  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0
  set Z : Finset (Place L F) := D.support.filter (fun Q => Q ∈ An.dom) with hZ
  have hZdom : ∀ Q ∈ Z, Q ∈ An.dom := fun Q hQ => (Finset.mem_filter.mp hQ).2
  have hordnn : ∀ P ∈ An.dom, 0 ≤ P.ord f := fun P hP => ord_nonneg_of_mem P (hO P hP).1
  set e : Place L F → ℕ := fun Q => (Q.ord f).toNat with he
  have he_eq : ∀ P ∈ An.dom, ((e P : ℕ) : ℤ) = P.ord f := fun P hP => Int.toNat_of_nonneg (hordnn P hP)
  have hnotZ : ∀ P ∈ An.dom, P ∉ Z → P.ord f = 0 := by
    intro P hP hPZ
    by_contra hne0
    exact hPZ (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rw [hD]; exact hne0), hP⟩)

  set w : Place L F → F := fun Q => z - algebraMap L F (Q.evalAt z) with hw
  have hwC : ∀ Q ∈ An.dom, w Q ∈ C.integers := fun Q hQ =>
    sub_mem hz ((C.algebraMap_mem_iff _).mpr (hzPA Q hQ))
  have hwres : ∀ Q (hQ : Q ∈ An.dom), C.residue ⟨w Q, hwC Q hQ⟩ = C.residue ⟨z, hz⟩ := by
    intro Q hQ
    have hsplit : (⟨w Q, hwC Q hQ⟩ : ↥C.integers) = ⟨z, hz⟩ -
        ⟨algebraMap L F ((⟨Q.evalAt z, hzPA Q hQ⟩ : ↥A) : L), (C.algebraMap_mem_iff _).mpr (hzPA Q hQ)⟩ := Subtype.ext rfl
    rw [hsplit, map_sub, C.residue_algebraMap ⟨Q.evalAt z, hzPA Q hQ⟩, (IsLocalRing.residue_eq_zero_iff _).mpr (hzPm Q hQ),
      map_zero, sub_zero]
  have hwne : ∀ Q, w Q ≠ 0 ∨ True := fun Q => Or.inr trivial
  have hword_self : ∀ Q ∈ An.dom, Q.ord (w Q) = 1 := fun Q hQ => An.ord_param_sub Q hQ
  have hwP : ∀ P ∈ An.dom, ∀ Q ∈ An.dom, w Q ∈ P.toValuationSubring := fun P hP Q hQ =>
    sub_mem (hzP P hP) (P.algebraMap_mem' _)
  have hwval : ∀ P (hP : P ∈ An.dom) Q (hQ : Q ∈ An.dom), P.evalAt (w Q) = P.evalAt z - Q.evalAt z := by
    intro P hP Q hQ
    rw [hw, evalAt_sub_of_mem P (hrat P hP) (hzP P hP) (P.algebraMap_mem' _), Place.evalAt_algebraMap_eq]
  have hword_other : ∀ P ∈ An.dom, ∀ Q ∈ An.dom, P ≠ Q → P.ord (w Q) = 0 := by
    intro P hP Q hQ hPQ
    apply ord_eq_zero_of_evalAt_ne_zero P (hwP P hP Q hQ)
    rw [hwval P hP Q hQ, sub_ne_zero]
    exact fun h => hPQ (hzinj P hP Q hQ h)
  have hw0 : ∀ Q ∈ An.dom, w Q ≠ 0 := by
    intro Q hQ h
    have := hword_self Q hQ
    rw [h, Place.ord_zero] at this
    exact zero_ne_one this

  set wC : Place L F → ↥C.integers := fun Q => if hQ : Q ∈ An.dom then ⟨w Q, hwC Q hQ⟩ else 1 with hwCdef
  have hwC_eq : ∀ Q (hQ : Q ∈ An.dom), wC Q = ⟨w Q, hwC Q hQ⟩ := fun Q hQ => by simp [hwCdef, hQ]
  set hC : ↥C.integers := ∏ Q ∈ Z, (wC Q) ^ (e Q) with hhC
  set h : F := (hC : F) with hhdef
  have hh_eq : h = ∏ Q ∈ Z, (w Q) ^ (e Q) := by
    rw [hhdef, hhC]
    push_cast
    refine Finset.prod_congr rfl fun Q hQ => ?_
    rw [hwC_eq Q (hZdom Q hQ)]
  set E : ℕ := ∑ Q ∈ Z, e Q with hE
  have hhres : C.residue hC = C.residue ⟨z, hz⟩ ^ E := by
    rw [hhC, map_prod]
    simp_rw [map_pow]
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun Q hQ => ?_
    rw [hwC_eq Q (hZdom Q hQ), hwres Q (hZdom Q hQ)]
  have hhres0 : C.residue hC ≠ 0 := by rw [hhres]; exact pow_ne_zero _ hzres
  have hhunit : IsUnit hC := by
    by_contra hnu
    apply hhres0
    have : hC ∈ maximalIdeal ↥C.integers := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← C.ker_residue] at this
    exact this
  obtain ⟨uC, huC⟩ := hhunit
  have hh0 : h ≠ 0 := by
    rw [hh_eq]; exact Finset.prod_ne_zero_iff.mpr fun Q hQ => pow_ne_zero _ (hw0 Q (hZdom Q hQ))

  set gC : ↥C.integers := ⟨f, hf⟩ * ((uC⁻¹ : (↥C.integers)ˣ) : ↥C.integers) with hgC
  set g : F := (gC : F) with hgdef
  have hginv : ((uC⁻¹ : (↥C.integers)ˣ) : ↥C.integers) * hC = 1 := by rw [← huC]; exact uC.inv_mul
  have hg_mul_h : g * h = f := by
    rw [hgdef, hgC, hhdef]
    have := congrArg Subtype.val (show (⟨f, hf⟩ * ((uC⁻¹ : (↥C.integers)ˣ) : ↥C.integers)) * hC = ⟨f, hf⟩ by
      rw [mul_assoc, hginv, mul_one])
    simpa using this
  have hg_eq : g = f * h⁻¹ := by rw [← hg_mul_h, mul_assoc, mul_inv_cancel₀ hh0, mul_one]
  have hgres_mul : C.residue gC * C.residue hC = C.residue ⟨f, hf⟩ := by
    rw [← map_mul, hgC, mul_assoc, hginv, mul_one]
  have hgres : C.residue gC ≠ 0 := fun h0 => hfres (by rw [← hgres_mul, h0, zero_mul])
  have hordg : x.ord (C.residue gC) = x.ord (C.residue ⟨f, hf⟩) - E := by
    have := congrArg x.ord hgres_mul
    rw [Place.ord_mul _ hgres hhres0, hhres, ← zpow_natCast, Place.ord_zpow, hz1, mul_one] at this
    omega

  have hordh : ∀ P ∈ An.dom, P.ord h = P.ord f := by
    intro P hP
    rw [hh_eq, ord_finset_prod P Z _ (fun Q hQ => pow_ne_zero _ (hw0 Q (hZdom Q hQ)))]
    simp_rw [← zpow_natCast, Place.ord_zpow]
    by_cases hPZ : P ∈ Z
    · rw [Finset.sum_eq_single_of_mem P hPZ (fun Q hQ hQP => by rw [hword_other P hP Q (hZdom Q hQ) (Ne.symm hQP), mul_zero]),
        hword_self P hP, mul_one, he_eq P hP]
    · rw [Finset.sum_eq_zero (fun Q hQ => by rw [hword_other P hP Q (hZdom Q hQ) (fun h => hPZ (h ▸ hQ)), mul_zero]),
        hnotZ P hP hPZ]
  have hgord : ∀ P ∈ An.dom, P.ord g = 0 := by
    intro P hP
    rw [hg_eq, Place.ord_mul _ hf0 (inv_ne_zero hh0), Place.ord_inv, hordh P hP]
    ring

  have law := hlaw g gC.2 (by rw [show (⟨g, gC.2⟩ : ↥C.integers) = gC from Subtype.ext rfl]; exact hgres) hgord

  set Z₀ : Finset (Place L F) := insert P₀ Z with hZ₀
  have hZ₀dom : ∀ Q ∈ Z₀, Q ∈ An.dom := by
    intro Q hQ; rcases Finset.mem_insert.mp hQ with rfl | hQ
    · exact hP₀
    · exact hZdom Q hQ
  obtain ⟨Qm, hQm, hmax⟩ := Finset.exists_max_image Z₀ (fun Q => v (Q.evalAt z)) ⟨P₀, Finset.mem_insert_self _ _⟩
  have hQmdom := hZ₀dom Qm hQm
  set b : L := Qm.evalAt z with hb
  obtain ⟨cs, hcs⟩ := IsAlgClosed.exists_eq_mul_self b
  have hb0 : b ≠ 0 := hzP0 Qm hQmdom
  have hvb1 : v b < 1 := (A.valuation_lt_one_iff ⟨b, hzPA Qm hQmdom⟩).mp (hzPm Qm hQmdom)
  have hcs0 : cs ≠ 0 := by rintro rfl; exact hb0 (by rw [hcs, mul_zero])
  have hvcs0 : v cs ≠ 0 := (Valuation.ne_zero_iff _).mpr hcs0
  have hvcs1 : v cs < 1 := by
    by_contra hge; push_neg at hge
    have : 1 ≤ v b := by rw [hcs, map_mul]; exact one_le_mul hge hge
    exact absurd hvb1 (not_lt.mpr this)
  have hvb_lt : v b < v cs := by
    rw [hcs, map_mul]
    calc v cs * v cs < 1 * v cs := mul_lt_mul_of_pos_right hvcs1 (lt_of_le_of_ne zero_le' hvcs0.symm)
      _ = v cs := one_mul _
  have hcsA : cs ∈ A := (A.valuation_le_one_iff cs).mp hvcs1.le
  have hcsm : (⟨cs, hcsA⟩ : ↥A) ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff ⟨cs, hcsA⟩).mpr hvcs1
  have hcsadm : ∃ m ∈ maximalIdeal ↥A, ((An.modulus : ↥A) : L) = cs * m := by
    obtain ⟨m₀, hm₀, hmod⟩ := hzadm Qm hQmdom
    refine ⟨⟨cs, hcsA⟩ * m₀, Ideal.mul_mem_left _ _ hm₀, ?_⟩
    rw [hmod, ← hb, hcs]; push_cast; ring
  obtain ⟨Ps, ⟨hPs, hPsv⟩, -⟩ := An.existsUnique_evalAt_eq ⟨cs, hcsA⟩ hcsm hcs0 hcsadm
  have hPsv' : Ps.evalAt z = cs := hPsv

  have hvwPs : ∀ Q ∈ Z, v (Ps.evalAt (w Q)) = v cs := by
    intro Q hQ
    have hlt : v (Q.evalAt z) < v cs := lt_of_le_of_lt (hmax Q (Finset.mem_insert_of_mem hQ)) hvb_lt
    rw [hwval Ps hPs Q (hZdom Q hQ), hPsv', sub_eq_add_neg,
      Valuation.map_add_of_distinct_val v (by rw [Valuation.map_neg]; exact (ne_of_gt hlt)), Valuation.map_neg,
      max_eq_left hlt.le]
  have hvhPs : v (Ps.evalAt h) = v cs ^ E := by
    rw [hh_eq, evalAt_finset_prod_of_mem Ps (hrat Ps hPs) Z _ (fun Q hQ => pow_mem (hwP Ps hPs Q (hZdom Q hQ)) _),
      map_prod, hE, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun Q hQ => ?_
    rw [evalAt_pow_of_mem Ps (hrat Ps hPs) (hwP Ps hPs Q (hZdom Q hQ)), map_pow, hvwPs Q hQ]

  obtain ⟨hgA, hgU⟩ := law Ps hPs
  have hgres_eq : C.residue ⟨g, gC.2⟩ = C.residue gC := rfl
  have hvg : v (Ps.evalAt g) = v cs ^ (x.ord (C.residue gC)) := by
    have e1 : v (Ps.evalAt g * Ps.evalAt An.param ^ (-(x.ord (C.residue ⟨g, gC.2⟩)))) = 1 :=
      (A.valuation_eq_one_iff _).mp hgU
    rw [map_mul, map_zpow₀, ← hzdef, hPsv', hgres_eq] at e1
    rw [eq_inv_of_mul_eq_one_left e1, zpow_neg, inv_inv]

  have hg0 : g ≠ 0 := by rw [hg_eq]; exact mul_ne_zero hf0 (inv_ne_zero hh0)
  have hgPs : g ∈ Ps.toValuationSubring := Ps.mem_toValuationSubring_of_ord_nonneg_alt hg0 (hgord Ps hPs).ge
  have hhPs : h ∈ Ps.toValuationSubring :=
    hh_eq ▸ prod_mem_valuationSubring Ps Z _ (fun Q hQ => pow_mem (hwP Ps hPs Q (hZdom Q hQ)) _)
  have hvf : v (Ps.evalAt f) = v cs ^ (x.ord (C.residue ⟨f, hf⟩)) := by
    have hfe : Ps.evalAt f = Ps.evalAt g * Ps.evalAt h := by
      rw [← Ps.evalAt_mul_of_mem (hrat Ps hPs) hgPs hhPs, hg_mul_h]
    rw [hfe, map_mul, hvg, hvhPs, hordg, ← zpow_natCast, ← zpow_add₀ hvcs0]
    congr 1; omega
  have hvf1 : v (Ps.evalAt f) ≤ 1 := (A.valuation_le_one_iff _).mpr (hO Ps hPs).2
  set m : ℕ := (-(x.ord (C.residue ⟨f, hf⟩))).toNat with hm
  have hm_eq : (m : ℤ) = -(x.ord (C.residue ⟨f, hf⟩)) := Int.toNat_of_nonneg (by omega)
  have hm0 : m ≠ 0 := by intro h0; rw [h0] at hm_eq; simp at hm_eq; omega
  have hpow : v cs ^ (x.ord (C.residue ⟨f, hf⟩)) = (v cs ^ m)⁻¹ := by
    rw [← zpow_natCast, ← zpow_neg]; congr 1; omega
  rw [hvf, hpow] at hvf1
  have hlt1 : v cs ^ m < 1 := pow_lt_one₀ zero_le' hvcs1 hm0
  have hpos : 0 < v cs ^ m := pow_pos (lt_of_le_of_ne zero_le' hvcs0.symm) m
  exact absurd ((inv_le_one₀ hpos).mp hvf1) (not_le.mpr hlt1)

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : (A : Set (AlgebraicClosure ℚ)) ≠ Set.univ)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (𝒞 : SemistableCovering q M' A W)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : ↥(fieldBar q M') ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : AlgebraicClosure ℚ)) =
      SemistableModel.baseToFunctionField toBase a)

    (pt sp : Place (AlgebraicClosure ℚ) ↥(fieldBar q M') → X)
    (hpt : ∀ P, SemistableModel.localRing X φ (pt P) = P.toValuationSubring.toSubring ∧ (toBase.base (pt P)).asIdeal = ⊥)
    (hsp : ∀ P, pt P ⤳ sp P ∧ sp P ≠ pt P ∧ toBase.base (sp P) = closedPoint ↥A ∧ (∀ y : X, sp P ⤳ y → y = sp P) ∧
      (∀ y : X, pt P ⤳ y → y = pt P ∨ y = sp P) ∧
      ∀ f : ↥(fieldBar q M'), f ∈ SemistableModel.localRing X φ (sp P) →
        f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
          (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ (sp P), f * g = 1))

    (gen : CuspidalType.ProjLine q ⊕ ↥W → X)
    (hgenI : ∀ ℓ, SemistableModel.localRing X φ (gen (Sum.inl ℓ)) = (𝒞.CIg ℓ).integers.toSubring)
    (hgenS : ∀ s, SemistableModel.localRing X φ (gen (Sum.inr s)) = (𝒞.CSS s).integers.toSubring)
    (hgen_sp : ∀ i, toBase.base (gen i) = closedPoint ↥A)
    (hgen : ∀ x : X, toBase.base x = closedPoint ↥A → ((∃ i, x = gen i) ↔ ∃ y : X, x ⤳ y ∧ y ≠ x))

    (hnode : ∀ x : X, toBase.base x = closedPoint ↥A → (∀ y : X, x ⤳ y → y = x) → x ∉ toBase.smoothLocus →
      ∃ i j, i ≠ j ∧ gen i ⤳ x ∧ gen j ⤳ x ∧ (∀ k, gen k ⤳ x → k = i ∨ k = j) ∧
      ∃ (t₁ t₂ u u' : ↥(fieldBar q M')) (μ : ↥A), μ ∈ maximalIdeal ↥A ∧ (μ : AlgebraicClosure ℚ) ≠ 0 ∧
        t₁ ∈ SemistableModel.localRing X φ x ∧ t₂ ∈ SemistableModel.localRing X φ x ∧
        u ∈ SemistableModel.localRing X φ x ∧ u' ∈ SemistableModel.localRing X φ x ∧ u * u' = 1 ∧
        (¬ ∃ g ∈ SemistableModel.localRing X φ x, t₁ * g = 1) ∧ (¬ ∃ g ∈ SemistableModel.localRing X φ x, t₂ * g = 1) ∧
        t₁ * t₂ = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (μ : AlgebraicClosure ℚ) * u ∧

        (∃ g ∈ SemistableModel.localRing X φ (gen i), t₁ * g = 1) ∧ (∃ g ∈ SemistableModel.localRing X φ (gen j), t₂ * g = 1))

    (hAnSp : ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ∃ x : X,
      x ∉ toBase.smoothLocus ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
      gen (Sum.inl ℓ) ⤳ x ∧ gen (Sum.inr s) ⤳ x ∧ ∀ P, P ∈ (𝒞.An ℓ s).dom → sp P = x) :
    ∀ (ℓ : CuspidalType.ProjLine q) (s : ↥W), ∃ x : X,
      x ∉ toBase.smoothLocus ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
      (∀ P, P ∈ (𝒞.An ℓ s).dom → sp P = x) ∧
      gen (Sum.inl ℓ) ⤳ x ∧ gen (Sum.inr s) ⤳ x ∧
      (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (𝒞.CIg ℓ).integers), f ∈ SemistableModel.localRing X φ x →
        (𝒞.CIg ℓ).residue ⟨f, hf⟩ ∈ (𝒞.xs ℓ s).toValuationSubring) ∧
      (∀ (f : ↥(fieldBar q M')) (hf : f ∈ (𝒞.CSS s).integers), f ∈ SemistableModel.localRing X φ x →
        (𝒞.CSS s).residue ⟨f, hf⟩ ∈ (𝒞.xt ℓ s).toValuationSubring) := by
  classical
  intro ℓ s

  obtain ⟨P₀, hP₀⟩ : ∃ P, P ∈ (𝒞.An ℓ s).dom := by

    have hmod := (𝒞.An ℓ s).modulus_mem
    by_cases hμ : (((𝒞.An ℓ s).modulus : ↥A) : AlgebraicClosure ℚ) = 0
    ·
      obtain ⟨x, hx⟩ : ∃ x : AlgebraicClosure ℚ, x ∉ (A : Set (AlgebraicClosure ℚ)) := by
        by_contra h
        push_neg at h
        exact hA (Set.eq_univ_iff_forall.mpr h)
      have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0]; exact A.zero_mem)
      have hxv : ¬ A.valuation x ≤ 1 := fun h => hx ((A.valuation_le_one_iff x).mp h)
      have hci : x⁻¹ ∈ A := by
        rw [← SetLike.mem_coe]
        exact (A.valuation_le_one_iff x⁻¹).mp (by rw [map_inv₀]; exact le_of_lt (inv_lt_one_of_one_lt₀ (lt_of_not_ge hxv)))
      have hcm : (⟨x⁻¹, hci⟩ : ↥A) ∈ maximalIdeal ↥A := by
        rw [ValuationSubring.valuation_lt_one_iff]
        show A.valuation x⁻¹ < 1
        rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ (lt_of_not_ge hxv)
      obtain ⟨P, hP, -⟩ := ((𝒞.An ℓ s).existsUnique_evalAt_eq ⟨x⁻¹, hci⟩ hcm (by simpa using inv_ne_zero hx0)
        ⟨0, Ideal.zero_mem _, by simp [hμ]⟩).exists
      exact ⟨P, hP⟩
    ·
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_eq_mul_self (((𝒞.An ℓ s).modulus : ↥A) : AlgebraicClosure ℚ)
      have hc0 : c ≠ 0 := by rintro rfl; exact hμ (by rw [hc, mul_zero])
      have hμle : A.valuation (((𝒞.An ℓ s).modulus : ↥A) : AlgebraicClosure ℚ) < 1 :=
        (ValuationSubring.valuation_lt_one_iff A _).mp hmod
      have hcv : A.valuation c < 1 := by
        have h2 : A.valuation c * A.valuation c < 1 := by rw [← map_mul, ← hc]; exact hμle
        by_contra hge
        push_neg at hge
        exact absurd h2 (not_lt.mpr (by simpa using mul_le_mul' hge hge))
      have hcA : c ∈ A := by
        rw [← SetLike.mem_coe]; exact (A.valuation_le_one_iff c).mp hcv.le
      have hcm : (⟨c, hcA⟩ : ↥A) ∈ maximalIdeal ↥A := (ValuationSubring.valuation_lt_one_iff A _).mpr hcv
      obtain ⟨P, hP, -⟩ := ((𝒞.An ℓ s).existsUnique_evalAt_eq ⟨c, hcA⟩ hcm (by simpa using hc0)
        ⟨⟨c, hcA⟩, hcm, by simpa using hc⟩).exists
      exact ⟨P, hP⟩

  obtain ⟨x, hxns, hxsp, hxcl, h2b, h2b', h2a⟩ := hAnSp ℓ s

  obtain ⟨hcurve, -⟩ :=
    ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(fieldBar q M') := hcurve
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(fieldBar q M') := IsCurveOver.hasPrincipalDivisors

  have hO : ∀ P, P ∈ (𝒞.An ℓ s).dom → ∀ f : ↥(fieldBar q M'), f ∈ SemistableModel.localRing X φ x →
      f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A := by
    intro P hP f hfx
    have hfx' : f ∈ SemistableModel.localRing X φ (sp P) := by rw [h2a P hP]; exact hfx
    obtain ⟨hmem, hA, -⟩ := (hsp P).2.2.2.2.2 f hfx'
    exact ⟨hmem, hA⟩
  refine ⟨x, hxns, hxsp, hxcl, h2a, h2b, h2b', ?_, ?_⟩
  ·
    intro f hf hfx
    obtain ⟨-, hz, hz1, hlaw⟩ := (𝒞.isAttached ℓ s).1
    exact Ws33.residue_mem_of_attached_of_forall_mem_evalAt A (𝒞.An ℓ s) (𝒞.CIg ℓ) (𝒞.xs ℓ s) hz hz1 hlaw
      ⟨P₀, hP₀⟩ f hf (fun P hP => hO P hP f hfx)
  ·
    intro f hf hfx
    obtain ⟨-, hz, hz1, hlaw⟩ := (𝒞.isAttached ℓ s).2
    have hdom := 𝒞.dom_eq ℓ s
    exact Ws33.residue_mem_of_attached_of_forall_mem_evalAt A (𝒞.An' ℓ s) (𝒞.CSS s) (𝒞.xt ℓ s) hz hz1 hlaw
      ⟨P₀, by rw [hdom]; exact hP₀⟩ f hf (fun P hP => hO P (by rw [← hdom]; exact hP) f hfx)

end S_ModularCurve_FullLevel_SemistableCovering_exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre
end P2MW
export P2MW.S_ModularCurve_FullLevel_SemistableCovering_exists_node_forall_mem_annulus_dom_sp_eq_of_smoothFibres_subset_charts_of_annulusFibre (solution)
