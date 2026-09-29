-- Prove2me | solution 1 for ModularCurve.exists_chartData_of_lineResidues
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f035ef38-167a-540f-aabd-9e61f165e114

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_evalAt_placeOfPoint_algebraMap
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_evalAt_placeInfty_eq
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_algebraMap_polynomial_mem_of_ne_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_chartData_of_lineResidues
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

namespace LineResidues

section Generic

open Classical

variable
    {A : ValuationSubring (AlgebraicClosure ℚ)} [DecidableEq (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] [HasPrincipalDivisors (AlgebraicClosure ℚ) F]
    (hFrat : ∀ P : Place (AlgebraicClosure ℚ) F, P.IsRational)
    (C : ComponentChart A F ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
    {r : ℕ} (s : Fin r → F) (hint : ∀ l, s l ∈ C.integers) (hunit : ∀ l, C.residue ⟨s l, hint l⟩ ≠ 0)

    (D : Polynomial (IsLocalRing.ResidueField ↥A)) (R : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)) (hD : D ≠ 0)
    (hR : ∀ l, (C.residue ⟨s l, hint l⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D
      = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R l))

    (c₀ : Place (AlgebraicClosure ℚ) F) (hc₀ : c₀ ∈ C.dom)
    (hc₀inf : C.placeMap c₀ = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
    (hreg₀ : ∀ P ∈ C.dom, P ≠ c₀ → ∀ l, s l ∈ P.toValuationSubring)

    (hdom : ∀ P ∈ C.dom, (∃ x₀ : IsLocalRing.ResidueField ↥A, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ ∧ D.eval x₀ ≠ 0) ∨
      C.placeMap P = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))

    (hcusp : ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) F, (∀ W, E W = W.ord f) →
        Finsupp.mapDomain C.placeMap
            (E.filter (fun W => W ∈ C.dom ∧ C.placeMap W = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))))
            (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
          = (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (C.residue ⟨f, hf⟩))

    (c i : IsLocalRing.ResidueField ↥A → Fin r) (H : Finset (Fin r))
    (hcx : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → (R (c x₀)).eval x₀ ≠ 0)
    (hix : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      (R (i x₀) * Polynomial.C ((R (c x₀)).eval x₀) - R (c x₀) * Polynomial.C ((R (i x₀)).eval x₀)).rootMultiplicity x₀ = 1)
    (hsepx : ∀ P ∈ C.dom, ∀ Q ∈ C.dom, ∀ x₀ y₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → C.placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) y₀ → x₀ ≠ y₀ →
      ∃ a b, (R a).eval x₀ * (R b).eval y₀ ≠ (R b).eval x₀ * (R a).eval y₀)
    (hHx : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → ∃ l ∈ H, (R l).eval x₀ ≠ 0)

    (cInf iInf : Fin r) (hcInf : ∀ l, (R l).natDegree ≤ (R cInf).natDegree) (hcInfD : D.natDegree ≤ (R cInf).natDegree) (hcInfH : cInf ∈ H)
    (hpole : ∀ l, -(((R cInf).natDegree - D.natDegree : ℕ) : ℤ) ≤ c₀.ord (s l))
    (hiInf : (R iInf - Polynomial.C ((R iInf).coeff (R cInf).natDegree / (R cInf).leadingCoeff) * R cInf).natDegree + 1
      = (R cInf).natDegree)
    (hiInf0 : R iInf - Polynomial.C ((R iInf).coeff (R cInf).natDegree / (R cInf).leadingCoeff) * R cInf ≠ 0)
    (hsepInf : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      ∃ a b, (R a).eval x₀ * ((R b).coeff (R cInf).natDegree / (R cInf).leadingCoeff)
        ≠ (R b).eval x₀ * ((R a).coeff (R cInf).natDegree / (R cInf).leadingCoeff))

theorem line_evalAt_congrRingEquiv {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F ≃+* F') (he : ∀ a, e (algebraMap K F a) = algebraMap K F' a) (v : Place K F) (hv : v.IsRational)
    (f : F) (hf : f ∈ v.toValuationSubring) :
    (Place.congrRingEquiv e he v).evalAt (e f) = v.evalAt f := by
  have hf' : e f ∈ (Place.congrRingEquiv e he v).toValuationSubring := by
    rw [Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
    show e.symm (e f) ∈ v.toValuationSubring
    rw [e.symm_apply_apply]; exact hf
  have hcomm : ∀ a : K, algebraMap K (Place.congrRingEquiv e he v).ResidueField a
      = Place.congrResidueAlgEquiv e he v (algebraMap K v.ResidueField a) :=
    fun a => ((Place.congrResidueAlgEquiv e he v).commutes a).symm
  have hv' : (Place.congrRingEquiv e he v).IsRational := by
    intro y
    obtain ⟨a, ha⟩ := hv ((Place.congrResidueAlgEquiv e he v).symm y)
    exact ⟨a, by rw [hcomm, ha, AlgEquiv.apply_symm_apply]⟩
  apply Place.algebraMap_residueField_injective (Place.congrRingEquiv e he v)
  rw [Place.algebraMap_evalAt _ hv' hf', hcomm, Place.algebraMap_evalAt _ hv hf]
  show _ = IsLocalRing.ResidueField.mapEquiv (Place.comapSymmRingEquiv e v.toValuationSubring)
    (IsLocalRing.residue _ ⟨f, hf⟩)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  congr 1

theorem line_mem_congrRingEquiv_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F ≃+* F') (he : ∀ a, e (algebraMap K F a) = algebraMap K F' a) (v : Place K F) (f : F) :
    e f ∈ (Place.congrRingEquiv e he v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
  show e.symm (e f) ∈ v.toValuationSubring ↔ _
  rw [e.symm_apply_apply]

set_option synthInstance.maxHeartbeats 1600000 in

theorem line_ratFuncEquivCharLOneC_algebraMap (Q : Polynomial (IsLocalRing.ResidueField ↥A)) :
    ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A) (algebraMap (Polynomial (IsLocalRing.ResidueField ↥A)) (RatFunc (IsLocalRing.ResidueField ↥A)) Q)
      = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q := by
  show ((RatFunc.algEquivOfTranscendental (jqModC (IsLocalRing.ResidueField ↥A)) (ModularCurve.transcendental_jqModC (IsLocalRing.ResidueField ↥A))).trans
    (IntermediateField.equivOfEq (modularFunctionFieldC_one (IsLocalRing.ResidueField ↥A)).symm)) (algebraMap _ _ Q) = _
  rw [AlgEquiv.trans_apply, RatFunc.algEquivOfTranscendental_algebraMap, ← Polynomial.aeval_algHom_apply]
  congr 1

theorem line_toRingEquiv_algebraMap (Q : Polynomial (IsLocalRing.ResidueField ↥A)) :
    (ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A)).toRingEquiv (algebraMap (Polynomial (IsLocalRing.ResidueField ↥A)) (RatFunc (IsLocalRing.ResidueField ↥A)) Q)
      = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q :=
  line_ratFuncEquivCharLOneC_algebraMap Q

theorem line_charLGeomPlaceOfPoint_eq (x₀ : IsLocalRing.ResidueField ↥A) :
    charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ = Place.congrRingEquiv (ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A)).toRingEquiv
      (fun a => (ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A)).commutes a) (RationalFunctionField.placeOfPoint (IsLocalRing.ResidueField ↥A) x₀) := rfl

theorem line_charLGeomPlaceEquiv_eq (v : Place (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A))) :
    charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) v = Place.congrRingEquiv (ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A)).toRingEquiv
      (fun a => (ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A)).commutes a) v := rfl

theorem line_placeOfPoint_ne_placeInfty (x₀ : IsLocalRing.ResidueField ↥A) :
    RationalFunctionField.placeOfPoint (IsLocalRing.ResidueField ↥A) x₀ ≠ RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A) := by
  intro h
  rw [RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum] at h
  exact ((AlgebraicCurve.RationalFunctionField.eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum _).mp h) _ rfl

theorem line_isRational_ratFunc (v : Place (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A))) : v.IsRational :=
  AlgebraicCurve.Place.isRational_of_isAlgClosed v

theorem ord_pt_aeval (Q : Polynomial (IsLocalRing.ResidueField ↥A)) (hQ : Q ≠ 0) (x₀ : IsLocalRing.ResidueField ↥A) :
    (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀).ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = (Q.rootMultiplicity x₀ : ℤ) := by
  rw [line_charLGeomPlaceOfPoint_eq, ← line_toRingEquiv_algebraMap, Place.ord_congrRingEquiv,
    AlgebraicCurve.RationalFunctionField.ord_placeOfPoint_algebraMap x₀ hQ]

theorem aeval_mem_pt (Q : Polynomial (IsLocalRing.ResidueField ↥A)) (x₀ : IsLocalRing.ResidueField ↥A) :
    (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ∈ (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀).toValuationSubring := by
  rw [line_charLGeomPlaceOfPoint_eq, ← line_toRingEquiv_algebraMap, line_mem_congrRingEquiv_iff]
  exact AlgebraicCurve.RationalFunctionField.algebraMap_polynomial_mem_of_ne_placeInfty _
    (line_placeOfPoint_ne_placeInfty x₀) Q

theorem evalAt_pt_aeval (Q : Polynomial (IsLocalRing.ResidueField ↥A)) (x₀ : IsLocalRing.ResidueField ↥A) :
    (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀).evalAt (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = Q.eval x₀ := by
  rw [line_charLGeomPlaceOfPoint_eq, ← line_toRingEquiv_algebraMap,
    line_evalAt_congrRingEquiv _ _ _ (line_isRational_ratFunc _) _
      (AlgebraicCurve.RationalFunctionField.algebraMap_polynomial_mem_of_ne_placeInfty _ (line_placeOfPoint_ne_placeInfty x₀) Q),
    AlgebraicCurve.RationalFunctionField.evalAt_placeOfPoint_algebraMap]

theorem ord_inf_aeval (Q : Polynomial (IsLocalRing.ResidueField ↥A)) (hQ : Q ≠ 0) :
    (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = -(Q.natDegree : ℤ) := by
  rw [line_charLGeomPlaceEquiv_eq, ← line_toRingEquiv_algebraMap, Place.ord_congrRingEquiv,
    AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap hQ]

theorem evalAt_inf_aeval_div (Q Q' : Polynomial (IsLocalRing.ResidueField ↥A)) (hQ' : Q' ≠ 0) (h : Q.natDegree ≤ Q'.natDegree) :
    (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) * (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q')⁻¹
        ∈ (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).toValuationSubring ∧
    (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).evalAt ((Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) * (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q')⁻¹)
      = Q.coeff Q'.natDegree / Q'.leadingCoeff := by
  set k := IsLocalRing.ResidueField ↥A
  set e := ratFuncEquivCharLOneC k with he_def
  set f : RatFunc k := algebraMap (Polynomial k) (RatFunc k) Q / algebraMap (Polynomial k) (RatFunc k) Q' with hf
  have hx : (Polynomial.aeval (jBar k) Q : ↥(modularFunctionFieldC k 1)) * (Polynomial.aeval (jBar k) Q')⁻¹ = e.toRingEquiv f := by
    rw [hf, div_eq_mul_inv, map_mul, map_inv₀, line_toRingEquiv_algebraMap, line_toRingEquiv_algebraMap]
  have hQ'0 : algebraMap (Polynomial k) (RatFunc k) Q' ≠ 0 := RatFunc.algebraMap_ne_zero hQ'

  have hdeg : ∀ P : Polynomial k, P ≠ 0 →
      (algebraMap (Polynomial k) (RatFunc k) P / algebraMap (Polynomial k) (RatFunc k) Q').intDegree
        = (P.natDegree : ℤ) - Q'.natDegree := by
    intro P hP
    rw [div_eq_mul_inv, RatFunc.intDegree_mul (RatFunc.algebraMap_ne_zero hP) (inv_ne_zero hQ'0),
      RatFunc.intDegree_inv, RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
    ring

  have hmem : f ∈ (RationalFunctionField.placeInfty k).toValuationSubring := by
    by_cases hQ0 : Q = 0
    · rw [hf, hQ0, map_zero, zero_div]; exact zero_mem _
    · have hf0 : f ≠ 0 := div_ne_zero (RatFunc.algebraMap_ne_zero hQ0) hQ'0
      rw [RationalFunctionField.placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
        RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero _ hf0, ← WithZero.exp_zero,
        WithZero.exp_le_exp, hf, hdeg Q hQ0]
      omega
  rw [hx, line_charLGeomPlaceEquiv_eq]
  refine ⟨(line_mem_congrRingEquiv_iff _ _ _ _).mpr hmem, ?_⟩
  rw [line_evalAt_congrRingEquiv _ _ _ (line_isRational_ratFunc _) _ hmem]

  apply AlgebraicCurve.RationalFunctionField.evalAt_placeInfty_eq
  set c : k := Q.coeff Q'.natDegree / Q'.leadingCoeff with hc
  set P : Polynomial k := Q - Polynomial.C c * Q' with hP
  have hCc : algebraMap k (RatFunc k) c = algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c) := by
    rw [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
  have hfc : f - algebraMap k (RatFunc k) c = algebraMap (Polynomial k) (RatFunc k) P / algebraMap (Polynomial k) (RatFunc k) Q' := by
    rw [hCc, hP, map_sub, map_mul, sub_div, mul_div_assoc, div_self hQ'0, mul_one, hf]
  by_cases hP0 : P = 0
  · left
    rw [hfc, hP0, map_zero, zero_div]
  · right
    rw [hfc, hdeg P hP0]
    have hPdeg : P.natDegree < Q'.natDegree := by
      rw [Polynomial.natDegree_lt_iff_degree_lt hP0, Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      rw [hP, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases lt_or_eq_of_le hm with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt h hlt),
          Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero, sub_zero]
      · rw [← heq, hc, Polynomial.coeff_natDegree, div_mul_cancel₀ _ (Polynomial.leadingCoeff_ne_zero.mpr hQ'), sub_self]
    omega

theorem aeval_ne_zero_iff (Q : Polynomial (IsLocalRing.ResidueField ↥A)) :
    (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ≠ 0 ↔ Q ≠ 0 := by
  rw [not_iff_not]
  constructor
  · intro h
    have h3 : Polynomial.aeval (jqModC (IsLocalRing.ResidueField ↥A)) Q
        = (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1).val
            (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) Q) :=
      Polynomial.aeval_algHom_apply (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1).val
        (jBar (IsLocalRing.ResidueField ↥A)) Q
    rw [h, map_zero] at h3
    have hinj := transcendental_iff_injective.mp (ModularCurve.transcendental_jqModC (IsLocalRing.ResidueField ↥A))
    exact hinj (by rw [h3, map_zero])
  · rintro rfl
    rw [map_zero]

set_option synthInstance.maxHeartbeats 1600000 in

theorem isRational_pt (x₀ : IsLocalRing.ResidueField ↥A) : (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀).IsRational := by
  rw [line_charLGeomPlaceOfPoint_eq]
  intro y
  obtain ⟨a, ha⟩ := line_isRational_ratFunc _ ((Place.congrResidueAlgEquiv _ _ _).symm y)
  exact ⟨a, by rw [← (Place.congrResidueAlgEquiv _ _ _).commutes a, ha, AlgEquiv.apply_symm_apply]⟩

set_option synthInstance.maxHeartbeats 1600000 in
theorem isRational_inf : (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).IsRational := by
  rw [line_charLGeomPlaceEquiv_eq]
  intro y
  obtain ⟨a, ha⟩ := line_isRational_ratFunc _ ((Place.congrResidueAlgEquiv _ _ _).symm y)
  exact ⟨a, by rw [← (Place.congrResidueAlgEquiv _ _ _).commutes a, ha, AlgEquiv.apply_symm_apply]⟩

include hunit in
theorem isUnit_s (l : Fin r) : IsUnit (⟨s l, hint l⟩ : C.integers) := by
  by_contra h
  have hmem : (⟨s l, hint l⟩ : C.integers) ∈ IsLocalRing.maximalIdeal C.integers :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
  rw [← C.ker_residue, RingHom.mem_ker] at hmem
  exact hunit l hmem

include hunit hD hR in

theorem ratio_mem_and_residue (j c' : Fin r) :
    ∃ h : s j * (s c')⁻¹ ∈ C.integers,
      (C.residue ⟨_, h⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R j) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) * (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R c'))⁻¹ := by
  classical

  have hu : IsUnit (⟨s c', hint c'⟩ : C.integers) := by
    by_contra h
    have hmem : (⟨s c', hint c'⟩ : C.integers) ∈ IsLocalRing.maximalIdeal C.integers :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
    rw [← C.ker_residue, RingHom.mem_ker] at hmem
    exact hunit c' hmem
  obtain ⟨u, hu'⟩ := hu
  have hsc0 : s c' ≠ 0 := fun h0 => hunit c' (by
    have : (⟨s c', hint c'⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero])
  have hinv_val : ((u⁻¹ : C.integersˣ) : C.integers).1 = (s c')⁻¹ := by
    have hmul : (u : C.integers).1 * ((u⁻¹ : C.integersˣ) : C.integers).1 = 1 := by
      have h := congrArg Subtype.val u.mul_inv
      rwa [MulMemClass.coe_mul, OneMemClass.coe_one] at h
    rw [hu'] at hmul
    exact (eq_inv_of_mul_eq_one_right hmul)
  have hinv_mem : (s c')⁻¹ ∈ C.integers := by rw [← hinv_val]; exact SetLike.coe_mem _
  have hmem : s j * (s c')⁻¹ ∈ C.integers := mul_mem (hint j) hinv_mem
  refine ⟨hmem, ?_⟩

  have hres_inv : C.residue ⟨(s c')⁻¹, hinv_mem⟩ * C.residue ⟨s c', hint c'⟩ = 1 := by
    rw [← map_mul, ← map_one C.residue]
    congr 1
    apply Subtype.ext
    show (s c')⁻¹ * s c' = 1
    exact inv_mul_cancel₀ hsc0
  have hres_c0 : C.residue ⟨s c', hint c'⟩ ≠ 0 := hunit c'
  have hres_inv' : C.residue ⟨(s c')⁻¹, hinv_mem⟩ = (C.residue ⟨s c', hint c'⟩)⁻¹ :=
    eq_inv_of_mul_eq_one_left hres_inv
  have hprod : C.residue ⟨s j * (s c')⁻¹, hmem⟩ = C.residue ⟨s j, hint j⟩ * (C.residue ⟨s c', hint c'⟩)⁻¹ := by
    rw [← hres_inv', ← map_mul]
    rfl

  have hDne : (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ≠ 0 :=
    (aeval_ne_zero_iff D).mpr hD
  have hres_eq : ∀ l, (C.residue ⟨s l, hint l⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
      = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R l) * (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D)⁻¹ := by
    intro l
    rw [← hR l, mul_assoc, mul_inv_cancel₀ hDne, mul_one]
  rw [hprod, hres_eq j, hres_eq c', mul_inv, inv_inv]
  have hRc : (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R c') : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ≠ 0 := by
    rw [← hR c']
    exact mul_ne_zero (hunit c') hDne
  field_simp

include hD hR hunit in
theorem R_ne_zero (l : Fin r) : R l ≠ 0 := by
  intro h0
  have hDne : (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ≠ 0 :=
    (aeval_ne_zero_iff D).mpr hD
  have h := hR l
  rw [h0, map_zero] at h
  exact mul_ne_zero (hunit l) hDne h

include hFrat hdom in

theorem value_mem_and_residue_eq {P : Place (AlgebraicClosure ℚ) F} (hP : P ∈ C.dom) (f : F) (hf : f ∈ C.integers)
    (hfib : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → f ∈ w.toValuationSubring) :
    (C.residue ⟨f, hf⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ∈ (C.placeMap P).toValuationSubring ∧
    ∃ h : P.evalAt f ∈ A,
      IsLocalRing.residue (↥A) ⟨P.evalAt f, h⟩ = (C.placeMap P).evalAt (C.residue ⟨f, hf⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) := by
  obtain ⟨hm, h, hcompat⟩ := C.pointwise P hP (hFrat P) f hf hfib
  refine ⟨hm, h, ?_⟩

  have hrat : (C.placeMap P).IsRational := by
    rcases hdom P hP with ⟨x₀, hx, -⟩ | hx
    · rw [hx]; exact isRational_pt (A := A) x₀
    · rw [hx]; exact isRational_inf (A := A)
  apply (C.placeMap P).algebraMap_residueField_injective
  rw [hcompat, (C.placeMap P).algebraMap_evalAt hrat hm]

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in

theorem aux_mapDomain_apply_eq_sum {α β : Type*} (g : α → β) (E : α →₀ ℤ) (b : β) [DecidableEq β] :
    Finsupp.mapDomain g E b = ∑ a ∈ E.support, if g a = b then E a else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun a _ => by rw [Finsupp.single_apply]

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in

theorem aux_ord_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) {a : K} (ha : a ≠ 0) :
    v.ord (algebraMap K L a) = 0 := by
  have hu : IsUnit (⟨algebraMap K L a, v.algebraMap_mem' a⟩ : v.toValuationSubring) :=
    ⟨⟨⟨algebraMap K L a, v.algebraMap_mem' a⟩, ⟨algebraMap K L a⁻¹, v.algebraMap_mem' a⁻¹⟩,
      Subtype.ext (by simpa using mul_inv_cancel₀ ((map_ne_zero (algebraMap K L)).mpr ha)),
      Subtype.ext (by simpa using inv_mul_cancel₀ ((map_ne_zero (algebraMap K L)).mpr ha))⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in

theorem aux_inv_mem_of_evalAt_ne_zero {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L) {f : L}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) : f⁻¹ ∈ v.toValuationSubring := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0
    apply h
    rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]
  have hunit : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    by_contra hn
    exact hres ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn))
  obtain ⟨u, hu⟩ := hunit
  have hmul : f * ((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring).1 = 1 := by
    have h1 := congrArg Subtype.val u.mul_inv
    rw [hu] at h1
    exact h1
  rw [inv_eq_of_mul_eq_one_right hmul]
  exact ((u⁻¹ : (v.toValuationSubring)ˣ) : v.toValuationSubring).2

theorem aux_pt_ne_inf (x₀ : IsLocalRing.ResidueField ↥A) :
    charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀
      ≠ charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) := by
  intro h
  have hX : (Polynomial.X - Polynomial.C x₀ : Polynomial (IsLocalRing.ResidueField ↥A)) ≠ 0 := Polynomial.X_sub_C_ne_zero x₀
  have h1 := ord_pt_aeval (Polynomial.X - Polynomial.C x₀) hX x₀
  have h2 := ord_inf_aeval (A := A) (Polynomial.X - Polynomial.C x₀) hX
  rw [h, h2, Polynomial.rootMultiplicity_X_sub_C_self, Polynomial.natDegree_X_sub_C] at h1
  norm_num at h1

include hFrat hunit hD hR hreg₀ hdom hcx hc₀inf in
theorem blockA_reg {P : Place (AlgebraicClosure ℚ) F} (hP : P ∈ C.dom) {x₀ : IsLocalRing.ResidueField ↥A}
    (hx : C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀) (j : Fin r) :
    s j * (s (c x₀))⁻¹ ∈ P.toValuationSubring := by
  classical

  have hne : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → w ≠ c₀ := by
    rintro w - hw rfl
    exact aux_pt_ne_inf x₀ (hx.symm.trans (hw.symm.trans hc₀inf))
  have hPc : P ≠ c₀ := hne P hP rfl
  have hfib : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → s (c x₀) ∈ w.toValuationSubring :=
    fun w hw hwP => hreg₀ w hw (hne w hw hwP) (c x₀)

  have hDx : D.eval x₀ ≠ 0 := by
    rcases hdom P hP with ⟨x₁, hx₁, hD₁⟩ | hinf
    · rw [hx] at hx₁
      rwa [← charLGeomPlaceOfPoint_injective _ hx₁] at hD₁
    · exact (aux_pt_ne_inf x₀ (hx.symm.trans hinf)).elim
  have hRx : (R (c x₀)).eval x₀ ≠ 0 := hcx P hP x₀ hx

  set v := charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ with hv
  have hDt : (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ≠ 0 :=
    (aeval_ne_zero_iff D).mpr hD
  have hRc0 : R (c x₀) ≠ 0 := R_ne_zero (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (c x₀)
  have hRt : (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R (c x₀)) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ≠ 0 :=
    (aeval_ne_zero_iff _).mpr hRc0
  have hres_eq : (C.residue ⟨s (c x₀), hint _⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
      = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R (c x₀)) * (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D)⁻¹ := by
    rw [← hR (c x₀), mul_inv_cancel_right₀ hDt]
  have hord : v.ord (C.residue ⟨s (c x₀), hint _⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 0 := by
    rw [hres_eq, v.ord_mul hRt (inv_ne_zero hDt), v.ord_inv, hv, ord_pt_aeval _ hRc0, ord_pt_aeval _ hD,
      Polynomial.rootMultiplicity_eq_zero hRx, Polynomial.rootMultiplicity_eq_zero hDx]
    simp

  have hev : v.evalAt (C.residue ⟨s (c x₀), hint _⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ≠ 0 :=
    Place.evalAt_ne_zero v (isRational_pt x₀) (hunit _) hord
  obtain ⟨-, hval, hres⟩ := value_mem_and_residue_eq (hFrat := hFrat) (C := C) (D := D) (hdom := hdom) hP (s (c x₀)) (hint _) hfib
  rw [hx] at hres
  have hPev : P.evalAt (s (c x₀)) ≠ 0 := by
    intro h0
    apply hev
    rw [← hres]
    have : (⟨P.evalAt (s (c x₀)), hval⟩ : ↥A) = 0 := Subtype.ext h0
    rw [this, map_zero]
  exact mul_mem (hreg₀ P hP hPc j) (aux_inv_mem_of_evalAt_ne_zero P (hreg₀ P hP hPc (c x₀)) hPev)

include hFrat hunit hD hR hdom hcx in
theorem blockA_evalAt {P : Place (AlgebraicClosure ℚ) F} (hP : P ∈ C.dom) {x₀ : IsLocalRing.ResidueField ↥A}
    (hx : C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀) (j : Fin r)
    (hmem : s j * (s (c x₀))⁻¹ ∈ C.integers) :
    (C.placeMap P).evalAt (C.residue ⟨_, hmem⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
      = (R j).eval x₀ / (R (c x₀)).eval x₀ := by
  classical
  obtain ⟨h', hres⟩ := ratio_mem_and_residue (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) j (c x₀)
  have hpi : (⟨_, hmem⟩ : ↥C.integers) = ⟨_, h'⟩ := rfl
  rw [hpi, hres, hx]
  set v := charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ with hv
  set a := (R j).eval x₀
  set b := (R (c x₀)).eval x₀ with hb
  have hb0 : b ≠ 0 := hcx P hP x₀ hx
  have hRc0 : R (c x₀) ≠ 0 := R_ne_zero (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (c x₀)
  have hRj0 : R j ≠ 0 := R_ne_zero (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) j
  set Rc := (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R (c x₀)) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) with hRc
  set Rj := (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R j) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) with hRj
  have hRct : Rc ≠ 0 := (aeval_ne_zero_iff _).mpr hRc0
  have hRjt : Rj ≠ 0 := (aeval_ne_zero_iff _).mpr hRj0

  have hf_mem : Rj * Rc⁻¹ ∈ v.toValuationSubring := by
    rw [Place.mem_iff_ord_nonneg _ (mul_ne_zero hRjt (inv_ne_zero hRct)), v.ord_mul hRjt (inv_ne_zero hRct), v.ord_inv,
      hv, ord_pt_aeval _ hRj0, ord_pt_aeval _ hRc0, Polynomial.rootMultiplicity_eq_zero hb0]
    simp
  have hg_mem : algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (a / b) ∈ v.toValuationSubring := v.algebraMap_mem' _

  set N := R j - Polynomial.C (a / b) * R (c x₀) with hN
  have hNroot : N.IsRoot x₀ := by
    simp only [hN, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    rw [div_mul_cancel₀ _ hb0]; exact sub_self _
  have hdiff : Rj * Rc⁻¹ - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (a / b)
      = (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) N : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) * Rc⁻¹ := by
    rw [hN, map_sub, map_mul, Polynomial.aeval_C, sub_mul, mul_assoc, mul_inv_cancel₀ hRct, mul_one]
  have hcongr : Rj * Rc⁻¹ - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (a / b) = 0 ∨
      0 < v.ord (Rj * Rc⁻¹ - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (a / b)) := by
    rw [hdiff]
    by_cases hN0 : N = 0
    · left; rw [hN0, map_zero, zero_mul]
    · right
      rw [v.ord_mul ((aeval_ne_zero_iff _).mpr hN0) (inv_ne_zero hRct), v.ord_inv, hv, ord_pt_aeval _ hN0, ord_pt_aeval _ hRc0,
        Polynomial.rootMultiplicity_eq_zero hb0]
      simp only [Nat.cast_zero, neg_zero, add_zero, Nat.cast_pos]
      exact (Polynomial.rootMultiplicity_pos hN0).mpr hNroot
  rw [Place.evalAt_congr v hf_mem hg_mem hcongr, Place.evalAt_algebraMap]

include hFrat hunit hD hR hreg₀ hdom hcx hix hc₀inf in
theorem blockA_imm {P : Place (AlgebraicClosure ℚ) F} (hP : P ∈ C.dom) {x₀ : IsLocalRing.ResidueField ↥A}
    (hx : C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀)
    (hmem : s (i x₀) * (s (c x₀))⁻¹ ∈ C.integers) :
    (C.placeMap P).ord ((C.residue ⟨_, hmem⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
      - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
          ((C.placeMap P).evalAt (C.residue ⟨_, hmem⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)))) = 1 := by
  classical
  rw [blockA_evalAt (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR)
    (hdom := hdom) (c := c) (hcx := hcx) hP hx (i x₀) hmem]
  obtain ⟨h', hres⟩ := ratio_mem_and_residue (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (i x₀) (c x₀)
  have hpi : (⟨_, hmem⟩ : ↥C.integers) = ⟨_, h'⟩ := rfl
  rw [hpi, hres, hx]
  set v := charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ with hv
  set a := (R (i x₀)).eval x₀ with ha
  set b := (R (c x₀)).eval x₀ with hb
  have hb0 : b ≠ 0 := hcx P hP x₀ hx
  have hRc0 : R (c x₀) ≠ 0 := R_ne_zero (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (c x₀)
  set Rc := (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R (c x₀)) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) with hRc
  set Ri := (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R (i x₀)) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) with hRi
  have hRct : Rc ≠ 0 := (aeval_ne_zero_iff _).mpr hRc0

  set M := R (i x₀) * Polynomial.C b - R (c x₀) * Polynomial.C a with hM
  have hMmult : M.rootMultiplicity x₀ = 1 := hix P hP x₀ hx
  have hM0 : M ≠ 0 := fun h0 => by rw [h0, Polynomial.rootMultiplicity_zero] at hMmult; exact zero_ne_one hMmult
  have hdiff : Ri * Rc⁻¹ - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (a / b)
      = algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) b⁻¹ * (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) M : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) * Rc⁻¹ := by
    rw [hM, map_sub, map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C]
    have hbt : (algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) b) ≠ 0 := (map_ne_zero _).mpr hb0
    rw [map_div₀, map_inv₀]
    field_simp
    ring
  rw [hdiff, v.ord_mul (mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero hb0)) ((aeval_ne_zero_iff _).mpr hM0)) (inv_ne_zero hRct),
    v.ord_mul ((map_ne_zero _).mpr (inv_ne_zero hb0)) ((aeval_ne_zero_iff _).mpr hM0),
    aux_ord_algebraMap v (inv_ne_zero hb0), v.ord_inv, hv, ord_pt_aeval _ hM0, ord_pt_aeval _ hRc0, hMmult,
    Polynomial.rootMultiplicity_eq_zero hb0]
  simp

include hFrat hunit hD hR hc₀ hc₀inf hreg₀ hdom hcusp hcInf hcInfD hpole in
theorem blockB_top :
    c₀.ord (s cInf) = -(((R cInf).natDegree - D.natDegree : ℕ) : ℤ) ∧
    ∀ W ∈ C.dom, C.placeMap W = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) →
      W ≠ c₀ → W.ord (s cInf) = 0 := by
  classical
  set vinf := charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) with hvinf
  set N : ℕ := (R cInf).natDegree - D.natDegree with hNdef
  have hsc0 : s cInf ≠ 0 := fun h0 => hunit cInf (by
    have : (⟨s cInf, hint cInf⟩ : ↥C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero])

  obtain ⟨E, hE, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (s cInf) hsc0
  have hlaw := hcusp (s cInf) (hint cInf) (hunit cInf) E hE

  have hDt : (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ≠ 0 := (aeval_ne_zero_iff D).mpr hD
  have hRc0 : R cInf ≠ 0 := R_ne_zero (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) cInf
  have hRt : (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R cInf) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) ≠ 0 := (aeval_ne_zero_iff _).mpr hRc0
  have hres_eq : (C.residue ⟨s cInf, hint _⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
      = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R cInf) * (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D)⁻¹ := by
    rw [← hR cInf, mul_inv_cancel_right₀ hDt]
  have hrhs : vinf.ord (C.residue ⟨s cInf, hint _⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = -(N : ℤ) := by
    rw [hres_eq, vinf.ord_mul hRt (inv_ne_zero hDt), vinf.ord_inv, hvinf, ord_inf_aeval _ hRc0, ord_inf_aeval _ hD, hNdef,
      Nat.cast_sub hcInfD]
    ring
  rw [hrhs] at hlaw

  set T : Place (AlgebraicClosure ℚ) F → Prop := fun W => W ∈ C.dom ∧ C.placeMap W = vinf with hT
  set S := E.filter T with hS
  have hSapp : ∀ W, S W = if T W then E W else 0 := fun W => by rw [hS, Finsupp.filter_apply]
  have hsum : Finsupp.mapDomain C.placeMap S vinf = ∑ W ∈ S.support, S W := by
    rw [aux_mapDomain_apply_eq_sum]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hTW : T W := by
      by_contra hn
      rw [Finsupp.mem_support_iff, hSapp, if_neg hn] at hW
      exact hW rfl
    rw [if_pos hTW.2]
  rw [hsum] at hlaw

  have hnn : ∀ W ∈ S.support, W ≠ c₀ → 0 ≤ S W := by
    intro W hW hWc
    have hTW : T W := by
      by_contra hn
      rw [Finsupp.mem_support_iff, hSapp, if_neg hn] at hW
      exact hW rfl
    rw [hSapp, if_pos hTW, hE]
    exact W.ord_nonneg_of_mem (hreg₀ W hTW.1 hWc cInf)
  have hTc : T c₀ := ⟨hc₀, hc₀inf⟩
  have hSc : S c₀ = c₀.ord (s cInf) := by rw [hSapp, if_pos hTc, hE]

  have hsplit : ∑ W ∈ S.support, S W = S c₀ + ∑ W ∈ S.support.erase c₀, S W := by
    by_cases hc : c₀ ∈ S.support
    · rw [← Finset.add_sum_erase _ _ hc]
    · rw [Finset.erase_eq_of_notMem hc, Finsupp.notMem_support_iff.mp hc, zero_add]
  rw [hsplit] at hlaw
  have hrest_nn : 0 ≤ ∑ W ∈ S.support.erase c₀, S W :=
    Finset.sum_nonneg fun W hW => hnn W (Finset.mem_of_mem_erase hW) (Finset.ne_of_mem_erase hW)
  have hpole' : -(N : ℤ) ≤ S c₀ := by rw [hSc]; exact hpole cInf
  have hc0val : S c₀ = -(N : ℤ) := by omega
  have hrest0 : ∑ W ∈ S.support.erase c₀, S W = 0 := by omega
  refine ⟨by rw [← hSc, hc0val], fun W hW hWinf hWc => ?_⟩
  have hTW : T W := ⟨hW, hWinf⟩

  by_contra hne
  have hWsupp : W ∈ S.support := by
    rw [Finsupp.mem_support_iff, hSapp, if_pos hTW, hE]; exact hne
  have hWer : W ∈ S.support.erase c₀ := Finset.mem_erase.mpr ⟨hWc, hWsupp⟩
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun W' hW' => hnn W' (Finset.mem_of_mem_erase hW') (Finset.ne_of_mem_erase hW'))).mp
    hrest0 W hWer
  rw [hSapp, if_pos hTW, hE] at h0
  exact hne h0

include hFrat hunit hD hR hc₀ hc₀inf hreg₀ hdom hcusp hcInf hcInfD hpole in
theorem blockB_reg {P : Place (AlgebraicClosure ℚ) F} (hP : P ∈ C.dom)
    (hx : C.placeMap P = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
    (j : Fin r) : s j * (s cInf)⁻¹ ∈ P.toValuationSubring := by
  classical
  obtain ⟨htop, hzero⟩ := blockB_top (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR)
    (c₀ := c₀) (hc₀ := hc₀) (hc₀inf := hc₀inf) (hreg₀ := hreg₀) (hdom := hdom) (hcusp := hcusp) (cInf := cInf) (hcInf := hcInf) (hcInfD := hcInfD) (hpole := hpole)
  have hs0 : ∀ l, s l ≠ 0 := fun l h0 => hunit l (by
    have : (⟨s l, hint l⟩ : ↥C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero])
  by_cases hPc : P = c₀
  · subst hPc
    rw [Place.mem_iff_ord_nonneg _ (mul_ne_zero (hs0 j) (inv_ne_zero (hs0 cInf))), Place.ord_mul _ (hs0 j) (inv_ne_zero (hs0 cInf)),
      Place.ord_inv, htop]
    have := hpole j
    omega
  · have hcmem : s cInf ∈ P.toValuationSubring := hreg₀ P hP hPc cInf
    have hord0 : P.ord (s cInf) = 0 := hzero P hP hx hPc
    have hev : P.evalAt (s cInf) ≠ 0 := Place.evalAt_ne_zero P (hFrat P) (hs0 cInf) hord0
    exact mul_mem (hreg₀ P hP hPc j) (aux_inv_mem_of_evalAt_ne_zero P hcmem hev)

include hFrat hunit hD hR hdom hcInf hcInfD in
theorem blockB_evalAt {P : Place (AlgebraicClosure ℚ) F} (hP : P ∈ C.dom)
    (hx : C.placeMap P = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
    (j : Fin r) (hmem : s j * (s cInf)⁻¹ ∈ C.integers) :
    (C.placeMap P).evalAt (C.residue ⟨_, hmem⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
      = (R j).coeff (R cInf).natDegree / (R cInf).leadingCoeff := by
  obtain ⟨h', hres⟩ := ratio_mem_and_residue (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) j cInf
  have hpi : (⟨_, hmem⟩ : ↥C.integers) = ⟨_, h'⟩ := rfl
  rw [hpi, hres, hx]
  exact (evalAt_inf_aeval_div (R j) (R cInf) (R_ne_zero (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) cInf) (hcInf j)).2

include hFrat hunit hD hR hc₀ hc₀inf hreg₀ hdom hcusp hcInf hcInfD hpole hiInf hiInf0 in
theorem blockB_imm {P : Place (AlgebraicClosure ℚ) F} (hP : P ∈ C.dom)
    (hx : C.placeMap P = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
    (hmem : s iInf * (s cInf)⁻¹ ∈ C.integers) :
    (C.placeMap P).ord ((C.residue ⟨_, hmem⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
      - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)
          ((C.placeMap P).evalAt (C.residue ⟨_, hmem⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)))) = 1 := by
  classical
  rw [blockB_evalAt (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR)
    (hdom := hdom) (cInf := cInf) (hcInf := hcInf) (hcInfD := hcInfD) hP hx iInf hmem]
  obtain ⟨h', hres⟩ := ratio_mem_and_residue (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) iInf cInf
  have hpi : (⟨_, hmem⟩ : ↥C.integers) = ⟨_, h'⟩ := rfl
  rw [hpi, hres, hx]
  set vinf := charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) with hvinf
  set lam := (R iInf).coeff (R cInf).natDegree / (R cInf).leadingCoeff with hlam
  have hRc0 : R cInf ≠ 0 := R_ne_zero (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) cInf
  set Rc := (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R cInf) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) with hRc
  set Ri := (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R iInf) : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) with hRi
  have hRct : Rc ≠ 0 := (aeval_ne_zero_iff _).mpr hRc0
  set M := R iInf - Polynomial.C lam * R cInf with hM
  have hM0 : M ≠ 0 := hiInf0
  have hdiff : Ri * Rc⁻¹ - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) lam
      = (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) M : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) * Rc⁻¹ := by
    rw [hM, map_sub, map_mul, Polynomial.aeval_C, sub_mul, mul_assoc, mul_inv_cancel₀ hRct, mul_one]
  rw [hdiff, vinf.ord_mul ((aeval_ne_zero_iff _).mpr hM0) (inv_ne_zero hRct), vinf.ord_inv, hvinf, ord_inf_aeval _ hM0,
    ord_inf_aeval _ hRc0]
  have := hiInf
  omega

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in
theorem pt_ne_inf (x₀ : IsLocalRing.ResidueField ↥A) : charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ ≠ charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) := by
  intro h
  exact AlgebraicCurve.RationalFunctionField.placeOfPoint_ne_placeInfty (IsLocalRing.ResidueField ↥A) x₀
    ((charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A)).injective h)

noncomputable def xOf (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : IsLocalRing.ResidueField ↥A :=
  if h : ∃ x₀, v = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ then h.choose else 0

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in
theorem xOf_pt (x₀ : IsLocalRing.ResidueField ↥A) : xOf (A := A) (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀) = x₀ := by
  have h : ∃ y, charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) y := ⟨x₀, rfl⟩
  rw [xOf, dif_pos h]
  exact (charLGeomPlaceOfPoint_injective (IsLocalRing.ResidueField ↥A) h.choose_spec).symm

noncomputable def idxOf (g : IsLocalRing.ResidueField ↥A → Fin r) (gInf : Fin r) (v : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) : Fin r :=
  if v = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)) then gInf else g (xOf (A := A) v)

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in
theorem idxOf_pt (g : IsLocalRing.ResidueField ↥A → Fin r) (gInf : Fin r) (x₀ : IsLocalRing.ResidueField ↥A) :
    idxOf (A := A) g gInf (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀) = g x₀ := by
  rw [idxOf, if_neg (pt_ne_inf (A := A) x₀), xOf_pt]

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in
theorem idxOf_inf (g : IsLocalRing.ResidueField ↥A → Fin r) (gInf : Fin r) : idxOf (A := A) g gInf (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))) = gInf := if_pos rfl

omit [DecidableEq (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] in

theorem abv_eq_one_of_isUnit (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    {a : AlgebraicClosure ℚ} (ha : a ∈ A) (hu : IsLocalRing.residue (↥A) ⟨a, ha⟩ ≠ 0) : μ a = 1 := by
  have hunitA : IsUnit (⟨a, ha⟩ : ↥A) := by
    by_contra hn
    exact hu ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hn))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hu (by rw [show (⟨(0 : AlgebraicClosure ℚ), ha⟩ : ↥A) = 0 from rfl, map_zero])
  have hinv : a⁻¹ ∈ A := by
    obtain ⟨u, hu'⟩ := hunitA
    have h1 : (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * a = 1 := by
      have := congrArg (fun x : ↥A => (x : AlgebraicClosure ℚ)) u.inv_mul
      rw [hu'] at this
      simpa using this
    have : (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = a⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [← this]; exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
  have h1 : μ a ≤ 1 := (hμ a).mp ha
  have h2 : μ a⁻¹ ≤ 1 := (hμ a⁻¹).mp hinv
  rw [map_inv₀] at h2
  have hpos : 0 < μ a := μ.pos ha0
  have h3 : 1 ≤ μ a := by rwa [inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h3

set_option maxHeartbeats 6400000 in
include hFrat hunit hD hR hc₀ hc₀inf hreg₀ hdom hcusp hcx hix hsepx hHx hcInf hcInfD hcInfH hpole hiInf hiInf0 hsepInf in
theorem assembly :
    ∃ (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → Fin r),
      (∀ P ∈ C.dom, P.IsRational ∧ (C.placeMap P).IsRational) ∧
      (∀ P ∈ C.dom, C.residue ⟨s (cQ (C.placeMap P)), hint _⟩ ≠ 0) ∧
      (∀ P ∈ C.dom, ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers) ∧
      (∀ P ∈ C.dom, ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ P.toValuationSubring) ∧
      (∀ P ∈ C.dom, ∀ hmem : s (iQ (C.placeMap P)) * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers,
        (C.placeMap P).ord (C.residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) ((C.placeMap P).evalAt (C.residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ C.dom, ∀ Q ∈ C.dom, C.placeMap P ≠ C.placeMap Q →
        ∀ (hmP : ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
          (hmQ : ∀ j, s j * (s (cQ (C.placeMap Q)))⁻¹ ∈ C.integers),
        ∃ i' j', (C.placeMap P).evalAt (C.residue ⟨_, hmP i'⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ j'⟩)
          ≠ (C.placeMap P).evalAt (C.residue ⟨_, hmP j'⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ i'⟩)) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P ∈ C.dom, ∃ l ∈ H, μ (P.evalAt (s l * (s (cQ (C.placeMap P)))⁻¹)) = 1) := by
  have evA : ∀ {P} (hP : P ∈ C.dom) {x₀} (hx : C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀) (j : Fin r)
      (hmem : s j * (s (c x₀))⁻¹ ∈ C.integers),
      (C.placeMap P).evalAt (C.residue ⟨_, hmem⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = (R j).eval x₀ / (R (c x₀)).eval x₀ :=
    fun hP _ hx j hmem => blockA_evalAt (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (hdom := hdom) (c := c) (hcx := hcx) hP hx j hmem
  have evB : ∀ {P} (hP : P ∈ C.dom) (hx : C.placeMap P = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))) (j : Fin r)
      (hmem : s j * (s cInf)⁻¹ ∈ C.integers),
      (C.placeMap P).evalAt (C.residue ⟨_, hmem⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = (R j).coeff (R cInf).natDegree / (R cInf).leadingCoeff :=
    fun hP hx j hmem => blockB_evalAt (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (hdom := hdom) (cInf := cInf) (hcInf := hcInf) (hcInfD := hcInfD) hP hx j hmem
  refine ⟨idxOf (A := A) c cInf, idxOf (A := A) i iInf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro P hP
    refine ⟨hFrat P, ?_⟩
    rcases hdom P hP with ⟨x₀, hx, -⟩ | hx
    · rw [hx]; exact isRational_pt (A := A) x₀
    · rw [hx]; exact isRational_inf (A := A)
  ·
    intro P hP; exact hunit _
  ·
    intro P hP j
    exact (ratio_mem_and_residue (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) j _).1
  ·
    intro P hP j
    rcases hdom P hP with ⟨x₀, hx, -⟩ | hx
    · rw [hx, idxOf_pt]
      exact blockA_reg (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (c₀ := c₀) (hc₀inf := hc₀inf) (hreg₀ := hreg₀) (hdom := hdom) (c := c) (hcx := hcx) hP hx j
    · rw [hx, idxOf_inf]
      exact blockB_reg (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (c₀ := c₀) (hc₀ := hc₀) (hc₀inf := hc₀inf) (hreg₀ := hreg₀) (hdom := hdom) (hcusp := hcusp) (cInf := cInf) (hcInf := hcInf) (hcInfD := hcInfD) (hpole := hpole) hP hx j
  ·
    intro P hP
    rcases hdom P hP with ⟨x₀, hx, -⟩ | hx
    · rw [hx, idxOf_pt, idxOf_pt]
      intro hmem
      have := blockA_imm (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (c₀ := c₀) (hc₀inf := hc₀inf) (hreg₀ := hreg₀) (hdom := hdom) (c := c) (i := i) (hcx := hcx) (hix := hix) hP hx hmem
      rwa [hx] at this
    · rw [hx, idxOf_inf, idxOf_inf]
      intro hmem
      have := blockB_imm (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (c₀ := c₀) (hc₀ := hc₀) (hc₀inf := hc₀inf) (hreg₀ := hreg₀) (hdom := hdom) (hcusp := hcusp) (cInf := cInf) (iInf := iInf) (hcInf := hcInf) (hcInfD := hcInfD) (hpole := hpole) (hiInf := hiInf) (hiInf0 := hiInf0) hP hx hmem
      rwa [hx] at this
  ·
    intro P hP Q hQ hne
    rcases hdom P hP with ⟨x₀, hx, hDx⟩ | hx <;> rcases hdom Q hQ with ⟨y₀, hy, hDy⟩ | hy
    ·
      have hxy : x₀ ≠ y₀ := by rintro rfl; exact hne (hx.trans hy.symm)
      rw [hx, hy, idxOf_pt, idxOf_pt]
      intro hmP hmQ
      obtain ⟨a, b, hab⟩ := hsepx P hP Q hQ x₀ y₀ hx hy hxy
      refine ⟨a, b, ?_⟩
      have e1 := evA hP hx a (hmP a); have e2 := evA hQ hy b (hmQ b)
      have e3 := evA hP hx b (hmP b); have e4 := evA hQ hy a (hmQ a)
      rw [hx] at e1 e3; rw [hy] at e2 e4
      rw [e1, e2, e3, e4]
      have hc1 := hcx P hP x₀ hx; have hc2 := hcx Q hQ y₀ hy
      intro h; apply hab
      rw [div_mul_div_comm, div_mul_div_comm, div_left_inj' (mul_ne_zero hc1 hc2)] at h
      exact h
    ·
      rw [hx, hy, idxOf_pt, idxOf_inf]
      intro hmP hmQ
      obtain ⟨a, b, hab⟩ := hsepInf P hP x₀ hx
      refine ⟨a, b, ?_⟩
      have e1 := evA hP hx a (hmP a); have e2 := evB hQ hy b (hmQ b)
      have e3 := evA hP hx b (hmP b); have e4 := evB hQ hy a (hmQ a)
      rw [hx] at e1 e3; rw [hy] at e2 e4
      rw [e1, e2, e3, e4]
      have hc1 := hcx P hP x₀ hx
      intro h; apply hab
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_left_inj' hc1] at h
      exact h
    ·
      rw [hx, hy, idxOf_inf, idxOf_pt]
      intro hmP hmQ
      obtain ⟨a, b, hab⟩ := hsepInf Q hQ y₀ hy
      refine ⟨b, a, ?_⟩
      have e1 := evB hP hx b (hmP b); have e2 := evA hQ hy a (hmQ a)
      have e3 := evB hP hx a (hmP a); have e4 := evA hQ hy b (hmQ b)
      rw [hx] at e1 e3; rw [hy] at e2 e4
      rw [e1, e2, e3, e4]
      have hc2 := hcx Q hQ y₀ hy
      intro h; apply hab
      rw [mul_div_assoc', mul_div_assoc', div_left_inj' hc2] at h
      rw [mul_comm ((R a).eval y₀), mul_comm ((R b).eval y₀)]
      exact h
    ·
      exact absurd (hx.trans hy.symm) hne
  ·
    intro μ hμ P hP
    rcases hdom P hP with ⟨x₀, hx, -⟩ | hx
    · obtain ⟨l, hlH, hl⟩ := hHx P hP x₀ hx
      refine ⟨l, hlH, ?_⟩
      rw [hx, idxOf_pt]
      obtain ⟨hmem, -⟩ := ratio_mem_and_residue (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) l (c x₀)
      have hfib : ∀ w ∈ C.dom, C.placeMap w = C.placeMap P → s l * (s (c x₀))⁻¹ ∈ w.toValuationSubring := by
        intro w hw hwP
        exact blockA_reg (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (c₀ := c₀) (hc₀inf := hc₀inf) (hreg₀ := hreg₀) (hdom := hdom) (c := c) (hcx := hcx) hw (hwP.trans hx) l
      obtain ⟨-, hA, hres⟩ := value_mem_and_residue_eq (hFrat := hFrat) (C := C) (D := D) (hdom := hdom) hP _ hmem hfib
      apply abv_eq_one_of_isUnit (A := A) μ hμ hA
      rw [hres, evA hP hx l hmem]
      exact div_ne_zero hl (hcx P hP x₀ hx)
    · refine ⟨cInf, hcInfH, ?_⟩
      rw [hx, idxOf_inf]
      have hs0 : s cInf ≠ 0 := by
        intro h0
        apply hunit cInf
        have : (⟨s cInf, hint cInf⟩ : C.integers) = 0 := Subtype.ext h0
        rw [this, map_zero]
      rw [mul_inv_cancel₀ hs0, Place.evalAt_one, map_one]

end Generic

end LineResidues

set_option maxHeartbeats 3200000 in
open Classical in

theorem solution
    {A : ValuationSubring (AlgebraicClosure ℚ)} [DecidableEq (IsLocalRing.ResidueField ↥A)] [DecidableEq (RatFunc (IsLocalRing.ResidueField ↥A))] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] [HasPrincipalDivisors (AlgebraicClosure ℚ) F]
    (hFrat : ∀ P : Place (AlgebraicClosure ℚ) F, P.IsRational)
    (C : ComponentChart A F ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
    {r : ℕ} (s : Fin r → F) (hint : ∀ l, s l ∈ C.integers) (hunit : ∀ l, C.residue ⟨s l, hint l⟩ ≠ 0)

    (D : Polynomial (IsLocalRing.ResidueField ↥A)) (R : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)) (hD : D ≠ 0)
    (hR : ∀ l, (C.residue ⟨s l, hint l⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) D
      = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (R l))

    (c₀ : Place (AlgebraicClosure ℚ) F) (hc₀ : c₀ ∈ C.dom)
    (hc₀inf : C.placeMap c₀ = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
    (hreg₀ : ∀ P ∈ C.dom, P ≠ c₀ → ∀ l, s l ∈ P.toValuationSubring)

    (hdom : ∀ P ∈ C.dom, (∃ x₀ : IsLocalRing.ResidueField ↥A, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ ∧ D.eval x₀ ≠ 0) ∨
      C.placeMap P = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))

    (hcusp : ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) F, (∀ W, E W = W.ord f) →
        Finsupp.mapDomain C.placeMap
            (E.filter (fun W => W ∈ C.dom ∧ C.placeMap W = charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))))
            (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A)))
          = (charLGeomPlaceEquiv (IsLocalRing.ResidueField ↥A) (RationalFunctionField.placeInfty (IsLocalRing.ResidueField ↥A))).ord (C.residue ⟨f, hf⟩))

    (c i : IsLocalRing.ResidueField ↥A → Fin r) (H : Finset (Fin r))
    (hcx : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → (R (c x₀)).eval x₀ ≠ 0)
    (hix : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      (R (i x₀) * Polynomial.C ((R (c x₀)).eval x₀) - R (c x₀) * Polynomial.C ((R (i x₀)).eval x₀)).rootMultiplicity x₀ = 1)
    (hsepx : ∀ P ∈ C.dom, ∀ Q ∈ C.dom, ∀ x₀ y₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → C.placeMap Q = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) y₀ → x₀ ≠ y₀ →
      ∃ a b, (R a).eval x₀ * (R b).eval y₀ ≠ (R b).eval x₀ * (R a).eval y₀)
    (hHx : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ → ∃ l ∈ H, (R l).eval x₀ ≠ 0)

    (cInf iInf : Fin r) (hcInf : ∀ l, (R l).natDegree ≤ (R cInf).natDegree) (hcInfD : D.natDegree ≤ (R cInf).natDegree) (hcInfH : cInf ∈ H)
    (hpole : ∀ l, -(((R cInf).natDegree - D.natDegree : ℕ) : ℤ) ≤ c₀.ord (s l))
    (hiInf : (R iInf - Polynomial.C ((R iInf).coeff (R cInf).natDegree / (R cInf).leadingCoeff) * R cInf).natDegree + 1
      = (R cInf).natDegree)
    (hiInf0 : R iInf - Polynomial.C ((R iInf).coeff (R cInf).natDegree / (R cInf).leadingCoeff) * R cInf ≠ 0)
    (hsepInf : ∀ P ∈ C.dom, ∀ x₀, C.placeMap P = charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) x₀ →
      ∃ a b, (R a).eval x₀ * ((R b).coeff (R cInf).natDegree / (R cInf).leadingCoeff)
        ≠ (R b).eval x₀ * ((R a).coeff (R cInf).natDegree / (R cInf).leadingCoeff)) :
    ∃ (cQ iQ : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) → Fin r),
      (∀ P ∈ C.dom, P.IsRational ∧ (C.placeMap P).IsRational) ∧
      (∀ P ∈ C.dom, C.residue ⟨s (cQ (C.placeMap P)), hint _⟩ ≠ 0) ∧
      (∀ P ∈ C.dom, ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers) ∧
      (∀ P ∈ C.dom, ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ P.toValuationSubring) ∧
      (∀ P ∈ C.dom, ∀ hmem : s (iQ (C.placeMap P)) * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers,
        (C.placeMap P).ord (C.residue ⟨_, hmem⟩
          - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) ((C.placeMap P).evalAt (C.residue ⟨_, hmem⟩))) = 1) ∧
      (∀ P ∈ C.dom, ∀ Q ∈ C.dom, C.placeMap P ≠ C.placeMap Q →
        ∀ (hmP : ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
          (hmQ : ∀ j, s j * (s (cQ (C.placeMap Q)))⁻¹ ∈ C.integers),
        ∃ i' j', (C.placeMap P).evalAt (C.residue ⟨_, hmP i'⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ j'⟩)
          ≠ (C.placeMap P).evalAt (C.residue ⟨_, hmP j'⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ i'⟩)) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P ∈ C.dom, ∃ l ∈ H, μ (P.evalAt (s l * (s (cQ (C.placeMap P)))⁻¹)) = 1) := by
  exact LineResidues.assembly (hFrat := hFrat) (C := C) (s := s) (hint := hint) (hunit := hunit) (D := D) (R := R) (hD := hD) (hR := hR) (c₀ := c₀) (hc₀ := hc₀) (hc₀inf := hc₀inf) (hreg₀ := hreg₀) (hdom := hdom) (hcusp := hcusp) (c := c) (i := i) (H := H) (hcx := hcx) (hix := hix) (hsepx := hsepx) (hHx := hHx) (cInf := cInf) (iInf := iInf) (hcInf := hcInf) (hcInfD := hcInfD) (hcInfH := hcInfH) (hpole := hpole) (hiInf := hiInf) (hiInf0 := hiInf0) (hsepInf := hsepInf)

end S_ModularCurve_exists_chartData_of_lineResidues
end P2MW
export P2MW.S_ModularCurve_exists_chartData_of_lineResidues (solution)
