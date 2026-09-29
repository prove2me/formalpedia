-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_exists_fibreCoord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/fe3ef4cf-407b-54cf-bd8c-1d163ab94609

import Mathlib
import Definitions.Def_ModularCurve_LevelOneChartFst
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_ComponentChart_fibreParam_laws_of_ord_residue_sub_eq_one
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_jqModC
import Theorems.Thm_ModularCurve_isRational_place_modularFunctionFieldC_one
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_jFun_jqFun
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers"

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun modularFunctionFieldBar ModularPolynomialData jqModC modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence charLGeomPlaceEquiv charLGeomPlaceOfPoint cuspInftyBar coeff_jqModC_neg_one ssPlaces ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap hasPrincipalDivisors_modularFunctionFieldBar_unconditional deg_eq_one_modularFunctionFieldBar eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty ord_charLGeomPlaceEquiv_placeInfty_jqModC isRational_place_modularFunctionFieldC_one"
namespace P2MC10inf
p2m_open "ModularCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem' (Q : Place K F) {f : F} (hf0 : f ≠ 0) (hf : f ∈ Q.toValuationSubring) :
    0 ≤ Q.ord f := by
  have h1 : Q.adicValuation f ≤ 1 := by
    have := Q.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : Q.toValuationSubring) : F) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := Q.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (Q.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (Q.adicValuation f))
  omega

theorem evalAt_eq_zero_of_ord_pos (Q : Place K F) (hQ : Q.IsRational) {f : F}
    (hf : f ∈ Q.toValuationSubring) (h : 0 < Q.ord f) : Q.evalAt f = 0 := by
  by_contra hne
  have hf0 : f ≠ 0 := by rintro rfl; rw [Place.ord_zero] at h; exact lt_irrefl _ h
  have : IsUnit (⟨f, hf⟩ : Q.toValuationSubring) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0; apply hne
    apply Q.algebraMap_residueField_injective
    rw [Q.algebraMap_evalAt hQ hf, h0, map_zero]
  obtain ⟨u, hu⟩ := this
  have h0 : Q.ord f = 0 := by
    have := Q.ord_coe_unit u
    rw [hu] at this
    exact this
  omega

theorem evalAt_sub_algebraMap_of_mem (Q : Place K F) (hQ : Q.IsRational) {f : F}
    (hf : f ∈ Q.toValuationSubring) (a : K) :
    Q.evalAt (f - algebraMap K F a) = Q.evalAt f - a := by
  apply Q.algebraMap_residueField_injective
  have ha : algebraMap K F a ∈ Q.toValuationSubring := Q.algebraMap_mem' a
  have h1 : (⟨f - algebraMap K F a, sub_mem hf ha⟩ : Q.toValuationSubring) = ⟨f, hf⟩ - ⟨algebraMap K F a, ha⟩ := rfl
  rw [map_sub, Q.algebraMap_evalAt hQ (sub_mem hf ha), Q.algebraMap_evalAt hQ hf, h1, map_sub]
  congr 1

theorem inv_mem_integers_of_residue_ne_zero {L : Type*} [Field L] {A : ValuationSubring L} {E : Type*} [Field E]
    [Algebra L E] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A E Fbar) {f : E} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    ∃ h : f⁻¹ ∈ C.integers, C.residue ⟨f⁻¹, h⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hunit : IsUnit (⟨f, hf⟩ : C.integers) := by
    by_contra hnu
    apply hres
    have hmem : (⟨f, hf⟩ : C.integers) ∈ IsLocalRing.maximalIdeal C.integers := hnu
    rw [← C.ker_residue] at hmem
    exact hmem
  obtain ⟨u, hu⟩ := hunit
  have e2 : f * (((u⁻¹ : (C.integers)ˣ) : C.integers) : E) = 1 := by
    have h := congrArg (fun z : C.integers => (z : E)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
    rw [hu] at h
    exact h
  have hinv : f⁻¹ = (((u⁻¹ : (C.integers)ˣ) : C.integers) : E) := (eq_inv_of_mul_eq_one_right e2).symm
  have hmem : f⁻¹ ∈ C.integers := by rw [hinv]; exact ((u⁻¹ : (C.integers)ˣ) : C.integers).2
  refine ⟨hmem, ?_⟩
  have hsub : (⟨f⁻¹, hmem⟩ : C.integers) = ((u⁻¹ : (C.integers)ˣ) : C.integers) := Subtype.ext hinv
  have hres_inv : C.residue ((u⁻¹ : (C.integers)ˣ) : C.integers) = (C.residue (u : C.integers))⁻¹ := by
    have h := congrArg C.residue u.mul_inv
    rw [map_mul, map_one] at h
    exact eq_inv_of_mul_eq_one_right h
  rw [hsub, hres_inv, hu]

theorem isRational_bar (M : ℕ) [NeZero M] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) :
    w.IsRational :=
  (Place.isRational_iff_deg_eq_one _).mpr (deg_eq_one_modularFunctionFieldBar M w)

end ModularCurve.P2MC10inf

open ModularCurve.P2MC10inf

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun modularFunctionFieldBar ModularPolynomialData jqModC modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence charLGeomPlaceEquiv charLGeomPlaceOfPoint cuspInftyBar coeff_jqModC_neg_one ssPlaces ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap hasPrincipalDivisors_modularFunctionFieldBar_unconditional deg_eq_one_modularFunctionFieldBar eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty ord_charLGeomPlaceEquiv_placeInfty_jqModC isRational_place_modularFunctionFieldC_one"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun IsCuspidal IsInftySide redFst"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "ChartFst.ι_coe_eq ChartFstSupply chartFst redFst_eq_redFst_cuspInftyBar_iff_of_mem_chartFst_dom residue₁ residue₁_apply residue_jFun_jqFun"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve"

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [DecidableEq (ResidueField ↥A)]
  {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
  {P : PlaceSpecialization A p 1 data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}

noncomputable scoped instance instFieldFbarC10 (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Field ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) := inferInstance

noncomputable scoped instance instAlgebraFbarC10 (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  inferInstance

noncomputable abbrev jBarC (k : Type*) [Field k] : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩

theorem redFst_cuspInftyBar_eq_placeInfty [IsAlgClosed (ResidueField ↥A)] [DecidableEq (RatFunc (ResidueField ↥A))]
    {R : LevelOneProlongationPair P} {S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))}
    (Γ : R.ChartFstSupply S₁) :
    P.redFst (cuspInftyBar (1 * p))
      = charLGeomPlaceEquiv (ResidueField ↥A) (RationalFunctionField.placeInfty (ResidueField ↥A)) := by
  rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (ResidueField ↥A)
      (P.redFst (cuspInftyBar (1 * p))) with ⟨c, hc⟩ | h
  · exact absurd hc (Γ.redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal Γ.isInftySide_cuspInftyBar.1 c)
  · exact h

theorem exists_ord_jFun_sub_pos_or_isInftySide_of_mem_chartFst_dom [IsAlgClosed (ResidueField ↥A)]
    (R : LevelOneProlongationPair P) (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
    (Wn : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)))
    (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (ResidueField ↥A)) (Γ : R.ChartFstSupply S₁)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hW : W ∈ (chartFst R S₁ Wn hWn Γ).dom) :
    (∃ a : ↥A, 0 < W.ord (PlaceSpecialization.jFun (q := p)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ))) ∨ P.IsInftySide W := by
  haveI : DecidableEq (RatFunc (ResidueField ↥A)) := Classical.decEq _
  by_cases hinf : P.IsInftySide W
  · exact Or.inr hinf
  · left
    have hne : P.redFst W ≠ P.redFst (cuspInftyBar (1 * p)) :=
      fun h => hinf ((redFst_eq_redFst_cuspInftyBar_iff_of_mem_chartFst_dom R S₁ Wn hWn Γ W hW).mp h)
    rcases eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty (ResidueField ↥A) (P.redFst W) with ⟨c, hc⟩ | h
    · obtain ⟨a, -, ha⟩ := (Γ.redFst_eq_charLGeomPlaceOfPoint_iff W c).mp hc
      exact ⟨a, ha⟩
    · exact absurd (h.trans (redFst_cuspInftyBar_eq_placeInfty Γ).symm) hne

omit [DecidableEq (ResidueField ↥A)] in

theorem jFun_inv_mem_of_isInftySide (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (hW : P.IsInftySide W) : (PlaceSpecialization.jFun (q := p))⁻¹ ∈ W.toValuationSubring := by
  by_cases h0 : PlaceSpecialization.jFun (q := p) = 0
  · rw [h0, inv_zero]; exact zero_mem _
  · have hle : W.ord (PlaceSpecialization.jFun (q := p)) ≤ 0 := by
      have h := hW.1 (0 : ↥A)
      simpa using h
    exact W.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero h0) (by rw [Place.ord_inv]; omega)

theorem ord_redFst_cuspInftyBar_jBarC [IsAlgClosed (ResidueField ↥A)]
    {R : LevelOneProlongationPair P} {S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))}
    (Γ : R.ChartFstSupply S₁) :
    (P.redFst (cuspInftyBar (1 * p))).ord (jBarC (ResidueField ↥A)) = -1 := by
  haveI : DecidableEq (RatFunc (ResidueField ↥A)) := Classical.decEq _
  rw [redFst_cuspInftyBar_eq_placeInfty Γ]
  exact ord_charLGeomPlaceEquiv_placeInfty_jqModC (ResidueField ↥A)

theorem jFun_mem_chartFst_integers_residue_eq (hA : A.LiesOverPrime p)
    (R : LevelOneProlongationPair P) (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
    (Wn : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)))
    (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (ResidueField ↥A)) (Γ : R.ChartFstSupply S₁) :
    ∃ h : PlaceSpecialization.jFun (q := p) ∈ (chartFst R S₁ Wn hWn Γ).integers,
      (chartFst R S₁ Wn hWn Γ).residue ⟨_, h⟩ = jBarC (ResidueField ↥A) := by
  obtain ⟨h₁, -, -, -, hres, -, -, -⟩ := residue_jFun_jqFun hA R
  refine ⟨h₁, Subtype.ext ?_⟩
  show ((R.residue₁ ⟨_, h₁⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) : LaurentSeries (ResidueField ↥A))
    = jqModC (ResidueField ↥A)
  rw [residue₁_apply, ChartFst.ι_coe_eq]
  exact hres

open Classical in

noncomputable def fibreCoordFst (p : ℕ) [Fact p.Prime] (k : Type*) [Field k]
    (x : Place k ↥(modularFunctionFieldC k 1)) : ↥(modularFunctionFieldBar (1 * p)) :=
  if ∃ c : k, x = charLGeomPlaceOfPoint k c then PlaceSpecialization.jFun (q := p)
  else (PlaceSpecialization.jFun (q := p))⁻¹

theorem chartFst_fibreCoords_of_hyps (R : LevelOneProlongationPair P)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
    (Wn : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)))
    (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (ResidueField ↥A)) (Γ : R.ChartFstSupply S₁)
    (h_i : ∀ W ∈ (chartFst R S₁ Wn hWn Γ).dom,
      (∃ a : ↥A, 0 < W.ord (PlaceSpecialization.jFun (q := p)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : AlgebraicClosure ℚ))) ∨ P.IsInftySide W)
    (h_ii : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), P.IsInftySide W →
      (PlaceSpecialization.jFun (q := p))⁻¹ ∈ W.toValuationSubring)
    (h_iii : (P.redFst (cuspInftyBar (1 * p))).ord (jBarC (ResidueField ↥A)) = -1)
    (h_iv : ∃ h : PlaceSpecialization.jFun (q := p) ∈ (chartFst R S₁ Wn hWn Γ).integers,
      (chartFst R S₁ Wn hWn Γ).residue ⟨_, h⟩ = jBarC (ResidueField ↥A))
    (h_v : ∀ W ∈ (chartFst R S₁ Wn hWn Γ).dom, (P.redFst W).IsRational) :
    ∀ W ∈ (chartFst R S₁ Wn hWn Γ).dom,
    ∃ h : fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
            (W.evalAt (fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)))
          ∈ (chartFst R S₁ Wn hWn Γ).integers,
      (chartFst R S₁ Wn hWn Γ).residue ⟨_, h⟩ ≠ 0 ∧
      ((chartFst R S₁ Wn hWn Γ).placeMap W).ord ((chartFst R S₁ Wn hWn Γ).residue ⟨_, h⟩) = 1 ∧
      0 < W.ord (fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
            (W.evalAt (fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)))) ∧
      ∀ Q ∈ (chartFst R S₁ Wn hWn Γ).dom, (chartFst R S₁ Wn hWn Γ).placeMap Q = (chartFst R S₁ Wn hWn Γ).placeMap W →
        Q ≠ W →
        Q.ord (fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
              (W.evalAt (fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)))) = 0 := by
  haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨hjint, hjres⟩ := h_iv
  intro W hW
  have hWrat : W.IsRational := isRational_bar (1 * p) W
  have hxrat : ((chartFst R S₁ Wn hWn Γ).placeMap W).IsRational := h_v W hW
  have hpm : ∀ V, (chartFst R S₁ Wn hWn Γ).placeMap V = P.redFst V := fun V => rfl
  rcases h_i W hW with ⟨a, ha⟩ | hinf
  ·
    have hx : P.redFst W = charLGeomPlaceOfPoint (ResidueField ↥A) (IsLocalRing.residue ↥A a) :=
      (Γ.redFst_eq_charLGeomPlaceOfPoint_iff W _).mpr ⟨a, rfl, ha⟩
    have hT : fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W) = (PlaceSpecialization.jFun (q := p)) := by
      rw [hpm, fibreCoordFst, if_pos ⟨_, hx⟩]
    rw [hT]

    have hreg : ∀ w ∈ (chartFst R S₁ Wn hWn Γ).dom, (chartFst R S₁ Wn hWn Γ).placeMap w = (chartFst R S₁ Wn hWn Γ).placeMap W → (PlaceSpecialization.jFun (q := p)) ∈ w.toValuationSubring := by
      intro w hw hwx
      rw [hpm, hpm, hx] at hwx
      obtain ⟨b, -, hb⟩ := (Γ.redFst_eq_charLGeomPlaceOfPoint_iff w _).mp hwx
      have hne : (PlaceSpecialization.jFun (q := p)) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : AlgebraicClosure ℚ) ≠ 0 := by
        intro h0; rw [h0, Place.ord_zero] at hb; exact lt_irrefl _ hb
      have hmem := w.mem_toValuationSubring_of_ord_nonneg_alt hne hb.le
      have := add_mem hmem (w.algebraMap_mem' (b : AlgebraicClosure ℚ))
      rwa [sub_add_cancel] at this

    have hunif : ((chartFst R S₁ Wn hWn Γ).placeMap W).ord ((chartFst R S₁ Wn hWn Γ).residue ⟨(PlaceSpecialization.jFun (q := p)), hjint⟩
        - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) (((chartFst R S₁ Wn hWn Γ).placeMap W).evalAt ((chartFst R S₁ Wn hWn Γ).residue ⟨(PlaceSpecialization.jFun (q := p)), hjint⟩))) = 1 := by
      rw [hjres, hpm, hx]
      set c := IsLocalRing.residue ↥A a
      have h1 : (charLGeomPlaceOfPoint (ResidueField ↥A) c).ord (jBarC (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ c) = 1 := by
        rw [jBarC, ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap, if_pos rfl]
      have hxr : (charLGeomPlaceOfPoint (ResidueField ↥A) c).IsRational := by rw [← hx, ← hpm]; exact hxrat
      have hne : jBarC (ResidueField ↥A) - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) c ≠ 0 := by
        intro h0; rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
      have hmem := (charLGeomPlaceOfPoint (ResidueField ↥A) c).mem_toValuationSubring_of_ord_nonneg_alt hne (by rw [h1]; exact zero_le_one)
      have hjmem : jBarC (ResidueField ↥A) ∈ (charLGeomPlaceOfPoint (ResidueField ↥A) c).toValuationSubring := by
        have := add_mem hmem ((charLGeomPlaceOfPoint (ResidueField ↥A) c).algebraMap_mem' c); rwa [sub_add_cancel] at this
      have hev0 : (charLGeomPlaceOfPoint (ResidueField ↥A) c).evalAt (jBarC (ResidueField ↥A) - algebraMap (ResidueField ↥A) _ c) = 0 :=
        evalAt_eq_zero_of_ord_pos _ hxr hmem (by rw [h1]; exact zero_lt_one)
      have hev : (charLGeomPlaceOfPoint (ResidueField ↥A) c).evalAt (jBarC (ResidueField ↥A)) = c := by
        have hsub := evalAt_sub_algebraMap_of_mem (K := ResidueField ↥A)
          (F := ↥(modularFunctionFieldC (ResidueField ↥A) 1)) (charLGeomPlaceOfPoint (ResidueField ↥A) c) hxr hjmem c
        exact sub_eq_zero.mp (hsub.symm.trans hev0)
      rw [hev]; exact h1
    exact AlgebraicCurve.ComponentChart.fibreParam_laws_of_ord_residue_sub_eq_one (chartFst R S₁ Wn hWn Γ) W hW hWrat hxrat (PlaceSpecialization.jFun (q := p)) hjint hreg hunif
  ·
    have hcsp : P.IsCuspidal W := hinf.1
    have hx : P.redFst W = P.redFst (cuspInftyBar (1 * p)) := Γ.redFst_eq_of_isInftySide W hinf
    have hT : fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W) = (PlaceSpecialization.jFun (q := p))⁻¹ := by
      rw [hpm, fibreCoordFst, if_neg]
      rintro ⟨c, hc⟩
      exact Γ.redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal hcsp c hc
    rw [hT]

    have hj0 : (chartFst R S₁ Wn hWn Γ).residue ⟨(PlaceSpecialization.jFun (q := p)), hjint⟩ ≠ 0 := by
      rw [hjres]; intro h0
      have hc : ((jBarC (ResidueField ↥A) : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
          LaurentSeries (ResidueField ↥A)).coeff (-1) = 0 := by rw [h0]; simp
      rw [show ((jBarC (ResidueField ↥A) : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
          LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) from rfl, coeff_jqModC_neg_one] at hc
      exact one_ne_zero hc
    obtain ⟨hjinv, hresinv⟩ := inv_mem_integers_of_residue_ne_zero (chartFst R S₁ Wn hWn Γ) hjint hj0
    have hreg : ∀ w ∈ (chartFst R S₁ Wn hWn Γ).dom, (chartFst R S₁ Wn hWn Γ).placeMap w = (chartFst R S₁ Wn hWn Γ).placeMap W → (PlaceSpecialization.jFun (q := p))⁻¹ ∈ w.toValuationSubring := by
      intro w hw hwx
      rw [hpm, hpm, hx] at hwx
      exact h_ii w ((redFst_eq_redFst_cuspInftyBar_iff_of_mem_chartFst_dom R S₁ Wn hWn Γ w hw).mp hwx)
    have hunif : ((chartFst R S₁ Wn hWn Γ).placeMap W).ord ((chartFst R S₁ Wn hWn Γ).residue ⟨(PlaceSpecialization.jFun (q := p))⁻¹, hjinv⟩
        - algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) (((chartFst R S₁ Wn hWn Γ).placeMap W).evalAt ((chartFst R S₁ Wn hWn Γ).residue ⟨(PlaceSpecialization.jFun (q := p))⁻¹, hjinv⟩))) = 1 := by
      rw [hresinv, hjres, hpm, hx]
      set xinf := P.redFst (cuspInftyBar (1 * p))
      have h1 : xinf.ord (jBarC (ResidueField ↥A))⁻¹ = 1 := by rw [Place.ord_inv, h_iii]; rfl
      have hxr : xinf.IsRational := by rw [← hx, ← hpm]; exact hxrat
      have hne : (jBarC (ResidueField ↥A))⁻¹ ≠ 0 := by intro h0; rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
      have hmem := xinf.mem_toValuationSubring_of_ord_nonneg_alt hne (by rw [h1]; exact zero_le_one)
      have hev : xinf.evalAt (jBarC (ResidueField ↥A))⁻¹ = 0 := evalAt_eq_zero_of_ord_pos _ hxr hmem (by rw [h1]; exact zero_lt_one)
      rw [hev, map_zero, sub_zero]; exact h1
    exact AlgebraicCurve.ComponentChart.fibreParam_laws_of_ord_residue_sub_eq_one (chartFst R S₁ Wn hWn Γ) W hW hWrat hxrat _ hjinv hreg hunif

theorem chartFst_fibreCoords (hA : A.LiesOverPrime p) (R : LevelOneProlongationPair P)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
    (Wn : Finset (Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)))
    (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (ResidueField ↥A)) (Γ : R.ChartFstSupply S₁) :
    ∀ W ∈ (chartFst R S₁ Wn hWn Γ).dom,
    ∃ h : fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
            (W.evalAt (fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)))
          ∈ (chartFst R S₁ Wn hWn Γ).integers,
      (chartFst R S₁ Wn hWn Γ).residue ⟨_, h⟩ ≠ 0 ∧
      ((chartFst R S₁ Wn hWn Γ).placeMap W).ord ((chartFst R S₁ Wn hWn Γ).residue ⟨_, h⟩) = 1 ∧
      0 < W.ord (fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
            (W.evalAt (fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)))) ∧
      ∀ Q ∈ (chartFst R S₁ Wn hWn Γ).dom, (chartFst R S₁ Wn hWn Γ).placeMap Q = (chartFst R S₁ Wn hWn Γ).placeMap W →
        Q ≠ W →
        Q.ord (fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
              (W.evalAt (fibreCoordFst p (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W)))) = 0 := by
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  exact chartFst_fibreCoords_of_hyps R S₁ Wn hWn Γ
    (exists_ord_jFun_sub_pos_or_isInftySide_of_mem_chartFst_dom R S₁ Wn hWn Γ)
    (jFun_inv_mem_of_isInftySide (p := p) (P := P))
    (ord_redFst_cuspInftyBar_jBarC Γ)
    (jFun_mem_chartFst_integers_residue_eq hA R S₁ Wn hWn Γ)
    (fun W _ => isRational_place_modularFunctionFieldC_one (ResidueField ↥A) ((chartFst R S₁ Wn hWn Γ).placeMap W))

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord.ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord.ModularCurve.PlaceSpecialization.LevelOneProlongationPair"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord.ModularCurve"

p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord.ModularCurve.PlaceSpecialization.LevelOneProlongationPair"

theorem solution
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (IsLocalRing.ResidueField ↥A) p] [DecidableEq (IsLocalRing.ResidueField ↥A)]
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    {P : PlaceSpecialization A p 1 data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ}
    (hA : A.LiesOverPrime p) (R : LevelOneProlongationPair P)
    (S₁ : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))))
    (Wn : Finset (Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)))
    (hWn : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (IsLocalRing.ResidueField ↥A)) (Γ : R.ChartFstSupply S₁) :
    ∃ T : Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) →
        ↥(modularFunctionFieldBar (1 * p)),
    ∀ W ∈ (chartFst R S₁ Wn hWn Γ).dom,
    ∃ h : T ((chartFst R S₁ Wn hWn Γ).placeMap W)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
            (W.evalAt (T ((chartFst R S₁ Wn hWn Γ).placeMap W)))
          ∈ (chartFst R S₁ Wn hWn Γ).integers,
      (chartFst R S₁ Wn hWn Γ).residue ⟨_, h⟩ ≠ 0 ∧
      ((chartFst R S₁ Wn hWn Γ).placeMap W).ord ((chartFst R S₁ Wn hWn Γ).residue ⟨_, h⟩) = 1 ∧
      0 < W.ord (T ((chartFst R S₁ Wn hWn Γ).placeMap W)
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
            (W.evalAt (T ((chartFst R S₁ Wn hWn Γ).placeMap W)))) ∧
      ∀ Q ∈ (chartFst R S₁ Wn hWn Γ).dom, (chartFst R S₁ Wn hWn Γ).placeMap Q = (chartFst R S₁ Wn hWn Γ).placeMap W →
        Q ≠ W →
        Q.ord (T ((chartFst R S₁ Wn hWn Γ).placeMap W)
          - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
              (W.evalAt (T ((chartFst R S₁ Wn hWn Γ).placeMap W)))) = 0 :=
  ⟨ModularCurve.PlaceSpecialization.LevelOneProlongationPair.fibreCoordFst p (IsLocalRing.ResidueField ↥A),
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_fibreCoords hA R S₁ Wn hWn Γ⟩

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_exists_fibreCoord (solution)
