-- Prove2me | solution 1 for ModularCurve.MultCovering.cuspInftyBar_not_mem_zeroChart_dom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9a7f10c5-a9c0-5f46-8f29-1314798f904f

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_not_isInftySide_of_isZeroSide
import Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_frickeInvolutionBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeTwo_frickeInvolutionBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isZeroSide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_cuspInftyBar_not_mem_zeroChart_dom
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_cuspInftyBar_not_mem_zeroChart_dom.ModularCurve ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "cuspInftyBar qExpand jq ModularPolynomialData modularFunctionFieldBar coeffEmb PlaceSpecialization.jFun PlaceSpecialization.jqFun PlaceSpecialization.tInfty PlaceSpecialization.tZero modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence charLGeomPlaceEquiv charLGeomPlaceOfPoint frickeInvolutionBar IsAffineGeomPlace not_isInftySide_of_isZeroSide not_isStrictType_of_isCuspidal geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "ChartCtx zeroChart chart"
p2m_open "ModularCurve.MultCovering ModularCurve"

section Seams

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem jQFun_tuple_eq_mc : ProlongationTuple.jQFun 1 q = PlaceSpecialization.jqFun (q := q) := by
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
  have key : ∀ (n : ℕ) [NeZero n], n = q → qExpand ℚ n jq = qExpand ℚ q jq := by
    intro n _ hn
    subst hn
    rfl
  rw [key (1 * q) (one_mul q)]

theorem tInfty_tuple_eq_mc : ProlongationTuple.tInfty 1 q = PlaceSpecialization.tInfty (q := q) := by
  show ProlongationTuple.jQFun 1 q / ProlongationTuple.jFun 1 q ^ q =
    PlaceSpecialization.jqFun (q := q) / PlaceSpecialization.jFun (q := q) ^ (1 * q)
  rw [jQFun_tuple_eq_mc, pow_mul, pow_one]
  rfl

theorem tZero_tuple_eq_mc : ProlongationTuple.tZero 1 q = PlaceSpecialization.tZero (q := q) := by
  show ProlongationTuple.jFun 1 q / ProlongationTuple.jQFun 1 q ^ q =
    PlaceSpecialization.jFun (q := q) / PlaceSpecialization.jqFun (q := q) ^ (1 * q)
  rw [jQFun_tuple_eq_mc, pow_mul, pow_one]
  rfl

variable (P)

theorem isInftySide_tuple_iff_mc (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    ProlongationTuple.IsInftySide P W ↔ P.IsInftySide W := by
  show (ProlongationTuple.IsCuspidal P W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (ProlongationTuple.tInfty 1 q) (τ : AlgebraicClosure ℚ)) ↔
    (P.IsCuspidal W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (PlaceSpecialization.tInfty (q := q)) (τ : AlgebraicClosure ℚ))
  rw [tInfty_tuple_eq_mc]
  rfl

theorem isZeroSide_tuple_iff_mc (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    ProlongationTuple.IsZeroSide P W ↔ P.IsZeroSide W := by
  show (ProlongationTuple.IsCuspidal' P W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (ProlongationTuple.tZero 1 q) (τ : AlgebraicClosure ℚ)) ↔
    (IsCuspidal' P W ∧ ∃ τ : A, red τ = 1 ∧ W.HasValue (PlaceSpecialization.tZero (q := q)) (τ : AlgebraicClosure ℚ))
  have hc : ProlongationTuple.IsCuspidal' P W ↔ IsCuspidal' P W := by
    show (∀ a : A, W.ord (ProlongationTuple.jQFun 1 q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
        (a : AlgebraicClosure ℚ)) ≤ 0) ↔
      (∀ a : A, W.ord (PlaceSpecialization.jqFun (q := q) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))
        (a : AlgebraicClosure ℚ)) ≤ 0)
    rw [jQFun_tuple_eq_mc]
  rw [tZero_tuple_eq_mc, hc]

theorem isInftySide_frickeInvolutionBar_smul_iff_mc (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    P.IsInftySide (frickeInvolutionBar (1 * q) • W) ↔ P.IsZeroSide W := by
  have h := ProlongationTuple.isInftySide_atkinLehnerBar_smul_iff P
    (fun hd => (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp hd)) W
  rw [isInftySide_tuple_iff_mc, isZeroSide_tuple_iff_mc] at h
  have hw : ProlongationTuple.atkinLehnerBar 1 q = frickeInvolutionBar (1 * q) :=
    geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar q
  rwa [hw] at h

theorem isZeroSide_frickeInvolutionBar_smul_iff_mc (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    P.IsZeroSide (frickeInvolutionBar (1 * q) • W) ↔ P.IsInftySide W := by
  have h := ProlongationTuple.isZeroSide_atkinLehnerBar_smul_iff P
    (fun hd => (Fact.out : q.Prime).ne_one (Nat.dvd_one.mp hd)) W
  rw [isInftySide_tuple_iff_mc, isZeroSide_tuple_iff_mc] at h
  have hw : ProlongationTuple.atkinLehnerBar 1 q = frickeInvolutionBar (1 * q) :=
    geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar q
  rwa [hw] at h

theorem isCuspidal_of_isInftySide_mc {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : P.IsInftySide W) : P.IsCuspidal W := h.1

theorem isCuspidal_iff_not_isAffineGeomPlace_mc (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    P.IsCuspidal W ↔ ¬ IsAffineGeomPlace k 1 (P.redFst W) :=
  ⟨fun h => ProlongationTuple.not_isAffineGeomPlace_reduceFst_of_isCuspidal P W h,
   fun h => ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst P W h⟩

end Seams

section Dichotomy

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem frob_eq_redFst_cuspInftyBar_iff_mc (x : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
    frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr x = Γ.P.redFst (cuspInftyBar (1 * p)) ↔
      x = Γ.P.redFst (cuspInftyBar (1 * p)) := by
  classical
  constructor
  · intro h
    rcases RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty (ResidueField ↥A)
        ((charLGeomPlaceEquiv (ResidueField ↥A)).symm x) with ⟨c, hc⟩ | hinf
    · have hx : x = charLGeomPlaceOfPoint (ResidueField ↥A) c := by
        rw [charLGeomPlaceOfPoint, ← hc, Equiv.apply_symm_apply]
      rw [hx, Γ.supply.frob_charLGeomPlaceOfPoint] at h
      exact (Γ.supply.redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal Γ.supply.isInftySide_cuspInftyBar.1 _ h.symm).elim
    · rw [Γ.P.redFst_cuspInftyBar, ← hinf, Equiv.apply_symm_apply]
  · intro h
    rw [h]
    have h2 := Γ.supply.cusp_fixed

    rcases RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty (ResidueField ↥A)
        ((charLGeomPlaceEquiv (ResidueField ↥A)).symm
          (frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst (cuspInftyBar (1 * p))))) with ⟨c, hc⟩ | hinf
    · have hx : frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst (cuspInftyBar (1 * p)))
          = charLGeomPlaceOfPoint (ResidueField ↥A) c := by
        rw [charLGeomPlaceOfPoint, ← hc, Equiv.apply_symm_apply]
      rw [hx, Γ.supply.frob_charLGeomPlaceOfPoint] at h2
      exact (Γ.supply.redFst_ne_charLGeomPlaceOfPoint_of_isCuspidal Γ.supply.isInftySide_cuspInftyBar.1 _ h2.symm).elim
    · have hy : frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst (cuspInftyBar (1 * p)))
          = charLGeomPlaceEquiv (ResidueField ↥A) (RationalFunctionField.placeInfty (ResidueField ↥A)) := by
        rw [← hinf, Equiv.apply_symm_apply]
      rw [hy, Γ.P.redFst_cuspInftyBar]

theorem redSnd_eq_of_redFst_eq_cusp_mc {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))}
    (h : Γ.P.redFst W = Γ.P.redFst (cuspInftyBar (1 * p))) : Γ.P.redSnd W = Γ.P.redFst (cuspInftyBar (1 * p)) := by
  rcases Γ.P.d1 W with h1 | h1
  ·
    have h1' : Γ.P.redFst W = frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redSnd W) := h1
    exact (frob_eq_redFst_cuspInftyBar_iff_mc Γ _).mp (h1'.symm.trans h)
  ·
    have h1' : frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst W) = Γ.P.redSnd W := h1
    rw [← h1', h]
    exact (frob_eq_redFst_cuspInftyBar_iff_mc Γ _).mpr rfl

end Dichotomy

end ModularCurve.MultCovering

open _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_MultCovering_cuspInftyBar_not_mem_zeroChart_dom.ModularCurve.MultCovering in

theorem solution
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    cuspInftyBar (1 * p) ∉ (zeroChart Γ).dom := by
  classical
  have hI : Γ.P.IsInftySide (cuspInftyBar (1 * p)) := Γ.supply.isInftySide_cuspInftyBar
  intro h
  have h' : Γ.P.IsStrictTypeOne (frickeInvolutionBar (1 * p) • cuspInftyBar (1 * p)) ∨
      Γ.P.IsInftySide (frickeInvolutionBar (1 * p) • cuspInftyBar (1 * p)) ∨
      frickeInvolutionBar (1 * p) • cuspInftyBar (1 * p) ∈ Γ.S₁ := h
  rw [isStrictTypeOne_frickeInvolutionBar_smul_iff, isInftySide_frickeInvolutionBar_smul_iff_mc] at h'
  rcases h' with h2 | hZ | hS
  · exact (not_isStrictType_of_isCuspidal Γ.P _ hI.1).2 h2
  · exact not_isInftySide_of_isZeroSide Γ.P _ hZ hI
  ·
    have haff := Γ.supply.sheet.sheet_affine _ hS
    rw [redFst_frickeInvolutionBar_smul, redSnd_eq_of_redFst_eq_cusp_mc Γ rfl] at haff
    exact (isCuspidal_iff_not_isAffineGeomPlace_mc Γ.P _).mp hI.1 haff

end S_ModularCurve_MultCovering_cuspInftyBar_not_mem_zeroChart_dom
end P2MW
export P2MW.S_ModularCurve_MultCovering_cuspInftyBar_not_mem_zeroChart_dom (solution)
