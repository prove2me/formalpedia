-- Prove2me | solution 1 for ModularCurve.MultCovering.mem_infChart_dom_xor_mem_zeroChart_dom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/739ed65d-158c-5644-9fe7-e8c2aed4399e

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_not_isInftySide_of_isZeroSide
import Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_frickeInvolutionBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeTwo_frickeInvolutionBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo
import Theorems.Thm_ModularCurve_PlaceSpecialization_not_isStrictTypeOne_and_isStrictTypeTwo
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isInftySide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isZeroSide_atkinLehnerBar_smul_iff
import Theorems.Thm_ModularCurve_geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_eq_iff_centred_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isAffineGeomPlace_reduceFst_of_isCuspidal
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_not_fixed_reduceFst_of_isStrictSnd
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_mem_infChart_dom_xor_mem_zeroChart_dom
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_mem_infChart_dom_xor_mem_zeroChart_dom.ModularCurve ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "cuspInftyBar qExpand jq ModularPolynomialData modularFunctionFieldBar coeffEmb ssJSet PlaceSpecialization.jFun PlaceSpecialization.jqFun PlaceSpecialization.tInfty PlaceSpecialization.tZero modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence charLGeomPlaceEquiv charLGeomPlaceOfPoint frickeInvolutionBar ssPlaces jGeomGen IsAffineGeomPlace isInftySide_or_isZeroSide_of_isCuspidal not_isInftySide_of_isZeroSide not_isStrictType_of_isCuspidal geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "IsSSCentred ChartCtx infChart zeroChart chart"
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

theorem not_fixed_redFst_of_isStrictTypeTwo_mc {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : P.IsStrictTypeTwo W) :
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W)) ≠ P.redFst W :=
  not_fixed_reduceFst_of_isStrictSnd P W h

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

theorem redFst_not_mem_ssPlaces_of_not_isSSCentred_mc {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))}
    (hW : ∀ a ∈ ssJSet p (ResidueField ↥A), ¬ IsSSCentred p A W a) :
    Γ.P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A) := by
  intro hss
  set w := Γ.P.redFst W with hw
  have ha : w.evalAt (jGeomGen (ResidueField ↥A) 1) ∈ ssJSet p (ResidueField ↥A) := hss.2.2
  have hc := (reduceFst_eq_iff_centred_levelOne Γ.P w hss _ rfl W).mp hw.symm
  apply hW _ ha
  refine ⟨hc.1, ?_⟩
  obtain ⟨y, hy, hyo⟩ := hc.2
  refine ⟨y, hy, ?_⟩
  rw [jQFun_tuple_eq_mc] at hyo
  exact hyo

end Dichotomy

end ModularCurve.MultCovering

open _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_MultCovering_mem_infChart_dom_xor_mem_zeroChart_dom.ModularCurve.MultCovering in

theorem solution
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hsep : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      W ∈ Γ.S₁ → frickeInvolutionBar (1 * p) • W ∉ Γ.S₁)
    (hcov : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr
          (frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst W)) = Γ.P.redFst W →
      IsAffineGeomPlace (ResidueField ↥A) 1 (Γ.P.redFst W) → Γ.P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A) →
      W ∈ Γ.S₁ ∨ frickeInvolutionBar (1 * p) • W ∈ Γ.S₁)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (hW : ∀ a ∈ ssJSet p (ResidueField ↥A), ¬ IsSSCentred p A W a) :
    Xor (W ∈ (infChart Γ).dom) (W ∈ (zeroChart Γ).dom) := by
  classical

  have hinf : W ∈ (infChart Γ).dom ↔ Γ.P.IsStrictTypeOne W ∨ Γ.P.IsInftySide W ∨ W ∈ Γ.S₁ := Iff.rfl
  have hzero : W ∈ (zeroChart Γ).dom ↔
      Γ.P.IsStrictTypeTwo W ∨ Γ.P.IsZeroSide W ∨ frickeInvolutionBar (1 * p) • W ∈ Γ.S₁ := by
    show (frickeInvolutionBar (1 * p) • W ∈ (infChart Γ).dom) ↔ _
    show (Γ.P.IsStrictTypeOne (frickeInvolutionBar (1 * p) • W) ∨ Γ.P.IsInftySide (frickeInvolutionBar (1 * p) • W) ∨
        frickeInvolutionBar (1 * p) • W ∈ Γ.S₁) ↔ _
    rw [isStrictTypeOne_frickeInvolutionBar_smul_iff, isInftySide_frickeInvolutionBar_smul_iff_mc]
  rw [hinf, hzero]

  have hS_fixed : ∀ V ∈ Γ.S₁, frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst V)) = Γ.P.redFst V := Γ.supply.sheet.sheet_fixed
  have hS_aff : ∀ V ∈ Γ.S₁, IsAffineGeomPlace (ResidueField ↥A) 1 (Γ.P.redFst V) := Γ.supply.sheet.sheet_affine

  have hwred : Γ.P.redFst (frickeInvolutionBar (1 * p) • W) = Γ.P.redSnd W := redFst_frickeInvolutionBar_smul Γ.P W

  have hZS_snd : Γ.P.IsZeroSide W → Γ.P.redSnd W = Γ.P.redFst (cuspInftyBar (1 * p)) := fun hz => by
    rw [← hwred]
    exact Γ.supply.redFst_eq_of_isInftySide _ ((isInftySide_frickeInvolutionBar_smul_iff_mc Γ.P W).mpr hz)
  have hcusp_not_aff : ¬ IsAffineGeomPlace (ResidueField ↥A) 1 (Γ.P.redFst (cuspInftyBar (1 * p))) :=
    (isCuspidal_iff_not_isAffineGeomPlace_mc Γ.P _).mp Γ.supply.isInftySide_cuspInftyBar.1

  have hwS_aff : frickeInvolutionBar (1 * p) • W ∈ Γ.S₁ → IsAffineGeomPlace (ResidueField ↥A) 1 (Γ.P.redSnd W) :=
    fun h => hwred ▸ hS_aff _ h
  have hwS_fixed : frickeInvolutionBar (1 * p) • W ∈ Γ.S₁ → frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redSnd W)) = Γ.P.redSnd W :=
    fun h => hwred ▸ hS_fixed _ h

  have hSTO_snd : Γ.P.IsStrictTypeOne W → frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr
      (frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redSnd W)) ≠ Γ.P.redSnd W := fun h1 => by
    have h2 : Γ.P.IsStrictTypeTwo (frickeInvolutionBar (1 * p) • W) :=
      (isStrictTypeTwo_frickeInvolutionBar_smul_iff Γ.P W).mpr h1
    have := not_fixed_redFst_of_isStrictTypeTwo_mc Γ.P h2
    rwa [hwred] at this
  by_cases hc : Γ.P.IsCuspidal W
  ·
    have hsides := isInftySide_or_isZeroSide_of_isCuspidal Γ.P W hc
    have hnst := not_isStrictType_of_isCuspidal Γ.P W hc
    have hnaff : ¬ IsAffineGeomPlace (ResidueField ↥A) 1 (Γ.P.redFst W) :=
      (isCuspidal_iff_not_isAffineGeomPlace_mc Γ.P W).mp hc
    have hWS : W ∉ Γ.S₁ := fun h => hnaff (hS_aff W h)
    rcases hsides with hI | hZ
    ·
      have hnZ : ¬ Γ.P.IsZeroSide W := fun hZ => not_isInftySide_of_isZeroSide Γ.P W hZ hI
      have hsnd : Γ.P.redSnd W = Γ.P.redFst (cuspInftyBar (1 * p)) :=
        redSnd_eq_of_redFst_eq_cusp_mc Γ (Γ.supply.redFst_eq_of_isInftySide W hI)
      have hwS : frickeInvolutionBar (1 * p) • W ∉ Γ.S₁ := fun h => hcusp_not_aff (hsnd ▸ hwS_aff h)
      exact Or.inl ⟨Or.inr (Or.inl hI), fun h => h.elim hnst.2 (fun h => h.elim hnZ hwS)⟩
    ·
      have hnI : ¬ Γ.P.IsInftySide W := not_isInftySide_of_isZeroSide Γ.P W hZ
      exact Or.inr ⟨Or.inr (Or.inl hZ), fun h => h.elim hnst.1 (fun h => h.elim hnI hWS)⟩
  ·
    have haff : IsAffineGeomPlace (ResidueField ↥A) 1 (Γ.P.redFst W) :=
      not_not.mp (fun h => hc ((isCuspidal_iff_not_isAffineGeomPlace_mc Γ.P W).mpr h))
    have hnI : ¬ Γ.P.IsInftySide W := fun h => hc h.1
    have hnZ : ¬ Γ.P.IsZeroSide W := fun hZ => by

      have hsnd := hZS_snd hZ
      apply hcusp_not_aff
      rcases Γ.P.d1 W with h1 | h1
      ·
        have h1' : Γ.P.redFst W = frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redSnd W) := h1
        have : Γ.P.redFst W = Γ.P.redFst (cuspInftyBar (1 * p)) := by
          rw [h1', hsnd]; exact (frob_eq_redFst_cuspInftyBar_iff_mc Γ _).mpr rfl
        rwa [this] at haff
      ·
        have h1' : frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst W) = Γ.P.redSnd W := h1
        have : Γ.P.redFst W = Γ.P.redFst (cuspInftyBar (1 * p)) :=
          (frob_eq_redFst_cuspInftyBar_iff_mc Γ _).mp (h1'.trans hsnd)
        rwa [this] at haff
    by_cases hfix : frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr
        (frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst W)) = Γ.P.redFst W
    ·
      have hnss := redFst_not_mem_ssPlaces_of_not_isSSCentred_mc Γ hW
      have hn1 : ¬ Γ.P.IsStrictTypeOne W := fun h => h.2 hfix
      have hn2 : ¬ Γ.P.IsStrictTypeTwo W := fun h => not_fixed_redFst_of_isStrictTypeTwo_mc Γ.P h hfix
      rcases hcov W hfix haff hnss with hS | hwS
      · exact Or.inl ⟨Or.inr (Or.inr hS), fun h => h.elim hn2 (fun h => h.elim hnZ (hsep W hS))⟩
      · have hWS : W ∉ Γ.S₁ := fun h => hsep W h hwS
        exact Or.inr ⟨Or.inr (Or.inr hwS), fun h => h.elim hn1 (fun h => h.elim hnI hWS)⟩
    ·
      have hWS : W ∉ Γ.S₁ := fun h => hfix (hS_fixed W h)
      rcases isStrictTypeOne_or_isStrictTypeTwo Γ.P W hfix with h1 | h2
      · have hn2 : ¬ Γ.P.IsStrictTypeTwo W := fun h2 => not_isStrictTypeOne_and_isStrictTypeTwo Γ.P W ⟨h1, h2⟩
        have hwS : frickeInvolutionBar (1 * p) • W ∉ Γ.S₁ := fun h => hSTO_snd h1 (hwS_fixed h)
        exact Or.inl ⟨Or.inl h1, fun h => h.elim hn2 (fun h => h.elim hnZ hwS)⟩
      · have hn1 : ¬ Γ.P.IsStrictTypeOne W := fun h1 => not_isStrictTypeOne_and_isStrictTypeTwo Γ.P W ⟨h1, h2⟩
        exact Or.inr ⟨Or.inl h2, fun h => h.elim hn1 (fun h => h.elim hnI hWS)⟩

end S_ModularCurve_MultCovering_mem_infChart_dom_xor_mem_zeroChart_dom
end P2MW
export P2MW.S_ModularCurve_MultCovering_mem_infChart_dom_xor_mem_zeroChart_dom (solution)
