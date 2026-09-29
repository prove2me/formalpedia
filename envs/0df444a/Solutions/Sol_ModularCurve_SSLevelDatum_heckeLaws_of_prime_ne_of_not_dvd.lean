-- Prove2me | solution 1 for ModularCurve.SSLevelDatum.heckeLaws_of_prime_ne_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f670e825-2740-5ccf-bcff-d32f379e1078

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_correspondence_heckeBetaC_heckeAlphaC_comm
import Theorems.Thm_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_heckeBetaC_heckeAlphaC_comm_of_ne_of_not_dvd
import Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_of_restrictAlong_heckeBetaC_mem_ssPlaces
import Theorems.Thm_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Theorems.Thm_AlgebraicCurve_SemilinearAut_correspondence_smul
import Theorems.Thm_ModularCurve_exists_semilinearAut_intertwinesAlong_heckeAlphaC_heckeBetaC_coeffSemilinearAut
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_arithFrobC_smul_mem_ssPlaces
import Theorems.Thm_ModularCurve_SSLevelDatum_degeneracyData_b_eq_a_atkinLehnerPerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSLevelDatum_heckeLaws_of_prime_ne_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open AlgebraicCurve ModularCurve

namespace LawsCore

section MatrixCalculus

variable {K F₁ F₂ F₃ : Type*} [Field K] [Field F₁] [Field F₂] [Field F₃]
  [Algebra K F₁] [Algebra K F₂] [Algebra K F₃]

def mat (S₁ : Set (Place K F₁)) (S₂ : Set (Place K F₂)) (Φ : Divisor K F₁ →+ Divisor K F₂) :
    Matrix ↥S₂ ↥S₁ ℤ :=
  Matrix.of fun t s => Φ (Finsupp.single s.1 1) t.1

theorem mat_apply (S₁ : Set (Place K F₁)) (S₂ : Set (Place K F₂)) (Φ : Divisor K F₁ →+ Divisor K F₂)
    (t : ↥S₂) (s : ↥S₁) : mat S₁ S₂ Φ t s = Φ (Finsupp.single s.1 1) t.1 := rfl

def Stable (S₁ : Set (Place K F₁)) (S₂ : Set (Place K F₂)) (Φ : Divisor K F₁ →+ Divisor K F₂) : Prop :=
  ∀ s ∈ S₁, ∀ t, Φ (Finsupp.single s 1) t ≠ 0 → t ∈ S₂

theorem eq_sum_single_of_support_subset (S : Set (Place K F₁)) [Fintype ↥S] (D : Divisor K F₁)
    (hD : ∀ w, D w ≠ 0 → w ∈ S) : D = ∑ s : ↥S, Finsupp.single s.1 (D s.1) := by
  classical
  ext w
  rw [Finsupp.finsetSum_apply]
  by_cases hw : w ∈ S
  · rw [Finset.sum_eq_single (⟨w, hw⟩ : ↥S)]
    · simp
    · rintro b - hb
      rw [Finsupp.single_apply, if_neg]
      exact fun h => hb (Subtype.ext h)
    · exact fun h => absurd (Finset.mem_univ _) h
  · have h0 : D w = 0 := by
      by_contra h
      exact hw (hD w h)
    rw [h0, eq_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact hw s.2

theorem apply_eq_sum_of_support_subset (S : Set (Place K F₁)) [Fintype ↥S] (Φ : Divisor K F₁ →+ Divisor K F₂)
    (D : Divisor K F₁) (hD : ∀ w, D w ≠ 0 → w ∈ S) (t : Place K F₂) :
    Φ D t = ∑ s : ↥S, Φ (Finsupp.single s.1 1) t * D s.1 := by
  conv_lhs => rw [eq_sum_single_of_support_subset S D hD]
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : Finsupp.single s.1 (D s.1) = D s.1 • Finsupp.single s.1 (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h, map_zsmul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

theorem mat_comp (S₁ : Set (Place K F₁)) (S₂ : Set (Place K F₂)) (S₃ : Set (Place K F₃)) [Fintype ↥S₂]
    (Φ : Divisor K F₁ →+ Divisor K F₂) (Ψ : Divisor K F₂ →+ Divisor K F₃) (hΦ : Stable S₁ S₂ Φ) :
    mat S₁ S₃ (Ψ.comp Φ) = mat S₂ S₃ Ψ * mat S₁ S₂ Φ := by
  ext t s
  rw [mat_apply, Matrix.mul_apply, AddMonoidHom.comp_apply,
    apply_eq_sum_of_support_subset S₂ Ψ _ (fun w hw => hΦ s.1 s.2 w hw) t.1]
  rfl

theorem commute_mat (S : Set (Place K F₁)) [Fintype ↥S] (Φ Ψ : Divisor K F₁ →+ Divisor K F₁)
    (hΦ : Stable S S Φ) (hΨ : Stable S S Ψ)
    (h : ∀ s ∈ S, Φ (Ψ (Finsupp.single s 1)) = Ψ (Φ (Finsupp.single s 1))) :
    Commute (mat S S Φ) (mat S S Ψ) := by
  have h1 : mat S S (Φ.comp Ψ) = mat S S (Ψ.comp Φ) := by
    ext t s
    simp only [mat_apply, AddMonoidHom.comp_apply, h s.1 s.2]
  have h2 := mat_comp S S S Ψ Φ hΨ
  have h3 := mat_comp S S S Φ Ψ hΦ
  show mat S S Φ * mat S S Ψ = mat S S Ψ * mat S S Φ
  rw [← h2, ← h3, h1]

theorem mat_intertwine (S₁ : Set (Place K F₁)) (S₂ : Set (Place K F₂)) [Fintype ↥S₁] [Fintype ↥S₂]
    (T₁ : Divisor K F₁ →+ Divisor K F₁) (T₂ : Divisor K F₂ →+ Divisor K F₂)
    (P Q : Divisor K F₁ →+ Divisor K F₂) (hT₁ : Stable S₁ S₁ T₁) (hQ : Stable S₁ S₂ Q)
    (h : ∀ s ∈ S₁, P (T₁ (Finsupp.single s 1)) = T₂ (Q (Finsupp.single s 1))) :
    mat S₁ S₂ P * mat S₁ S₁ T₁ = mat S₂ S₂ T₂ * mat S₁ S₂ Q := by
  rw [← mat_comp S₁ S₁ S₂ T₁ P hT₁, ← mat_comp S₁ S₂ S₂ Q T₂ hQ]
  ext t s
  simp only [mat_apply, AddMonoidHom.comp_apply, h s.1 s.2]

end MatrixCalculus

section PlaceCalculus

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F'']

theorem restrictAlong_toValuationSubring (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).toValuationSubring = w.toValuationSubring.comap φ.toRingHom := rfl

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem restrictAlong_comp (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral)
    (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (w : Place K F'') :
    w.restrictAlong (χ.comp φ) hχφ = (w.restrictAlong χ hχ).restrictAlong φ hφ := by
  ext1
  rfl

theorem smul_restrictAlong_semilinear (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (g : SemilinearAut K F) (g' : SemilinearAut K F')
    (hint : SemilinearAut.IntertwinesAlong φ.toRingHom g g') (w : Place K F') :
    (g' • w).restrictAlong φ hφ = g • w.restrictAlong φ hφ := by
  ext1
  refine SetLike.ext fun x => ?_
  rw [restrictAlong_toValuationSubring, ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
    SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_restrictAlong_iff]
  have key : φ (g⁻¹ • x) = g'⁻¹ • φ.toRingHom x := by
    have h := hint (g⁻¹ • x)
    rw [smul_inv_smul] at h
    have h2 := congrArg (fun y => g'⁻¹ • y) h
    simp only [inv_smul_smul] at h2
    exact h2
  rw [key]

end PlaceCalculus

section Corr

variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [DecidableEq K] (N : ℕ) [NeZero N]

abbrev corr (ℓ : ℕ) [NeZero ℓ] [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)]
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral) :
    Divisor K ↥(modularFunctionFieldC K N) →+ Divisor K ↥(modularFunctionFieldC K N) :=
  Divisor.correspondence (heckeBetaC K N ℓ) (heckeAlphaC K N ℓ) hβ hα

variable {p K N}

theorem corr_single (ℓ : ℕ) [NeZero ℓ] [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)]
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (x : Place K ↥(modularFunctionFieldC K N)) :
    corr K N ℓ hα hβ (Finsupp.single x 1)
      = ∑ W ∈ Place.fiberAlong (heckeBetaC K N ℓ) hβ x,
          Finsupp.single (W.restrictAlong (heckeAlphaC K N ℓ) hα)
            ((Place.ramificationIndexAlong (heckeBetaC K N ℓ) W : ℤ)
              * (Place.inertiaDegAlong (heckeAlphaC K N ℓ) hα W : ℤ)) := by
  rw [corr, Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Divisor.pushforwardAlong_single, one_mul]

theorem ssHeckeMatrixC_eq_mat (ℓ : ℕ) [NeZero ℓ] [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)]
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral) :
    ssHeckeMatrixC p K N ℓ hα hβ = mat (ssPlaces p N K) (ssPlaces p N K) (corr K N ℓ hα hβ) := by
  classical
  ext y x
  rw [mat_apply, corr_single, Finsupp.finsetSum_apply]
  show (∑ᶠ W : Place K (charLDegeneracyRoof K N ℓ), _) = _
  rw [finsum_eq_sum_of_support_subset _ (s := Place.fiberAlong (heckeBetaC K N ℓ) hβ x.1) ?_]
  · refine Finset.sum_congr rfl fun W hW => ?_
    rw [Place.mem_fiberAlong] at hW
    rw [Finsupp.single_apply]
    by_cases hy : Place.restrictAlong (heckeAlphaC K N ℓ) hα W = y.1
    · rw [if_pos ⟨hW, hy⟩, if_pos hy]
    · rw [if_neg (fun h => hy h.2), if_neg hy]
  · intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, Place.mem_fiberAlong]
    by_contra hx
    exact hW (if_neg fun h => hx h.1)

theorem stable_corr [IsAlgClosed K] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (hpN : ¬ p ∣ N)
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)]
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral) :
    Stable (ssPlaces p N K) (ssPlaces p N K) (corr K N ℓ hα hβ) := by
  classical
  intro x hx y hy
  rw [corr_single, Finsupp.finsetSum_apply] at hy
  obtain ⟨W, hW, hWy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  rw [Finsupp.single_apply] at hWy
  split_ifs at hWy with hyW
  · rw [← hyW]
    have h := restrictAlong_heckeAlphaC_mem_ssPlaces_of_restrictAlong_heckeBetaC_mem_ssPlaces p N ℓ hℓ hℓp hpN
      (k := K) hα hβ W
    rw [Place.mem_fiberAlong] at hW
    have hW' : Place.restrictAlong (heckeBetaC K N ℓ) hβ W ∈ ssPlaces p N K := by rw [hW]; exact hx
    exact h hW'
  · exact absurd rfl hWy

end Corr

section Frobenius

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] [DecidableEq K] [IsAlgClosed K]
variable {N : ℕ} [NeZero N]

abbrev smulOp {F : Type*} [Field F] [Algebra K F] (g : SemilinearAut K F) : Divisor K F →+ Divisor K F :=
  DistribMulAction.toAddMonoidHom (Divisor K F) g

theorem smulOp_apply {F : Type*} [Field F] [Algebra K F] (g : SemilinearAut K F) (D : Divisor K F) :
    smulOp g D = g • D := rfl

theorem ssFrobMatrixC_eq_mat (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data) :
    ssFrobMatrixC p K N data hKr = mat (ssPlaces p N K) (ssPlaces p N K) (smulOp (arithFrobC p K N)) := by
  classical
  ext y x
  rw [mat_apply, smulOp_apply, SemilinearAut.smul_single, Finsupp.single_apply,
    arithFrobC_smul_eq_frobOnPlacesGeomLevel p K N data hKr x.1]
  show (if frobOnPlacesGeomLevel K N data hKr x.1 = y.1 then (1 : ℤ) else 0) = _
  by_cases h : frobOnPlacesGeomLevel K N data hKr x.1 = y.1
  · simp only [if_pos h]
  · simp only [if_neg h]

theorem stable_smulOp : Stable (ssPlaces p N K) (ssPlaces p N K) (smulOp (arithFrobC p K N)) := by
  classical
  intro x hx y hy
  rw [smulOp_apply, SemilinearAut.smul_single, Finsupp.single_apply] at hy
  split_ifs at hy with h
  · rw [← h]
    exact arithFrobC_smul_mem_ssPlaces p N K x hx
  · exact absurd rfl hy

theorem smul_corr (ℓ : ℕ) [NeZero ℓ] [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)]
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (D : Divisor K ↥(modularFunctionFieldC K N)) :
    arithFrobC p K N • corr K N ℓ hα hβ D = corr K N ℓ hα hβ (arithFrobC p K N • D) := by
  obtain ⟨g', hgα, hgβ⟩ :=
    exists_semilinearAut_intertwinesAlong_heckeAlphaC_heckeBetaC_coeffSemilinearAut N ℓ (k := K) (frobeniusEquiv K p)
  exact (SemilinearAut.correspondence_smul (heckeBetaC K N ℓ) (heckeAlphaC K N ℓ) hβ hα hgβ hgα D).symm

end Frobenius

section OneLevel

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] [DecidableEq K] [IsAlgClosed K]
variable {N : ℕ} [NeZero N]

theorem natCast_ne_zero_of_prime_ne {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) : (ℓ : K) ≠ 0 := fun h =>
  hℓp (((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hℓ).mp ((CharP.cast_eq_zero_iff K p ℓ).mp h)).symm)

theorem natCast_ne_zero_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : (n : K) ≠ 0 := fun h =>
  hn ((CharP.cast_eq_zero_iff K p n).mp h)

theorem hasPrincipalDivisors_roof (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hpN : ¬ p ∣ N) :
    HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ) :=
  hasPrincipalDivisors_charLDegeneracyRoof K N ℓ (natCast_ne_zero_of_not_dvd hpN)
    (natCast_ne_zero_of_prime_ne (Fact.out) hℓp)

theorem ssHeckeFamilyC_of_ne (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (hlegs : ∀ (ℓ : ℕ) [NeZero ℓ], (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) :
    ssHeckeFamilyC p K N data hKr hlegs ℓ =
      (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.pos.ne'⟩; ssHeckeMatrixC p K N ℓ (hlegs ℓ).1 (hlegs ℓ).2) := by
  show (if (ℓ : ℕ) = p then _ else _) = _
  rw [if_neg hℓ]

theorem ssHeckeFamilyC_of_eq (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (hlegs : ∀ (ℓ : ℕ) [NeZero ℓ], (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) = p) :
    ssHeckeFamilyC p K N data hKr hlegs ℓ = ssFrobMatrixC p K N data hKr := by
  show (if (ℓ : ℕ) = p then _ else _) = _
  rw [if_pos hℓ]

theorem ssHeckeFamilyC_eq_mat_corr (hpN : ¬ p ∣ N) (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (hlegs : ∀ (ℓ : ℕ) [NeZero ℓ], (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.pos.ne'⟩
    haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
    haveI : HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ) := hasPrincipalDivisors_roof (K := K) ℓ hℓ hpN
    ssHeckeFamilyC p K N data hKr hlegs ℓ = mat (ssPlaces p N K) (ssPlaces p N K) (corr K N ℓ (hlegs ℓ).1 (hlegs ℓ).2) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.pos.ne'⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  haveI : HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ) := hasPrincipalDivisors_roof (K := K) ℓ hℓ hpN
  rw [ssHeckeFamilyC_of_ne data hKr hlegs ℓ hℓ]
  exact ssHeckeMatrixC_eq_mat (p := p) ℓ (hlegs ℓ).1 (hlegs ℓ).2

theorem commute_ssHeckeFamilyC (hpN : ¬ p ∣ N) [Fintype ↥(ssPlaces p N K)]
    (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (hlegs : ∀ (ℓ : ℕ) [NeZero ℓ], (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (ℓ ℓ' : Nat.Primes) :
    Commute (ssHeckeFamilyC p K N data hKr hlegs ℓ) (ssHeckeFamilyC p K N data hKr hlegs ℓ') := by
  by_cases hℓ : (ℓ : ℕ) = p <;> by_cases hℓ' : (ℓ' : ℕ) = p
  ·
    rw [ssHeckeFamilyC_of_eq data hKr hlegs ℓ hℓ, ssHeckeFamilyC_of_eq data hKr hlegs ℓ' hℓ']
  ·
    rw [ssHeckeFamilyC_of_eq data hKr hlegs ℓ hℓ, ssFrobMatrixC_eq_mat data hKr,
      ssHeckeFamilyC_eq_mat_corr hpN data hKr hlegs ℓ' hℓ']
    haveI : NeZero (ℓ' : ℕ) := ⟨ℓ'.2.pos.ne'⟩
    haveI : Fact (ℓ' : ℕ).Prime := ⟨ℓ'.2⟩
    haveI : HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ') := hasPrincipalDivisors_roof (K := K) ℓ' hℓ' hpN
    refine commute_mat _ _ _ stable_smulOp (stable_corr (p := p) ℓ' ℓ'.2 hℓ' hpN _ _) fun x hx => ?_
    rw [smulOp_apply, smulOp_apply, smul_corr]
  · rw [ssHeckeFamilyC_of_eq data hKr hlegs ℓ' hℓ', ssFrobMatrixC_eq_mat data hKr,
      ssHeckeFamilyC_eq_mat_corr hpN data hKr hlegs ℓ hℓ]
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.pos.ne'⟩
    haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
    haveI : HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ) := hasPrincipalDivisors_roof (K := K) ℓ hℓ hpN
    refine commute_mat _ _ _ (stable_corr (p := p) ℓ ℓ.2 hℓ hpN _ _) stable_smulOp fun x hx => ?_
    rw [smulOp_apply, smulOp_apply, smul_corr]
  ·
    rw [ssHeckeFamilyC_eq_mat_corr hpN data hKr hlegs ℓ hℓ, ssHeckeFamilyC_eq_mat_corr hpN data hKr hlegs ℓ' hℓ']
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.pos.ne'⟩
    haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
    haveI : NeZero (ℓ' : ℕ) := ⟨ℓ'.2.pos.ne'⟩
    haveI : Fact (ℓ' : ℕ).Prime := ⟨ℓ'.2⟩
    haveI : HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ) := hasPrincipalDivisors_roof (K := K) ℓ hℓ hpN
    haveI : HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ') := hasPrincipalDivisors_roof (K := K) ℓ' hℓ' hpN
    refine commute_mat _ _ _ (stable_corr (p := p) ℓ ℓ.2 hℓ hpN _ _) (stable_corr (p := p) ℓ' ℓ'.2 hℓ' hpN _ _)
      fun x hx => ?_
    exact correspondence_heckeBetaC_heckeAlphaC_correspondence_heckeBetaC_heckeAlphaC_comm N ℓ ℓ' p ℓ.2 ℓ'.2
      hℓ hℓ' hpN (k := K) (hlegs ℓ).1 (hlegs ℓ).2 (hlegs ℓ').1 (hlegs ℓ').2 (Finsupp.single x 1)

end OneLevel

section TwoLevel

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] [DecidableEq K] [IsAlgClosed K]
variable {M s : ℕ} [NeZero M] [Fact s.Prime] (X : SSLevelDatum p K M s)
variable [Fintype ↥(ssPlaces p (M * s) K)] [Fintype ↥(ssPlaces p M K)] [DecidableEq ↥(ssPlaces p M K)]

theorem inertiaDegAlong_eq_one_of_isRational {F F' : Type*} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (hw : w.IsRational)
    (hv : (w.restrictAlong φ hφ).IsRational) : w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.inertiaDeg_eq_one_of_isRational w hw hv

abbrev pushA : Divisor K ↥(modularFunctionFieldC K (M * s)) →+ Divisor K ↥(modularFunctionFieldC K M) :=
  Divisor.pushforwardAlong (levelAlphaC K M s X.mem_M) X.fstIntegral

abbrev pushB : Divisor K ↥(modularFunctionFieldC K (M * s)) →+ Divisor K ↥(modularFunctionFieldC K M) :=
  Divisor.pushforwardAlong (levelBetaC K M s X.mem_s) X.sndIntegral

variable {X}

theorem pushA_single_of_mem (W : Place K ↥(modularFunctionFieldC K (M * s))) (hW : W ∈ ssPlaces p (M * s) K) :
    pushA X (Finsupp.single W 1) = Finsupp.single (X.fst ⟨W, hW⟩).1 1 := by
  rw [Divisor.pushforwardAlong_single, one_mul, inertiaDegAlong_eq_one_of_isRational _ _ W hW.1 (X.fst ⟨W, hW⟩).2.1]
  rfl

theorem pushB_single_of_mem (W : Place K ↥(modularFunctionFieldC K (M * s))) (hW : W ∈ ssPlaces p (M * s) K) :
    pushB X (Finsupp.single W 1) = Finsupp.single (X.snd ⟨W, hW⟩).1 1 := by
  rw [Divisor.pushforwardAlong_single, one_mul, inertiaDegAlong_eq_one_of_isRational _ _ W hW.1 (X.snd ⟨W, hW⟩).2.1]
  rfl

theorem stable_pushA : Stable (ssPlaces p (M * s) K) (ssPlaces p M K) (pushA X) := by
  classical
  intro W hW t ht
  rw [pushA_single_of_mem (X := X) W hW, Finsupp.single_apply] at ht
  split_ifs at ht with h
  · rw [← h]; exact (X.fst ⟨W, hW⟩).2
  · exact absurd rfl ht

theorem stable_pushB : Stable (ssPlaces p (M * s) K) (ssPlaces p M K) (pushB X) := by
  classical
  intro W hW t ht
  rw [pushB_single_of_mem (X := X) W hW, Finsupp.single_apply] at ht
  split_ifs at ht with h
  · rw [← h]; exact (X.snd ⟨W, hW⟩).2
  · exact absurd rfl ht

theorem degeneracyMatrix_fst : CerednikDrinfeld.degeneracyMatrix X.fst = mat _ _ (pushA X) := by
  classical
  ext v e
  rw [mat_apply, pushA_single_of_mem (X := X) e.1 e.2, Finsupp.single_apply, CerednikDrinfeld.degeneracyMatrix,
    Matrix.of_apply]
  by_cases h : X.fst e = v
  · rw [if_pos h, if_pos (by rw [← h])]
  · rw [if_neg h, if_neg (fun h' => h (Subtype.ext (by simpa using h')))]

theorem degeneracyMatrix_snd : CerednikDrinfeld.degeneracyMatrix X.snd = mat _ _ (pushB X) := by
  classical
  ext v e
  rw [mat_apply, pushB_single_of_mem (X := X) e.1 e.2, Finsupp.single_apply, CerednikDrinfeld.degeneracyMatrix,
    Matrix.of_apply]
  by_cases h : X.snd e = v
  · rw [if_pos h, if_pos (by rw [← h])]
  · rw [if_neg h, if_neg (fun h' => h (Subtype.ext (by simpa using h')))]

def levelPair : Fin 2 → (↥(modularFunctionFieldC K M) →ₐ[K] ↥(modularFunctionFieldC K (M * s))) :=
  ![levelAlphaC K M s X.mem_M, levelBetaC K M s X.mem_s]

theorem levelPair_zero : levelPair (X := X) 0 = levelAlphaC K M s X.mem_M := rfl
theorem levelPair_one : levelPair (X := X) 1 = levelBetaC K M s X.mem_s := rfl

theorem levelPair_integral : ∀ i, (levelPair (X := X) i).toRingHom.IsIntegral := by
  intro i
  fin_cases i
  · exact X.fstIntegral
  · exact X.sndIntegral

theorem not_dvd_mul_mul (hpM : ¬ p ∣ M) (hsp : s ≠ p) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) : ¬ p ∣ M * s * ℓ := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact hpM h
    · exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp h).symm
  · exact hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h).symm

theorem not_dvd_mul (hpM : ¬ p ∣ M) (hsp : s ≠ p) : ¬ p ∣ M * s := by
  have hp : p.Prime := Fact.out
  have hs : s.Prime := Fact.out
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · exact hpM h
  · exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp h).symm

theorem push_corr_comm (hpM : ¬ p ∣ M) (hsp : s ≠ p) (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hℓs : ℓ ≠ s)
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) ℓ)] [HasPrincipalDivisors K ↥(charLDegeneracyRoof K M ℓ)]
    (i : Fin 2) (D : Divisor K ↥(modularFunctionFieldC K (M * s))) :
    Divisor.pushforwardAlong (levelPair (X := X) i) (levelPair_integral i)
        (corr K (M * s) ℓ (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 D)
      = corr K M ℓ (X.legsIntegral M ℓ).1 (X.legsIntegral M ℓ).2
          (Divisor.pushforwardAlong (levelPair (X := X) i) (levelPair_integral i) D) :=
  degeneracyPair_pushforwardAlong_correspondence_heckeBetaC_heckeAlphaC_comm_of_ne_of_not_dvd M s ℓ Fact.out Fact.out
    hℓs (k := K) p (not_dvd_mul_mul hpM hsp Fact.out hℓp) (levelPair (X := X)) levelPair_integral
    (fun x => coe_levelAlphaC K M s X.mem_M x) (fun x => coe_levelBetaC K M s X.mem_s x)
    (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 (X.legsIntegral M ℓ).1 (X.legsIntegral M ℓ).2 i D

theorem degeneracyMatrix_mul_edgeHecke_of_ne (hpM : ¬ p ∣ M) (hsp : s ≠ p) (ℓ : Nat.Primes) (hℓp : (ℓ : ℕ) ≠ p)
    (hℓs : (ℓ : ℕ) ≠ s) :
    CerednikDrinfeld.degeneracyMatrix X.fst * X.edgeHecke ℓ = X.vertexHecke ℓ * CerednikDrinfeld.degeneracyMatrix X.fst ∧
    CerednikDrinfeld.degeneracyMatrix X.snd * X.edgeHecke ℓ = X.vertexHecke ℓ * CerednikDrinfeld.degeneracyMatrix X.snd := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.pos.ne'⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hpMs : ¬ p ∣ M * s := not_dvd_mul hpM hsp
  haveI iE : HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) ℓ) := hasPrincipalDivisors_roof (K := K) ℓ hℓp hpMs
  haveI iV : HasPrincipalDivisors K ↥(charLDegeneracyRoof K M ℓ) := hasPrincipalDivisors_roof (K := K) ℓ hℓp hpM
  have hE : X.edgeHecke ℓ = mat _ _ (corr K (M * s) ℓ (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2) :=
    ssHeckeFamilyC_eq_mat_corr hpMs X.frobData X.kronecker (X.legsIntegral (M * s)) ℓ hℓp
  have hV : X.vertexHecke ℓ = mat _ _ (corr K M ℓ (X.legsIntegral M ℓ).1 (X.legsIntegral M ℓ).2) :=
    ssHeckeFamilyC_eq_mat_corr hpM X.frobData X.kronecker (X.legsIntegral M) ℓ hℓp
  have hstE := stable_corr (p := p) (N := M * s) ℓ ℓ.2 hℓp hpMs (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2
  refine ⟨?_, ?_⟩
  · rw [hE, hV, degeneracyMatrix_fst]
    exact mat_intertwine _ _ _ _ (pushA X) (pushA X) hstE stable_pushA fun e he =>
      push_corr_comm (X := X) hpM hsp ℓ hℓp hℓs 0 (Finsupp.single e 1)
  · rw [hE, hV, degeneracyMatrix_snd]
    exact mat_intertwine _ _ _ _ (pushB X) (pushB X) hstE stable_pushB fun e he =>
      push_corr_comm (X := X) hpM hsp ℓ hℓp hℓs 1 (Finsupp.single e 1)

theorem intertwines_levelAlphaC :
    SemilinearAut.IntertwinesAlong (levelAlphaC K M s X.mem_M).toRingHom (arithFrobC p K M) (arithFrobC p K (M * s)) := by
  intro x
  refine Subtype.ext ?_
  show coeffMap _ ((levelAlphaC K M s X.mem_M x : ↥(modularFunctionFieldC K (M * s))) : LaurentSeries K)
    = ((levelAlphaC K M s X.mem_M (arithFrobC p K M • x) : ↥(modularFunctionFieldC K (M * s))) : LaurentSeries K)
  rw [coe_levelAlphaC, coe_levelAlphaC]
  rfl

theorem intertwines_levelBetaC :
    SemilinearAut.IntertwinesAlong (levelBetaC K M s X.mem_s).toRingHom (arithFrobC p K M) (arithFrobC p K (M * s)) := by
  intro x
  refine Subtype.ext ?_
  show coeffMap _ ((levelBetaC K M s X.mem_s x : ↥(modularFunctionFieldC K (M * s))) : LaurentSeries K)
    = ((levelBetaC K M s X.mem_s (arithFrobC p K M • x) : ↥(modularFunctionFieldC K (M * s))) : LaurentSeries K)
  rw [coe_levelBetaC, coe_levelBetaC, coeffSemilinearAut.coeffMap_qExpand]
  rfl

theorem degeneracyMatrix_mul_edgeHecke_of_eq (ℓ : Nat.Primes) (hℓp : (ℓ : ℕ) = p) :
    CerednikDrinfeld.degeneracyMatrix X.fst * X.edgeHecke ℓ = X.vertexHecke ℓ * CerednikDrinfeld.degeneracyMatrix X.fst ∧
    CerednikDrinfeld.degeneracyMatrix X.snd * X.edgeHecke ℓ = X.vertexHecke ℓ * CerednikDrinfeld.degeneracyMatrix X.snd := by
  have hE : X.edgeHecke ℓ = mat _ _ (smulOp (arithFrobC p K (M * s))) := by
    rw [← ssFrobMatrixC_eq_mat X.frobData X.kronecker]
    exact ssHeckeFamilyC_of_eq X.frobData X.kronecker (X.legsIntegral (M * s)) ℓ hℓp
  have hV : X.vertexHecke ℓ = mat _ _ (smulOp (arithFrobC p K M)) := by
    rw [← ssFrobMatrixC_eq_mat X.frobData X.kronecker]
    exact ssHeckeFamilyC_of_eq X.frobData X.kronecker (X.legsIntegral M) ℓ hℓp
  refine ⟨?_, ?_⟩
  · rw [hE, hV, degeneracyMatrix_fst]
    refine mat_intertwine _ _ _ _ (pushA X) (pushA X) stable_smulOp stable_pushA fun e he => ?_
    have he' : arithFrobC p K (M * s) • e ∈ ssPlaces p (M * s) K := arithFrobC_smul_mem_ssPlaces p (M * s) K e he
    rw [smulOp_apply, smulOp_apply, SemilinearAut.smul_single, pushA_single_of_mem (X := X) _ he',
      pushA_single_of_mem (X := X) _ he,
      SemilinearAut.smul_single]
    congr 1
    exact smul_restrictAlong_semilinear (levelAlphaC K M s X.mem_M) X.fstIntegral (arithFrobC p K M)
      (arithFrobC p K (M * s)) (intertwines_levelAlphaC (X := X)) e
  · rw [hE, hV, degeneracyMatrix_snd]
    refine mat_intertwine _ _ _ _ (pushB X) (pushB X) stable_smulOp stable_pushB fun e he => ?_
    have he' : arithFrobC p K (M * s) • e ∈ ssPlaces p (M * s) K := arithFrobC_smul_mem_ssPlaces p (M * s) K e he
    rw [smulOp_apply, smulOp_apply, SemilinearAut.smul_single, pushB_single_of_mem (X := X) _ he',
      pushB_single_of_mem (X := X) _ he,
      SemilinearAut.smul_single]
    congr 1
    exact smul_restrictAlong_semilinear (levelBetaC K M s X.mem_s) X.sndIntegral (arithFrobC p K M)
      (arithFrobC p K (M * s)) (intertwines_levelBetaC (X := X)) e

theorem degeneracyMatrix_mul_edgeHecke (hpM : ¬ p ∣ M) (hsp : s ≠ p) (ℓ : Nat.Primes) (hℓs : (ℓ : ℕ) ≠ s) :
    CerednikDrinfeld.degeneracyMatrix X.fst * X.edgeHecke ℓ = X.vertexHecke ℓ * CerednikDrinfeld.degeneracyMatrix X.fst ∧
    CerednikDrinfeld.degeneracyMatrix X.snd * X.edgeHecke ℓ = X.vertexHecke ℓ * CerednikDrinfeld.degeneracyMatrix X.snd := by
  by_cases hℓp : (ℓ : ℕ) = p
  · exact degeneracyMatrix_mul_edgeHecke_of_eq ℓ hℓp
  · exact degeneracyMatrix_mul_edgeHecke_of_ne hpM hsp ℓ hℓp hℓs

theorem jointDelta_zero : CerednikDrinfeld.jointDelta X.degeneracyData 0 = CerednikDrinfeld.pushforward X.fst := rfl

theorem jointDelta_one : CerednikDrinfeld.jointDelta X.degeneracyData 1 = CerednikDrinfeld.pushforward X.snd := rfl

theorem good_equivariant (hpM : ¬ p ∣ M) (hsp : s ≠ p) (ℓ : Nat.Primes) (hℓs : (ℓ : ℕ) ≠ s) (i : Fin 2)
    (x : ↥(ssPlaces p (M * s) K) → ℤ) :
    CerednikDrinfeld.jointDelta X.degeneracyData i ((X.edgeHecke ℓ).mulVecLin x) =
      (X.vertexHecke ℓ).mulVecLin (CerednikDrinfeld.jointDelta X.degeneracyData i x) := by
  obtain ⟨ha, hb⟩ := degeneracyMatrix_mul_edgeHecke (X := X) hpM hsp ℓ hℓs
  fin_cases i
  · show CerednikDrinfeld.pushforward X.fst _ = (X.vertexHecke ℓ).mulVecLin (CerednikDrinfeld.pushforward X.fst x)
    simp only [CerednikDrinfeld.pushforward, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ha]
  · show CerednikDrinfeld.pushforward X.snd _ = (X.vertexHecke ℓ).mulVecLin (CerednikDrinfeld.pushforward X.snd x)
    simp only [CerednikDrinfeld.pushforward, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hb]

theorem eq_top_of_inv_mem_of_generators (Z : IntermediateField K (LaurentSeries K)) (A : Subalgebra K Z)
    (hinv : ∀ a ∈ A, a⁻¹ ∈ A) (S₀ : Set (LaurentSeries K)) (hZ : Z ≤ IntermediateField.adjoin K S₀)
    (hS₀ : ∀ t ∈ S₀, ∃ a ∈ A, (a : LaurentSeries K) = t) : A = ⊤ := by
  let E : IntermediateField K Z := A.toIntermediateField hinv
  have hmap : IntermediateField.adjoin K S₀ ≤ E.map Z.val := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro t ht
    obtain ⟨a, ha, rfl⟩ := hS₀ t ht
    exact ⟨a, ha, rfl⟩
  have hE : E = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨e, he, hez⟩ := hmap (hZ z.2)
    exact (Subtype.ext hez : e = z) ▸ he
  have := congrArg IntermediateField.toSubalgebra hE
  simpa [E] using this

theorem atkinLehnerAut_atkinLehnerAut (x : ↥(modularFunctionFieldC K (M * s))) :
    X.atkinLehnerAut (X.atkinLehnerAut x) = x := by
  obtain ⟨h1, h2, h3, h4⟩ := X.isAtkinLehner
  let A : Subalgebra K ↥(modularFunctionFieldC K (M * s)) :=
    AlgHom.equalizer
      ((X.atkinLehnerAut : ↥(modularFunctionFieldC K (M * s)) →ₐ[K] ↥(modularFunctionFieldC K (M * s))).comp
        X.atkinLehnerAut)
      (AlgHom.id K _)
  have hmem : ∀ y, y ∈ A ↔ X.atkinLehnerAut (X.atkinLehnerAut y) = y := fun y => Iff.rfl
  have hinv : ∀ a ∈ A, a⁻¹ ∈ A := fun a ha => by
    rw [hmem] at ha ⊢
    rw [map_inv₀, map_inv₀, ha]
  have hA : A = ⊤ := by
    refine eq_top_of_inv_mem_of_generators (modularFunctionFieldC K (M * s)) A hinv
      {jqModC K, jqNModC K (M * s)} le_rfl ?_
    intro t ht
    rcases ht with rfl | ht
    · refine ⟨jGeomGen K (M * s), ?_, coe_jGeomGen K (M * s)⟩
      rw [hmem, h1, h2]
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      refine ⟨jNGeomGen K (M * s), ?_, coe_jNGeomGen K (M * s)⟩
      rw [hmem, h3, h4]
  have hx : x ∈ A := hA ▸ Algebra.mem_top
  exact (hmem x).mp hx

theorem atkinLehnerPerm_atkinLehnerPerm (e : ↥(ssPlaces p (M * s) K)) : X.atkinLehnerPerm (X.atkinLehnerPerm e) = e := by
  refine Subtype.ext ?_
  show autOnPlaces K M s X.atkinLehnerAut (autOnPlaces K M s X.atkinLehnerAut e.1) = e.1
  have hsymm : ∀ y, X.atkinLehnerAut.toRingEquiv.symm y = X.atkinLehnerAut y := fun y => by
    conv_lhs => rw [← atkinLehnerAut_atkinLehnerAut (X := X) y]
    exact X.atkinLehnerAut.toRingEquiv.symm_apply_apply _
  ext1
  refine SetLike.ext fun y => ?_
  simp only [autOnPlaces, Place.congrEquiv_apply, Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
  show X.atkinLehnerAut.toRingEquiv.symm (X.atkinLehnerAut.toRingEquiv.symm y) ∈ _ ↔ _
  rw [hsymm, hsymm, atkinLehnerAut_atkinLehnerAut]

theorem atkinLehnerPerm_involutive : Function.Involutive (X.atkinLehnerPerm) := atkinLehnerPerm_atkinLehnerPerm

theorem snd_eq_fst_perm (e : ↥(ssPlaces p (M * s) K)) : X.snd e = X.fst (X.atkinLehnerPerm e) :=
  SSLevelDatum.degeneracyData_b_eq_a_atkinLehnerPerm p K M s X e

theorem fst_eq_snd_perm (e : ↥(ssPlaces p (M * s) K)) : X.fst e = X.snd (X.atkinLehnerPerm e) := by
  rw [snd_eq_fst_perm, atkinLehnerPerm_atkinLehnerPerm]

theorem pushA_single (e : ↥(ssPlaces p (M * s) K)) : pushA X (Finsupp.single e.1 1) = Finsupp.single (X.fst e).1 1 :=
  pushA_single_of_mem (X := X) e.1 e.2

theorem corr_level_entry [DecidableEq ↥(ssPlaces p (M * s) K)] (hpM : ¬ p ∣ M) (hsp : s ≠ p) (hsM : ¬ s ∣ M)
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) s)] [HasPrincipalDivisors K ↥(modularFunctionFieldC K (M * s))]
    (e e' : ↥(ssPlaces p (M * s) K)) :
    corr K (M * s) s (X.legsIntegral (M * s) s).1 (X.legsIntegral (M * s) s).2 (Finsupp.single e.1 1) e'.1
      + (if X.atkinLehnerPerm e = e' then 1 else 0)
      = (Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e'.1 : ℤ) * (if X.fst e = X.snd e' then 1 else 0) := by
  classical
  have h := correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong M s
    Fact.out hsM (k := K) p (not_dvd_mul hpM hsp) X.mem_M X.mem_s X.atkinLehnerAut X.isAtkinLehner
    (X.legsIntegral (M * s) s).1 (X.legsIntegral (M * s) s).2 X.fstIntegral X.sndIntegral e.1
  have hpush : Divisor.pushforwardAlong (levelAlphaC K M s X.mem_M) X.fstIntegral (Finsupp.single e.1 1)
      = Finsupp.single (X.fst e).1 1 := pushA_single (X := X) e
  rw [hpush] at h
  have h' := congrArg (fun D => D e'.1) h
  simp only [Finsupp.add_apply, Divisor.pullbackAlong_apply] at h'
  have hS : Finsupp.single (autOnPlaces K M s X.atkinLehnerAut e.1) (1 : ℤ) e'.1
      = if X.atkinLehnerPerm e = e' then 1 else 0 := by
    rw [Finsupp.single_apply]
    by_cases hπ : X.atkinLehnerPerm e = e'
    · rw [if_pos hπ, if_pos]
      exact congrArg Subtype.val hπ
    · rw [if_neg hπ, if_neg]
      exact fun h'' => hπ (Subtype.ext h'')
  have hA : Finsupp.single (X.fst e).1 (1 : ℤ) (Place.restrictAlong (levelBetaC K M s X.mem_s) X.sndIntegral e'.1)
      = if X.fst e = X.snd e' then 1 else 0 := by
    rw [Finsupp.single_apply]
    by_cases hab : X.fst e = X.snd e'
    · rw [if_pos hab, if_pos]
      exact congrArg Subtype.val hab
    · rw [if_neg hab, if_neg]
      exact fun h'' => hab (Subtype.ext h'')
  rw [hS, hA] at h'
  exact h'

theorem level_mulVec_of_ker [DecidableEq ↥(ssPlaces p (M * s) K)] (hpM : ¬ p ∣ M) (hsp : s ≠ p) (hsM : ¬ s ∣ M)
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) s)] [HasPrincipalDivisors K ↥(modularFunctionFieldC K (M * s))]
    (x : ↥(ssPlaces p (M * s) K) → ℤ) (ha : (CerednikDrinfeld.degeneracyMatrix X.fst).mulVec x = 0)
    (e' : ↥(ssPlaces p (M * s) K)) :
    (mat _ _ (corr K (M * s) s (X.legsIntegral (M * s) s).1 (X.legsIntegral (M * s) s).2)).mulVec x e'
      = - x (X.atkinLehnerPerm e') := by
  have hrow : ∀ e, mat _ _ (corr K (M * s) s (X.legsIntegral (M * s) s).1 (X.legsIntegral (M * s) s).2) e' e
      = (Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e'.1 : ℤ) * (if X.fst e = X.snd e' then 1 else 0)
        - (if X.atkinLehnerPerm e = e' then 1 else 0) := fun e => by
    rw [mat_apply, ← corr_level_entry hpM hsp hsM e e']
    ring
  have hA : ∑ e, (if X.fst e = X.snd e' then (1 : ℤ) else 0) * x e = 0 := by
    have h0 := congrArg (fun v => v (X.snd e')) ha
    simp only [Matrix.mulVec, dotProduct, CerednikDrinfeld.degeneracyMatrix, Matrix.of_apply, Pi.zero_apply] at h0
    exact h0
  have hS : ∑ e, (if X.atkinLehnerPerm e = e' then (1 : ℤ) else 0) * x e = x (X.atkinLehnerPerm e') := by
    rw [Finset.sum_eq_single (X.atkinLehnerPerm e')]
    · rw [if_pos (atkinLehnerPerm_atkinLehnerPerm e'), one_mul]
    · intro e _ hne
      rw [if_neg, zero_mul]
      intro he
      apply hne
      rw [← he, atkinLehnerPerm_atkinLehnerPerm]
    · exact fun h => absurd (Finset.mem_univ _) h
  calc (mat _ _ (corr K (M * s) s (X.legsIntegral (M * s) s).1 (X.legsIntegral (M * s) s).2)).mulVec x e'
      = ∑ e, ((Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e'.1 : ℤ) * (if X.fst e = X.snd e' then 1 else 0)
          - (if X.atkinLehnerPerm e = e' then 1 else 0)) * x e := by
        simp only [Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun e _ => by rw [hrow]
    _ = (Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e'.1 : ℤ)
          * ∑ e, (if X.fst e = X.snd e' then (1 : ℤ) else 0) * x e
        - ∑ e, (if X.atkinLehnerPerm e = e' then (1 : ℤ) else 0) * x e := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ = - x (X.atkinLehnerPerm e') := by rw [hA, hS, mul_zero, zero_sub]

theorem sum_perm_reindex (f : ↥(ssPlaces p (M * s) K) → ℤ) : ∑ e, f (X.atkinLehnerPerm e) = ∑ e, f e :=
  Equiv.sum_comp ((atkinLehnerPerm_involutive (X := X)).toPerm _) f

theorem kernel_stable_level [DecidableEq ↥(ssPlaces p (M * s) K)] (hpM : ¬ p ∣ M) (hsp : s ≠ p) (hsM : ¬ s ∣ M)
    (ℓ : Nat.Primes) (hℓs : (ℓ : ℕ) = s)
    (x : ↥(ssPlaces p (M * s) K) → ℤ) (hx : ∀ i, CerednikDrinfeld.jointDelta X.degeneracyData i x = 0) (i : Fin 2) :
    CerednikDrinfeld.jointDelta X.degeneracyData i ((X.edgeHecke ℓ).mulVecLin x) = 0 := by
  have hℓ : ℓ = ⟨s, Fact.out⟩ := Subtype.ext hℓs
  subst hℓ
  have hpMs : ¬ p ∣ M * s := not_dvd_mul hpM hsp
  haveI iE : HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) s) := hasPrincipalDivisors_roof (K := K) s hsp hpMs
  haveI iL : HasPrincipalDivisors K ↥(modularFunctionFieldC K (M * s)) :=
    hasPrincipalDivisors_modularFunctionFieldC_of_perfectField K (M * s)
  have hE : X.edgeHecke ⟨s, Fact.out⟩
      = mat _ _ (corr K (M * s) s (X.legsIntegral (M * s) s).1 (X.legsIntegral (M * s) s).2) :=
    ssHeckeFamilyC_eq_mat_corr hpMs X.frobData X.kronecker (X.legsIntegral (M * s)) ⟨s, Fact.out⟩ hsp
  have ha : (CerednikDrinfeld.degeneracyMatrix X.fst).mulVec x = 0 := by
    have h0 := hx 0
    rw [jointDelta_zero] at h0
    exact h0
  have hb : (CerednikDrinfeld.degeneracyMatrix X.snd).mulVec x = 0 := by
    have h1 := hx 1
    rw [jointDelta_one] at h1
    exact h1
  have hU : (X.edgeHecke ⟨s, Fact.out⟩).mulVec x = fun e' => - x (X.atkinLehnerPerm e') := by
    rw [hE]
    funext e'
    exact level_mulVec_of_ker hpM hsp hsM x ha e'

  have hav : ∀ v, ∑ e, (if X.fst e = v then (1 : ℤ) else 0) * x e = 0 := fun v => by
    have h0 := congrArg (fun w => w v) ha
    simp only [Matrix.mulVec, dotProduct, CerednikDrinfeld.degeneracyMatrix, Matrix.of_apply, Pi.zero_apply] at h0
    exact h0
  have hbv : ∀ v, ∑ e, (if X.snd e = v then (1 : ℤ) else 0) * x e = 0 := fun v => by
    have h0 := congrArg (fun w => w v) hb
    simp only [Matrix.mulVec, dotProduct, CerednikDrinfeld.degeneracyMatrix, Matrix.of_apply, Pi.zero_apply] at h0
    exact h0
  have keyA : (CerednikDrinfeld.degeneracyMatrix X.fst).mulVec (fun e' => - x (X.atkinLehnerPerm e')) = 0 := by
    funext v
    simp only [Matrix.mulVec, dotProduct, CerednikDrinfeld.degeneracyMatrix, Matrix.of_apply, Pi.zero_apply]
    calc ∑ e', (if X.fst e' = v then (1 : ℤ) else 0) * (- x (X.atkinLehnerPerm e'))
        = ∑ e, (if X.fst (X.atkinLehnerPerm e) = v then (1 : ℤ) else 0) * (- x (X.atkinLehnerPerm (X.atkinLehnerPerm e))) :=
          (sum_perm_reindex (X := X) (fun e' => (if X.fst e' = v then (1 : ℤ) else 0) * (- x (X.atkinLehnerPerm e')))).symm
      _ = - ∑ e, (if X.snd e = v then (1 : ℤ) else 0) * x e := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [atkinLehnerPerm_atkinLehnerPerm, ← snd_eq_fst_perm, mul_neg]
      _ = 0 := by rw [hbv v, neg_zero]
  have keyB : (CerednikDrinfeld.degeneracyMatrix X.snd).mulVec (fun e' => - x (X.atkinLehnerPerm e')) = 0 := by
    funext v
    simp only [Matrix.mulVec, dotProduct, CerednikDrinfeld.degeneracyMatrix, Matrix.of_apply, Pi.zero_apply]
    calc ∑ e', (if X.snd e' = v then (1 : ℤ) else 0) * (- x (X.atkinLehnerPerm e'))
        = ∑ e, (if X.snd (X.atkinLehnerPerm e) = v then (1 : ℤ) else 0) * (- x (X.atkinLehnerPerm (X.atkinLehnerPerm e))) :=
          (sum_perm_reindex (X := X) (fun e' => (if X.snd e' = v then (1 : ℤ) else 0) * (- x (X.atkinLehnerPerm e')))).symm
      _ = - ∑ e, (if X.fst e = v then (1 : ℤ) else 0) * x e := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [atkinLehnerPerm_atkinLehnerPerm, ← fst_eq_snd_perm, mul_neg]
      _ = 0 := by rw [hav v, neg_zero]
  fin_cases i
  · show CerednikDrinfeld.pushforward X.fst ((X.edgeHecke ⟨s, Fact.out⟩).mulVecLin x) = 0
    rw [Matrix.mulVecLin_apply, hU, CerednikDrinfeld.pushforward, Matrix.mulVecLin_apply, keyA]
  · show CerednikDrinfeld.pushforward X.snd ((X.edgeHecke ⟨s, Fact.out⟩).mulVecLin x) = 0
    rw [Matrix.mulVecLin_apply, hU, CerednikDrinfeld.pushforward, Matrix.mulVecLin_apply, keyB]

theorem heckeLaws (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M) : X.HeckeLaws := by
  classical
  have hpMs : ¬ p ∣ M * s := not_dvd_mul hpM hsp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ℓ ℓ'
    exact commute_ssHeckeFamilyC hpMs X.frobData X.kronecker (X.legsIntegral (M * s)) ℓ ℓ'
  · intro ℓ ℓ'
    exact commute_ssHeckeFamilyC hpM X.frobData X.kronecker (X.legsIntegral M) ℓ ℓ'
  · intro ℓ hℓ i x
    have hℓs : (ℓ : ℕ) ≠ s := fun h => hℓ (Finset.mem_singleton.mpr (Subtype.ext h))
    exact good_equivariant hpM hsp ℓ hℓs i x
  · intro ℓ x hx i
    by_cases hℓs : (ℓ : ℕ) = s
    · exact kernel_stable_level hpM hsp hsM ℓ hℓs x hx i
    · rw [good_equivariant hpM hsp ℓ hℓs i x, hx i, map_zero]

end TwoLevel

end LawsCore

open LawsCore in

theorem solution
    (M s q' : ℕ) [NeZero M] [Fact q'.Prime] [Fact s.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s) :
    X.HeckeLaws := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  exact heckeLaws (X := X) hsq' hq'M hsM

end

end S_ModularCurve_SSLevelDatum_heckeLaws_of_prime_ne_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_SSLevelDatum_heckeLaws_of_prime_ne_of_not_dvd (solution)
