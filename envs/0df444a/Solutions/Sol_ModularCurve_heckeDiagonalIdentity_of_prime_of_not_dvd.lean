-- Prove2me | solution 1 for ModularCurve.heckeDiagonalIdentity_of_prime_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/64ebc003-90ae-5d43-abb3-45ddf615aee6

import Mathlib
import Definitions.Def_ModularCurve_HeckeNamedInputs
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_heckeRoof_adjoin_range_union_eq_top
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_finrankAlong_towerInclBar_of_eq
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_finiteAlong_comp
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
import Theorems.Thm_ModularCurve_towerSubstBar_finiteAlong
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_Place_exists_restrict_eq
import Theorems.Thm_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp
import Theorems.Thm_AlgebraicCurve_Place_inertiaDegAlong_comp
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber_defect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeDiagonalIdentity_of_prime_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "HeckeDiagonalIdentity heckeAlphaBar heckeBetaBar coe_heckeBetaBar heckeDivBar towerInclBar towerSubstBar coe_towerSubstBar heckeSquareBar_commutes dvd_of_eq_roof modularPolynomialFamily functionFieldGeneration heckeRoof_adjoin_range_union_eq_top finrankAlong_heckeBetaBar finrankAlong_towerInclBar_of_eq finiteAlong_heckeAlphaBar_of_prime towerSubstBar_finiteAlong towerSubstBar_isIntegral towerInclBar_isIntegral"
p2m_open "ModularCurve"

namespace WK2AlphaAux

open scoped Classical in

private theorem bifiber_defect {K F F₁ F₂ E : Type*} (M : Type*) [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
    [Field M] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra K M] [Algebra F F₁] [Algebra F F₂]
    [Algebra F E] [Algebra F M] [Algebra F₁ E] [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M] [Algebra E M]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F M] [IsScalarTower K F₁ E]
    [IsScalarTower K F₂ E] [IsScalarTower K F₁ M] [IsScalarTower K F₂ M] [IsScalarTower K E M] [IsScalarTower F F₁ M]
    [IsScalarTower F F₂ M] [IsScalarTower F E M] [IsScalarTower F₁ E M] [IsScalarTower F₂ E M] [FiniteDimensional F F₁]
    [FiniteDimensional F F₂] [FiniteDimensional F E] [FiniteDimensional F₁ E] [FiniteDimensional F₂ E]
    [FiniteDimensional F M] [IsGalois F M]
    [Algebra F₂ F₁] [IsScalarTower F F₂ F₁] [IsScalarTower K F₂ F₁] [Algebra.IsIntegral F₂ F₁]
    (hθ : Function.Surjective (algebraMap F₂ F₁))
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD2 : Module.finrank F E + Module.finrank F F₁ = Module.finrank F F₁ * Module.finrank F F₂)
    (hn : Module.finrank F F₂ ≠ 2)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂) (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F
        + (if w₁.restrict F₂ = w₂ then w₁.ramificationIndex F * w₁.inertiaDeg F else 0) =
      (w₁.ramificationIndex F * w₁.inertiaDeg F) * (w₂.ramificationIndex F * w₂.inertiaDeg F) :=
  AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_defect M hθ hgen hLD2 hn v w₁ w₂ hw₁ hw₂ T hT

section TowerLaws

variable {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]

private theorem isIntegral_toAlgHom' {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] :
    (IsScalarTower.toAlgHom K F F').toRingHom.IsIntegral :=
  fun x => Algebra.IsIntegral.isIntegral (R := F) x

private theorem inertiaDegAlong_congr' {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    {φ φ' : F →ₐ[K] F'} (h : φ = φ') (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = w.inertiaDegAlong φ' hφ' := by
  subst h; rfl

private theorem toAlgHom_comp_toAlgHom' :
    (IsScalarTower.toAlgHom K E M).comp (IsScalarTower.toAlgHom K F E) = IsScalarTower.toAlgHom K F M :=
  AlgHom.ext fun x => (IsScalarTower.algebraMap_apply F E M x).symm

private theorem ramificationIndex_tower [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] (W : Place K M) :
    W.ramificationIndex F = W.ramificationIndex E * (W.restrict E).ramificationIndex F := by
  have h := Place.ramificationIndexAlong_comp (IsScalarTower.toAlgHom K F E) (IsScalarTower.toAlgHom K E M)
    isIntegral_toAlgHom' isIntegral_toAlgHom'
    (by rw [toAlgHom_comp_toAlgHom']
        haveI : Algebra.IsIntegral F M := Algebra.IsIntegral.trans E
        exact isIntegral_toAlgHom') W
  rw [toAlgHom_comp_toAlgHom'] at h
  exact h

private theorem inertiaDeg_tower [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] [Algebra.IsIntegral F M] (W : Place K M) :
    W.inertiaDeg F = W.inertiaDeg E * (W.restrict E).inertiaDeg F := by
  have h := Place.inertiaDegAlong_comp (IsScalarTower.toAlgHom K F E) (IsScalarTower.toAlgHom K E M)
    isIntegral_toAlgHom' isIntegral_toAlgHom' (by rw [toAlgHom_comp_toAlgHom']; exact isIntegral_toAlgHom') W
  rw [inertiaDegAlong_congr' toAlgHom_comp_toAlgHom' _ isIntegral_toAlgHom'] at h
  exact h

private theorem restrict_restrict [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] [Algebra.IsIntegral F M] (W : Place K M) :
    (W.restrict E).restrict F = W.restrict F :=
  Place.ext (by
    simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])

end TowerLaws

section Envelope

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

private abbrev Env : Type _ := ↥(IntermediateField.normalClosure F E (AlgebraicClosure E))

private theorem isGalois_env [FiniteDimensional F E] [Algebra.IsSeparable F E] : IsGalois F (Env F E) := by
  haveI : Normal F (AlgebraicClosure E) := IsAlgClosure.normal F _
  haveI : ∀ f : E →ₐ[F] AlgebraicClosure E, Algebra.IsSeparable F f.fieldRange := fun f =>
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
  haveI : Algebra.IsSeparable F (Env F E) :=
    IntermediateField.isSeparable_iSup (F := F) (E := AlgebraicClosure E)
      (t := fun f : E →ₐ[F] AlgebraicClosure E => f.fieldRange)
  exact ⟨⟩

variable (R : Type*) [Field R] [Algebra R E]

@[reducible] private def algebraEnv : Algebra R (Env F E) :=
  ((algebraMap E (Env F E)).comp (algebraMap R E)).toAlgebra

private theorem isScalarTower_env_mid : letI := algebraEnv F E R; IsScalarTower R E (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem isScalarTower_env_base [Algebra F R] [IsScalarTower F R E] :
    letI := algebraEnv F E R; IsScalarTower F R (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    show algebraMap F (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap R E (algebraMap F R x))
    rw [← IsScalarTower.algebraMap_apply F R E x,
      ← IsScalarTower.algebraMap_apply F E (AlgebraicClosure E) x])

variable (K : Type*) [Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E]

private theorem isScalarTower_env_bot [Algebra K R] [IsScalarTower K R E] :
    letI := algebraEnv F E R; IsScalarTower K R (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    show algebraMap K (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap R E (algebraMap K R x))
    rw [← IsScalarTower.algebraMap_apply K R E x,
      ← IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) x])

omit [Algebra R E] in
private theorem isScalarTower_env_const : IsScalarTower K E (Env F E) :=
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    show algebraMap K (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap K E x)
    rw [← IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) x])

end Envelope

open scoped Classical in

private theorem localDefect_of_isGalois {K F F₁ F₂ E : Type*} (M : Type*)
    [Field K] [Field F] [Field F₁] [Field F₂] [Field E] [Field M]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra K M]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F M]
    [Algebra F₁ E] [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M] [Algebra E M]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F M]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower K F₁ M] [IsScalarTower K F₂ M]
    [IsScalarTower K E M]
    [IsScalarTower F F₁ E] [IsScalarTower F F₂ E] [IsScalarTower F F₁ M] [IsScalarTower F F₂ M]
    [IsScalarTower F E M] [IsScalarTower F₁ E M] [IsScalarTower F₂ E M]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E]
    [FiniteDimensional F M] [IsGalois F M]
    [Algebra F₂ F₁] [IsScalarTower F F₂ F₁] [IsScalarTower K F₂ F₁] [Algebra.IsIntegral F₂ F₁]
    (hθ : Function.Surjective (algebraMap F₂ F₁))
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD2 : Module.finrank F E + Module.finrank F F₁ = Module.finrank F F₁ * Module.finrank F F₂)
    (hn : Module.finrank F F₂ ≠ 2)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ + (if w₁.restrict F₂ = w₂ then w₁.inertiaDeg F₂ else 0) =
      w₁.inertiaDeg F * w₂.ramificationIndex F := by
  have hB := bifiber_defect M hθ hgen hLD2 hn v w₁ w₂ hw₁ hw₂ T hT

  have hsum : ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F =
      (∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂) *
        (w₁.ramificationIndex F * w₂.inertiaDeg F) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun W hW => ?_
    obtain ⟨h₁, h₂⟩ := (hT W).mp hW
    rw [ramificationIndex_tower (F := F) (E := F₁) W, h₁, inertiaDeg_tower (F := F) (E := F₂) W, h₂]
    ring

  have he₁ : 0 < w₁.ramificationIndex F := Place.ramificationIndex_pos (F := F) w₁
  have hf₂ : 0 < w₂.inertiaDeg F := by
    haveI : FiniteDimensional F₂ M := Module.Finite.of_restrictScalars_finite F F₂ M
    haveI : IsGalois F₂ M := IsGalois.tower_top_of_isGalois F F₂ M
    obtain ⟨P, hP⟩ := Place.exists_restrict_eq (M := M) w₂
    have hPF : P.restrict F = v := by rw [← restrict_restrict (E := F₂) P, hP, hw₂]
    have hTC := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg v P hPF
    have hf := inertiaDeg_tower (F := F) (E := F₂) P
    rw [hP] at hf
    have hne : Module.finrank F M ≠ 0 := Module.finrank_pos.ne'
    rw [← hTC, hf] at hne
    exact Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos he₁ hf₂)
  by_cases hm : w₁.restrict F₂ = w₂
  ·
    rw [if_pos hm] at hB ⊢
    haveI : Algebra.IsIntegral F F₂ := Algebra.IsIntegral.of_finite F F₂
    haveI : Algebra.IsIntegral F F₁ := Algebra.IsIntegral.of_finite F F₁
    have hf₁ : w₁.inertiaDeg F = w₁.inertiaDeg F₂ * w₂.inertiaDeg F := by
      rw [inertiaDeg_tower (F := F) (E := F₂) w₁, hm]
    rw [add_mul, ← hsum, hf₁]
    rw [hf₁] at hB
    have e1 : w₁.inertiaDeg F₂ * (w₁.ramificationIndex F * w₂.inertiaDeg F) =
        w₁.ramificationIndex F * (w₁.inertiaDeg F₂ * w₂.inertiaDeg F) := by ring
    have e2 : w₁.inertiaDeg F₂ * w₂.inertiaDeg F * w₂.ramificationIndex F *
          (w₁.ramificationIndex F * w₂.inertiaDeg F) =
        w₁.ramificationIndex F * (w₁.inertiaDeg F₂ * w₂.inertiaDeg F) *
          (w₂.ramificationIndex F * w₂.inertiaDeg F) := by ring
    rw [e1, e2]
    exact hB
  · rw [if_neg hm] at hB ⊢
    rw [add_zero] at hB ⊢
    rw [← hsum, hB]
    ring

open scoped Classical in

private theorem localDefect {K F F₁ F₂ E : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E] [Algebra F₂ F₁]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F₁ E]
    [IsScalarTower K F₂ E] [IsScalarTower K F₂ F₁]
    [IsScalarTower F F₁ E] [IsScalarTower F F₂ E] [IsScalarTower F F₂ F₁]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E] [FiniteDimensional F₁ E]
    [FiniteDimensional F₂ E] [Algebra.IsSeparable F E] [Algebra.IsIntegral F₂ F₁]
    (hθ : Function.Surjective (algebraMap F₂ F₁))
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD2 : Module.finrank F E + Module.finrank F F₁ = Module.finrank F F₁ * Module.finrank F F₂)
    (hn : Module.finrank F F₂ ≠ 2)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂) (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ + (if w₁.restrict F₂ = w₂ then w₁.inertiaDeg F₂ else 0) =
      w₁.inertiaDeg F * w₂.ramificationIndex F := by
  letI : Algebra F₁ (Env F E) := algebraEnv F E F₁
  letI : Algebra F₂ (Env F E) := algebraEnv F E F₂
  haveI : IsScalarTower F₁ E (Env F E) := isScalarTower_env_mid F E F₁
  haveI : IsScalarTower F₂ E (Env F E) := isScalarTower_env_mid F E F₂
  haveI : IsScalarTower F F₁ (Env F E) := isScalarTower_env_base F E F₁
  haveI : IsScalarTower F F₂ (Env F E) := isScalarTower_env_base F E F₂
  haveI : IsScalarTower K F₁ (Env F E) := isScalarTower_env_bot F E F₁ K
  haveI : IsScalarTower K F₂ (Env F E) := isScalarTower_env_bot F E F₂ K
  haveI : IsScalarTower K E (Env F E) := isScalarTower_env_const F E K
  haveI : IsGalois F (Env F E) := isGalois_env F E
  exact localDefect_of_isGalois (Env F E) hθ hgen hLD2 hn v w₁ w₂ hw₁ hw₂ T hT

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem pushforwardAlong_congr' {φ ψ : F →ₐ[K] F'} (h : φ = ψ) (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (D : Divisor K F') :
    Divisor.pushforwardAlong φ hφ D = Divisor.pushforwardAlong ψ hψ D := by
  subst h; rfl

private theorem pullbackAlong_congr' [HasPrincipalDivisors K F'] {φ ψ : F →ₐ[K] F'} (h : φ = ψ)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong ψ hψ D := by
  subst h; rfl

end Congr

private theorem pullbackAlong_pushforwardAlong_eq_add_of_defect
    {K F A B E : Type*} [Field K] [Field F] [Field A] [Field B] [Field E]
    [Algebra K F] [Algebra K A] [Algebra K B] [Algebra K E]
    [HasPrincipalDivisors K B] [HasPrincipalDivisors K E]
    (a : F →ₐ[K] A) (b : F →ₐ[K] B) (a' : A →ₐ[K] E) (b' : B →ₐ[K] E)
    (ha : a.toRingHom.IsIntegral) (hb : b.toRingHom.IsIntegral)
    (ha' : a'.toRingHom.IsIntegral) (hb' : b'.toRingHom.IsIntegral)
    (hsq : b'.comp b = a'.comp a)
    (hfin : FiniteAlong K (a'.comp a)) (hsep : SeparableAlong K (a'.comp a))
    (hgen : Algebra.adjoin K (Set.range a' ∪ Set.range b') = ⊤)
    (θ : B →ₐ[K] A) (hθ : θ.toRingHom.IsIntegral) (hθs : Function.Surjective θ) (hθb : θ.comp b = a)
    (hLD2 : finrankAlong K (a'.comp a) + finrankAlong K a = finrankAlong K a * finrankAlong K b)
    (hn : finrankAlong K b ≠ 2)
    (D : Divisor K A) :
    Divisor.pullbackAlong b hb (Divisor.pushforwardAlong a ha D) =
      Divisor.pushforwardAlong b' hb' (Divisor.pullbackAlong a' ha' D) + Divisor.pushforwardAlong θ hθ D := by
  classical

  letI : Algebra F A := algebraAlong a
  letI : Algebra F B := algebraAlong b
  letI : Algebra A E := algebraAlong a'
  letI : Algebra B E := algebraAlong b'
  letI : Algebra F E := algebraAlong (a'.comp a)
  letI : Algebra B A := algebraAlong θ
  haveI : IsScalarTower K F A := isScalarTower_along a
  haveI : IsScalarTower K F B := isScalarTower_along b
  haveI : IsScalarTower K A E := isScalarTower_along a'
  haveI : IsScalarTower K B E := isScalarTower_along b'
  haveI : IsScalarTower K F E := isScalarTower_along (a'.comp a)
  haveI : IsScalarTower K B A := isScalarTower_along θ
  haveI : IsScalarTower F A E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F B E :=
    IsScalarTower.of_algebraMap_eq fun x => (AlgHom.congr_fun hsq x).symm
  haveI : IsScalarTower F B A :=
    IsScalarTower.of_algebraMap_eq fun x => (AlgHom.congr_fun hθb x).symm
  haveI : Algebra.IsIntegral F A := isIntegral_along a ha
  haveI : Algebra.IsIntegral F B := isIntegral_along b hb
  haveI : Algebra.IsIntegral A E := isIntegral_along a' ha'
  haveI : Algebra.IsIntegral B E := isIntegral_along b' hb'
  haveI : Algebra.IsIntegral B A := isIntegral_along θ hθ

  haveI : Module.Finite F E := hfin
  haveI : Algebra.IsIntegral F E := Algebra.IsIntegral.of_finite F E
  haveI : Algebra.IsSeparable F E := hsep
  haveI : FiniteDimensional A E := Module.Finite.of_restrictScalars_finite F A E
  haveI : FiniteDimensional B E := Module.Finite.of_restrictScalars_finite F B E
  haveI : FiniteDimensional F A := Module.Finite.left F A E
  haveI : FiniteDimensional F B := Module.Finite.left F B E

  have hgenF : Algebra.adjoin F (Set.range (algebraMap A E) ∪ Set.range (algebraMap B E)) = ⊤ := by
    have hs : Set.range (algebraMap A E) ∪ Set.range (algebraMap B E) =
        Set.range a' ∪ Set.range b' := rfl
    rw [hs, eq_top_iff]
    intro z _
    have hz : z ∈ Algebra.adjoin K (Set.range a' ∪ Set.range b') := hgen ▸ Algebra.mem_top
    have hle : Algebra.adjoin K (Set.range a' ∪ Set.range b') ≤
        (Algebra.adjoin F (Set.range a' ∪ Set.range b')).restrictScalars K :=
      Algebra.adjoin_le fun x hx =>
        (Subalgebra.mem_restrictScalars K).mpr (Algebra.subset_adjoin hx)
    exact (Subalgebra.mem_restrictScalars K).mp (hle hz)
  have hθs' : Function.Surjective (algebraMap B A) := hθs
  have hLD2' : Module.finrank F E + Module.finrank F A = Module.finrank F A * Module.finrank F B := hLD2
  have hn' : Module.finrank F B ≠ 2 := hn

  have eA : ∀ W : Place K E, Place.ramificationIndexAlong a' W = W.ramificationIndex A :=
    fun _ => rfl
  have fB : ∀ W : Place K E, W.inertiaDegAlong b' hb' = W.inertiaDeg B := fun _ => rfl
  have fF : ∀ w : Place K A, w.inertiaDegAlong a ha = w.inertiaDeg F := fun _ => rfl
  have eF : ∀ w : Place K B, Place.ramificationIndexAlong b w = w.ramificationIndex F :=
    fun _ => rfl
  have rθ : ∀ w : Place K A, w.restrictAlong θ hθ = w.restrict B := fun _ => rfl
  have fθ : ∀ w : Place K A, w.inertiaDegAlong θ hθ = w.inertiaDeg B := fun _ => rfl

  suffices h : (Divisor.pullbackAlong b hb).comp (Divisor.pushforwardAlong a ha) =
      (Divisor.pushforwardAlong b' hb').comp (Divisor.pullbackAlong a' ha') + Divisor.pushforwardAlong θ hθ from
    DFunLike.congr_fun h D
  refine Finsupp.addHom_ext fun wA n => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.add_apply]
  rw [Divisor.pushforwardAlong_single, Divisor.pullbackAlong_single, Divisor.pullbackAlong_single,
    map_sum, Divisor.pushforwardAlong_single]
  simp only [Divisor.pushforwardAlong_single]

  ext wB
  rw [Finsupp.add_apply, Finset.sum_apply', Finset.sum_apply']
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', eA, fB, fF, eF, rθ, fθ]
  by_cases hv : wB.restrictAlong b hb = wA.restrictAlong a ha
  ·
    rw [if_pos (Place.mem_fiberAlong.mpr hv), ← Finset.sum_filter]
    have hT : ∀ W, W ∈ (Place.fiberAlong a' ha' wA).filter (fun W => W.restrictAlong b' hb' = wB)
        ↔ W.restrict A = wA ∧ W.restrict B = wB := fun W => by
      rw [Finset.mem_filter, Place.mem_fiberAlong]
      exact Iff.rfl
    have key := localDefect (K := K) (F := F) (F₁ := A) (F₂ := B) (E := E) hθs' hgenF hLD2' hn'
      (wA.restrictAlong a ha) wA wB rfl hv _ hT
    have key' : ((∑ W ∈ (Place.fiberAlong a' ha' wA).filter (fun W => W.restrictAlong b' hb' = wB),
        (W.ramificationIndex A : ℤ) * (W.inertiaDeg B : ℤ)) +
          (if wA.restrict B = wB then (wA.inertiaDeg B : ℤ) else 0)) =
        (wA.inertiaDeg F : ℤ) * (wB.ramificationIndex F : ℤ) := by
      exact_mod_cast key
    rw [mul_assoc, ← key', mul_add, Finset.mul_sum, mul_ite, mul_zero]
    congr 1
    exact Finset.sum_congr rfl fun W _ => by ring
  ·
    rw [if_neg (fun h => hv (Place.mem_fiberAlong.mp h))]
    have hθB : ¬ wA.restrict B = wB := by
      intro hθB
      apply hv
      show wB.restrict F = wA.restrict F
      rw [← hθB, restrict_restrict]
    rw [if_neg hθB, add_zero]
    symm
    refine Finset.sum_eq_zero fun W hW => ?_
    rw [if_neg]
    intro hWB
    apply hv
    have h₁ : W.restrict A = wA := Place.mem_fiberAlong.mp hW
    have h₂ : W.restrict B = wB := hWB
    show wB.restrict F = wA.restrict F
    rw [← h₁, ← h₂, restrict_restrict, restrict_restrict]

private theorem heckeDiagonalIdentity_of_localDefect (L : Type*) [Field L] [Algebra ℚ L] (N p : ℕ) [NeZero N] [NeZero p]
    (hp : p.Prime) (hpN : ¬ p ∣ N) : HeckeDiagonalIdentity L N p := by
  intro _ _ hα hβ hα₂ hβ₂ σ hσ hσi D
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have h12 := dvd_of_eq_roof N p p (N * p * p) rfl
  have ha' := towerSubstBar_isIntegral L p h12.2
  have hb' := towerInclBar_isIntegral L h12.1
  have key := pullbackAlong_pushforwardAlong_eq_add_of_defect (heckeAlphaBar L N p) (heckeBetaBar L N p)
    (towerSubstBar L (N * p) p h12.2) (towerInclBar L h12.1) hα hβ ha' hb'
    (heckeSquareBar_commutes L p p h12.1 h12.2) ?hfin ?hsep ?hgen σ.toAlgHom hσi σ.surjective hσ ?hLD2 ?hn D
  case hfin =>
    exact finiteAlong_comp _ _ (finiteAlong_heckeAlphaBar_of_prime L N p) (towerSubstBar_finiteAlong L p h12.2)
  case hsep =>
    exact separableAlong_of_charZero _ (RingHom.IsIntegral.trans _ _ hα ha')
  case hgen =>
    exact heckeRoof_adjoin_range_union_eq_top L N p p (N * p * p) rfl (functionFieldGeneration (N * p * p))
      (modularPolynomialFamily p hp).choose
  case hLD2 =>
    rw [finrankAlong_comp, show towerSubstBar L (N * p) p h12.2 =
        (towerInclBar L h12.2).comp (heckeBetaBar L (N * p) p) from rfl, finrankAlong_comp,
      finrankAlong_heckeBetaBar L (N * p) p, if_pos (dvd_mul_left p N),
      finrankAlong_towerInclBar_of_eq L (N * p * p) (N * p * p) rfl h12.2, finrankAlong_heckeBetaBar L N p,
      if_neg hpN]
    ring
  case hn =>
    rw [finrankAlong_heckeBetaBar L N p, if_neg hpN]
    have := hp.two_le
    omega

  have e1 : towerInclBar L h12.1 = heckeAlphaBar L (N * p) p := rfl
  have e2 : towerSubstBar L (N * p) p h12.2 = heckeBetaBar L (N * p) p :=
    AlgHom.ext fun x => Subtype.ext (by rw [coe_towerSubstBar, coe_heckeBetaBar])
  rw [key, heckeDivBar, Divisor.correspondence_apply, pushforwardAlong_congr' e1 hb' hα₂,
    pullbackAlong_congr' e2 ha' hβ₂]

end WK2AlphaAux

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_heckeDiagonalIdentity_of_prime_of_not_dvd.ModularCurve in

theorem solution
    (L : Type*) [Field L] [Algebra ℚ L] (N p : ℕ) [NeZero N] [NeZero p]
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    HeckeDiagonalIdentity L N p :=
  ModularCurve.WK2AlphaAux.heckeDiagonalIdentity_of_localDefect L N p hp hpN

end S_ModularCurve_heckeDiagonalIdentity_of_prime_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_heckeDiagonalIdentity_of_prime_of_not_dvd (solution)
