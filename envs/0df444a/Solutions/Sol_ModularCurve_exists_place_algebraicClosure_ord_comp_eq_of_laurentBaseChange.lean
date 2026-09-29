-- Prove2me | solution 1 for ModularCurve.exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9e204ab1-42d0-5306-a73d-987999a5db75

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange.ModularCurve"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange mem_laurentBaseChange_iff JOneES.exists_transcendental_finiteDimensional_laurentBaseChange"
namespace T1Aux
p2m_open "ModularCurve"

section CoeffLift

variable {L : Type*} [Field L] {Ω : Type*} [Field Ω] [Algebra ℚ L] [Algebra ℚ Ω] (τ : L →ₐ[ℚ] Ω)
  (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem coeffMap_coeffEmb' (x : LaurentSeries ℚ) : coeffMap τ.toRingHom (coeffEmb L x) = coeffEmb Ω x := by
  change coeffMap _ (coeffMap _ x) = coeffMap _ x
  rw [coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_rat _ _) x

theorem coeffMap_algebraMap' (c : L) :
    coeffMap τ.toRingHom (algebraMap L (LaurentSeries L) c) = algebraMap Ω (LaurentSeries Ω) (τ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

theorem coeffMap_mem_laurentBaseChange' {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    coeffMap τ.toRingHom x ∈ laurentBaseChange Ω F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact (laurentBaseChange Ω F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange Ω hz
  | one => simp
  | add _ _ _ _ hx hy => simpa using add_mem hx hy
  | neg _ _ hx => simpa using neg_mem hx
  | inv _ _ hx => simpa using inv_mem hx
  | mul _ _ _ _ hx hy => simpa using mul_mem hx hy

@[reducible] def algebraOfLift : Algebra L ↥(laurentBaseChange Ω F₀) :=
  ((algebraMap Ω ↥(laurentBaseChange Ω F₀)).comp τ.toRingHom).toAlgebra

def liftRingHom : ↥(laurentBaseChange L F₀) →+* ↥(laurentBaseChange Ω F₀) :=
  ((coeffMap τ.toRingHom).comp (laurentBaseChange L F₀).toSubring.subtype).codRestrict
    (laurentBaseChange Ω F₀).toSubring (fun x => coeffMap_mem_laurentBaseChange' τ F₀ x.2)

theorem coe_liftRingHom (x : ↥(laurentBaseChange L F₀)) :
    ((liftRingHom τ F₀ x : ↥(laurentBaseChange Ω F₀)) : LaurentSeries Ω) = coeffMap τ.toRingHom x :=
  rfl

def liftHom : letI := algebraOfLift τ F₀; ↥(laurentBaseChange L F₀) →ₐ[L] ↥(laurentBaseChange Ω F₀) :=
  letI := algebraOfLift τ F₀
  { liftRingHom τ F₀ with
    commutes' := fun c => Subtype.ext (by
      change coeffMap τ.toRingHom (algebraMap L (LaurentSeries L) c) = algebraMap Ω (LaurentSeries Ω) (τ c)
      exact coeffMap_algebraMap' τ c) }

theorem coe_liftHom (x : ↥(laurentBaseChange L F₀)) :
    letI := algebraOfLift τ F₀; ((liftHom τ F₀ x : ↥(laurentBaseChange Ω F₀)) : LaurentSeries Ω) = coeffMap τ.toRingHom x :=
  rfl

theorem liftHom_toRingHom : letI := algebraOfLift τ F₀; (liftHom τ F₀).toRingHom = liftRingHom τ F₀ := rfl

set_option synthInstance.maxHeartbeats 1600000 in

theorem adjoin_range_liftRingHom_eq_top :
    IntermediateField.adjoin Ω (Set.range (liftRingHom τ F₀)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  let T : IntermediateField Ω ↥(laurentBaseChange Ω F₀) := IntermediateField.adjoin Ω (Set.range (liftRingHom τ F₀))
  let T' : Subfield (LaurentSeries Ω) := T.toSubfield.map (laurentBaseChange Ω F₀).val.toRingHom
  have hgens : Set.range (algebraMap Ω (LaurentSeries Ω)) ∪ (⇑(coeffEmb Ω) '' (F₀ : Set (LaurentSeries ℚ))) ⊆ T' := by
    rintro w (⟨a, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨algebraMap Ω ↥(laurentBaseChange Ω F₀) a, T.algebraMap_mem a, rfl⟩
    · refine ⟨liftRingHom τ F₀ ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩,
        IntermediateField.subset_adjoin Ω _ ⟨_, rfl⟩, ?_⟩
      change coeffMap τ.toRingHom (coeffEmb L x) = coeffEmb Ω x
      exact coeffMap_coeffEmb' τ x
  have hle : Subfield.closure (Set.range (algebraMap Ω (LaurentSeries Ω)) ∪
      (⇑(coeffEmb Ω) '' (F₀ : Set (LaurentSeries ℚ)))) ≤ T' := Subfield.closure_le.mpr hgens
  obtain ⟨w, hw, hwz⟩ := hle (mem_laurentBaseChange_iff.mp z.2)
  have : w = z := Subtype.ext hwz
  rw [← this]
  exact hw

end CoeffLift

end ModularCurve.T1Aux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
open ModularCurve.T1Aux in
theorem solution
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (τ : AlgebraicClosure ℚ →ₐ[ℚ] K)
    (Ψ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) →+*
           ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hΨ : ∀ f, ((Ψ f : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ))) : LaurentSeries K)
             = ModularCurve.coeffMap τ.toRingHom (f : LaurentSeries (AlgebraicClosure ℚ)))
    (P : AlgebraicCurve.Place K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hP : ∃ f, P.ord (Ψ f) ≠ 0) :
    ∃ P₀ : AlgebraicCurve.Place (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)),
      ∀ f, P.ord (Ψ f) = P₀.ord f := by
  classical

  have hΨeq : Ψ = liftRingHom τ (ModularCurve.qExpFunctionFieldC ℚ Γ) := by
    refine RingHom.ext fun f => Subtype.ext ?_
    rw [hΨ, coe_liftRingHom]

  letI algQK : Algebra (AlgebraicClosure ℚ) K := τ.toRingHom.toAlgebra
  letI algQF : Algebra (AlgebraicClosure ℚ) ↥(laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)) := algebraOfLift τ (ModularCurve.qExpFunctionFieldC ℚ Γ)
  haveI : IsScalarTower (AlgebraicClosure ℚ) K ↥(laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI algFF : Algebra ↥(laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥(laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)) := Ψ.toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥(laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    show _ = Ψ (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) c)
    rw [hΨeq]
    exact ((liftHom τ (ModularCurve.qExpFunctionFieldC ℚ Γ)).commutes c).symm

  obtain ⟨x₀, hx₀tr, hx₀fd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) Γ hT
  haveI := hx₀fd
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
    isCurveOver_of_transcendental_of_perfectField hx₀tr hx₀fd
  obtain ⟨x₁, hx₁tr, hx₁fd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange K Γ hT
  have hgen : IntermediateField.adjoin K (Set.range (algebraMap ↥(laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥(laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)))) = ⊤ := by
    show IntermediateField.adjoin K (Set.range Ψ) = ⊤
    rw [hΨeq]
    exact adjoin_range_liftRingHom_eq_top τ (ModularCurve.qExpFunctionFieldC ℚ Γ)

  have hwK : ∀ a : AlgebraicClosure ℚ, Ψ (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) ∈ P.toValuationSubring := by
    intro a
    have : Ψ (algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) = algebraMap K ↥(laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)) (τ a) := by
      rw [hΨeq]
      exact (liftHom τ (ModularCurve.qExpFunctionFieldC ℚ Γ)).commutes a
    rw [this]
    exact P.algebraMap_mem' (τ a)
  have hwx : ∃ y : ↥(laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)), Ψ y ∉ P.toValuationSubring := by
    obtain ⟨f, hf⟩ := hP
    by_contra hall
    push_neg at hall
    apply hf
    have hf0 : Ψ f ≠ 0 := by
      intro h0; apply hf; rw [h0, Place.ord_zero]
    have h1 : Ψ f ∈ P.toValuationSubring := hall f
    have h2 : (Ψ f)⁻¹ ∈ P.toValuationSubring := by rw [← map_inv₀]; exact hall f⁻¹
    let u : (↥P.toValuationSubring)ˣ :=
      ⟨⟨Ψ f, h1⟩, ⟨(Ψ f)⁻¹, h2⟩, Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext (inv_mul_cancel₀ hf0)⟩
    exact P.ord_coe_unit u
  obtain ⟨P₀, hP₀⟩ := Place.exists_toValuationSubring_eq_comap_ringHom (K := AlgebraicClosure ℚ) x₀ Ψ
    P.toValuationSubring hwK hwx

  obtain ⟨P', -, hP'ord, huniq⟩ := Place.exists_comap_algebraMap_eq_of_constantFieldExtension
    (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) K ↥(laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ))
    ⟨x₀, hx₀tr, hx₀fd⟩ ⟨x₁, hx₁tr, hx₁fd⟩ hgen P₀
  have hPP' : P = P' := huniq P (by rw [hP₀]; rfl)
  refine ⟨P₀, fun f => ?_⟩
  rw [hPP']
  exact hP'ord f

end

end S_ModularCurve_exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_exists_place_algebraicClosure_ord_comp_eq_of_laurentBaseChange (solution)
