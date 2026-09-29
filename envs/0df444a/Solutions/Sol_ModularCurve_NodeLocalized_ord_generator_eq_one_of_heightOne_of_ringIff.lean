-- Prove2me | solution 1 for ModularCurve.NodeLocalized.ord_generator_eq_one_of_heightOne_of_ringIff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ab0a44fa-cf72-5572-8db1-6fede1f72697

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_constantsAreBase_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_ord_generator_eq_one_of_heightOne_of_ringIff
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqNModC_one map_jqModC modularFunctionFieldC jqModC_mem qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full modularFunctionFieldBar constantsAreBase_modularFunctionFieldBar"
p2m_open "ModularCurve"

section Remint

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem coeffMap_qExpand' (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem coeffMap_jqModC' (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

private theorem coeffMap_jqNModC' (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, jqNModC, coeffMap_qExpand', coeffMap_jqModC']

private theorem mem_of_ord_nonneg' {K₂ F₂ : Type*} [Field K₂] [Field F₂] [Algebra K₂ F₂]
    (v : AlgebraicCurve.Place K₂ F₂) {f : F₂} (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  have h1 : v.adicValuation f ≤ 1 := v.adicValuation_le_one_iff.mpr (Or.inr h)
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h1
  exact a.2

end Remint

namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "fieldOver jIntegralClosure"
p2m_open "ModularCurve.NodeLocalized"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {K' : IntermediateField ℚ (AlgebraicClosure ℚ)}

omit [Fact q.Prime] in

private theorem Place_ord_one (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    W.ord (1 : modularFunctionFieldBar (1 * q)) = 0 := by
  exact AlgebraicCurve.Place.ord_one (v := W)

omit [Fact q.Prime] in

private theorem Place_ord_inv (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    {g : ↥(modularFunctionFieldBar (1 * q))} (hg : g ≠ 0) : W.ord g⁻¹ = -(W.ord g) := by
  have hginv : g⁻¹ ≠ 0 := inv_ne_zero hg
  have hmul : W.ord (g * g⁻¹) = W.ord g + W.ord g⁻¹ := W.ord_mul hg hginv
  rw [mul_inv_cancel₀ hg, Place_ord_one W] at hmul
  omega

private theorem ord_generator_pos
    {𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K')}
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hWiff : ∀ g : ↥(modularFunctionFieldBar (1 * q)), (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' →
      ((∃ r₀ s₀ : ↥(jIntegralClosure (1 * q) A K'), s₀ ∉ 𝔭 ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * (s₀ : LaurentSeries (AlgebraicClosure ℚ)) = (r₀ : LaurentSeries (AlgebraicClosure ℚ))) ↔ g ∈ W.toValuationSubring))
    {r : ↥(jIntegralClosure (1 * q) A K')} (hr : r ∈ 𝔭) (hr0 : r ≠ 0)
    {gr : ↥(modularFunctionFieldBar (1 * q))} (hgr : (gr : LaurentSeries (AlgebraicClosure ℚ)) = (r : LaurentSeries (AlgebraicClosure ℚ))) :
    0 < W.ord gr := by
  have hrLS : (r : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => hr0 (Subtype.ext h)
  have hgr0 : gr ≠ 0 := fun h => hrLS (by rw [← hgr, h]; exact ZeroMemClass.coe_zero _)
  have hgrF : (gr : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' := by
    rw [hgr]; exact r.2.1
  have hinvF : ((gr⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' := by
    rw [show ((gr⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((gr : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ by push_cast; ring]
    exact (fieldOver (1 * q) K').inv_mem hgrF
  have hnot : (gr⁻¹ : ↥(modularFunctionFieldBar (1 * q))) ∉ W.toValuationSubring := by
    intro hmem
    obtain ⟨r₀, s₀, hs₀, heq₀⟩ := (hWiff gr⁻¹ hinvF).mpr hmem
    rw [show ((gr⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((gr : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ by push_cast; ring,
      hgr] at heq₀
    have hs₀r : (s₀ : LaurentSeries (AlgebraicClosure ℚ)) = (r : LaurentSeries (AlgebraicClosure ℚ)) * (r₀ : LaurentSeries (AlgebraicClosure ℚ)) := by
      field_simp at heq₀
      linear_combination heq₀
    have : s₀ = r * r₀ := Subtype.ext (by push_cast; rw [hs₀r])
    exact hs₀ (this ▸ Ideal.mul_mem_right r₀ 𝔭 hr)
  have hneg : ¬ (0 ≤ W.ord gr⁻¹) := fun hge =>
    hnot (mem_of_ord_nonneg' W hge)
  have h₃ := Place_ord_inv W hgr0
  omega

private theorem fieldOver_le_bar :
    ∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ fieldOver (1 * q) K' → x ∈ modularFunctionFieldBar (1 * q) := by
  have hle : fieldOver (1 * q) K' ≤ (modularFunctionFieldBar (1 * q)).toSubfield := by
    unfold fieldOver
    refine Subfield.closure_le.mpr ?_
    rintro y (⟨a, rfl⟩ | hy)
    · exact (modularFunctionFieldBar (1 * q)).algebraMap_mem (a : AlgebraicClosure ℚ)
    · rcases hy with rfl | rfl
      · have h : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
          rw [show jq = jqModC ℚ from rfl]
          exact coeffMap_jqModC' _
        rw [← h]
        exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))
      · have h : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
          rw [show jq = jqModC ℚ from rfl]
          unfold jqNModC
          rw [show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) (jqModC ℚ))
              = qExpand (AlgebraicClosure ℚ) (1 * q) (coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ)) from
            coeffMap_qExpand' _ (1 * q) _]
          exact congrArg (qExpand (AlgebraicClosure ℚ) (1 * q)) (coeffMap_jqModC' _)
        rw [← h]
        exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (dvd_refl (1 * q)))
  exact fun x hx => hle hx

private def liftHom : ↥(fieldOver (1 * q) K') →+* ↥(modularFunctionFieldBar (1 * q)) where
  toFun x := ⟨(x : LaurentSeries (AlgebraicClosure ℚ)), fieldOver_le_bar (q := q) (K' := K') _ x.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

private theorem const_mem_fieldOver (a : ↥K') :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) ∈ fieldOver (1 * q) K' := by
  unfold fieldOver
  exact Subfield.subset_closure (Or.inl ⟨⟨(a : AlgebraicClosure ℚ), a.2⟩, rfl⟩)

private def constHom0 : ↥K' →+* LaurentSeries (AlgebraicClosure ℚ) :=
  (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp
    (algebraMap ↥K' (AlgebraicClosure ℚ))

private def constHom : ↥K' →+* ↥(fieldOver (1 * q) K') where
  toFun a := ⟨constHom0 (K' := K') a, const_mem_fieldOver a⟩
  map_one' := Subtype.ext (map_one (constHom0 (K' := K')))
  map_mul' a b := Subtype.ext (map_mul (constHom0 (K' := K')) a b)
  map_zero' := Subtype.ext (map_zero (constHom0 (K' := K')))
  map_add' a b := Subtype.ext (map_add (constHom0 (K' := K')) a b)

@[reducible] private def algKFO : Algebra ↥K' ↥(fieldOver (1 * q) K') := constHom.toAlgebra
attribute [local instance] algKFO
@[reducible] private def algFOBar : Algebra ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q)) := liftHom.toAlgebra
attribute [local instance] algFOBar
private theorem towerKFOBar : IsScalarTower ↥K' ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
attribute [local instance] towerKFOBar

private theorem coeffEmb_mem_fieldOver_of_mem_full
    {x : LaurentSeries ℚ} (hx : x ∈ modularFunctionFieldFull (1 * q)) :
    coeffEmb (AlgebraicClosure ℚ) x ∈ fieldOver (1 * q) K' := by
  induction hx using IntermediateField.adjoin_induction with
  | mem z hz =>
      obtain ⟨d, hdne, hd, rfl⟩ := hz
      haveI := hdne
      have hcz : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq)
          = jqNModC (AlgebraicClosure ℚ) d := by
        rw [show jq = jqModC ℚ from rfl]
        rw [show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d (jqModC ℚ))
            = qExpand (AlgebraicClosure ℚ) d (coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ)) from
          coeffMap_qExpand' _ d _]
        exact congrArg (qExpand (AlgebraicClosure ℚ) d) (coeffMap_jqModC' _)
      rw [hcz]
      rw [one_mul] at hd
      rcases (Fact.out : q.Prime).eq_one_or_self_of_dvd d hd with rfl | h
      · rw [jqNModC_one]
        exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
      · subst h
        have hval : jqNModC (AlgebraicClosure ℚ) d = jqNModC (AlgebraicClosure ℚ) (1 * d) := by
          congr 1
          exact (one_mul d).symm
        rw [hval]
        exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
  | algebraMap r =>
      simp
  | add a b ha hb iha ihb => rw [map_add]; exact add_mem iha ihb
  | mul a b ha hb iha ihb => rw [map_mul]; exact mul_mem iha ihb
  | inv a ha iha => rw [map_inv₀]; exact inv_mem iha

private theorem isIntegral_constant (c : AlgebraicClosure ℚ) :
    IsIntegral ↥(fieldOver (1 * q) K') (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c) := by
  haveI := towerKFOBar (q := q) (K' := K')
  have h1 : IsIntegral ↥K' c :=
    (((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c).tower_top (L := ↥K')).isIntegral
  have h2 : IsIntegral ↥K' (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c) :=
    h1.algebraMap
  exact h2.tower_top

private theorem adjoinS_le_integralClosure :
    Algebra.adjoin ↥(fieldOver (1 * q) K')
      (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))))
      ≤ integralClosure ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q)) := by
  apply Algebra.adjoin_le
  rintro x ⟨c, rfl⟩
  exact isIntegral_constant c

private theorem inv_mem_adjoinS {y : ↥(modularFunctionFieldBar (1 * q))}
    (hy : y ∈ Algebra.adjoin ↥(fieldOver (1 * q) K')
      (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))))) :
    y⁻¹ ∈ Algebra.adjoin ↥(fieldOver (1 * q) K')
      (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) := by
  have hyi : IsIntegral ↥(fieldOver (1 * q) K') y := adjoinS_le_integralClosure (q := q) (K' := K') hy
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hy) hyi.inv_mem_adjoin

private def Sfield : IntermediateField (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) where
  carrier := (Algebra.adjoin ↥(fieldOver (1 * q) K')
    (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) : Set ↥(modularFunctionFieldBar (1 * q)))
  mul_mem' := fun ha hb => Subalgebra.mul_mem _ ha hb
  add_mem' := fun ha hb => Subalgebra.add_mem _ ha hb
  algebraMap_mem' := fun r => Algebra.subset_adjoin ⟨r, rfl⟩
  inv_mem' := fun _ hy => inv_mem_adjoinS (q := q) (K' := K') hy

private theorem hgen_leg :
    Algebra.adjoin ↥(fieldOver (1 * q) K')
      (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) = (⊤ : Subalgebra ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q))) := by
  rw [eq_top_iff]
  intro y _
  have hle : modularFunctionFieldBar (1 * q)
      ≤ IntermediateField.map (modularFunctionFieldBar (1 * q)).val (Sfield (q := q) (K' := K')) := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨x₀, hx₀, rfl⟩
    exact ⟨algebraMap ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q))
        ⟨coeffEmb (AlgebraicClosure ℚ) x₀, coeffEmb_mem_fieldOver_of_mem_full (K' := K') hx₀⟩,
      (Subalgebra.algebraMap_mem
        (Algebra.adjoin ↥(fieldOver (1 * q) K') (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))))
        ⟨coeffEmb (AlgebraicClosure ℚ) x₀, coeffEmb_mem_fieldOver_of_mem_full (K' := K') hx₀⟩ : _),
      rfl⟩
  obtain ⟨s, hs, hval⟩ := hle y.2
  have hsy : s = y := Subtype.coe_injective hval
  exact hsy ▸ hs

private theorem hintegral_leg :
    ∀ y : ↥(modularFunctionFieldBar (1 * q)), IsIntegral ↥(fieldOver (1 * q) K') y := fun y => by
  have htop := hgen_leg (q := q) (K' := K')
  have hy : y ∈ Algebra.adjoin ↥(fieldOver (1 * q) K')
      (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) := by
    rw [htop]; exact Algebra.mem_top
  exact adjoinS_le_integralClosure (q := q) (K' := K') hy

private theorem instIsIntegral_fieldOver_bar : Algebra.IsIntegral ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨fun y => hintegral_leg (q := q) (K' := K') y⟩
attribute [local instance] instIsIntegral_fieldOver_bar

private theorem isConstant_of_isAlgebraic
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (halg : IsAlgebraic ↥K' (f : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ c : AlgebraicClosure ℚ, (f : LaurentSeries (AlgebraicClosure ℚ))
      = CharPReduction.constSeries (⊤ : Subring (AlgebraicClosure ℚ)) ⟨c, trivial⟩ := by
  have h1 : IsAlgebraic (AlgebraicClosure ℚ) (f : LaurentSeries (AlgebraicClosure ℚ)) := by
    haveI := IsScalarTower.of_algebraMap_eq (R := ↥K') (S := AlgebraicClosure ℚ)
      (A := LaurentSeries (AlgebraicClosure ℚ)) fun x => rfl
    exact halg.tower_top (L := AlgebraicClosure ℚ)
  have h2 : IsAlgebraic (AlgebraicClosure ℚ) f := by
    rwa [← IntermediateField.isAlgebraic_iff] at h1
  have hint : IsIntegral (AlgebraicClosure ℚ) f := h2.isIntegral
  have hmem : ∀ v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), f ∈ v.toValuationSubring := by
    intro v
    have h4 : IsIntegral v.toValuationSubring f := hint.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h4
    rw [← hy]
    exact y.2
  have h5 : f ∈ LSpace (0 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) := by
    rw [mem_lSpace_iff]
    intro v
    calc v.adicValuation f
        = v.heightOneSpectrum.intValuation ⟨f, hmem v⟩ := v.adicValuation_coe ⟨f, hmem v⟩
      _ ≤ 1 := v.heightOneSpectrum.intValuation_le_one _
      _ = WithZero.exp ((0 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) v) := by
          simp
  have h6 := ModularCurve.constantsAreBase_modularFunctionFieldBar (1 * q)
  rw [ConstantsAreBase] at h6
  rw [h6] at h5
  obtain ⟨c, hc⟩ := h5
  exact ⟨c, by rw [← hc]; rfl⟩

private theorem coeff_mem_of_constSeries_mem_fieldOver_ls
    {c : AlgebraicClosure ℚ}
    (hc : CharPReduction.constSeries (⊤ : Subring (AlgebraicClosure ℚ)) ⟨c, trivial⟩
      ∈ fieldOver (1 * q) K') :
    c ∈ K' := by
  have hle : fieldOver (1 * q) K' ≤
      Subfield.map (coeffMap (algebraMap ↥K' (AlgebraicClosure ℚ)))
        (modularFunctionFieldC ↥K' (1 * q)).toSubfield := by
    rw [fieldOver]
    apply Subfield.closure_le.mpr
    rintro z (⟨a, rfl⟩ | hz)
    · refine ⟨algebraMap ↥K' (LaurentSeries ↥K') ⟨(a : AlgebraicClosure ℚ), a.2⟩,
        IntermediateField.algebraMap_mem _ _, ?_⟩
      show coeffMap (algebraMap ↥K' (AlgebraicClosure ℚ))
            (algebraMap ↥K' (LaurentSeries ↥K') ⟨(a : AlgebraicClosure ℚ), a.2⟩)
          = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ)
      rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single,
        coeffMap_single]
      rfl
    · rcases hz with rfl | hz1
      · exact ⟨jqModC ↥K', jqModC_mem ↥K' (1 * q),
          coeffMap_jqModC' (algebraMap ↥K' (AlgebraicClosure ℚ))⟩
      · rcases Set.mem_singleton_iff.mp hz1 with rfl
        exact ⟨jqNModC ↥K' (1 * q),
          IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl),
          coeffMap_jqNModC' (algebraMap ↥K' (AlgebraicClosure ℚ)) (1 * q)⟩
  obtain ⟨x, hxmem, hxeq⟩ := hle hc
  have h0 := congrArg (fun t => t.coeff 0) hxeq
  simp only [coeffMap_coeff] at h0
  have hc0 : (CharPReduction.constSeries (⊤ : Subring (AlgebraicClosure ℚ)) ⟨c, trivial⟩).coeff 0
      = c := by
    show ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) c).coeff 0 = c
    rw [algebraMap_laurentSeries_eq_single]
    exact HahnSeries.coeff_single_same 0 c
  rw [hc0] at h0
  rw [← h0]
  exact (x.coeff 0).2

private theorem hconst_leg :
    ∀ y : ↥(fieldOver (1 * q) K'), IsAlgebraic ↥K' y → y ∈ (algebraMap ↥K' ↥(fieldOver (1 * q) K')).range := by
  intro y halg
  have hyb : (y : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar (1 * q) :=
    fieldOver_le_bar (q := q) (K' := K') _ y.2
  have halg' : IsAlgebraic ↥K' ((⟨(y : LaurentSeries (AlgebraicClosure ℚ)), hyb⟩ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    have hφ : ∀ k : ↥K',
        ((algebraMap ↥K' ↥(fieldOver (1 * q) K') k : ↥(fieldOver (1 * q) K')) : LaurentSeries (AlgebraicClosure ℚ))
          = algebraMap ↥K' (LaurentSeries (AlgebraicClosure ℚ)) k := fun k => rfl
    exact halg.algHom
      { toRingHom := (fieldOver (1 * q) K').subtype, commutes' := hφ }
  obtain ⟨c, hc⟩ := isConstant_of_isAlgebraic (q := q) (K' := K')
    ⟨(y : LaurentSeries (AlgebraicClosure ℚ)), hyb⟩ halg'
  have hcK : c ∈ K' := by
    apply coeff_mem_of_constSeries_mem_fieldOver_ls (q := q) (K' := K')
    rw [← hc]
    exact y.2
  refine ⟨⟨c, hcK⟩, ?_⟩
  apply Subtype.ext
  have heq : ((algebraMap ↥K' ↥(fieldOver (1 * q) K') ⟨c, hcK⟩ : ↥(fieldOver (1 * q) K')) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap ↥K' (LaurentSeries (AlgebraicClosure ℚ)) ⟨c, hcK⟩ := rfl
  rw [heq]
  exact hc.symm

private theorem ord_eq_one_of_irreducible (w₀ : Place ↥K' ↥(fieldOver (1 * q) K')) (rF : ↥(fieldOver (1 * q) K'))
    (hrFmem : rF ∈ w₀.toValuationSubring) (hirr' : Irreducible (⟨rF, hrFmem⟩ : w₀.toValuationSubring)) :
    w₀.ord rF = 1 := by
  have hval : w₀.adicValuation (rF : ↥(fieldOver (1 * q) K')) = WithZero.exp (-1 : ℤ) := by
    have h := w₀.adicValuation_coe_irreducible hirr'
    exact h
  rw [AlgebraicCurve.Place.ord, hval, WithZero.log_exp]
  omega

private theorem hdownstairs_leg
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K')) (h𝔭p : 𝔭.IsPrime)
    (r : ↥(jIntegralClosure (1 * q) A K')) (_hr : r ∈ 𝔭) (hr0 : r ≠ 0)
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime 𝔭))
    (hspan : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭)
      = Ideal.span {algebraMap ↥(jIntegralClosure (1 * q) A K') (Localization.AtPrime 𝔭) r})
    (w₀ : Place ↥K' ↥(fieldOver (1 * q) K'))
    (hw₀ : ∀ g : ↥(fieldOver (1 * q) K'), ((∃ r₀ s₀ : ↥(jIntegralClosure (1 * q) A K'), s₀ ∉ 𝔭 ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * (s₀ : LaurentSeries (AlgebraicClosure ℚ)) = (r₀ : LaurentSeries (AlgebraicClosure ℚ))) ↔ g ∈ w₀.toValuationSubring))
    (rF : ↥(fieldOver (1 * q) K')) (hrF : (rF : LaurentSeries (AlgebraicClosure ℚ)) = (r : LaurentSeries (AlgebraicClosure ℚ))) :
    w₀.ord rF = 1 := by
  haveI := h𝔭p
  classical
  have hmem : ∀ x : ↥(jIntegralClosure (1 * q) A K'), (⟨(x : LaurentSeries (AlgebraicClosure ℚ)), x.2.1⟩ : ↥(fieldOver (1 * q) K')) ∈ w₀.toValuationSubring := by
    intro x
    refine (hw₀ _).mp ⟨x, 1, fun h => ?_, by push_cast; ring⟩
    exact h𝔭p.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 h isUnit_one)
  let φ : ↥(jIntegralClosure (1 * q) A K') →+* w₀.toValuationSubring :=
    { toFun := fun x => ⟨⟨(x : LaurentSeries (AlgebraicClosure ℚ)), x.2.1⟩, hmem x⟩
      map_one' := Subtype.ext (Subtype.ext rfl)
      map_mul' := fun a b => Subtype.ext (Subtype.ext rfl)
      map_zero' := Subtype.ext (Subtype.ext rfl)
      map_add' := fun a b => Subtype.ext (Subtype.ext rfl) }
  have hφcoeLS : ∀ x : ↥(jIntegralClosure (1 * q) A K'), ((φ x : ↥(fieldOver (1 * q) K')) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) := fun _ => rfl
  have hφne : ∀ x : ↥(jIntegralClosure (1 * q) A K'), x ≠ 0 → (φ x : ↥(fieldOver (1 * q) K')) ≠ 0 := by
    intro x hx h
    apply hx
    apply Subtype.ext
    have h2 : ((φ x : ↥(fieldOver (1 * q) K')) : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by rw [h]; exact ZeroMemClass.coe_zero _
    rwa [hφcoeLS] at h2
  have hψ0 : ∀ y : 𝔭.primeCompl, IsUnit (φ (y : ↥(jIntegralClosure (1 * q) A K'))) := by
    rintro ⟨s, hs⟩
    have hs0 : s ≠ 0 := by rintro rfl; exact hs 𝔭.zero_mem
    have hFne : (φ s : ↥(fieldOver (1 * q) K')) ≠ 0 := hφne s hs0
    have hinvLS : (((φ s : ↥(fieldOver (1 * q) K'))⁻¹ : ↥(fieldOver (1 * q) K')) : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) = ((1 : ↥(jIntegralClosure (1 * q) A K')) : LaurentSeries (AlgebraicClosure ℚ)) := by
      push_cast
      exact inv_mul_cancel₀ (fun h0 => hs0 (Subtype.ext h0))
    have hinv : (φ s : ↥(fieldOver (1 * q) K'))⁻¹ ∈ w₀.toValuationSubring := (hw₀ _).mp ⟨1, s, hs, hinvLS⟩
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hFne)⟩
  let ψ : Localization.AtPrime 𝔭 →+* w₀.toValuationSubring := IsLocalization.lift hψ0
  have hψalg : ∀ x : ↥(jIntegralClosure (1 * q) A K'), ψ (algebraMap _ _ x) = φ x := fun x => IsLocalization.lift_eq hψ0 x
  have hψr0 : ψ (algebraMap _ _ r) ≠ 0 := by
    rw [hψalg]
    intro h0
    exact hφne r hr0 (by rw [h0]; rfl)
  have hirr : Irreducible (algebraMap ↥(jIntegralClosure (1 * q) A K') (Localization.AtPrime 𝔭) r) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    exact hspan
  have hψinj : Function.Injective ψ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    haveI hkp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
    have hmax : (RingHom.ker ψ).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne hkp
    have heqm : RingHom.ker ψ = IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) :=
      IsLocalRing.eq_maximalIdeal hmax
    have hrin : algebraMap ↥(jIntegralClosure (1 * q) A K') (Localization.AtPrime 𝔭) r ∈ RingHom.ker ψ := by
      rw [heqm, hspan]
      exact Ideal.mem_span_singleton_self _
    exact hψr0 hrin
  have hψsurj : Function.Surjective ψ := by
    intro g
    obtain ⟨r₀, s₀, hs₀, heq⟩ := (hw₀ g).mpr g.2
    refine ⟨IsLocalization.mk' _ r₀ (⟨s₀, hs₀⟩ : 𝔭.primeCompl), ?_⟩
    have h1 : ψ (IsLocalization.mk' _ r₀ (⟨s₀, hs₀⟩ : 𝔭.primeCompl)) * φ s₀ = φ r₀ := by
      rw [← hψalg s₀, ← hψalg r₀, ← map_mul]
      congr 1
      exact IsLocalization.mk'_spec _ r₀ ⟨s₀, hs₀⟩
    have h2 : g * φ s₀ = φ r₀ := Subtype.ext (Subtype.ext (by push_cast; exact heq))
    refine (hψ0 ⟨s₀, hs₀⟩).mul_left_cancel ?_
    calc φ ((⟨s₀, hs₀⟩ : 𝔭.primeCompl) : ↥(jIntegralClosure (1 * q) A K')) * ψ (IsLocalization.mk' _ r₀ (⟨s₀, hs₀⟩ : 𝔭.primeCompl))
        = ψ (IsLocalization.mk' _ r₀ (⟨s₀, hs₀⟩ : 𝔭.primeCompl)) * φ s₀ := mul_comm _ _
      _ = φ r₀ := h1
      _ = g * φ s₀ := h2.symm
      _ = φ ((⟨s₀, hs₀⟩ : 𝔭.primeCompl) : ↥(jIntegralClosure (1 * q) A K')) * g := mul_comm _ _
  let ψe : Localization.AtPrime 𝔭 ≃+* w₀.toValuationSubring := RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have hrFmem : rF ∈ w₀.toValuationSubring := by
    refine (hw₀ _).mp ⟨r, 1, fun h => h𝔭p.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 h isUnit_one), ?_⟩
    push_cast
    rw [hrF]; ring
  have hψr : ψe (algebraMap _ _ r) = ⟨rF, hrFmem⟩ := by
    show ψ (algebraMap _ _ r) = _
    rw [hψalg]
    exact Subtype.ext (Subtype.ext (by push_cast [hφcoeLS]; exact hrF.symm))
  have hirr' : Irreducible (⟨rF, hrFmem⟩ : w₀.toValuationSubring) := by
    have h := hirr.map ψe
    rwa [hψr] at h
  exact ord_eq_one_of_irreducible (q := q) (K' := K') w₀ rF hrFmem hirr'

section GenericRestrict

variable {K₀ K₁ F₀ F₁ : Type*} [Field K₀] [Field K₁] [Field F₀] [Field F₁]
  [Algebra K₀ K₁] [Algebra K₁ F₁] [Algebra K₀ F₁] [IsScalarTower K₀ K₁ F₁]
  [Algebra K₀ F₀] [Algebra F₀ F₁] [IsScalarTower K₀ F₀ F₁] [Algebra.IsIntegral F₀ F₁]

private theorem ord_le_one_of_restrict_generic (w : AlgebraicCurve.Place K₁ F₁) (g : F₀)
    (hord : (AlgebraicCurve.Place.restrictConstants F₀ (K := K₀) w).ord g = 1)
    (hram : AlgebraicCurve.Place.ramificationIndex (F := F₀)
      (AlgebraicCurve.Place.forgetConstants (K := K₀) w) = 1) :
    w.ord (algebraMap F₀ F₁ g) ≤ 1 := by
  rw [AlgebraicCurve.Place.ord_restrictConstants (K := K₀) w g, hram, hord]
  simp

end GenericRestrict

private theorem hram_leg (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    AlgebraicCurve.Place.ramificationIndex (F := ↥(fieldOver (1 * q) K'))
      (AlgebraicCurve.Place.forgetConstants (K := ↥K') W) = 1 := by
  haveI : CharZero ↥K' := charZero_of_injective_algebraMap (algebraMap ℚ ↥K').injective
  haveI : Algebra.IsAlgebraic ↥K' (AlgebraicClosure ℚ) :=
    ⟨fun x => (((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).tower_top (L := ↥K'))⟩
  exact AlgebraicCurve.Place.ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
    (hgen_leg (q := q) (K' := K')) (hconst_leg (q := q) (K' := K')) W

private theorem coe_algebraMap_fieldOver (g : ↥(fieldOver (1 * q) K')) :
    ((algebraMap ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q)) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = (g : LaurentSeries (AlgebraicClosure ℚ)) := rfl

private theorem restrict_ring_eq (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    (AlgebraicCurve.Place.restrictConstants (↥(fieldOver (1 * q) K')) (K := ↥K') W).toValuationSubring
      = W.toValuationSubring.comap (algebraMap ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q))) :=
  AlgebraicCurve.Place.restrictConstants_toValuationSubring (K := ↥K') W

private theorem hw₀_leg₁ (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K')) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hWiff : ∀ g : ↥(modularFunctionFieldBar (1 * q)), (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' →
      ((∃ r₀ s₀ : ↥(jIntegralClosure (1 * q) A K'), s₀ ∉ 𝔭 ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * (s₀ : LaurentSeries (AlgebraicClosure ℚ)) = (r₀ : LaurentSeries (AlgebraicClosure ℚ))) ↔ g ∈ W.toValuationSubring)) :
    ∀ g : ↥(fieldOver (1 * q) K'), ((∃ r₀ s₀ : ↥(jIntegralClosure (1 * q) A K'), s₀ ∉ 𝔭 ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) * (s₀ : LaurentSeries (AlgebraicClosure ℚ)) = (r₀ : LaurentSeries (AlgebraicClosure ℚ))) ↔ algebraMap ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q)) g ∈ W.toValuationSubring) := by
  intro g
  have hmem : ((algebraMap ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q)) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' :=
    (congrArg (fun t : LaurentSeries (AlgebraicClosure ℚ) => t ∈ fieldOver (1 * q) K') (coe_algebraMap_fieldOver g)).mpr g.2
  have h2 := Iff.of_eq (congrArg
    (fun t : LaurentSeries (AlgebraicClosure ℚ) => ∃ r₀ s₀ : ↥(jIntegralClosure (1 * q) A K'), s₀ ∉ 𝔭 ∧ t * (s₀ : LaurentSeries (AlgebraicClosure ℚ)) = (r₀ : LaurentSeries (AlgebraicClosure ℚ)))
    (coe_algebraMap_fieldOver g))
  exact h2.symm.trans (hWiff (algebraMap ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q)) g) hmem)

private theorem hw₀_leg (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K')) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hWiff : ∀ g : ↥(modularFunctionFieldBar (1 * q)), (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' →
      ((∃ r₀ s₀ : ↥(jIntegralClosure (1 * q) A K'), s₀ ∉ 𝔭 ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * (s₀ : LaurentSeries (AlgebraicClosure ℚ)) = (r₀ : LaurentSeries (AlgebraicClosure ℚ))) ↔ g ∈ W.toValuationSubring)) :
    ∀ g : ↥(fieldOver (1 * q) K'), ((∃ r₀ s₀ : ↥(jIntegralClosure (1 * q) A K'), s₀ ∉ 𝔭 ∧
      (g : LaurentSeries (AlgebraicClosure ℚ)) * (s₀ : LaurentSeries (AlgebraicClosure ℚ)) = (r₀ : LaurentSeries (AlgebraicClosure ℚ))) ↔ g ∈ (AlgebraicCurve.Place.restrictConstants (↥(fieldOver (1 * q) K')) (K := ↥K') W).toValuationSubring) := by
  intro g
  rw [restrict_ring_eq W, ValuationSubring.mem_comap]
  exact hw₀_leg₁ 𝔭 W hWiff g

private theorem ord_le_one_of_heightOne_of_ringIff
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K')) (h𝔭p : 𝔭.IsPrime) (_hheight : 𝔭.height = 1)
    (_hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K')) ∉ 𝔭)
    (r : ↥(jIntegralClosure (1 * q) A K')) (hr : r ∈ 𝔭) (hr0 : r ≠ 0)
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime 𝔭))
    (hspan : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭)
      = Ideal.span {algebraMap ↥(jIntegralClosure (1 * q) A K') (Localization.AtPrime 𝔭) r})
    (_hval : (@IsDiscreteValuationRing.addVal (Localization.AtPrime 𝔭) _ _ hdvr)
      (algebraMap ↥(jIntegralClosure (1 * q) A K') (Localization.AtPrime 𝔭) r) = 1)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hWiff : ∀ g : ↥(modularFunctionFieldBar (1 * q)), (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' →
      ((∃ r₀ s₀ : ↥(jIntegralClosure (1 * q) A K'), s₀ ∉ 𝔭 ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * (s₀ : LaurentSeries (AlgebraicClosure ℚ)) = (r₀ : LaurentSeries (AlgebraicClosure ℚ))) ↔ g ∈ W.toValuationSubring))
    (gr : ↥(modularFunctionFieldBar (1 * q))) (hgr : (gr : LaurentSeries (AlgebraicClosure ℚ)) = (r : LaurentSeries (AlgebraicClosure ℚ))) :
    W.ord gr ≤ 1 := by
  have hrFO : (gr : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' := by
    rw [hgr]; exact r.2.1
  have hw₀ := hw₀_leg (q := q) (K' := K') (A := A) 𝔭 W hWiff
  have hord₀ : (AlgebraicCurve.Place.restrictConstants (↥(fieldOver (1 * q) K')) (K := ↥K') W).ord (⟨(gr : LaurentSeries (AlgebraicClosure ℚ)), hrFO⟩ : ↥(fieldOver (1 * q) K')) = 1 :=
    hdownstairs_leg (q := q) (K' := K') (A := A) 𝔭 h𝔭p r hr hr0 hdvr hspan _ hw₀ _ hgr
  have hram := hram_leg (q := q) (K' := K') W
  have h := ord_le_one_of_restrict_generic (K₀ := ↥K') W _ hord₀ hram
  have hg₀ : gr = algebraMap ↥(fieldOver (1 * q) K') ↥(modularFunctionFieldBar (1 * q)) (⟨(gr : LaurentSeries (AlgebraicClosure ℚ)), hrFO⟩ : ↥(fieldOver (1 * q) K')) :=
    Subtype.ext rfl
  rw [hg₀]
  exact h

end NodeLocalized

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_NodeLocalized_ord_generator_eq_one_of_heightOne_of_ringIff.ModularCurve _root_.ModularCurve.NodeLocalized _root_.P2MW.S_ModularCurve_NodeLocalized_ord_generator_eq_one_of_heightOne_of_ringIff.ModularCurve.NodeLocalized in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {K' : IntermediateField ℚ (AlgebraicClosure ℚ)} [FiniteDimensional ℚ ↥K']
    (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K')) (h𝔭p : 𝔭.IsPrime) (hheight : 𝔭.height = 1)
    (hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K')) ∉ 𝔭)
    (r : ↥(jIntegralClosure (1 * q) A K')) (hr : r ∈ 𝔭) (hr0 : r ≠ 0)
    (hdvr : IsDiscreteValuationRing (Localization.AtPrime 𝔭))
    (hspan : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭)
      = Ideal.span {algebraMap ↥(jIntegralClosure (1 * q) A K') (Localization.AtPrime 𝔭) r})
    (hval : (@IsDiscreteValuationRing.addVal (Localization.AtPrime 𝔭) _ _ hdvr)
      (algebraMap ↥(jIntegralClosure (1 * q) A K') (Localization.AtPrime 𝔭) r) = 1)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hWiff : ∀ g : ↥(modularFunctionFieldBar (1 * q)), (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K' →
      ((∃ r₀ s₀ : ↥(jIntegralClosure (1 * q) A K'), s₀ ∉ 𝔭 ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) * (s₀ : LaurentSeries (AlgebraicClosure ℚ)) = (r₀ : LaurentSeries (AlgebraicClosure ℚ))) ↔ g ∈ W.toValuationSubring))
    (gr : ↥(modularFunctionFieldBar (1 * q))) (hgr : (gr : LaurentSeries (AlgebraicClosure ℚ)) = (r : LaurentSeries (AlgebraicClosure ℚ))) :
    W.ord gr = 1 := by
  have h1 := ModularCurve.NodeLocalized.ord_generator_pos W hWiff hr hr0 hgr
  have h2 := ModularCurve.NodeLocalized.ord_le_one_of_heightOne_of_ringIff 𝔭 h𝔭p hheight hq𝔭 r hr hr0 hdvr hspan hval W hWiff gr hgr
  omega

section Probes
#print axioms solution
end Probes

end S_ModularCurve_NodeLocalized_ord_generator_eq_one_of_heightOne_of_ringIff
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_ord_generator_eq_one_of_heightOne_of_ringIff (solution)
