-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ba350f73-b810-540f-b199-c58f27e18a88

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_range_comp_zero_iff_map_ker_le
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

noncomputable section

namespace CompFrob

section Rings

variable {R κ O O' : Type*} [CommRing R] [CommRing κ] [CommRing O] [CommRing O'] [Algebra R κ] [Algebra R O] [Algebra R O']

theorem comm_comp_includeLeftRingHom :
    (Algebra.TensorProduct.comm R O κ).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := O) (B := κ)) =
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom := by
  refine RingHom.ext fun o => ?_
  show Algebra.TensorProduct.comm R O κ (o ⊗ₜ[R] (1 : κ)) = (1 : κ) ⊗ₜ[R] o
  exact Algebra.TensorProduct.comm_tmul R o (1 : κ)

theorem comm_comp_includeRight :
    (Algebra.TensorProduct.comm R O κ).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := O) (B := κ)).toRingHom =
      Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O) := by
  refine RingHom.ext fun a => ?_
  show Algebra.TensorProduct.comm R O κ ((1 : O) ⊗ₜ[R] a) = a ⊗ₜ[R] (1 : O)
  exact Algebra.TensorProduct.comm_tmul R (1 : O) a

theorem map_id_comp_includeRight (ι : O' →ₐ[R] O) :
    (Algebra.TensorProduct.map (AlgHom.id R κ) ι).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O')).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom.comp ι.toRingHom := by
  refine RingHom.ext fun b => ?_
  show Algebra.TensorProduct.map (AlgHom.id R κ) ι ((1 : κ) ⊗ₜ[R] b) = (1 : κ) ⊗ₜ[R] (ι b)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem map_id_comp_includeLeftRingHom (ι : O' →ₐ[R] O) :
    (Algebra.TensorProduct.map (AlgHom.id R κ) ι).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O')) =
      Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O) := by
  refine RingHom.ext fun a => ?_
  show Algebra.TensorProduct.map (AlgHom.id R κ) ι (a ⊗ₜ[R] (1 : O')) = a ⊗ₜ[R] (1 : O)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

end Rings

section Chart

variable (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
  (κ : Type) [CommRing κ] [Algebra (R p) κ]

set_option maxHeartbeats 3200000 in

theorem chartInf_baseChange :
    ∃ g : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p Γ hj))) ⟶ fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ),
      IsOpenImmersion g ∧
      g ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))).toRingHom) ≫ ιInf p Γ hj ∧
      g ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj)))) ∧
      Set.range g.base = ((pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) ⁻¹ᵁ
        ((ιInf p Γ hj) ''ᵁ ⊤) : Set ↥(fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ))) := by
  set A : Type := ↥(chartAlgInf p Γ hj) with hA
  set b : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of (R p)) := Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)) with hb
  set a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (R p)) := Spec.map (CommRingCat.ofHom (algebraMap (R p) A)) with ha
  have hιa : ιInf p Γ hj ≫ toBase p Γ hj = a := TwoChartIntegralModel.ιInf_toBase _ _ _
  let g' : pullback a b ⟶ pullback (toBase p Γ hj) b :=
    pullback.lift (pullback.fst a b ≫ ιInf p Γ hj) (pullback.snd a b) (by rw [Category.assoc, hιa, pullback.condition])
  have hg'fst : g' ≫ pullback.fst _ _ = pullback.fst a b ≫ ιInf p Γ hj := pullback.lift_fst _ _ _
  have hg'snd : g' ≫ pullback.snd _ _ = pullback.snd a b := pullback.lift_snd _ _ _
  have sq : IsPullback (pullback.fst a b) g' (ιInf p Γ hj) (pullback.fst (toBase p Γ hj) b) := by
    refine IsPullback.of_bot ?_ hg'fst.symm (IsPullback.of_hasPullback (toBase p Γ hj) b)
    rw [hg'snd, hιa]
    exact IsPullback.of_hasPullback a b
  have hopen : IsOpenImmersion g' := MorphismProperty.of_isPullback sq inferInstance
  have hrange : Set.range g'.base = ((pullback.fst (toBase p Γ hj) b) ⁻¹ᵁ ((ιInf p Γ hj) ''ᵁ ⊤) : Set _) := by
    have e1 : g' = sq.isoPullback.hom ≫ pullback.snd (ιInf p Γ hj) (pullback.fst (toBase p Γ hj) b) :=
      (sq.isoPullback_hom_snd).symm
    have hs1 : Function.Surjective sq.isoPullback.hom.base := sq.isoPullback.hom.homeomorph.surjective
    rw [e1, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs1, Set.image_univ,
      Scheme.Pullback.range_snd]
    ext x
    simp only [Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, trivial, hy⟩
    · rintro ⟨y, -, hy⟩; exact ⟨y, hy⟩

  set gq : Spec (CommRingCat.of (A ⊗[R p] κ)) ⟶ pullback (toBase p Γ hj) b := (pullbackSpecIso (R p) A κ).inv ≫ g' with hgq
  have hgqfst : gq ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := R p) (A := A) (B := κ))) ≫ ιInf p Γ hj := by
    rw [hgq, Category.assoc, hg'fst, ← Category.assoc, pullbackSpecIso_inv_fst]
  have hgqsnd : gq ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
      (R := R p) (A := A) (B := κ)).toRingHom) := by
    rw [hgq, Category.assoc, hg'snd, pullbackSpecIso_inv_snd]
    rfl
  set tw : Spec (CommRingCat.of (κ ⊗[R p] A)) ⟶ Spec (CommRingCat.of (A ⊗[R p] κ)) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm (R p) A κ).toAlgHom.toRingHom) with htw
  haveI : IsIso tw := by
    have e : tw = Spec.map ((Algebra.TensorProduct.comm (R p) A κ).toRingEquiv.toCommRingCatIso.hom) := rfl
    rw [e]
    infer_instance
  refine ⟨tw ≫ gq, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, hgqfst, ← Category.assoc, htw, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      comm_comp_includeLeftRingHom]
  · rw [Category.assoc, hgqsnd, htw, ← Spec.map_comp, ← CommRingCat.ofHom_comp, comm_comp_includeRight]
  · have hs2 : Function.Surjective (pullbackSpecIso (R p) A κ).inv.base := (pullbackSpecIso (R p) A κ).inv.homeomorph.surjective
    have hs3 : Function.Surjective tw.base := (asIso tw).hom.homeomorph.surjective
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs3, Set.image_univ, hgq,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hs2, Set.image_univ, hrange]

theorem isOpenImmersion_and_range_of_comp_eq
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p Γ hj))) ⟶ fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))).toRingHom) ≫ ιInf p Γ hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p Γ hj))))) :
    IsOpenImmersion c' ∧
      Set.range c'.base = ((pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) κ)))) ⁻¹ᵁ
        ((ιInf p Γ hj) ''ᵁ ⊤) : Set ↥(fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ))) := by
  obtain ⟨g, hg, hgfst, hgsnd, hrange⟩ := chartInf_baseChange p Γ hj κ
  have heq : c' = g := by
    apply pullback.hom_ext
    · rw [hc'fst, hgfst]
    · rw [hc'snd, hgsnd]
  subst heq
  exact ⟨hg, hrange⟩

end Chart

section Twist

variable {R κ O : Type*} [CommRing R] [CommRing κ] [CommRing O] [Algebra R κ] [Algebra R O]
  (ψ : κ ≃+* κ) (hψ : ψ.toRingHom.comp (algebraMap R κ) = algebraMap R κ)

def ψR : κ →ₐ[R] κ :=
  { ψ.toRingHom with commutes' := fun r => DFunLike.congr_fun hψ r }

theorem ψR_apply (a : κ) : ψR ψ hψ a = ψ a := rfl

abbrev twistAlg : κ ⊗[R] O →ₐ[R] κ ⊗[R] O := Algebra.TensorProduct.map (ψR ψ hψ) (AlgHom.id R O)

theorem twistAlg_comp_includeRight :
    (twistAlg (O := O) ψ hψ).toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom := by
  refine RingHom.ext fun b => ?_
  show Algebra.TensorProduct.map (ψR ψ hψ) (AlgHom.id R O) ((1 : κ) ⊗ₜ[R] b) = (1 : κ) ⊗ₜ[R] b
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem twistAlg_comp_includeLeftRingHom :
    (twistAlg (O := O) ψ hψ).toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O)) =
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O)).comp ψ.toRingHom := by
  refine RingHom.ext fun a => ?_
  show Algebra.TensorProduct.map (ψR ψ hψ) (AlgHom.id R O) (a ⊗ₜ[R] (1 : O)) = (ψ a) ⊗ₜ[R] (1 : O)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem map_le_twist_of_map_le (J : Ideal O) (w : PrimeSpectrum (κ ⊗[R] O))
    (h : Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)) J ≤ w.asIdeal) :
    Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)) J ≤
      (PrimeSpectrum.comap (twistAlg (O := O) ψ hψ).toRingHom w).asIdeal := by
  have e : Ideal.map (twistAlg (O := O) ψ hψ).toRingHom
      (Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom J) =
      Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom J := by
    rw [Ideal.map_map, twistAlg_comp_includeRight]
  rw [PrimeSpectrum.comap_asIdeal, ← Ideal.map_le_iff_le_comap]
  change Ideal.map (twistAlg (O := O) ψ hψ).toRingHom
      (Ideal.map (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom J) ≤ _
  rw [e]
  exact h

end Twist

section Red

variable (p : ℕ) [Fact p.Prime] (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

theorem coeffMap_injective {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := fun x y h => by
  ext k
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

theorem algebraMap_R_injective : Function.Injective (algebraMap (R p) ℚ) := Subtype.val_injective

theorem exists_lift (b : ↥(chartAlgInf p Γ hj)) :
    ∃ y : LaurentSeries (R p), coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) :=
  (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC Γ p (jAt Γ hj)
    (coe_jAt Γ hj)).2 b

theorem lift_unique {b : ↥(chartAlgInf p Γ hj)} {y y' : LaurentSeries (R p)}
    (hy : coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ))
    (hy' : coeffMap (algebraMap (R p) ℚ) y' = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) : y = y' :=
  coeffMap_injective _ (algebraMap_R_injective p) (hy.trans hy'.symm)

variable {κ : Type} [CommRing κ] (toκ : R p →+* κ)

def red : ↥(chartAlgInf p Γ hj) →+* LaurentSeries κ where
  toFun b := coeffMap toκ (exists_lift p Γ hj b).choose
  map_one' := by
    have h1 : (exists_lift p Γ hj 1).choose = 1 :=
      lift_unique p Γ hj (exists_lift p Γ hj 1).choose_spec (by rw [map_one]; simp)
    rw [h1, map_one]
  map_mul' b b' := by
    have h : (exists_lift p Γ hj (b * b')).choose = (exists_lift p Γ hj b).choose * (exists_lift p Γ hj b').choose :=
      lift_unique p Γ hj (exists_lift p Γ hj (b * b')).choose_spec
        (by rw [map_mul, (exists_lift p Γ hj b).choose_spec, (exists_lift p Γ hj b').choose_spec]; simp)
    rw [h, map_mul]
  map_zero' := by
    have h0 : (exists_lift p Γ hj 0).choose = 0 :=
      lift_unique p Γ hj (exists_lift p Γ hj 0).choose_spec (by rw [map_zero]; simp)
    rw [h0, map_zero]
  map_add' b b' := by
    have h : (exists_lift p Γ hj (b + b')).choose = (exists_lift p Γ hj b).choose + (exists_lift p Γ hj b').choose :=
      lift_unique p Γ hj (exists_lift p Γ hj (b + b')).choose_spec
        (by rw [map_add, (exists_lift p Γ hj b).choose_spec, (exists_lift p Γ hj b').choose_spec]; simp)
    rw [h, map_add]

theorem red_spec (b : ↥(chartAlgInf p Γ hj)) (y : LaurentSeries (R p))
    (hy : coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) :
    red p Γ hj toκ b = coeffMap toκ y := by
  show coeffMap toκ (exists_lift p Γ hj b).choose = coeffMap toκ y
  rw [lift_unique p Γ hj (exists_lift p Γ hj b).choose_spec hy]

end Red

section FibreMaps

variable {p : ℕ} [Fact p.Prime] {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (κ : Type) [CommRing κ]

theorem fibreMap_comp_fst {Γ Γ' : Subgroup SL(2, ℤ)}
    (φ : NeronModelInfra.SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) (toκ : R p →+* κ) :
    fibreMap φ toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ.1 := by
  unfold fibreMap
  rw [pullback.lift_fst]

theorem fibreMap_comp_snd {Γ Γ' : Subgroup SL(2, ℤ)}
    (φ : NeronModelInfra.SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) (toκ : R p →+* κ) :
    fibreMap φ toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  unfold fibreMap
  rw [pullback.lift_snd, Category.comp_id]

theorem fibreMap_comp_twist {Γ Γ' : Subgroup SL(2, ℤ)}
    (φ : NeronModelInfra.SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) (toκ : R p →+* κ) (ψ : κ →+* κ)
    (Ξ : fibre (Γ := Γ) (hj := hj) toκ ⟶ fibre (Γ := Γ) (hj := hj) toκ)
    (hΞ₁ : Ξ ≫ pullback.fst _ _ = pullback.fst _ _) (hΞ₂ : Ξ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ))
    (Ξ' : fibre (Γ := Γ') (hj := hj) toκ ⟶ fibre (Γ := Γ') (hj := hj) toκ)
    (hΞ'₁ : Ξ' ≫ pullback.fst _ _ = pullback.fst _ _) (hΞ'₂ : Ξ' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ)) :
    fibreMap φ toκ ≫ Ξ' = Ξ ≫ fibreMap φ toκ := by
  apply pullback.hom_ext
  · rw [Category.assoc, hΞ'₁, fibreMap_comp_fst, Category.assoc, fibreMap_comp_fst, ← Category.assoc, hΞ₁]
  · rw [Category.assoc, hΞ'₂, ← Category.assoc, fibreMap_comp_snd, Category.assoc, fibreMap_comp_snd, hΞ₂]

end FibreMaps

section Main

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

set_option maxHeartbeats 3200000 in
theorem baseTwist_mem_range_comp_zero
    (ψ : ResidueField ↥A ≃+* ResidueField ↥A)
    (hψ : ψ.toRingHom.comp ((IsLocalRing.residue ↥A).comp ρ) = (IsLocalRing.residue ↥A).comp ρ)
    (ΞM : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶
      (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hΞM₁ : ΞM ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞM₂ : ΞM ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom))
    (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hy0 : y ∈ Set.range (𝔛.comp A hA ρ hρ 0).base)
    (hy : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y ∈
      Set.range (ιInf p (ΓM M H) hj).base) :
    ΞM.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0).base := by
  classical
  letI instAlg : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  have halg : algebraMap (R p) (ResidueField ↥A) = (IsLocalRing.residue ↥A).comp ρ := rfl
  have hψ' : ψ.toRingHom.comp (algebraMap (R p) (ResidueField ↥A)) = algebraMap (R p) (ResidueField ↥A) := hψ

  obtain ⟨c', -, hc'fst, hc'snd, hc'range⟩ := chartInf_baseChange p (ΓM M H) hj (ResidueField ↥A)
  have hrd := red_spec p (ΓM M H) hj ((IsLocalRing.residue ↥A).comp ρ)
  have hcrit := fun w => 𝔛.mem_range_comp_zero_iff_map_ker_le A hA ρ hρ halg
    (red p (ΓM M H) hj ((IsLocalRing.residue ↥A).comp ρ)) hrd c' hc'fst hc'snd w

  obtain ⟨α, hα⟩ : ∃ α : (ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →+*
      (ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj), α = (twistAlg (O := ↥(chartAlgInf p (ΓM M H) hj)) ψ hψ').toRingHom :=
    ⟨_, rfl⟩
  have hαR : α.comp (Algebra.TensorProduct.includeRight (R := R p) (A := ResidueField ↥A)
      (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom = (Algebra.TensorProduct.includeRight (R := R p) (A := ResidueField ↥A)
      (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom := by
    rw [hα]; exact twistAlg_comp_includeRight ψ hψ'
  have hαL : α.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ResidueField ↥A)
      (B := ↥(chartAlgInf p (ΓM M H) hj))) = (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ResidueField ↥A)
      (B := ↥(chartAlgInf p (ΓM M H) hj))).comp ψ.toRingHom := by
    rw [hα]; exact twistAlg_comp_includeLeftRingHom ψ hψ'
  have hΞc : c' ≫ ΞM = Spec.map (CommRingCat.ofHom α) ≫ c' := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΞM₁, hc'fst, Category.assoc, hc'fst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hαR]
    · rw [Category.assoc, hΞM₂, ← Category.assoc, hc'snd, Category.assoc, hc'snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, hαL]

  have hyc : y ∈ Set.range c'.base := by
    rw [hc'range]
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, trivial, hx⟩
  obtain ⟨w, hw⟩ := hyc
  have hI := (hcrit w).mp (hw.symm ▸ hy0)
  have hI' := map_le_twist_of_map_le ψ hψ' (RingHom.ker (red p (ΓM M H) hj ((IsLocalRing.residue ↥A).comp ρ))) w hI
  rw [← hα] at hI'
  have hmem := (hcrit (PrimeSpectrum.comap α w)).mpr hI'
  have e : c'.base (PrimeSpectrum.comap α w) = ΞM.base (c'.base w) := by
    have := congrArg (fun f => f.base w) hΞc
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
    rw [this]
    rfl
  rw [← hw, ← e]
  exact hmem

end Main

end CompFrob

open CompFrob in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (ψ : ResidueField ↥A ≃+* ResidueField ↥A)
    (hψ : ψ.toRingHom.comp ((IsLocalRing.residue ↥A).comp ρ) = (IsLocalRing.residue ↥A).comp ρ)

    (ΞN : (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶
      (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hΞN₁ : ΞN ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞN₂ : ΞN ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom))
    (ΞM : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶
      (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hΞM₁ : ΞM ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞM₂ : ΞM ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom))

    (z : ↥(fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hz : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.comp A hA ρ hρ 0).base z) ∈ Set.range (ιInf p (ΓM M H) hj).base)
    (i : Fin 2) :
    (𝔛.comp A hA ρ hρ i).base (ΞN.base z) = ΞM.base ((𝔛.comp A hA ρ hρ i).base z) := by
  have key0 := CompFrob.baseTwist_mem_range_comp_zero 𝔛 A hA ρ hρ ψ hψ ΞM hΞM₁ hΞM₂ _ ⟨z, rfl⟩ hz
  obtain ⟨z', hz'⟩ := key0
  have hπΞ := fibreMap_comp_twist (ResidueField ↥A) 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) ψ.toRingHom ΞM hΞM₁ hΞM₂ ΞN hΞN₁ hΞN₂
  have hcp := 𝔛.comp_pi A hA ρ hρ
  have hz'eq : z' = ΞN.base z := by
    calc z' = (fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base ((𝔛.comp A hA ρ hρ 0).base z') := by
          rw [← Scheme.Hom.comp_apply, hcp]; rfl
      _ = (fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base (ΞM.base ((𝔛.comp A hA ρ hρ 0).base z)) := by rw [hz']
      _ = (ΞM ≫ fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base ((𝔛.comp A hA ρ hρ 0).base z) := by
          rw [Scheme.Hom.comp_apply]
      _ = (fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) ≫ ΞN).base ((𝔛.comp A hA ρ hρ 0).base z) := by rw [hπΞ]
      _ = ΞN.base ((𝔛.comp A hA ρ hρ 0 ≫ fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base z) := by
          rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      _ = ΞN.base z := by rw [hcp]; rfl
  have h0 : (𝔛.comp A hA ρ hρ 0).base (ΞN.base z) = ΞM.base ((𝔛.comp A hA ρ hρ 0).base z) := by rw [← hz'eq]; exact hz'
  obtain (hi | hi) : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · subst hi; exact h0
  · subst hi
    have hcw := 𝔛.comp_w A hA ρ hρ
    have hwΞ := fibreMap_comp_twist (ResidueField ↥A) (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ) ψ.toRingHom
      ΞM hΞM₁ hΞM₂ ΞM hΞM₁ hΞM₂
    calc (𝔛.comp A hA ρ hρ 1).base (ΞN.base z)
        = (𝔛.comp A hA ρ hρ 0 ≫ fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ)).base (ΞN.base z) := by
          rw [hcw]
      _ = (fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ)).base (ΞM.base ((𝔛.comp A hA ρ hρ 0).base z)) := by
          rw [Scheme.Hom.comp_apply, h0]
      _ = (ΞM ≫ fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ)).base ((𝔛.comp A hA ρ hρ 0).base z) := by
          rw [Scheme.Hom.comp_apply]
      _ = (fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ) ≫ ΞM).base ((𝔛.comp A hA ρ hρ 0).base z) := by
          rw [hwΞ]
      _ = ΞM.base ((𝔛.comp A hA ρ hρ 0 ≫ fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ)).base z) := by
          rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      _ = ΞM.base ((𝔛.comp A hA ρ hρ 1).base z) := by rw [hcw]

end
end S_ModularCurve_XHDRModelAtP_comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf (solution)
