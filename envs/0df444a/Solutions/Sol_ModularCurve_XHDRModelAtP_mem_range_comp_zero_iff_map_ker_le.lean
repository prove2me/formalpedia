-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.mem_range_comp_zero_iff_map_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/33aad162-4ff6-5a15-964c-de9a03ff10ca

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Theorems.Thm_ModularCurve_XHDRLevel_map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf
import Theorems.Thm_ModularCurve_XHDRModelAtP_subsingleton_minimalPrimes_le_ker_cusp
import Theorems.Thm_ModularCurve_XHDRLevel_exists_retraction_chartInf_comp_zero_eq_of_dvd
import Theorems.Thm_AlgebraicCurve_CurveModel_infinite_place
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_mem_range_comp_zero_iff_map_ker_le
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

noncomputable section

namespace DictGlue

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

section Bundle

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj) (κ : Type) [CommRing κ] [Algebra (R p) κ]

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

theorem comp_fibreMap_pi_eq_spec_map_comp
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))) ⟶
      fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))))) :
    c' ≫ fibreMap 𝔓.π (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (R p) κ) 𝔓.iotaInf).toRingHom) ≫ c₀ := by
  apply pullback.hom_ext
  · rw [Category.assoc, fibreMap_comp_fst, ← Category.assoc, hc'fst, Category.assoc, 𝔓.pi_chartInf, ← Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, Category.assoc, hc₀fst, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, map_id_comp_includeRight]
  · rw [Category.assoc, fibreMap_comp_snd, hc'snd, Category.assoc, hc₀snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      map_id_comp_includeLeftRingHom]

theorem spec_map_comp_eq_sectionFibre_εinf
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (ev : κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[κ] κ)
    (hev : ∀ b : ↥(chartAlgInf p (ΓM M H) hj), ev ((1 : κ) ⊗ₜ[R p] b) = algebraMap (R p) κ (𝔓.rhoInf b)) :
    Spec.map (CommRingCat.ofHom ev.toRingHom) ≫ c' = sectionFibre 𝔓.εinf (algebraMap (R p) κ) := by
  have h1 : ev.toRingHom.comp (Algebra.TensorProduct.includeRight
      (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom =
      (algebraMap (R p) κ).comp 𝔓.rhoInf.toRingHom := by
    refine RingHom.ext fun b => ?_
    exact hev b
  have h2 : ev.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom
      (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))) = RingHom.id κ := by
    refine RingHom.ext fun a => ?_
    show ev (a ⊗ₜ[R p] (1 : ↥(chartAlgInf p (ΓM M H) hj))) = a
    exact ev.commutes a
  apply pullback.hom_ext
  · rw [Category.assoc, hc'fst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h1, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, ← 𝔓.εinf_chart, sectionFibre, pullback.lift_fst]
  · rw [Category.assoc, hc'snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h2, CommRingCat.ofHom_id, Spec.map_id,
      sectionFibre, pullback.lift_snd]

theorem base_spec_map_mem_range_sectionFibre_εinf
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (ev : κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[κ] κ)
    (hev : ∀ b : ↥(chartAlgInf p (ΓM M H) hj), ev ((1 : κ) ⊗ₜ[R p] b) = algebraMap (R p) κ (𝔓.rhoInf b))
    (x : ↥(Spec (CommRingCat.of κ))) :
    c'.base ((Spec.map (CommRingCat.ofHom ev.toRingHom)).base x) ∈
      Set.range (sectionFibre 𝔓.εinf (algebraMap (R p) κ)).base := by
  refine ⟨x, ?_⟩
  have := congrArg (fun f => f.base x) (spec_map_comp_eq_sectionFibre_εinf 𝔓 κ c' hc'fst hc'snd ev hev)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
  exact this.symm

end Bundle

end DictGlue

namespace DictGlue

section Reshapes

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj) (κ : Type) [CommRing κ] [Algebra (R p) κ]

theorem map_id_kappa_toRingHom_eq :
    (Algebra.TensorProduct.map (AlgHom.id κ κ) 𝔓.iotaInf).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id (R p) κ) 𝔓.iotaInf).toRingHom := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    show Algebra.TensorProduct.map (AlgHom.id κ κ) 𝔓.iotaInf (a ⊗ₜ b) =
      Algebra.TensorProduct.map (AlgHom.id (R p) κ) 𝔓.iotaInf (a ⊗ₜ b)
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy =>
    simp only [map_add]
    rw [show (Algebra.TensorProduct.map (AlgHom.id κ κ) 𝔓.iotaInf).toRingHom x =
        (Algebra.TensorProduct.map (AlgHom.id (R p) κ) 𝔓.iotaInf).toRingHom x from hx,
      show (Algebra.TensorProduct.map (AlgHom.id κ κ) 𝔓.iotaInf).toRingHom y =
        (Algebra.TensorProduct.map (AlgHom.id (R p) κ) 𝔓.iotaInf).toRingHom y from hy]

theorem comp_fibreMap_pi_eq_spec_map_kappa_comp
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (c₀ : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))) ⟶
      fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) κ))
    (hc₀fst : c₀ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom) ≫ ιInf p (ΓN p M H hpM) hj)
    (hc₀snd : c₀ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))))) :
    c' ≫ fibreMap 𝔓.π (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) 𝔓.iotaInf).toRingHom) ≫ c₀ := by
  rw [map_id_kappa_toRingHom_eq]
  exact comp_fibreMap_pi_eq_spec_map_comp 𝔓 κ c' hc'fst hc'snd c₀ hc₀fst hc₀snd

end Reshapes

section Point

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
  (𝔓 : XHDRModelAtP p M H hpM hj) (κ : Type) [Field κ] [Algebra (R p) κ]

theorem base_spec_map_eq_ker {A : Type} [CommRing A] (φ : A →+* κ) (x : ↥(Spec (CommRingCat.of κ))) :
    (Spec.map (CommRingCat.ofHom φ)).base x = ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ := by
  apply PrimeSpectrum.ext
  show Ideal.comap φ x.asIdeal = RingHom.ker φ
  have hx : x.asIdeal = ⊥ := by
    haveI : x.asIdeal.IsPrime := x.isPrime
    exact Ideal.eq_bot_of_prime (K := κ) x.asIdeal
  rw [hx]
  rfl

theorem ker_mem_range_sectionFibre_εinf
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (ev : κ ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[κ] κ)
    (hev : ∀ b : ↥(chartAlgInf p (ΓM M H) hj), ev ((1 : κ) ⊗ₜ[R p] b) = algebraMap (R p) κ (𝔓.rhoInf b)) :
    c'.base ⟨RingHom.ker ev.toRingHom, RingHom.ker_isPrime ev.toRingHom⟩ ∈
      Set.range (sectionFibre 𝔓.εinf (algebraMap (R p) κ)).base := by
  have h := base_spec_map_mem_range_sectionFibre_εinf 𝔓 κ c' hc'fst hc'snd ev hev (IsLocalRing.closedPoint κ)
  rwa [base_spec_map_eq_ker] at h

end Point

end DictGlue

end

set_option maxHeartbeats 12800000 in
theorem solution
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) (IsLocalRing.ResidueField ↥A)]
    (halg : algebraMap (R p) (IsLocalRing.ResidueField ↥A) = (IsLocalRing.residue ↥A).comp ρ)
    (red : ↥(chartAlgInf p (ΓM M H) hj) →+* LaurentSeries (IsLocalRing.ResidueField ↥A))
    (hred : ∀ (b : ↥(chartAlgInf p (ΓM M H) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
        red b = coeffMap ((IsLocalRing.residue ↥A).comp ρ) y)
    (c' : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
      fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgInf p (ΓM M H) hj)))))
    (z : ↥(Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))))) :
    c'.base z ∈ Set.range (𝔓.comp A hA ρ hρ 0).base ↔
      Ideal.map (Algebra.TensorProduct.includeRight :
          ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))
        (RingHom.ker red) ≤ z.asIdeal := by
  classical

  obtain rfl : ‹Algebra (R p) (IsLocalRing.ResidueField ↥A)› = ((IsLocalRing.residue ↥A).comp ρ).toAlgebra :=
    Algebra.algebra_ext _ _ (fun r => by
      rw [RingHom.algebraMap_toAlgebra]
      exact congrArg (fun φ : R p →+* (IsLocalRing.ResidueField ↥A) => φ r) halg)
  letI instκ : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  have halg' : algebraMap (R p) (IsLocalRing.ResidueField ↥A) = (IsLocalRing.residue ↥A).comp ρ := rfl

  let ev : (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj) →ₐ[(IsLocalRing.ResidueField ↥A)] (IsLocalRing.ResidueField ↥A) :=
    Algebra.TensorProduct.lift (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) ((Algebra.ofId (R p) (IsLocalRing.ResidueField ↥A)).comp 𝔓.rhoInf)
      (fun _ _ => Commute.all _ _)
  have hev2 : ∀ b : ↥(chartAlgInf p (ΓM M H) hj), ev (1 ⊗ₜ b) = algebraMap (R p) (IsLocalRing.ResidueField ↥A) (𝔓.rhoInf b) := by
    intro b
    simp only [ev, Algebra.TensorProduct.lift_tmul, map_one, one_mul, AlgHom.comp_apply, Algebra.ofId_apply]
  have hev1 : ∀ b : ↥(chartAlgInf p (ΓM M H) hj), ev (1 ⊗ₜ b) = (red b).coeff 0 := by
    intro b
    obtain ⟨y, hy⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
      (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt (ΓM M H) hj)).2 b
    rw [hev2, hred b y hy]
    have h0 : y.coeff 0 = 𝔓.rhoInf b := by
      apply Subtype.ext
      have e := congrArg (fun s : LaurentSeries ℚ => s.coeff 0) hy
      simp only [coeffMap_coeff] at e
      rw [𝔓.rhoInf_spec]
      exact e
    rw [coeffMap_coeff, h0]
    rfl

  obtain ⟨hP0min, hP0le⟩ :=
    ModularCurve.XHDRLevel.map_ker_mem_minimalPrimes_and_le_ker_of_chartAlgInf (ΓM M H) p hj (IsLocalRing.ResidueField ↥A) red hred ev hev1
  have huniq := ModularCurve.XHDRModelAtP.subsingleton_minimalPrimes_le_ker_cusp 𝔓 A hA ρ hρ halg' ev hev2

  have L2 : IsOpenImmersion c' ∧
      Set.range c'.base = ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (IsLocalRing.ResidueField ↥A))))) ⁻¹ᵁ
        ((ιInf p (ΓM M H) hj) ''ᵁ ⊤) : Set _) := by
    exact DictGlue.isOpenImmersion_and_range_of_comp_eq p (ΓM M H) hj (IsLocalRing.ResidueField ↥A) c' hc'fst hc'snd
  obtain ⟨c₀, hc₀open, hc₀fst, hc₀snd, hc₀range⟩ : ∃ c₀ : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))) ⟶
        fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) (IsLocalRing.ResidueField ↥A)),
      IsOpenImmersion c₀ ∧
      c₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj))).toRingHom) ≫ ιInf p (ΓN p M H hpM) hj ∧
      c₀ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓN p M H hpM) hj)))) ∧
      Set.range c₀.base = ((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (IsLocalRing.ResidueField ↥A))))) ⁻¹ᵁ
        ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤) : Set _) := by
    exact DictGlue.chartInf_baseChange p (ΓN p M H hpM) hj (IsLocalRing.ResidueField ↥A)
  have L3 : c' ≫ fibreMap 𝔓.π (algebraMap (R p) (IsLocalRing.ResidueField ↥A)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) 𝔓.iotaInf).toRingHom) ≫ c₀ := by
    exact DictGlue.comp_fibreMap_pi_eq_spec_map_kappa_comp 𝔓 (IsLocalRing.ResidueField ↥A) c' hc'fst hc'snd c₀ hc₀fst hc₀snd
  have L4 : c'.base ⟨RingHom.ker ev.toRingHom, RingHom.ker_isPrime ev.toRingHom⟩ ∈
      Set.range (𝔓.comp A hA ρ hρ 0).base := by
    exact 𝔓.εinf_mem_comp0 A hA ρ hρ (DictGlue.ker_mem_range_sectionFibre_εinf 𝔓 (IsLocalRing.ResidueField ↥A) c' hc'fst hc'snd ev hev2)

  obtain ⟨σ₀, hσret, hσc⟩ := ModularCurve.XHDRLevel.exists_retraction_chartInf_comp_zero_eq_of_dvd p M H hpM hj
    𝔓.π 𝔓.iotaInf 𝔓.iotaInf_spec 𝔓.pi_chartInf (IsLocalRing.ResidueField ↥A) c₀ hc₀fst hc₀snd c' hc'fst hc'snd
    (𝔓.comp A hA ρ hρ) (𝔓.comp_over A hA ρ hρ) (𝔓.comp_isClosedImmersion A hA ρ hρ) (𝔓.comp_pi A hA ρ hρ)
  have hσsurj : Function.Surjective σ₀ := fun w => ⟨_, hσret w⟩

  have key : ∀ w : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))),
      c'.base w ∈ Set.range (𝔓.comp A hA ρ hρ 0).base ↔ RingHom.ker σ₀.toRingHom ≤ w.asIdeal := by
    intro w
    constructor
    · rintro ⟨v, hv⟩

      have hv' : (fibreMap 𝔓.π (algebraMap (R p) (IsLocalRing.ResidueField ↥A))).base (c'.base w) = v := by
        rw [← hv]
        change ((𝔓.comp A hA ρ hρ 0) ≫ fibreMap 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base v = v
        rw [𝔓.comp_pi A hA ρ hρ]
        rfl

      have hw₀ : (fibreMap 𝔓.π (algebraMap (R p) (IsLocalRing.ResidueField ↥A))).base (c'.base w) =
          c₀.base ((Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) 𝔓.iotaInf).toRingHom)).base w) := by
        change (c' ≫ fibreMap 𝔓.π (algebraMap (R p) (IsLocalRing.ResidueField ↥A))).base w = _
        rw [L3]
        rfl

      have e1 : c'.base w = c'.base ((Spec.map (CommRingCat.ofHom σ₀.toRingHom)).base
          ((Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) 𝔓.iotaInf).toRingHom)).base w)) := by
        rw [← hv, ← hv', hw₀]
        change (c₀ ≫ 𝔓.comp A hA ρ hρ 0).base _ = (Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ c').base _
        rw [hσc]
      have e2 := L2.1.base_open.injective e1
      rw [e2]
      intro t ht
      rw [RingHom.mem_ker] at ht
      change t ∈ Ideal.comap σ₀.toRingHom _
      rw [Ideal.mem_comap, ht]
      exact Ideal.zero_mem _
    · intro hw

      have hmap : (Ideal.map σ₀.toRingHom w.asIdeal).IsPrime :=
        Ideal.map_isPrime_of_surjective hσsurj (by simp at hw; exact hw)
      refine ⟨c₀.base ⟨Ideal.map σ₀.toRingHom w.asIdeal, hmap⟩, ?_⟩
      rw [← Scheme.Hom.comp_apply, hσc, Scheme.Hom.comp_apply]
      congr 1
      apply PrimeSpectrum.ext
      change Ideal.comap σ₀.toRingHom (Ideal.map σ₀.toRingHom w.asIdeal) = w.asIdeal
      rw [Ideal.comap_map_of_surjective σ₀.toRingHom hσsurj, sup_eq_left]
      exact le_trans (Ideal.comap_mono bot_le) (by rw [← RingHom.ker_eq_comap_bot]; exact hw)

  have hkerle : RingHom.ker σ₀.toRingHom ≤ RingHom.ker ev.toRingHom := (key _).mp L4

  haveI hntN : Nontrivial ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj)) :=
    (ev.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) 𝔓.iotaInf).toRingHom).domain_nontrivial
  haveI := 𝔓.efib_iso A hA ρ hρ
  haveI hneFN : Nonempty (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) (IsLocalRing.ResidueField ↥A))) := ⟨(𝔓.efib A hA ρ hρ).base (Classical.arbitrary _)⟩
  haveI hintFN : IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) (IsLocalRing.ResidueField ↥A))) := isIntegral_of_isOpenImmersion (inv (𝔓.efib A hA ρ hρ))
  haveI hintSN : IsIntegral (Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj)))) := isIntegral_of_isOpenImmersion c₀
  haveI hdomN : IsDomain ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj)) :=
    MulEquiv.isDomain Γ(Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))), ⊤)
      (Scheme.ΓSpecIso (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj)))).symm.commRingCatIsoToRingEquiv.toMulEquiv
  have hkerprime : (RingHom.ker σ₀.toRingHom).IsPrime := RingHom.ker_isPrime σ₀.toRingHom

  have hkermin : RingHom.ker σ₀.toRingHom ∈ minimalPrimes ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj)) := by
    refine ⟨⟨hkerprime, bot_le⟩, ?_⟩
    rintro Q ⟨hQprime, -⟩ hQle
    let q : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) := ⟨Q, hQprime⟩
    rcases 𝔓.comp_jointly_surjective A hA ρ hρ (c'.base q) with h0 | h1
    · exact (key q).mp h0
    · exfalso
      let k : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) := ⟨RingHom.ker σ₀.toRingHom, hkerprime⟩
      have hqk : q ⤳ k := (PrimeSpectrum.le_iff_specializes q k).mp hQle
      have hck : c'.base k ∈ Set.range (𝔓.comp A hA ρ hρ 1).base :=
        (hqk.map c'.continuous).mem_closed (𝔓.comp_isClosedImmersion A hA ρ hρ 1).base_closed.isClosed_range h1

      let ξ : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))) := ⟨⊥, Ideal.bot_prime⟩
      have hk0 : c'.base k = (𝔓.comp A hA ρ hρ 0).base (c₀.base ξ) := by
        have e := congrArg (fun φ => φ.base ξ) hσc
        simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at e
        rw [e]
        rfl
      obtain ⟨y1, hy1⟩ := hck
      obtain ⟨n, hn1, -⟩ := Scheme.Pullback.exists_preimage_pullback (c₀.base ξ) y1 (by rw [← hk0, hy1])
      obtain ⟨-, ⟨hclosed, -⟩⟩ := 𝔓.node_pin A hA ρ hρ n
      rw [hn1] at hclosed

      have hξ : c₀.base ξ = genericPoint (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) (IsLocalRing.ResidueField ↥A))) := by
        rw [← genericPoint_eq_of_isOpenImmersion c₀, genericPoint_eq_bot_of_affine]
        rfl
      have hη : (inv (𝔓.efib A hA ρ hρ)).base (genericPoint (fibre (Γ := ΓN p M H hpM) (hj := hj) (algebraMap (R p) (IsLocalRing.ResidueField ↥A)))) = genericPoint (𝔓.Mfib A hA ρ hρ).C :=
        genericPoint_eq_of_isOpenImmersion _
      have hcl : IsClosed ({genericPoint (𝔓.Mfib A hA ρ hρ).C} : Set (𝔓.Mfib A hA ρ hρ).C) := by
        rw [← mem_closedPoints_iff, ← hη]
        convert hclosed using 2
        exact hξ.symm

      have hsub : ∀ x : (𝔓.Mfib A hA ρ hρ).C, x = genericPoint _ := fun x =>
        ((genericPoint_spec (𝔓.Mfib A hA ρ hρ).C).specializes (Set.mem_univ x)).mem_closed hcl rfl
      haveI : Subsingleton (closedPoints (𝔓.Mfib A hA ρ hρ).C) :=
        ⟨fun a b => Subtype.ext ((hsub a.1).trans (hsub b.1).symm)⟩
      haveI : Finite (Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) :=
        Finite.of_surjective _ (𝔓.Mfib A hA ρ hρ).placeOfPoint_bijective.2
      exact (AlgebraicCurve.CurveModel.infinite_place (𝔓.Mfib A hA ρ hρ)).not_finite this
  have hP0 : Ideal.map (Algebra.TensorProduct.includeRight :
      ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] (IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj)) (RingHom.ker red) = RingHom.ker σ₀.toRingHom :=
    huniq _ _ hP0min hkermin hP0le hkerle
  rw [key z, ← hP0]

#print axioms solution

end S_ModularCurve_XHDRModelAtP_mem_range_comp_zero_iff_map_ker_le
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_mem_range_comp_zero_iff_map_ker_le (solution)
