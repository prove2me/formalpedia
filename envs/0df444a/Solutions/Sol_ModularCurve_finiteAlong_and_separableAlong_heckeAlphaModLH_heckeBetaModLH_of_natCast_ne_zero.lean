-- Prove2me | solution 1 for ModularCurve.finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d221ddc7-d127-575b-a310-df332bc99481

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_isSeparable_adjoin_qExpFunctionFieldC_gamma1
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_heckeBetaModLHDefined
import Theorems.Thm_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH_of_natCast_ne_zero
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped IntermediateField MatrixGroups

namespace SepLegsHGen

section Generic

variable {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A] [Algebra K B]
  (φ : A →ₐ[K] B) (a₀ : A)

def adjoinEquiv : K⟮a₀⟯ ≃ₐ[K] K⟮φ a₀⟯ :=
  (IntermediateField.equivMap K⟮a₀⟯ φ).trans
    (IntermediateField.equivOfEq (by rw [IntermediateField.adjoin_map, Set.image_singleton]))

theorem coe_adjoinEquiv_apply (r : K⟮a₀⟯) : ((adjoinEquiv φ a₀ r : K⟮φ a₀⟯) : B) = φ (r : A) := rfl

theorem isSeparable_adjoin_along (hsep : Algebra.IsSeparable K⟮φ a₀⟯ B) :
    letI : Algebra A B := AlgebraicCurve.algebraAlong φ
    Algebra.IsSeparable K⟮a₀⟯ B := by
  letI : Algebra A B := AlgebraicCurve.algebraAlong φ
  have he : (algebraMap K⟮a₀⟯ B).comp ((adjoinEquiv φ a₀).symm : K⟮φ a₀⟯ ≃+* K⟮a₀⟯).toRingHom
      = (RingEquiv.refl B).toRingHom.comp (algebraMap K⟮φ a₀⟯ B) := by
    ext r
    show φ ((((adjoinEquiv φ a₀).symm r : K⟮a₀⟯) : A)) = (r : B)
    rw [← coe_adjoinEquiv_apply φ a₀, AlgEquiv.apply_symm_apply]
  exact Algebra.IsSeparable.of_equiv_equiv ((adjoinEquiv φ a₀).symm : K⟮φ a₀⟯ ≃+* K⟮a₀⟯)
    (RingEquiv.refl B) he

theorem finite_adjoin_along (hfin : FiniteDimensional K⟮φ a₀⟯ B) :
    letI : Algebra A B := AlgebraicCurve.algebraAlong φ
    Module.Finite K⟮a₀⟯ B := by
  letI : Algebra A B := AlgebraicCurve.algebraAlong φ
  have he : (algebraMap K⟮a₀⟯ B).comp ((adjoinEquiv φ a₀).symm : K⟮φ a₀⟯ ≃+* K⟮a₀⟯).toRingHom
      = (RingEquiv.refl B).toRingHom.comp (algebraMap K⟮φ a₀⟯ B) := by
    ext r
    show φ ((((adjoinEquiv φ a₀).symm r : K⟮a₀⟯) : A)) = (r : B)
    rw [← coe_adjoinEquiv_apply φ a₀, AlgEquiv.apply_symm_apply]
  have hr := Algebra.finrank_eq_of_equiv_equiv ((adjoinEquiv φ a₀).symm : K⟮φ a₀⟯ ≃+* K⟮a₀⟯)
    (RingEquiv.refl B) he
  have hpos : 0 < Module.finrank K⟮φ a₀⟯ B := Module.finrank_pos
  exact Module.finite_of_finrank_pos (hr ▸ hpos)

theorem finiteAlong_and_separableAlong_of_adjoin_simple
    (hfin : FiniteDimensional K⟮φ a₀⟯ B) (hsep : Algebra.IsSeparable K⟮φ a₀⟯ B) :
    AlgebraicCurve.FiniteAlong K φ ∧ AlgebraicCurve.SeparableAlong K φ := by
  letI : Algebra A B := AlgebraicCurve.algebraAlong φ
  haveI := isSeparable_adjoin_along φ a₀ hsep
  haveI := finite_adjoin_along φ a₀ hfin
  exact ⟨Module.Finite.of_restrictScalars_finite K⟮a₀⟯ A B,
    Algebra.isSeparable_tower_top_of_isSeparable K⟮a₀⟯ A B⟩

variable {E : Type*} [Field E] [Algebra K E] {S S' : IntermediateField K E} (h : S ≤ S') (x : S)

theorem isSeparable_adjoin_of_le (hsep : Algebra.IsSeparable K⟮IntermediateField.inclusion h x⟯ S') :
    Algebra.IsSeparable K⟮x⟯ S := by
  letI : Algebra S S' := AlgebraicCurve.algebraAlong (IntermediateField.inclusion h)
  haveI := isSeparable_adjoin_along (IntermediateField.inclusion h) x hsep
  exact Algebra.IsSeparable.of_algHom K⟮x⟯ S' (IsScalarTower.toAlgHom K⟮x⟯ S S')

theorem finite_adjoin_of_le (hfin : FiniteDimensional K⟮IntermediateField.inclusion h x⟯ S') :
    FiniteDimensional K⟮x⟯ S := by
  letI : Algebra S S' := AlgebraicCurve.algebraAlong (IntermediateField.inclusion h)
  haveI := finite_adjoin_along (IntermediateField.inclusion h) x hfin
  exact Module.Finite.of_injective (IsScalarTower.toAlgHom K⟮x⟯ S S').toLinearMap
    (IntermediateField.inclusion h).injective

end Generic

section Modular

open ModularCurve CongruenceSubgroup

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
  (ℓ : ℕ) [NeZero ℓ]

theorem gamma1_mul_le : Gamma1 (N * ℓ) ≤ CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ) :=
  le_inf ((Gamma1_le_of_dvd (dvd_mul_right N ℓ)).trans (Gamma1_le_GammaH N H'))
    (Gamma1_in_Gamma0 _)

scoped instance : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩

scoped instance finiteIndex_top : (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)).FiniteIndex :=
  Subgroup.finiteIndex_of_le (gamma1_mul_le N H' ℓ)

theorem T_mem_top : ModularGroup.T ∈ CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ) :=
  gamma1_mul_le N H' ℓ (by simp [Gamma1_mem, ModularGroup.T])

def jb : qExpFunctionFieldC K (CohCarrier.GammaH N H') :=
  ⟨jqModC K, IntermediateField.subset_adjoin K _ (jqModC_mem_intFormRatiosC K _)⟩

@[scoped simp] theorem coe_jb : (jb K N H' : LaurentSeries K) = jqModC K := rfl

theorem top_le_gamma1 :
    qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) ≤ qExpFunctionFieldC K (Gamma1 (N * ℓ)) :=
  qExpFunctionFieldC_mono K (gamma1_mul_le N H' ℓ)

theorem alpha_leg :
    AlgebraicCurve.FiniteAlong K (heckeAlphaModLH K N H' ℓ) ∧
      AlgebraicCurve.SeparableAlong K (heckeAlphaModLH K N H' ℓ) := by

  set jt := heckeAlphaModLH K N H' ℓ (jb K N H') with hjt
  have hcoe : (jt : LaurentSeries K) = jqModC K := coe_heckeAlphaModLH K N H' ℓ _

  have hfin : FiniteDimensional K⟮jt⟯ (qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ))) :=
    (finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
      (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) (T_mem_top N H' ℓ) _ le_rfl
      (fun γ hγ => Or.inl hγ) jt hcoe).1

  have hsepT : Algebra.IsSeparable K⟮IntermediateField.inclusion (top_le_gamma1 K N H' ℓ) jt⟯
      (qExpFunctionFieldC K (Gamma1 (N * ℓ))) :=
    isSeparable_adjoin_qExpFunctionFieldC_gamma1 K (N * ℓ) _
      (by rw [IntermediateField.coe_inclusion, hcoe])
  have hsep : Algebra.IsSeparable K⟮jt⟯ (qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ))) :=
    isSeparable_adjoin_of_le (top_le_gamma1 K N H' ℓ) jt hsepT
  exact finiteAlong_and_separableAlong_of_adjoin_simple (heckeAlphaModLH K N H' ℓ) (jb K N H') hfin hsep

end Modular

section Transfer

variable {K B : Type*} [Field K] [Field B] [Algebra K B]

def extendScalarsRingEquiv {F C : IntermediateField K B} (h : F ≤ C) :
    C ≃+* IntermediateField.extendScalars h where
  toFun x := ⟨x.1, (IntermediateField.mem_extendScalars h).2 x.2⟩
  invFun x := ⟨x.1, (IntermediateField.mem_extendScalars h).1 x.2⟩
  left_inv x := rfl
  right_inv x := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_extendScalarsRingEquiv {F C : IntermediateField K B} (h : F ≤ C) (x : C) :
    ((extendScalarsRingEquiv h x : IntermediateField.extendScalars h) : B) = (x : B) := rfl

def adjoinValEquiv (C : IntermediateField K B) (x : C) : K⟮x⟯ ≃ₐ[K] K⟮(x : B)⟯ :=
  (adjoinEquiv (IntermediateField.val C) x).trans (IntermediateField.equivOfEq rfl)

theorem coe_adjoinValEquiv_apply (C : IntermediateField K B) (x : C) (r : K⟮x⟯) :
    ((adjoinValEquiv C x r : K⟮(x : B)⟯) : B) = ((r : C) : B) :=
  coe_adjoinEquiv_apply (IntermediateField.val C) x r

def adjoinAutEquiv {C : Type*} [Field C] [Algebra K C] (τ : C ≃ₐ[K] C) (x : C) : K⟮x⟯ ≃ₐ[K] K⟮τ x⟯ :=
  (adjoinEquiv (τ : C →ₐ[K] C) x).trans (IntermediateField.equivOfEq rfl)

theorem coe_adjoinAutEquiv_apply {C : Type*} [Field C] [Algebra K C] (τ : C ≃ₐ[K] C) (x : C) (r : K⟮x⟯) :
    ((adjoinAutEquiv τ x r : K⟮τ x⟯) : C) = τ (r : C) :=
  coe_adjoinEquiv_apply (τ : C →ₐ[K] C) x r

theorem finite_and_isSeparable_adjoin_sub (C : IntermediateField K B) (x : C)
    (hfin : FiniteDimensional K⟮(x : B)⟯ B) (hsep : Algebra.IsSeparable K⟮(x : B)⟯ B) :
    FiniteDimensional K⟮x⟯ C ∧ Algebra.IsSeparable K⟮x⟯ C := by
  have hle : K⟮(x : B)⟯ ≤ C := IntermediateField.adjoin_simple_le_iff.mpr x.2
  set CJ := IntermediateField.extendScalars hle with hCJ
  haveI : FiniteDimensional K⟮(x : B)⟯ CJ := IntermediateField.finiteDimensional_left CJ
  haveI : Algebra.IsSeparable K⟮(x : B)⟯ CJ := Algebra.isSeparable_tower_bot_of_isSeparable _ CJ B

  let e₁ : K⟮(x : B)⟯ ≃+* K⟮x⟯ := (adjoinValEquiv C x).symm.toRingEquiv
  let e₂ : CJ ≃+* C := (extendScalarsRingEquiv hle).symm
  have he : (algebraMap K⟮x⟯ C).comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K⟮(x : B)⟯ CJ) := by
    refine RingHom.ext fun r => Subtype.ext ?_
    show ((((adjoinValEquiv C x).symm r : K⟮x⟯) : C) : B) = (r : B)
    have h := coe_adjoinValEquiv_apply C x ((adjoinValEquiv C x).symm r)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · have hr := Algebra.finrank_eq_of_equiv_equiv e₁ e₂ he
    have hpos : 0 < Module.finrank K⟮(x : B)⟯ CJ := Module.finrank_pos
    exact Module.finite_of_finrank_pos (hr ▸ hpos)
  · exact Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he

theorem finite_and_isSeparable_adjoin_of_tower (C : IntermediateField K B) (x y : C)
    (hfin : FiniteDimensional K⟮(x : B)⟯ B) (hsep : Algebra.IsSeparable K⟮(x : B)⟯ B)
    (hfinC : FiniteDimensional K⟮y⟯ C) (hsepC : Algebra.IsSeparable K⟮y⟯ C) :
    FiniteDimensional K⟮(y : B)⟯ B ∧ Algebra.IsSeparable K⟮(y : B)⟯ B := by
  have hxle : K⟮(x : B)⟯ ≤ C := IntermediateField.adjoin_simple_le_iff.mpr x.2
  have hyle : K⟮(y : B)⟯ ≤ C := IntermediateField.adjoin_simple_le_iff.mpr y.2
  set CX := IntermediateField.extendScalars hxle with hCX
  set CY := IntermediateField.extendScalars hyle with hCY
  haveI := hfin
  haveI := hsep

  haveI hfX : Module.Finite CX B := Module.Finite.of_restrictScalars_finite K⟮(x : B)⟯ CX B
  haveI hsX : Algebra.IsSeparable CX B := Algebra.isSeparable_tower_top_of_isSeparable K⟮(x : B)⟯ CX B

  let i : CX ≃+* CY := (extendScalarsRingEquiv hxle).symm.trans (extendScalarsRingEquiv hyle)
  have hi : (algebraMap CY B).comp i.toRingHom = (RingEquiv.refl B).toRingHom.comp (algebraMap CX B) := by
    ext r
    rfl
  haveI hfY : Module.Finite CY B := Module.Finite.of_equiv_equiv i (RingEquiv.refl B) hi
  haveI hsY : Algebra.IsSeparable CY B := Algebra.IsSeparable.of_equiv_equiv i (RingEquiv.refl B) hi

  let e₁ : K⟮y⟯ ≃+* K⟮(y : B)⟯ := (adjoinValEquiv C y).toRingEquiv
  let e₂ : C ≃+* CY := extendScalarsRingEquiv hyle
  have he : (algebraMap K⟮(y : B)⟯ CY).comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K⟮y⟯ C) := by
    refine RingHom.ext fun r => Subtype.ext ?_
    exact coe_adjoinValEquiv_apply C y r
  haveI := hfinC
  haveI := hsepC
  haveI hfCY : Module.Finite K⟮(y : B)⟯ CY := Module.Finite.of_equiv_equiv e₁ e₂ he
  haveI hsCY : Algebra.IsSeparable K⟮(y : B)⟯ CY := Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he
  exact ⟨Module.Finite.trans CY B, Algebra.IsSeparable.trans K⟮(y : B)⟯ CY B⟩

theorem finite_and_isSeparable_adjoin_of_swap {C : Type*} [Field C] [Algebra K C] (τ : C ≃ₐ[K] C)
    (x y : C) (hτ : τ x = y)
    (hfin : FiniteDimensional K⟮x⟯ C) (hsep : Algebra.IsSeparable K⟮x⟯ C) :
    FiniteDimensional K⟮y⟯ C ∧ Algebra.IsSeparable K⟮y⟯ C := by
  subst hτ
  let e₁ : K⟮x⟯ ≃+* K⟮τ x⟯ := (adjoinAutEquiv τ x).toRingEquiv
  let e₂ : C ≃+* C := τ.toRingEquiv
  have he : (algebraMap K⟮τ x⟯ C).comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K⟮x⟯ C) :=
    RingHom.ext fun r => coe_adjoinAutEquiv_apply τ x r
  haveI := hfin
  haveI := hsep
  refine ⟨?_, Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he⟩
  have hr := Algebra.finrank_eq_of_equiv_equiv e₁ e₂ he
  have hpos : 0 < Module.finrank K⟮x⟯ C := Module.finrank_pos
  exact Module.finite_of_finrank_pos (hr ▸ hpos)

end Transfer

section Beta

open ModularCurve CongruenceSubgroup

variable (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
  (ℓ : ℕ) [NeZero ℓ]

abbrev Ft : IntermediateField K (LaurentSeries K) := qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ))

def jt : Ft K N H' ℓ := heckeAlphaModLH K N H' ℓ (jb K N H')
def yt : Ft K N H' ℓ := heckeBetaModLH K N H' ℓ (jb K N H')

theorem coe_jt : (jt K N H' ℓ : LaurentSeries K) = jqModC K := coe_heckeAlphaModLH K N H' ℓ _

theorem coe_yt : (yt K N H' ℓ : LaurentSeries K) = jqNModC K ℓ := by
  show (heckeBetaModLH K N H' ℓ (jb K N H') : LaurentSeries K) = qExpand K ℓ (jqModC K)
  rw [coe_heckeBetaModLH K N H' ℓ (heckeBetaModLHDefined K N H' ℓ), coe_jb]

def Cf : IntermediateField K (Ft K N H' ℓ) := K⟮jt K N H' ℓ, yt K N H' ℓ⟯

theorem jt_mem_Cf : jt K N H' ℓ ∈ Cf K N H' ℓ := IntermediateField.subset_adjoin K _ (Set.mem_insert _ _)
theorem yt_mem_Cf : yt K N H' ℓ ∈ Cf K N H' ℓ :=
  IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ rfl)

theorem map_Cf : (Cf K N H' ℓ).map (IntermediateField.val _) = modularFunctionFieldC K ℓ := by
  have h := IntermediateField.adjoin_map K ({jt K N H' ℓ, yt K N H' ℓ} : Set (Ft K N H' ℓ))
    (IntermediateField.val (Ft K N H' ℓ))
  rw [Set.image_pair] at h
  refine h.trans ?_
  show IntermediateField.adjoin K {((jt K N H' ℓ : Ft K N H' ℓ) : LaurentSeries K),
    ((yt K N H' ℓ : Ft K N H' ℓ) : LaurentSeries K)} = _
  rw [coe_jt, coe_yt]
  rfl

theorem exists_swap (hℓK : (ℓ : K) ≠ 0) :
    ∃ τ : Cf K N H' ℓ ≃ₐ[K] Cf K N H' ℓ, τ ⟨jt K N H' ℓ, jt_mem_Cf K N H' ℓ⟩ = ⟨yt K N H' ℓ, yt_mem_Cf K N H' ℓ⟩ := by

  obtain ⟨p, hp⟩ := CharP.exists K
  haveI := hp
  have hpℓ : ¬ p ∣ ℓ := by rwa [Ne, CharP.cast_eq_zero_iff K p] at hℓK
  have hfull : modularFunctionFieldC K ℓ = modularFunctionFieldFullC K ℓ :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC K p ℓ hpℓ

  let e : Cf K N H' ℓ ≃ₐ[K] modularFunctionFieldFullC K ℓ :=
    (IntermediateField.equivMap (Cf K N H' ℓ) (IntermediateField.val _)).trans
      (IntermediateField.equivOfEq ((map_Cf K N H' ℓ).trans hfull))
  have hcoe : ∀ z : Cf K N H' ℓ, ((e z : modularFunctionFieldFullC K ℓ) : LaurentSeries K) =
      ((z : Ft K N H' ℓ) : LaurentSeries K) := fun z => rfl
  obtain ⟨σ, hσ1, hσ2, -⟩ := exists_algEquiv_swap_jqModC_jqNModC_modularFunctionFieldFullC K ℓ hℓK
  refine ⟨e.trans (σ.trans e.symm), ?_⟩
  have hej : e ⟨jt K N H' ℓ, jt_mem_Cf K N H' ℓ⟩ = ⟨jqModC K, jqModC_mem_full K ℓ⟩ := by
    apply Subtype.ext
    rw [hcoe]
    exact coe_jt K N H' ℓ
  have hey : e ⟨yt K N H' ℓ, yt_mem_Cf K N H' ℓ⟩ = ⟨jqNModC K ℓ, jqModCd_mem_full K ℓ (dvd_refl ℓ)⟩ := by
    apply Subtype.ext
    rw [hcoe]
    exact coe_yt K N H' ℓ
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, hej, hσ1, ← hey, AlgEquiv.symm_apply_apply]

theorem beta_leg (hℓK : (ℓ : K) ≠ 0) :
    AlgebraicCurve.FiniteAlong K (heckeBetaModLH K N H' ℓ) ∧
      AlgebraicCurve.SeparableAlong K (heckeBetaModLH K N H' ℓ) := by

  have hcoe : ((jt K N H' ℓ : Ft K N H' ℓ) : LaurentSeries K) = jqModC K := coe_jt K N H' ℓ
  have hfin : FiniteDimensional K⟮jt K N H' ℓ⟯ (Ft K N H' ℓ) :=
    (finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
      (CohCarrier.GammaH N H' ⊓ Gamma0 (N * ℓ)) (T_mem_top N H' ℓ) _ le_rfl
      (fun γ hγ => Or.inl hγ) (jt K N H' ℓ) hcoe).1
  have hsepT : Algebra.IsSeparable K⟮IntermediateField.inclusion (top_le_gamma1 K N H' ℓ) (jt K N H' ℓ)⟯
      (qExpFunctionFieldC K (Gamma1 (N * ℓ))) :=
    isSeparable_adjoin_qExpFunctionFieldC_gamma1 K (N * ℓ) _
      (by rw [IntermediateField.coe_inclusion, hcoe])
  have hsep : Algebra.IsSeparable K⟮jt K N H' ℓ⟯ (Ft K N H' ℓ) :=
    isSeparable_adjoin_of_le (top_le_gamma1 K N H' ℓ) (jt K N H' ℓ) hsepT

  let xC : Cf K N H' ℓ := ⟨jt K N H' ℓ, jt_mem_Cf K N H' ℓ⟩
  let yC : Cf K N H' ℓ := ⟨yt K N H' ℓ, yt_mem_Cf K N H' ℓ⟩
  obtain ⟨hfinC, hsepC⟩ := finite_and_isSeparable_adjoin_sub (Cf K N H' ℓ) xC hfin hsep
  obtain ⟨τ, hτ⟩ := exists_swap K N H' ℓ hℓK
  obtain ⟨hfinC', hsepC'⟩ := finite_and_isSeparable_adjoin_of_swap τ xC yC hτ hfinC hsepC

  obtain ⟨hfinY, hsepY⟩ :=
    finite_and_isSeparable_adjoin_of_tower (Cf K N H' ℓ) xC yC hfin hsep hfinC' hsepC'

  exact finiteAlong_and_separableAlong_of_adjoin_simple (heckeBetaModLH K N H' ℓ) (jb K N H') hfinY hsepY

theorem main (hℓK : (ℓ : K) ≠ 0) :
    AlgebraicCurve.FiniteAlong K (heckeAlphaModLH K N H' ℓ) ∧
    AlgebraicCurve.FiniteAlong K (heckeBetaModLH K N H' ℓ) ∧
    AlgebraicCurve.SeparableAlong K (heckeAlphaModLH K N H' ℓ) ∧
    AlgebraicCurve.SeparableAlong K (heckeBetaModLH K N H' ℓ) :=
  ⟨(alpha_leg K N H' ℓ).1, (beta_leg K N H' ℓ hℓK).1, (alpha_leg K N H' ℓ).2, (beta_leg K N H' ℓ hℓK).2⟩

end Beta

end SepLegsHGen
p2m_reactivate "P2MW.S_ModularCurve_finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH_of_natCast_ne_zero.SepLegsHGen"

end
p2m_reactivate "P2MW.S_ModularCurve_finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH_of_natCast_ne_zero.SepLegsHGen"

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [NeZero ℓ] (hℓK : (ℓ : K) ≠ 0) :
    AlgebraicCurve.FiniteAlong K (ModularCurve.heckeAlphaModLH K N H' ℓ) ∧
    AlgebraicCurve.FiniteAlong K (ModularCurve.heckeBetaModLH K N H' ℓ) ∧
    AlgebraicCurve.SeparableAlong K (ModularCurve.heckeAlphaModLH K N H' ℓ) ∧
    AlgebraicCurve.SeparableAlong K (ModularCurve.heckeBetaModLH K N H' ℓ) :=
  SepLegsHGen.main K N H' ℓ hℓK

end S_ModularCurve_finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH_of_natCast_ne_zero
end P2MW
export P2MW.S_ModularCurve_finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH_of_natCast_ne_zero (solution)
