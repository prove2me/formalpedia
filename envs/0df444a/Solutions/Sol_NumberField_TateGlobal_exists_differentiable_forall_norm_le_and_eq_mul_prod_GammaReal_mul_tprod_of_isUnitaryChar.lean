-- Prove2me | solution 1 for NumberField.TateGlobal.exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/16592829-26e5-50ed-b56d-d654b5a34f8b

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Theorems.Thm_EisensteinGeneral_Factorization_inv_measure_adelicBox_mul_fourierIntegral_tensor_eq
import Theorems.Thm_LanglandsTunnell_ArchPlace_complexZeta_complexTestFun_complexCharFun_eq_pi_mul_GammaComplex
import Theorems.Thm_LanglandsTunnell_ArchPlace_forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun
import Theorems.Thm_LanglandsTunnell_ArchPlace_fourierIntegral_mixedSpace_pureTensor
import Theorems.Thm_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal
import Theorems.Thm_LanglandsTunnell_TateLocal_complexZeta_eq_localZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_of_unramified
import Theorems.Thm_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_eq_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_realZeta_eq_localZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_image_higherUnitsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_units_eq
import Theorems.Thm_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_indicator_coset_finiteAdeleRing_apply
import Theorems.Thm_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one
import Theorems.Thm_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Definitions.Def_LanglandsTunnell_ArchPlace
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_ArchParam
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_IntegralAdelicTrace
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

section ArchCharacterModulus

set_option autoImplicit false

namespace ArchCharacterModulus

private theorem re_eq_zero_of_forall_norm_realCharFun_eq_one (u : ℂ) (a : ZMod 2)
    (h : ∀ x : ℝˣ, ‖((LanglandsTunnell.ArchPlace.realCharFun u a x : ℂˣ) : ℂ)‖ = 1) : u.re = 0 := by
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsign : LanglandsTunnell.ArchPlace.realSign (Units.mk0 (Real.exp 1) hpos.ne') = 1 := by
    ext
    simp [LanglandsTunnell.ArchPlace.realSign, Real.norm_of_nonneg hpos.le]
  have hval : ((LanglandsTunnell.ArchPlace.realCharFun u a (Units.mk0 (Real.exp 1) hpos.ne') : ℂˣ) : ℂ) =
      ((Real.exp 1 : ℝ) : ℂ) ^ u := by
    show ((Units.mk0 ((‖((Units.mk0 (Real.exp 1) hpos.ne' : ℝˣ) : ℝ)‖ : ℂ) ^ u) _ *
        LanglandsTunnell.ArchPlace.realSign (Units.mk0 (Real.exp 1) hpos.ne') ^ (a.val : ℕ) : ℂˣ) : ℂ) = _
    rw [hsign, one_pow, mul_one, Units.val_mk0, Units.val_mk0, Real.norm_of_nonneg hpos.le]
  have hn := h (Units.mk0 (Real.exp 1) hpos.ne')
  rw [hval, Complex.norm_cpow_eq_rpow_re_of_pos hpos, Real.exp_one_rpow] at hn
  exact (Real.exp_eq_one_iff _).mp hn

private theorem re_eq_zero_of_forall_norm_complexCharFun_eq_one (u : ℂ) (k : ℤ)
    (h : ∀ z : ℂˣ, ‖((LanglandsTunnell.ArchPlace.complexCharFun u k z : ℂˣ) : ℂ)‖ = 1) : u.re = 0 := by
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hne : ((Real.exp 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  have hnorm : ‖((Units.mk0 (((Real.exp 1 : ℝ) : ℂ)) hne : ℂˣ) : ℂ)‖ = Real.exp 1 := by
    rw [Units.val_mk0, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  have hphase : LanglandsTunnell.ArchPlace.anglePhase (Units.mk0 (((Real.exp 1 : ℝ) : ℂ)) hne) = 1 := by
    rw [LanglandsTunnell.ArchPlace.anglePhase, hnorm, Units.val_mk0, div_self hne]
  have hn := h (Units.mk0 (((Real.exp 1 : ℝ) : ℂ)) hne)
  rw [LanglandsTunnell.ArchPlace.complexCharFun_apply, hphase, one_zpow, mul_one, hnorm,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos, Real.exp_one_rpow] at hn
  have h2 : (2 * u).re = 0 := (Real.exp_eq_one_iff _).mp hn
  have h2' : (2 * u).re = 2 * u.re := by simp [Complex.mul_re]
  linarith

end ArchCharacterModulus

end ArchCharacterModulus

section ArchCharacterTransportUnconditional

set_option autoImplicit false

open NumberField

namespace ArchCharacterTransport

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_of_continuous_val {X : Type} [TopologicalSpace X] (f : X → ℂˣ)
    (hf : Continuous fun x => ((f x : ℂˣ) : ℂ)) : Continuous f := by
  rw [Units.continuous_iff]
  refine ⟨hf, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact hf.inv₀ fun x => (f x).ne_zero

private theorem continuous_archUnitHom (w : InfinitePlace F) : Continuous (TateGlobal.archUnitHom (F := F) w) := by
  classical
  rw [Units.continuous_iff]
  constructor
  · show Continuous fun a : (w.Completion)ˣ =>
      ((Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion),
        (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F)
    exact (continuous_const.update w Units.continuous_val).prodMk continuous_const
  · show Continuous fun a : (w.Completion)ˣ =>
      ((Function.update (1 : InfiniteAdeleRing F) w (((a⁻¹ : (w.Completion)ˣ) : w.Completion)),
        (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F)
    exact (continuous_const.update w (Units.continuous_iff.mp continuous_id).2).prodMk continuous_const

private theorem continuous_unitsMap_of_continuous {K L : Type} [Monoid K] [Monoid L] [TopologicalSpace K]
    [TopologicalSpace L] (f : K →* L) (hf : Continuous f) : Continuous (Units.map f) := by
  rw [Units.continuous_iff]
  exact ⟨hf.comp Units.continuous_val,
    by simpa only [Units.coe_map_inv, Function.comp_def, id_eq] using hf.comp (Units.continuous_iff.mp (continuous_id (X := Kˣ))).2⟩

private theorem realCharFun_val_of_pos (u : ℂ) (a : ZMod 2) (y : ℝˣ) (hy : 0 < (y : ℝ)) :
    ((LanglandsTunnell.ArchPlace.realCharFun u a y : ℂˣ) : ℂ) = ((y : ℝ) : ℂ) ^ u := by
  have hsign : LanglandsTunnell.ArchPlace.realSign y = 1 := by
    ext
    simp [LanglandsTunnell.ArchPlace.realSign, Real.norm_of_nonneg hy.le]
  show ((Units.mk0 ((‖(y : ℝ)‖ : ℂ) ^ u) _ * LanglandsTunnell.ArchPlace.realSign y ^ (a.val : ℕ) : ℂˣ) : ℂ) = _
  rw [hsign, one_pow, mul_one, Units.val_mk0, Real.norm_of_nonneg hy.le]

private theorem complexCharFun_val_of_pos (u : ℂ) (k : ℤ) (z : ℂˣ) (r : ℝ) (hr : 0 < r) (hz : (z : ℂ) = r) :
    ((LanglandsTunnell.ArchPlace.complexCharFun u k z : ℂˣ) : ℂ) = (r : ℂ) ^ (2 * u) := by
  have hnorm : ‖(z : ℂ)‖ = r := by rw [hz, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hphase : LanglandsTunnell.ArchPlace.anglePhase z = 1 := by
    rw [LanglandsTunnell.ArchPlace.anglePhase, hnorm, hz, div_self (Complex.ofReal_ne_zero.mpr hr.ne')]
  rw [LanglandsTunnell.ArchPlace.complexCharFun_apply, hphase, one_zpow, mul_one, hnorm]

private theorem exists_re_eq_zero_and_forall_eq_realCharFun (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ))
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 F) F χ) {w : InfinitePlace F} (hw : w.IsReal) :
    ∃ (u : ℂ) (a : ZMod 2), u.re = 0 ∧ ∀ x : (w.Completion)ˣ,
      χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.realCharFun u a
        (Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).toMonoidHom x) := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he_def
  set ψ : ℝˣ →* ℂˣ := (TateGlobal.archLocalChar χ w).comp (Units.map e.symm.toRingHom.toMonoidHom) with hψ_def
  have hψc : Continuous ψ := by
    apply continuous_of_continuous_val
    refine hχc.comp ((continuous_archUnitHom w).comp (continuous_unitsMap_of_continuous _ ?_))
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous
  obtain ⟨u, a, hψ⟩ :=
    LanglandsTunnell.ArchPlace.forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun.1
      ψ hψc
  refine ⟨u, a, ?_, fun x => ?_⟩
  · apply ArchCharacterModulus.re_eq_zero_of_forall_norm_realCharFun_eq_one u a
    intro t
    rw [← hψ]
    exact hχu _
  · have hx : Units.map e.symm.toRingHom.toMonoidHom
        (Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).toMonoidHom x) = x := by
      ext
      exact e.symm_apply_apply (x : w.Completion)
    have h := DFunLike.congr_fun hψ
      (Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).toMonoidHom x)
    rw [hψ_def, MonoidHom.comp_apply, hx] at h
    exact h

private theorem exists_re_eq_zero_and_forall_eq_complexCharFun (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ))
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 F) F χ) {w : InfinitePlace F} (hw : w.IsComplex) :
    ∃ (u : ℂ) (k : ℤ), u.re = 0 ∧ ∀ x : (w.Completion)ˣ,
      χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.complexCharFun u k
        (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom x) := by
  set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw with he_def
  set ψ : ℂˣ →* ℂˣ := (TateGlobal.archLocalChar χ w).comp (Units.map e.symm.toRingHom.toMonoidHom) with hψ_def
  have hψc : Continuous ψ := by
    apply continuous_of_continuous_val
    refine hχc.comp ((continuous_archUnitHom w).comp (continuous_unitsMap_of_continuous _ ?_))
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous
  obtain ⟨u, k, hψ⟩ :=
    LanglandsTunnell.ArchPlace.forall_continuous_exists_eq_realCharFun_and_forall_continuous_exists_eq_complexCharFun.2
      ψ hψc
  refine ⟨u, k, ?_, fun x => ?_⟩
  · apply ArchCharacterModulus.re_eq_zero_of_forall_norm_complexCharFun_eq_one u k
    intro t
    rw [← hψ]
    exact hχu _
  · have hx : Units.map e.symm.toRingHom.toMonoidHom
        (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom x) = x := by
      ext
      exact e.symm_apply_apply (x : w.Completion)
    have h := DFunLike.congr_fun hψ (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom x)
    rw [hψ_def, MonoidHom.comp_apply, hx] at h
    exact h

private theorem archLocalChar_comp_eq_realCharFun (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {w : InfinitePlace F}
    (hw : w.IsReal) (u : ℂ) (a : ZMod 2)
    (h : ∀ x : (w.Completion)ˣ, χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.realCharFun u a
      (Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).toMonoidHom x)) :
    (TateGlobal.archLocalChar χ w).comp
        (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom) =
      LanglandsTunnell.ArchPlace.realCharFun u a := by
  ext t
  rw [MonoidHom.comp_apply, TateGlobal.archLocalChar, MonoidHom.comp_apply, h]
  congr 2
  ext
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal hw).apply_symm_apply (t : ℝ)

private theorem archLocalChar_comp_eq_complexCharFun (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {w : InfinitePlace F}
    (hw : w.IsComplex) (u : ℂ) (k : ℤ)
    (h : ∀ x : (w.Completion)ˣ, χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.complexCharFun u k
      (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom x)) :
    (TateGlobal.archLocalChar χ w).comp
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom.toMonoidHom) =
      LanglandsTunnell.ArchPlace.complexCharFun u k := by
  ext t
  rw [MonoidHom.comp_apply, TateGlobal.archLocalChar, MonoidHom.comp_apply, h]
  congr 2
  ext
  exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).apply_symm_apply (t : ℂ)

private theorem ofReal_extensionEmbeddingOfIsReal_cpow_eq (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {w : InfinitePlace F}
    (hw : w.IsReal) (u : ℂ) (a : ZMod 2)
    (h : ∀ x : (w.Completion)ˣ, χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.realCharFun u a
      (Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).toMonoidHom x))
    (x : (w.Completion)ˣ) (hx : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x : w.Completion)) :
    ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x : w.Completion) : ℝ) : ℂ) ^ u =
      ((χ (TateGlobal.archUnitHom w x) : ℂˣ) : ℂ) := by
  rw [h, realCharFun_val_of_pos u a _ hx]
  rfl

private theorem ofReal_cpow_two_mul_eq_of_extensionEmbedding_eq (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {w : InfinitePlace F} (_hw : w.IsComplex) (u : ℂ) (k : ℤ)
    (h : ∀ x : (w.Completion)ˣ, χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.complexCharFun u k
      (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom x))
    (x : (w.Completion)ˣ) (r : ℝ) (hr : 0 < r)
    (hx : InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) = (r : ℂ)) :
    (r : ℂ) ^ (2 * u) = ((χ (TateGlobal.archUnitHom w x) : ℂˣ) : ℂ) := by
  rw [h, complexCharFun_val_of_pos u k _ r hr hx]

private theorem forall_eq_realCharFun_of_archLocalChar_comp_eq (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {w : InfinitePlace F} (hw : w.IsReal) (u : ℂ) (a : ZMod 2)
    (H : (TateGlobal.archLocalChar χ w).comp
        (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom) =
      LanglandsTunnell.ArchPlace.realCharFun u a)
    (x : (w.Completion)ˣ) :
    χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.realCharFun u a
      (Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).toMonoidHom x) := by
  have h := DFunLike.congr_fun H
    (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom.toMonoidHom x)
  rw [MonoidHom.comp_apply, TateGlobal.archLocalChar, MonoidHom.comp_apply] at h
  have hx : Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom
      (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom.toMonoidHom x) = x := by
    ext
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm_apply_apply (x : w.Completion)
  rw [hx] at h
  rw [h]
  congr 2

private theorem forall_eq_complexCharFun_of_archLocalChar_comp_eq (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {w : InfinitePlace F} (hw : w.IsComplex) (u : ℂ) (k : ℤ)
    (H : (TateGlobal.archLocalChar χ w).comp
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom.toMonoidHom) =
      LanglandsTunnell.ArchPlace.complexCharFun u k)
    (x : (w.Completion)ˣ) :
    χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.complexCharFun u k
      (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom x) := by
  have h := DFunLike.congr_fun H
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toRingHom.toMonoidHom x)
  rw [MonoidHom.comp_apply, TateGlobal.archLocalChar, MonoidHom.comp_apply] at h
  have hx : Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom.toMonoidHom
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toRingHom.toMonoidHom x) = x := by
    ext
    exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm_apply_apply (x : w.Completion)
  rw [hx] at h
  rw [h]
  congr 2

private theorem ofReal_extensionEmbeddingOfIsReal_cpow_eq_of_archLocalChar_comp_eq (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {w : InfinitePlace F} (hw : w.IsReal) (u : ℂ) (a : ZMod 2)
    (H : (TateGlobal.archLocalChar χ w).comp
        (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom.toMonoidHom) =
      LanglandsTunnell.ArchPlace.realCharFun u a)
    (x : (w.Completion)ˣ) (hx : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x : w.Completion)) :
    ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (x : w.Completion) : ℝ) : ℂ) ^ u =
      ((χ (TateGlobal.archUnitHom w x) : ℂˣ) : ℂ) :=
  ofReal_extensionEmbeddingOfIsReal_cpow_eq χ hw u a
    (forall_eq_realCharFun_of_archLocalChar_comp_eq χ hw u a H) x hx

private theorem ofReal_cpow_two_mul_eq_of_archLocalChar_comp_eq (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    {w : InfinitePlace F} (hw : w.IsComplex) (u : ℂ) (k : ℤ)
    (H : (TateGlobal.archLocalChar χ w).comp
        (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom.toMonoidHom) =
      LanglandsTunnell.ArchPlace.complexCharFun u k)
    (x : (w.Completion)ˣ) (r : ℝ) (hr : 0 < r)
    (hx : InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) = (r : ℂ)) :
    (r : ℂ) ^ (2 * u) = ((χ (TateGlobal.archUnitHom w x) : ℂˣ) : ℂ) :=
  ofReal_cpow_two_mul_eq_of_extensionEmbedding_eq χ hw u k
    (forall_eq_complexCharFun_of_archLocalChar_comp_eq χ hw u k H) x r hr hx

end ArchCharacterTransport

end ArchCharacterTransportUnconditional

section CharacterDual

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox
open scoped Pointwise

noncomputable section

namespace CharacterDual

variable {F : Type} [Field F] [NumberField F]

private def characterDual (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {w | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}

private def localCharacterDual (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Set (v.adicCompletion F) :=
  {y | ∀ z ∈ v.adicCompletionIntegers F, ψ (0, AdelicDock.splice (𝓞 F) F v 0 (y * z)) = 1}

private theorem exists_units_smul_eq_of_forall (v : HeightOneSpectrum (𝓞 F)) {D : Set (v.adicCompletion F)}
    (h0 : ∃ y ∈ D, y ≠ 0) (hstab : ∀ y ∈ D, ∀ a ∈ v.adicCompletionIntegers F, a * y ∈ D)
    (hbdd : ∃ B : WithZero (Multiplicative ℤ), ∀ y ∈ D, Valued.v y ≤ B) :
    ∃ c : (v.adicCompletion F)ˣ,
      D = (c : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨y₀, hy₀, hy₀0⟩ := h0
  have hv0 : ∀ y : v.adicCompletion F, y ≠ 0 → Valued.v y ≠ 0 := fun y hy => (map_ne_zero _).mpr hy
  have hB0 : B ≠ 0 := by
    intro hB0
    have h := hB y₀ hy₀
    rw [hB0] at h
    exact hv0 y₀ hy₀0 (le_antisymm h zero_le')

  have hbound : ∀ y ∈ D, y ≠ 0 → WithZero.log (Valued.v y) ≤ WithZero.log B := by
    intro y hy hy0
    have h := hB y hy
    rwa [← WithZero.exp_log (hv0 y hy0), ← WithZero.exp_log hB0, WithZero.exp_le_exp] at h
  obtain ⟨n, ⟨c, hcD, hc0, hcn⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun n : ℤ => ∃ y ∈ D, y ≠ 0 ∧ WithZero.log (Valued.v y) = n)
    ⟨WithZero.log B, fun n ⟨y, hy, hy0, hyn⟩ => hyn ▸ hbound y hy hy0⟩ ⟨_, y₀, hy₀, hy₀0, rfl⟩
  refine ⟨Units.mk0 c hc0, Set.ext fun y => ⟨fun hy => ?_, ?_⟩⟩
  ·
    rw [Set.mem_smul_set]
    refine ⟨y / c, ?_, ?_⟩
    · rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
      refine (div_le_one₀ (zero_lt_iff.mpr (hv0 c hc0))).mpr ?_
      by_cases hy0 : y = 0
      · rw [hy0, map_zero]
        exact zero_le'
      have hle : WithZero.log (Valued.v y) ≤ WithZero.log (Valued.v c) := hcn ▸ hmax _ ⟨y, hy, hy0, rfl⟩
      rwa [← WithZero.exp_log (hv0 y hy0), ← WithZero.exp_log (hv0 c hc0), WithZero.exp_le_exp]
    · rw [Units.val_mk0, smul_eq_mul]
      field_simp
  ·
    rw [Set.mem_smul_set]
    rintro ⟨a, ha, rfl⟩
    rw [Units.val_mk0, smul_eq_mul, mul_comm]
    exact hstab c hcD a ha

private def evalAddHom (u : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →+ u.adicCompletion F where
  toFun x := x u
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem sub_apply (x a : FiniteAdeleRing (𝓞 F) F) (u : HeightOneSpectrum (𝓞 F)) :
    (x - a) u = x u - a u := rfl

private theorem sum_apply {ι : Type} (s : Finset ι) (f : ι → FiniteAdeleRing (𝓞 F) F) (u : HeightOneSpectrum (𝓞 F)) :
    (∑ i ∈ s, f i) u = ∑ i ∈ s, f i u :=
  map_sum (evalAddHom u) f s

private theorem psi_zero_add (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (a b : FiniteAdeleRing (𝓞 F) F) :
    ψ (0, a + b) = ψ (0, a) * ψ (0, b) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  show ((0 : InfiniteAdeleRing F), a + b) = (0 + 0, a + b)
  rw [add_zero]

private theorem psi_zero_sum_eq_one (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → FiniteAdeleRing (𝓞 F) F) (hf : ∀ i ∈ s, ψ (0, f i) = 1) : ψ (0, ∑ i ∈ s, f i) = 1 := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact AddChar.map_zero_eq_one ψ
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, psi_zero_add, hf i (Finset.mem_insert_self i s),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj), one_mul]

private theorem exists_finite_forall_apply_mem_of_subset {C : Set (FiniteAdeleRing (𝓞 F) F)}
    {s : Finset (FiniteAdeleRing (𝓞 F) F)}
    (hs : C ⊆ ⋃ a ∈ s, {x : FiniteAdeleRing (𝓞 F) F | x - a ∈ integralFiniteAdeles (𝓞 F) F}) :
    ∃ T : Set (HeightOneSpectrum (𝓞 F)), T.Finite ∧
      ∀ x ∈ C, ∀ u : HeightOneSpectrum (𝓞 F), u ∉ T → x u ∈ u.adicCompletionIntegers F := by
  refine ⟨⋃ a ∈ s, {u : HeightOneSpectrum (𝓞 F) | a u ∉ u.adicCompletionIntegers F},
    s.finite_toSet.biUnion fun a _ => Filter.eventually_cofinite.mp a.2, fun x hx u hu => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hs hx)
  have hau : a u ∈ u.adicCompletionIntegers F := by
    by_contra h
    exact hu (Set.mem_iUnion₂.mpr ⟨a, ha, h⟩)
  have hxu : x u = (x - a) u + a u := by rw [sub_apply, sub_add_cancel]
  rw [hxu]
  exact add_mem (hxa u) hau

private theorem exists_forall_valued_apply_le_of_subset {C : Set (FiniteAdeleRing (𝓞 F) F)}
    {s : Finset (FiniteAdeleRing (𝓞 F) F)}
    (hs : C ⊆ ⋃ a ∈ s, {x : FiniteAdeleRing (𝓞 F) F | x - a ∈ integralFiniteAdeles (𝓞 F) F})
    (u : HeightOneSpectrum (𝓞 F)) :
    ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ C, Valued.v (x u) ≤ B := by
  refine ⟨s.sup fun a => max (Valued.v (a u)) 1, fun x hx => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hs hx)
  have h1 : Valued.v ((x - a) u) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hxa u)
  calc Valued.v (x u) = Valued.v ((x - a) u + a u) := by rw [sub_apply, sub_add_cancel]
    _ ≤ max (Valued.v ((x - a) u)) (Valued.v (a u)) := Valuation.map_add _ _ _
    _ ≤ max (Valued.v (a u)) 1 := by
        rw [max_comm]
        exact max_le_max le_rfl h1
    _ ≤ s.sup fun a => max (Valued.v (a u)) 1 := Finset.le_sup (f := fun a => max (Valued.v (a u)) 1) ha

private theorem exists_finset_subset_iUnion_of_isCompact {C : Set (FiniteAdeleRing (𝓞 F) F)} (hC : IsCompact C) :
    ∃ s : Finset (FiniteAdeleRing (𝓞 F) F),
      C ⊆ ⋃ a ∈ s, {x : FiniteAdeleRing (𝓞 F) F | x - a ∈ integralFiniteAdeles (𝓞 F) F} := by
  refine hC.elim_finite_subcover
    (fun a : FiniteAdeleRing (𝓞 F) F => {x : FiniteAdeleRing (𝓞 F) F | x - a ∈ integralFiniteAdeles (𝓞 F) F})
    (fun _ => (isOpen_integralFiniteAdeles F).preimage (continuous_id.sub continuous_const)) fun x _ => ?_
  refine Set.mem_iUnion.mpr ⟨x, ?_⟩
  show x - x ∈ integralFiniteAdeles (𝓞 F) F
  rw [sub_self]
  exact fun u => zero_mem _

variable (v : HeightOneSpectrum (𝓞 F))

private theorem splice_zero_apply_of_ne (y : v.adicCompletion F) {u : HeightOneSpectrum (𝓞 F)} (hu : u ≠ v) :
    AdelicDock.splice (𝓞 F) F v 0 y u = 0 := by
  rw [AdelicDock.splice_apply_of_ne (𝓞 F) F v 0 y hu]
  rfl

private theorem splice_zero_mul (y : v.adicCompletion F) (z : FiniteAdeleRing (𝓞 F) F) :
    AdelicDock.splice (𝓞 F) F v 0 y * z = AdelicDock.splice (𝓞 F) F v 0 (y * z v) := by
  refine DFunLike.ext _ _ fun u => ?_
  show AdelicDock.splice (𝓞 F) F v 0 y u * z u = AdelicDock.splice (𝓞 F) F v 0 (y * z v) u
  by_cases hu : u = v
  · subst hu
    rw [AdelicDock.splice_apply_self, AdelicDock.splice_apply_self]
  · rw [splice_zero_apply_of_ne v y hu, splice_zero_apply_of_ne v _ hu, zero_mul]

private theorem mul_splice_zero (w : FiniteAdeleRing (𝓞 F) F) (z : v.adicCompletion F) :
    w * AdelicDock.splice (𝓞 F) F v 0 z = AdelicDock.splice (𝓞 F) F v 0 (w v * z) := by
  rw [mul_comm, splice_zero_mul, mul_comm]

private theorem splice_zero_mem_integralFiniteAdeles {y : v.adicCompletion F} (hy : y ∈ v.adicCompletionIntegers F) :
    AdelicDock.splice (𝓞 F) F v 0 y ∈ integralFiniteAdeles (𝓞 F) F := by
  intro u
  by_cases hu : u = v
  · subst hu
    rw [AdelicDock.splice_apply_self]
    exact hy
  · rw [splice_zero_apply_of_ne v y hu]
    exact zero_mem _

variable {v}

private theorem splice_zero_mem_characterDual {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {y : v.adicCompletion F}
    (hy : y ∈ localCharacterDual ψ v) : AdelicDock.splice (𝓞 F) F v 0 y ∈ characterDual ψ := by
  intro z hz
  rw [splice_zero_mul]
  exact hy (z v) (hz v)

private theorem apply_mem_localCharacterDual {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {w : FiniteAdeleRing (𝓞 F) F}
    (hw : w ∈ characterDual ψ) (v : HeightOneSpectrum (𝓞 F)) : w v ∈ localCharacterDual ψ v := by
  intro z hz
  rw [← mul_splice_zero]
  exact hw _ (splice_zero_mem_integralFiniteAdeles v hz)

private theorem mul_mem_localCharacterDual {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {y : v.adicCompletion F}
    (hy : y ∈ localCharacterDual ψ v) {a : v.adicCompletion F} (ha : a ∈ v.adicCompletionIntegers F) :
    a * y ∈ localCharacterDual ψ v := by
  intro z hz
  rw [mul_assoc, mul_comm a, mul_assoc]
  exact hy (z * a) (mul_mem hz ha)

private theorem exists_ne_zero_forall_psi_eq_one {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : Continuous ψ) :
    ∃ d : 𝓞 F, d ≠ 0 ∧
      ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) = 1 := by
  have hcont :
      Continuous (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) := by
    rw [AddChar.coe_compAddMonoidHom]
    exact hψ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨d, hd, hd1⟩ := exists_ne_zero_forall_addChar_mul_eq_one F hcont
  refine ⟨d, hd, fun z hz => ?_⟩
  have h := hd1 z hz
  rw [AddChar.coe_compAddMonoidHom, Function.comp_apply] at h
  exact h

private theorem psi_eq_one_of_forall_exists {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} {d : 𝓞 F}
    (hd : ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) = 1)
    (r : FiniteAdeleRing (𝓞 F) F)
    (hr : ∀ u : HeightOneSpectrum (𝓞 F), ∃ a ∈ u.adicCompletionIntegers F,
      r u = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) u * a) :
    ψ (0, r) = 1 := by
  let z : FiniteAdeleRing (𝓞 F) F :=
    ⟨fun u => Classical.choose (hr u), Filter.Eventually.of_forall fun u => (Classical.choose_spec (hr u)).1⟩
  have hz : z ∈ integralFiniteAdeles (𝓞 F) F := fun u => (Classical.choose_spec (hr u)).1
  have hrz : r = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z :=
    DFunLike.ext _ _ fun u => (Classical.choose_spec (hr u)).2
  rw [hrz]
  exact hd z hz

private theorem algebraMap_mul_algebraMap_inv {d : 𝓞 F} (hd : d ≠ 0) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) = 1 := by
  rw [← map_mul, mul_inv_cancel₀ (RingOfIntegers.coe_ne_zero_iff.mpr hd), map_one]

private theorem algebraMap_apply_mul_algebraMap_inv_apply {d : 𝓞 F} (hd : d ≠ 0) (u : HeightOneSpectrum (𝓞 F)) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) u * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) u = 1 := by
  show (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹)) u = 1
  rw [algebraMap_mul_algebraMap_inv hd]
  rfl

private theorem mem_characterDual_iff {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : Continuous ψ)
    (w : FiniteAdeleRing (𝓞 F) F) :
    w ∈ characterDual ψ ↔ ∀ v : HeightOneSpectrum (𝓞 F), w v ∈ localCharacterDual ψ v := by
  refine ⟨fun hw v => apply_mem_localCharacterDual hw v, fun hw z hz => ?_⟩
  classical
  obtain ⟨d, hd0, hd⟩ := exists_ne_zero_forall_psi_eq_one hψ

  have hfin : {u : HeightOneSpectrum (𝓞 F) | ¬ ((w * z) u ∈ u.adicCompletionIntegers F ∧
      algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) u ∈ u.adicCompletionIntegers F)}.Finite := by
    refine Set.Finite.subset ((Filter.eventually_cofinite.mp (w * z).2).union
      (Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹)).2)) fun u hu => ?_
    rw [Set.mem_setOf_eq, not_and_or] at hu
    exact hu
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ u, u ∈ T ↔ ¬ ((w * z) u ∈ u.adicCompletionIntegers F ∧
      algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) u ∈ u.adicCompletionIntegers F) :=
    ⟨hfin.toFinset, fun u => hfin.mem_toFinset⟩

  let r : FiniteAdeleRing (𝓞 F) F :=
    ⟨fun u => if u ∈ T then 0 else (w * z) u, (w * z).2.mono fun u hu => by
      beta_reduce
      split_ifs
      · exact zero_mem _
      · exact hu⟩
  have hr_apply : ∀ u, r u = if u ∈ T then 0 else (w * z) u := fun u => rfl
  have hsplit : w * z = (∑ u ∈ T, AdelicDock.splice (𝓞 F) F u 0 ((w * z) u)) + r := by
    refine DFunLike.ext _ _ fun u => ?_
    show (w * z) u = (∑ t ∈ T, AdelicDock.splice (𝓞 F) F t 0 ((w * z) t)) u + r u
    rw [sum_apply, hr_apply]
    by_cases hu : u ∈ T
    · rw [if_pos hu, add_zero, Finset.sum_eq_single u (fun t _ htu => splice_zero_apply_of_ne t _ htu.symm)
        (fun h => absurd hu h), AdelicDock.splice_apply_self]
    · rw [if_neg hu, Finset.sum_eq_zero fun t ht => splice_zero_apply_of_ne t _ fun h => hu (by rw [h]; exact ht),
        zero_add]
  have htail : ψ (0, r) = 1 := by
    refine psi_eq_one_of_forall_exists hd r fun u => ?_
    rw [hr_apply]
    by_cases hu : u ∈ T
    · exact ⟨0, zero_mem _, by rw [if_pos hu, mul_zero]⟩
    · have hu' := not_not.mp (fun h => hu ((hT u).mpr h))
      refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) u * (w * z) u, mul_mem hu'.2 hu'.1, ?_⟩
      rw [if_neg hu, ← mul_assoc, algebraMap_apply_mul_algebraMap_inv_apply hd0, one_mul]
  have hsum : ψ (0, ∑ u ∈ T, AdelicDock.splice (𝓞 F) F u 0 ((w * z) u)) = 1 :=
    psi_zero_sum_eq_one ψ T _ fun u _ => hw u (z u) (hz u)
  rw [hsplit, psi_zero_add, hsum, htail, one_mul]

private theorem exists_units_smul_eq_localCharacterDual {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : Continuous ψ)
    (hc : IsCompact (characterDual ψ)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ c : (v.adicCompletion F)ˣ,
      localCharacterDual ψ v = (c : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  obtain ⟨d, hd0, hd⟩ := exists_ne_zero_forall_psi_eq_one hψ
  refine exists_units_smul_eq_of_forall v ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) v, fun z hz => ?_, ?_⟩
    (fun y hy a ha => mul_mem_localCharacterDual hy ha) ?_
  ·
    refine psi_eq_one_of_forall_exists hd _ fun u => ?_
    by_cases hu : u = v
    · subst hu
      exact ⟨z, hz, by rw [AdelicDock.splice_apply_self]⟩
    · exact ⟨0, zero_mem _, by rw [splice_zero_apply_of_ne v _ hu, mul_zero]⟩
  ·
    rw [FiniteAdeleRing.algebraMap_apply]
    intro h
    have h' := congrArg Valued.v h
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_zero] at h'
    exact (map_ne_zero (v.valuation F)).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hd0) h'
  ·
    obtain ⟨s, hs⟩ := exists_finset_subset_iUnion_of_isCompact hc
    obtain ⟨B, hB⟩ := exists_forall_valued_apply_le_of_subset hs v
    refine ⟨B, fun y hy => ?_⟩
    have h := hB _ (splice_zero_mem_characterDual hy)
    rwa [AdelicDock.splice_apply_self] at h

private theorem exists_finset_forall_localCharacterDual_eq {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : Continuous ψ)
    (hc : IsCompact (characterDual ψ)) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ v : HeightOneSpectrum (𝓞 F), v ∉ T →
      localCharacterDual ψ v = (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_ne_zero_forall_psi_eq_one hψ
  obtain ⟨s, hs⟩ := exists_finset_subset_iUnion_of_isCompact hc
  obtain ⟨T₁, hT₁, hint⟩ := exists_finite_forall_apply_mem_of_subset hs
  have hT₂ := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹)).2
  refine ⟨(hT₁.union hT₂).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hv
  refine Set.ext fun y => ⟨fun hy => ?_, fun hy z hz => ?_⟩
  ·
    have h := hint _ (splice_zero_mem_characterDual hy) v hv.1
    rwa [AdelicDock.splice_apply_self] at h
  ·
    refine psi_eq_one_of_forall_exists hd _ fun u => ?_
    by_cases hu : u = v
    · subst hu
      refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) u * (y * z), mul_mem hv.2 (mul_mem hy hz), ?_⟩
      rw [AdelicDock.splice_apply_self, ← mul_assoc, algebraMap_apply_mul_algebraMap_inv_apply hd0, one_mul]
    · exact ⟨0, zero_mem _, by rw [splice_zero_apply_of_ne v _ hu, mul_zero]⟩

end CharacterDual

end

end CharacterDual

section TensorFactorization

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.TateGlobal IsDedekindDomain

noncomputable section

namespace TensorFactorization

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

private def mixedTensor (φr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (φc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) (y : mixedEmbedding.mixedSpace F) : ℂ :=
  (∏ w, φr w (y.1 w)) * ∏ w, φc w (y.2 w)

open scoped Classical in
private theorem mixedTensor_apply (φr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (φc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) (y : mixedEmbedding.mixedSpace F) :
    mixedTensor φr φc y = (∏ w, φr w (y.1 w)) * ∏ w, φc w (y.2 w) :=
  rfl

open scoped Classical in

private def finiteTensor (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (x : FiniteAdeleRing (𝓞 F) F) : ℂ :=
  (∏ v ∈ S, h v (x v)) *
    (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then 1 else 0)

open scoped Classical in
private theorem finiteTensor_apply (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (x : FiniteAdeleRing (𝓞 F) F) :
    finiteTensor S h x = (∏ v ∈ S, h v (x v)) *
      (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then 1 else 0) :=
  rfl

private def adelicTensor (φr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (φc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (x : AdeleRing (𝓞 F) F) : ℂ :=
  mixedTensor φr φc (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
    finiteTensor S h (x.2 : FiniteAdeleRing (𝓞 F) F)

private theorem adelicTensor_apply (φr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (φc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (x : AdeleRing (𝓞 F) F) :
    adelicTensor φr φc S h x
      = mixedTensor φr φc (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
          finiteTensor S h (x.2 : FiniteAdeleRing (𝓞 F) F) :=
  rfl

open scoped Classical in

private def placeFactor (φr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (φc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) (w : InfinitePlace F) : w.Completion → ℂ :=
  if hw : w.IsReal then φr ⟨w, hw⟩ ∘ Completion.ringEquivRealOfIsReal hw
  else φc ⟨w, not_isReal_iff_isComplex.1 hw⟩ ∘
    Completion.ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)

omit [NumberField F] in
open scoped Classical in
private theorem placeFactor_of_isReal (φr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (φc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) {w : InfinitePlace F} (hw : w.IsReal) :
    placeFactor φr φc w = φr ⟨w, hw⟩ ∘ Completion.ringEquivRealOfIsReal hw := by
  simp only [placeFactor, dif_pos hw]

omit [NumberField F] in
open scoped Classical in
private theorem placeFactor_of_isComplex (φr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (φc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) {w : InfinitePlace F} (hw : w.IsComplex) :
    placeFactor φr φc w = φc ⟨w, hw⟩ ∘ Completion.ringEquivComplexOfIsComplex hw := by
  have hw' : ¬ w.IsReal := not_isReal_iff_isComplex.2 hw
  simp only [placeFactor, dif_neg hw']

open scoped Classical in

private theorem prod_placeFactor (φr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (φc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) (x : InfiniteAdeleRing F) :
    ∏ w, placeFactor φr φc w (x w) = mixedTensor φr φc (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  simp only [mixedTensor_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)
    (fun w => placeFactor φr φc w (x w))]
  congr 1
  · refine Fintype.prod_congr _ _ fun v => ?_
    beta_reduce
    rw [placeFactor_of_isReal φr φc v.2]
    rfl
  · calc ∏ v : {w : InfinitePlace F // ¬ w.IsReal}, placeFactor φr φc v (x v)
        = ∏ v : {w : InfinitePlace F // ¬ w.IsReal},
            φc (Equiv.subtypeEquivRight (fun w : InfinitePlace F => not_isReal_iff_isComplex) v)
              (Completion.extensionEmbedding (v : InfinitePlace F) (x v)) :=
          Fintype.prod_congr _ _ fun v => by
            rw [placeFactor_of_isComplex φr φc (not_isReal_iff_isComplex.1 v.2)]
            rfl
      _ = ∏ u : {w : InfinitePlace F // w.IsComplex},
            φc u (Completion.extensionEmbedding (u : InfinitePlace F) (x u)) :=
          Equiv.prod_comp (Equiv.subtypeEquivRight fun w : InfinitePlace F => not_isReal_iff_isComplex)
            (fun u : {w : InfinitePlace F // w.IsComplex} =>
              φc u (Completion.extensionEmbedding (u : InfinitePlace F) (x u)))

open scoped Classical in

private theorem isFactorizableStandardOutside_adelicTensor (φr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (φc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) :
    IsFactorizableStandardOutside (adelicTensor φr φc S h) S (placeFactor φr φc) h := by
  intro x
  rw [adelicTensor_apply, finiteTensor_apply, ← prod_placeFactor]
  by_cases hx : x ∈ integralOutside S
  · have hx' : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
        (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := hx
    rw [Set.indicator_of_mem hx, if_pos hx', mul_one]
  · have hx' : ¬ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
        (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := fun h' => hx h'
    rw [Set.indicator_of_notMem hx, if_neg hx', mul_zero, mul_zero]

open scoped Classical in

private theorem isFactorizableStandardOutside_of_forall_eq (φr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ)
    (φc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (f : AdeleRing (𝓞 F) F → ℂ)
    (hf : ∀ x, f x = adelicTensor φr φc S h x) :
    IsFactorizableStandardOutside f S (placeFactor φr φc) h :=
  fun x => (hf x).trans (isFactorizableStandardOutside_adelicTensor φr φc S h x)

end TensorFactorization

end

end TensorFactorization

section CosetTensor

set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain TensorFactorization CharacterDual

namespace CosetTensor

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

private noncomputable def cosetIndicator (α : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) (v : HeightOneSpectrum (𝓞 F))
    (y : v.adicCompletion F) : ℂ :=
  if (u v : v.adicCompletion F)⁻¹ * (y - α v) ∈ v.adicCompletionIntegers F then 1 else 0

section Elements

variable (S : Finset (HeightOneSpectrum (𝓞 F))) (α : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
  (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)

private noncomputable def spliceOn : FiniteAdeleRing (𝓞 F) F :=
  ∑ v ∈ S, AdelicDock.splice (𝓞 F) F v 0 (α v)

private noncomputable def unitOn : FiniteAdeleRing (𝓞 F) F :=
  1 + ∑ v ∈ S, AdelicDock.splice (𝓞 F) F v 0 ((u v : v.adicCompletion F) - 1)

private noncomputable def unitInvOn : FiniteAdeleRing (𝓞 F) F :=
  1 + ∑ v ∈ S, AdelicDock.splice (𝓞 F) F v 0 (((u v)⁻¹ : (v.adicCompletion F)ˣ) - 1)

variable {S}

private theorem sum_splice_apply_of_mem (t : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    (∑ w ∈ S, AdelicDock.splice (𝓞 F) F w 0 (t w)) v = t v := by
  rw [CharacterDual.sum_apply,
    Finset.sum_eq_single v (fun w _ hw => CharacterDual.splice_zero_apply_of_ne w (t w) hw.symm)
      (fun h => (h hv).elim)]
  exact AdelicDock.splice_apply_self (𝓞 F) F v 0 (t v)

private theorem sum_splice_apply_of_not_mem (t : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    (∑ w ∈ S, AdelicDock.splice (𝓞 F) F w 0 (t w)) v = 0 := by
  rw [CharacterDual.sum_apply]
  exact Finset.sum_eq_zero fun w hw =>
    CharacterDual.splice_zero_apply_of_ne w (t w) (by rintro rfl; exact hv hw)

private theorem add_apply (a b : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : (a + b) v = a v + b v :=
  rfl

private theorem _root_.CosetTensor.mul_apply (a b : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) : (a * b) v = a v * b v :=
  rfl

p2m_export "CosetTensor" "mul_apply"
private theorem _root_.CosetTensor.one_apply (v : HeightOneSpectrum (𝓞 F)) : (1 : FiniteAdeleRing (𝓞 F) F) v = 1 :=
  rfl

p2m_export "CosetTensor" "one_apply"
private theorem spliceOn_apply_of_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : spliceOn S α v = α v :=
  sum_splice_apply_of_mem α hv

private theorem spliceOn_apply_of_not_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : spliceOn S α v = 0 :=
  sum_splice_apply_of_not_mem α hv

private theorem unitOn_apply_of_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : unitOn S u v = u v := by
  rw [unitOn, add_apply, one_apply, sum_splice_apply_of_mem (fun w => (u w : w.adicCompletion F) - 1) hv]
  ring

private theorem unitOn_apply_of_not_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : unitOn S u v = 1 := by
  rw [unitOn, add_apply, one_apply, sum_splice_apply_of_not_mem (fun w => (u w : w.adicCompletion F) - 1) hv,
    add_zero]

private theorem unitInvOn_apply_of_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    unitInvOn S u v = ((u v)⁻¹ : (v.adicCompletion F)ˣ) := by
  rw [unitInvOn, add_apply, one_apply,
    sum_splice_apply_of_mem (fun w => (((u w)⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) - 1) hv]
  ring

private theorem unitInvOn_apply_of_not_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : unitInvOn S u v = 1 := by
  rw [unitInvOn, add_apply, one_apply,
    sum_splice_apply_of_not_mem (fun w => (((u w)⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) - 1) hv,
    add_zero]

private theorem unitOn_mul_unitInvOn : unitOn S u * unitInvOn S u = 1 := by
  refine DFunLike.ext _ _ fun v => ?_
  rw [mul_apply, one_apply]
  by_cases hv : v ∈ S
  · rw [unitOn_apply_of_mem u hv, unitInvOn_apply_of_mem u hv]
    exact Units.mul_inv (u v)
  · rw [unitOn_apply_of_not_mem u hv, unitInvOn_apply_of_not_mem u hv, one_mul]

end Elements

section Identities

variable {S : Finset (HeightOneSpectrum (𝓞 F))} {α : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F}
  {u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ}

private theorem mem_coset_image_iff (x : FiniteAdeleRing (𝓞 F) F) :
    x ∈ (fun z => spliceOn S α + unitOn S u * z) '' integralFiniteAdeles (𝓞 F) F ↔
      (∀ v ∈ S, (u v : v.adicCompletion F)⁻¹ * (x v - α v) ∈ v.adicCompletionIntegers F) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [add_apply, mul_apply, spliceOn_apply_of_mem α hv, unitOn_apply_of_mem u hv, add_sub_cancel_left,
        ← mul_assoc, inv_mul_cancel₀ (u v).ne_zero, one_mul]
      exact hz v
    · rw [add_apply, mul_apply, spliceOn_apply_of_not_mem α hv, unitOn_apply_of_not_mem u hv, zero_add, one_mul]
      exact hz v
  · rintro ⟨hS, hS'⟩
    refine ⟨unitInvOn S u * (x - spliceOn S α), fun v => ?_, ?_⟩
    · rw [mul_apply, CharacterDual.sub_apply]
      by_cases hv : v ∈ S
      · rw [unitInvOn_apply_of_mem u hv, spliceOn_apply_of_mem α hv, Units.val_inv_eq_inv_val]
        exact hS v hv
      · rw [unitInvOn_apply_of_not_mem u hv, spliceOn_apply_of_not_mem α hv, one_mul, sub_zero]
        exact hS' v hv
    · show spliceOn S α + unitOn S u * (unitInvOn S u * (x - spliceOn S α)) = x
      rw [← mul_assoc, unitOn_mul_unitInvOn]
      ring

open scoped Classical in

private theorem finiteTensor_cosetIndicator_eq (S : Finset (HeightOneSpectrum (𝓞 F)))
    (α : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) :
    finiteTensor S (cosetIndicator α u) =
      ((fun z => spliceOn S α + unitOn S u * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1 := by
  funext x
  rw [Set.indicator_apply, finiteTensor_apply]
  simp only [cosetIndicator, Finset.prod_boole, Pi.one_apply]
  by_cases hx : x ∈ (fun z => spliceOn S α + unitOn S u * z) '' integralFiniteAdeles (𝓞 F) F
  · obtain ⟨h₁, h₂⟩ := (mem_coset_image_iff x).mp hx
    rw [if_pos hx, if_pos h₁, if_pos h₂, one_mul]
  · rw [if_neg hx]
    by_cases h₁ : ∀ v ∈ S, (u v : v.adicCompletion F)⁻¹ * (x v - α v) ∈ v.adicCompletionIntegers F
    · have h₂ : ¬ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F :=
        fun h₂ => hx ((mem_coset_image_iff x).mpr ⟨h₁, h₂⟩)
      rw [if_pos h₁, if_neg h₂, mul_zero]
    · rw [if_neg h₁, zero_mul]

private theorem splice_zero_neg (v : HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F) :
    -AdelicDock.splice (𝓞 F) F v 0 t = AdelicDock.splice (𝓞 F) F v 0 (-t) := by
  refine DFunLike.ext _ _ fun w => ?_
  show -(AdelicDock.splice (𝓞 F) F v 0 t w) = AdelicDock.splice (𝓞 F) F v 0 (-t) w
  by_cases hw : w = v
  · subst hw
    rw [AdelicDock.splice_apply_self, AdelicDock.splice_apply_self]
  · rw [CharacterDual.splice_zero_apply_of_ne v t hw, CharacterDual.splice_zero_apply_of_ne v (-t) hw, neg_zero]

private theorem psi_zero_finset_sum (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → FiniteAdeleRing (𝓞 F) F) : ψ (0, ∑ i ∈ s, f i) = ∏ i ∈ s, ψ (0, f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact AddChar.map_zero_eq_one ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, CharacterDual.psi_zero_add, ih]

private
theorem spliceOn_mul (S : Finset (HeightOneSpectrum (𝓞 F))) (α : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (w : FiniteAdeleRing (𝓞 F) F) :
    spliceOn S α * w = ∑ v ∈ S, AdelicDock.splice (𝓞 F) F v 0 (α v * w v) := by
  rw [spliceOn, Finset.sum_mul]
  exact Finset.sum_congr rfl fun v _ => CharacterDual.splice_zero_mul v (α v) w

open scoped Classical in

private theorem psi_neg_spliceOn_mul (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (α : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) (w : FiniteAdeleRing (𝓞 F) F) :
    ψ (0, -(spliceOn S α * w)) = ∏ v ∈ S, ψ (0, AdelicDock.splice (𝓞 F) F v 0 (-(α v * w v))) := by
  rw [spliceOn_mul, ← Finset.sum_neg_distrib, psi_zero_finset_sum]
  exact Finset.prod_congr rfl fun v _ => by rw [splice_zero_neg]

end Identities

end CosetTensor

end CosetTensor

section EulerSpellingBridge

set_option autoImplicit false

namespace EulerSpellingBridge

private theorem one_lt_absNorm (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    1 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast lt_of_lt_of_le one_lt_two h2

private theorem one_sub_mul_cpow_ne_zero (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : ℂ) (ha : ‖a‖ ≤ 1) (s : ℂ) (hs : 0 < s.re) :
    1 - a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
  have hN := one_lt_absNorm K v
  have hNpos : 0 < Ideal.absNorm v.asIdeal := by exact_mod_cast zero_lt_one.trans hN
  intro h0
  have h1 : a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) = 1 := (sub_eq_zero.1 h0).symm
  have h2 : ‖a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    have hlt : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hN (by linarith)
    have hnn : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [norm_nonneg a]
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

private theorem norm_prod_one_sub_mul_cpow_le (K : Type) [Field K] [NumberField K]
    (U : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
    (σ : ℝ) (s : ℂ) (hs : σ ≤ s.re) :
    ‖∏ v ∈ U, (1 - a v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))‖ ≤
      ∏ v ∈ U, (1 + ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_
  have hN := one_lt_absNorm K v
  have hNpos : 0 < Ideal.absNorm v.asIdeal := by exact_mod_cast zero_lt_one.trans hN
  have h1 : ‖a v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ ≤
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    have hnn : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hmono :
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
    nlinarith [ha v, norm_nonneg (a v)]
  calc ‖1 - a v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖
      ≤ ‖(1 : ℂ)‖ + ‖a v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ := norm_sub_le _ _
    _ ≤ 1 + ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by rw [norm_one]; linarith

private theorem euler_compare (K : Type) [Field K] [NumberField K]
    (χ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ →* ℂˣ)
    (hcf : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ‖((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ)‖ ≤ 1)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (b : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℂ) (hbS : ∀ v, v ∈ S → b v = 0)
    (hbS' : ∀ v, v ∉ S → b v = ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ))
    (s : ℂ) (hs : 1 < s.re) (Ls : ℂ)
    (hLs : Ls = ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ T},
          (1 - b v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    (∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S},
        (1 - ((χ (AutomorphicForm.uniformizerIdele K v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (-s)))⁻¹) =
      (∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) * Ls := by
  classical

  obtain ⟨g, hg_def⟩ : ∃ g : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℂ, g = fun v =>
      if v ∈ S then 1 else
        (1 - ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ :=
    ⟨_, rfl⟩
  have hg_mem : ∀ v, v ∈ S → g v = 1 := fun v hv => by rw [hg_def]; exact if_pos hv
  have hg_nmem : ∀ v, v ∉ S → g v =
      (1 - ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ :=
    fun v hv => by rw [hg_def]; exact if_neg hv

  have h1 : Ls = ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ T}, g v.1 := by
    rw [hLs]
    refine tprod_congr fun v => ?_
    by_cases hv : v.1 ∈ S
    · rw [hbS v.1 hv, hg_mem v.1 hv]
      simp
    · rw [hbS' v.1 hv, hg_nmem v.1 hv]

  have h2 : (∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S},
        (1 - ((χ (AutomorphicForm.uniformizerIdele K v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (-s)))⁻¹) =
      ∏' v, g v := by
    have h := tprod_subtype ((↑S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))ᶜ) (fun v =>
      (1 - ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    refine h.trans (tprod_congr fun v => ?_)
    rw [Set.mulIndicator_apply]
    by_cases hv : v ∈ S
    · rw [if_neg (by simpa using hv), hg_mem v hv]
    · rw [if_pos (by simpa using hv), hg_nmem v hv]

  have hR := fun (U : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (z : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ U} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) =>
    (NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K U z hz).1 s hs
  have hgm : Multipliable g := by
    have h := hR S (fun v => ((χ (AutomorphicForm.uniformizerIdele K v.1) : ℂˣ) : ℂ)) (fun v => hcf v.1)
    have h' : Multipliable
        (((↑S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))ᶜ).mulIndicator fun v =>
        (1 - ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^
            (-s)))⁻¹) :=
      multipliable_subtype_iff_mulIndicator.1 h
    refine h'.congr fun v => ?_
    rw [Set.mulIndicator_apply]
    by_cases hv : v ∈ S
    · rw [if_neg (by simpa using hv), hg_mem v hv]
    · rw [if_pos (by simpa using hv), hg_nmem v hv]
  have hgT : Multipliable
      fun v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ T} => g v.1 := by
    have h := hR T (fun v => b v.1)
      (fun v => by
        beta_reduce
        by_cases hv : v.1 ∈ S
        · rw [hbS v.1 hv, norm_zero]; exact zero_le_one
        · rw [hbS' v.1 hv]; exact hcf v.1)
    refine h.congr fun v => ?_
    beta_reduce
    by_cases hv : v.1 ∈ S
    · rw [hbS v.1 hv, hg_mem v.1 hv]
      simp
    · rw [hbS' v.1 hv, hg_nmem v.1 hv]

  have hsplit : (∏' v, g v) = (∏ v ∈ T, g v) *
      ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ T}, g v.1 :=
    hgm.hasProd.unique ((T.hasProd g).mul_compl hgT.hasProd)
  have hfin : (∏ v ∈ T, g v) = ∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : v ∈ S
    · rw [hg_mem v hv, hbS v hv]
      simp
    · rw [hg_nmem v hv, hbS' v hv]
  rw [h2, hsplit, hfin, ← h1]

private theorem euler_compare_empty (K : Type) [Field K] [NumberField K]
    (χ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ →* ℂˣ)
    (hcf : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ‖((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ)‖ ≤ 1)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (b : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℂ) (hbS : ∀ v, v ∈ S → b v = 0)
    (hbS' : ∀ v, v ∉ S → b v = ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ))
    (s : ℂ) (hs : 1 < s.re) (Ls : ℂ)
    (hLs : Ls = ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
        v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))},
          (1 - b v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    (∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S},
        (1 - ((χ (AutomorphicForm.uniformizerIdele K v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (-s)))⁻¹) =
      Ls := by
  have h := euler_compare K χ hcf S ∅ b hbS hbS' s hs Ls hLs
  rw [Finset.prod_empty, one_mul] at h
  exact h

end EulerSpellingBridge

end EulerSpellingBridge

section LocalZetaTransport

set_option autoImplicit false

open scoped NNReal ENNReal Pointwise
open MeasureTheory LanglandsTunnell.TateLocal

noncomputable section

namespace ZetaTransport

section Helpers

variable {K L : Type*} [Field K] [TopologicalSpace K] [Field L] [TopologicalSpace L]

private def homeomorphOfRingEquiv (φ : K ≃+* L) (hφ : Continuous φ) (hφs : Continuous φ.symm) : K ≃ₜ L :=
  { φ.toEquiv with continuous_toFun := hφ, continuous_invFun := hφs }

private theorem coe_homeomorphOfRingEquiv (φ : K ≃+* L) (hφ : Continuous φ) (hφs : Continuous φ.symm) :
    ⇑(homeomorphOfRingEquiv φ hφ hφs) = ⇑φ := rfl

omit [TopologicalSpace K] [TopologicalSpace L] in

private theorem preimage_smul_set (φ : K ≃+* L) (a : Kˣ) (t : Set L) :
    ⇑φ ⁻¹' ((Units.map φ.toRingHom.toMonoidHom a : Lˣ) • t) = a • (⇑φ ⁻¹' t) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨φ.symm y, ?_, ?_⟩
    · show φ (φ.symm y) ∈ t
      simpa using hy
    · apply φ.injective
      simp only [smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
      simpa [smul_eq_mul, Units.coe_map] using hxy
  · rintro ⟨y, hy, rfl⟩
    refine ⟨φ y, hy, ?_⟩
    simp [smul_eq_mul, Units.coe_map]

end Helpers

section Transport

variable {K L : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
  [Field L] [TopologicalSpace L] [IsTopologicalRing L] [LocallyCompactSpace L] [MeasurableSpace L] [BorelSpace L]

private theorem modulus_ringEquiv (φ : K ≃+* L) (hφ : Continuous φ) (hφs : Continuous φ.symm) (a : K) :
    modulus (φ a) = modulus a := by
  by_cases ha : a = 0
  · subst ha; simp [modulus_zero]
  have hφa : φ a ≠ 0 := by simpa using ha
  rw [modulus_of_ne_zero hφa, modulus_of_ne_zero ha]

  let e := homeomorphOfRingEquiv φ hφ hφs
  let em : K ≃ᵐ L := e.toMeasurableEquiv
  have hem : ⇑em = ⇑φ := rfl
  let μ : Measure K := Measure.addHaar
  let ν : Measure L := Measure.map em μ
  haveI : ν.IsAddHaarMeasure := by
    have h := AddEquiv.isAddHaarMeasure_map μ (φ : K ≃+ L) hφ hφs
    simpa [ν, hem] using h
  haveI : ν.Regular := Measure.Regular.map e

  obtain ⟨t, ht, ht0⟩ := exists_compact_mem_nhds (0 : L)
  have hνt0 : ν t ≠ 0 :=
    (Measure.measure_pos_of_nonempty_interior (μ := ν) ⟨0, mem_interior_iff_mem_nhds.2 ht0⟩).ne'
  have hνt : ν t ≠ ∞ := ht.measure_lt_top.ne

  have hunit : Units.map φ.toRingHom.toMonoidHom (Units.mk0 a ha) = Units.mk0 (φ a) hφa := by
    ext; rfl
  refine (distribHaarChar_eq_of_measure_smul_eq_mul (μ := ν) hνt0 hνt ?_)
  rw [← hunit]
  show (Measure.map em μ) ((Units.map φ.toRingHom.toMonoidHom (Units.mk0 a ha) : Lˣ) • t)
      = _ * (Measure.map em μ) t
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.map_apply, hem, preimage_smul_set]
  exact (distribHaarChar_mul μ (Units.mk0 a ha) (⇑φ ⁻¹' t)).symm

private theorem mulMeasure_map (φ : K ≃+* L) (hφ : Continuous φ) (hφs : Continuous φ.symm) (μ : Measure K) :
    mulMeasure (Measure.map φ μ) = Measure.map φ (mulMeasure μ) := by
  let e := homeomorphOfRingEquiv φ hφ hφs
  let em : K ≃ᵐ L := e.toMeasurableEquiv
  have hem : ⇑em = ⇑φ := rfl
  have hpre : ⇑φ ⁻¹' ({0}ᶜ : Set L) = {0}ᶜ := by
    ext x; simp
  ext S hS
  rw [← hem, MeasurableEquiv.map_apply, mulMeasure, mulMeasure, withDensity_apply _ hS,
    withDensity_apply _ (em.measurable hS), MeasurableEquiv.restrict_map, hem, hpre, ← hem,
    MeasurableEquiv.restrict_map, lintegral_map_equiv]
  refine lintegral_congr fun a => ?_
  rw [hem, modulus_ringEquiv φ hφ hφs]

private theorem localZeta_map_ringEquiv (φ : K ≃+* L) (hφ : Continuous φ) (hφs : Continuous φ.symm) (μ : Measure K)
    (g : L → ℂ) (χ : Lˣ →* ℂˣ) (s : ℂ) :
    localZeta (Measure.map φ μ) g χ s = localZeta μ (g ∘ φ) (χ.comp (Units.map φ.toRingHom.toMonoidHom)) s := by
  let e := homeomorphOfRingEquiv φ hφ hφs
  let em : K ≃ᵐ L := e.toMeasurableEquiv
  have hem : ⇑em = ⇑φ := rfl
  unfold localZeta
  rw [mulMeasure_map φ hφ hφs, ← hem, integral_map_equiv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hem, Function.comp_apply, modulus_ringEquiv φ hφ hφs]
  congr 2
  by_cases hy : y = 0
  · subst hy; simp [charExt_zero]
  · have hφy : φ y ≠ 0 := by simpa using hy
    rw [charExt_of_ne_zero _ hφy, charExt_of_ne_zero _ hy, MonoidHom.comp_apply]
    congr 2
    ext; rfl

end Transport

end ZetaTransport

end

end LocalZetaTransport

section ArchimedeanSlots

set_option autoImplicit false

open scoped NNReal ENNReal
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell.TateLocal

noncomputable section

namespace ZetaTransport

section Core

variable {F : Type} [Field F]

private theorem continuous_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) :
    Continuous (ringEquivRealOfIsReal hw) :=
  (isometryEquivRealOfIsReal hw).continuous

private theorem continuous_ringEquivRealOfIsReal_symm {w : InfinitePlace F} (hw : w.IsReal) :
    Continuous (ringEquivRealOfIsReal hw).symm :=
  (isometryEquivRealOfIsReal hw).symm.continuous

private theorem continuous_ringEquivComplexOfIsComplex {w : InfinitePlace F} (hw : w.IsComplex) :
    Continuous (ringEquivComplexOfIsComplex hw) :=
  (isometryEquivComplexOfIsComplex hw).continuous

private theorem continuous_ringEquivComplexOfIsComplex_symm {w : InfinitePlace F} (hw : w.IsComplex) :
    Continuous (ringEquivComplexOfIsComplex hw).symm :=
  (isometryEquivComplexOfIsComplex hw).symm.continuous

open scoped Classical in

private def archMeasure (w : InfinitePlace F) [MeasurableSpace w.Completion] [BorelSpace w.Completion] :
    Measure w.Completion :=
  if hw : w.IsReal then Measure.map (ringEquivRealOfIsReal hw).symm volume
  else Measure.map (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm ((2 : ℝ≥0∞) • volume)

private theorem archMeasure_of_isReal {w : InfinitePlace F} [MeasurableSpace w.Completion] [BorelSpace w.Completion]
    (hw : w.IsReal) : archMeasure w = Measure.map (ringEquivRealOfIsReal hw).symm volume := by
  classical exact dif_pos hw

private theorem archMeasure_of_isComplex {w : InfinitePlace F} [MeasurableSpace w.Completion] [BorelSpace w.Completion]
    (hw : w.IsComplex) :
    archMeasure w = Measure.map (ringEquivComplexOfIsComplex hw).symm ((2 : ℝ≥0∞) • volume) := by
  classical exact dif_neg (not_isReal_iff_isComplex.2 hw)

private
theorem isAddHaarMeasure_archMeasure (w : InfinitePlace F) [MeasurableSpace w.Completion] [BorelSpace w.Completion] :
    (archMeasure w).IsAddHaarMeasure := by
  by_cases hw : w.IsReal
  · rw [archMeasure_of_isReal hw]
    exact AddEquiv.isAddHaarMeasure_map _ ((ringEquivRealOfIsReal hw).symm : ℝ ≃+ w.Completion)
      (continuous_ringEquivRealOfIsReal_symm hw) (continuous_ringEquivRealOfIsReal hw)
  · have hw' := not_isReal_iff_isComplex.1 hw
    rw [archMeasure_of_isComplex hw']
    haveI : ((2 : ℝ≥0∞) • (volume : Measure ℂ)).IsAddHaarMeasure :=
      Measure.IsAddHaarMeasure.smul volume (by norm_num) (by norm_num)
    exact AddEquiv.isAddHaarMeasure_map _ ((ringEquivComplexOfIsComplex hw').symm : ℂ ≃+ w.Completion)
      (continuous_ringEquivComplexOfIsComplex_symm hw') (continuous_ringEquivComplexOfIsComplex hw')

private scoped instance instIsAddHaarMeasureArchMeasure (w : InfinitePlace F) [MeasurableSpace w.Completion]
    [BorelSpace w.Completion] : (archMeasure w).IsAddHaarMeasure :=
  isAddHaarMeasure_archMeasure w

private
theorem Gammaℂ_eq_Gammaℝ_mul_Gammaℝ_add_one (z : ℂ) : Complex.Gammaℂ z = Complex.Gammaℝ z * Complex.Gammaℝ (z + 1) :=
  (Complex.Gammaℝ_mul_Gammaℝ_add_one z).symm

end Core

section Slots

variable {F : Type} [Field F] [NumberField F]

private theorem localZeta_archMeasure_of_isReal (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {w : InfinitePlace F}
    [MeasurableSpace w.Completion] [BorelSpace w.Completion] (hw : w.IsReal) (u : ℂ) (a : ZMod 2)
    (h : ∀ x : (w.Completion)ˣ, χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.realCharFun u a
      (Units.map (extensionEmbeddingOfIsReal hw).toMonoidHom x))
    (f : ℝ → ℂ) (s : ℂ) :
    localZeta (archMeasure w) (f ∘ ringEquivRealOfIsReal hw) (TateGlobal.archLocalChar χ w) s
      = localZeta volume f (LanglandsTunnell.ArchPlace.realCharFun u a) s := by
  rw [archMeasure_of_isReal hw,
    localZeta_map_ringEquiv _ (continuous_ringEquivRealOfIsReal_symm hw)
      (by rw [RingEquiv.symm_symm]; exact continuous_ringEquivRealOfIsReal hw),
    ArchCharacterTransport.archLocalChar_comp_eq_realCharFun χ hw u a h]
  congr 1
  funext x
  simp

private theorem localZeta_archMeasure_of_isComplex (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {w : InfinitePlace F}
    [MeasurableSpace w.Completion] [BorelSpace w.Completion] (hw : w.IsComplex) (u : ℂ) (k : ℤ)
    (h : ∀ x : (w.Completion)ˣ, χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.complexCharFun u k
      (Units.map (extensionEmbedding w).toMonoidHom x))
    (f : ℂ → ℂ) (s : ℂ) :
    localZeta (archMeasure w) (f ∘ ringEquivComplexOfIsComplex hw) (TateGlobal.archLocalChar χ w) s
      = localZeta ((2 : ℝ≥0∞) • volume) f (LanglandsTunnell.ArchPlace.complexCharFun u k) s := by
  rw [archMeasure_of_isComplex hw,
    localZeta_map_ringEquiv _ (continuous_ringEquivComplexOfIsComplex_symm hw)
      (by rw [RingEquiv.symm_symm]; exact continuous_ringEquivComplexOfIsComplex hw),
    ArchCharacterTransport.archLocalChar_comp_eq_complexCharFun χ hw u k h]
  congr 1
  funext x
  simp

end Slots

section Values

private theorem localZeta_realTestFun_realCharFun (u : ℂ) (a : ZMod 2) (s : ℂ)
    (hs : 0 < (s + (u + LanglandsTunnell.signShift a)).re) :
    localZeta volume (LanglandsTunnell.ArchPlace.realTestFun a) (LanglandsTunnell.ArchPlace.realCharFun u a) s
      = Complex.Gammaℝ (s + (u + LanglandsTunnell.signShift a)) := by
  rw [← realZeta_eq_localZeta]
  exact LanglandsTunnell.ArchPlace.realZeta_realTestFun_realCharFun_eq_GammaReal u a s hs

private theorem localZeta_complexTestFun_complexCharFun (u : ℂ) (k : ℤ) (s : ℂ)
    (hs : 0 < (s + (u + (k.natAbs : ℂ) / 2)).re) :
    localZeta ((2 : ℝ≥0∞) • volume) (LanglandsTunnell.ArchPlace.complexTestFun k)
        (LanglandsTunnell.ArchPlace.complexCharFun u k) s
      = (Real.pi : ℂ) * Complex.Gammaℂ (s + (u + (k.natAbs : ℂ) / 2)) := by
  rw [← complexZeta_eq_localZeta]
  exact LanglandsTunnell.ArchPlace.complexZeta_complexTestFun_complexCharFun_eq_pi_mul_GammaComplex u k s hs

end Values

end ZetaTransport
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end ArchimedeanSlots
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section InverseCharacter

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell.ArchPlace

namespace InverseCharacter

section Regions

private theorem re_signShift_nonneg (a : ZMod 2) : 0 ≤ (LanglandsTunnell.signShift a).re := by
  unfold LanglandsTunnell.signShift
  split_ifs <;> simp

private theorem re_neg_eq_zero {u : ℂ} (hu : u.re = 0) : (-u).re = 0 := by
  rw [Complex.neg_re, hu, neg_zero]

private theorem re_add_signShift_pos {s u : ℂ} (hs : 1 < s.re) (hu : u.re = 0) (a : ZMod 2) :
    0 < (s + (u + LanglandsTunnell.signShift a)).re := by
  have ha := re_signShift_nonneg a
  simp only [Complex.add_re, hu]
  linarith

private theorem re_add_half_natAbs_pos {s u : ℂ} (hs : 1 < s.re) (hu : u.re = 0) (k : ℤ) :
    0 < (s + (u + (k.natAbs : ℂ) / 2)).re := by
  have hk : (0 : ℝ) ≤ (k.natAbs : ℝ) / 2 := by positivity
  simp only [Complex.add_re, hu, Complex.div_ofNat_re, Complex.natCast_re]
  linarith

end Regions
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section ArchimedeanInverse

private theorem realSign_mul_self (x : ℝˣ) : realSign x * realSign x = 1 := by
  have hx : (x : ℝ) / ‖(x : ℝ)‖ * ((x : ℝ) / ‖(x : ℝ)‖) = 1 := by
    rw [div_mul_div_comm, Real.norm_eq_abs, abs_mul_abs_self, div_self (mul_ne_zero x.ne_zero x.ne_zero)]
  ext
  simp only [realSign, Units.val_mul, Units.val_mk0, Units.val_one]
  exact_mod_cast hx

private theorem realCharFun_inv (u : ℂ) (a : ZMod 2) : (realCharFun u a)⁻¹ = realCharFun (-u) a := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.inv_apply]
  simp only [realCharFun, MonoidHom.coe_mk, OneHom.coe_mk, mul_inv]
  congr 1
  · ext
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, Complex.cpow_neg]
  · exact inv_eq_of_mul_eq_one_right (by rw [← mul_pow, realSign_mul_self, one_pow])

private theorem complexCharFun_inv (u : ℂ) (k : ℤ) : (complexCharFun u k)⁻¹ = complexCharFun (-u) (-k) := by
  refine MonoidHom.ext fun z => Units.ext ?_
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, complexCharFun_apply, complexCharFun_apply, mul_inv,
    mul_neg, Complex.cpow_neg, zpow_neg]

end ArchimedeanInverse
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section IdeleClassInverse

variable {F : Type} [Field F] [NumberField F]

private theorem localChar_inv (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) :
    NumberField.TateGlobal.localChar χ⁻¹ v = (NumberField.TateGlobal.localChar χ v)⁻¹ :=
  MonoidHom.ext fun _ => rfl

private theorem archLocalChar_inv (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (w : InfinitePlace F) :
    NumberField.TateGlobal.archLocalChar χ⁻¹ w = (NumberField.TateGlobal.archLocalChar χ w)⁻¹ :=
  MonoidHom.ext fun _ => rfl

private theorem isUnramifiedCharAt_inv {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 F)}
    (h : NumberField.TateGlobal.IsUnramifiedCharAt χ v) : NumberField.TateGlobal.IsUnramifiedCharAt χ⁻¹ v :=
  fun t ht ht' => by rw [localChar_inv, MonoidHom.inv_apply, h t ht ht', inv_one]

private theorem isUnitaryChar_inv {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (h : IsUnitaryChar (𝓞 F) F χ) :
    IsUnitaryChar (𝓞 F) F χ⁻¹ :=
  fun x => by rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]

private theorem continuous_inv_of_continuous {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (h : Continuous χ) : Continuous χ⁻¹ :=
  h.inv

private theorem inv_archUnitHom_eq_realCharFun (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (ur : {w : InfinitePlace F // w.IsReal} → ℂ) (ar : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (h : ∀ (i : {w : InfinitePlace F // w.IsReal}) (x : (i.1.Completion)ˣ),
      χ (NumberField.TateGlobal.archUnitHom i.1 x) =
        LanglandsTunnell.ArchPlace.realCharFun (ur i) (ar i)
          (Units.map
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal i.2).toMonoidHom x)) :
    ∀ (i : {w : InfinitePlace F // w.IsReal}) (x : (i.1.Completion)ˣ),
      χ⁻¹ (NumberField.TateGlobal.archUnitHom i.1 x) =
        LanglandsTunnell.ArchPlace.realCharFun (-ur i) (ar i)
          (Units.map
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal i.2).toMonoidHom x) :=
  fun i x => by rw [MonoidHom.inv_apply, h i x, ← realCharFun_inv, MonoidHom.inv_apply]

private theorem inv_archUnitHom_eq_complexCharFun (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (uc : {w : InfinitePlace F // w.IsComplex} → ℂ) (kc : {w : InfinitePlace F // w.IsComplex} → ℤ)
    (h : ∀ (j : {w : InfinitePlace F // w.IsComplex}) (z : (j.1.Completion)ˣ),
      χ (NumberField.TateGlobal.archUnitHom j.1 z) =
        LanglandsTunnell.ArchPlace.complexCharFun (uc j) (kc j)
          (Units.map
            (NumberField.InfinitePlace.Completion.extensionEmbedding j.1).toMonoidHom z)) :
    ∀ (j : {w : InfinitePlace F // w.IsComplex}) (z : (j.1.Completion)ˣ),
      χ⁻¹ (NumberField.TateGlobal.archUnitHom j.1 z) =
        LanglandsTunnell.ArchPlace.complexCharFun (-uc j) (-kc j)
          (Units.map
            (NumberField.InfinitePlace.Completion.extensionEmbedding j.1).toMonoidHom z) :=
  fun j z => by rw [MonoidHom.inv_apply, h j z, ← complexCharFun_inv, MonoidHom.inv_apply]

end IdeleClassInverse
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end InverseCharacter
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end InverseCharacter
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section ArchProduct

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory LanglandsTunnell.TateLocal TensorFactorization ZetaTransport
open NumberField.TateGlobal NumberField.InfinitePlace

namespace ArchProduct

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

private theorem prod_localZeta_archMeasure [∀ w : InfinitePlace F, MeasurableSpace w.Completion]
    [∀ w : InfinitePlace F, BorelSpace w.Completion] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (ur : {w : InfinitePlace F // w.IsReal} → ℂ) (ar : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (hreal : ∀ (i : {w : InfinitePlace F // w.IsReal}) (x : (i.1.Completion)ˣ),
      χ (NumberField.TateGlobal.archUnitHom i.1 x) = LanglandsTunnell.ArchPlace.realCharFun (ur i) (ar i)
        (Units.map (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal i.2).toMonoidHom x))
    (uc : {w : InfinitePlace F // w.IsComplex} → ℂ) (kc : {w : InfinitePlace F // w.IsComplex} → ℤ)
    (hcomplex : ∀ (j : {w : InfinitePlace F // w.IsComplex}) (z : (j.1.Completion)ˣ),
      χ (NumberField.TateGlobal.archUnitHom j.1 z) = LanglandsTunnell.ArchPlace.complexCharFun (uc j) (kc j)
        (Units.map (NumberField.InfinitePlace.Completion.extensionEmbedding j.1).toMonoidHom z))
    (hur : ∀ i, (ur i).re = 0) (huc : ∀ j, (uc j).re = 0) (s : ℂ) (hs : 1 < s.re) :
    ∏ w, localZeta (archMeasure w)
        (placeFactor (fun i => LanglandsTunnell.ArchPlace.realTestFun (ar i))
          (fun j => LanglandsTunnell.ArchPlace.complexTestFun (kc j)) w) (archLocalChar χ w) s
      = (∏ i : {w : InfinitePlace F // w.IsReal}, Complex.Gammaℝ (s + (ur i + LanglandsTunnell.signShift (ar i))))
        * ((Real.pi : ℂ) ^ Fintype.card {w : InfinitePlace F // w.IsComplex}
          * ∏ j : {w : InfinitePlace F // w.IsComplex}, Complex.Gammaℂ (s + (uc j + ((kc j).natAbs : ℂ) / 2))) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Fintype.prod_congr _ _ fun i => ?_
    beta_reduce
    rw [placeFactor_of_isReal _ _ i.2]
    exact (localZeta_archMeasure_of_isReal χ i.2 (ur i) (ar i) (hreal i) _ s).trans
      (localZeta_realTestFun_realCharFun _ _ _ (InverseCharacter.re_add_signShift_pos hs (hur i) _))
  · refine (Fintype.prod_equiv (Equiv.subtypeEquivRight fun w : InfinitePlace F => not_isReal_iff_isComplex) _
      (fun j : {w : InfinitePlace F // w.IsComplex} =>
        (Real.pi : ℂ) * Complex.Gammaℂ (s + (uc j + ((kc j).natAbs : ℂ) / 2))) fun v => ?_).trans ?_
    · beta_reduce
      rw [placeFactor_of_isComplex _ _ (not_isReal_iff_isComplex.1 v.2)]
      exact (localZeta_archMeasure_of_isComplex χ (not_isReal_iff_isComplex.1 v.2) _ _
        (hcomplex ((Equiv.subtypeEquivRight fun w : InfinitePlace F => not_isReal_iff_isComplex) v)) _ s).trans
        (localZeta_complexTestFun_complexCharFun _ _ _ (InverseCharacter.re_add_half_natAbs_pos hs (huc _) _))
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end ArchProduct
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end ArchProduct
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section LocalCharacterData

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm

namespace UnramifiedLocalData

variable {F : Type} [Field F] [NumberField F]

private theorem localChar_uniformizerUnit (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 F)) :
    localChar χ v (uniformizerUnit F v) = χ (uniformizerIdele F v) :=
  localChar_apply χ v (uniformizerUnit F v)

private theorem valued_uniformizerUnit_eq_ofAdd_neg_one (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (uniformizerUnit F v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) :=
  valued_uniformizerUnit F v

private theorem localChar_eq_one_of_valued_eq_one {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 F)}
    (hχ : IsUnramifiedCharAt χ v) (u : (v.adicCompletion F)ˣ) (hu : Valued.v (u : v.adicCompletion F) = 1) :
    localChar χ v u = 1 := by
  have hinv : Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  refine hχ u ?_ ?_
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hu.le
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hinv.le

private theorem isUnitaryChar_mul_inv {μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 F) F μ)
    (hν : IsUnitaryChar (𝓞 F) F ν) : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := by
  intro x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, hμ x,
    hν x, inv_one, mul_one]

private theorem continuous_of_continuous_coe (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχ : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((χ x : ℂˣ) : ℂ)) : Continuous χ := by
  refine Units.continuous_iff.mpr ⟨hχ, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact hχ.inv₀ fun x => (χ x).ne_zero

private theorem continuous_mul_inv_of_continuous_coe (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hν : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ)) : Continuous (μ * ν⁻¹) := by
  refine continuous_of_continuous_coe (μ * ν⁻¹) ?_
  have hfun : (fun x : (AdeleRing (𝓞 F) F)ˣ => (((μ * ν⁻¹) x : ℂˣ) : ℂ)) =
      fun x => ((μ x : ℂˣ) : ℂ) * (((ν x : ℂˣ) : ℂ))⁻¹ := by
    funext x
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hfun]
  exact hμ.mul (hν.inv₀ fun x => (ν x).ne_zero)

private theorem norm_localChar_eq_one {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχ : IsUnitaryChar (𝓞 F) F χ)
    (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) : ‖((localChar χ v t : ℂˣ) : ℂ)‖ = 1 := by
  rw [localChar_apply]
  exact hχ _

open scoped Classical in

private theorem localData (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, IsUnramifiedCharAt χ v) :
    (∀ v ∉ S, Valued.v (uniformizerUnit F v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
      (∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → localChar χ v u = 1) ∧
      (∀ v ∉ S, ‖((localChar χ v (uniformizerUnit F v) : ℂˣ) : ℂ)‖ ≤ 1) ∧
      ∀ v ∉ S, ((localChar χ v (uniformizerUnit F v) : ℂˣ) : ℂ) =
        (if NumberField.TateGlobal.IsUnramifiedCharAt χ v then
          ((χ (AutomorphicForm.uniformizerIdele F v) : ℂˣ) : ℂ) else 0) := by
  refine ⟨fun v _ => valued_uniformizerUnit_eq_ofAdd_neg_one v,
    fun v hv u hu => localChar_eq_one_of_valued_eq_one (hS v hv) u hu,
    fun v _ => le_of_eq (norm_localChar_eq_one hχu v _), fun v hv => ?_⟩
  rw [if_pos (hS v hv), localChar_uniformizerUnit]

end UnramifiedLocalData
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end LocalCharacterData
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section ConductorCoset

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.TateLocal

namespace ConductorCoset

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem valued_pow_of_valued_eq {ϖ : (v.adicCompletion K)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) (n : ℕ) :
    Valued.v ((ϖ ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-(n : ℤ)) := by
  rw [Units.val_pow_eq_pow_val, map_pow, hϖ]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    rw [neg_add, WithZero.exp_add]
    rfl

private theorem inv_mul_sub_one_mem_iff {ϖ : (v.adicCompletion K)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)) {n : ℕ} (hn : n ≠ 0)
    (y : v.adicCompletion K) :
    ((ϖ ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ * (y - 1) ∈ v.adicCompletionIntegers K ↔
      y ∈ ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' LanglandsTunnell.TateLocal.higherUnitsAt K v n := by
  have hpow := valued_pow_of_valued_eq hϖ n
  have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-(n : ℤ)) := WithZero.zero_lt_coe _
  have hlt1 : WithZero.exp (-(n : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have key : ((ϖ ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K)⁻¹ * (y - 1) ∈ v.adicCompletionIntegers K ↔
      Valued.v (y - 1) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hpow, inv_mul_le_iff₀ hpos, mul_one]
  rw [key]
  constructor
  · intro hy
    have hy1 : Valued.v y = 1 := by
      have : y = 1 + (y - 1) := by ring
      rw [this]
      exact Valuation.map_one_add_of_lt _ (hy.trans_lt hlt1)
    have hy0 : y ≠ 0 := fun h => by simp [h] at hy1
    exact ⟨Units.mk0 y hy0, ⟨hy1, Or.inr hy⟩, rfl⟩
  · rintro ⟨u, ⟨-, hu⟩, rfl⟩
    exact hu.resolve_left hn

private theorem isUnramifiedCharAt_of_hasConductorExponentAt_zero {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    (h : HasConductorExponentAt K v (localChar χ v) 0) : IsUnramifiedCharAt χ v := by
  intro t ht hti
  refine (hasConductorExponentAt_zero_iff K v).1 h t (le_antisymm ht ?_)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀] at hti
  exact (inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 t.ne_zero))).1 hti

private theorem cosetIndicator_eq_stdTestFunAt {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {e : HeightOneSpectrum (𝓞 K) → ℕ}
    (he : HasConductorExponentAt K v (localChar χ v) (e v)) (h0 : e v ≠ 0) :
    CosetTensor.cosetIndicator (fun _ => 1) (fun w => AdelicLevel.uniformizerUnit K w ^ e w) v
      = stdTestFunAt K v (localChar χ v) := by
  classical
  have hnot : ¬ HasConductorExponentAt K v (localChar χ v) 0 := fun h00 =>
    h0 (hasConductorExponentAt_unique K v he h00)
  funext y
  rw [stdTestFunAt, if_neg hnot, conductorExponentAt_eq_of_hasConductorExponentAt K v he, CosetTensor.cosetIndicator,
    Set.indicator_apply]
  have hiff := inv_mul_sub_one_mem_iff (UnramifiedLocalData.valued_uniformizerUnit_eq_ofAdd_neg_one v) h0 y
  split_ifs with h1 h2 h3
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h3) h1
  · rfl

private theorem exists_pos_forall_localZeta_cosetIndicator_eq {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}
    {e : HeightOneSpectrum (𝓞 K) → ℕ} (he : HasConductorExponentAt K v (localChar χ v) (e v)) (h0 : e v ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℂ,
      letI := localBorel K v
      localZeta (selfDualHaarAt K v)
          (CosetTensor.cosetIndicator (fun _ => 1) (fun w => AdelicLevel.uniformizerUnit K w ^ e w) v)
          (localChar χ v) s
        = (r : ℂ) := by
  have h1 : 1 ≤ e v := Nat.one_le_iff_ne_zero.2 h0
  refine ⟨(selfDualHaarAt K v).real (((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v (e v)),
    ?_, fun s => ?_⟩
  · rw [selfDualHaarAt_real_image_higherUnitsAt K v (e v) h1]
    have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := zero_lt_one.trans (EulerSpellingBridge.one_lt_absNorm K v)
    positivity
  · rw [cosetIndicator_eq_stdTestFunAt he h0]
    exact localZeta_stdTestFunAt_eq_real_image_higherUnitsAt K v (localChar χ v) (e v) h1 he s

end ConductorCoset
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end ConductorCoset
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section HeckeAuxiliary

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace HeckeAuxiliary

variable {F : Type} [Field F] [NumberField F]

private theorem multipliable_one_sub_mul_cpow {S : Finset (HeightOneSpectrum (𝓞 F))}
    (z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s) := by
  have hbase : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-s.re) :=
    (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt F hs).comp_injective
      Subtype.val_injective
  have hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      ‖-(z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))‖ := by
    refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hbase
    have hpos : 0 < Ideal.absNorm v.1.asIdeal := by
      exact_mod_cast zero_lt_one.trans (EulerSpellingBridge.one_lt_absNorm F v.1)
    rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (hz v)
  have hmul := multipliable_one_add_of_summable hsum
  simpa only [← sub_eq_add_neg] using hmul

private theorem tprod_mul_tprod_inv_eq_one (S : Finset (HeightOneSpectrum (𝓞 F)))
    (z : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))
      * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ = 1 := by
  have hA := multipliable_one_sub_mul_cpow z hz hs
  have hB :=
    (NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S z hz).1 s hs
  rw [← hA.tprod_mul hB]
  calc (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
            * (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
        = ∏' _v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 : ℂ) :=
          tprod_congr fun v =>
            mul_inv_cancel₀ (EulerSpellingBridge.one_sub_mul_cpow_ne_zero F v.1 (z v) (hz v) s (by linarith))
    _ = 1 := tprod_one

omit [NumberField F] in

private theorem exists_forall_norm_finset_prod_le (S' : Finset (HeightOneSpectrum (𝓞 F)))
    (g : HeightOneSpectrum (𝓞 F) → ℂ → ℂ) (σ₂ : ℝ)
    (h : ∀ v ∈ S', ∃ C : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ σ₂ → ‖g v s‖ ≤ C) :
    ∃ C : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ σ₂ → ‖∏ v ∈ S', g v s‖ ≤ C := by
  choose! C hC using h
  refine ⟨∏ v ∈ S', max 0 (C v), fun s hs1 hs2 => ?_⟩
  rw [norm_prod]
  exact Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v hv =>
    (hC v hv s hs1 hs2).trans (le_max_right _ _)

private abbrev Slots (F : Type) [Field F] : Type :=
  {w : InfinitePlace F // w.IsReal} ⊕ ({w : InfinitePlace F // w.IsComplex} ⊕ {w : InfinitePlace F // w.IsComplex})

private def packShifts (xr : {w : InfinitePlace F // w.IsReal} → ℂ) (xc : {w : InfinitePlace F // w.IsComplex} → ℂ) :
    Slots F → ℂ :=
  Sum.elim xr (Sum.elim xc fun j => xc j + 1)

omit [NumberField F] in
private theorem re_packShifts_nonneg (xr : {w : InfinitePlace F // w.IsReal} → ℂ)
    (xc : {w : InfinitePlace F // w.IsComplex} → ℂ) (hr : ∀ i, 0 ≤ (xr i).re) (hc : ∀ j, 0 ≤ (xc j).re)
    (x : Slots F) : 0 ≤ (packShifts xr xc x).re := by
  rcases x with i | j | j
  · exact hr i
  · exact hc j
  · show 0 ≤ (xc j + 1).re
    rw [Complex.add_re, Complex.one_re]
    linarith [hc j]

open scoped Classical in
private theorem prod_packShifts (xr : {w : InfinitePlace F // w.IsReal} → ℂ)
    (xc : {w : InfinitePlace F // w.IsComplex} → ℂ) (s : ℂ) :
    ∏ l : Fin (Fintype.card (Slots F)),
        Complex.Gammaℝ (s + packShifts xr xc ((Fintype.equivFin (Slots F)).symm l))
      = (∏ i, Complex.Gammaℝ (s + xr i)) * ∏ j, Complex.Gammaℂ (s + xc j) := by
  refine (Fintype.prod_equiv (Fintype.equivFin (Slots F)).symm _
    (fun x => Complex.Gammaℝ (s + packShifts xr xc x)) fun _ => rfl).trans ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [packShifts, Sum.elim_inl, Sum.elim_inr]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← add_assoc, Complex.Gammaℝ_mul_Gammaℝ_add_one]

open scoped Classical in

private theorem exists_fin_lists (cr dr : {w : InfinitePlace F // w.IsReal} → ℂ)
    (cc dc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (_h1 : ∀ i, 0 ≤ (cr i).re) (_h2 : ∀ i, 0 ≤ (dr i).re) (_h3 : ∀ j, 0 ≤ (cc j).re) (_h4 : ∀ j, 0 ≤ (dc j).re) :
    ∃ (m : ℕ) (c d : Fin m → ℂ), (∀ l, 0 ≤ (c l).re) ∧ (∀ l, 0 ≤ (d l).re) ∧
      (∀ s : ℂ,
        ∏ l, Complex.Gammaℝ (s + c l) = (∏ i, Complex.Gammaℝ (s + cr i)) * ∏ j, Complex.Gammaℂ (s + cc j)) ∧
      (∀ s : ℂ,
        ∏ l, Complex.Gammaℝ (s + d l) = (∏ i, Complex.Gammaℝ (s + dr i)) * ∏ j, Complex.Gammaℂ (s + dc j)) := by
  exact ⟨Fintype.card (Slots F), fun l => packShifts cr cc ((Fintype.equivFin (Slots F)).symm l),
    fun l => packShifts dr dc ((Fintype.equivFin (Slots F)).symm l),
    fun _ => re_packShifts_nonneg cr cc _h1 _h3 _, fun _ => re_packShifts_nonneg dr dc _h2 _h4 _,
    fun s => prod_packShifts cr cc s, fun s => prod_packShifts dr dc s⟩

end HeckeAuxiliary
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end HeckeAuxiliary
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section HeckeObjects

set_option autoImplicit false

open NumberField IsDedekindDomain
open NumberField.TateGlobal

noncomputable section

namespace HeckeObjects

open MeasureTheory NumberField.AdelicFourier

variable (F : Type) [Field F] [NumberField F]

private def heckeMu : @Measure (AdeleRing (𝓞 F) F) (AdelicHaar.adeleBorel (𝓞 F) F) :=
  (AdelicHaar.adelicAddHaar (𝓞 F) F (AdelicBox.adelicBox F))⁻¹ • AdelicHaar.adelicAddHaar (𝓞 F) F

private
def testTensor (ar : {w : InfinitePlace F // w.IsReal} → ZMod 2) (kc : {w : InfinitePlace F // w.IsComplex} → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ) : AdeleRing (𝓞 F) F → ℂ :=
  TensorFactorization.adelicTensor (fun w => LanglandsTunnell.ArchPlace.realTestFun (ar w))
    (fun w => LanglandsTunnell.ArchPlace.complexTestFun (kc w)) S
    (CosetTensor.cosetIndicator (fun _ => 1) (fun v => AdelicLevel.uniformizerUnit F v ^ e v))

private def dualZeta (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (ar : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (kc : {w : InfinitePlace F // w.IsComplex} → ℤ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : HeightOneSpectrum (𝓞 F) → ℕ) (s : ℂ) : ℂ :=
  letI := AdelicHaar.adeleBorel (𝓞 F) F
  letI := Idele.ideleBorel F
  zetaIntegral (Idele.idelicHaar F)
    (fourierIntegral (StandardAddChar.stdAddChar F) (heckeMu F) (testTensor F ar kc S e)) χ⁻¹ s

end HeckeObjects
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end HeckeObjects
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section GaussianSchwartz

set_option autoImplicit false

open scoped SchwartzMap
open Nat

namespace GaussianSchwartz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem one_add_pow_mul_exp_le (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) ^ m * Real.exp (-(Real.pi * t ^ 2)) ≤ 2 ^ m * (1 + m ! / Real.pi ^ m) := by
  have hpi : (0 : ℝ) < Real.pi ^ m := pow_pos Real.pi_pos m
  have hexp : Real.exp (-(Real.pi * t ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg Real.pi_pos.le (sq_nonneg t)))
  have h1 : (1 + t) ^ m ≤ 2 ^ m * (1 + (t ^ 2) ^ m) := by
    have hmax : 1 + t ≤ 2 * max 1 t := by
      have h₁ := le_max_left 1 t
      have h₂ := le_max_right 1 t
      linarith
    calc (1 + t) ^ m ≤ (2 * max 1 t) ^ m := pow_le_pow_left₀ (by linarith) hmax m
      _ = 2 ^ m * (max 1 t) ^ m := mul_pow 2 (max 1 t) m
      _ ≤ 2 ^ m * (1 + (t ^ 2) ^ m) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total t 1 with h | h
        · rw [max_eq_left h, one_pow]
          exact le_add_of_nonneg_right (by positivity)
        · rw [max_eq_right h]
          calc t ^ m ≤ (t ^ 2) ^ m := pow_le_pow_left₀ ht (by nlinarith) m
            _ ≤ 1 + (t ^ 2) ^ m := le_add_of_nonneg_left zero_le_one
  have h2 : (t ^ 2) ^ m * Real.exp (-(Real.pi * t ^ 2)) ≤ m ! / Real.pi ^ m := by
    have hb := Real.pow_div_factorial_le_exp (Real.pi * t ^ 2) (mul_nonneg Real.pi_pos.le (sq_nonneg t)) m
    rw [div_le_iff₀ (by positivity), mul_pow] at hb
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hpi]
    linarith
  calc (1 + t) ^ m * Real.exp (-(Real.pi * t ^ 2))
      ≤ 2 ^ m * (1 + (t ^ 2) ^ m) * Real.exp (-(Real.pi * t ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 2 ^ m * (Real.exp (-(Real.pi * t ^ 2)) + (t ^ 2) ^ m * Real.exp (-(Real.pi * t ^ 2))) := by ring
    _ ≤ 2 ^ m * (1 + m ! / Real.pi ^ m) := mul_le_mul_of_nonneg_left (add_le_add hexp h2) (by positivity)

private theorem exists_schwartzMap_eq_exp_neg_pi_mul (Q : E → ℝ) (hQ : Q.HasTemperateGrowth)
    (hQn : ∀ x, ‖x‖ ^ 2 ≤ Q x) :
    ∃ g : 𝓢(E, ℂ), ∀ x, g x = Complex.exp (((-(Real.pi * Q x) : ℝ) : ℂ)) := by
  have hf : (fun x : E => -(Real.pi * Q x)).HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const (E := E) Real.pi).mul hQ).neg
  let r : 𝓢(E, ℝ) :=
    { toFun := Real.exp ∘ fun x : E => -(Real.pi * Q x)
      smooth' := Real.contDiff_exp.comp hf.1
      decay' := by
        intro k n
        obtain ⟨K, A, hA0, hA⟩ := hf.norm_iteratedFDeriv_le_uniform n
        refine ⟨n ! * (1 + A) ^ n * (2 ^ (k + K * n) * (1 + (k + K * n) ! / Real.pi ^ (k + K * n))),
          fun x => ?_⟩
        have hx1 : (1 : ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
        have hcomp : ‖iteratedFDeriv ℝ n (Real.exp ∘ fun x : E => -(Real.pi * Q x)) x‖
            ≤ n ! * Real.exp (-(Real.pi * Q x)) * ((1 + A) * (1 + ‖x‖) ^ K) ^ n := by
          refine norm_iteratedFDeriv_comp_le Real.contDiff_exp hf.1 (mod_cast le_top) x
            (fun i _ => ?_) (fun i hi hin => ?_)
          · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
              Real.norm_of_nonneg (Real.exp_pos _).le]
          · calc ‖iteratedFDeriv ℝ i (fun x : E => -(Real.pi * Q x)) x‖ ≤ A * (1 + ‖x‖) ^ K := hA i hin x
              _ ≤ (1 + A) * (1 + ‖x‖) ^ K := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
              _ ≤ ((1 + A) * (1 + ‖x‖) ^ K) ^ i :=
                le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hx1)) (by omega)
        have hgauss : Real.exp (-(Real.pi * Q x)) ≤ Real.exp (-(Real.pi * ‖x‖ ^ 2)) :=
          Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (hQn x) Real.pi_pos.le))
        have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
        calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ fun x : E => -(Real.pi * Q x)) x‖
            ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-(Real.pi * ‖x‖ ^ 2)) * ((1 + A) * (1 + ‖x‖) ^ K) ^ n) := by
              refine mul_le_mul hxk (hcomp.trans ?_) (norm_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgauss (by positivity))
                (by positivity)
          _ = n ! * (1 + A) ^ n * ((1 + ‖x‖) ^ (k + K * n) * Real.exp (-(Real.pi * ‖x‖ ^ 2))) := by
              rw [mul_pow, ← pow_mul, pow_add]
              ring
          _ ≤ n ! * (1 + A) ^ n * (2 ^ (k + K * n) * (1 + (k + K * n) ! / Real.pi ^ (k + K * n))) :=
              mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_le (k + K * n) (norm_nonneg x))
                (by positivity) }
  refine ⟨r.postcompCLM Complex.ofRealCLM, fun x => ?_⟩
  rw [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply]
  exact Complex.ofReal_exp _

end GaussianSchwartz
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end GaussianSchwartz
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section ArchSchwartz

set_option autoImplicit false

noncomputable section

open Complex Real NumberField
open scoped Classical

namespace ArchSchwartz

open LanglandsTunnell.ArchPlace (realTestFun complexTestFun)

variable (K : Type) [Field K] [NumberField K]

private def quadForm (x : mixedEmbedding.mixedSpace K) : ℝ :=
  (∑ w, x.1 w ^ 2) + 2 * ∑ w, ‖x.2 w‖ ^ 2

private def monomial (a : {w : InfinitePlace K // w.IsReal} → ZMod 2) (k : {w : InfinitePlace K // w.IsComplex} → ℤ)
    (x : mixedEmbedding.mixedSpace K) : ℂ :=
  (∏ w, ((x.1 w : ℂ) ^ ((a w).val : ℕ))) *
    ∏ w, ((starRingEnd ℂ (x.2 w)) ^ (k w).toNat * (x.2 w) ^ (-(k w)).toNat)

variable {K}

private def realCoord (w : {w : InfinitePlace K // w.IsReal}) : mixedEmbedding.mixedSpace K →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj w).comp (ContinuousLinearMap.fst ℝ _ _)

private def complexCoord (w : {w : InfinitePlace K // w.IsComplex}) : mixedEmbedding.mixedSpace K →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj w).comp (ContinuousLinearMap.snd ℝ _ _)

private theorem hasTemperateGrowth_finset_prod {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedCommRing R] [NormedAlgebra ℝ R] {ι : Type*} (s : Finset ι) (f : ι → E → R)
    (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Function.HasTemperateGrowth.const (E := E) (1 : R)
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    have h1 : (f j).HasTemperateGrowth := hf j (Finset.mem_insert_self j s)
    have h2 : (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth :=
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    exact h1.mul h2

private theorem quadForm_hasTemperateGrowth : (quadForm K).HasTemperateGrowth := by
  have hr : (fun x : mixedEmbedding.mixedSpace K => ∑ w, x.1 w ^ 2).HasTemperateGrowth := by
    refine Function.HasTemperateGrowth.sum (f := fun w (x : mixedEmbedding.mixedSpace K) => x.1 w ^ 2) fun w _ => ?_
    exact ((realCoord w).hasTemperateGrowth).pow 2
  have hc : (fun x : mixedEmbedding.mixedSpace K => ∑ w, ‖x.2 w‖ ^ 2).HasTemperateGrowth := by
    refine Function.HasTemperateGrowth.sum (f := fun w (x : mixedEmbedding.mixedSpace K) => ‖x.2 w‖ ^ 2) fun w _ => ?_
    exact Function.HasTemperateGrowth.comp (Function.hasTemperateGrowth_norm_sq (H := ℂ))
      (complexCoord w).hasTemperateGrowth
  have h2 : (fun x : mixedEmbedding.mixedSpace K => 2 * ∑ w, ‖x.2 w‖ ^ 2).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (E := mixedEmbedding.mixedSpace K) (2 : ℝ)).mul hc
  exact hr.add h2

private theorem monomial_hasTemperateGrowth (a : {w : InfinitePlace K // w.IsReal} → ZMod 2)
    (k : {w : InfinitePlace K // w.IsComplex} → ℤ) : (monomial K a k).HasTemperateGrowth := by
  have hr : (fun x : mixedEmbedding.mixedSpace K => ∏ w, ((x.1 w : ℂ) ^ ((a w).val : ℕ))).HasTemperateGrowth := by
    refine hasTemperateGrowth_finset_prod Finset.univ
      (fun w (x : mixedEmbedding.mixedSpace K) => (x.1 w : ℂ) ^ ((a w).val : ℕ)) fun w _ => ?_
    exact (Function.HasTemperateGrowth.comp Complex.ofRealCLM.hasTemperateGrowth
      (realCoord w).hasTemperateGrowth).pow _
  have hc : (fun x : mixedEmbedding.mixedSpace K =>
      ∏ w, ((starRingEnd ℂ (x.2 w)) ^ (k w).toNat * (x.2 w) ^ (-(k w)).toNat)).HasTemperateGrowth := by
    refine hasTemperateGrowth_finset_prod Finset.univ
      (fun w (x : mixedEmbedding.mixedSpace K) => (starRingEnd ℂ (x.2 w)) ^ (k w).toNat * (x.2 w) ^ (-(k w)).toNat)
      fun w _ => ?_
    have hconj : (fun x : mixedEmbedding.mixedSpace K => starRingEnd ℂ (x.2 w)).HasTemperateGrowth :=
      Function.HasTemperateGrowth.comp Complex.conjCLE.hasTemperateGrowth (complexCoord w).hasTemperateGrowth
    exact (hconj.pow _).mul (((complexCoord w).hasTemperateGrowth).pow _)
  exact hr.mul hc

private theorem norm_sq_le_quadForm (x : mixedEmbedding.mixedSpace K) : ‖x‖ ^ 2 ≤ quadForm K x := by
  have hr0 : 0 ≤ ∑ w, x.1 w ^ 2 := Finset.sum_nonneg fun w _ => sq_nonneg _
  have hc0 : 0 ≤ ∑ w, ‖x.2 w‖ ^ 2 := Finset.sum_nonneg fun w _ => sq_nonneg _
  have h1 : ‖x.1‖ ^ 2 ≤ ∑ w, x.1 w ^ 2 := by
    have : ‖x.1‖ ≤ Real.sqrt (∑ w, x.1 w ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => ?_
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (Finset.single_le_sum (fun v _ => sq_nonneg (x.1 v)) (Finset.mem_univ w))
    calc ‖x.1‖ ^ 2 ≤ Real.sqrt (∑ w, x.1 w ^ 2) ^ 2 := by gcongr
      _ = ∑ w, x.1 w ^ 2 := Real.sq_sqrt hr0
  have h2 : ‖x.2‖ ^ 2 ≤ ∑ w, ‖x.2 w‖ ^ 2 := by
    have : ‖x.2‖ ≤ Real.sqrt (∑ w, ‖x.2 w‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => ?_
      exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun v _ => sq_nonneg ‖x.2 v‖) (Finset.mem_univ w))
    calc ‖x.2‖ ^ 2 ≤ Real.sqrt (∑ w, ‖x.2 w‖ ^ 2) ^ 2 := by gcongr
      _ = ∑ w, ‖x.2 w‖ ^ 2 := Real.sq_sqrt hc0
  unfold quadForm
  rw [Prod.norm_def]
  rcases le_total ‖x.1‖ ‖x.2‖ with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

private
theorem tensor_eq (a : {w : InfinitePlace K // w.IsReal} → ZMod 2) (k : {w : InfinitePlace K // w.IsComplex} → ℤ)
    (x : mixedEmbedding.mixedSpace K) :
    (∏ w, realTestFun (a w) (x.1 w)) * ∏ w, complexTestFun (k w) (x.2 w)
      = monomial K a k x * Complex.exp (((-(π * quadForm K x) : ℝ) : ℂ)) := by
  unfold realTestFun complexTestFun monomial quadForm
  simp only [Finset.prod_mul_distrib]
  rw [← Complex.exp_sum, ← Complex.exp_sum, mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  push_cast
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← neg_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

private theorem exists_schwartzMap_tensor (a : {w : InfinitePlace K // w.IsReal} → ZMod 2)
    (k : {w : InfinitePlace K // w.IsComplex} → ℤ) :
    ∃ g : SchwartzMap (mixedEmbedding.mixedSpace K) ℂ,
      ∀ x, g x = (∏ w, realTestFun (a w) (x.1 w)) * ∏ w, complexTestFun (k w) (x.2 w) := by
  obtain ⟨g, hg⟩ := GaussianSchwartz.exists_schwartzMap_eq_exp_neg_pi_mul (quadForm K) quadForm_hasTemperateGrowth
    norm_sq_le_quadForm
  refine ⟨SchwartzMap.smulLeftCLM ℂ (monomial K a k) g, fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (monomial_hasTemperateGrowth a k), hg, smul_eq_mul, tensor_eq]

end ArchSchwartz
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end ArchSchwartz
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section TensorSchwartz

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.AdelicFourier NumberField.AdelicBox

namespace TensorSchwartz

variable {F : Type} [Field F] [NumberField F]

private theorem isLocallyConstant_indicator_one {X : Type} [TopologicalSpace X] {B : Set X} (ho : IsOpen B)
    (hc : IsClosed B) : IsLocallyConstant (B.indicator (1 : X → ℂ)) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  by_cases hx : x ∈ B
  · filter_upwards [ho.mem_nhds hx] with y hy
    simp [hx, hy]
  · filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy
    have hy' : y ∉ B := hy
    simp [hx, hy']

private theorem coset_image_eq_preimage (S : Finset (HeightOneSpectrum (𝓞 F)))
    (α : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) :
    (fun z => CosetTensor.spliceOn S α + CosetTensor.unitOn S u * z) '' integralFiniteAdeles (𝓞 F) F
      = (fun x => CosetTensor.unitInvOn S u * (x - CosetTensor.spliceOn S α)) ⁻¹'
          integralFiniteAdeles (𝓞 F) F := by
  refine congrFun (Set.image_eq_preimage_of_inverse (fun z => ?_) (fun x => ?_)) _
  · show CosetTensor.unitInvOn S u * (CosetTensor.spliceOn S α + CosetTensor.unitOn S u * z - CosetTensor.spliceOn S α)
      = z
    rw [add_sub_cancel_left, ← mul_assoc, mul_comm (CosetTensor.unitInvOn S u), CosetTensor.unitOn_mul_unitInvOn,
      one_mul]
  · show CosetTensor.spliceOn S α
        + CosetTensor.unitOn S u * (CosetTensor.unitInvOn S u * (x - CosetTensor.spliceOn S α)) = x
    rw [← mul_assoc, CosetTensor.unitOn_mul_unitInvOn, one_mul, add_sub_cancel]

private
theorem isLocallyConstant_and_hasCompactSupport_finiteTensor_cosetIndicator (S : Finset (HeightOneSpectrum (𝓞 F)))
    (α : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) :
    IsLocallyConstant (TensorFactorization.finiteTensor S (CosetTensor.cosetIndicator α u)) ∧
      HasCompactSupport (TensorFactorization.finiteTensor S (CosetTensor.cosetIndicator α u)) := by
  rw [CosetTensor.finiteTensor_cosetIndicator_eq]
  have hBc : IsCompact
      ((fun z => CosetTensor.spliceOn S α + CosetTensor.unitOn S u * z) '' integralFiniteAdeles (𝓞 F) F) :=
    (isCompact_integralFiniteAdeles F).image (continuous_const.add (continuous_const.mul continuous_id))
  refine ⟨isLocallyConstant_indicator_one ?_ ?_, HasCompactSupport.intro hBc fun x hx => ?_⟩
  rotate_left 2
  · simp [hx]
  · rw [coset_image_eq_preimage]
    exact (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul (continuous_id.sub continuous_const))
  · rw [coset_image_eq_preimage]
    exact (isClosed_integralFiniteAdeles F).preimage (continuous_const.mul (continuous_id.sub continuous_const))

private theorem adelicTensor_cosetIndicator_mem_schwartzBruhat (ar : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (kc : {w : InfinitePlace F // w.IsComplex} → ℤ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (α : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) :
    TensorFactorization.adelicTensor (fun w => LanglandsTunnell.ArchPlace.realTestFun (ar w))
        (fun w => LanglandsTunnell.ArchPlace.complexTestFun (kc w)) S (CosetTensor.cosetIndicator α u)
      ∈ schwartzBruhat F := by
  obtain ⟨g, hg⟩ := ArchSchwartz.exists_schwartzMap_tensor ar kc
  obtain ⟨hlc, hcs⟩ := isLocallyConstant_and_hasCompactSupport_finiteTensor_cosetIndicator S α u
  have heq : TensorFactorization.adelicTensor (fun w => LanglandsTunnell.ArchPlace.realTestFun (ar w))
      (fun w => LanglandsTunnell.ArchPlace.complexTestFun (kc w)) S (CosetTensor.cosetIndicator α u)
      = fun x : AdeleRing (𝓞 F) F => g (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) *
          TensorFactorization.finiteTensor S (CosetTensor.cosetIndicator α u) x.2 := by
    funext x
    simp only [TensorFactorization.adelicTensor_apply, TensorFactorization.mixedTensor_apply, hg]
  rw [heq]
  exact mem_schwartzBruhat_of_mem_pureTensorSet (tensor_mem_pureTensorSet g _ hlc hcs)

private theorem testTensor_mem_schwartzBruhat (ar : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (kc : {w : InfinitePlace F // w.IsComplex} → ℤ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (e : HeightOneSpectrum (𝓞 F) → ℕ) : HeckeObjects.testTensor F ar kc S e ∈ schwartzBruhat F := by
  unfold HeckeObjects.testTensor
  exact adelicTensor_cosetIndicator_mem_schwartzBruhat ar kc S _ _

end TensorSchwartz
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end TensorSchwartz
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section UnitaryExponent

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace UnitaryExponent

variable {F : Type} [Field F] [NumberField F]

private theorem re_eq_zero_of_isUnitaryChar_of_forall_eq_realCharFun {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 F) F χ) {w : InfinitePlace F} {hw : w.IsReal} {u : ℂ} {a : ZMod 2}
    (h : ∀ x : (w.Completion)ˣ, χ (TateGlobal.archUnitHom w x) = LanglandsTunnell.ArchPlace.realCharFun u a
      (Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).toMonoidHom x)) :
    u.re = 0 := by
  apply ArchCharacterModulus.re_eq_zero_of_forall_norm_realCharFun_eq_one u a
  intro t
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have ht : Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).toMonoidHom
      (Units.map e.symm.toRingHom.toMonoidHom t) = t := by
    ext
    exact e.apply_symm_apply (t : ℝ)
  rw [← ht, ← h]
  exact hχu _

private theorem re_eq_zero_of_isUnitaryChar_of_forall_eq_complexCharFun {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    (hχu : AutomorphicForm.IsUnitaryChar (𝓞 F) F χ) {w : InfinitePlace F} (hw : w.IsComplex) {u : ℂ} {k : ℤ}
    (h : ∀ z : (w.Completion)ˣ, χ (TateGlobal.archUnitHom w z) = LanglandsTunnell.ArchPlace.complexCharFun u k
      (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom z)) :
    u.re = 0 := by
  apply ArchCharacterModulus.re_eq_zero_of_forall_norm_complexCharFun_eq_one u k
  intro t
  set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  have ht : Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom
      (Units.map e.symm.toRingHom.toMonoidHom t) = t := by
    ext
    exact e.apply_symm_apply (t : ℂ)
  rw [← ht, ← h]
  exact hχu _

end UnitaryExponent
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end UnitaryExponent
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section HeckeCore

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal

noncomputable section

namespace HeckeCore

section Helpers

open MeasureTheory LanglandsTunnell.TateLocal

variable (F : Type) [Field F] [NumberField F]

private theorem isAddHaarMeasure_heckeMu :
    letI := AdelicHaar.adeleBorel (𝓞 F) F
    (HeckeObjects.heckeMu F).IsAddHaarMeasure := by
  letI := AdelicHaar.adeleBorel (𝓞 F) F
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  unfold HeckeObjects.heckeMu
  exact Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (AdelicBox.measure_adelicBox_lt_top F _).ne)
    (ENNReal.inv_ne_top.2 (AdelicBox.measure_adelicBox_pos F _).ne')

private theorem heckeMu_adelicBox : HeckeObjects.heckeMu F (AdelicBox.adelicBox F) = 1 := by
  letI := AdelicHaar.adeleBorel (𝓞 F) F
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  unfold HeckeObjects.heckeMu
  rw [Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel (AdelicBox.measure_adelicBox_pos F _).ne' (AdelicBox.measure_adelicBox_lt_top F _).ne]

private theorem isAddHaarMeasure_selfDualHaarAt (v : HeightOneSpectrum (𝓞 F)) :
    letI := localBorel F v
    (selfDualHaarAt F v).IsAddHaarMeasure := by
  letI := localBorel F v
  haveI := borelSpace_localBorel F v
  unfold selfDualHaarAt
  refine Measure.IsAddHaarMeasure.nnreal_smul _ ?_
  have hN : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    exact_mod_cast zero_lt_one.trans (EulerSpellingBridge.one_lt_absNorm F v)
  exact (NNReal.rpow_pos hN).ne'

end Helpers
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

open HeckeObjects MeasureTheory NumberField.AdelicFourier

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in

private theorem heckeCore
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχ : IsIdeleClassChar (𝓞 F) F χ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 F) F χ)
    (_hχ1 : ∃ x ∈ normOneIdeles F, χ x ≠ 1)
    (ur : {w : InfinitePlace F // w.IsReal} → ℂ) (ar : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (_hreal : ∀ (i : {w : InfinitePlace F // w.IsReal}) (x : (i.1.Completion)ˣ),
      χ (NumberField.TateGlobal.archUnitHom i.1 x) =
        LanglandsTunnell.ArchPlace.realCharFun (ur i) (ar i)
          (Units.map
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal i.2).toMonoidHom x))
    (uc : {w : InfinitePlace F // w.IsComplex} → ℂ) (kc : {w : InfinitePlace F // w.IsComplex} → ℤ)
    (_hcomplex : ∀ (j : {w : InfinitePlace F // w.IsComplex}) (z : (j.1.Completion)ˣ),
      χ (NumberField.TateGlobal.archUnitHom j.1 z) =
        LanglandsTunnell.ArchPlace.complexCharFun (uc j) (kc j)
          (Units.map
            (NumberField.InfinitePlace.Completion.extensionEmbedding j.1).toMonoidHom z)) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ) (Z : ℂ → ℂ) (c₁ : ℂ),
      (∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ↔ ¬ IsUnramifiedCharAt χ v) ∧ c₁ ≠ 0 ∧ Differentiable ℂ Z ∧
      (∀ σ₁ σ₂ : ℝ, ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Z s‖ ≤ C) ∧
      (∀ s : ℂ, 1 < s.re →
        Z s = c₁
          * (∏ i : {w : InfinitePlace F // w.IsReal}, Complex.Gammaℝ (s + (ur i + LanglandsTunnell.signShift (ar i))))
          * (∏ j : {w : InfinitePlace F // w.IsComplex}, Complex.Gammaℂ (s + (uc j + ((kc j).natAbs : ℂ) / 2)))
          * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
              (1 - ((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ∧
      (∀ s : ℂ, 1 < s.re → Z (1 - s) = dualZeta F χ ar kc S e s) := by

  obtain ⟨S₀, hS₀⟩ := exists_finset_forall_isUnramifiedCharAt_of_continuous F χ _hχc
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀.filter (fun v => ¬ IsUnramifiedCharAt χ v)
  have hS : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ↔ ¬ IsUnramifiedCharAt χ v := fun v =>
    ⟨fun hv => (Finset.mem_filter.1 hv).2, fun hv => Finset.mem_filter.2 ⟨by_contra fun h0 => hv (hS₀ v h0), hv⟩⟩
  have hSc : ∀ v ∉ S, IsUnramifiedCharAt χ v := fun v hv => by_contra fun h => hv ((hS v).2 h)
  choose e he using fun v : HeightOneSpectrum (𝓞 F) =>
    LanglandsTunnell.TateLocal.exists_hasConductorExponentAt_of_continuous F v (localChar χ v)
      (continuous_localChar χ _hχc v)
  have he0 : ∀ v ∈ S, e v ≠ 0 := fun v hv h0 =>
    (hS v).1 hv (ConductorCoset.isUnramifiedCharAt_of_hasConductorExponentAt_zero (h0 ▸ he v))

  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : ℝ, v ∈ S → (0 < r ∧ ∀ t : ℂ,
      letI := LanglandsTunnell.TateLocal.localBorel F v
      LanglandsTunnell.TateLocal.localZeta (LanglandsTunnell.TateLocal.selfDualHaarAt F v)
        (CosetTensor.cosetIndicator (fun _ => 1) (fun w => AdelicLevel.uniformizerUnit F w ^ e w) v)
        (localChar χ v) t = (r : ℂ)) := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨r, hr, hrz⟩ := ConductorCoset.exists_pos_forall_localZeta_cosetIndicator_eq (he v) (he0 v hv)
      exact ⟨r, fun _ => ⟨hr, hrz⟩⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose r hr using hloc

  letI := Idele.ideleBorel F
  haveI := Idele.borelSpace_ideleBorel F
  haveI := Idele.isHaarMeasure_idelicHaar F
  letI := AdelicHaar.adeleBorel (𝓞 F) F
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_heckeMu F
  letI : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) := fun v =>
    LanglandsTunnell.TateLocal.localBorel F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) := fun v =>
    LanglandsTunnell.TateLocal.borelSpace_localBorel F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), (LanglandsTunnell.TateLocal.selfDualHaarAt F v).IsAddHaarMeasure := fun v =>
    isAddHaarMeasure_selfDualHaarAt F v
  letI : ∀ w : InfinitePlace F, MeasurableSpace w.Completion := fun _ => borel _
  haveI : ∀ w : InfinitePlace F, BorelSpace w.Completion := fun _ => ⟨rfl⟩
  haveI : ∀ w : InfinitePlace F, (ZetaTransport.archMeasure w).IsAddHaarMeasure := fun w =>
    ZetaTransport.isAddHaarMeasure_archMeasure w

  obtain ⟨Z, hZ, hid, hfe, hstrip⟩ :=
    zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one F
      (Idele.idelicHaar F) (heckeMu F) (heckeMu_adelicBox F) (StandardAddChar.stdAddChar F)
      (StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK
      (StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace F)
      (TensorSchwartz.testTensor_mem_schwartzBruhat ar kc S e) _hχc _hχu _hχ _hχ1

  obtain ⟨c, hc, hfact⟩ := zetaIntegral_mul_eulerFactors_eq F (Idele.idelicHaar F) S
    (fun v => LanglandsTunnell.TateLocal.selfDualHaarAt F v) (fun w => ZetaTransport.archMeasure w)
    (fun v => AdelicLevel.uniformizerUnit F v) (fun v => UnramifiedLocalData.valued_uniformizerUnit_eq_ofAdd_neg_one v)
  have hur : ∀ i, (ur i).re = 0 := fun i =>
    UnitaryExponent.re_eq_zero_of_isUnitaryChar_of_forall_eq_realCharFun _hχu (_hreal i)
  have huc : ∀ j, (uc j).re = 0 := fun j =>
    UnitaryExponent.re_eq_zero_of_isUnitaryChar_of_forall_eq_complexCharFun _hχu j.2 (_hcomplex j)
  refine ⟨S, e, Z, (c : ℂ) * (Real.pi : ℂ) ^ Fintype.card {w : InfinitePlace F // w.IsComplex} * ∏ v ∈ S, (r v : ℂ),
    hS, ?_, hZ,
    hstrip, fun s hs => ?_, fun s hs => ?_⟩
  · refine mul_ne_zero (mul_ne_zero (by exact_mod_cast hc.ne') (pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero))) ?_
    exact Finset.prod_ne_zero_iff.2 fun v hv => by exact_mod_cast (hr v hv).1.ne'
  ·
    set A : ℂ :=
      ∏ i : {w : InfinitePlace F // w.IsReal}, Complex.Gammaℝ (s + (ur i + LanglandsTunnell.signShift (ar i)))
    set B : ℂ := ∏ j : {w : InfinitePlace F // w.IsComplex}, Complex.Gammaℂ (s + (uc j + ((kc j).natAbs : ℂ) / 2))

    set Pk : ℂ := ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (1 - ((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))
    set Pi : ℂ := ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
      (1 - ((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹
    have hrow := hfact (testTensor F ar kc S e) _ _
      (TensorFactorization.isFactorizableStandardOutside_adelicTensor _ _ S _) χ _hχc _hχu hSc s hs
    have harch : _ = A * ((Real.pi : ℂ) ^ Fintype.card {w : InfinitePlace F // w.IsComplex} * B) :=
      ArchProduct.prod_localZeta_archMeasure χ ur ar _hreal uc kc _hcomplex hur huc s hs
    have hSprod : (∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (LanglandsTunnell.TateLocal.selfDualHaarAt F v)
          (CosetTensor.cosetIndicator (fun _ => 1) (fun w => AdelicLevel.uniformizerUnit F w ^ e w) v)
          (localChar χ v) s)
        = ∏ v ∈ S, (r v : ℂ) :=
      Finset.prod_congr rfl fun v hv => (hr v hv).2 s
    have hP : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - ((localChar χ v.1 (AdelicLevel.uniformizerUnit F v.1) : ℂˣ) : ℂ)
            * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))) = Pk :=
      tprod_congr fun v => by rw [UnramifiedLocalData.localChar_uniformizerUnit]
    have hF2 : Pk * Pi = 1 :=
      HeckeAuxiliary.tprod_mul_tprod_inv_eq_one S (fun v => ((χ (uniformizerIdele F v.1) : ℂˣ) : ℂ))
        (fun v => (_hχu (uniformizerIdele F v.1)).le) s hs
    have hrow2 : zetaIntegral (Idele.idelicHaar F) (testTensor F ar kc S e) χ s * Pk
        = (c : ℂ) * (A * ((Real.pi : ℂ) ^ Fintype.card {w : InfinitePlace F // w.IsComplex} * B))
          * ∏ v ∈ S, (r v : ℂ) := by
      rw [← hP, ← harch, ← hSprod]
      exact hrow
    rw [hid s hs, show zetaIntegral (Idele.idelicHaar F) (testTensor F ar kc S e) χ s
        = zetaIntegral (Idele.idelicHaar F) (testTensor F ar kc S e) χ s * (Pk * Pi) by rw [hF2, mul_one],
      ← mul_assoc, hrow2]
    ring
  ·
    exact hfe s hs

end HeckeCore
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end HeckeCore
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section LocalZetaStripBound

set_option autoImplicit false

open scoped NNReal ENNReal Pointwise
open MeasureTheory LanglandsTunnell.TateLocal

noncomputable section

namespace ZetaTransport

section Units

variable {K : Type*} [Field K]

private theorem charExt_units_mul (χ : Kˣ →* ℂˣ) (c : Kˣ) (y : K) :
    charExt χ ((c : K) * y) = (χ c : ℂ) * charExt χ y := by
  by_cases hy : y = 0
  · simp [hy]
  · have hcy : (c : K) * y ≠ 0 := mul_ne_zero c.ne_zero hy
    rw [charExt_of_ne_zero χ hcy, charExt_of_ne_zero χ hy]
    have : Units.mk0 ((c : K) * y) hcy = c * Units.mk0 y hy := Units.ext (by simp)
    rw [this, map_mul, Units.val_mul]

end Units
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section Modulus

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

private theorem distribHaarChar_units_inv (c : Kˣ) : distribHaarChar K c⁻¹ = (distribHaarChar K c)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])

private theorem modulus_units_inv (c : Kˣ) : modulus ((c : K)⁻¹) = (modulus (c : K))⁻¹ := by
  rw [← Units.val_inv_eq_inv_val, modulus_coe_units, modulus_coe_units, distribHaarChar_units_inv]

end Modulus
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section Dilation

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]

private def mulUnitEquiv (c : Kˣ) : K ≃ᵐ K :=
  (Homeomorph.mulLeft₀ (c : K) c.ne_zero).toMeasurableEquiv

private theorem mulUnitEquiv_apply (c : Kˣ) (x : K) : mulUnitEquiv c x = (c : K) * x := rfl

private theorem preimage_mulUnitEquiv (c : Kˣ) (t : Set K) : mulUnitEquiv c ⁻¹' t = (c⁻¹ : Kˣ) • t := by
  ext x
  rw [Set.mem_preimage, mulUnitEquiv_apply, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def, smul_eq_mul]

end Dilation
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section Invariance

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

private theorem map_mulUnitEquiv (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (c : Kˣ) :
    Measure.map (mulUnitEquiv c) μ = ((modulus (c : K) : ℝ≥0∞))⁻¹ • μ := by
  ext t ht
  rw [MeasurableEquiv.map_apply, Measure.smul_apply, smul_eq_mul, preimage_mulUnitEquiv,
    ← distribHaarChar_mul μ c⁻¹ t, distribHaarChar_units_inv, ← modulus_coe_units,
    ENNReal.coe_inv (modulus_ne_zero c.ne_zero)]

private theorem map_mulUnitEquiv_mulMeasure (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (c : Kˣ) :
    Measure.map (mulUnitEquiv c) (mulMeasure μ) = mulMeasure μ := by
  have hc0 : (modulus (c : K) : ℝ≥0∞) ≠ 0 := by exact_mod_cast modulus_ne_zero c.ne_zero
  have hct : (modulus (c : K) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hzero : mulUnitEquiv c ⁻¹' ({0}ᶜ : Set K) = {0}ᶜ := by
    ext x
    simp [mulUnitEquiv_apply, c.ne_zero]
  have hmap : Measure.map (mulUnitEquiv c) (μ.restrict {0}ᶜ)
      = ((modulus (c : K) : ℝ≥0∞))⁻¹ • μ.restrict {0}ᶜ := by
    conv_lhs => rw [← hzero]
    rw [← MeasurableEquiv.restrict_map, map_mulUnitEquiv, Measure.restrict_smul]
  ext t ht
  rw [MeasurableEquiv.map_apply, mulMeasure, withDensity_apply _ ((mulUnitEquiv c).measurable ht),
    withDensity_apply _ ht]
  have hpt : ∀ y : K, ((modulus ((mulUnitEquiv c).symm y) : ℝ≥0∞))⁻¹
      = (modulus (c : K) : ℝ≥0∞) * ((modulus y : ℝ≥0∞))⁻¹ := by
    intro y
    have : (mulUnitEquiv c).symm y = ((c : K)⁻¹) * y := rfl
    rw [this, modulus_mul, modulus_units_inv, ENNReal.coe_mul, ENNReal.coe_inv (modulus_ne_zero c.ne_zero),
      ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hct)) (Or.inl (ENNReal.inv_ne_top.2 hc0)), inv_inv]
  calc ∫⁻ a in mulUnitEquiv c ⁻¹' t, ((modulus a : ℝ≥0∞))⁻¹ ∂μ.restrict {0}ᶜ
      = ∫⁻ a, ((modulus ((mulUnitEquiv c).symm (mulUnitEquiv c a)) : ℝ≥0∞))⁻¹
          ∂(μ.restrict {0}ᶜ).restrict (mulUnitEquiv c ⁻¹' t) := by
        simp only [MeasurableEquiv.symm_apply_apply]
    _ = ∫⁻ y, ((modulus ((mulUnitEquiv c).symm y) : ℝ≥0∞))⁻¹
          ∂Measure.map (mulUnitEquiv c) ((μ.restrict {0}ᶜ).restrict (mulUnitEquiv c ⁻¹' t)) := by
        rw [lintegral_map_equiv]
    _ = ∫⁻ y in t, ((modulus ((mulUnitEquiv c).symm y) : ℝ≥0∞))⁻¹ ∂Measure.map (mulUnitEquiv c) (μ.restrict {0}ᶜ) := by
        rw [MeasurableEquiv.restrict_map]
    _ = (modulus (c : K) : ℝ≥0∞)⁻¹
          * ∫⁻ y in t, (modulus (c : K) : ℝ≥0∞) * ((modulus y : ℝ≥0∞))⁻¹ ∂μ.restrict {0}ᶜ := by
        rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
        congr 1
        exact lintegral_congr fun y => hpt y
    _ = ∫⁻ a in t, ((modulus a : ℝ≥0∞))⁻¹ ∂μ.restrict {0}ᶜ := by
        rw [lintegral_const_mul' _ _ hct, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

private theorem localZeta_comp_inv_mul (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular] (f : K → ℂ) (χ : Kˣ →* ℂˣ)
    (s : ℂ) (c : Kˣ) :
    localZeta μ (fun x => f (((c : K)⁻¹) * x)) χ s
      = (χ c : ℂ) * ((modulus (c : K) : ℝ) : ℂ) ^ s * localZeta μ f χ s := by
  unfold localZeta
  calc ∫ x, f (((c : K)⁻¹) * x) * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s ∂mulMeasure μ
      = ∫ x, f (((c : K)⁻¹) * x) * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s
          ∂Measure.map (mulUnitEquiv c) (mulMeasure μ) := by
        rw [map_mulUnitEquiv_mulMeasure]
    _ = ∫ y, f (((c : K)⁻¹) * ((c : K) * y)) * charExt χ ((c : K) * y) * ((modulus ((c : K) * y) : ℝ) : ℂ) ^ s
          ∂mulMeasure μ := by
        rw [integral_map_equiv]
        rfl
    _ = ∫ y, (χ c : ℂ) * ((modulus (c : K) : ℝ) : ℂ) ^ s * (f y * charExt χ y * ((modulus y : ℝ) : ℂ) ^ s)
          ∂mulMeasure μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        beta_reduce
        rw [charExt_units_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (modulus (c : K)).coe_nonneg (modulus y).coe_nonneg,
          inv_mul_cancel_left₀ c.ne_zero]
        ring
    _ = (χ c : ℂ) * ((modulus (c : K) : ℝ) : ℂ) ^ s
          * ∫ y, f y * charExt χ y * ((modulus y : ℝ) : ℂ) ^ s ∂mulMeasure μ := by
        exact integral_const_mul _ _

end Invariance
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section Domination

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

private theorem norm_zeta_integrand_le (h : K → ℂ) (T : Set K) (B : ℝ) (hB : ∀ x, ‖h x‖ ≤ B)
    (hT : ∀ x, h x ≠ 0 → x ∈ T)
    (χ : Kˣ →* ℂˣ) (hχ : ∀ u, ‖(χ u : ℂ)‖ = 1) (s : ℂ) (hs : 0 < s.re) (x : K) :
    ‖h x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s‖
      ≤ B * (T.indicator (fun _ => (1 : ℂ)) x * charExt (1 : Kˣ →* ℂˣ) x * ((modulus x : ℝ) : ℂ) ^ (s.re : ℂ)).re := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
  by_cases hx : x = 0
  · have hs0 : s ≠ 0 := fun h0 => by simp [h0] at hs
    have hsre : (s.re : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    subst hx
    simp [Complex.zero_cpow hs0, Complex.zero_cpow hsre]
  · have hmod : (0 : ℝ) < modulus x := modulus_pos hx
    rw [charExt_of_ne_zero χ hx, charExt_one_of_ne_zero hx]
    rw [norm_mul, norm_mul, hχ, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos hmod]
    have hcp : ((modulus x : ℝ) : ℂ) ^ (s.re : ℂ) = (((modulus x : ℝ) ^ s.re : ℝ) : ℂ) :=
      (Complex.ofReal_cpow hmod.le s.re).symm
    rw [hcp]
    by_cases hxT : x ∈ T
    · rw [Set.indicator_of_mem hxT]
      simp only [one_mul, Complex.ofReal_re]
      exact mul_le_mul_of_nonneg_right (hB x) (Real.rpow_nonneg hmod.le _)
    · have hx0 : h x = 0 := by
        by_contra hne
        exact hxT (hT x hne)
      rw [Set.indicator_of_notMem hxT, hx0]
      simp

end Domination
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section NormBound

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K]

private theorem norm_localZeta_le (μ : Measure K) (h : K → ℂ) (T : Set K) (B : ℝ) (hB : ∀ x, ‖h x‖ ≤ B)
    (hT : ∀ x, h x ≠ 0 → x ∈ T) (χ : Kˣ →* ℂˣ) (hχ : ∀ u, ‖(χ u : ℂ)‖ = 1) (s : ℂ) (hs : 0 < s.re)
    (hne : localZeta μ (T.indicator fun _ => (1 : ℂ)) 1 (s.re : ℂ) ≠ 0) :
    ‖localZeta μ h χ s‖ ≤ B * (localZeta μ (T.indicator fun _ => (1 : ℂ)) 1 (s.re : ℂ)).re := by
  unfold localZeta at hne ⊢
  have hint : Integrable (fun x => T.indicator (fun _ => (1 : ℂ)) x * charExt (1 : Kˣ →* ℂˣ) x
      * ((modulus x : ℝ) : ℂ) ^ (s.re : ℂ)) (mulMeasure μ) := by
    by_contra hcon
    exact hne (integral_undef hcon)
  calc ‖∫ x, h x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s ∂mulMeasure μ‖
      ≤ ∫ x, B * (T.indicator (fun _ => (1 : ℂ)) x * charExt (1 : Kˣ →* ℂˣ) x
          * ((modulus x : ℝ) : ℂ) ^ (s.re : ℂ)).re ∂mulMeasure μ :=
        norm_integral_le_of_norm_le ((hint.re).const_mul B)
          (Filter.Eventually.of_forall fun x => norm_zeta_integrand_le h T B hB hT χ hχ s hs x)
    _ = B * (∫ x, T.indicator (fun _ => (1 : ℂ)) x * charExt (1 : Kˣ →* ℂˣ) x
          * ((modulus x : ℝ) : ℂ) ^ (s.re : ℂ) ∂mulMeasure μ).re := by
        rw [integral_const_mul]
        congr 1
        exact integral_re hint

end NormBound
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section RealBound

private theorem exists_forall_re_rpow_mul_le (m N V : ℝ) (hm : 0 < m) (hN : 1 < N) (hV : 0 ≤ V) (σ₁ σ₂ : ℝ)
    (hσ₁ : 0 < σ₁) :
    ∃ C : ℝ, ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ σ₂ →
      (((m : ℂ) ^ (σ : ℂ)) * ((V : ℂ) * (1 - (N : ℂ) ^ (-(σ : ℂ)))⁻¹)).re ≤ C := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hden₁ : 0 < 1 - N ^ (-σ₁) := by
    have : N ^ (-σ₁) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN (by linarith)
    linarith
  refine ⟨max (m ^ σ₁) (m ^ σ₂) * (V * (1 - N ^ (-σ₁))⁻¹), fun σ hσ₁σ hσσ₂ => ?_⟩

  have hcast : (((m : ℂ) ^ (σ : ℂ)) * ((V : ℂ) * (1 - (N : ℂ) ^ (-(σ : ℂ)))⁻¹)).re
      = m ^ σ * (V * (1 - N ^ (-σ))⁻¹) := by
    rw [← Complex.ofReal_cpow hm.le, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hN0]
    norm_cast
  rw [hcast]
  have hden : 0 < 1 - N ^ (-σ) := by
    have : N ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN (by linarith)
    linarith
  have h1 : m ^ σ ≤ max (m ^ σ₁) (m ^ σ₂) := by
    rcases le_or_gt 1 m with hm1 | hm1
    · exact (Real.rpow_le_rpow_of_exponent_le hm1 hσσ₂).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hm hm1.le hσ₁σ).trans (le_max_left _ _)
  have h2 : (1 - N ^ (-σ))⁻¹ ≤ (1 - N ^ (-σ₁))⁻¹ := by
    apply inv_anti₀ hden₁
    have : N ^ (-σ) ≤ N ^ (-σ₁) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
    linarith
  have h3 : V * (1 - N ^ (-σ))⁻¹ ≤ V * (1 - N ^ (-σ₁))⁻¹ := mul_le_mul_of_nonneg_left h2 hV
  exact mul_le_mul h1 h3 (mul_nonneg hV (inv_nonneg.2 hden.le)) (le_max_of_le_left (Real.rpow_nonneg hm.le _))

end RealBound
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section Place

open NumberField IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))

attribute [local instance] localBorel borelSpace_localBorel

private theorem two_le_absNorm_asIdeal : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast (two_le_absNorm_asIdeal K v).trans_lt' one_lt_two

private theorem selfDualHaarAt_eq :
    selfDualHaarAt K v
      = ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(addCharLevel (NumberField.StandardAddChar.psiLocal K v) : ℝ) / 2))
          • Measure.addHaarMeasure (integersPositiveCompacts K v) := rfl

private theorem isAddHaarMeasure_selfDualHaarAt : (selfDualHaarAt K v).IsAddHaarMeasure := by
  rw [selfDualHaarAt_eq]
  have hpos : (0 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    exact_mod_cast (two_le_absNorm_asIdeal K v).trans_lt' two_pos
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hpos).ne'

private theorem regular_selfDualHaarAt : (selfDualHaarAt K v).Regular := by
  rw [selfDualHaarAt_eq]
  infer_instance

private theorem stdTestFunAt_one :
    stdTestFunAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ)
      = (v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator fun _ => (1 : ℂ) := by
  rw [stdTestFunAt, if_pos (hasConductorExponentAt_one_zero K v)]

private theorem indicator_smul_set_eq (c : (v.adicCompletion K)ˣ) :
    (((c : v.adicCompletion K) • (v.adicCompletionIntegers K : Set (v.adicCompletion K))).indicator
        fun _ => (1 : ℂ))
      = fun x => (v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator (fun _ => (1 : ℂ))
          (((c : v.adicCompletion K)⁻¹) * x) := by
  funext x
  by_cases hx : x ∈ (c : v.adicCompletion K) • (v.adicCompletionIntegers K : Set (v.adicCompletion K))
  · have hx' := (Set.mem_smul_set_iff_inv_smul_mem₀ c.ne_zero _ _).1 hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem (by simpa [smul_eq_mul] using hx')]
  · have hx' : ((c : v.adicCompletion K)⁻¹) * x ∉ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := fun h =>
      hx ((Set.mem_smul_set_iff_inv_smul_mem₀ c.ne_zero _ _).2 (by simpa [smul_eq_mul] using h))
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']

private theorem localZeta_indicator_ball (c : (v.adicCompletion K)ˣ) (σ : ℝ) (hσ : 0 < σ) :
    localZeta (selfDualHaarAt K v)
        (((c : v.adicCompletion K) • (v.adicCompletionIntegers K : Set (v.adicCompletion K))).indicator
          fun _ => (1 : ℂ)) 1 (σ : ℂ)
      = ((modulus (c : v.adicCompletion K) : ℝ) : ℂ) ^ (σ : ℂ)
          * (((selfDualHaarAt K v).real {x | Valued.v x = 1} : ℂ)
              * (1 - ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-(σ : ℂ)))⁻¹) := by
  haveI := isAddHaarMeasure_selfDualHaarAt K v
  haveI := regular_selfDualHaarAt K v
  rw [indicator_smul_set_eq, localZeta_comp_inv_mul, MonoidHom.one_apply, Units.val_one, one_mul,
    ← stdTestFunAt_one, localZeta_stdTestFunAt_eq_of_unramified K v 1 (σ : ℂ) (hasConductorExponentAt_one_zero K v),
    localLFactorAt_one]
  · push_cast
    ring_nf
  · rw [MonoidHom.one_apply, Units.val_one, norm_one, one_mul, Complex.ofReal_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (one_lt_absNorm_real K v) (by linarith)

private theorem units_real_pos : 0 < (selfDualHaarAt K v).real {x | Valued.v x = 1} := by
  rw [selfDualHaarAt_real_units_eq K v]
  have hN := one_lt_absNorm_real K v
  have h1 : (0 : ℝ) < 1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    rw [sub_pos]
    exact inv_lt_one_of_one_lt₀ hN
  exact mul_pos h1 (Real.rpow_pos_of_pos (by linarith) _)

private theorem exists_forall_norm_localZeta_le (χ : (v.adicCompletion K)ˣ →* ℂˣ) (hχ : ∀ u, ‖(χ u : ℂ)‖ = 1)
    (h : v.adicCompletion K → ℂ) (c : (v.adicCompletion K)ˣ) (B : ℝ) (hB : ∀ y, ‖h y‖ ≤ B)
    (hsupp : Function.support h
      ⊆ (c : v.adicCompletion K) • (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (σ₁ σ₂ : ℝ) (hσ₁ : 0 < σ₁) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖localZeta (selfDualHaarAt K v) h χ s‖ ≤ C := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hm : (0 : ℝ) < (modulus (c : v.adicCompletion K) : ℝ) := by exact_mod_cast modulus_pos c.ne_zero
  obtain ⟨C₀, hC₀⟩ := exists_forall_re_rpow_mul_le (modulus (c : v.adicCompletion K) : ℝ) (Ideal.absNorm v.asIdeal : ℝ)
    ((selfDualHaarAt K v).real {x | Valued.v x = 1}) hm (one_lt_absNorm_real K v) (units_real_pos K v).le σ₁ σ₂ hσ₁
  refine ⟨B * C₀, fun s hs₁ hs₂ => ?_⟩
  have hs : 0 < s.re := hσ₁.trans_le hs₁
  have hval := localZeta_indicator_ball K v c s.re hs
  have hne : localZeta (selfDualHaarAt K v)
      (((c : v.adicCompletion K) • (v.adicCompletionIntegers K : Set (v.adicCompletion K))).indicator
        fun _ => (1 : ℂ)) 1 (s.re : ℂ) ≠ 0 := by
    rw [hval]
    have hq : ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-(s.re : ℂ))
        = (((Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by linarith [one_lt_absNorm_real K v]), Complex.ofReal_neg]
    have hlt : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (one_lt_absNorm_real K v) (by linarith)
    refine mul_ne_zero ?_ (mul_ne_zero ?_ (inv_ne_zero ?_))
    · rw [← Complex.ofReal_cpow hm.le]
      exact_mod_cast (Real.rpow_pos_of_pos hm _).ne'
    · exact_mod_cast (units_real_pos K v).ne'
    · rw [hq]
      exact_mod_cast (sub_pos.2 hlt).ne'
  calc ‖localZeta (selfDualHaarAt K v) h χ s‖
      ≤ B * (localZeta (selfDualHaarAt K v)
          (((c : v.adicCompletion K) • (v.adicCompletionIntegers K : Set (v.adicCompletion K))).indicator
            fun _ => (1 : ℂ)) 1 (s.re : ℂ)).re :=
        norm_localZeta_le (selfDualHaarAt K v) h _ B hB (fun x hx => hsupp hx) χ hχ s hs hne
    _ ≤ B * C₀ := by
        rw [hval]
        exact mul_le_mul_of_nonneg_left (hC₀ s.re hs₁ hs₂) hB0

end Place
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end ZetaTransport
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end LocalZetaStripBound
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section DualSlots

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox CharacterDual CosetTensor TensorFactorization
open scoped Pointwise

namespace DualSlots

variable {F : Type} [Field F] [NumberField F]

private theorem units_mul_mem_smul_iff (v : HeightOneSpectrum (𝓞 F)) (a c : (v.adicCompletion F)ˣ)
    (y : v.adicCompletion F) (A : Set (v.adicCompletion F)) :
    (a : v.adicCompletion F) * y ∈ (c : v.adicCompletion F) • A ↔
      y ∈ ((a⁻¹ * c : (v.adicCompletion F)ˣ) : v.adicCompletion F) • A := by
  have key : (((a⁻¹ * c : (v.adicCompletion F)ˣ) : v.adicCompletion F))⁻¹ * y =
      (c : v.adicCompletion F)⁻¹ * ((a : v.adicCompletion F) * y) := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv, inv_inv]
    ring
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ c.ne_zero, Set.mem_smul_set_iff_inv_smul_mem₀ (a⁻¹ * c).ne_zero,
    smul_eq_mul, smul_eq_mul, key]

open scoped Classical in

private theorem exists_finset_units_ite_eq_finiteTensor (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (hc : IsCompact (characterDual ψ)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (c : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
      ∀ w : FiniteAdeleRing (𝓞 F) F,
        (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, unitOn S u * w * z) = 1 then (1 : ℂ) else 0) =
          finiteTensor (S ∪ T) (fun v y =>
            if y ∈ (c v : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)) then 1
            else 0) w := by
  obtain ⟨T, hT⟩ := exists_finset_forall_localCharacterDual_eq hψ hc
  choose c' hc' using exists_units_smul_eq_localCharacterDual hψ hc
  let c : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ := fun v => if v ∈ S then (u v)⁻¹ * c' v else c' v
  refine ⟨T, c, fun w => ?_⟩

  have hplace : ∀ v : HeightOneSpectrum (𝓞 F), (unitOn S u * w) v ∈ localCharacterDual ψ v ↔
      w v ∈ (c v : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    show unitOn S u v * w v ∈ localCharacterDual ψ v ↔ _
    rw [hc' v]
    by_cases hv : v ∈ S
    · rw [unitOn_apply_of_mem (S := S) (u := u) hv, show c v = (u v)⁻¹ * c' v from if_pos hv]
      exact units_mul_mem_smul_iff v (u v) (c' v) (w v) _
    · rw [unitOn_apply_of_not_mem (S := S) (u := u) hv, one_mul, show c v = c' v from if_neg hv]
  have hsplit : (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, unitOn S u * w * z) = 1) ↔
      (∀ v ∈ S ∪ T,
          w v ∈ (c v : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∧
        (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S ∪ T → w v ∈ v.adicCompletionIntegers F) := by
    change unitOn S u * w ∈ characterDual ψ ↔ _
    rw [mem_characterDual_iff hψ]
    constructor
    · intro h
      refine ⟨fun v _ => (hplace v).mp (h v), fun v hv => ?_⟩
      rw [Finset.mem_union, not_or] at hv
      have h1 := h v
      rw [hT v hv.2] at h1
      have h2 : (unitOn S u * w) v = w v := by
        show unitOn S u v * w v = w v
        rw [unitOn_apply_of_not_mem (S := S) (u := u) hv.1, one_mul]
      rw [h2] at h1
      exact h1
    · rintro ⟨h1, h2⟩ v
      by_cases hv : v ∈ S ∪ T
      · exact (hplace v).mpr (h1 v hv)
      · have hv' := hv
        rw [Finset.mem_union, not_or] at hv'
        rw [hT v hv'.2]
        show unitOn S u v * w v ∈ _
        rw [unitOn_apply_of_not_mem (S := S) (u := u) hv'.1, one_mul]
        exact h2 v hv
  rw [finiteTensor_apply, Finset.prod_boole, ite_zero_mul_ite_zero, one_mul]
  by_cases h : ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, unitOn S u * w * z) = 1
  · rw [if_pos h, if_pos (hsplit.mp h)]
  · rw [if_neg h, if_neg fun h' => h (hsplit.mpr h')]

end DualSlots
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end DualSlots
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section TensorInsert

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace TensorFactorization

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

private theorem finiteTensor_insert_eq_mul (S₁ : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) {v₀ : HeightOneSpectrum (𝓞 F)}
    (hv₀ : v₀ ∉ S₁) (K : ℂ)
    (hh : ∀ y, h v₀ y = K * (if y ∈ v₀.adicCompletionIntegers F then 1 else 0))
    (x : FiniteAdeleRing (𝓞 F) F) :
    finiteTensor (insert v₀ S₁) h x = K * finiteTensor S₁ h x := by
  have hiff :
      (x v₀ ∈ v₀.adicCompletionIntegers F ∧
          ∀ v : HeightOneSpectrum (𝓞 F), v ∉ insert v₀ S₁ → x v ∈ v.adicCompletionIntegers F) ↔
        ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S₁ → x v ∈ v.adicCompletionIntegers F := by
    constructor
    · rintro ⟨h0, hrest⟩ v hv
      by_cases hv0 : v = v₀
      · subst hv0
        exact h0
      · exact hrest v (by simp only [Finset.mem_insert, not_or]; exact ⟨hv0, hv⟩)
    · intro hall
      exact ⟨hall v₀ hv₀, fun v hv => hall v fun hvS => hv (Finset.mem_insert_of_mem hvS)⟩
  have key :
      (if x v₀ ∈ v₀.adicCompletionIntegers F then (1 : ℂ) else 0) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ insert v₀ S₁ → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)
        = if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S₁ → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0 := by
    simp only [ite_zero_mul_ite_zero, one_mul, hiff]
  rw [finiteTensor_apply, finiteTensor_apply, Finset.prod_insert hv₀, hh (x v₀), ← key]
  ring

end TensorFactorization
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end TensorInsert
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section TensorTransform

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicFourier LanglandsTunnell.ArchPlace IsDedekindDomain TensorFactorization

namespace TensorTransform

variable {F : Type} [Field F] [NumberField F]

private theorem exists_fourierIntegral_adelicTensor_eq
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hψinf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (a : {w : InfinitePlace F // w.IsReal} → ZMod 2) (k : {w : InfinitePlace F // w.IsComplex} → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) :
    ∃ C : ℂ, ∀ w : AdeleRing (𝓞 F) F,
      fourierIntegral ψ μ (adelicTensor (fun w => realTestFun (a w)) (fun w => complexTestFun (k w)) S h) w
        = C * mixedTensor (fun w => realTestFun (a w)) (fun w => complexTestFun (-k w))
              (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
            * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr _ _)) ν (finiteTensor S h) w.2 := by
  classical
  set ψ' : AddChar (mixedEmbedding.mixedSpace F) ℂ :=
    ψ.compAddMonoidHom
      ((AddMonoidHom.inl _ _).comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom) with hψ'
  have hψ'eq : ∀ v : mixedEmbedding.mixedSpace F,
      ψ' v = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) v) : ℂ) := fun v => by
    have hv := hψinf ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm v)
    rw [RingEquiv.apply_symm_apply] at hv
    exact hv
  have hpos : 0 < μ (adelicBox F) := by
    obtain ⟨U, hU, hne, hsub⟩ := exists_isOpen_subset_adelicBox F
    exact (hU.measure_pos μ hne).trans_le (measure_mono hsub)
  have hfin : μ (adelicBox F) < ⊤ := by
    obtain ⟨K₀, hK₀, hsub⟩ := exists_isCompact_adelicBox_subset F
    exact (measure_mono hsub).trans_lt hK₀.measure_lt_top
  have hμ : ((μ (adelicBox F)).toReal : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  refine ⟨((μ (adelicBox F)).toReal : ℂ)
      * (((2 : ℝ) ^ InfinitePlace.nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
      * ((∏ w, (-Complex.I) ^ (a w).val) * (∏ w, (-Complex.I) ^ (k w).natAbs)
          * (1 / 2 : ℂ) ^ InfinitePlace.nrComplexPlaces F)
      * (((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ))⁻¹, fun w => ?_⟩
  have h1 := EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq F μ ν ψ
    (mixedTensor (fun w => realTestFun (a w)) (fun w => complexTestFun (k w))) (finiteTensor S h) w
  have h2 : (fun x : AdeleRing (𝓞 F) F =>
        mixedTensor (fun w => realTestFun (a w)) (fun w => complexTestFun (k w))
            (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
          * finiteTensor S h x.2)
      = adelicTensor (fun w => realTestFun (a w)) (fun w => complexTestFun (k w)) S h :=
    funext fun x => (adelicTensor_apply _ _ S h x).symm
  have h3 := LanglandsTunnell.ArchPlace.fourierIntegral_mixedSpace_pureTensor F a k ψ' hψ'eq
    (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
  have h4 : (fun v : mixedEmbedding.mixedSpace F =>
        (∏ w', realTestFun (a w') (v.1 w')) * ∏ w', complexTestFun (k w') (v.2 w'))
      = mixedTensor (fun w => realTestFun (a w)) (fun w => complexTestFun (k w)) :=
    funext fun v => (mixedTensor_apply _ _ v).symm
  rw [h4] at h3
  rw [h2, h3, inv_mul_eq_iff_eq_mul₀ hμ] at h1
  rw [h1]
  simp only [mixedTensor_apply]
  ring

end TensorTransform
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end TensorTransform
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section TransformedTensor

set_option autoImplicit false

open MeasureTheory NumberField NumberField.TateGlobal NumberField.AdelicFourier NumberField.AdelicBox LanglandsTunnell.ArchPlace AutomorphicForm IsDedekindDomain TensorFactorization CosetTensor

open scoped Pointwise

namespace TransformedTensor

variable {F : Type} [Field F] [NumberField F]

section FiniteAdelicHaar

private noncomputable abbrev finiteBorel : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _

attribute [local instance] finiteBorel

private theorem finiteBorel_borelSpace : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

attribute [local instance] finiteBorel_borelSpace

private noncomputable def integralCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing (𝓞 F) F) :=
  ⟨⟨integralFiniteAdeles (𝓞 F) F, isCompact_integralFiniteAdeles F⟩, by
    rw [(isOpen_integralFiniteAdeles F).interior_eq]
    exact ⟨0, fun v => show (0 : v.adicCompletion F) ∈ v.adicCompletionIntegers F from zero_mem _⟩⟩

private theorem exists_isAddHaarMeasure : ∃ ν : Measure (FiniteAdeleRing (𝓞 F) F), ν.IsAddHaarMeasure :=
  ⟨Measure.addHaarMeasure (integralCompacts (F := F)), inferInstance⟩

end FiniteAdelicHaar
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

private theorem exists_isFactorizableStandardOutside_fourierIntegral_adelicTensor_cosetIndicator
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (hψinf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (a : {w : InfinitePlace F // w.IsReal} → ZMod 2) (k : {w : InfinitePlace F // w.IsComplex} → ℤ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (α : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F)
    (u : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) :
    ∃ (S' : Finset (HeightOneSpectrum (𝓞 F))) (h' : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ),
      S ⊆ S' ∧
      IsFactorizableStandardOutside
        (fourierIntegral ψ μ
          (adelicTensor (fun w => realTestFun (a w)) (fun w => complexTestFun (k w)) S (cosetIndicator α u)))
        S' (placeFactor (fun w => realTestFun (a w)) (fun w => complexTestFun (-k w))) h' ∧
      ∀ v ∈ S', ∃ (c : (v.adicCompletion F)ˣ) (B : ℝ), (∀ y, ‖h' v y‖ ≤ B) ∧
        Function.support (h' v)
          ⊆ (c : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  classical

  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := finiteBorel
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := finiteBorel_borelSpace
  obtain ⟨ν, hνH⟩ := exists_isAddHaarMeasure (F := F)
  haveI : ν.IsAddHaarMeasure := hνH

  have hψc : Continuous ψ := hψ.continuous
  have hψf : Continuous (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) := by
    show Continuous fun x : FiniteAdeleRing (𝓞 F) F => ψ ((0 : InfiniteAdeleRing F), x)
    fun_prop

  have hc : IsCompact (CharacterDual.characterDual ψ) :=
    (NumberField.AdelicFourier.isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one F hψ hψinf).1
  obtain ⟨T, c, hTc⟩ := DualSlots.exists_finset_units_ite_eq_finiteTensor ψ hψc hc S u
  obtain ⟨C, hC⟩ := TensorTransform.exists_fourierIntegral_adelicTensor_eq μ ν ψ hψinf a k S (cosetIndicator α u)

  set slots : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ := fun v y =>
    if y ∈ (c v : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)) then 1 else 0
    with hslots
  set N : ℂ := ((ν ((fun z => spliceOn S α + unitOn S u * z) '' integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) with hN
  have hfin : ∀ w₂ : FiniteAdeleRing (𝓞 F) F,
      fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) ν
          (finiteTensor S (cosetIndicator α u)) w₂
        = (∏ v ∈ S, ψ (0, AdelicDock.splice (𝓞 F) F v 0 (-(α v * w₂ v)))) * N * finiteTensor (S ∪ T) slots w₂ := by
    intro w₂
    have hif : (if ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
          (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
            (unitOn S u * w₂ * z) = 1 then (1 : ℂ) else 0) = finiteTensor (S ∪ T) slots w₂ := hTc w₂
    have hphase : (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
        (-(spliceOn S α * w₂)) = ∏ v ∈ S, ψ (0, AdelicDock.splice (𝓞 F) F v 0 (-(α v * w₂ v))) :=
      psi_neg_spliceOn_mul ψ S α w₂
    rw [finiteTensor_cosetIndicator_eq,
      NumberField.AdelicFourier.fourierIntegral_indicator_coset_finiteAdeleRing_apply F ν hψf, hphase, hif]

  obtain ⟨v₀⟩ := NumberField.AdelicTrace.nonempty_heightOneSpectrum F
  set K : ℂ := C * N with hK
  set c' : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ := fun v => if v ∈ S ∪ T then c v else 1 with hc'
  set h' : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ := fun v y =>
    (if v = v₀ then K else 1) * (if v ∈ S then ψ (0, AdelicDock.splice (𝓞 F) F v 0 (-(α v * y))) else 1)
      * (if y ∈ (c' v : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)) then 1 else 0)
    with hh'

  have hkey : ∀ w₂ : FiniteAdeleRing (𝓞 F) F, finiteTensor (insert v₀ (S ∪ T)) h' w₂
      = K * ((∏ v ∈ S, ψ (0, AdelicDock.splice (𝓞 F) F v 0 (-(α v * w₂ v)))) * finiteTensor (S ∪ T) slots w₂) := by
    intro w₂
    have hunion : finiteTensor (S ∪ T) h' w₂
        = (if v₀ ∈ S ∪ T then K else 1)
          * ((∏ v ∈ S, ψ (0, AdelicDock.splice (𝓞 F) F v 0 (-(α v * w₂ v)))) * finiteTensor (S ∪ T) slots w₂) := by
      have hinter : (S ∪ T) ∩ S = S := by
        ext v
        simp only [Finset.mem_inter, Finset.mem_union]
        tauto
      have hslot : ∀ v ∈ S ∪ T, (if w₂ v ∈ (c' v : v.adicCompletion F) • (v.adicCompletionIntegers F :
          Set (v.adicCompletion F)) then (1 : ℂ) else 0) = slots v (w₂ v) := fun v hv => by
        simp only [hc', hslots, if_pos hv]
      rw [finiteTensor_apply, finiteTensor_apply, hh']
      beta_reduce
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_mem, hinter,
        Finset.prod_congr rfl hslot]
      ring
    by_cases hv : v₀ ∈ S ∪ T
    · rw [Finset.insert_eq_of_mem hv, hunion, if_pos hv]
    · have hvS : v₀ ∉ S := fun h => hv (Finset.mem_union_left T h)
      have hone : ((1 : (v₀.adicCompletion F)ˣ) : v₀.adicCompletion F)
          • (v₀.adicCompletionIntegers F : Set (v₀.adicCompletion F)) = v₀.adicCompletionIntegers F := by
        rw [Units.val_one, one_smul]
      have hh₀ : ∀ y, h' v₀ y = K * (if y ∈ v₀.adicCompletionIntegers F then 1 else 0) := fun y => by
        simp only [hh', hc', if_true, if_neg hvS, if_neg hv, hone, SetLike.mem_coe, mul_one]
      rw [TensorFactorization.finiteTensor_insert_eq_mul (S ∪ T) h' hv K hh₀, hunion, if_neg hv, one_mul]
  refine ⟨insert v₀ (S ∪ T), h', fun v hv => Finset.mem_insert_of_mem (Finset.mem_union_left T hv), ?_, ?_⟩
  ·
    refine isFactorizableStandardOutside_of_forall_eq _ _ _ _ _ fun x => ?_
    rw [hC x, adelicTensor_apply, hfin x.2, hkey x.2, hK]
    ring
  ·
    intro v _
    refine ⟨c' v, max 1 ‖K‖, fun y => ?_, fun y hy => ?_⟩
    · have hA : ‖(if v = v₀ then K else (1 : ℂ))‖ ≤ max 1 ‖K‖ := by
        split_ifs
        · exact le_max_right _ _
        · rw [norm_one]
          exact le_max_left _ _
      have hP : ‖(if v ∈ S then ψ (0, AdelicDock.splice (𝓞 F) F v 0 (-(α v * y))) else (1 : ℂ))‖ ≤ 1 := by
        split_ifs
        · exact (NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar F hψ _).le
        · rw [norm_one]
      have hI : ‖(if y ∈ (c' v : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
          then (1 : ℂ) else 0)‖ ≤ 1 := by
        split_ifs
        · rw [norm_one]
        · rw [norm_zero]
          exact zero_le_one
      have h0 : (0 : ℝ) ≤ max 1 ‖K‖ := le_max_of_le_left zero_le_one
      calc ‖h' v y‖ = ‖(if v = v₀ then K else 1)‖
            * ‖(if v ∈ S then ψ (0, AdelicDock.splice (𝓞 F) F v 0 (-(α v * y))) else (1 : ℂ))‖
            * ‖(if y ∈ (c' v : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
                then (1 : ℂ) else 0)‖ := by
              rw [hh']
              simp only [norm_mul]
        _ ≤ max 1 ‖K‖ * 1 * 1 :=
              mul_le_mul (mul_le_mul hA hP (norm_nonneg _) h0) hI (norm_nonneg _) (by positivity)
        _ = max 1 ‖K‖ := by ring
    · by_contra hmem
      exact Function.mem_support.mp hy (by simp only [hh', if_neg hmem, mul_zero])

end TransformedTensor
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end TransformedTensor
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section HeckeDual

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal

noncomputable section

namespace HeckeDual

section Helpers

open MeasureTheory LanglandsTunnell.TateLocal

variable (F : Type) [Field F] [NumberField F]

private theorem isAddHaarMeasure_heckeMu :
    letI := AdelicHaar.adeleBorel (𝓞 F) F
    (HeckeObjects.heckeMu F).IsAddHaarMeasure := by
  letI := AdelicHaar.adeleBorel (𝓞 F) F
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  unfold HeckeObjects.heckeMu
  exact Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 (AdelicBox.measure_adelicBox_lt_top F _).ne)
    (ENNReal.inv_ne_top.2 (AdelicBox.measure_adelicBox_pos F _).ne')

private theorem isAddHaarMeasure_selfDualHaarAt (v : HeightOneSpectrum (𝓞 F)) :
    letI := localBorel F v
    (selfDualHaarAt F v).IsAddHaarMeasure := by
  letI := localBorel F v
  haveI := borelSpace_localBorel F v
  unfold selfDualHaarAt
  refine Measure.IsAddHaarMeasure.nnreal_smul _ ?_
  have hN : (0 : NNReal) < (Ideal.absNorm v.asIdeal : NNReal) := by
    exact_mod_cast zero_lt_one.trans (EulerSpellingBridge.one_lt_absNorm F v)
  exact (NNReal.rpow_pos hN).ne'

variable {F}

open scoped Classical in

private theorem prod_localZeta_archMeasure_inv [∀ w : InfinitePlace F, MeasurableSpace w.Completion]
    [∀ w : InfinitePlace F, BorelSpace w.Completion] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (ur : {w : InfinitePlace F // w.IsReal} → ℂ) (ar : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (hreal : ∀ (i : {w : InfinitePlace F // w.IsReal}) (x : (i.1.Completion)ˣ),
      χ (NumberField.TateGlobal.archUnitHom i.1 x) = LanglandsTunnell.ArchPlace.realCharFun (ur i) (ar i)
        (Units.map (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal i.2).toMonoidHom x))
    (uc : {w : InfinitePlace F // w.IsComplex} → ℂ) (kc : {w : InfinitePlace F // w.IsComplex} → ℤ)
    (hcomplex : ∀ (j : {w : InfinitePlace F // w.IsComplex}) (z : (j.1.Completion)ˣ),
      χ (NumberField.TateGlobal.archUnitHom j.1 z) = LanglandsTunnell.ArchPlace.complexCharFun (uc j) (kc j)
        (Units.map (NumberField.InfinitePlace.Completion.extensionEmbedding j.1).toMonoidHom z))
    (hur : ∀ i, (ur i).re = 0) (huc : ∀ j, (uc j).re = 0) (s : ℂ) (hs : 1 < s.re) :
    ∏ w, LanglandsTunnell.TateLocal.localZeta (ZetaTransport.archMeasure w)
        (TensorFactorization.placeFactor (fun w => LanglandsTunnell.ArchPlace.realTestFun (ar w))
          (fun w => LanglandsTunnell.ArchPlace.complexTestFun (-kc w)) w) (archLocalChar χ⁻¹ w) s
      = (∏ i : {w : InfinitePlace F // w.IsReal}, Complex.Gammaℝ (s + (-ur i + LanglandsTunnell.signShift (ar i))))
        * ((Real.pi : ℂ) ^ Fintype.card {w : InfinitePlace F // w.IsComplex}
          * ∏ j : {w : InfinitePlace F // w.IsComplex}, Complex.Gammaℂ (s + (-uc j + ((kc j).natAbs : ℂ) / 2))) := by
  have h := ArchProduct.prod_localZeta_archMeasure χ⁻¹ (-ur) ar
    (InverseCharacter.inv_archUnitHom_eq_realCharFun χ ur ar hreal) (-uc) (-kc)
    (InverseCharacter.inv_archUnitHom_eq_complexCharFun χ uc kc hcomplex)
    (fun i => InverseCharacter.re_neg_eq_zero (hur i)) (fun j => InverseCharacter.re_neg_eq_zero (huc j)) s hs
  simpa only [Pi.neg_apply, Int.natAbs_neg] using h

end Helpers
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

open HeckeObjects MeasureTheory NumberField.AdelicFourier

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in

private theorem heckeDual
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 F) F χ)
    (ur : {w : InfinitePlace F // w.IsReal} → ℂ) (ar : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (_hreal : ∀ (i : {w : InfinitePlace F // w.IsReal}) (x : (i.1.Completion)ˣ),
      χ (NumberField.TateGlobal.archUnitHom i.1 x) =
        LanglandsTunnell.ArchPlace.realCharFun (ur i) (ar i)
          (Units.map
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal i.2).toMonoidHom x))
    (uc : {w : InfinitePlace F // w.IsComplex} → ℂ) (kc : {w : InfinitePlace F // w.IsComplex} → ℤ)
    (_hcomplex : ∀ (j : {w : InfinitePlace F // w.IsComplex}) (z : (j.1.Completion)ˣ),
      χ (NumberField.TateGlobal.archUnitHom j.1 z) =
        LanglandsTunnell.ArchPlace.complexCharFun (uc j) (kc j)
          (Units.map
            (NumberField.InfinitePlace.Completion.extensionEmbedding j.1).toMonoidHom z))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (_hS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → IsUnramifiedCharAt χ v)
    (e : HeightOneSpectrum (𝓞 F) → ℕ) :
    ∃ (S' : Finset (HeightOneSpectrum (𝓞 F))) (D : ℂ → ℂ), S ⊆ S' ∧
      (∀ σ₂ : ℝ, ∃ D₀ : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ σ₂ → ‖D s‖ ≤ D₀) ∧
      ∀ s : ℂ, 1 < s.re →
        dualZeta F χ ar kc S e s
          = D s
            * (∏ i : {w : InfinitePlace F // w.IsReal},
                Complex.Gammaℝ (s + (-ur i + LanglandsTunnell.signShift (ar i))))
            * (∏ j : {w : InfinitePlace F // w.IsComplex}, Complex.Gammaℂ (s + (-uc j + ((kc j).natAbs : ℂ) / 2)))
            * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S'},
                (1 - (((χ (uniformizerIdele F v.1))⁻¹ : ℂˣ) : ℂ)
                  * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by

  letI := Idele.ideleBorel F
  haveI := Idele.borelSpace_ideleBorel F
  haveI := Idele.isHaarMeasure_idelicHaar F
  letI := AdelicHaar.adeleBorel (𝓞 F) F
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_heckeMu F
  letI : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) := fun v =>
    LanglandsTunnell.TateLocal.localBorel F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) := fun v =>
    LanglandsTunnell.TateLocal.borelSpace_localBorel F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), (LanglandsTunnell.TateLocal.selfDualHaarAt F v).IsAddHaarMeasure := fun v =>
    isAddHaarMeasure_selfDualHaarAt F v
  letI : ∀ w : InfinitePlace F, MeasurableSpace w.Completion := fun _ => borel _
  haveI : ∀ w : InfinitePlace F, BorelSpace w.Completion := fun _ => ⟨rfl⟩
  haveI : ∀ w : InfinitePlace F, (ZetaTransport.archMeasure w).IsAddHaarMeasure := fun w =>
    ZetaTransport.isAddHaarMeasure_archMeasure w

  have hχc' : Continuous χ⁻¹ := InverseCharacter.continuous_inv_of_continuous _hχc
  have hχu' : IsUnitaryChar (𝓞 F) F χ⁻¹ := InverseCharacter.isUnitaryChar_inv _hχu
  have hur : ∀ i, (ur i).re = 0 := fun i =>
    UnitaryExponent.re_eq_zero_of_isUnitaryChar_of_forall_eq_realCharFun _hχu (_hreal i)
  have huc : ∀ j, (uc j).re = 0 := fun j =>
    UnitaryExponent.re_eq_zero_of_isUnitaryChar_of_forall_eq_complexCharFun _hχu j.2 (_hcomplex j)

  obtain ⟨S', h', hSS', hfac, hslots⟩ :=
    TransformedTensor.exists_isFactorizableStandardOutside_fourierIntegral_adelicTensor_cosetIndicator (heckeMu F)
      (StandardAddChar.stdAddChar F) (StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK
      (StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace F) ar kc S (fun _ => 1)
      (fun v => AdelicLevel.uniformizerUnit F v ^ e v)
  have hS' : ∀ v ∉ S', IsUnramifiedCharAt χ⁻¹ v := fun v hv =>
    InverseCharacter.isUnramifiedCharAt_inv (_hS v fun h => hv (hSS' h))

  obtain ⟨c, _hc, hfact⟩ := zetaIntegral_mul_eulerFactors_eq F (Idele.idelicHaar F) S'
    (fun v => LanglandsTunnell.TateLocal.selfDualHaarAt F v) (fun w => ZetaTransport.archMeasure w)
    (fun v => AdelicLevel.uniformizerUnit F v) (fun v => UnramifiedLocalData.valued_uniformizerUnit_eq_ofAdd_neg_one v)
  set n : ℕ := Fintype.card {w : InfinitePlace F // w.IsComplex}
  set Q : ℂ → ℂ := fun t : ℂ =>
    ∏ v ∈ S', LanglandsTunnell.TateLocal.localZeta (LanglandsTunnell.TateLocal.selfDualHaarAt F v) (h' v)
      (localChar χ⁻¹ v) t
  refine ⟨S', fun s => ((c : ℂ) * (Real.pi : ℂ) ^ n) * Q s, hSS', fun σ₂ => ?_, fun s hs => ?_⟩
  ·
    obtain ⟨D₀, hD₀⟩ := HeckeAuxiliary.exists_forall_norm_finset_prod_le S'
      (fun v t => LanglandsTunnell.TateLocal.localZeta (LanglandsTunnell.TateLocal.selfDualHaarAt F v) (h' v)
        (localChar χ⁻¹ v) t) σ₂ fun v hv => by
          obtain ⟨cv, B, hB, hsupp⟩ := hslots v hv
          exact ZetaTransport.exists_forall_norm_localZeta_le F v (localChar χ⁻¹ v)
            (UnramifiedLocalData.norm_localChar_eq_one hχu' v) (h' v) cv B hB hsupp 1 σ₂ one_pos
    refine ⟨‖(c : ℂ) * (Real.pi : ℂ) ^ n‖ * D₀, fun s hs1 hs2 => ?_⟩
    calc ‖((c : ℂ) * (Real.pi : ℂ) ^ n) * Q s‖ = ‖(c : ℂ) * (Real.pi : ℂ) ^ n‖ * ‖Q s‖ := norm_mul _ _
      _ ≤ ‖(c : ℂ) * (Real.pi : ℂ) ^ n‖ * D₀ := mul_le_mul_of_nonneg_left (hD₀ s hs1 hs2) (norm_nonneg _)
  ·
    set A : ℂ :=
      ∏ i : {w : InfinitePlace F // w.IsReal}, Complex.Gammaℝ (s + (-ur i + LanglandsTunnell.signShift (ar i)))

    set B : ℂ :=
      ∏ j : {w : InfinitePlace F // w.IsComplex}, Complex.Gammaℂ (s + (-uc j + ((kc j).natAbs : ℂ) / 2))
    set Pk : ℂ := ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S'},
      (1 - (((χ (uniformizerIdele F v.1))⁻¹ : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))
    set Pi : ℂ := ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S'},
      (1 - (((χ (uniformizerIdele F v.1))⁻¹ : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹
    set zh : ℂ := zetaIntegral (Idele.idelicHaar F)
      (fourierIntegral (StandardAddChar.stdAddChar F) (heckeMu F) (testTensor F ar kc S e)) χ⁻¹ s
    have hrow := hfact _ _ _ hfac χ⁻¹ hχc' hχu' hS' s hs
    have harch : _ = A * ((Real.pi : ℂ) ^ n * B) :=
      prod_localZeta_archMeasure_inv χ ur ar _hreal uc kc _hcomplex hur huc s hs
    have hP : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S'},
          (1 - ((localChar χ⁻¹ v.1 (AdelicLevel.uniformizerUnit F v.1) : ℂˣ) : ℂ)
            * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))) = Pk :=
      tprod_congr fun v => by
        rw [InverseCharacter.localChar_inv, MonoidHom.inv_apply, UnramifiedLocalData.localChar_uniformizerUnit]
    have hz : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S'}, ‖(((χ (uniformizerIdele F v.1))⁻¹ : ℂˣ) : ℂ)‖ ≤ 1 :=
      fun v => by
        rw [Units.val_inv_eq_inv_val, norm_inv, _hχu (uniformizerIdele F v.1)]
        exact inv_one.le
    have hF2 : Pk * Pi = 1 :=
      HeckeAuxiliary.tprod_mul_tprod_inv_eq_one S' (fun v => (((χ (uniformizerIdele F v.1))⁻¹ : ℂˣ) : ℂ)) hz s hs
    have hrow2 : zh * Pk = (c : ℂ) * (A * ((Real.pi : ℂ) ^ n * B)) * Q s := by
      rw [← hP, ← harch]
      exact hrow
    show zh = ((c : ℂ) * (Real.pi : ℂ) ^ n) * Q s * A * B * Pi
    rw [show zh = zh * (Pk * Pi) by rw [hF2, mul_one], ← mul_assoc, hrow2]
    ring

end HeckeDual
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end HeckeDual
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

section HeckeFunctionalEquation

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal

noncomputable section

namespace HeckeFunctionalEquation

private theorem re_natCast_div_two_nonneg (n : ℕ) : 0 ≤ ((n : ℂ) / 2).re := by
  rw [Complex.div_ofNat_re, Complex.natCast_re]
  positivity

end HeckeFunctionalEquation
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

open HeckeObjects HeckeCore HeckeDual HeckeAuxiliary InverseCharacter HeckeFunctionalEquation in

private theorem HeckeFunctionalEquation.exists_entire_functionalEquation
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hχ : IsIdeleClassChar (𝓞 K) K χ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 K) K χ)
    (_hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1) :
    ∃ (S S' : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (c d : Fin m → ℂ) (Z D : ℂ → ℂ) (C₀ : ℂ),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ S ↔ ¬ IsUnramifiedCharAt χ v) ∧ S ⊆ S' ∧ C₀ ≠ 0 ∧
      (∀ j, 0 ≤ (c j).re) ∧ (∀ j, 0 ≤ (d j).re) ∧ Differentiable ℂ Z ∧
      (∀ σ₁ σ₂ : ℝ, ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Z s‖ ≤ C) ∧
      (∀ s : ℂ, 1 < s.re →
        Z s = C₀ * (∏ j, Complex.Gammaℝ (s + c j)) *
          ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
            (1 - ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ∧
      (∀ σ₂ : ℝ, ∃ D₀ : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ σ₂ → ‖D s‖ ≤ D₀) ∧
      (∀ s : ℂ, 1 < s.re →
        Z (1 - s) = D s * (∏ j, Complex.Gammaℝ (s + d j)) *
          ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S'},
            (1 - (((χ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) := by
  have hχc' : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((χ x : ℂˣ) : ℂ) := Units.continuous_val.comp _hχc
  choose ur ar hr using fun i : {w : InfinitePlace K // w.IsReal} =>
    ArchCharacterTransport.exists_re_eq_zero_and_forall_eq_realCharFun χ hχc' _hχu i.2
  choose uc kc hc using fun j : {w : InfinitePlace K // w.IsComplex} =>
    ArchCharacterTransport.exists_re_eq_zero_and_forall_eq_complexCharFun χ hχc' _hχu j.2
  obtain ⟨S, e, Z, c₁, hS, hc₁, hZ, hstrip, hid, hfe⟩ :=
    heckeCore K χ _hχ _hχc _hχu _hχ1 ur ar (fun i => (hr i).2) uc kc (fun j => (hc j).2)
  obtain ⟨S', D, hSS', hDb, hdual⟩ :=
    heckeDual K χ _hχc _hχu ur ar (fun i => (hr i).2) uc kc (fun j => (hc j).2) S
      (fun v hv => by_contra fun hn => hv ((hS v).2 hn)) e
  obtain ⟨m, c, d, hcre, hdre, hcl, hdl⟩ := exists_fin_lists
    (fun i => ur i + LanglandsTunnell.signShift (ar i)) (fun i => -ur i + LanglandsTunnell.signShift (ar i))
    (fun j => uc j + ((kc j).natAbs : ℂ) / 2) (fun j => -uc j + ((kc j).natAbs : ℂ) / 2)
    (fun i => by simp only [Complex.add_re, (hr i).1, zero_add]; exact re_signShift_nonneg _)
    (fun i => by simp only [Complex.add_re, Complex.neg_re, (hr i).1, neg_zero, zero_add]; exact re_signShift_nonneg _)
    (fun j => by simp only [Complex.add_re, (hc j).1, zero_add]; exact re_natCast_div_two_nonneg _)
    (fun j => by
      simp only [Complex.add_re, Complex.neg_re, (hc j).1, neg_zero, zero_add]; exact re_natCast_div_two_nonneg _)
  refine ⟨S, S', m, c, d, Z, D, c₁, hS, hSS', hc₁, hcre, hdre, hZ, hstrip, ?_, hDb, ?_⟩
  · intro s hs
    rw [hid s hs, hcl s]
    ring
  · intro s hs
    rw [hfe s hs, hdual s hs, hdl s]
    ring

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

end HeckeFunctionalEquation
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar.ZetaTransport"

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal

open NumberField NumberField.TateGlobal in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hχ : IsIdeleClassChar (𝓞 K) K χ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 K) K χ)
    (_hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1) :
    ∃ (S S' : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (c d : Fin m → ℂ) (Z D : ℂ → ℂ) (C₀ : ℂ),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ S ↔ ¬ IsUnramifiedCharAt χ v) ∧ S ⊆ S' ∧ C₀ ≠ 0 ∧
      (∀ j, 0 ≤ (c j).re) ∧ (∀ j, 0 ≤ (d j).re) ∧ Differentiable ℂ Z ∧
      (∀ σ₁ σ₂ : ℝ, ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Z s‖ ≤ C) ∧
      (∀ s : ℂ, 1 < s.re →
        Z s = C₀ * (∏ j, Complex.Gammaℝ (s + c j)) *
          ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
            (1 - ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ∧
      (∀ σ₂ : ℝ, ∃ D₀ : ℝ, ∀ s : ℂ, 1 ≤ s.re → s.re ≤ σ₂ → ‖D s‖ ≤ D₀) ∧
      (∀ s : ℂ, 1 < s.re →
        Z (1 - s) = D s * (∏ j, Complex.Gammaℝ (s + d j)) *
          ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S'},
            (1 - (((χ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) := by
  exact HeckeFunctionalEquation.exists_entire_functionalEquation K χ _hχ _hχc _hχu _hχ1

#print axioms solution

end S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar (solution)
