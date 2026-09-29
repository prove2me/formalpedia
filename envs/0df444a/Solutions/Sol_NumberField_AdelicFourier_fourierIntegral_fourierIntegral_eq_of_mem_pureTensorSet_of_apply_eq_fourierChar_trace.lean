-- Prove2me | solution 1 for NumberField.AdelicFourier.fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f0c8c28d-eb79-5cd0-94ec-24047b2f9737

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq
import Theorems.Thm_VectorFourier_fourierIntegral_flip_fourierIntegral_eq
import Theorems.Thm_SchwartzMap_exists_coe_eq_vectorFourierIntegral
import Theorems.Thm_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_finiteAdeleRing_eq
import Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import Theorems.Thm_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

set_option maxHeartbeats 6400000 in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) (x : AdeleRing (𝓞 F) F) :
    fourierIntegral ψ μ (fourierIntegral ψ μ f) x
      = ((μ (AdelicBox.adelicBox F)).toReal : ℂ) ^ 2 * f (-x) := by
  classical
  obtain ⟨g, h, hlc, hcs, rfl⟩ := hf
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  let ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F) := MeasureTheory.Measure.addHaar
  have hψu : ∀ y, ‖ψ y‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ

  let V := mixedEmbedding.mixedSpace F
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let Bt : LinearMap.BilinForm ℝ V := Algebra.traceForm ℝ V
  have hBt : Bt.Nondegenerate := mixedEmbedding.traceForm_mixedSpace_nondegenerate F
  have hflip : Bt.flip = Bt := by
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    show Algebra.trace ℝ V (w * v) = Algebra.trace ℝ V (v * w)
    rw [mul_comm]

  have hflip' : LinearMap.flip Bt = Bt := by
    refine LinearMap.ext fun v => LinearMap.ext fun w => ?_
    show Algebra.trace ℝ V (w * v) = Algebra.trace ℝ V (v * w)
    rw [mul_comm]
  let ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let ψV : AddChar V ℂ :=
    ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
      e.symm.toAddMonoidHom)
  have hψV_apply : ∀ v : V, ψV v = ψ (e.symm v, 0) := fun v => rfl

  have hglue : ∀ (g' : SchwartzMap V ℂ) (w' : V),
      fourierIntegral ψV MeasureTheory.volume (g' : V → ℂ) w'
        = VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume Bt g' w' := by
    intro g' w'
    rw [fourierIntegral_def]
    show _ = ∫ v, 𝐞 (-(Bt v w')) • g' v
    congr 1; funext v
    rw [Circle.smul_def, smul_eq_mul, hψV_apply, hψ_inf, RingEquiv.apply_symm_apply, map_neg]
    rfl

  obtain ⟨g₁, hg₁⟩ := SchwartzMap.exists_coe_eq_vectorFourierIntegral
    (MeasureTheory.volume : MeasureTheory.Measure V) Bt hBt g
  have hh₁ := isLocallyConstant_and_hasCompactSupport_fourierIntegral_finiteAdeleRing F ν hψ hψ_inf hlc hcs

  have hν0 : ν (integralFiniteAdeles (𝓞 F) F) ≠ 0 :=
    (isOpen_integralFiniteAdeles F).measure_ne_zero ν ⟨0, fun v => (v.adicCompletionIntegers F).zero_mem⟩
  have hνtop : ν (integralFiniteAdeles (𝓞 F) F) ≠ ⊤ := (isCompact_integralFiniteAdeles F).measure_lt_top.ne
  have hνreal : (ν (integralFiniteAdeles (𝓞 F) F)).toReal ≠ 0 := (ENNReal.toReal_pos hν0 hνtop).ne'
  have hcovΛ : 0 < ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume :=
    ZLattice.covolume_pos _ _

  have hFD : MeasureTheory.volume.real (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))
      = ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume :=
    (ZLattice.covolume_eq_measure_fundamentalDomain _ _ (mixedEmbedding.fundamentalDomain_integerLattice F)).symm
  have hdet : (Matrix.of fun i j => Bt (mixedEmbedding.latticeBasis F i) (mixedEmbedding.latticeBasis F j)).det
      = (NumberField.discr F : ℝ) := by
    have hM : (Matrix.of fun i j => Bt (mixedEmbedding.latticeBasis F i) (mixedEmbedding.latticeBasis F j))
        = (algebraMap ℚ ℝ).mapMatrix (Algebra.traceMatrix ℚ (integralBasis F)) := by
      ext i j
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
        Algebra.traceForm_apply, mixedEmbedding.latticeBasis_apply, eq_ratCast]
      show Algebra.trace ℝ V (mixedEmbedding F _ * mixedEmbedding F _) = _
      rw [← map_mul, mixedEmbedding.trace_mixedEmbedding]
    rw [hM, ← RingHom.map_det, ← Algebra.discr_def, ← NumberField.coe_discr, eq_ratCast]
    push_cast
    rfl
  have hdiff : (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) = |(NumberField.discr F : ℝ)| := by
    rw [NumberField.absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, Int.cast_abs]
  have hdisc : (NumberField.discr F : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero F

  have harch : ∀ v : V, VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume Bt
        (VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume Bt g) v
      = ((ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume ^ 2
          / (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) : ℝ) : ℂ) * g (-v) := by
    intro v
    have := VectorFourier.fourierIntegral_flip_fourierIntegral_eq
      (MeasureTheory.volume : MeasureTheory.Measure V) Bt hBt (mixedEmbedding.latticeBasis F) g v
    first
      | (rw [hflip, hFD, hdet, ← hdiff] at this; exact this)
      | (rw [hflip', hFD, hdet, ← hdiff] at this; exact this)

  have hfin : ∀ y, fourierIntegral ψf ν (fourierIntegral ψf ν h) y
      = ((Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℂ) * ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) ^ 2)
        * h (-y) :=
    fun y => fourierIntegral_fourierIntegral_finiteAdeleRing_eq F ν hψ hψ_inf hlc hcs y

  let C : ℂ := ((μ (adelicBox F)).toReal : ℂ) /
      ((ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume : ℂ)
        * ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ))
  have hinner : fourierIntegral ψ μ (fun x => g (e x.1) * h x.2)
      = C • fun w => g₁ (e w.1) * fourierIntegral ψf ν h w.2 := by
    funext w
    rw [fourierIntegral_pureTensor_eq F μ ν hψ.continuous hψu g hlc hcs w, Pi.smul_apply, smul_eq_mul,
      hglue g, ← hg₁]
    simp only [C]
    ring

  rw [hinner, fourierIntegral_smul, Pi.smul_apply, smul_eq_mul,
    fourierIntegral_pureTensor_eq F μ ν hψ.continuous hψu g₁ hh₁.1 hh₁.2 x, hglue g₁, hg₁, harch, hfin]

  rw [show (fun x : AdeleRing (𝓞 F) F => g (e x.1) * h x.2) (-x) = g (-(e x.1)) * h (-x.2) from by
    change g (e (-x).1) * h (-x).2 = _
    rw [show (-x).1 = -x.1 from rfl, show (-x).2 = -x.2 from rfl, map_neg]]

  have hN : (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℂ) ≠ 0 := by
    have : (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ℝ) ≠ 0 := by rw [hdiff]; exact abs_ne_zero.mpr hdisc
    exact_mod_cast this
  have hcovC : (ZLattice.covolume (mixedEmbedding.integerLattice F) MeasureTheory.volume : ℂ) ≠ 0 := by
    exact_mod_cast hcovΛ.ne'
  have hνC : ((ν (integralFiniteAdeles (𝓞 F) F)).toReal : ℂ) ≠ 0 := by exact_mod_cast hνreal
  simp only [C]
  push_cast
  field_simp
  ring

end S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
end P2MW
export P2MW.S_NumberField_AdelicFourier_fourierIntegral_fourierIntegral_eq_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace (solution)
