-- Prove2me | solution 1 for Kyprianou.Ch04.fullClockSupportedBandSquare
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:43:41.454801+00:00
-- url     : https://prove2.me/submissions/65c98eff-dd47-4c21-bfe1-350326adf998

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finiteBandPredictableClockAgreement
import Theorems.Thm_Kyprianou_Ch04_finiteBandPhysicalL2Core
import Theorems.Thm_Kyprianou_Ch04_supportedSetIntegrals
import Theorems.Thm_Kyprianou_Ch04_supportedSetLIntegrals
import Theorems.Thm_Kyprianou_Ch04_sharedClockNonnegativeIntegral
import Theorems.Thm_Kyprianou_Ch04_markedPredictableLeAmbientProduct
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The full physical square identity for a predictable kernel supported on a finite mark band. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
    (hPast : ∀ (u : NNReal) (E : Set (ℝ × ℝ)), MeasurableSet E →
      E ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun w => N.N w E))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : nu B < ⊤)
    [mAll : MeasurableSpace ((NNReal × Omega) × ℝ)]
    (hAll : mAll = F.predictable.prod (inferInstance : MeasurableSpace ℝ))
    (mu : Measure ((NNReal × Omega) × ℝ))
    (hClock : ∀ f : ((NNReal × Omega) × ℝ) → ENNReal, Measurable f →
      AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu) P ∧
      (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P))
    (g : ((NNReal × Omega) × ℝ) → ℝ) (hgm : Measurable g) (hg : MemLp g 2 mu)
    (hsupp : ∀ a, a.2 ∉ B → g a = 0) :
    let V := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
    let X := fun w => (∫ z in V, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in V, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu
    Integrable (fun w => (X w)^2) P ∧ (∫ w, (X w)^2 ∂P) = ∫ a, (g a)^2 ∂mu := by
  let A := (NNReal × Omega) × ℝ
  let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
  let V := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
  let q := fun (w : Omega) (z : ℝ × ℝ) => ((z.1.toNNReal,w),z.2)
  let S := (referenceIntensity nu).restrict V
  have hU : MeasurableSet U := measurableSet_Icc.prod hB
  have hV : MeasurableSet V := measurableSet_Icc.prod MeasurableSet.univ
  have hUV : U ⊆ V := fun z hz => ⟨hz.1,Set.mem_univ _⟩
  have hzero (w : Omega) (z : ℝ × ℝ) (hz : z ∈ V) (hz' : z ∉ U) :
      g (q w z) = 0 := hsupp _ (fun hb => hz' ⟨hz.1,hb⟩)
  have hq (w : Omega) : Measurable (q w) := by
    have hm : @Measurable (ℝ × ℝ) A inferInstance
        (((inferInstance : MeasurableSpace NNReal).prod
          (inferInstance : MeasurableSpace Omega)).prod (inferInstance : MeasurableSpace ℝ))
        (q w) :=
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
        measurable_const).prodMk measurable_snd
    apply hm.mono le_rfl
    rw [hAll]
    exact markedPredictableLeAmbientProduct F
  have hS (f : A → ENNReal) (hf : Measurable f) :
      AEMeasurable (fun w => ∫⁻ z, f (q w z) ∂S) P ∧
      (∫⁻ w, ∫⁻ z, f (q w z) ∂S ∂P) = ∫⁻ a, f a ∂mu :=
    ⟨(hClock f hf).1,(hClock f hf).2.symm⟩
  have hsq (w : Omega) :
      (∫ z in V, (g (q w z))^2 ∂referenceIntensity nu) =
      ∫ z in U, (g (q w z))^2 ∂referenceIntensity nu :=
    supportedSetIntegrals _ U V hU hV hUV _ (fun z hz hz' => by rw [hzero w z hz hz']; simp)
  have hsqE (w : Omega) :
      (∫⁻ z in V, ENNReal.ofReal ((g (q w z))^2) ∂referenceIntensity nu) =
      ∫⁻ z in U, ENNReal.ofReal ((g (q w z))^2) ∂referenceIntensity nu :=
    supportedSetLIntegrals _ U V hU hV hUV _ (fun z hz hz' => by rw [hzero w z hz hz']; simp)
  have hband : ∃ muB : Measure A, IsFiniteMeasure muB ∧
      ∀ f : A → ENNReal, Measurable f →
        AEMeasurable (fun w => ∫⁻ z in U, f (q w z) ∂(N.N w)) P ∧
        AEMeasurable (fun w => ∫⁻ z in U, f (q w z) ∂referenceIntensity nu) P ∧
        (∫⁻ p, f p ∂muB) = (∫⁻ w, ∫⁻ z in U, f (q w z) ∂(N.N w) ∂P) ∧
        (∫⁻ p, f p ∂muB) = (∫⁻ w, ∫⁻ z in U, f (q w z) ∂referenceIntensity nu ∂P) := by
    subst mAll
    exact finiteBandPredictableClockAgreement P nu F N hFuture t B hB hfin
  obtain ⟨muB,hmuB,hC⟩ := hband
  letI : IsFiniteMeasure muB := hmuB
  have hsqgm : Measurable (fun a => (g a)^2) := hgm.pow_const 2
  have hEB := (hC (fun a => ENNReal.ofReal ((g a)^2))
    (ENNReal.measurable_ofReal.comp hsqgm)).2.2.2
  have hEF := (hClock (fun a => ENNReal.ofReal ((g a)^2))
    (ENNReal.measurable_ofReal.comp hsqgm)).2
  have hEg : (∫⁻ a, ENNReal.ofReal ((g a)^2) ∂muB) =
      ∫⁻ a, ENNReal.ofReal ((g a)^2) ∂mu := by
    rw [hEB,hEF]
    exact lintegral_congr fun w => (hsqE w).symm
  have hgB : MemLp g 2 muB := by
    apply (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2
    refine ⟨hsqgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun a => sq_nonneg (g a))).2 ?_⟩
    rw [hEg]
    exact (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun a => sq_nonneg (g a))).1 hg.integrable_sq.2
  have hb := finiteBandPhysicalL2Core P nu F N hFuture hPast t B hB hfin hAll muB hC g hgm hgB
  have hx (w : Omega) :
      ((∫ z in V, g (q w z) ∂(N.N w)) - ∫ z in V, g (q w z) ∂referenceIntensity nu) =
      ((∫ z in U, g (q w z) ∂(N.N w)) - ∫ z in U, g (q w z) ∂referenceIntensity nu) := by
    rw [supportedSetIntegrals _ U V hU hV hUV _ (hzero w),
      supportedSetIntegrals _ U V hU hV hUV _ (hzero w)]
  have he := sharedClockNonnegativeIntegral P mu (fun _ => S) q hq hS
    (fun a => (g a)^2) hsqgm (fun a => sq_nonneg _) hg.integrable_sq
  have hx2 : (fun w => ((∫ z in V, g (q w z) ∂(N.N w)) -
      ∫ z in V, g (q w z) ∂referenceIntensity nu)^2) =ᵐ[P]
      fun w => ((∫ z in U, g (q w z) ∂(N.N w)) -
        ∫ z in U, g (q w z) ∂referenceIntensity nu)^2 :=
    Eventually.of_forall fun w => congrArg (fun x : ℝ => x^2) (hx w)
  exact ⟨hb.1.congr hx2.symm, (integral_congr_ae hx2).trans
    (hb.2.trans ((integral_congr_ae (Eventually.of_forall hsq)).symm.trans he))⟩
