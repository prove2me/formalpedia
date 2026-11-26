-- Prove2me | solution 1 for Kyprianou.Ch04.finiteBandPhysicalL2Core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:12.877322+00:00
-- url     : https://prove2.me/submissions/7b1841b0-de6f-44f4-becc-be495bc82f28

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_markedPredictableLeAmbientProduct
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_original_filtration_marked_finite_band_l2_dense
import Theorems.Thm_Kyprianou_Ch04_sharedClockPhysicalL1Difference
import Theorems.Thm_Kyprianou_Ch04_sharedClockPhysicalSubAE
import Theorems.Thm_Kyprianou_Ch04_sharedClockNonnegativeIntegral
import Theorems.Thm_Kyprianou_Ch04_physicalRestrictedGeneratorSumIsometry
import Theorems.Thm_Kyprianou_Ch04_finiteGeneratorSpanPhysicalSquare
import Theorems.Thm_Kyprianou_Ch04_densePhysicalL2Isometry
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Physical Poisson isometry on a finite marked predictable clock measure. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P nu F N)
    (hPast : ∀ (u : NNReal) (E : Set (ℝ × ℝ)), MeasurableSet E →
      E ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun w => N.N w E))
    (t : NNReal) (B : Set ℝ) (hB : MeasurableSet B) (hfin : nu B < ⊤)
    [mAll : MeasurableSpace ((NNReal × Omega) × ℝ)]
    (hAll : mAll = F.predictable.prod (inferInstance : MeasurableSpace ℝ))
    (mu : Measure ((NNReal × Omega) × ℝ)) [IsFiniteMeasure mu]
    (hClock : ∀ f : ((NNReal × Omega) × ℝ) → ENNReal, Measurable f →
      AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B,
        f ((z.1.toNNReal,w),z.2) ∂(N.N w)) P ∧
      AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu) P ∧
      (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B,
        f ((z.1.toNNReal,w),z.2) ∂(N.N w) ∂P) ∧
      (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P))
    (g : ((NNReal × Omega) × ℝ) → ℝ) (hgm : Measurable g) (hg : MemLp g 2 mu) :
    let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
    let K := fun w (z : ℝ × ℝ) => g ((z.1.toNNReal,w),z.2)
    let X := fun w => (∫ z in U, K w z ∂(N.N w)) -
      ∫ z in U, K w z ∂referenceIntensity nu
    Integrable (fun w => (X w)^2) P ∧
      (∫ w, (X w)^2 ∂P) = ∫ w, ∫ z in U, (K w z)^2 ∂referenceIntensity nu ∂P := by
  let A := (NNReal × Omega) × ℝ
  let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ B
  let q := fun (w : Omega) (z : ℝ × ℝ) => ((z.1.toNNReal,w),z.2)
  let R := fun w => (N.N w).restrict U
  let S := (referenceIntensity nu).restrict U
  let T := fun f : A → ℝ => fun w => (∫ z, f (q w z) ∂(R w)) -
    ∫ z, f (q w z) ∂S
  have hle : mAll ≤ ((inferInstance : MeasurableSpace NNReal).prod
      (inferInstance : MeasurableSpace Omega)).prod (inferInstance : MeasurableSpace ℝ) := by
    rw [hAll]
    exact Kyprianou.Ch04.markedPredictableLeAmbientProduct F
  have hq (w : Omega) : Measurable (q w) := by
    have hm : @Measurable (ℝ × ℝ) A inferInstance
        (((inferInstance : MeasurableSpace NNReal).prod
          (inferInstance : MeasurableSpace Omega)).prod (inferInstance : MeasurableSpace ℝ))
        (q w) :=
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
        measurable_const).prodMk measurable_snd
    exact hm.mono le_rfl hle
  have hR (f : A → ENNReal) (hf : Measurable f) :
      AEMeasurable (fun w => ∫⁻ z, f (q w z) ∂(R w)) P ∧
      (∫⁻ w, ∫⁻ z, f (q w z) ∂(R w) ∂P) = ∫⁻ a, f a ∂mu :=
    ⟨(hClock f hf).1,(hClock f hf).2.2.1.symm⟩
  have hS (f : A → ENNReal) (hf : Measurable f) :
      AEMeasurable (fun w => ∫⁻ z, f (q w z) ∂S) P ∧
      (∫⁻ w, ∫⁻ z, f (q w z) ∂S ∂P) = ∫⁻ a, f a ∂mu :=
    ⟨(hClock f hf).2.1,(hClock f hf).2.2.2.symm⟩
  have hT := Kyprianou.Ch04.sharedClockPhysicalL1Difference P mu R S q hq hR hS
  have hSub := Kyprianou.Ch04.sharedClockPhysicalSubAE P mu R S q hq hR hS
  let G : Set (Set A) := insert Set.univ (insert ∅
    (Set.image2 (· ×ˢ ·)
      {E : Set (NNReal × Omega) |
        (∃ A : Set Omega, MeasurableSet[F ⊥] A ∧ E = ({⊥} ×ˢ A)) ∨
        (∃ a : NNReal, ∃ A : Set Omega, MeasurableSet[F a] A ∧ E = (Set.Ioi a ×ˢ A))}
      {C : Set ℝ | MeasurableSet C}))
  let V : Submodule ℝ (Lp ℝ 2 mu) := Submodule.span ℝ
    {v | ∃ (D : Set A), D ∈ G ∧ ∃ (hD : MeasurableSet D) (hfin : mu D ≠ ⊤),
      indicatorConstLp 2 hD hfin (1 : ℝ) = v}
  have hDense : ∀ v : Lp ℝ 2 mu, v ∈ V.topologicalClosure := by
    simpa only [V, G, exists_prop] using
      (AvramDividend.Classical.avram_wave4_p1_original_filtration_marked_finite_band_l2_dense F mu hAll)
  have hSq (v : Lp ℝ 2 mu) (hv : v ∈ V) :
      Integrable (fun w => (T (v : A → ℝ) w)^2) P ∧
      (∫ w, (T (v : A → ℝ) w)^2 ∂P) = ∫ a, (v a)^2 ∂mu := by
    apply Kyprianou.Ch04.finiteGeneratorSpanPhysicalSquare mu P G T hT _ v hv
    intro k D c hD
    dsimp only
    intro hf hflp
    let f : A → ℝ := fun a => ∑ i, c i * (D i).indicator (fun _ => (1 : ℝ)) a
    have hs := Kyprianou.Ch04.physicalRestrictedGeneratorSumIsometry
      P nu F N hFuture hPast t B hB hfin k D c hD
    have he := Kyprianou.Ch04.sharedClockNonnegativeIntegral P mu (fun _ => S) q hq hS
      (fun a => (f a)^2) (hf.pow_const 2) (fun a => sq_nonneg _) hflp.integrable_sq
    exact ⟨hs.1,hs.2.trans he⟩
  have h := Kyprianou.Ch04.densePhysicalL2Isometry mu P T hT hSub V hDense hSq g hgm hg
  have he := Kyprianou.Ch04.sharedClockNonnegativeIntegral P mu (fun _ => S) q hq hS
    (fun a => (g a)^2) (hgm.pow_const 2) (fun a => sq_nonneg _) hg.integrable_sq
  exact ⟨h.1.integrable_sq,h.2.trans he.symm⟩
