-- Prove2me | solution 1 for Kyprianou.Ch04.fullPredictablePhysicalL2Core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:46:23.426957+00:00
-- url     : https://prove2.me/submissions/aafa8331-ccaa-482c-9281-3e4573a4c997

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_markedPredictableLeAmbientProduct
import Theorems.Thm_Kyprianou_Ch04_sharedClockPhysicalL1Difference
import Theorems.Thm_Kyprianou_Ch04_sharedClockPhysicalSubAE
import Theorems.Thm_Kyprianou_Ch04_sharedClockNonnegativeIntegral
import Theorems.Thm_Kyprianou_Ch04_fullClockSupportedBandSquare
import Theorems.Thm_Kyprianou_Ch04_exhaustedPhysicalL2Isometry
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The full physical compensated Poisson isometry for integrable predictable L2 kernels. -/
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
    (t : NNReal)
    [mAll : MeasurableSpace ((NNReal × Omega) × ℝ)]
    (hAll : mAll = F.predictable.prod (inferInstance : MeasurableSpace ℝ))
    (mu : Measure ((NNReal × Omega) × ℝ))
    (hClock : ∀ f : ((NNReal × Omega) × ℝ) → ENNReal, Measurable f →
      AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂(N.N w)) P ∧
      AEMeasurable (fun w => ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu) P ∧
      (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂(N.N w) ∂P) ∧
      (∫⁻ p, f p ∂mu) = (∫⁻ w, ∫⁻ z in Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ,
        f ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu ∂P))
    (g : ((NNReal × Omega) × ℝ) → ℝ) (hgm : Measurable g)
    (hgi : Integrable g mu) (hg : MemLp g 2 mu) :
    let V := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
    let X := fun w => (∫ z in V, g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      ∫ z in V, g ((z.1.toNNReal,w),z.2) ∂referenceIntensity nu
    Integrable (fun w => (X w)^2) P ∧
      (∫ w, (X w)^2 ∂P) = ∫ w, ∫ z in V,
        (g ((z.1.toNNReal,w),z.2))^2 ∂referenceIntensity nu ∂P := by
  let A := (NNReal × Omega) × ℝ
  let V := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
  let q := fun (w : Omega) (z : ℝ × ℝ) => ((z.1.toNNReal,w),z.2)
  let R := fun w => (N.N w).restrict V
  let S := (referenceIntensity nu).restrict V
  let T := fun f : A → ℝ => fun w => (∫ z, f (q w z) ∂(R w)) -
    ∫ z, f (q w z) ∂S
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
  have hR (f : A → ENNReal) (hf : Measurable f) :
      AEMeasurable (fun w => ∫⁻ z, f (q w z) ∂(R w)) P ∧
      (∫⁻ w, ∫⁻ z, f (q w z) ∂(R w) ∂P) = ∫⁻ a, f a ∂mu :=
    ⟨(hClock f hf).1,(hClock f hf).2.2.1.symm⟩
  have hS (f : A → ENNReal) (hf : Measurable f) :
      AEMeasurable (fun w => ∫⁻ z, f (q w z) ∂S) P ∧
      (∫⁻ w, ∫⁻ z, f (q w z) ∂S ∂P) = ∫⁻ a, f a ∂mu :=
    ⟨(hClock f hf).2.1,(hClock f hf).2.2.2.symm⟩
  let B := spanningSets nu
  let D : ℕ → Set A := fun n => Prod.snd ⁻¹' B n
  have hmark : @Measurable A ℝ mAll inferInstance Prod.snd := by
    rw [hAll]
    exact measurable_snd
  have hD (n : ℕ) : MeasurableSet (D n) := hmark (measurableSet_spanningSets nu n)
  have hmono : Monotone D := fun i j hij _ ha => monotone_spanningSets nu hij ha
  have hcover : (⋃ n, D n) = Set.univ := by
    rw [show (⋃ n, D n) = Prod.snd ⁻¹' (⋃ n, B n) from Set.preimage_iUnion.symm]
    simp [B,iUnion_spanningSets]
  have hSq (n : ℕ) (f : A → ℝ) (hf : Measurable f) (_hi : Integrable f mu)
      (hflp : MemLp f 2 mu) (hz : ∀ a ∉ D n, f a = 0) :
      Integrable (fun w => (T f w)^2) P ∧
        (∫ w, (T f w)^2 ∂P) = ∫ a, (f a)^2 ∂mu :=
    fullClockSupportedBandSquare P nu F N hFuture hPast t (B n)
      (measurableSet_spanningSets nu n) (measure_spanningSets_lt_top nu n)
      hAll mu (fun k hk => ⟨(hClock k hk).2.1,(hClock k hk).2.2.2⟩)
      f hf hflp hz
  have h := exhaustedPhysicalL2Isometry mu P T
    (sharedClockPhysicalL1Difference P mu R S q hq hR hS)
    (sharedClockPhysicalSubAE P mu R S q hq hR hS) D hD hmono hcover hSq g hgm hgi hg
  have he := sharedClockNonnegativeIntegral P mu (fun _ => S) q hq hS
    (fun a => (g a)^2) (hgm.pow_const 2) (fun a => sq_nonneg _) hg.integrable_sq
  exact ⟨h.1.integrable_sq,h.2.trans he.symm⟩
