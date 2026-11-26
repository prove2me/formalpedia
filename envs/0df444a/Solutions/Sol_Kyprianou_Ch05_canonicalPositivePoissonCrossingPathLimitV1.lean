-- Prove2me | solution 1 for Kyprianou.Ch05.canonicalPositivePoissonCrossingPathLimitV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:39:51.181414+00:00
-- url     : https://prove2.me/submissions/768ebef8-ecbe-44e8-9b24-646df4783530
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_markedPositiveCrossingAmbientMeasurableV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCrossingFullIntegralV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonCrossingAtomicSumV1
import Theorems.Thm_Kyprianou_Ch05_pointFamilyPairLIntegralV1
import Theorems.Thm_Kyprianou_Ch05_pointFamilyJointRestrictedIntegralMeasurableV1
import Theorems.Thm_Kyprianou_Ch05_nonnegativeKernelHorizonExhaustionV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonCadlagMonotoneV1
import Theorems.Thm_Kyprianou_Ch05_canonicalPositivePoissonJumpFibreV1
import Theorems.Thm_Kyprianou_Ch05_positiveTimeLeftLimitRealNNRealV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonDistinctActiveTimesV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonStripMeasurableAmbientV1
import Theorems.Thm_Kyprianou_Ch05_predictableMarkedPositiveCrossingKernelV1
import Theorems.Thm_Kyprianou_Ch04_markedPredictableLeAmbientProduct
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q)
    (eta d : ℝ) (heta : 0 ≤ eta) (hdrift : 0 ≤ d)
    (hs : Pi (Iic (0 : ℝ)) = 0)
    (hint : Integrable (fun z : ℝ => min (1 : ℝ) |z|) Pi)
    (x : ℝ) (hx : 0 < x) (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAp : A ⊆ Ioi (0 : ℝ)) (hBp : B ⊆ Icc (0 : ℝ) x)
    (H : (NNReal → ℝ) → ENNReal) (hHmeas : Measurable H)
    (hH : ∀ f : NNReal → ℝ, Monotone f → f 0 = 0 →
        (∀ t, ContinuousWithinAt f (Ici t) t) →
        (∀ t, 0 < t → ∃ l : ℝ, Tendsto f (nhdsWithin t (Iio t)) (nhds l)) →
        H f = ∑' t : NNReal, if 0 < t ∧ f t > x ∧
          Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
          f t - x ∈ A ∧ x - Function.leftLim f t ∈ B then
          ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0)     (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} Q Pi)
    (hN : ∀ w, N.N w = (poissonRandomMeasure K Z w).restrict (Ici (0 : ℝ) ×ˢ univ))
    (F : Filtration NNReal inferInstance)
    (hF : ∀ t : NNReal, F t = prmEvalSigma K Z ((volume : Measure ℝ).prod Pi)
      (Iic (t : ℝ) ×ˢ univ))
    (V : NNReal → Lambda → ℝ)
    (hV : Measurable[F.predictable] (Function.uncurry V))
    (hleft : ∀ᵐ w ∂Q, ∀ t : NNReal, 0 < t →
      V t w = Function.leftLim (fun s => d * (s : ℝ) +
        (∫⁻ z in Ioc (0 : ℝ) (s : ℝ) ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal) t) :
    let X := fun (t : NNReal) (w : Lambda) =>
      d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
    let psi := fun (s z : ℝ) (w : Lambda) =>
      if 0 < s ∧ V s.toNNReal w ∈ Icc (0 : ℝ) x ∧
        x - V s.toNNReal w < z ∧ z-(x-V s.toNNReal w) ∈ A ∧
        x-V s.toNNReal w ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0
    Tendsto (fun n : ℕ => ∫⁻ w, ∫⁻ z in Icc (0 : ℝ) (n : ℝ) ×ˢ univ,
        psi z.1 z.2 w ∂(N.N w) ∂Q) atTop (nhds (∫⁻ f, H f ∂(Q.map (fun w t => X t w)))) := by
  classical
  dsimp only
  let X := fun (t : NNReal) (w : Lambda) =>
    d * (t : ℝ) + (∫⁻ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal z.2 ∂(poissonRandomMeasure K Z w)).toReal
  let psi := fun (s z : ℝ) (w : Lambda) =>
    if 0 < s ∧ V s.toNNReal w ∈ Icc (0 : ℝ) x ∧
      x - V s.toNNReal w < z ∧ z-(x-V s.toNNReal w) ∈ A ∧
      x-V s.toNNReal w ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0
  let g (w : Lambda) (z : ℝ × ℝ) := psi z.1 z.2 w
  let S (n : ℕ) := Icc (0 : ℝ) (n : ℝ) ×ˢ (univ : Set ℝ)
  have hg : Measurable (Function.uncurry g) :=
    markedPositiveCrossingAmbientMeasurableV1 F V hV eta x A B hA hB
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_Icc.prod MeasurableSet.univ
  have hmono : Monotone S := fun i j hij => Set.prod_mono
    (Icc_subset_Icc_right (by exact_mod_cast hij)) le_rfl
  have hM (n : ℕ) : AEMeasurable (fun w => ∫⁻ z in S n, g w z ∂(N.N w)) Q := by
    have he (w : Lambda) : (N.N w).restrict (S n) =
        (poissonRandomMeasure K Z w).restrict (S n) := by
      rw [hN,Measure.restrict_restrict_of_subset]
      exact Set.prod_mono Icc_subset_Ici_self le_rfl
    simp_rw [show ∀ w, (∫⁻ z in S n, g w z ∂(N.N w)) =
        ∫⁻ z in S n, g w z ∂(poissonRandomMeasure K Z w) from
        fun w => by rw [he w]]
    exact (pointFamilyJointRestrictedIntegralMeasurableV1 K Z
      hd.measurable_count hd.measurable_point _ hg _ (hS n)).aemeasurable
  have hh := nonnegativeKernelHorizonExhaustionV1 Q N.N g
    (fun w => hg.comp measurable_prodMk_left) S hS hmono hM
  have hu : (⋃ n, S n) = Ici (0 : ℝ) ×ˢ (univ : Set ℝ) := by
    ext z
    constructor
    · intro hz
      obtain ⟨n,hn⟩ := mem_iUnion.mp hz
      exact ⟨hn.1.1,hn.2⟩
    · intro hz
      obtain ⟨n,hn⟩ := exists_nat_ge z.1
      exact mem_iUnion.mpr ⟨n,⟨hz.1,hn⟩,hz.2⟩
  rw [hu] at hh
  have hXm : Measurable (fun w t => X t w) :=
    measurable_pi_iff.mpr (fun t =>
      (positivePoissonStripMeasurableAmbientV1 Q Pi K Z hd hint 0 t).const_add (d*(t : ℝ)))
  rw [lintegral_map hHmeas hXm]
  convert hh using 2
  apply lintegral_congr_ae
  filter_upwards [canonicalPositivePoissonCrossingFullIntegralV1
    Q Pi K Z hd eta d heta hdrift hs hint x hx A B hA hB hAp hBp
    H hHmeas hH N hN F hF V hV hleft] with w hw
  exact hw.symm
