-- Prove2me | solution 1 for Kyprianou.Ch04.actualNormalisedSmallJumpGridPairBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:57:47.078747+00:00
-- url     : https://prove2.me/submissions/80cfc3a8-ce8a-4fc5-914b-606ca2dc5ecd

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_actualPoissonFutureIndependenceV1
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_actualCutoffMaximalBoundV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffCompactBoundV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffAdaptedV1
import Theorems.Thm_Kyprianou_Ch04_normalisedGridPredictableCoefficientsV1
import Theorems.Thm_Kyprianou_Ch04_compactDifferenceSquareEnvelopeV1
import Theorems.Thm_Kyprianou_Ch04_normalisedWeightStateBoundV1
import Theorems.Thm_Kyprianou_Ch04_physicalStepGridPairMaximalBoundV1
import Theorems.Thm_Kyprianou_Ch04_poissonZeroTimeSliceV1
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual two-cutoff small-jump grid error is bounded uniformly in the mesh. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (X Xleft X2 U V L R : NNReal → Ω → ℝ)
    (F : Filtration NNReal inferInstance)
    (hF : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P ν F N)
    (hPast : ∀ (t : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Icc (0 : ℝ) (t : ℝ) ×ˢ univ → Measurable[F t] (fun w => N.N w D))
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X Xleft w)
    (c a b K : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (hK : 0 ≤ K)
    (h2 : ∀ t w, X2 t w = c * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},z.2 ∂(N.N w))
    (hU : ∀ t w, U t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | a < |x| ∧ |x| < 1},z.2 ∂(N.N w)) -
      (t : ℝ) * (∫ x in {x : ℝ | a < |x| ∧ |x| < 1},x ∂ν))
    (hV : ∀ t w, V t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | b < |x| ∧ |x| < 1},z.2 ∂(N.N w)) -
      (t : ℝ) * (∫ x in {x : ℝ | b < |x| ∧ |x| < 1},x ∂ν))
    (hL : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => U s w) (𝓝[<] t) (𝓝 (L t w)))
    (hR : ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => V s w) (𝓝[<] t) (𝓝 (R t w)))
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hBound : ∀ s x : ℝ, 0 ≤ s → |f s x| ≤ K)
    (hLip : ∀ s : NNReal, ∀ x y : ℝ, |f s x-f s y| ≤ K*|x-y|)
    (T : NNReal) (hT : 0 < T) (n : ℕ) (u : ℕ → NNReal) (hu : Monotone u)
    (huT : ∀ k ∈ Finset.range n, u k ≤ T) :
    let G := fun (Y Z : NNReal → Ω → ℝ) (t : NNReal) w =>
      ∑ k ∈ Finset.range n, (if u k=0 then 0 else f (u k) (Z (u k) w)) *
        ((Y (min t (u (k+1))) w-X2 (min t (u (k+1))) w)-
          (Y (min t (u k)) w-X2 (min t (u k)) w))
    ∀ δ : ℝ, 0 < δ →
      P {w | ∃ t ≤ T, δ ≤ |G U L t w-G V R t w|} ≤
        ENNReal.ofReal (4 * ((K^2 * (T : ℝ) * (1 + 4 * (T : ℝ) *
          (∫⁻ z in {z : ℝ | |z| < 1}, ENNReal.ofReal (z^2) ∂ν).toReal)) *
          (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal)) /
          ENNReal.ofReal ((δ/2)^2) := by
  intro G δ hδ
  let S := fun w => sSup ((fun t : NNReal => |U t w-V t w|^2) '' Iic T)
  obtain ⟨hS,hEnergy⟩ := Kyprianou.Ch04.actualCutoffMaximalBoundV1 P ν hν N
    X Xleft X2 U V a b ha hab hb hN hU hV T hT
  have hUb := Kyprianou.Ch04.actualCutoffCompactBoundV1 P ν hν N
    X Xleft X2 U c a ha hN h2 hU
  have hVb := Kyprianou.Ch04.actualCutoffCompactBoundV1 P ν hν N
    X Xleft X2 V c b (ha.trans hab) hN h2 hV
  have hEnv : ∀ᵐ w ∂P, 0 ≤ S w ∧ ∀ t ≤ T, |U t w-V t w| ≤ Real.sqrt (S w) := by
    filter_upwards [hUb,hVb] with w hw1 hw2
    obtain ⟨C,hC⟩ := hw1 T
    obtain ⟨D,hD⟩ := hw2 T
    exact Kyprianou.Ch04.compactDifferenceSquareEnvelopeV1 (fun t => U t w)
      (fun t => V t w) T C D hC hD
  have hUa := Kyprianou.Ch04.actualCutoffAdaptedV1 P ν F N hPast c a U X2 h2 hU
  have hVa := Kyprianou.Ch04.actualCutoffAdaptedV1 P ν F N hPast c b V X2 h2 hV
  obtain ⟨H,hH,hHb,hHe⟩ := Kyprianou.Ch04.normalisedGridPredictableCoefficientsV1
    P X F hF U L hUa hL f K hK hf hBound u
  obtain ⟨Q,hQ,hQb,hQe⟩ := Kyprianou.Ch04.normalisedGridPredictableCoefficientsV1
    P X F hF V R hVa hR f K hK hf hBound u
  have hDiff : ∀ᵐ w ∂P, ∀ k ∈ Finset.range n, |H k w-Q k w| ≤ K*Real.sqrt (S w) := by
    filter_upwards [hHe,hQe,hL,hR,hEnv] with w he1 he2 hl hr hEnvw
    intro k hk
    rw [he1 k,he2 k]
    exact Kyprianou.Ch04.normalisedWeightStateBoundV1 (fun t => U t w) (fun t => V t w)
      (fun t => L t w) (fun t => R t w) T f K _ hK (Real.sqrt_nonneg _)
      hl hr hEnvw.2 hLip (u k) (huT k hk)
  let Y := fun t w => U t w-X2 t w
  let Z := fun t w => V t w-X2 t w
  have hY (t w) : Y t w = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | a < |x| ∧ |x| < 1},
      z.2 ∂(N.N w)) - (t : ℝ) * (∫ x in {x : ℝ | a < |x| ∧ |x| < 1},x ∂ν) := by
    dsimp [Y]; rw [hU]; ring
  have hZ (t w) : Z t w = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | b < |x| ∧ |x| < 1},
      z.2 ∂(N.N w)) - (t : ℝ) * (∫ x in {x : ℝ | b < |x| ∧ |x| < 1},x ∂ν) := by
    dsimp [Z]; rw [hV]; ring
  have hmax := Kyprianou.Ch04.physicalStepGridPairMaximalBoundV1 P ν hν F N
    (Kyprianou.Ch04.poissonZeroTimeSliceV1 P ν N).2 a b K ha hab hb hK
    u hu n H Q (fun k _ => hH k) (fun k _ => hQ k)
    (fun k _ => hHb k) (fun k _ => hQb k) Y Z hY hZ X hF hFuture hPast T hT
    S hS (hEnv.mono fun w hw => hw.1) hDiff hEnergy δ hδ
  refine le_trans (measure_mono_ae ?_) hmax
  filter_upwards [hHe,hQe] with w hw1 hw2
  rintro ⟨t,ht,hd⟩
  refine ⟨t,ht,?_⟩
  simpa only [Y,Z,hw1,hw2,G] using hd
