-- Prove2me | solution 1 for Kyprianou.Ch04.adaptedCutoffRawEnergyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:32:41.999262+00:00
-- url     : https://prove2.me/submissions/1fb0a69a-06fa-4714-ae1b-dacc69493b00

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Theorems.Thm_Kyprianou_Ch04_adaptedAELeftPredictableVersionV1
import Theorems.Thm_Kyprianou_Ch04_predictableVersionCutoffRawEnergyV1
open MeasureTheory ProbabilityTheory Filter ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Choose predictable versions and transport the exact original energy obligation. -/
theorem solution :
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure]
    (hFiltration : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0} P triplet.levyMeasure)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P triplet.levyMeasure F N)
    (hPast : ∀ (u : NNReal) (D : Set (ℝ × ℝ)), MeasurableSet D →
      D ⊆ Set.Icc (0 : ℝ) (u : ℝ) ×ˢ Set.univ →
      Measurable[F u] (fun ω => N.N ω D))
    (fSpace : ℝ → ℝ → ℝ)
    (hJoint : ContinuousOn (fun z : ℝ × ℝ => fSpace z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (K : ℝ) (hK : 0 < K)
    (hBound : ∀ s x : ℝ, 0 ≤ s → |fSpace s x| ≤ K)
    (Xeps XepsLeft : ℝ → NNReal → Omega → ℝ)
    (hAdapt : ∀ e : ℝ, 0 < e → e < 1 → Adapted F (Xeps e))
    (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 ->
      ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => Xeps epsilon s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (XepsLeft epsilon t omega))),
    ∀ (T : NNReal), 0 < T ->
          ∀ (M : Real -> NNReal -> Omega -> Real),
            (∀ epsilon : Real, 0 < epsilon -> epsilon < 1 ->
              (∀ t omega, M epsilon t omega = (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
        {x : Real | epsilon < |x| ∧ |x| < 1},
        z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega)
        ∂(N.N omega)) -
      (∫ s in Set.Icc (0 : Real) (t : Real),
        (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1},
          x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
          ∂triplet.levyMeasure) ∂volume)) ∧
              MeasureTheory.Martingale (M epsilon) F P) ->
    ∀ a b : ℝ, 0 < a → a < b → b < 1 →
      (∫ ω, (M a T ω - M b T ω)^2 ∂P) ≤
        (∫ ω, ∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ z, (({w : ℝ | a < |w| ∧ |w| < 1}).indicator
              (fun w => w * fSpace s (XepsLeft a s.toNNReal ω)) z -
            ({w : ℝ | b < |w| ∧ |w| < 1}).indicator
              (fun w => w * fSpace s (XepsLeft b s.toNNReal ω)) z)^2
              ∂triplet.levyMeasure ∂volume ∂P) := by
  intro Ω m P hP F X triplet hSigma hFiltration N hFuture hPast fSpace hJoint
    K hK hBound Xeps XepsLeft hAdapt hXepsLeft T hT M hM a b ha hab hb
  classical
  have hex (e : ℝ) : 0 < e → e < 1 →
      ∃ V : NNReal → Ω → ℝ, IsStronglyPredictable F V ∧
        ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → V t ω = XepsLeft e t ω := by
    intro he he1
    exact Kyprianou.Ch04.adaptedAELeftPredictableVersionV1 P X F hFiltration
      (Xeps e) (XepsLeft e) (hAdapt e he he1) (hXepsLeft e he he1)
  have hall (e : ℝ) : ∃ V : NNReal → Ω → ℝ,
      (0 < e → e < 1 → IsStronglyPredictable F V ∧
        ∀ᵐ ω ∂P, ∀ t : NNReal, 0 < t → V t ω = XepsLeft e t ω) := by
    by_cases h : 0 < e ∧ e < 1
    · obtain ⟨V,hV,hEq⟩ := hex e h.1 h.2
      exact ⟨V,fun _ _ => ⟨hV,hEq⟩⟩
    · exact ⟨fun _ _ => 0,fun he he1 => (h ⟨he,he1⟩).elim⟩
  choose V hV using hall
  exact Kyprianou.Ch04.predictableVersionCutoffRawEnergyV1 P F triplet N hFuture hPast
    fSpace hJoint K hK hBound XepsLeft V (fun e he he1 => (hV e he he1).1)
    (fun e he he1 => (hV e he he1).2) T hT M hM a b ha hab hb
