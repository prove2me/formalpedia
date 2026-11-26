-- Prove2me | solution 1 for Kyprianou.Ch04.exercise44CompensatedJumpL2IsometryV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:49:23.467029+00:00
-- url     : https://prove2.me/submissions/1f3c13b5-63c7-4289-9d5a-8e98603be835

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_commonNullPredictableENNRepresentative
import Theorems.Thm_Kyprianou_Ch04_fullPredictableClockAgreement
import Theorems.Thm_Kyprianou_Ch04_fullPredictablePhysicalL2Core
import Theorems.Thm_Kyprianou_Ch04_nonnegativeHorizonPhysicalFubini
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
/-- Exercise 4.4 (p. 107). Second-moment isometry for the compensated jump integral. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (hFuture : IsFutureIndependentPoissonMeasure P levyMeasure F N)
    (hPast : forall (u : NNReal) (B : Set (Real × Real)),
      MeasurableSet B →
      B ⊆ Set.prod (Set.Icc (0 : Real) (u : Real)) Set.univ →
      Measurable[F u] (fun omega => N.N omega B))
    (phi : Real -> Real -> Omega -> Real)
    (hPhi : IsAdmissiblePoissonKernel P F phi)
    (hCommon : ∀ᵐ omega ∂P, ∀ (x : Real) (t : NNReal), 0 < t →
      Tendsto (fun s : Real => phi s x omega)
        (nhdsWithin (t : Real) (Set.Iio (t : Real)))
        (nhds (phi (t : Real) x omega)))
    (hL1 : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure)
          ∂volume) ∂P) < ⊤)
    (hL2 : forall t : NNReal,
      (∫⁻ omega,
        (∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (∫⁻ x, ENNReal.ofReal ((phi s x omega) ^ 2) ∂levyMeasure)
          ∂volume) ∂P) < ⊤) :
    forall t : NNReal,
      (∫ omega,
        ((∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
            phi z.1 z.2 omega ∂(N.N omega)) -
          (∫ s in Set.Icc (0 : Real) (t : Real),
            (∫ x, phi s x omega ∂levyMeasure) ∂volume)) ^ 2 ∂P) =
      (∫ omega,
        (∫ s in Set.Icc (0 : Real) (t : Real),
          (∫ x, (phi s x omega) ^ 2 ∂levyMeasure)
          ∂volume) ∂P) := by
  intro t
  obtain ⟨psi,hpsi,hEq⟩ := commonNullPredictableENNRepresentative P F phi hPhi hCommon
  obtain ⟨mu,hClock⟩ := fullPredictableClockAgreement P levyMeasure F N hFuture t
  letI : MeasurableSpace ((NNReal × Omega) × ℝ) :=
    F.predictable.prod (inferInstance : MeasurableSpace ℝ)
  let g : ((NNReal × Omega) × ℝ) → ℝ := fun a => (psi (a.1.1 : ℝ) a.2 a.1.2).toReal
  have hgm : Measurable g := hpsi.ennreal_toReal
  have hg0 (a : (NNReal × Omega) × ℝ) : 0 ≤ g a := ENNReal.toReal_nonneg
  let U := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
  have hU : MeasurableSet U := measurableSet_Icc.prod MeasurableSet.univ
  let q := fun (w : Omega) (z : ℝ × ℝ) => ((z.1.toNNReal,w),z.2)
  have hRep : ∀ᵐ w ∂P, ∀ z ∈ U, g (q w z) = phi z.1 z.2 w := by
    filter_upwards [hEq] with w hw
    intro z hz
    dsimp only [g,q]
    rw [Real.coe_toNNReal _ hz.1.1, hw, ENNReal.toReal_ofReal (hPhi.1 _ _ _)]
  let k : Omega → ℝ × ℝ → ℝ := fun w z => phi z.1 z.2 w
  have hkm : Measurable (fun z : Omega × (ℝ × ℝ) => k z.1 z.2) :=
    hPhi.2.1.comp measurable_swap
  have hF1 := nonnegativeHorizonPhysicalFubini P levyMeasure t k hkm
    (fun w z => hPhi.1 z.1 z.2 w) (hL1 t)
  have hF2 := nonnegativeHorizonPhysicalFubini P levyMeasure t (fun w z => (k w z)^2)
    (hkm.pow_const 2) (fun w z => sq_nonneg _) (hL2 t)
  have henergy (f : ℝ → ℝ) (hf : Measurable f)
      (hfin : (∫⁻ w, ∫⁻ z in U, ENNReal.ofReal (f (k w z))
        ∂referenceIntensity levyMeasure ∂P) < ⊤) :
      (∫⁻ a, ENNReal.ofReal (f (g a)) ∂mu) < ⊤ := by
    rw [(hClock (fun a => ENNReal.ofReal (f (g a)))
      (ENNReal.measurable_ofReal.comp (hf.comp hgm))).2.2.2]
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hfin
    filter_upwards [hRep] with w hw
    exact setLIntegral_congr_fun hU fun z hz => by rw [hw z hz]
  have h1 : (∫⁻ w, ∫⁻ z in U, ENNReal.ofReal (k w z)
        ∂referenceIntensity levyMeasure ∂P) < ⊤ :=
    lt_of_eq_of_lt (lintegral_congr hF1.1) (hL1 t)
  have h2 : (∫⁻ w, ∫⁻ z in U, ENNReal.ofReal ((k w z)^2)
        ∂referenceIntensity levyMeasure ∂P) < ⊤ :=
    lt_of_eq_of_lt (lintegral_congr hF2.1) (hL2 t)
  have hgi : Integrable g mu :=
    ⟨hgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall hg0)).2 (henergy id measurable_id h1)⟩
  have hg2 : MemLp g 2 mu := by
    apply (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).2
    exact ⟨(hgm.pow_const 2).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun a => sq_nonneg (g a))).2
        (henergy (fun x => x^2) (measurable_id.pow_const 2) h2)⟩
  have hc := fullPredictablePhysicalL2Core P levyMeasure F N hFuture hPast t rfl
    mu hClock g hgm hgi hg2
  have hleft : (fun w => ((∫ z in U, phi z.1 z.2 w ∂(N.N w)) -
      ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, phi s x w ∂levyMeasure ∂volume)^2) =ᵐ[P]
      fun w => ((∫ z in U, g (q w z) ∂(N.N w)) -
        ∫ z in U, g (q w z) ∂referenceIntensity levyMeasure)^2 := by
    filter_upwards [hRep,hF1.2] with w hw hfw
    have hraw := setIntegral_congr_fun (μ := N.N w) hU (fun z hz => hw z hz)
    have href := setIntegral_congr_fun (μ := referenceIntensity levyMeasure) hU
      (fun z hz => hw z hz)
    rw [hraw, href, hfw]
  have hright : (fun w => ∫ z in U, (g (q w z))^2 ∂referenceIntensity levyMeasure) =ᵐ[P]
      fun w => ∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∫ x, (phi s x w)^2 ∂levyMeasure ∂volume := by
    filter_upwards [hRep,hF2.2] with w hw hfw
    exact (setIntegral_congr_fun hU (fun z hz => by rw [hw z hz])).trans hfw
  exact (integral_congr_ae hleft).trans (hc.2.trans (integral_congr_ae hright))
