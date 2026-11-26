-- Prove2me | solution 1 for Kyprianou.Ch04.signedRawHorizonRegularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:21:05.334052+00:00
-- url     : https://prove2.me/submissions/c248cfa3-d3b9-4eff-836f-d5fe6dc05c98

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_rawCompensationClockRegularity
import Theorems.Thm_Kyprianou_Ch04_nonnegativePredictableJumpCompensationCommonNullV2
import Theorems.Thm_Kyprianou_Ch04_exactSignedRandomIntegralMeasurable
import Theorems.Thm_Kyprianou_Ch04_finiteRandomIntegralSplitAE
open MeasureTheory Filter LevyStochCalc.Poisson Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Raw signed Poisson integration has exact adaptedness and a.e. signed-part splitting. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure ℝ) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : IsFutureIndependentPoissonMeasure P nu F N)
    (k : ℝ → ℝ → Omega → ℝ)
    (hm : Measurable (fun z : (ℝ × ℝ) × Omega => k z.1.1 z.1.2 z.2))
    (t : NNReal)
    (hPast : ∀ B : Set (ℝ × ℝ), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ →
      Measurable[F t] (fun w => N.N w B))
    (hLocal : ∀ n : ℕ, ∀ w : Omega,
      N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets nu n) ≠ ⊤)
    (hP : IsAdmissiblePoissonKernel P F (fun s x w => max (k s x w) 0))
    (hN : IsAdmissiblePoissonKernel P F (fun s x w => max (-k s x w) 0))
    (hcP : ∀ᵐ w ∂P, ∀ (x : ℝ) (u : NNReal), 0 < u →
      Tendsto (fun s : ℝ => max (k s x w) 0) (nhdsWithin (u : ℝ) (Set.Iio (u : ℝ)))
        (nhds (max (k (u : ℝ) x w) 0)))
    (hcN : ∀ᵐ w ∂P, ∀ (x : ℝ) (u : NNReal), 0 < u →
      Tendsto (fun s : ℝ => max (-k s x w) 0) (nhdsWithin (u : ℝ) (Set.Iio (u : ℝ)))
        (nhds (max (-k (u : ℝ) x w) 0)))
    (hmP : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then max (k z.2.1 z.2.2 z.1) 0 else 0))
    (hmN : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then max (-k z.2.1 z.2.2 z.1) 0 else 0))
    (hp : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (k s x w) 0) ∂nu ∂volume ∂P) < ⊤)
    (hn : (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (max (-k s x w) 0) ∂nu ∂volume ∂P) < ⊤) :
    let V := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
    StronglyMeasurable[F t] (fun w => ∫ z in V, k z.1 z.2 w ∂(N.N w)) ∧
    ∀ᵐ w ∂P, (∫ z in V, k z.1 z.2 w ∂(N.N w)) =
      (∫ z in V, max (k z.1 z.2 w) 0 ∂(N.N w)) -
      ∫ z in V, max (-k z.1 z.2 w) 0 ∂(N.N w) := by
  let V := Set.Icc (0 : ℝ) (t : ℝ) ×ˢ (Set.univ : Set ℝ)
  let R := fun w => (N.N w).restrict V
  let f := fun (w : Omega) (z : ℝ × ℝ) => k z.1 z.2 w
  have hf (w : Omega) : Measurable (f w) :=
    hm.comp (measurable_id.prodMk measurable_const)
  have hRP := rawCompensationClockRegularity P nu F _ hP t hmP N hPast hLocal
  have hRN := rawCompensationClockRegularity P nu F _ hN t hmN N hPast hLocal
  have hRPfin := lt_of_eq_of_lt
    (nonnegativePredictableJumpCompensationCommonNullV2 P nu F N hFuture _ hP hcP t) hp
  have hRNfin := lt_of_eq_of_lt
    (nonnegativePredictableJumpCompensationCommonNullV2 P nu F N hFuture _ hN hcN t) hn
  have ha : StronglyMeasurable[F t] (fun w => ∫ z, f w z ∂(R w)) := by
    letI : MeasurableSpace Omega := F t
    exact exactSignedRandomIntegralMeasurable R f hf hRP.1 hRN.1
  have hs := finiteRandomIntegralSplitAE P R f hf
    (hRP.1.mono (F.le t) le_rfl).aemeasurable
    (hRN.1.mono (F.le t) le_rfl).aemeasurable hRPfin hRNfin
  exact ⟨ha, hs.mono fun _ h => h.2⟩
