-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonZeroRateCemetery
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:56:51.482167+00:00
-- url     : https://prove2.me/submissions/6261e19e-13d6-4997-8050-0a2c94bee97c

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_markedPoissonZeroIntensityAllCountsVanish
import Theorems.Thm_Kyprianou_Ch06_markedPoissonNoPointPathsYieldCemeteryAe
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch06

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    let sigma : Omega → WithTop NNReal := fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A})
    (n A = 0 →
      P {omega | sigma omega = ⊤ ∧ firstMark omega = none} = 1) := by
  dsimp only
  intro hZero
  have hNoPoints : ∀ᵐ omega ∂P, ∀ t : NNReal, N omega t A = 0 :=
    Kyprianou.Ch06.markedPoissonZeroIntensityAllCountsVanish
      P n N hPPP A hA hZero
  have hCemetery :=
    Kyprianou.Ch06.markedPoissonNoPointPathsYieldCemeteryAe
      P N A firstMark hMark hNoPoints
  let S : Set Omega :=
    {omega | sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | 0 < t ∧ 0 < N omega t A}) = ⊤ ∧
      firstMark omega = none}
  change P S = 1
  have hmem : ∀ᵐ omega ∂P, omega ∈ S := by
    simpa [S] using hCemetery
  have hcomp : P Sᶜ = 0 := (MeasureTheory.mem_ae_iff).mp hmem
  have htotal : P Set.univ ≤ P S + P Sᶜ := by
    simpa only [Set.union_compl_self] using
      measure_union_le (μ := P) S Sᶜ
  have hlower : (1 : ENNReal) ≤ P S := by
    simpa [measure_univ, hcomp] using htotal
  have hupper : P S ≤ 1 := by
    simpa [measure_univ] using
      measure_mono (μ := P) (Set.subset_univ S)
  exact le_antisymm hupper hlower
