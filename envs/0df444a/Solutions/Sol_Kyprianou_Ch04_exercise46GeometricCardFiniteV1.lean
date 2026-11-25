-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46GeometricCardFiniteV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:33:29.189582+00:00
-- url     : https://prove2.me/submissions/b12d1c61-0560-4de7-a903-6abc298d0dd9

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega T : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → Set T) (p : Real) (hp : 0 < p) (hp1 : p < 1)
    (htail : ∀ k : Nat,
      (P {omega | ((k + 1 : Nat) : ENat) ≤ (B omega).encard}).toReal =
        (1 - p) ^ k) :
    ∀ᵐ omega ∂P, (B omega).Finite := by
  let E : Set Omega := {omega | ¬ (B omega).Finite}
  have hle (k : Nat) : (P E).toReal ≤ (1 - p) ^ k := by
    rw [← htail k]
    apply ENNReal.toReal_mono (measure_ne_top P _)
    apply measure_mono
    intro omega ho
    have ht : (B omega).encard = ⊤ := by
      by_contra hn
      exact ho (Set.encard_ne_top_iff.mp hn)
    simp [ht]
  have hl : Tendsto (fun k : Nat => (1 - p) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have hz : (P E).toReal = 0 :=
    le_antisymm (ge_of_tendsto hl (Eventually.of_forall hle)) ENNReal.toReal_nonneg
  have hnull : P E = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top P E)
  exact ae_iff.mpr hnull
