-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovFiniteVectorLawOfPrefixRectanglesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:23:49.879817+00:00
-- url     : https://prove2.me/submissions/8801cf5b-a92d-43b1-b2a1-810c9003bcff

import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsFiniteMeasure P] (A : Set Omega) (n : ℕ)
    (U V : Omega → (Fin n → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (hRect : ∀ C : ℕ → Set ℝ, (∀ k, MeasurableSet (C k)) →
      P (A ∩ {w | ∀ k : ℕ, ∀ hk : k < n, U w ⟨k,hk⟩ ∈ C k}) =
        P A * P {w | ∀ k : ℕ, ∀ hk : k < n, V w ⟨k,hk⟩ ∈ C k}) :
    Measure.map U (P.restrict A) = P A • Measure.map V P := by
  classical
  apply AvramDividend.Classical.piPathMeasure_eq_of_finite_cylinder_masses
  · rw [Measure.map_apply hU MeasurableSet.univ, Set.preimage_univ]
    exact measure_ne_top (P.restrict A) Set.univ
  intro J B hB
  let C (i : ℕ) : Set ℝ := if hi : i < n then
    if (⟨i, hi⟩ : Fin n) ∈ J then B ⟨i, hi⟩ else Set.univ else Set.univ
  have hC (i : ℕ) : MeasurableSet (C i) := by
    dsimp [C]
    split_ifs with hi hj
    · exact hB _ hj
    · exact MeasurableSet.univ
    · exact MeasurableSet.univ
  let R := Set.pi (J : Set (Fin n)) B
  have hR : MeasurableSet R :=
    MeasurableSet.pi J.countable_toSet (fun i hi => hB i (Finset.mem_coe.mp hi))
  have hp (W : Omega → (Fin n → ℝ)) :
      W ⁻¹' R = {w | ∀ i : ℕ, ∀ hi : i < n, W w ⟨i,hi⟩ ∈ C i} := by
    ext w
    change (∀ i : Fin n, i ∈ J → W w i ∈ B i) ↔ _
    constructor
    · intro hh i hi
      by_cases hj : (⟨i, hi⟩ : Fin n) ∈ J
      · simpa [C, hi, hj] using hh ⟨i, hi⟩ hj
      · simp [C, hi, hj]
    · intro hh i hj
      simpa [C, i.isLt, hj] using hh i.val i.isLt
  change Measure.map U (P.restrict A) R = (P A • Measure.map V P) R
  rw [Measure.map_apply hU hR, Measure.restrict_apply (hU hR), Set.inter_comm,
    Measure.smul_apply, Measure.map_apply hV hR, hp U, hp V]
  exact hRect C hC
