-- Prove2me | solution 1 for Kyprianou.Ch02.equalGridPositiveTimeCoverV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:07:46.382448+00:00
-- url     : https://prove2.me/submissions/2e5a98c0-6605-440f-9910-199ff8a1c28d

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Positivity
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    (T t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T) (n : ℕ) :
    let d : ℝ := (T : ℝ) / ((n+1 : ℕ) : ℝ)
    ∃ k : ℕ, k < n+1 ∧
      (t : ℝ) ∈ Set.Ioc ((k : ℝ) * d) (((k+1 : ℕ) : ℝ) * d) := by
  dsimp only
  let d : ℝ := (T : ℝ) / ((n+1 : ℕ) : ℝ)
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have htT' : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
  have hd : 0 < d := div_pos (ht'.trans_le htT') (by positivity)
  let q : ℝ := (t : ℝ) / d
  have hq : 0 < q := div_pos ht' hd
  have hqmax : q ≤ ((n+1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ hd).2
    dsimp [d]
    field_simp
    <;> nlinarith
  let m : ℕ := ⌈q⌉₊
  have hm : 0 < m := Nat.ceil_pos.mpr hq
  have hmmax : m ≤ n+1 := Nat.ceil_le.mpr hqmax
  have hkm : m-1+1 = m := by omega
  refine ⟨m-1, by omega, ?_, ?_⟩
  · change ((m-1 : ℕ) : ℝ) * d < (t : ℝ)
    apply (lt_div_iff₀ hd).1
    exact Nat.lt_ceil.mp (show m-1 < ⌈q⌉₊ by omega)
  · change (t : ℝ) ≤ (((m-1+1 : ℕ) : ℝ)) * d
    rw [hkm]
    exact (div_le_iff₀ hd).1 (Nat.le_ceil q)
