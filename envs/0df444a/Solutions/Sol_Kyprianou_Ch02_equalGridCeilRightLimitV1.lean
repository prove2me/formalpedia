-- Prove2me | solution 1 for Kyprianou.Ch02.equalGridCeilRightLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:46:09.437573+00:00
-- url     : https://prove2.me/submissions/b5fb9658-170e-4c7d-b57e-f1dc74103801

import Theorems.Thm_Kyprianou_Ch02_equalGridCeilSqueezeV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (a b : ℝ≥0) (hab : a < b) :
    let g : ℕ → ℕ → ℝ≥0 := fun n k =>
      a + (b - a) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let r : ℕ → ℝ≥0 → ℝ≥0 := fun n x =>
      g n ⌈(x - a) * ((n + 1 : ℕ) : ℝ≥0) / (b - a)⌉₊
    ∀ x ∈ Icc a b, Tendsto (fun n => r n x) atTop (nhdsWithin x (Ici x)) := by
  dsimp only
  let g (n k : ℕ) : ℝ≥0 := a + (b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
  let q (n : ℕ) (x : ℝ≥0) : ℝ≥0 :=
    (x-a)*((n+1 : ℕ) : ℝ≥0)/(b-a)
  let r (n : ℕ) (x : ℝ≥0) := g n ⌈q n x⌉₊
  have hd : 0 < b-a := tsub_pos_of_lt hab
  intro x hx
  change Tendsto (fun n => r n x) atTop (nhdsWithin x (Ici x))
  have H := Kyprianou.Ch02.equalGridCeilSqueezeV1 a b hab
  have hlow (n : ℕ) : x ≤ r n x := (H n x hx).1
  have hup (n : ℕ) : r n x ≤ x+(b-a)/((n+1 : ℕ) : ℝ≥0) := (H n x hx).2
  have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have htop : Tendsto (fun n : ℕ => (x : ℝ) +
      ((b-a : ℝ≥0) : ℝ)/((n+1 : ℕ) : ℝ)) atTop (nhds (x : ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (hn.const_div_atTop ((b-a : ℝ≥0) : ℝ))
  have hr : Tendsto (fun n => (r n x : ℝ)) atTop (nhds (x : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop
      (fun n => by exact_mod_cast hlow n) (fun n => by exact_mod_cast hup n)
  exact tendsto_nhdsWithin_iff.mpr ⟨NNReal.tendsto_coe.mp hr,
    Eventually.of_forall (fun n => hlow n)⟩
