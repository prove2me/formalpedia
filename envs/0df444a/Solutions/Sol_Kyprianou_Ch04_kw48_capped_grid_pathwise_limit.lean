-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_capped_grid_pathwise_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:41:30.238219+00:00
-- url     : https://prove2.me/submissions/da95a6a0-48ef-4247-8d01-709884a63dee

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_actual_grid_correction_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_product_grid_pathwise_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The capped uniform product grid converges pathwise to the signed increment. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (a b : NNReal) (hab : a ≤ b) (w : Ω) :
    let u : Nat → Nat → NNReal := fun n i =>
      a+(b-a)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
    Tendsto (fun n => Q L Psi alpha beta (u n) (n+1) w) atTop
      (nhds (M L Psi alpha beta a w-M L Psi alpha beta b w)) := by
  dsimp only
  let u : Nat → Nat → NNReal := fun n i =>
    a+(b-a)*((min i (n+1):Nat):NNReal)/((n+1:Nat):NNReal)
  obtain ⟨hu,h0,hN,hT,hMesh,hDelta⟩ :=
    Kyprianou.Ch04.kw47_capped_uniform_grid a b hab
  have hC := Kyprianou.Ch04.kw48_actual_grid_correction_limit L Psi alpha beta
    w a b hab u (fun n => n+1) hu h0 hN
    (fun n => ((b:Real)-(a:Real))/((n+1:Nat):Real)) hDelta
    (fun n i hi => le_of_eq (hMesh n i hi))
  exact Kyprianou.Ch04.kw48_product_grid_pathwise_limit L Psi alpha beta
    a b w u (fun n => n+1) h0 hN hC
