-- Prove2me | solution 1 for Kyprianou.Ch03.supInfDuality_of_dyadicPairLaws
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T10:49:56.52897+00:00
-- url     : https://prove2.me/submissions/bfd20fed-d8d6-4fa5-a1ce-4e9a629bd316

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch03_supInfDyadicPairsAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_supInfDyadicExtremaAELimitsV1
import Theorems.Thm_Kyprianou_Ch02_identDistribPairOfAELimitsV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t)
    (hGrid : ∀ n : ℕ,
      Measure.map
      (fun omega : Omega =>
        let a := sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
          X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) omega))
        (a, a - X t omega)) P =
    Measure.map
      (fun omega : Omega =>
        let b := sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
          X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) omega))
        (X t omega - b, -b)) P) :
    Measure.map
      (fun omega : Omega =>
        let a := LevyExtrema.SBA.runSup (fun s => X s omega) t
        (a, a - X t omega)) P =
    Measure.map
      (fun omega : Omega =>
        let b := sInf ((fun s : NNReal => X s omega) '' Set.Icc 0 t)
        (X t omega - b, -b)) P := by
  let F (n : ℕ) (ω : Omega) :=
    let a := sSup (Set.range (fun i : Fin (2 ^ n + 1) =>
      X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω))
    (a, a - X t ω)
  let G (n : ℕ) (ω : Omega) :=
    let b := sInf (Set.range (fun i : Fin (2 ^ n + 1) =>
      X ((i.val : NNReal) * (t / ((2 ^ n : ℕ) : NNReal))) ω))
    (X t ω - b, -b)
  let f (ω : Omega) :=
    let a := LevyExtrema.SBA.runSup (fun s => X s ω) t
    (a, a - X t ω)
  let g (ω : Omega) :=
    let b := sInf ((fun s : NNReal => X s ω) '' Set.Icc 0 t)
    (X t ω - b, -b)
  have hLaw (n : ℕ) : IdentDistrib (F n) (G n) P P := by
    obtain ⟨hF, hG⟩ := Kyprianou.Ch03.supInfDyadicPairsAEMeasurableV1 P X hX t n
    exact ⟨hF, hG, hGrid n⟩
  have hLim := Kyprianou.Ch03.supInfDyadicExtremaAELimitsV1 P X hX t ht
  have hf : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (f ω)) := by
    filter_upwards [hLim] with ω hω
    exact hω.1.prodMk_nhds (hω.1.sub tendsto_const_nhds)
  have hg : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hLim] with ω hω
    exact (tendsto_const_nhds.sub hω.2).prodMk_nhds hω.2.neg
  exact (Kyprianou.Ch02.identDistribPairOfAELimitsV1 P F G f g hLaw hf hg).map_eq
