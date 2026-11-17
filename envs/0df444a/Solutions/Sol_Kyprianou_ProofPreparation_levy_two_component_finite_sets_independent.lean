-- Prove2me | solution 1 for Kyprianou.ProofPreparation.levy_two_component_finite_sets_independent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:46:24.34612+00:00
-- url     : https://prove2.me/submissions/078ffe76-90bc-4117-b1fd-48d3d1afd65f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Theorems.Thm_Kyprianou_ProofPreparation_finite_pair_vectors_iIndepFun
import Theorems.Thm_Kyprianou_ProofPreparation_finite_pair_vectors_aemeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false

private theorem levy_fixed_time_aemeasurable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : IsLevyProcess X P) (t : ℝ≥0) :
    AEMeasurable (X t) P := by
  have hs := (hX.stationary_increments 0 t).aemeasurable_fst
  have hz (ω : Ω) : X 0 ω = 0 := congrFun hX.start_zero ω
  change AEMeasurable (fun ω => X (0 + t) ω - X 0 ω) P at hs
  simpa [hz] using hs

/-- Finite dimensional independence of two-component sums and the
    third component, with distinct finite observation sets allowed. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : IsLevyProcess Xgauss P)
    (hlarge : IsLevyProcess Xlarge P)
    (hsmall : IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall)
    (I J : Finset ℝ≥0) :
    IndepFun
      (fun ω => fun i : I => Xgauss i ω + Xlarge i ω)
      (fun ω => fun j : J => Xsmall j ω) P := by
  let F : Fin 3 → Ω → (ℝ≥0 → ℝ) :=
    fun i ω => fun s =>
      if i = 0 then Xgauss s ω else
      if i = 1 then Xlarge s ω else Xsmall s ω
  have hF : iIndepFun F P := hind
  let G : Fin 3 → Ω → ((I → ℝ) × (J → ℝ)) :=
    fun i ω => ((fun s : I => F i ω s), (fun s : J => F i ω s))
  have hG : iIndepFun G P :=
    finite_pair_vectors_iIndepFun P F hF I J
  have hFae : ∀ (i : Fin 3) (s : ℝ≥0),
      AEMeasurable (fun ω => F i ω s) P := by
    intro i s
    fin_cases i
    · simpa [F] using levy_fixed_time_aemeasurable P Xgauss hgauss s
    · simpa [F] using levy_fixed_time_aemeasurable P Xlarge hlarge s
    · simpa [F] using levy_fixed_time_aemeasurable P Xsmall hsmall s
  have hGae : ∀ i : Fin 3, AEMeasurable (G i) P :=
    finite_pair_vectors_aemeasurable P F hFae I J
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hp : IndepFun (fun ω => (G 0 ω, G 1 ω)) (G 2) P :=
    hG.indepFun_prodMk₀ hGae 0 1 2 h02 h12
  have hadd : Measurable
      (fun a : ((I → ℝ) × (J → ℝ)) × ((I → ℝ) × (J → ℝ)) =>
        fun s : I => a.1.1 s + a.2.1 s) := by
    apply measurable_pi_iff.mpr
    intro s
    exact (((measurable_pi_apply s).comp measurable_fst).comp measurable_fst).add
      (((measurable_pi_apply s).comp measurable_fst).comp measurable_snd)
  have hproj : Measurable
      (fun a : (I → ℝ) × (J → ℝ) => a.2) := measurable_snd
  have hs := hp.comp hadd hproj
  simpa [G, F, Function.comp_def] using hs
