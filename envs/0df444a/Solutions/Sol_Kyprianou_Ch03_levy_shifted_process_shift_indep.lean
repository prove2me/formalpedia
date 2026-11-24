-- Prove2me | solution 1 for Kyprianou.Ch03.levy_shifted_process_shift_indep
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T13:25:20.40798+00:00
-- url     : https://prove2.me/submissions/53446d5c-9a44-4bdd-af5a-23b51636ea33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_Kyprianou_Ch03_levy_future_path_indep_pastSigma

open MeasureTheory ProbabilityTheory DurrettProbability Set
open scoped NNReal

set_option autoImplicit false

/-!
Shifted-process form of Lévy path independence.

Reduction:
1. Algebra: the target future map equals `u ↦ X_(t+s+u) - X_(t+s)`.
2. Inclusion: `pastSigma Y s ≤ pastSigma X (t+s)` for `Y_u = X_(t+u)-X_t`.
3. Open: `levy_future_path_indep_pastSigma` at time `t+s`.
4. Mono: restrict the past σ-algebra under `Indep`.
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal)
    (s : NNReal) (_hs : 0 < s) :
    Indep
      (MeasurableSpace.comap
        (fun ω (u : NNReal) =>
          (X (t + (s + u)) ω - X t ω) - (X (t + s) ω - X t ω))
        MeasurableSpace.pi)
      (pastSigma (fun u ω => X (t + u) ω - X t ω) s) P := by
  -- (1) Algebraic simplification of the future path map
  have hpath :
      (fun ω (u : NNReal) =>
          (X (t + (s + u)) ω - X t ω) - (X (t + s) ω - X t ω)) =
        (fun ω (u : NNReal) => X (t + s + u) ω - X (t + s) ω) := by
    funext ω u
    simp [sub_sub, add_assoc]
  -- (2) pastSigma of the shifted process sits under pastSigma of X at time t+s
  have hle :
      pastSigma (fun u ω => X (t + u) ω - X t ω) s ≤ pastSigma X (t + s) := by
    refine iSup₂_le fun v hv => ?_
    have hv' : t + v ∈ Set.Iic (t + s) := Set.mem_Iic.mpr (add_le_add le_rfl hv)
    have hXv :
        MeasurableSpace.comap (X (t + v)) (inferInstance : MeasurableSpace ℝ) ≤
          pastSigma X (t + s) :=
      le_iSup₂_of_le (t + v) hv' le_rfl
    have hXt :
        MeasurableSpace.comap (X t) (inferInstance : MeasurableSpace ℝ) ≤
          pastSigma X (t + s) :=
      le_iSup₂_of_le t (Set.mem_Iic.mpr le_self_add) le_rfl
    have hmeas_v :
        @Measurable Omega ℝ (pastSigma X (t + s)) _ (X (t + v)) :=
      measurable_iff_comap_le.2 hXv
    have hmeas_t :
        @Measurable Omega ℝ (pastSigma X (t + s)) _ (X t) :=
      measurable_iff_comap_le.2 hXt
    exact measurable_iff_comap_le.1 (hmeas_v.sub hmeas_t)
  -- (3)+(4) Path independence at time t+s, then restrict the past
  have hInd := levy_future_path_indep_pastSigma P X hX (t + s)
  -- Rewrite the left comap via hpath, then mono on the right
  rw [hpath]
  exact indep_of_indep_of_le_right hInd hle
