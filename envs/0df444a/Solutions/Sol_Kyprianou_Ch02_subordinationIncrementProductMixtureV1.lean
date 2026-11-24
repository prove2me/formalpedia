-- Prove2me | solution 1 for Kyprianou.Ch02.subordinationIncrementProductMixtureV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:53.347377+00:00
-- url     : https://prove2.me/submissions/c2f5997b-0f70-41da-b871-5547651e4f36

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_independentRandomTimeVectorIntegralV1
import Theorems.Thm_Kyprianou_Ch02_levyFixedIncrementTestV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0 → Ω → ℝ≥0)
    (hX : IsLevyProcess X P)
    (hτ : IsLevyProcess (fun t ω => (τ t ω : ℝ)) P)
    (hmon : ∀ᵐ ω ∂P, Monotone (fun t => τ t ω))
    (hind : iIndepFun (fun (i : Fin 2) (ω : Ω) => fun t : ℝ≥0 =>
      if i = 0 then X t ω else (τ t ω : ℝ)) P)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t)
    (H : Fin n → ℝ → ℂ) (hH : ∀ i, Measurable (H i))
    (hC : ∀ i x, ‖H i x‖ ≤ 1) :
    (∫ ω, ∏ i, H i (X (τ (t i.succ) ω) ω - X (τ (t i.castSucc) ω) ω) ∂P) =
      ∫ ω, ∏ i, (∫ ω', H i
        (X (((τ (t i.succ) ω : ℝ) - (τ (t i.castSucc) ω : ℝ)).toNNReal) ω') ∂P) ∂P := by
  let G (v : Fin (n + 1) → ℝ) := ∏ i : Fin n, H i (v i.succ - v i.castSucc)
  have hG : Measurable G := by
    unfold G
    fun_prop
  have hGbound (v : Fin (n + 1) → ℝ) : ‖G v‖ ≤ 1 := by
    simp only [G, norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hC i _)
  obtain ⟨_, hmix⟩ := Kyprianou.Ch02.independentRandomTimeVectorIntegralV1
    P X τ hX hτ hind (n + 1) t G hG
  change (∫ ω, G (fun i => X (τ (t i) ω) ω) ∂P) = _
  rw [hmix 1 hGbound]
  apply integral_congr_ae
  filter_upwards [hmon] with ω hw
  let r (i : Fin (n + 1)) := τ (t i) ω
  have hmi (i : Fin n) : AEMeasurable (increment X (r i.castSucc) (r i.succ)) P :=
    (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX _).sub
      (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX _)
  have hf := (hX.indep_increments n r (hw.comp ht)).integral_fun_prod_comp
    hmi (fun i => (hH i).aestronglyMeasurable)
  change (∫ ω', ∏ i : Fin n, H i (increment X (r i.castSucc) (r i.succ) ω') ∂P) = _
  rw [hf]
  apply Finset.prod_congr rfl
  intro i _
  exact Kyprianou.Ch02.levyFixedIncrementTestV1 P X hX
    (r i.castSucc) (r i.succ) (hw (ht (Fin.castSucc_le_succ i))) (H i) (hH i)
