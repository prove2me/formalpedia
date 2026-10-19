-- Prove2me | solution 1 for OAI.C0Absorption.tendsto_of_dense_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:03:52.252808+00:00
-- url     : https://prove2.me/submissions/5e74a5cc-237a-49b1-9cc1-652d1827f8a7

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset


theorem solution {A X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (d : A → X) (hd : DenseRange d) (f : ℕ → X → Y) (g : X → Y) (K : ℝ≥0)
    (hf : ∀ n, LipschitzWith K (f n)) (hg : LipschitzWith K g)
    (h : ∀ a, Filter.Tendsto (fun n => f n (d a)) Filter.atTop (nhds (g (d a))))
    (x : X) : Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hK : (0:ℝ) < 3 * ((K:ℝ) + 1) := by positivity
  obtain ⟨a, ha⟩ := hd.exists_dist_lt x (div_pos hε hK)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (h a)) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := (hf n).dist_le_mul x (d a)
  have h2 := hg.dist_le_mul x (d a)
  have h3 := hN n hn
  have hda : (K:ℝ) * dist x (d a) ≤ ε / 3 := by
    have : (K:ℝ) * dist x (d a) ≤ ((K:ℝ)+1) * (ε / (3 * ((K:ℝ) + 1))) := by
      apply mul_le_mul (by linarith) ha.le dist_nonneg (by positivity)
    have e : ((K:ℝ)+1) * (ε / (3 * ((K:ℝ) + 1))) = ε / 3 := by field_simp
    linarith
  have hda' : (K:ℝ) * dist x (d a) < ε / 3 ∨ True := Or.inr trivial
  calc dist (f n x) (g x) ≤ dist (f n x) (f n (d a)) + dist (f n (d a)) (g (d a)) + dist (g (d a)) (g x) :=
        dist_triangle4 _ _ _ _
    _ < ε := by rw [dist_comm (g (d a))]; linarith

