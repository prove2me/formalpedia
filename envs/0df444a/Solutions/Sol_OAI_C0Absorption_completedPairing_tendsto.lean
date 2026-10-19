-- Prove2me | solution 1 for OAI.C0Absorption.completedPairing_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:26:19.449041+00:00
-- url     : https://prove2.me/submissions/2f5e4881-75ca-44e2-9bc0-b91d039b3695

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open UniformSpace Completion
variable {S : Type*} [MetricSpace S] (L : ℕ → Set (S → ℝ)) (o : S)
theorem h41_dense_lip {A X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
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

theorem solution (f : ℕ → S → ℝ) (g : S → ℝ) (K : ℝ≥0)
    (hbound : ∀ n (m : PreSpace L o), |pairing S (f n) m| ≤ K * ‖m‖)
    (hpoint : ∀ s, Filter.Tendsto (fun n => f n s) Filter.atTop (nhds (g s))) :
    (∀ m : PreSpace L o, |pairing S g m| ≤ K * ‖m‖) ∧
    ∀ z : TestSpace L o,
      Filter.Tendsto (fun n => completedPairing L o (f n) z) Filter.atTop
        (nhds (completedPairing L o g z)) := by
  have hpt : ∀ m : PreSpace L o, Filter.Tendsto (fun n => pairing S (f n) m) Filter.atTop
      (nhds (pairing S g m)) := by
    intro m
    simp only [pairing, LinearMap.comp_apply, Submodule.subtype_apply,
      Finsupp.linearCombination_apply, Finsupp.sum]
    exact tendsto_finset_sum _ (fun s _ => (hpoint s).const_smul _)
  have hg : ∀ m : PreSpace L o, |pairing S g m| ≤ K * ‖m‖ := by
    intro m
    exact le_of_tendsto' ((continuous_abs.tendsto _).comp (hpt m)) (fun n => hbound n m)
  refine ⟨hg, ?_⟩
  have hlip : ∀ (F : S → ℝ), (∀ m : PreSpace L o, |pairing S F m| ≤ K * ‖m‖) →
      LipschitzWith K (completedPairing L o F) := by
    intro F hF
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have hc : Continuous (completedPairing L o F) := Completion.continuous_extension
    refine Completion.induction_on₂ (p := fun z w : Completion (PreSpace L o) =>
      dist (completedPairing L o F z) (completedPairing L o F w) ≤ K * dist z w) z w ?_ ?_
    · exact isClosed_le ((hc.comp continuous_fst).dist (hc.comp continuous_snd))
        (continuous_const.mul continuous_dist)
    · intro a b
      have ha := completedPairing_coe L o F K hF a
      have hb := completedPairing_coe L o F K hF b
      change dist (completedPairing L o F (toTestSpace L o a)) (completedPairing L o F (toTestSpace L o b))
        ≤ K * dist (a : Completion (PreSpace L o)) b
      rw [ha, hb, Completion.dist_eq]
      exact (initialPairing_lipschitz L o F K hF).dist_le_mul a b
  intro z
  refine h41_dense_lip (toTestSpace L o) Completion.denseRange_coe (fun n => completedPairing L o (f n))
    (completedPairing L o g) K (fun n => hlip _ (hbound n)) (hlip _ hg) ?_ z
  intro a
  simp only [completedPairing_coe L o _ K (hbound _), completedPairing_coe L o g K hg]
  exact hpt a

