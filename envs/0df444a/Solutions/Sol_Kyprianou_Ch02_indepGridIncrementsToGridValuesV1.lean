-- Prove2me | solution 1 for Kyprianou.Ch02.indepGridIncrementsToGridValuesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:26:00.553168+00:00
-- url     : https://prove2.me/submissions/2c33e91a-de37-49eb-a5a9-866347cfdbe2

import Mathlib
import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : ℝ≥0 → Ω → ℝ) (hA0 : A 0 = fun _ => 0)
    (hB0 : B 0 = fun _ => 0) (n : ℕ)
    (t : Fin (n+1) → ℝ≥0) (ht0 : t 0 = 0)
    (hi : IndepFun (fun ω (i : Fin n) => A (t i.succ) ω - A (t i.castSucc) ω)
      (fun ω (i : Fin n) => B (t i.succ) ω - B (t i.castSucc) ω) P) :
    IndepFun (fun ω k => A (t k) ω) (fun ω k => B (t k) ω) P := by

  classical
  let F (v : Fin n → ℝ) (k : Fin (n+1)) : ℝ :=
    ∑ j ∈ Finset.range k.val, if hj : j < n then v ⟨j,hj⟩ else 0
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro k
    unfold F
    apply Finset.measurable_sum
    intro j hj
    split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const
  have telescope (C : ℝ≥0 → Ω → ℝ) (hC : C 0 = fun _ => 0) (ω : Ω)
      (k : Fin (n+1)) :
      F (fun i => C (t i.succ) ω - C (t i.castSucc) ω) k = C (t k) ω := by
    induction k using Fin.induction with
    | zero => simp [F,ht0,hC]
    | succ k ih =>
      unfold F at *
      rw [Fin.val_succ, Finset.sum_range_succ, dif_pos k.isLt]
      change _ + (C (t k.succ) ω - C (t k.castSucc) ω) = _
      change (∑ j ∈ Finset.range k.castSucc.val, if hj : j < n then
        C (t (⟨j,hj⟩ : Fin n).succ) ω - C (t (⟨j,hj⟩ : Fin n).castSucc) ω else 0) +
        (C (t k.succ) ω - C (t k.castSucc) ω) = _
      rw [ih]
      ring
  have h := hi.comp hF hF
  have ha : F ∘ (fun ω (i : Fin n) => A (t i.succ) ω - A (t i.castSucc) ω) =
      (fun ω k => A (t k) ω) := by
    funext ω k
    exact telescope A hA0 ω k
  have hb : F ∘ (fun ω (i : Fin n) => B (t i.succ) ω - B (t i.castSucc) ω) =
      (fun ω k => B (t k) ω) := by
    funext ω k
    exact telescope B hB0 ω k
  rwa [ha,hb] at h
