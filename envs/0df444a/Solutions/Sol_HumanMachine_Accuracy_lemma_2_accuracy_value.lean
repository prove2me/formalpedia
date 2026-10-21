-- Prove2me | solution 1 for HumanMachine.Accuracy.lemma_2_accuracy_value
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:40:14.327348+00:00
-- url     : https://prove2.me/submissions/bd910c1a-93fd-4aac-bab0-9b4c844d5a4a

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel
import Definitions.Def_HumanMachine_Accuracy_Machine

set_option autoImplicit false
open HumanMachine.Accuracy

lemma hma_value_zero (lam pg pb : ℝ) :
    HumanMachine.Alone.value lam 0 pg pb = 1 - pb := by
  simp [HumanMachine.Alone.value, HumanMachine.Alone.accuracy, HumanMachine.Alone.cost,
    HumanMachine.Alone.choiceProb]

lemma hma_optPair_zero (lam : ℝ) : (optPair lam 0).2 = 0 := by
  have hex : ∃ q : ℝ × ℝ, HumanMachine.Alone.IsOptimal lam 0 q.1 q.2 := by
    refine ⟨(0, 0), ?_⟩
    refine ⟨by simp, by simp, ?_⟩
    intro qg hqg qb hqb
    rw [hma_value_zero, hma_value_zero]
    linarith [hqb.1]
  have h : HumanMachine.Alone.IsOptimal lam 0 (optPair lam 0).1 (optPair lam 0).2 :=
    Classical.epsilon_spec hex
  obtain ⟨_, hb, hopt⟩ := h
  have := hopt 0 (by simp) 0 (by simp)
  rw [hma_value_zero, hma_value_zero] at this
  linarith [hb.1]

lemma hma_AStar_zero (lam : ℝ) : AStar lam 0 = 1 := by
  have h := hma_optPair_zero lam
  simp [AStar, HumanMachine.Alone.accuracy, h]

lemma hma_VStar_zero (lam : ℝ) : VStar lam 0 = 1 := by
  have h := hma_optPair_zero lam
  unfold VStar; rw [hma_value_zero, h]; norm_num

theorem solution (lam : ℝ) (hlam : 0 < lam) (π : Bool → Bool → ℝ)
    (hπ : IsPrior π) :
    AStarM lam π = 1 - priorGood π / posterior π true
        + (priorGood π / posterior π true) * AStar lam (posterior π true) ∧
      VStarM lam π = 1 - priorGood π / posterior π true
        + (priorGood π / posterior π true) * VStar lam (posterior π true) := by
  obtain ⟨hpos, hsum⟩ := hπ
  have h1 : posterior π false = 0 := by
    simp [posterior, jointGood, isGood, Fintype.sum_bool]
  have hP : priorGood π = π true true := by
    simp [priorGood, isGood, Fintype.sum_bool]
  have hpt : probOut π true = π true true + π true false := by
    simp [probOut, Fintype.sum_bool]
  have hpf : probOut π false = π false true + π false false := by
    simp [probOut, Fintype.sum_bool]
  have h2 : posterior π true = π true true / (π true true + π true false) := by
    simp [posterior, jointGood, probOut, isGood, Fintype.sum_bool]
  have ha := hpos true true
  have hb := hpos true false
  have hne : π true true + π true false ≠ 0 := by positivity
  have hr : priorGood π / posterior π true = probOut π true := by
    rw [hP, h2, hpt]; field_simp
  have hrf : probOut π false = 1 - probOut π true := by
    rw [hpf, hpt]; linarith
  rw [hr]
  constructor
  · unfold AStarM; rw [h1, hma_AStar_zero, hrf]; ring
  · unfold VStarM; rw [h1, hma_VStar_zero, hrf]; ring
