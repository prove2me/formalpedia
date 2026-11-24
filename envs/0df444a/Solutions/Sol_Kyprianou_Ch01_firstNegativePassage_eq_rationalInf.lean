-- Prove2me | solution 1 for Kyprianou.Ch01.firstNegativePassage_eq_rationalInf
-- status  : ACCEPTED   (disprove)
-- author  : @pageman
-- created : 2026-11-24T20:25:30.538189+00:00
-- url     : https://prove2.me/submissions/cdfecd33-1f54-4a76-827a-592875ba8556

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Disproof: joint measurability does not identify the passage clock with a rational inf. -/
theorem solution
    (h : ∀ {Ω : Type} [MeasurableSpace Ω]
        (X : ℝ≥0 → Ω → ℤ)
        (_hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1))
        (ω : Ω),
        firstNegativePassage X ω =
          ⨅ q : {q : ℚ // 0 < q},
            if X (Real.toNNReal (q : ℝ)) ω < 0 then
              ((Real.toNNReal (q : ℝ) : ℝ≥0) : WithTop ℝ≥0)
            else ⊤) :
    False := by
  let t0 : ℝ≥0 := ⟨√(2 : ℝ), by positivity⟩
  let X0 : ℝ≥0 → Fin 1 → ℤ := fun t _ => if t = t0 then (-1 : ℤ) else 1
  let X : ℝ≥0 → ULift (Fin 1) → ℤ := fun t ω => X0 t ω.down
  have ht0pos : (0 : ℝ≥0) < t0 := by
    change (0 : ℝ) < √(2 : ℝ)
    exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have hX : Measurable (fun p : ULift (Fin 1) × ℝ≥0 => X p.2 p.1) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_singleton t0).preimage measurable_snd
  have hE : {t : ℝ≥0 | 0 < t ∧ X0 t 0 < 0} = {t0} := by
    ext t
    constructor
    · intro ⟨_, hXt⟩
      by_cases ht : t = t0
      · exact ht
      · simp [X0, ht] at hXt
    · rintro rfl
      exact ⟨ht0pos, by simp [X0]⟩
  have hhit : firstNegativePassage X (ULift.up (0 : Fin 1)) = (t0 : WithTop ℝ≥0) := by
    classical
    change (if ∃ t : ℝ≥0, 0 < t ∧ X t (ULift.up (0 : Fin 1)) < 0 then
        ((sInf ({t : ℝ≥0 | 0 < t ∧ X t (ULift.up (0 : Fin 1)) < 0} : Set ℝ≥0) : ℝ≥0) :
          WithTop ℝ≥0)
      else ⊤) = (t0 : WithTop ℝ≥0)
    have hex : ∃ t : ℝ≥0, 0 < t ∧ X t (ULift.up (0 : Fin 1)) < 0 :=
      ⟨t0, ht0pos, by simp [X, X0]⟩
    have hE' :
        {t : ℝ≥0 | 0 < t ∧ X t (ULift.up (0 : Fin 1)) < 0} = {t0} := by
      simpa [X, X0] using hE
    rw [if_pos hex, hE', csInf_singleton]
  have hrat :
      (⨅ q : {q : ℚ // 0 < q},
          if X (Real.toNNReal (q : ℝ)) (ULift.up (0 : Fin 1)) < 0 then
            ((Real.toNNReal (q : ℝ) : ℝ≥0) : WithTop ℝ≥0)
          else ⊤) = (⊤ : WithTop ℝ≥0) := by
    refine iInf_eq_top.mpr ?_
    intro q
    have hr : (0 : ℝ) < (q.1 : ℝ) := by exact_mod_cast q.property
    have hne : Real.toNNReal (q.1 : ℝ) ≠ t0 := by
      intro heq
      have hcoe : ((t0 : ℝ≥0) : ℝ) = √(2 : ℝ) := rfl
      have hEqR : ((Real.toNNReal (q.1 : ℝ) : ℝ≥0) : ℝ) = √(2 : ℝ) :=
        (congrArg (fun z : ℝ≥0 => (z : ℝ)) heq).trans hcoe
      have : (q.1 : ℝ) = √(2 : ℝ) :=
        (Real.coe_toNNReal (q.1 : ℝ) hr.le).symm.trans hEqR
      exact (irrational_sqrt_two).ne_rat q.1 this.symm
    have : X (Real.toNNReal (q.1 : ℝ)) (ULift.up (0 : Fin 1)) ≠ -1 := by
      simp [X, X0, hne]
    simp [X, X0, hne]
  have hEq := h (Ω := ULift.{0} (Fin 1)) X hX (ULift.up (0 : Fin 1))
  rw [hhit, hrat] at hEq
  exact (WithTop.coe_ne_top (a := t0)) hEq
