-- Prove2me | solution 1 for ModernConvex.EllipsoidMethod.guess_le_variation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:42:43.422592+00:00
-- url     : https://prove2.me/submissions/b8ced34c-b06c-45f7-a4f3-8f4a22003737

import Mathlib
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod

open Matrix MeasureTheory
open ModernConvex.EllipsoidMethod
theorem g69a2_ell_le {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin) (c : Fin n → ℝ) (hc : c ∈ X)
    (ha : (O c).2 ≠ 0) :
    R * eucNorm (O c).2 - (O c).2 ⬝ᵥ c ≤ Vmax - Vmin := by
  obtain ⟨-, -, -, -, -, -, hR, hXR, -⟩ := hP
  set a := (O c).2
  have haa : 0 < a ⬝ᵥ a := by
    rcases (dotProduct_self_eq_zero (v := a)).not.mpr ha |> lt_or_gt_of_ne with h | h
    · exact absurd h (not_lt.mpr (dotProduct_self_star_nonneg a))
    · exact h
  have hN : 0 < eucNorm a := Real.sqrt_pos.mpr haa
  have hNsq : eucNorm a ^ 2 = a ⬝ᵥ a := Real.sq_sqrt haa.le
  set y := (R / eucNorm a) • a
  have hy : eucNorm y ≤ R := by
    unfold eucNorm
    rw [show y ⬝ᵥ y = R ^ 2 by
      simp only [y, smul_dotProduct, dotProduct_smul, smul_eq_mul, ← hNsq]
      field_simp]
    rw [Real.sqrt_sq hR.le]
  have hsub := (hO c).2 y
  have h1 : f y ≤ Vmax := hVmax.2 ⟨y, hy, rfl⟩
  have h2 : Vmin ≤ f c := hVmin.2 ⟨c, hXR hc, rfl⟩
  have hay : a ⬝ᵥ y = R * eucNorm a := by
    simp only [y, dotProduct_smul, smul_eq_mul, ← hNsq]
    field_simp
  rw [dotProduct_sub, hay] at hsub
  linarith

theorem g69a2_step_L {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin) (s s' : State n)
    (hs : s.L ≤ Vmax - Vmin) (hstep : step sep O R s = StepResult.next s') :
    s'.L ≤ Vmax - Vmin := by
  unfold step at hstep
  rcases hc : sep s.c with _ | a
  · rw [hc] at hstep
    simp only at hstep
    by_cases h0 : (O s.c).2 = 0
    · rw [if_pos h0] at hstep; cases hstep
    · rw [if_neg h0] at hstep
      cases hstep
      simp only
      refine max_le hs ?_
      exact g69a2_ell_le f X r R hP O hO Vmax Vmin hVmax hVmin s.c ((hsep s.c).1.mp hc) h0
  · rw [hc] at hstep
    simp only at hstep
    cases hstep
    exact hs

theorem g69a2_run_L {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O) (ε : ℝ)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin) :
    ∀ (t : ℕ) (s : State n), run sep O R r ε t = Outcome.running s → s.L ≤ Vmax - Vmin := by
  intro t
  induction t with
  | zero =>
    intro s hs
    simp only [run] at hs
    cases hs
    simp only [initState]
    obtain ⟨x, hx, hxv⟩ := hVmin.1
    have := hVmax.2 ⟨x, hx, rfl⟩
    linarith
  | succ t ih =>
    intro s hs
    simp only [run] at hs
    rcases h : run sep O R r ε t with s0 | x
    · rw [h] at hs
      simp only at hs
      rcases hst : step sep O R s0 with x | s'
      · rw [hst] at hs; simp only at hs; cases hs
      · rw [hst] at hs
        simp only at hs
        split_ifs at hs
        cases hs
        exact g69a2_step_L f X r R hP sep hsep O hO Vmax Vmin hVmax hVmin s0 _ (ih s0 h) hst
    · rw [h] at hs; simp only at hs; cases hs


/-- Ben-Tal–Nemirovski, p. 352, Eq. (5.2.28), in the proof of Theorem 5.2.1. In the setting of
Theorem 5.2.1, let `Var_R(f) = max_{E₀} f − min_{E₀} f` over the ball `E₀ = {‖x‖₂ ≤ R}`
(the maximum `Vmax` and minimum `Vmin` of `f` on `E₀`). Every guess `L_{t+1}` computed at a
step `t + 1` of the method (the method still running after `t` steps, step `t + 1` not stopping
by rule 2) satisfies `L_{t+1} ≤ Var_R(f)` (and `L₀ = 0`). -/
theorem solution {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (Vmax Vmin : ℝ) (hVmax : IsGreatest (f '' {x | eucNorm x ≤ R}) Vmax)
    (hVmin : IsLeast (f '' {x | eucNorm x ≤ R}) Vmin)
    (t : ℕ) (s s' : State n) (hrun : run sep O R r ε t = Outcome.running s)
    (hstep : step sep O R s = StepResult.next s') :
    s'.L ≤ Vmax - Vmin := g69a2_step_L f X r R hP sep hsep O hO Vmax Vmin hVmax hVmin s s'
    (g69a2_run_L f X r R hP sep hsep O hO ε Vmax Vmin hVmax hVmin t s hrun) hstep

