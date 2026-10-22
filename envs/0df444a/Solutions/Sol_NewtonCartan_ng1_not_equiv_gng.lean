-- Prove2me | solution 1 for NewtonCartan.ng1_not_equiv_gng
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:49:41.040391+00:00
-- url     : https://prove2.me/submissions/6018b7ad-ef4e-4e25-8078-55ed2ff0ae29

import Definitions.Def_NewtonCartan_defs
import Mathlib
open scoped ContDiff
open NewtonCartan
theorem g69h2_polar (Q : Fin 4 → Fin 4 → ℝ) (hs : ∀ b c, Q b c = Q c b)
    (h : ∀ ξ : Fin 4 → ℝ, ξ 0 = 1 → ∑ b, ∑ c, Q b c * ξ b * ξ c = 0) : ∀ b c, Q b c = 0 := by
  have H : ∀ v1 v2 v3 : ℝ, ∑ b, ∑ c, Q b c * (![1, v1, v2, v3] : Fin 4 → ℝ) b *
      (![1, v1, v2, v3] : Fin 4 → ℝ) c = 0 := fun v1 v2 v3 => h _ rfl
  have e0 := H 0 0 0
  have e1 := H 1 0 0
  have e2 := H (-1) 0 0
  have e3 := H 0 1 0
  have e4 := H 0 (-1) 0
  have e5 := H 0 0 1
  have e6 := H 0 0 (-1)
  have e7 := H 1 1 0
  have e8 := H 1 0 1
  have e9 := H 0 1 1
  simp [Fin.sum_univ_four] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9
  have s01 := hs 0 1
  have s02 := hs 0 2
  have s03 := hs 0 3
  have s12 := hs 1 2
  have s13 := hs 1 3
  have s23 := hs 2 3
  intro b c
  fin_cases b <;> fin_cases c <;> simp <;> linarith

theorem g69h2_pd_const (c : ℝ) (b : Fin 4) (x : E) : pd (fun _ => c) b x = 0 := by
  simp [pd]

theorem g69h2_pd_coord (a b : Fin 4) (x : E) : pd (fun y => y a) b x = (Pi.single b (1:ℝ) : E) a := by
  unfold pd
  have : (fun y : E => y a) = (ContinuousLinearMap.proj a : E →L[ℝ] ℝ) := rfl
  rw [this, ContinuousLinearMap.fderiv]
  rfl

theorem g69h2_straight_zero (Γ : Conn) (φ : E → ℝ) (hsym : ∀ x a b c, Γ x a b c = Γ x a c b)
    (hφ : ∀ x a, gradUp φ x a = 0) (hT : SameTrajectories (fun _ _ _ _ => 0) φ Γ) :
    Γ = fun _ _ _ _ => 0 := by
  funext x a
  apply funext₂
  apply g69h2_polar (Γ x a) (hsym x a)
  intro ξ hξ
  let γ : ℝ → E := fun s => x + s • ξ
  have hd : ∀ s, HasDerivAt γ ξ s := by
    intro s
    have := ((hasDerivAt_id s).smul_const ξ).const_add x
    simpa [γ] using this
  have hdγ : deriv γ = fun _ => ξ := funext fun s => (hd s).deriv
  have htl : IsTimelikeOn γ (-1) 1 := by
    refine ⟨by norm_num, ?_, ?_⟩
    · exact (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
    · intro s _; rw [hdγ]; exact hξ
  have hN : IsNewtonianOn (fun _ _ _ _ => 0) φ γ (-1) 1 := by
    intro s _ a
    simp [accel, hdγ, hφ]
  have hG := ((hT γ (-1) 1 htl).2 hN) 0 (by norm_num) a
  simp only [accel, hdγ] at hG
  simpa [γ] using hG

theorem g69h2_isNG_zero (c : ℝ) : IsNG (fun _ _ _ _ => 0) (fun _ => c) := by
  refine ⟨⟨⟨contDiff_const, fun _ _ _ _ => rfl⟩, ?_, ?_⟩, ?_, contDiff_const⟩
  · intro x b c; simp
  · intro x a b c; simp
  · intro x a b c d; simp [riem, g69h2_pd_const]

theorem g69h2_gradUp_const (c : ℝ) (x : E) (a : Fin 4) : gradUp (fun _ => c) x a = 0 := by
  simp [gradUp, g69h2_pd_const]

theorem g69h2_id_arrow : IsGNGArrow (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (Equiv.refl E) := by
  refine ⟨⟨contDiff_id, contDiff_id⟩, ⟨?_, ?_⟩, ?_⟩
  · intro x b
    simp only [Equiv.refl_apply, g69h2_pd_coord]
    simp [tt, Pi.single_apply]
  · intro x a b
    simp only [Equiv.refl_apply, g69h2_pd_coord]
    simp [hh, Fin.sum_univ_four, Pi.single_apply]
    fin_cases a <;> fin_cases b <;> simp
  · intro x a b c
    simp only [Equiv.refl_apply, pd2, g69h2_pd_coord, g69h2_pd_const]
    simp

theorem solution :
    ¬ ∃ F : {p : Conn × (E → ℝ) // IsNG p.1 p.2} → {Γ : Conn // IsGNG Γ},
      (∀ A, SameTrajectories A.1.1 A.1.2 (F A).1) ∧
      ∀ A B, Nonempty ({f : E ≃ E // IsNG1Arrow A.1.1 A.1.2 B.1.1 B.1.2 f} ≃
        {f : E ≃ E // IsGNGArrow (F A).1 (F B).1 f}) := by
  rintro ⟨F, hT, hB⟩
  let A : {p : Conn × (E → ℝ) // IsNG p.1 p.2} := ⟨((fun _ _ _ _ => 0), fun _ => 0), g69h2_isNG_zero 0⟩
  let B : {p : Conn × (E → ℝ) // IsNG p.1 p.2} := ⟨((fun _ _ _ _ => 0), fun _ => 1), g69h2_isNG_zero 1⟩
  have hA : (F A).1 = fun _ _ _ _ => 0 :=
    g69h2_straight_zero _ (fun _ => 0) (F A).2.1.1.2 (g69h2_gradUp_const 0) (hT A)
  have hB' : (F B).1 = fun _ _ _ _ => 0 :=
    g69h2_straight_zero _ (fun _ => 1) (F B).2.1.1.2 (g69h2_gradUp_const 1) (hT B)
  obtain ⟨e⟩ := hB A B
  have hid : IsGNGArrow (F A).1 (F B).1 (Equiv.refl E) := by
    rw [hA, hB']; exact g69h2_id_arrow
  obtain ⟨f, hf⟩ := e.symm ⟨Equiv.refl E, hid⟩
  have := hf.2 0
  simp [A, B] at this
