-- Prove2me | solution 1 for ImpulseGames.LinearGame.prop_4_7_nash_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T16:55:59.008043+00:00
-- url     : https://prove2.me/submissions/806d4476-c762-434c-a49e-08ae73fac17a

import Mathlib
import Definitions.Def_ImpulseGames_LinearGame_Equilibrium
import Theorems.Thm_ImpulseGames_LinearGame_prop_4_2_explicit_solution
import Theorems.Thm_ImpulseGames_LinearGame_lemma_4_6
import Theorems.Thm_ImpulseGames_LinearGame_condition_v_admissible
import Theorems.Thm_ImpulseGames_LinearGame_prop_4_7_player_one_optimal
import Theorems.Thm_ImpulseGames_LinearGame_prop_4_7_player_two_optimal

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

open ImpulseGames.LinearGame in
theorem solution (M : Model) (hM : M.Standing) (hc : 0 < M.c)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (ξ : ℝ) (hξ : ξ ∈ Set.Ioo 0 (eta M)) (hFξ : F M ξ = 0) (s : ℝ) (x : ℝ) :
    InPhi M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) ∧
    IsNash M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) ∧
    J M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) .one = Vt1 M ξ s x ∧
    J M P W x (eqStrat1 M ξ s) (eqStrat2 M ξ s) .two = Vt2 M ξ s x := by
  obtain ⟨h47a, h47b, ⟨h48a, -⟩, h48b, h48c, h48d, ⟨h49a, -⟩, h49b, h49c, h49d, -⟩ :=
    prop_4_2_explicit_solution M hM hc ξ hξ hFξ s
  obtain ⟨h1, h2, h3, -, -, h6, -, -⟩ := lemma_4_6 M hM hc ξ hξ hFξ s
  have hq1 : ∀ y δ : ℝ, 0 ≤ δ → Vt1 M ξ s (y + δ) - M.c - M.lam * |δ| ≤ Vt1 M ξ s y := by
    intro y δ hδ
    have hb : BddAbove ((fun δ => Vt1 M ξ s (y + δ) - M.c - M.lam * |δ|) '' Set.Ici 0) := by
      refine ⟨Vt1 M ξ s (y + delta1 M ξ s y) - M.c - M.lam * |delta1 M ξ s y|, ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      exact ((h1 y).2 d hd).1
    have hle := le_csSup hb (Set.mem_image_of_mem
      (fun δ => Vt1 M ξ s (y + δ) - M.c - M.lam * |δ|) (show δ ∈ Set.Ici (0 : ℝ) from hδ))
    have h3y := h3 y
    unfold M1op at h3y
    linarith
  have hq2 : ∀ y δ : ℝ, δ ≤ 0 → Vt2 M ξ s (y + δ) - M.c - M.lam * |δ| ≤ Vt2 M ξ s y := by
    intro y δ hδ
    have hb : BddAbove ((fun δ => Vt2 M ξ s (y + δ) - M.c - M.lam * |δ|) '' Set.Iic 0) := by
      refine ⟨Vt2 M ξ s (y + delta2 M ξ s y) - M.c - M.lam * |delta2 M ξ s y|, ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      exact ((h2 y).2 d hd).1
    have hle := le_csSup hb (Set.mem_image_of_mem
      (fun δ => Vt2 M ξ s (y + δ) - M.c - M.lam * |δ|) (show δ ∈ Set.Iic (0 : ℝ) from hδ))
    have h6y := h6 y
    unfold M2op at h6y
    linarith
  have hΦ := condition_v_admissible M hM hc P W hW ξ hξ hFξ s x
  obtain ⟨d1, e1⟩ :=
    prop_4_7_player_one_optimal M hM ξ s h47a h47b h48a h48b h48c h48d hq1 P W hW x
  obtain ⟨d2, e2⟩ :=
    prop_4_7_player_two_optimal M hM ξ s h47a h47b h49a h49b h49c h49d hq2 P W hW x
  have j1 := e1 hΦ
  have j2 := e2 hΦ
  refine ⟨hΦ, ⟨hΦ, fun ψ₁ h => ?_, fun ψ₂ h => ?_⟩, j1, j2⟩
  · rw [j1]; exact d1 ψ₁ h
  · rw [j2]; exact d2 ψ₂ h
