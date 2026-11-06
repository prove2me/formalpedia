-- Prove2me | solution 1 for MinimaxSLP.RhsExtremal.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T21:43:20.680815+00:00
-- url     : https://prove2.me/submissions/8a45e75c-7f5c-41d9-aaa8-67c3d8ab22ef

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_RhsExtremal_Model
import Theorems.Thm_MinimaxSLP_RhsExtremal_disutility_Qval_eq_max_pairs
import Theorems.Thm_MinimaxSLP_RhsExtremal_Zhat_le_ZhatDD
import Theorems.Thm_MinimaxSLP_RhsExtremal_dual16_optimal_zero_or_positive
import Theorems.Thm_MinimaxSLP_RhsExtremal_mixture_mem_momentClass
import Theorems.Thm_MinimaxSLP_RhsExtremal_mixture_lower_bound

open MeasureTheory Matrix MinimaxSLP.RhsExtremal

theorem solution {m₁ n r d K N : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (ps : Fin N → Fin r → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) :
    ∃ P ∈ MinimaxSLP.ObjSDP.momentClass μ Q,
      (∀ P' ∈ MinimaxSLP.ObjSDP.momentClass μ Q,
        Integrable (fun h => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) P' ∧
        ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P' ≤ ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P) ∧
      IsGreatest (obj16 T α β ps x '' feasible16 K N μ Q)
        (∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P) ∧
      MinimaxSLP.RhsSDP.Zhat W T q α β μ Q x = ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P ∧
      ZhatDD T α β ps μ Q x = ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P := by
  have hN : 0 < N := by
    obtain ⟨⟨i, -⟩, -⟩ := (disutility_Qval_eq_max_pairs W T q α β ps hα hA2 hA3 hA5 x 0).1
    exact Nat.pos_of_ne_zero (fun h => by subst h; exact i.elim0)
  obtain ⟨s, hs, hgr, hpos⟩ := dual16_optimal_zero_or_positive T α β ps μ Q hN hQ hA4 x
  have hmem := mixture_mem_momentClass μ Q s hs hpos
  obtain ⟨-, hlow⟩ := mixture_lower_bound W T q α β ps μ Q hα hA2 hA3 hA5 x s hs hpos
  obtain ⟨hall, -, -⟩ := Zhat_le_ZhatDD W T q α β ps μ Q hα hA2 hA3 hA5 x
  have hle : ∀ P ∈ MinimaxSLP.ObjSDP.momentClass μ Q, ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P ≤ obj16 T α β ps x s := by
    intro P hP
    obtain ⟨-, s', hs', he⟩ := hall P hP
    rw [← he]; exact hgr.2 ⟨s', hs', rfl⟩
  have heq : ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂(mixture s) = obj16 T α β ps x s := le_antisymm (hle _ hmem) hlow
  refine ⟨mixture s, hmem, fun P' hP' => ⟨(hall P' hP').1, ?_⟩, ?_, ?_, ?_⟩
  · rw [heq]; exact hle P' hP'
  · rw [heq]; exact hgr
  · have : IsGreatest (MinimaxSLP.RhsSDP.primalValues W T q α β μ Q x) (∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂(mixture s)) := by
      refine ⟨⟨_, hmem, rfl⟩, ?_⟩
      rintro _ ⟨P, hP, rfl⟩
      rw [heq]; exact hle P hP
    exact this.csSup_eq
  · rw [heq]; exact hgr.csSup_eq
