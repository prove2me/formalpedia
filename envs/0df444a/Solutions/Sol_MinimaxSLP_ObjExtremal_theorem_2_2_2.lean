-- Prove2me | solution 2 for MinimaxSLP.ObjExtremal.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T23:05:52.282205+00:00
-- url     : https://prove2.me/submissions/5d03ac2c-a010-4b6f-8a0d-abc1a264c1b7

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model
import Theorems.Thm_MinimaxSLP_ObjExtremal_strong_duality
import Theorems.Thm_MinimaxSLP_ObjExtremal_dual6_le_dual9_upper
import Theorems.Thm_MinimaxSLP_ObjExtremal_feasible9_approx

open MeasureTheory Matrix Filter Topology
open MinimaxSLP.ObjExtremal

theorem solution {m₁ n r d K : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hx : x ∈ MinimaxSLP.ObjSDP.X A b) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty) :
    (∃ P : ℕ → Measure (Fin d → ℝ), (∀ j, P j ∈ MinimaxSLP.ObjSDP.momentClass μ Q) ∧
      Tendsto (fun j => ∫ q, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.ObjSDP.Qval W T h q x) ∂(P j)) atTop
        (𝓝 (MinimaxSLP.ObjSDP.Zx W T h α β μ Q x))) ∧
    IsLUB (MinimaxSLP.ObjSDP.primalValues W T h α β μ Q x) (MinimaxSLP.ObjSDP.Zx W T h α β μ Q x) ∧
    IsGLB (MinimaxSLP.ObjSDP.dualValues6 W T h α β μ Q x) (MinimaxSLP.ObjSDP.ZD W T h α β μ Q x) ∧
    IsLUB (dualValues9 W T h α β μ Q x) (ZDD W T h α β μ Q x) ∧
    MinimaxSLP.ObjSDP.Zx W T h α β μ Q x = MinimaxSLP.ObjSDP.ZD W T h α β μ Q x ∧
    MinimaxSLP.ObjSDP.ZD W T h α β μ Q x = ZDD W T h α β μ Q x := by
  obtain ⟨hlub, hglb, hZD⟩ := strong_duality A b W T h α β hα μ Q hQ hA4 hA3 x hx hrec
  have hne : (MinimaxSLP.ObjSDP.primalValues W T h α β μ Q x).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hlub
    have := hlub.2 (show MinimaxSLP.ObjSDP.Zx W T h α β μ Q x - 1 ∈ upperBounds (∅ : Set ℝ) by
      simp)
    linarith
  -- (1) a maximizing sequence of distributions
  obtain ⟨u, -, -, hu_tend, hu_mem⟩ := hlub.exists_seq_monotone_tendsto hne
  choose P hP hPu using hu_mem
  -- (9) has least upper bound `Z(x)`
  have hub9 : MinimaxSLP.ObjSDP.Zx W T h α β μ Q x ∈ upperBounds (dualValues9 W T h α β μ Q x) := by
    rintro _ ⟨s, hs, rfl⟩
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨P', hP', -, hb⟩ := feasible9_approx W T h α β hα μ Q hA3 x hrec s hs δ hδ
    have := hlub.1 ⟨P', hP', rfl⟩
    linarith
  have hlub9 : IsLUB (dualValues9 W T h α β μ Q x) (MinimaxSLP.ObjSDP.Zx W T h α β μ Q x) := by
    refine ⟨hub9, fun v hv => ?_⟩
    rw [hZD]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨s, hs, hval⟩ := dual6_le_dual9_upper W T h α β hα μ Q hQ hA4 hA3 x hrec v hv ε hε
    exact (hglb.1 ⟨s, hs, rfl⟩).trans hval
  have hne9 : (dualValues9 W T h α β μ Q x).Nonempty := by
    by_contra hne9
    rw [Set.not_nonempty_iff_eq_empty] at hne9
    rw [hne9] at hlub9
    have := hlub9.2 (show MinimaxSLP.ObjSDP.Zx W T h α β μ Q x - 1 ∈ upperBounds (∅ : Set ℝ) by
      simp)
    linarith
  have hZDD : ZDD W T h α β μ Q x = MinimaxSLP.ObjSDP.Zx W T h α β μ Q x := hlub9.csSup_eq hne9
  refine ⟨⟨P, hP, hu_tend.congr fun j => (hPu j).symm⟩, hlub, hglb, hZDD ▸ hlub9, hZD, ?_⟩
  rw [hZDD, hZD]
