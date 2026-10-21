-- Prove2me | solution 1 for ModernOnlineLearning.Aggregating.proposition_7_34
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:58:14.414354+00:00
-- url     : https://prove2.me/submissions/6cd6cc7e-ca06-424e-8929-f45858839aa9

import Mathlib
import Definitions.Def_ModernOnlineLearning_Aggregating_ExpConcave
set_option autoImplicit false
open ModernOnlineLearning.Aggregating

theorem solution {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))}
    {α : ℝ} {f : EuclideanSpace ℝ (Fin d) → WithTop ℝ}
    (hα : 0 < α) (hf : ExpConcaveOnExtended V α f) : ExtendedConvexOn V f := by
  have key : ∀ (z : EuclideanSpace ℝ (Fin d)) (r : ℝ), f z ≤ (r : WithTop ℝ) →
      Real.exp (-α * r) ≤ extendedExp α f z := by
    intro z r hz
    have hne : f z ≠ ⊤ := ne_top_of_le_ne_top (WithTop.coe_ne_top) hz
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hs] at hz
    have hsr : s ≤ r := WithTop.coe_le_coe.mp hz
    unfold extendedExp
    rw [if_neg hne, ← hs]
    simp only [WithTop.untopD_coe]
    exact Real.exp_le_exp.mpr (by nlinarith)
  intro p hp q hq a b ha hb hab
  obtain ⟨hpV, hpf⟩ := hp
  obtain ⟨hqV, hqf⟩ := hq
  have hV : a • p.1 + b • q.1 ∈ V := hf.1 hpV hqV ha hb hab
  refine ⟨hV, ?_⟩
  have hc := hf.2 hpV hqV ha hb hab
  have e1 := key _ _ hpf
  have e2 := key _ _ hqf
  have hconv : Real.exp (-α * (a * p.2 + b * q.2)) ≤
      a * Real.exp (-α * p.2) + b * Real.exp (-α * q.2) := by
    have := convexOn_exp.2 (Set.mem_univ (-α * p.2)) (Set.mem_univ (-α * q.2)) ha hb hab
    simpa [smul_eq_mul, mul_add, mul_left_comm] using this
  have hg : Real.exp (-α * (a * p.2 + b * q.2)) ≤ extendedExp α f (a • p.1 + b • q.1) := by
    refine hconv.trans (le_trans ?_ hc)
    simp only [smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]
  have hne : f (a • p.1 + b • q.1) ≠ ⊤ := by
    intro htop
    have : extendedExp α f (a • p.1 + b • q.1) = 0 := by
      unfold extendedExp; rw [if_pos htop]
    have := Real.exp_pos (-α * (a * p.2 + b * q.2))
    linarith
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hne
  have : extendedExp α f (a • p.1 + b • q.1) = Real.exp (-α * s) := by
    unfold extendedExp; rw [if_neg hne, ← hs]; simp
  rw [this, Real.exp_le_exp] at hg
  show f (a • p.1 + b • q.1) ≤ ((a • p + b • q).2 : ℝ)
  rw [← hs]
  simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
  exact WithTop.coe_le_coe.mpr (by nlinarith)
