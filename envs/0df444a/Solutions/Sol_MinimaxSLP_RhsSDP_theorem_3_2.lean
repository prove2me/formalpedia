-- Prove2me | solution 1 for MinimaxSLP.RhsSDP.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:57:17.175192+00:00
-- url     : https://prove2.me/submissions/2d285777-271d-4b4f-9d39-7fb4aaa1954a

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model
import Theorems.Thm_MinimaxSLP_RhsSDP_strong_duality
import Theorems.Thm_MinimaxSLP_RhsSDP_dualFeasible12_eq_feasible15
import Theorems.Thm_MinimaxSLP_RhsSDP_Qval_eq_max_extreme_points

open MeasureTheory Matrix

lemma isGLB_nonempty_aux {s : Set ℝ} {a : ℝ} (h : IsGLB s a) : s.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  have := h.2 (show a + 1 ∈ lowerBounds (∅ : Set ℝ) by simp)
  linarith

open MinimaxSLP.RhsSDP in
theorem solution {m₁ n r d K N : ℕ} [NeZero K]
    (A : Matrix (Fin m₁) (Fin n) ℝ) (b : Fin m₁ → ℝ) (c : Fin n → ℝ)
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (ps : Fin N → Fin r → ℝ)
    (hA1 : (MinimaxSLP.ObjSDP.X A b).Nonempty ∧ Bornology.IsBounded (MinimaxSLP.ObjSDP.X A b))
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q}) :
    (∀ x ∈ MinimaxSLP.ObjSDP.X A b, Zhat W T q α β μ Q x = ZhatD15 T α β ps μ Q x) ∧
      IsGLB (minimaxObj c W T q α β μ Q '' MinimaxSLP.ObjSDP.X A b) (ZhatSDP A b c T α β ps μ Q) ∧
      IsGLB (obj14 c μ Q '' feasible14 A b T α β ps) (ZhatSDP A b c T α β ps μ Q) ∧
      Zval A b c W T q α β μ Q = ZhatSDP A b c T α β ps μ Q := by
  have hSD := fun x => strong_duality W T q α β μ Q hα hA2 hA3 hQ hA4 x
  have hF := fun x => dualFeasible12_eq_feasible15 W T q α β μ Q ps hα hA2 hA3 hA5 x
  set SX := minimaxObj c W T q α β μ Q '' MinimaxSLP.ObjSDP.X A b with hSX
  set S14 := obj14 c μ Q '' feasible14 A b T α β ps with hS14
  -- lower bounds coincide
  have hlb : lowerBounds SX = lowerBounds S14 := by
    ext L
    constructor
    · rintro hL w ⟨z, hz, rfl⟩
      have hx : z.1 ∈ MinimaxSLP.ObjSDP.X A b := ⟨hz.1, hz.2.1⟩
      have hz2 : z.2 ∈ dualFeasible12 W T q α β z.1 := by
        rw [(hF z.1).1]; exact ⟨hz.2.2.1, hz.2.2.2⟩
      have h1 : Zhat W T q α β μ Q z.1 ≤ dualObj μ Q z.2 := (hSD z.1).2.1.1 ⟨z.2, hz2, rfl⟩
      have h2 : L ≤ minimaxObj c W T q α β μ Q z.1 := hL ⟨z.1, hx, rfl⟩
      unfold minimaxObj at h2
      unfold obj14
      linarith
    · rintro hL w ⟨x, hx, rfl⟩
      have hlow : L - c ⬝ᵥ x ∈ lowerBounds (dualObj μ Q '' dualFeasible12 W T q α β x) := by
        rintro v ⟨s, hs, rfl⟩
        rw [(hF x).1] at hs
        have hmem : ((x, s) : (Fin n → ℝ) × Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) ∈
            feasible14 A b T α β ps := ⟨hx.1, hx.2, hs.1, hs.2⟩
        have := hL ⟨_, hmem, rfl⟩
        unfold obj14 at this
        simp only at this
        linarith
      have := (hSD x).2.1.2 hlow
      unfold minimaxObj
      linarith
  -- a distribution in the moment class and a dual extreme point
  obtain ⟨x0, hx0⟩ := hA1.1
  obtain ⟨v0, P, hP, -⟩ := (hSD x0).1.nonempty
  obtain ⟨⟨i0, -⟩, -⟩ := Qval_eq_max_extreme_points W T q ps hA2 hA3 hA5 x0 0
  set p := ps i0 with hp
  have k0 : Fin K := 0
  have : IsProbabilityMeasure P := hP.1.1
  have hint_lin : Integrable (fun h : Fin r → ℝ => h ⬝ᵥ p) P := by
    unfold dotProduct
    refine integrable_finsetSum _ (fun j _ => ?_)
    exact ((hP.1.2 j).integrable one_le_two).mul_const _
  set C := ∫ h, h ⬝ᵥ p ∂P with hC
  -- pointwise lower bound for each x
  have hlowx : ∀ x ∈ MinimaxSLP.ObjSDP.X A b,
      c ⬝ᵥ x + min 0 (α k0 * (C - (T *ᵥ x) ⬝ᵥ p) + β k0) ≤ minimaxObj c W T q α β μ Q x := by
    intro x hx
    have hpt : ∀ h : Fin r → ℝ, α k0 * (h ⬝ᵥ p - (T *ᵥ x) ⬝ᵥ p) + β k0 ≤
        MinimaxSLP.ObjSDP.disutility α β (Qval W T q h x) := by
      intro h
      obtain ⟨-, hub⟩ := Qval_eq_max_extreme_points W T q ps hA2 hA3 hA5 x h
      have h1 : (h - T *ᵥ x) ⬝ᵥ p ≤ Qval W T q h x := hub ⟨i0, rfl⟩
      rw [sub_dotProduct] at h1
      have h2 : α k0 * Qval W T q h x + β k0 ≤ MinimaxSLP.ObjSDP.disutility α β (Qval W T q h x) := by
        unfold MinimaxSLP.ObjSDP.disutility
        exact Finset.le_sup' (fun k => α k * Qval W T q h x + β k) (Finset.mem_univ k0)
      nlinarith [hα k0]
    have hI : min 0 (α k0 * (C - (T *ᵥ x) ⬝ᵥ p) + β k0) ≤
        ∫ h, MinimaxSLP.ObjSDP.disutility α β (Qval W T q h x) ∂P := by
      by_cases hg : Integrable (fun h => MinimaxSLP.ObjSDP.disutility α β (Qval W T q h x)) P
      · have e1 : Integrable (fun h : Fin r → ℝ => h ⬝ᵥ p - (T *ᵥ x) ⬝ᵥ p) P :=
          hint_lin.sub (integrable_const _)
        have e2 : Integrable (fun h : Fin r → ℝ => α k0 * (h ⬝ᵥ p - (T *ᵥ x) ⬝ᵥ p)) P :=
          e1.const_mul _
        have hlin : Integrable (fun h : Fin r → ℝ => α k0 * (h ⬝ᵥ p - (T *ᵥ x) ⬝ᵥ p) + β k0) P :=
          e2.add (integrable_const _)
        have hval : ∫ h, α k0 * (h ⬝ᵥ p - (T *ᵥ x) ⬝ᵥ p) + β k0 ∂P =
            α k0 * (C - (T *ᵥ x) ⬝ᵥ p) + β k0 := by
          rw [integral_add e2 (integrable_const _), integral_const_mul,
            integral_sub hint_lin (integrable_const _)]
          simp [hC]
        have := integral_mono hlin hg hpt
        rw [hval] at this
        exact le_trans (min_le_right _ _) this
      · rw [integral_undef hg]; exact min_le_left _ _
    have hZ : ∫ h, MinimaxSLP.ObjSDP.disutility α β (Qval W T q h x) ∂P ≤ Zhat W T q α β μ Q x :=
      (hSD x).1.1 ⟨P, hP, rfl⟩
    unfold minimaxObj
    linarith
  -- bounded below on the bounded set X
  have hbddX : BddBelow SX := by
    have hcont : Continuous (fun x : Fin n → ℝ =>
        c ⬝ᵥ x + min 0 (α k0 * (C - (T *ᵥ x) ⬝ᵥ p) + β k0)) := by
      have h1 : Continuous (fun x : Fin n → ℝ => c ⬝ᵥ x) :=
        continuous_const.dotProduct continuous_id
      have h2 : Continuous (fun x : Fin n → ℝ => (T *ᵥ x) ⬝ᵥ p) :=
        (continuous_const.matrix_mulVec continuous_id).dotProduct continuous_const
      exact h1.add (continuous_const.min ((continuous_const.mul (continuous_const.sub h2)).add
        continuous_const))
    obtain ⟨L, hL⟩ := (hA1.2.isCompact_closure.bddBelow_image hcont.continuousOn)
    refine ⟨L, ?_⟩
    rintro w ⟨x, hx, rfl⟩
    exact le_trans (hL ⟨x, subset_closure hx, rfl⟩) (hlowx x hx)
  have hneX : SX.Nonempty := ⟨_, x0, hx0, rfl⟩
  have hne14 : S14.Nonempty := by
    obtain ⟨v, s, hs, -⟩ := isGLB_nonempty_aux (hSD x0).2.1
    rw [(hF x0).1] at hs
    exact ⟨_, (x0, s), ⟨hx0.1, hx0.2, hs.1, hs.2⟩, rfl⟩
  have hbdd14 : BddBelow S14 := by
    obtain ⟨L, hL⟩ := hbddX
    exact ⟨L, hlb ▸ hL⟩
  have hGLB14 : IsGLB S14 (ZhatSDP A b c T α β ps μ Q) := isGLB_csInf hne14 hbdd14
  have hGLBX : IsGLB SX (ZhatSDP A b c T α β ps μ Q) := by
    unfold IsGLB; rw [hlb]; exact hGLB14
  refine ⟨fun x _ => (hSD x).2.2.trans (hF x).2, hGLBX, hGLB14, ?_⟩
  exact hGLBX.csInf_eq hneX
