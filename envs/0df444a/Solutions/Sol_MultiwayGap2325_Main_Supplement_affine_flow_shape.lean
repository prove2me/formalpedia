-- Prove2me | solution 1 for MultiwayGap2325.Main.Supplement.affine_flow_shape
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:40:34.269332+00:00
-- url     : https://prove2.me/submissions/b03ea346-b7d8-44d7-ab6c-0c536f8bd792

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

open MultiwayGap2325.Main.Supplement

noncomputable section

theorem solution (q : ℕ) (T : ℝ) :
    HasAffineLabelFlows T (affineData q T) ∧
      HasConstantWeights T (affineData q T) := by
  constructor
  · intro S l hl
    rcases hl with rfl | ⟨i, hi, rfl⟩
    · refine ⟨0, 0, ?_⟩
      intro P hP x hx
      simp [affineData]
    · let a : ℝ := affineScale q T S.val.card
      let c : ℝ := (S.val.card : ℝ) * T - 1
      let A : Vec q →L[ℝ] Vec q := ContinuousLinearMap.pi fun s =>
        if s ∈ S.val then (a / c) • ContinuousLinearMap.proj s else 0
      refine ⟨A, fun s => a *
        ((if s = i then 1 else 0) - (if s ∈ S.val then T / c else 0)), ?_⟩
      intro P hP x hx
      funext s
      change affineScale q T S.val.card *
        ((if s = i then 1 else 0) - affineMargin T S x s) = _
      simp only [affineMargin, A, ContinuousLinearMap.pi_apply, Vec, Pi.add_apply]
      dsimp only [a, c]
      by_cases hs : s ∈ S.val
      · simp only [hs, if_true]
        by_cases hsi : s = i <;>
          simp [hsi, smul_eq_mul] <;> ring
      · simp only [hs, if_false]
        have hsi : s ≠ i := fun h => hs (h ▸ hi)
        simp [hsi, smul_eq_mul]
  · constructor
    · intro S i j hi hj hij
      refine ⟨affineScale q T S.val.card / (S.val.card - 1 : ℝ), ?_⟩
      intro x hx
      rfl
    · intro S i hi
      refine ⟨affineScale q T S.val.card, ?_⟩
      intro x hx
      rfl
