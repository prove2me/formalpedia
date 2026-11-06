-- Prove2me | solution 1 for MinimaxSLP.ObjSDP.constraint_iff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:41:59.395063+00:00
-- url     : https://prove2.me/submissions/6e62858c-96ed-4d36-84b9-506afcd8b659

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model
import Theorems.Thm_MinimaxSLP_ObjSDP_sion_exchange
import Theorems.Thm_MinimaxSLP_ObjSDP_Y_posSemidef
import Theorems.Thm_MinimaxSLP_ObjSDP_recourseSet_bounded

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP.CIAux

/-- Under Assumption 3 and `X(x) ≠ ∅`, the LP `min_{w ∈ X(x)} q′w` is attained, so
`𝒬(q, x) = q′w_q` for some `w_q ∈ X(x)` and `𝒬(q, x) ≤ q′w` for all `w ∈ X(x)`. -/
lemma Qval_attained {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) (q : Fin d → ℝ) :
    ∃ wq ∈ recourseSet W T h x, Qval W T h q x = q ⬝ᵥ wq ∧
      ∀ w ∈ recourseSet W T h x, Qval W T h q x ≤ q ⬝ᵥ w := by
  have hbdd := (recourseSet_bounded W T h hA3 x).1
  have hcl : IsClosed (recourseSet W T h x) := by
    have : recourseSet W T h x = {w | W *ᵥ w = h - T *ᵥ x} ∩ {w | 0 ≤ w} := rfl
    rw [this]
    refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_le continuous_const
      continuous_id)
    exact (Continuous.matrix_mulVec continuous_const continuous_id)
  have hK : IsCompact (recourseSet W T h x) := Metric.isCompact_of_isClosed_isBounded hcl hbdd
  have hcont : ContinuousOn (fun w : Fin d → ℝ => q ⬝ᵥ w) (recourseSet W T h x) :=
    (Continuous.dotProduct continuous_const continuous_id).continuousOn
  obtain ⟨wq, hwq, hmin⟩ := hK.exists_isMinOn hrec hcont
  have hleast : IsLeast ((fun w => q ⬝ᵥ w) '' recourseSet W T h x) (q ⬝ᵥ wq) :=
    ⟨⟨wq, hwq, rfl⟩, by rintro _ ⟨w, hw, rfl⟩; exact hmin hw⟩
  have hQ : Qval W T h q x = q ⬝ᵥ wq := hleast.csInf_eq
  refine ⟨wq, hwq, hQ, fun w hw => ?_⟩
  rw [hQ]; exact hmin hw

end MinimaxSLP.ObjSDP.CIAux

open MinimaxSLP.ObjSDP MinimaxSLP.ObjSDP.CIAux in
theorem solution {n r d K : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (k : Fin K) (hαk : 0 ≤ α k)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Y.IsSymm) (y : Fin d → ℝ) (y₀ : ℝ) :
    (∀ q : Fin d → ℝ, α k * Qval W T h q x + β k ≤ q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀) ↔
      ∃ w ∈ recourseSet W T h x, ∀ q : Fin d → ℝ,
        0 ≤ q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - α k * (q ⬝ᵥ w) - β k := by
  constructor
  · intro hC
    have hYpsd : Y.PosSemidef := Y_posSemidef W T h α β k hαk hA3 x hrec Y hY y y₀ hC
    have hbdd := (recourseSet_bounded W T h hA3 x).1
    obtain ⟨heq, w₀, hw₀, hmax⟩ := sion_exchange W T h x hrec hbdd Y hYpsd y y₀ (α k) (β k)
    -- `inf_q max_{w ∈ X(x)} g(q, w) ≥ 0`, using a minimiser `w_q` of `q′w` on `X(x)`
    have hL : (0 : EReal) ≤ ⨅ q : Fin d → ℝ, ⨆ w ∈ recourseSet W T h x,
        ((q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y₀ - α k * (q ⬝ᵥ w) - β k : ℝ) : EReal) := by
      refine le_iInf fun q => ?_
      obtain ⟨wq, hwq, hQ, -⟩ := Qval_attained W T h hA3 x hrec q
      refine le_iSup₂_of_le wq hwq ?_
      have := hC q
      rw [hQ] at this
      exact EReal.coe_nonneg.2 (by linarith)
    rw [heq, ← hmax] at hL
    refine ⟨w₀, hw₀, fun q => ?_⟩
    exact EReal.coe_nonneg.1 (le_trans hL (iInf_le _ q))
  · rintro ⟨w, hw, hq⟩ q
    obtain ⟨wq, -, -, hle⟩ := Qval_attained W T h hA3 x hrec q
    have h1 := mul_le_mul_of_nonneg_left (hle w hw) hαk
    have h2 := hq q
    linarith
