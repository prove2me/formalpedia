-- Prove2me | solution 1 for MinimaxSLP.RhsSDP.dual_constraint_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:06:20.556167+00:00
-- url     : https://prove2.me/submissions/f432b3f7-b32b-4b5d-bb0c-e49615e11433

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model

open MeasureTheory Matrix

open MinimaxSLP.RhsSDP in
theorem solution {r d n K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (s : Matrix (Fin r) (Fin r) ℝ × (Fin r → ℝ) × ℝ) :
    (s ∈ dualFeasible12 W T q α β x ↔
      s.1.IsSymm ∧ ∀ (h : Fin r → ℝ) (k : Fin K),
        α k * Qval W T q h x + β k ≤ h ⬝ᵥ (s.1 *ᵥ h) + s.2.1 ⬝ᵥ h + s.2.2) ∧
    (s ∈ dualFeasible12 W T q α β x ↔
      s.1.IsSymm ∧ ∀ (h : Fin r → ℝ) (π : Fin r → ℝ) (k : Fin K), Wᵀ *ᵥ π ≤ q →
        0 ≤ h ⬝ᵥ (s.1 *ᵥ h) + (s.2.1 - α k • π) ⬝ᵥ h + s.2.2 + α k * (π ⬝ᵥ (T *ᵥ x)) - β k) := by
  -- the image set defining Qval
  have hne : ∀ h : Fin r → ℝ,
      ((fun π => (h - T *ᵥ x) ⬝ᵥ π) '' {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q}).Nonempty := by
    intro h
    obtain ⟨π, hπ⟩ := hA3
    exact ⟨_, π, hπ, rfl⟩
  have hbdd : ∀ h : Fin r → ℝ,
      BddAbove ((fun π => (h - T *ᵥ x) ⬝ᵥ π) '' {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q}) := by
    intro h
    obtain ⟨w, hw0, hw⟩ := hA2 (h - T *ᵥ x)
    refine ⟨w ⬝ᵥ q, ?_⟩
    rintro _ ⟨π, hπ, rfl⟩
    have e : (h - T *ᵥ x) ⬝ᵥ π = w ⬝ᵥ (Wᵀ *ᵥ π) := by
      rw [← hw, dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
    show (h - T *ᵥ x) ⬝ᵥ π ≤ w ⬝ᵥ q
    rw [e]
    exact dotProduct_le_dotProduct_of_nonneg_left hπ hw0
  -- key equivalence for fixed h, k
  have key : ∀ (h : Fin r → ℝ) (k : Fin K) (R : ℝ),
      α k * Qval W T q h x + β k ≤ R ↔
        ∀ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q → α k * ((h - T *ᵥ x) ⬝ᵥ π) + β k ≤ R := by
    intro h k R
    constructor
    · intro hR π hπ
      have hle : (h - T *ᵥ x) ⬝ᵥ π ≤ Qval W T q h x := le_csSup (hbdd h) ⟨π, hπ, rfl⟩
      have := mul_le_mul_of_nonneg_left hle (hα k)
      linarith
    · intro hall
      rcases (hα k).lt_or_eq with hpos | hzero
      · have hQ : Qval W T q h x ≤ (R - β k) / α k := by
          refine csSup_le (hne h) ?_
          rintro _ ⟨π, hπ, rfl⟩
          rw [le_div_iff₀ hpos]
          have := hall π hπ
          linarith
        have := mul_le_mul_of_nonneg_left hQ (hα k)
        rw [mul_div_cancel₀ _ hpos.ne'] at this
        linarith
      · obtain ⟨π, hπ⟩ := hA3
        have := hall π hπ
        rw [← hzero] at this ⊢
        linarith
  have part1 : s ∈ dualFeasible12 W T q α β x ↔
      s.1.IsSymm ∧ ∀ (h : Fin r → ℝ) (k : Fin K),
        α k * Qval W T q h x + β k ≤ h ⬝ᵥ (s.1 *ᵥ h) + s.2.1 ⬝ᵥ h + s.2.2 := by
    unfold dualFeasible12 MinimaxSLP.ObjSDP.disutility
    simp only [Set.mem_setOf_eq, Finset.sup'_le_iff, Finset.mem_univ, true_implies]
  refine ⟨part1, part1.trans ?_⟩
  refine and_congr_right fun _ => ?_
  constructor
  · intro H h π k hπ
    have := (key h k _).mp (H h k) π hπ
    have e : (s.2.1 - α k • π) ⬝ᵥ h + α k * (π ⬝ᵥ (T *ᵥ x))
        = s.2.1 ⬝ᵥ h - α k * ((h - T *ᵥ x) ⬝ᵥ π) := by
      rw [sub_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul, dotProduct_comm π h,
        dotProduct_comm π (T *ᵥ x)]
      ring
    linarith
  · intro H h k
    refine (key h k _).mpr fun π hπ => ?_
    have := H h π k hπ
    have e : (s.2.1 - α k • π) ⬝ᵥ h + α k * (π ⬝ᵥ (T *ᵥ x))
        = s.2.1 ⬝ᵥ h - α k * ((h - T *ᵥ x) ⬝ᵥ π) := by
      rw [sub_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul, dotProduct_comm π h,
        dotProduct_comm π (T *ᵥ x)]
      ring
    linarith
