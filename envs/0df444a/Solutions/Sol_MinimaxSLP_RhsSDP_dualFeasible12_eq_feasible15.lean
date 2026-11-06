-- Prove2me | solution 1 for MinimaxSLP.RhsSDP.dualFeasible12_eq_feasible15
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:55:02.146536+00:00
-- url     : https://prove2.me/submissions/5e8fb1dd-ff11-4841-b4a6-cd56589495ae

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic
import Definitions.Def_MinimaxSLP_RhsSDP_Model
import Theorems.Thm_MinimaxSLP_RhsSDP_dual_constraint_rewrite
import Theorems.Thm_MinimaxSLP_RhsSDP_Qval_eq_max_extreme_points
import Theorems.Thm_WorstCaseVaR_KnownMoments_quadratic_form_nonneg_iff_posSemidef

open MeasureTheory Matrix

lemma bordered_isSymm_aux {r : ℕ} (Y : Matrix (Fin r) (Fin r) ℝ) (hY : Y.IsSymm)
    (v : Fin r → ℝ) (c : ℝ) : (WorstCaseVaR.KnownMoments.bordered Y v c).IsSymm := by
  unfold WorstCaseVaR.KnownMoments.bordered
  rw [Matrix.IsSymm, Matrix.fromBlocks_transpose]
  rw [hY.eq]
  congr 1

lemma quadFn_bordered_aux {r : ℕ} (Y : Matrix (Fin r) (Fin r) ℝ)
    (v : Fin r → ℝ) (c : ℝ) (h : Fin r → ℝ) :
    WorstCaseVaR.KnownMoments.quadFn (WorstCaseVaR.KnownMoments.bordered Y v c) h =
      h ⬝ᵥ (Y *ᵥ h) + 2 * (v ⬝ᵥ h) + c := by
  unfold WorstCaseVaR.KnownMoments.quadFn WorstCaseVaR.KnownMoments.bordered
    WorstCaseVaR.KnownMoments.liftVec
  rw [Matrix.fromBlocks_mulVec]
  simp only [sumElim_dotProduct_sumElim]
  simp [dotProduct, mulVec, Finset.mul_sum, Function.comp_def]
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : ∑ x, h x * v x = ∑ i, v i * h i := Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have h2 : ∑ i, 2 * (v i * h i) = 2 * ∑ i, v i * h i := (Finset.mul_sum _ _ _).symm
  have h3 : ∑ x, h x * ∑ x_1, Y x x_1 * h x_1 = ∑ x, ∑ i, h x * (Y x i * h i) :=
    Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
  linarith

lemma psd_bordered_iff_aux {r : ℕ} (Y : Matrix (Fin r) (Fin r) ℝ) (hY : Y.IsSymm)
    (v : Fin r → ℝ) (c : ℝ) :
    (WorstCaseVaR.KnownMoments.bordered Y v c).PosSemidef ↔
      ∀ h : Fin r → ℝ, 0 ≤ h ⬝ᵥ (Y *ᵥ h) + 2 * (v ⬝ᵥ h) + c := by
  rw [← WorstCaseVaR.KnownMoments.quadratic_form_nonneg_iff_posSemidef _
    (bordered_isSymm_aux Y hY v c)]
  constructor
  · intro H h
    have := H (WithLp.toLp 2 h)
    simpa [quadFn_bordered_aux] using this
  · intro H x
    rw [quadFn_bordered_aux]
    exact H _

theorem solution {r d n K N : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (ps : Fin N → Fin r → ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) :
    MinimaxSLP.RhsSDP.dualFeasible12 W T q α β x = MinimaxSLP.RhsSDP.feasible15 T α β ps x ∧
      MinimaxSLP.RhsSDP.ZhatD W T q α β μ Q x = MinimaxSLP.RhsSDP.ZhatD15 T α β ps μ Q x := by
  have hset : MinimaxSLP.RhsSDP.dualFeasible12 W T q α β x =
      MinimaxSLP.RhsSDP.feasible15 T α β ps x := by
    ext s
    have hrw := MinimaxSLP.RhsSDP.dual_constraint_rewrite W T q α β hα hA2 hA3 x s
    have key : ∀ (hY : s.1.IsSymm) (k : Fin K) (p : Fin r → ℝ),
        (MinimaxSLP.RhsSDP.bordered15 T s.1 s.2.1 s.2.2 (α k) (β k) p x).PosSemidef ↔
        ∀ h : Fin r → ℝ,
          0 ≤ h ⬝ᵥ (s.1 *ᵥ h) + (s.2.1 - α k • p) ⬝ᵥ h + s.2.2 + α k * (p ⬝ᵥ (T *ᵥ x)) - β k := by
      intro hY k p
      unfold MinimaxSLP.RhsSDP.bordered15
      rw [psd_bordered_iff_aux _ hY]
      refine forall_congr' (fun h => ?_)
      have : 2 * ((1 / 2 : ℝ) • (s.2.1 - α k • p) ⬝ᵥ h) = (s.2.1 - α k • p) ⬝ᵥ h := by
        rw [smul_dotProduct, smul_eq_mul]; ring
      rw [this]
      constructor <;> intro H <;> linarith
    constructor
    · intro hs
      obtain ⟨hY, H⟩ := hrw.2.1 hs
      refine ⟨hY, fun k i => (key hY k (ps i)).2 (fun h => H h (ps i) k ?_)⟩
      have : ps i ∈ Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q} := hA5 ▸ ⟨i, rfl⟩
      exact this.1
    · intro hs
      obtain ⟨hY, H⟩ := hs
      refine hrw.1.2 ⟨hY, fun h k => ?_⟩
      obtain ⟨⟨i, hi⟩, -⟩ :=
        MinimaxSLP.RhsSDP.Qval_eq_max_extreme_points W T q ps hA2 hA3 hA5 x h
      have H2 := (key hY k (ps i)).1 (H k i) h
      rw [← hi]
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul] at H2 ⊢
      rw [dotProduct_comm (T *ᵥ x) (ps i), dotProduct_comm h (ps i)]
      nlinarith [H2]
  refine ⟨hset, ?_⟩
  unfold MinimaxSLP.RhsSDP.ZhatD MinimaxSLP.RhsSDP.ZhatD15
  rw [hset]
