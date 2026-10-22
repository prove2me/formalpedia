-- Prove2me | solution 1 for MitigateSupplyRisk.LateCommit.late_dominates_early
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:32:52.584995+00:00
-- url     : https://prove2.me/submissions/3573854e-65c1-448f-9472-8b30b78ba856

import Mathlib
import Definitions.Def_MitigateSupplyRisk_LateCommit_Model

set_option autoImplicit false
open MeasureTheory MitigateSupplyRisk.LateCommit

lemma qq_pt (M : Market) (S : Supplier) (c q ξ x : ℝ) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hξ : 0 ≤ ξ) (hx : 0 ≤ x) :
    realizedProfit M S c q ξ x ≤ (M.r + max M.v 0) * S.K := by
  unfold realizedProfit
  have hy0 : 0 ≤ delivered S.K q ξ := le_min hq (le_max_right _ _)
  have hyK : delivered S.K q ξ ≤ S.K :=
    (min_le_right _ _).trans (max_le (by linarith) S.K_pos.le)
  set y := delivered S.K q ξ with hy
  have h1 : 0 ≤ (S.η * q + (1 - S.η) * y) * c :=
    mul_nonneg (add_nonneg (mul_nonneg S.η_nonneg hq)
      (mul_nonneg (sub_nonneg.2 S.η_le_one) hy0)) hc
  have h2 : M.r * min x y ≤ M.r * S.K :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hyK) M.r_nonneg
  have ht : max (y - x) 0 ≤ S.K := max_le (by linarith) S.K_pos.le
  have h3 : M.v * max (y - x) 0 ≤ max M.v 0 * S.K :=
    calc M.v * max (y - x) 0 ≤ max M.v 0 * max (y - x) 0 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (le_max_right _ _)
      _ ≤ max M.v 0 * S.K := mul_le_mul_of_nonneg_left ht (le_max_right _ _)
  have h4 : 0 ≤ M.p * max (x - y) 0 := mul_nonneg M.p_nonneg (le_max_right _ _)
  nlinarith

lemma qq_int (M : Market) (S : Supplier) (c q a : ℝ) (hc : 0 ≤ c) (hq : 0 ≤ q) :
    secondStageProfit M S c q a ≤ (M.r + max M.v 0) * S.K := by
  haveI := S.ν_prob a
  haveI := M.μ_prob
  have hB : 0 ≤ (M.r + max M.v 0) * S.K :=
    mul_nonneg (add_nonneg M.r_nonneg (le_max_right _ _)) S.K_pos.le
  have h1 : ∀ᵐ ξ ∂(S.ν a), 0 ≤ ξ := by
    have : {ξ : ℝ | ¬ 0 ≤ ξ} = Set.Iio 0 := by ext; simp
    rw [ae_iff, this]; exact S.loss_nonneg a
  have h2 : ∀ᵐ x ∂M.μ, 0 ≤ x := by
    have : {ξ : ℝ | ¬ 0 ≤ ξ} = Set.Iio 0 := by ext; simp
    rw [ae_iff, this]; exact M.demand_nonneg
  have h1' : ∀ᵐ w ∂((S.ν a).prod M.μ), 0 ≤ w.1 :=
    Measure.quasiMeasurePreserving_fst.ae h1
  have h2' : ∀ᵐ w ∂((S.ν a).prod M.μ), 0 ≤ w.2 :=
    Measure.quasiMeasurePreserving_snd.ae h2
  unfold secondStageProfit
  by_cases hI : Integrable (fun w : ℝ × ℝ => realizedProfit M S c q w.1 w.2)
      ((S.ν a).prod M.μ)
  · calc _ ≤ ∫ _w, (M.r + max M.v 0) * S.K ∂((S.ν a).prod M.μ) :=
          integral_mono_ae hI (integrable_const _) (by
            filter_upwards [h1', h2'] with w hw1 hw2
            exact qq_pt M S c q w.1 w.2 hc hq hw1 hw2)
      _ = _ := by simp
  · rw [integral_undef hI]; exact hB

theorem solution (X : Setting) : X.earlyValue ≤ X.lateValue := by
  have hB1 : ∀ a, X.P₁ a ≤ (X.M.r + max X.M.v 0) * X.S₁.K := by
    intro a
    apply csSup_le
    · exact ⟨_, ⟨0, Set.mem_Ici.2 le_rfl, rfl⟩⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact qq_int _ _ _ _ _ X.c₁_nonneg hq
  have hB2 : ∀ a, X.P₂ a ≤ (X.M.r + max X.M.v 0) * X.S₂.K := by
    intro a
    apply csSup_le
    · exact ⟨_, ⟨0, Set.mem_Ici.2 le_rfl, rfl⟩⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact qq_int _ _ _ _ _ X.c₂_nonneg hq
  set Bm := max ((X.M.r + max X.M.v 0) * X.S₁.K) ((X.M.r + max X.M.v 0) * X.S₂.K) with hBm
  have hP1 : ∀ a, X.P₁ a ≤ Bm := fun a => (hB1 a).trans (le_max_left _ _)
  have hP2 : ∀ a, X.P₂ a ≤ Bm := fun a => (hB2 a).trans (le_max_right _ _)
  have hz1 : ∀ a, X.I₁.a0 ≤ a → 0 ≤ X.I₁.z a := fun a ha => by
    have := X.I₁.z_mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ha) ha
    rwa [X.I₁.z_a0] at this
  have hz2 : ∀ a, X.I₂.a0 ≤ a → 0 ≤ X.I₂.z a := fun a ha => by
    have := X.I₂.z_mono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ha) ha
    rwa [X.I₂.z_a0] at this
  have t1 := X.I₁.θ_nonneg
  have t1' := X.I₁.θ_le_one
  have t2 := X.I₂.θ_nonneg
  have t2' := X.I₂.θ_le_one
  have m1 := X.I₁.m_nonneg
  have m2 := X.I₂.m_nonneg
  have hbdd : BddAbove ((fun a : ℝ × ℝ => X.lateProfit a.1 a.2) '' X.lateFeasible) := by
    refine ⟨Bm, ?_⟩
    rintro _ ⟨⟨a1, a2⟩, ⟨h1, h2⟩, rfl⟩
    have h1 : X.I₁.a0 ≤ a1 := h1
    have h2 : X.I₂.a0 ≤ a2 := h2
    have hmax : ∀ a b, max (X.P₁ a) (X.P₂ b) ≤ Bm := fun a b => max_le (hP1 a) (hP2 b)
    have e1 := mul_le_mul_of_nonneg_left (hmax a1 a2) (mul_nonneg t1 t2)
    have e2 := mul_le_mul_of_nonneg_left (hmax a1 X.I₂.a0) (mul_nonneg t1 (sub_nonneg.2 t2'))
    have e3 := mul_le_mul_of_nonneg_left (hmax X.I₁.a0 a2) (mul_nonneg (sub_nonneg.2 t1') t2)
    have e4 := mul_le_mul_of_nonneg_left (hmax X.I₁.a0 X.I₂.a0)
      (mul_nonneg (sub_nonneg.2 t1') (sub_nonneg.2 t2'))
    have f1 := mul_nonneg m1 (hz1 a1 h1)
    have f2 := mul_nonneg m2 (hz2 a2 h2)
    have : X.I₁.θ * X.I₂.θ * Bm + X.I₁.θ * (1 - X.I₂.θ) * Bm + (1 - X.I₁.θ) * X.I₂.θ * Bm
        + (1 - X.I₁.θ) * (1 - X.I₂.θ) * Bm = Bm := by ring
    unfold Setting.lateProfit
    linarith
  have hle : ∀ a1 a2, X.I₁.a0 ≤ a1 → X.I₂.a0 ≤ a2 → X.lateProfit a1 a2 ≤ X.lateValue :=
    fun a1 a2 h1 h2 => le_csSup hbdd ⟨(a1, a2), ⟨h1, h2⟩, rfl⟩
  unfold Setting.earlyValue
  apply max_le
  · apply csSup_le
    · exact ⟨_, ⟨X.I₁.a0, Set.mem_Ici.2 le_rfl, rfl⟩⟩
    · rintro _ ⟨a, ha, rfl⟩
      have ha : X.I₁.a0 ≤ a := ha
      refine le_trans ?_ (hle a X.I₂.a0 ha le_rfl)
      have k1 : 0 ≤ X.I₁.θ * (max (X.P₁ a) (X.P₂ X.I₂.a0) - X.P₁ a) :=
        mul_nonneg t1 (sub_nonneg.2 (le_max_left _ _))
      have k2 : 0 ≤ (1 - X.I₁.θ) * (max (X.P₁ X.I₁.a0) (X.P₂ X.I₂.a0) - X.P₁ X.I₁.a0) :=
        mul_nonneg (sub_nonneg.2 t1') (sub_nonneg.2 (le_max_left _ _))
      have e1 : X.early₁ a = -(X.I₁.m * X.I₁.z a) + X.I₁.θ * X.P₁ a
          + (1 - X.I₁.θ) * X.P₁ X.I₁.a0 := rfl
      rw [e1]
      unfold Setting.lateProfit
      rw [X.I₂.z_a0]
      nlinarith
  · apply csSup_le
    · exact ⟨_, ⟨X.I₂.a0, Set.mem_Ici.2 le_rfl, rfl⟩⟩
    · rintro _ ⟨a, ha, rfl⟩
      have ha : X.I₂.a0 ≤ a := ha
      refine le_trans ?_ (hle X.I₁.a0 a le_rfl ha)
      have k1 : 0 ≤ X.I₂.θ * (max (X.P₁ X.I₁.a0) (X.P₂ a) - X.P₂ a) :=
        mul_nonneg t2 (sub_nonneg.2 (le_max_right _ _))
      have k2 : 0 ≤ (1 - X.I₂.θ) * (max (X.P₁ X.I₁.a0) (X.P₂ X.I₂.a0) - X.P₂ X.I₂.a0) :=
        mul_nonneg (sub_nonneg.2 t2') (sub_nonneg.2 (le_max_right _ _))
      have e1 : X.early₂ a = -(X.I₂.m * X.I₂.z a) + X.I₂.θ * X.P₂ a
          + (1 - X.I₂.θ) * X.P₂ X.I₂.a0 := rfl
      rw [e1]
      unfold Setting.lateProfit
      rw [X.I₁.z_a0]
      nlinarith
