-- Prove2me | solution 1 for GlobalTheory.CharSeriesCoef.continuousAt_coef_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:42:10.053483+00:00
-- url     : https://prove2.me/submissions/f9f6dce4-990a-40e2-aabd-e50c4da72745

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousAtCharSeriesCoefZero
import Theorems.Thm_GlobalTheory_CharSeriesCoef_norm_avg_le_one_of
import Theorems.Thm_GlobalTheory_CharSeriesCoef_exists_avg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CharSeriesCoef
namespace GlobalTheory.CharSeriesCoef
theorem _root_.solution {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P]
    (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (he0 : ∀ y, e 0 y = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ) (hM : Summable M)
    (hb : ∀ᶠ p in 𝓝 p0, ∀ a, ‖c p a‖ ≤ M a)
    (hc : ∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) :
    ContinuousAt (fun p => c p 0) p0 := by
  classical
  have hM0 : ∀ a, 0 ≤ M a := fun a => (norm_nonneg _).trans (hb.self_of_nhds a)
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set S := ∑' a, M a with hSdef
  have hS : 0 ≤ S := tsum_nonneg hM0
  obtain ⟨s, hs⟩ : ∃ s : Finset Ξ, S - ∑ a ∈ s, M a < ε / 6 := by
    have h2 := (Metric.tendsto_nhds.mp hM.hasSum) (ε / 6) (by positivity)
    obtain ⟨s, hs⟩ := h2.exists
    refine ⟨s, ?_⟩
    rw [Real.dist_eq] at hs
    linarith [neg_abs_le (∑ a ∈ s, M a - S)]
  set δ := ε / 6 / (S + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδS : δ * S ≤ ε / 6 := by
    have : δ * (S + 1) = ε / 6 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨ι, _, _, w, hw⟩ := exists_avg e hn hne δ hδ (s.erase 0) (by simp)
  set α : Ξ → ℂ := fun b => avg w (e b) with hαdef
  have hα1 : ∀ b, ‖α b‖ ≤ 1 := fun b => norm_avg_le_one_of _ (fun i => (hn b _).le)
  have hα0 : α 0 = 1 := by
    simp only [hαdef, avg, he0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  let A : P → ℂ := fun p => (Fintype.card ι : ℂ)⁻¹ * ∑ i, ∑' a, e a (w i) * c p a
  have hAc : ContinuousAt A p0 :=
    continuousAt_const.mul (tendsto_finset_sum _ (fun i _ => hc (w i)))

  have key : ∀ p, (∀ a, ‖c p a‖ ≤ M a) → ‖A p - c p 0‖ ≤ δ * S + (S - ∑ a ∈ s, M a) := by
    intro p hp
    have hsum : ∀ i, HasSum (fun a => e a (w i) * c p a) (∑' a, e a (w i) * c p a) := by
      intro i
      refine (Summable.of_norm_bounded hM (fun a => ?_)).hasSum
      rw [norm_mul, hn, one_mul]; exact hp a
    have h1 : HasSum (fun a => α a * c p a) (A p) := by
      have := (hasSum_sum (s := Finset.univ) (fun i _ => hsum i)).mul_left
        ((Fintype.card ι : ℂ)⁻¹)
      have hfun : (fun a => α a * c p a)
          = fun a => (Fintype.card ι : ℂ)⁻¹ * ∑ i, e a (w i) * c p a := by
        funext a
        simp only [hαdef, avg, Finset.sum_mul, mul_assoc]
      rw [hfun]; exact this
    have h2 : HasSum (fun a : Ξ => if a = (0:Ξ) then c p 0 else 0) (c p 0) := hasSum_ite_eq (0:Ξ) (c p 0)
    have h3 : HasSum (fun a => α a * c p a - if a = 0 then c p 0 else 0) (A p - c p 0) :=
      HasSum.sub h1 h2
    have hg : HasSum (fun a => δ * M a + (M a - if a ∈ s then M a else 0))
        (δ * S + (S - ∑ a ∈ s, M a)) := by
      refine (hM.hasSum.mul_left δ).add (hM.hasSum.sub ?_)
      have : HasSum (fun a => if a ∈ s then M a else 0) (∑ b ∈ s, if b ∈ s then M b else 0) :=
        hasSum_sum_of_ne_finset_zero (fun b hb => if_neg hb)
      have e2 : (∑ b ∈ s, if b ∈ s then M b else 0) = ∑ b ∈ s, M b :=
        Finset.sum_congr rfl (fun b hb => if_pos hb)
      rw [e2] at this
      exact this
    refine h3.norm_le_of_bounded hg (fun a => ?_)
    have hMa := hM0 a
    by_cases ha : a = 0
    · subst ha
      simp only [hα0, one_mul, if_true, sub_self, norm_zero]
      split_ifs <;> nlinarith [mul_nonneg hδ.le hMa]
    · simp only [ha, if_false, sub_zero]
      by_cases has : a ∈ s
      · simp only [has, if_true, sub_self, add_zero]
        rw [norm_mul]
        have := hw a (Finset.mem_erase.mpr ⟨ha, has⟩)
        exact mul_le_mul this (hp a) (norm_nonneg _) hδ.le
      · simp only [has, if_false, sub_zero]
        rw [norm_mul]
        have : ‖α a‖ * ‖c p a‖ ≤ 1 * M a := mul_le_mul (hα1 a) (hp a) (norm_nonneg _) zero_le_one
        nlinarith
  have hAev := (Metric.tendsto_nhds.mp hAc) (ε / 3) (by positivity)
  have hp0 := key p0 hb.self_of_nhds
  filter_upwards [hb, hAev] with p hp hAp
  have hpk := key p hp
  rw [dist_eq_norm] at hAp ⊢
  have : c p 0 - c p0 0 = -(A p - c p 0) + (A p - A p0) + (A p0 - c p0 0) := by ring
  rw [this]
  calc ‖-(A p - c p 0) + (A p - A p0) + (A p0 - c p0 0)‖
      ≤ ‖-(A p - c p 0)‖ + ‖A p - A p0‖ + ‖A p0 - c p0 0‖ := norm_add₃_le
    _ < ε := by rw [norm_neg]; linarith
end GlobalTheory.CharSeriesCoef
