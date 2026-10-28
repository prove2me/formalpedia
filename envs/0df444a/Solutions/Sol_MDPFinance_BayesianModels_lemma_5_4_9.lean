-- Prove2me | solution 1 for MDPFinance.BayesianModels.lemma_5_4_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:42:20.140236+00:00
-- url     : https://prove2.me/submissions/bf6c9460-04a9-4501-b8fe-907b05aad5b7

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior
import Definitions.Def_MDPFinance_BayesianModels_SuffStat
import Definitions.Def_MDPFinance_BayesianModels_Orders

open MeasureTheory ProbabilityTheory

namespace MDP549Aux
open MDPFinance.BayesianModels

theorem lr_iff_mtp2 (q : ℝ → ℝ → ℝ) :
    (∀ θ θ' : ℝ, θ ≤ θ' → LikelihoodRatioOrder (q θ) (q θ')) ↔
      IsMTP2 fun p : ℝ × ℝ => q p.2 p.1 := by
  constructor
  · intro h x y
    obtain ⟨z₁, θ₁⟩ := x
    obtain ⟨z₂, θ₂⟩ := y
    simp only [Prod.mk_inf_mk, Prod.mk_sup_mk]
    rcases le_total z₁ z₂ with hz | hz <;> rcases le_total θ₁ θ₂ with hθ | hθ
    · simp [inf_eq_left.2 hz, sup_eq_right.2 hz, inf_eq_left.2 hθ, sup_eq_right.2 hθ]
    · rw [inf_eq_left.2 hz, sup_eq_right.2 hz, inf_eq_right.2 hθ, sup_eq_left.2 hθ]
      have := h θ₂ θ₁ hθ z₁ z₂ hz
      linarith [mul_comm (q θ₂ z₂) (q θ₁ z₁)]
    · rw [inf_eq_right.2 hz, sup_eq_left.2 hz, inf_eq_left.2 hθ, sup_eq_right.2 hθ]
      have := h θ₁ θ₂ hθ z₂ z₁ hz
      linarith [mul_comm (q θ₂ z₂) (q θ₁ z₁)]
    · simp [inf_eq_right.2 hz, sup_eq_left.2 hz, inf_eq_right.2 hθ, sup_eq_left.2 hθ, mul_comm]
  · intro h θ θ' hθ s t hst
    have := h (t, θ) (s, θ')
    simp only [Prod.mk_inf_mk, Prod.mk_sup_mk, inf_eq_right.2 hst, sup_eq_left.2 hst,
      inf_eq_left.2 hθ, sup_eq_right.2 hθ] at this
    exact this

end MDP549Aux

open MDPFinance.BayesianModels in
theorem solution {EX A I : Type*} [MeasurableSpace EX] [MeasurableSpace A] [MeasurableSpace I]
    [Preorder I] (M : BayesModel EX ℝ A ℝ) (Pf : M.Posterior) (S : SuffStat M Pf I)
    (Phihat : EX → I → A → ℝ → I) (qZbar : ℝ → A → ℝ → ℝ)
    (hqZ : ∀ x θ a z, M.qZ x θ a z = qZbar θ a z) (phat : I → ℝ → ℝ)
    (hphat : ∀ i, S.muHat i = M.Q0.withDensity fun θ => ENNReal.ofReal (phat i θ))
    (hI_order : ∀ i i' : I, i ≤ i' ↔ LRMeasure M.Q0 (S.muHat i) (S.muHat i'))
    (hSeq : S.IsSequential Phihat)
    (hPhihat_bayes : ∀ x i a z,
      0 < (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) →
      (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) < ⊤ →
      ∀ C : Set ℝ, MeasurableSet C →
        S.muHat (Phihat x i a z) C =
          (∫⁻ θ in C, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) /
            (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i))) :
    ((∀ a, IsMTP2 fun q : ℝ × ℝ => qZbar q.2 a q.1) →
        ∀ x a (i i' : I) (z z' : ℝ), i ≤ i' → z ≤ z' →
          0 < (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) →
          (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) < ⊤ →
          0 < (∫⁻ θ, ENNReal.ofReal (qZbar θ a z') ∂(S.muHat i')) →
          (∫⁻ θ, ENNReal.ofReal (qZbar θ a z') ∂(S.muHat i')) < ⊤ →
          Phihat x i a z ≤ Phihat x i' a z') ∧
      (∀ a, (∀ θ θ' : ℝ, θ ≤ θ' → LikelihoodRatioOrder (qZbar θ a) (qZbar θ' a)) ↔
        IsMTP2 fun q : ℝ × ℝ => qZbar q.2 a q.1) := by
  refine ⟨?_, fun a => MDP549Aux.lr_iff_mtp2 (fun θ z => qZbar θ a z)⟩
  intro hM x a i i' z z' hii' hzz' hc0 hc1 hc0' hc1'
  have qnn : ∀ θ w, 0 ≤ qZbar θ a w := fun θ w => hqZ x θ a w ▸ M.hqZ_nonneg x θ a w
  have qmeas : ∀ w, Measurable fun θ => qZbar θ a w := by
    intro w
    have h := M.hqZ_meas.comp (show Measurable fun θ : ℝ => (x, θ, a, w) by fun_prop)
    simpa [Function.comp_def, hqZ] using h
  -- the key representation
  have key : ∀ (j : I) (w : ℝ) (f : ℝ → ℝ), Measurable f → (∀ θ, 0 ≤ f θ) →
      S.muHat j = M.Q0.withDensity (fun θ => ENNReal.ofReal (f θ)) →
      0 < (∫⁻ θ, ENNReal.ofReal (qZbar θ a w) ∂(S.muHat j)) →
      (∫⁻ θ, ENNReal.ofReal (qZbar θ a w) ∂(S.muHat j)) < ⊤ →
      S.muHat (Phihat x j a w) = M.Q0.withDensity (fun θ => ENNReal.ofReal
        (qZbar θ a w * f θ * ((∫⁻ θ, ENNReal.ofReal (qZbar θ a w) ∂(S.muHat j)).toReal)⁻¹)) := by
    intro j w f hf hf0 hj h0 h1
    set c := ∫⁻ θ, ENNReal.ofReal (qZbar θ a w) ∂(S.muHat j) with hc
    ext C hC
    rw [hPhihat_bayes x j a w h0 h1 C hC, ← hc, withDensity_apply _ hC, hj,
      setLIntegral_withDensity_eq_setLIntegral_mul _ (by fun_prop) (by fun_prop) hC,
      ENNReal.div_eq_inv_mul, ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 h0.ne')]
    refine setLIntegral_congr_fun hC (fun θ _ => ?_)
    have hcpos : 0 < c.toReal := ENNReal.toReal_pos h0.ne' h1.ne
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (mul_nonneg (qnn θ w) (hf0 θ)), ENNReal.ofReal_mul (qnn θ w),
      ENNReal.ofReal_inv_of_pos hcpos, ENNReal.ofReal_toReal h1.ne]
    ring
  obtain ⟨f, g, hf, hg, hf0, hg0, hfi, hgi, hfg⟩ := (hI_order i i').1 hii'
  rw [hI_order]
  refine ⟨_, _, by fun_prop, by fun_prop, fun θ => ?_, fun θ => ?_,
    key i z f hf hf0 hfi hc0 hc1, key i' z' g hg hg0 hgi hc0' hc1', ?_⟩
  · exact mul_nonneg (mul_nonneg (qnn θ z) (hf0 θ)) (inv_nonneg.2 ENNReal.toReal_nonneg)
  · exact mul_nonneg (mul_nonneg (qnn θ z') (hg0 θ)) (inv_nonneg.2 ENNReal.toReal_nonneg)
  intro s t hst
  set c := (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)).toReal⁻¹
  set c' := (∫⁻ θ, ENNReal.ofReal (qZbar θ a z') ∂(S.muHat i')).toReal⁻¹
  have hc : 0 ≤ c := inv_nonneg.2 ENNReal.toReal_nonneg
  have hc' : 0 ≤ c' := inv_nonneg.2 ENNReal.toReal_nonneg
  have hq : qZbar t a z * qZbar s a z' ≤ qZbar s a z * qZbar t a z' := by
    have := (MDP549Aux.lr_iff_mtp2 (fun θ w => qZbar θ a w)).2 (hM a) s t hst z z' hzz'
    simp only at this
    linarith [mul_comm (qZbar t a z) (qZbar s a z')]
  have h1 := hfg s t hst
  have h2 := mul_le_mul h1 hq (mul_nonneg (qnn t z) (qnn s z'))
    (mul_nonneg (hf0 s) (hg0 t))
  have h3 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hc hc')
  calc qZbar t a z * f t * c * (qZbar s a z' * g s * c')
      = f t * g s * (qZbar t a z * qZbar s a z') * (c * c') := by ring
    _ ≤ f s * g t * (qZbar s a z * qZbar t a z') * (c * c') := h3
    _ = qZbar s a z * f s * c * (qZbar t a z' * g t * c') := by ring
