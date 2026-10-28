-- Prove2me | solution 1 for MultiItemRev.BundlingOpt.symmetrization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T18:05:11.981844+00:00
-- url     : https://prove2.me/submissions/89235fe3-ce41-44e8-ab04-0cc1692c91da

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_MultiItemRev_BundlingOpt_Bundling
open MeasureTheory
open scoped NNReal ENNReal

namespace Aux_MIR_sym

open MultiItemRev.BundlingOpt

lemma sw0 (x : Fin 2 → ℝ≥0) : swap2 x 0 = x 1 := by simp [swap2]
lemma sw1 (x : Fin 2 → ℝ≥0) : swap2 x 1 = x 0 := by simp [swap2]
lemma swsw (x : Fin 2 → ℝ≥0) : swap2 (swap2 x) = x := by
  funext i; fin_cases i <;> simp [swap2]

lemma meas_swap2 : Measurable swap2 := by
  unfold swap2
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)

lemma swap2_eq : swap2 = ⇑(MeasurableEquiv.arrowCongr' (Equiv.swap (0 : Fin 2) 1)
    (MeasurableEquiv.refl ℝ≥0)) := by
  funext x i
  simp [swap2, MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr]

lemma mp_swap2 (ν : Measure ℝ≥0) [SigmaFinite ν] :
    MeasurePreserving swap2 (Measure.pi (fun _ : Fin 2 => ν)) (Measure.pi (fun _ : Fin 2 => ν)) := by
  rw [swap2_eq]
  exact measurePreserving_arrowCongr' (fun _ => ν) (fun _ => ν) _ _
    (fun _ => MeasurePreserving.id ν)

end Aux_MIR_sym

open MultiItemRev.BundlingOpt Aux_MIR_sym in
theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] (M : Mechanism (Fin 2))
    (hM : IsAdmissible M ∧ IsNPT M) :
    IsAdmissible (symmetrize M) ∧ IsNPT (symmetrize M) ∧ IsSymmetric (symmetrize M) ∧
      expRevenue (Measure.pi (fun _ : Fin 2 => ν)) (symmetrize M) =
        expRevenue (Measure.pi (fun _ : Fin 2 => ν)) M := by
  obtain ⟨⟨hF, hIC, hIR, hmeas⟩, hNPT⟩ := hM
  have hq : ∀ x, (symmetrize M).q x 0 = (M.q x 0 + M.q (swap2 x) 1) / 2 ∧
      (symmetrize M).q x 1 = (M.q x 1 + M.q (swap2 x) 0) / 2 := fun x => ⟨rfl, rfl⟩
  have hs : ∀ x, (symmetrize M).s x = (M.s x + M.s (swap2 x)) / 2 := fun x => rfl
  -- IC term of the symmetrization
  have hterm : ∀ x x', ∑ i, (symmetrize M).q x' i * (x i : ℝ) - (symmetrize M).s x' =
      ((∑ i, M.q x' i * (x i : ℝ) - M.s x') +
        (∑ i, M.q (swap2 x') i * (swap2 x i : ℝ) - M.s (swap2 x'))) / 2 := by
    intro x x'
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, (hq x').1, (hq x').2, hs, sw0, sw1]
    ring
  have hpay : ∀ x, buyerPayoff (symmetrize M) x =
      (buyerPayoff M x + buyerPayoff M (swap2 x)) / 2 := fun x => hterm x x
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x i
    fin_cases i
    · simp only [Fin.zero_eta, (hq x).1]
      have h1 := hF x 0; have h2 := hF (swap2 x) 1
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · simp only [Fin.mk_one, (hq x).2]
      have h1 := hF x 1; have h2 := hF (swap2 x) 0
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · intro x x'
    rw [hterm, hpay]
    have h1 := hIC x x'
    have h2 := hIC (swap2 x) (swap2 x')
    unfold buyerPayoff at h1 h2 ⊢
    linarith
  · intro x
    rw [hpay]
    have := hIR x; have := hIR (swap2 x)
    linarith
  · show Measurable (fun x => (M.s x + M.s (swap2 x)) / 2)
    exact (hmeas.add (hmeas.comp meas_swap2)).div_const 2
  · intro x
    rw [hs]
    have := hNPT x; have := hNPT (swap2 x)
    linarith
  · intro x
    refine ⟨?_, ?_⟩
    · rw [(hq x).1, (hq (swap2 x)).2, swsw]; ring
    · rw [hs, hs, swsw]; ring
  · unfold expRevenue
    have hneg0 : ∀ x, ENNReal.ofReal (-(symmetrize M).s x) = 0 := by
      intro x; rw [hs]; apply ENNReal.ofReal_of_nonpos
      have := hNPT x; have := hNPT (swap2 x); linarith
    have hneg0' : ∀ x, ENNReal.ofReal (-M.s x) = 0 := by
      intro x; apply ENNReal.ofReal_of_nonpos; have := hNPT x; linarith
    simp only [hneg0, hneg0', lintegral_zero]
    congr 2
    have hsplit : ∀ x, ENNReal.ofReal ((symmetrize M).s x) =
        (ENNReal.ofReal (M.s x) + ENNReal.ofReal (M.s (swap2 x))) / 2 := by
      intro x
      rw [hs, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_add (hNPT x) (hNPT _)]
      simp
    simp only [hsplit]
    have hm1 : Measurable (fun x => ENNReal.ofReal (M.s x)) := ENNReal.measurable_ofReal.comp hmeas
    simp only [div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (by simp), lintegral_add_left hm1]
    have hswap : ∫⁻ x, ENNReal.ofReal (M.s (swap2 x)) ∂(Measure.pi fun _ : Fin 2 => ν) =
        ∫⁻ x, ENNReal.ofReal (M.s x) ∂(Measure.pi fun _ : Fin 2 => ν) :=
      (mp_swap2 ν).lintegral_comp hm1
    rw [hswap, ← two_mul, mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero
      ENNReal.ofNat_ne_top, one_mul]
