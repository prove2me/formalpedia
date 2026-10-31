-- Prove2me | solution 1 for MinBuying.pmf_affiliated_marginal
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:55:10.461739+00:00
-- url     : https://prove2.me/submissions/a11327cd-d3f5-4359-85e2-64acfeca1c27

import Theorems.Thm_MinBuying_mtp2_summable_marginal

open MeasureTheory Set MinBuying
open scoped BigOperators ENNReal
noncomputable section

namespace MinBuyingPMFMarginalProof

private def consEquiv (n : ℕ) : (ℝ × Valuations n) ≃ Valuations (n+1) where
  toFun p := Fin.cons p.1 p.2
  invFun v := (v 0,fun i => v i.succ)
  left_inv p := by rcases p with ⟨t,v⟩;rfl
  right_inv v := by funext i;refine Fin.cases ?_ (fun j => ?_) i <;> simp

private lemma map_fiber (n : ℕ) (w : PMF (Valuations (n+1))) (v : Valuations n) :
    (w.map (fun y : Valuations (n+1) => fun i : Fin n => y i.succ)) v =
      ∑' t : ℝ, w (Fin.cons t v) := by
  classical
  rw [PMF.map_apply,← (consEquiv n).tsum_eq]
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro t
  simp [consEquiv]

private lemma map_fiber_real (n : ℕ) (w : PMF (Valuations (n+1))) (v : Valuations n) :
    ((w.map (fun y : Valuations (n+1) => fun i : Fin n => y i.succ)) v).toReal =
      ∑' t : ℝ, (w (Fin.cons t v)).toReal := by
  rw [map_fiber,ENNReal.tsum_toReal_eq]
  intro t
  exact w.apply_ne_top _

end MinBuyingPMFMarginalProof

theorem solution (n : ℕ) (w : PMF (Valuations (n+1)))
    (hmtp : MTP2 (fun v => (w v).toReal)) :
    MTP2 (fun v : Valuations n =>
      ((w.map (fun y : Valuations (n+1) => fun i : Fin n => y i.succ)) v).toReal) := by
  have hs : Summable (fun v => (w v).toReal) := ENNReal.summable_toReal w.tsum_coe_ne_top
  have hsf : ∀ v : Valuations n, Summable (fun t : ℝ => (w (Fin.cons t v)).toReal) := by
    intro v
    apply hs.comp_injective
    intro s t hst
    exact congrFun hst 0
  have hh := mtp2_summable_marginal n (fun v => (w v).toReal)
    (fun _ => ENNReal.toReal_nonneg) hmtp hsf
  simpa only [MinBuyingPMFMarginalProof.map_fiber_real] using hh
