-- Prove2me | solution 2 for MinBuying.affiliated_policy_domination
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:09:44.216993+00:00
-- url     : https://prove2.me/submissions/56b6c5af-08d8-4978-a5ff-030996247e2f

import Theorems.Thm_MinBuying_finite_affiliated_coarsening
import Theorems.Thm_MinBuying_pmf_policy_domination

open MeasureTheory Set MinBuying
noncomputable section
namespace MinBuyingFinitePolicyProof

private lemma payment_measurable {n : ℕ} (p : Prices n) : Measurable (payment p) := by
  have ha : Measurable (affordable p) := by
    apply measurable_finset_iff.mpr
    intro i
    apply measurableSet_setOfPred.mp
    simpa [affordable] using
      (measurableSet_le measurable_const (measurable_pi_apply i) :
        MeasurableSet {v : Valuations n | p i ≤ v i})
  exact (measurable_of_countable
    (fun A : Finset (Fin n) => if h : A.Nonempty then A.inf' h p else 0)).comp ha

private lemma revenue_coarsening {n : ℕ} (μ : JointLaw n) (hμ : ValidLaw μ)
    (S : Finset ℝ) (q : ℝ → ℝ) (hq : Measurable q)
    (hcompare : ∀ t ∈ S, ∀ x, 0 ≤ x → (t ≤ q x ↔ t ≤ x))
    (p : Prices n) (hp : ∀ i, p i ∈ S) :
    Revenue (Measure.map (fun v : Valuations n => fun i => q (v i)) μ) p =
      Revenue μ p := by
  have hQ : Measurable (fun v : Valuations n => fun i => q (v i)) :=
    measurable_pi_lambda _ (fun i => hq.comp (measurable_pi_apply i))
  unfold Revenue
  rw [integral_map_of_stronglyMeasurable hQ (payment_measurable p).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hμ.2] with v hv
  have ha : affordable p (fun i => q (v i)) = affordable p v := by
    ext i
    simp only [affordable, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcompare (p i) (hp i) (v i) (hv i)
  simp only [payment, ha]

end MinBuyingFinitePolicyProof

open MinBuyingFinitePolicyProof

theorem solution (n : ℕ) (hn : 0 < n) (μ : JointLaw n)
    (hμ : ValidLaw μ) (hex : Exchangeable μ) (haff : Affiliated μ)
    (p : Prices n) (hp : FeasiblePrices p) :
    ∃ i : Fin n, Revenue μ p ≤ uniformRevenue μ (p i) := by
  classical
  let S : Finset ℝ := Finset.univ.image p
  have hS (i : Fin n) : p i ∈ S :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨q,w,hq,_,hcompare,hw,hwm,hwe,hwmtp⟩ :=
    finite_affiliated_coarsening n μ hμ hex haff S
  obtain ⟨i,hi⟩ := pmf_policy_domination n hn w hwm hwe hwmtp p hp
  have hR : Revenue w.toMeasure p = Revenue μ p := by
    rw [hw]
    exact MinBuyingFinitePolicyProof.revenue_coarsening μ hμ S q hq hcompare p hS
  have hU : uniformRevenue w.toMeasure (p i) = uniformRevenue μ (p i) := by
    unfold uniformRevenue
    rw [hw]
    exact MinBuyingFinitePolicyProof.revenue_coarsening μ hμ S q hq hcompare
      (fun _ => p i) (fun _ => hS i)
  exact ⟨i, by simpa only [hR,hU] using hi⟩
