-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_record_survival_path_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:31:56.610796+00:00
-- url     : https://prove2.me/submissions/167b90f1-dbbd-42f8-a57e-847d167d2452


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Zero slope path reduction. -/
theorem solution :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (a : ℝ),
      0 ≤ a → X 0 ω = 0 →
      (∀ T : ℝ≥0, BddAbove {z : ℝ | ∃ s : ℝ≥0, s ≤ T ∧ z = X s ω}) →
      (∀ n : ℕ, tauPlus X ((n : ℝ)+1) ω < reflectedSupExit X 0 a ω) →
      ∀ t : ℝ≥0, -a ≤ X t ω := by
  intro Ω X ω a ha h0 hb hs t
  by_contra! hn
  have ht : 0 < t := by
    by_contra! h
    have ht0 : t = 0 := le_antisymm h (show (0 : ℝ≥0) ≤ t by positivity)
    subst t
    rw [h0] at hn
    linarith
  have hR : reflectedSupExit X 0 a ω ≤ (t : WithTop ℝ≥0) := by
    unfold reflectedSupExit tauPlus
    exact sInf_le ⟨t, ht, rfl, by
      unfold reflectAtSup
      linarith [le_max_left (0:ℝ) (runningSup X t ω)]⟩
  obtain ⟨M,hM⟩ := hb t
  obtain ⟨n,hnM⟩ := exists_nat_gt M
  have hU : (t : WithTop ℝ≥0) ≤ tauPlus X ((n:ℝ)+1) ω := by
    unfold tauPlus
    apply le_sInf
    rintro _ ⟨u,hu,rfl,hcross⟩
    by_contra! hlt
    have hu' := WithTop.coe_lt_coe.mp hlt
    have hm := hM (show X u ω ∈ {z : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ z = X s ω}
      from ⟨u,hu'.le,rfl⟩)
    linarith
  exact (not_lt_of_ge (hR.trans hU)) (hs n)
