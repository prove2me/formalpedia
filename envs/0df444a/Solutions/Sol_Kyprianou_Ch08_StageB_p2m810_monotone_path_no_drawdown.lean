-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_monotone_path_no_drawdown
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:32:06.660488+00:00
-- url     : https://prove2.me/submissions/0cd06b31-4fd1-4d94-9385-39a43c0e1a99


import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Zero slope path reduction. -/
theorem solution :
    ∀ (Ω : Type) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (x a : ℝ),
      X 0 ω = 0 → Monotone (fun t : ℝ≥0 => X t ω) →
      0 ≤ x → x ≤ a → reflectedSupExit X x a ω = ⊤ := by
  intro Ω X ω x a h0 hm hx hxa
  unfold reflectedSupExit tauPlus
  have he : {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, 0 < u ∧
      (u : WithTop ℝ≥0) = t ∧ a < reflectAtSup X x u ω} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro t ⟨u,hu,rfl,hbad⟩
    have hX : 0 ≤ X u ω := by simpa [h0] using hm (show (0 : ℝ≥0) ≤ u by positivity)
    have hS : runningSup X u ω ≤ X u ω := by
      unfold runningSup
      exact csSup_le ⟨X u ω, u, le_rfl, rfl⟩ (by
        rintro z ⟨v,hv,rfl⟩
        exact hm hv)
    unfold reflectAtSup at hbad
    have hM : max x (runningSup X u ω) ≤ a + X u ω :=
      max_le (by linarith) (by linarith)
    linarith
  rw [he,sInf_empty]
