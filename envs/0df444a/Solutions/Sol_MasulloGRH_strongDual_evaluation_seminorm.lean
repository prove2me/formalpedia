-- Prove2me | solution 1 for MasulloGRH.strongDual_evaluation_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:18:08.176008+00:00
-- url     : https://prove2.me/submissions/7164e080-ccc0-4b62-be0a-caccc2d12e34

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Topology Filter Set

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (y : ℕ → E) (hy : Bornology.IsVonNBounded ℂ (Set.range y)) :
    ∃ (q : Seminorm ℂ (StrongDual ℂ E)) (φ : ℕ → StrongDual ℂ (StrongDual ℂ E)),
      Continuous q ∧ (∀ n f, φ n f = f (y n)) ∧
      ∀ n (f : StrongDual ℂ E), ‖f (y n)‖ ≤ q f := by
  classical
  obtain ⟨⟨ι, hι, p, hp⟩, hT⟩ := hE
  have : ContinuousSMul ℂ E := hp.continuousSMul
  let φ : ℕ → StrongDual ℂ (StrongDual ℂ E) := fun n =>
    { toLinearMap := (topDualPairing ℂ E).flip (y n)
      cont := continuous_eval_const (y n) }
  let P : ℕ → Seminorm ℂ (StrongDual ℂ E) := fun n => (φ n).toSeminorm
  have hN : ∀ᶠ f : StrongDual ℂ E in 𝓝 0, ∀ n, P n f ≤ 1 := by
    have h := ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hy
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
    filter_upwards [h] with f hf n
    exact (show ‖f (y n)‖ < 1 from by simpa using hf (Set.mem_range_self n)).le
  have hb : BddAbove (Set.range P) :=
    Seminorm.bddAbove_of_absorbent (absorbent_nhds_zero hN)
      (fun f hf => ⟨1, Set.forall_mem_range.mpr hf⟩)
  refine ⟨⨆ n, P n, φ, ?_, fun _ _ => rfl, ?_⟩
  · apply Seminorm.continuous' (r := 1)
    filter_upwards [hN] with f hf
    simpa only [Seminorm.closedBall_iSup hb _ zero_lt_one, Set.mem_iInter,
      Seminorm.mem_closedBall_zero] using hf
  · intro n f
    change P n f ≤ (⨆ k, P k) f
    rw [Seminorm.iSup_apply hb]
    exact le_ciSup (Seminorm.bddAbove_range_iff.mp hb f) n
