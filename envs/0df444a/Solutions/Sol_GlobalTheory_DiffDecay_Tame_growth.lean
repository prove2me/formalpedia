-- Prove2me | solution 1 for GlobalTheory.DiffDecay.Tame.growth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:47.946325+00:00
-- url     : https://prove2.me/submissions/c7659ba0-78d1-4ca8-abdb-2da9fd935aaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.DiffDecay
variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {W : Type} [SeminormedAddCommGroup W]
namespace GlobalTheory.DiffDecay
namespace Tame
theorem _root_.solution {R : W → E →ₗ[ℂ] E} (h : Tame R) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ (q : Seminorm ℂ E) (M : ℕ), Continuous q ∧ ∀ w f, p (R w f) ≤ (1 + ‖w‖) ^ M * q f := by
  obtain ⟨q, M, hq, hb⟩ := h p hp
  refine ⟨p + q, M + 1, (hp.add hq : Continuous fun f => p f + q f), fun w f => ?_⟩
  have h1 : p (R w f) ≤ p (R w f - f) + p f := by
    simpa using map_add_le_add p (R w f - f) f
  have h2 := hb w f
  have h3 : 1 ≤ (1 + ‖w‖) ^ M := one_le_pow₀ (by linarith [norm_nonneg w])
  have hp0 := apply_nonneg p f
  have hq0 := apply_nonneg q f
  have hw := norm_nonneg w
  rw [Seminorm.add_apply, pow_succ]
  nlinarith [mul_nonneg hw hp0, mul_nonneg (mul_nonneg hw hp0) (sub_nonneg.2 h3), mul_nonneg hp0 (sub_nonneg.2 h3),
    mul_nonneg hq0 (sub_nonneg.2 h3)]
end Tame
end GlobalTheory.DiffDecay
