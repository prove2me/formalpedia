-- Prove2me | solution 1 for GlobalTheory.DiffDecay.Tame.iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:22:04.732804+00:00
-- url     : https://prove2.me/submissions/afbbb47c-fcc7-4680-aa0a-ef1f062676a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousSmulSemi
import Theorems.Thm_GlobalTheory_DiffDecay_continuous_smul_semi

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
theorem _root_.solution {R : W → E →ₗ[ℂ] E} (h : Tame R) (j : ℕ) (p : Seminorm ℂ E) (hp : Continuous p) :
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ u, ‖u‖ ≤ 1 → ∀ f, p (((R u - 1) ^ j) f) ≤ ‖u‖ ^ j * q f := by
  induction j with
  | zero => exact ⟨p, hp, fun u _ f => by simp⟩
  | succ j ih =>
    obtain ⟨q, hq, hb⟩ := ih
    obtain ⟨q₁, M, hq₁, hb₁⟩ := h q hq
    obtain ⟨q₂, hq₂, e₂⟩ := continuous_smul_semi (2 ^ M) q₁ hq₁
    refine ⟨q₂, hq₂, fun u hu f => ?_⟩
    rw [pow_succ, Module.End.mul_apply]
    refine (hb u hu _).trans ?_
    rw [pow_succ, mul_assoc, e₂, abs_of_nonneg (by positivity)]
    gcongr
    rw [LinearMap.sub_apply, Module.End.one_apply, ← mul_assoc]
    refine (hb₁ u f).trans ?_
    gcongr
    linarith
end Tame
end GlobalTheory.DiffDecay
