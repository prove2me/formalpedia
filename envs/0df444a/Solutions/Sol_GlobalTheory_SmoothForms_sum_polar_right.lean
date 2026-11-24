-- Prove2me | solution 1 for GlobalTheory.SmoothForms.sum_polar_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:52:00.846593+00:00
-- url     : https://prove2.me/submissions/9c072e51-812f-4eb8-942c-081d0f6735c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutatorGlGeneratorTensorWordMapMatrixUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory GlobalTheory.SmoothForms
namespace GlobalTheory.SmoothForms
theorem _root_.solution {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (K : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b K J • g J = ∑ p, if K p = a then g (Function.update K p b) else 0 := by
  simp only [polar, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ J : Fin d → Fin n, (K p = a ∧ J p = b ∧ ∀ q, q ≠ p → K q = J q) ↔
      (K p = a ∧ J = Function.update K p b) := fun J => by
    rw [Function.eq_update_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
  simp only [h]
  by_cases hb : K p = a <;> simp [hb]
end GlobalTheory.SmoothForms
