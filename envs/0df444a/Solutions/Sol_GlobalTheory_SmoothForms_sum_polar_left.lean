-- Prove2me | solution 1 for GlobalTheory.SmoothForms.sum_polar_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:51:59.878319+00:00
-- url     : https://prove2.me/submissions/d525270e-7d28-4838-9c4d-4184deaad2c7

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
theorem _root_.solution {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (I : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b J I • g J = ∑ p, if b = I p then g (Function.update I p a) else 0 := by
  simp only [polar, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ J : Fin d → Fin n, (J p = a ∧ I p = b ∧ ∀ q, q ≠ p → J q = I q) ↔
      (b = I p ∧ J = Function.update I p a) := fun J => by
    rw [Function.eq_update_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2.symm, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1.symm, h3⟩
  simp only [h]
  by_cases hb : b = I p <;> simp [hb]
end GlobalTheory.SmoothForms
