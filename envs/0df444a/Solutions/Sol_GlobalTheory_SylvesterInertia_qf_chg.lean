-- Prove2me | solution 1 for GlobalTheory.SylvesterInertia.qf_chg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:07.780556+00:00
-- url     : https://prove2.me/submissions/ee771611-2eac-4eb2-837a-02122c37992c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSignatureFstUniqueSylvester
import Theorems.Thm_GlobalTheory_SylvesterInertia_chg_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SylvesterInertia
open Matrix Module
open scoped ComplexOrder
variable {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.SylvesterInertia
theorem _root_.solution {a b : ℕ} (J : Matrix n n ℂ) (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ)
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b) (y : Fin a ⊕ Fin b → ℂ) :
    qf J (chg e P y) = star y ⬝ᵥ Formalism.UG.Jpq a b *ᵥ y := by
  set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ := (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ)
  have hc : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by ext i j; rfl
  rw [← h, hc]
  set w := M *ᵥ y
  have h1 : J *ᵥ (w ∘ e) = (J.reindex e e *ᵥ w) ∘ e := by
    rw [reindex_apply, submatrix_mulVec_equiv]
    ext i; simp [Function.comp_def]
  have h2 : qf J (chg e P y) = star w ⬝ᵥ (J.reindex e e *ᵥ w) := by
    rw [qf, chg_apply, h1]
    simp only [dotProduct, Function.comp_apply, Pi.star_apply]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [h2]
  simp only [w, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, Matrix.mul_assoc]
end GlobalTheory.SylvesterInertia
