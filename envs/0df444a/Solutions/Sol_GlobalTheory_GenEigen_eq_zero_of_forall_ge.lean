-- Prove2me | solution 1 for GlobalTheory.GenEigen.eq_zero_of_forall_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:27:03.210297+00:00
-- url     : https://prove2.me/submissions/a9b57416-f8ee-4138-b8ab-cb842861518e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenvectorOfGeneralizedEigenUnramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GenEigen
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.GenEigen
theorem _root_.solution {z : C} (m : ℝ) (h : ∀ k : ℕ, V.Ge (m + k) z) : z = 0 := by
  by_contra hz
  have hne : V.v z ≠ ⊤ := by
    intro ht
    have h1 : V.v (z * z⁻¹) = ⊤ := by rw [V.v.map_mul, ht, top_add]
    rw [mul_inv_cancel₀ hz, V.v.map_one] at h1
    exact WithTop.zero_ne_top h1
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨k, hk⟩ := exists_nat_gt (t - m)
  have := h k
  unfold VF.Ge at this
  rw [← ht] at this
  have : m + k ≤ t := by exact_mod_cast this
  linarith
end GlobalTheory.GenEigen
