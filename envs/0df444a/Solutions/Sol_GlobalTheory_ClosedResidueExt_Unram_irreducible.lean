-- Prove2me | solution 1 for GlobalTheory.ClosedResidueExt.Unram.irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:43.408423+00:00
-- url     : https://prove2.me/submissions/82a206b9-2e9a-4248-89d5-55fb50706b77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
import Theorems.Thm_GlobalTheory_ClosedResidueExt_Unram_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedResidueExt
open Polynomial IsLocalRing
variable {W Ω : Type} [CommRing W] [Field Ω] [Algebra W Ω]
namespace GlobalTheory.ClosedResidueExt
namespace Unram
theorem _root_.solution {π : W} {R : Subalgebra W Ω} (h : Unram π R)
    (h0 : algebraMap W Ω π ≠ 0) : Irreducible (algebraMap W R π) := by
  have h0' : algebraMap W R π ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  have hnu : ¬ IsUnit (algebraMap W R π) := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv' : algebraMap W Ω π * (v : Ω) = 1 := congrArg Subtype.val hv
    exact h.2.1 (eq_inv_of_mul_eq_one_right hv' ▸ v.2)
  refine ⟨hnu, fun a b hab => ?_⟩
  have ha : a ≠ 0 := by
    rintro rfl
    exact h0' (by simpa using hab)
  have hb : b ≠ 0 := by
    rintro rfl
    exact h0' (by simpa using hab)
  obtain ⟨n, u, rfl⟩ := h.factor a ha
  obtain ⟨m, v, rfl⟩ := h.factor b hb
  rcases n with _ | n
  · left; simp
  rcases m with _ | m
  · right; simp
  exfalso
  refine hnu (IsUnit.of_mul_eq_one (algebraMap W R π ^ (n + m) * u * v) ?_)
  refine mul_left_cancel₀ h0' ?_
  rw [mul_one]
  conv_rhs => rw [hab]
  ring
end Unram
end GlobalTheory.ClosedResidueExt
