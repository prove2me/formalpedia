-- Prove2me | solution 1 for GordanGenProof.mem_hcone_stdIneq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:32.765622+00:00
-- url     : https://prove2.me/submissions/20ef3359-3906-4960-95a8-e85efdf90042

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
namespace GordanGenProof
open Finset
private theorem rat_dotProduct_zero_right {n : ℕ} (a : Fin n → ℚ) : a ⬝ᵥ (0 : Fin n → ℚ) = 0 := by
  show ∑ j, a j * (0 : Fin n → ℚ) j = 0
  simp
end GordanGenProof
end

set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset
namespace GordanGenProof
theorem _root_.solution (n : ℕ) (x : Fin n → ℚ) : x ∈ hcone (stdIneq n) id ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have h1 : 0 ≤ (Pi.single i (1 : ℚ) : Fin n → ℚ) ⬝ᵥ x :=
      h (Pi.single i 1) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have h2 : 0 ≤ (-(Pi.single i (1 : ℚ)) : Fin n → ℚ) ⬝ᵥ x :=
      h (-(Pi.single i 1)) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    have e1 : (Pi.single i (1 : ℚ) : Fin n → ℚ) ⬝ᵥ x = x i := by
      show ∑ j, (Pi.single i (1 : ℚ) : Fin n → ℚ) j * x j = x i
      simp [Pi.single_apply]
    have e2 : (-(Pi.single i (1 : ℚ)) : Fin n → ℚ) ⬝ᵥ x = -x i := by
      rw [← e1]
      show ∑ j, (-(Pi.single i (1 : ℚ)) : Fin n → ℚ) j * x j = -∑ j, (Pi.single i (1 : ℚ) : Fin n → ℚ) j * x j
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => neg_mul _ _
    rw [e1] at h1
    rw [e2] at h2
    show x i = 0
    exact le_antisymm (by linarith) h1
  · rintro rfl
    show ∀ a ∈ stdIneq n, 0 ≤ id a ⬝ᵥ (0 : Fin n → ℚ)
    intro a _
    exact le_of_eq (rat_dotProduct_zero_right _).symm
end GordanGenProof
