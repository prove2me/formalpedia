-- Prove2me | solution 1 for GlobalTheory.linFormElim_X_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:53.573656+00:00
-- url     : https://prove2.me/submissions/915d7e87-e4b3-4531-8d54-98b596446cc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_linFormEquiv_symm_X_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
namespace GlobalTheory
theorem _root_.solution {S : Set ι} {i : ι} (hi : i ∈ S) [DecidableEq J] :
    linFormElim u hu S (X (i, j₀)) = -∑ j : {j : J // j ≠ j₀},
      C ((↑hu.unit⁻¹ : R) * u j) * X ⟨(i, j.1), fun h => j.2 h.2⟩ := by
  rw [linFormElim_apply, linFormEquiv_symm_X_of_mem u hu hi, linForm_eq _ i j₀, map_add, map_mul,
    killVars_X_of_mem (by exact ⟨hi, rfl⟩), mul_zero, zero_add, map_sum,
    Finset.sum_subtype (p := fun j => j ≠ j₀) _ (by simp), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, killVars_C, killVars_X_of_notMem (fun h => j.2 h.2), linFormInvCoeff, if_neg j.2,
    C_neg, neg_mul]
end GlobalTheory
