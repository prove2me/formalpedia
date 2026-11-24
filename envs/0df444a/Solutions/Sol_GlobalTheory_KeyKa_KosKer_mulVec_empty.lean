-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosKer.mulVec_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:31:12.274934+00:00
-- url     : https://prove2.me/submissions/a39d2cf5-fcad-4f9e-bb9e-d9c4641c137d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MulVecCongrDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosKer
open Matrix
variable {g d : ℕ} {N : ℕ → ℕ}
namespace GlobalTheory.KeyKa.KosKer
theorem _root_.solution {R : Type} [CommRing R] (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin (N 0)) :
    (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩) = (∑ i, m i 0 1 *ᵥ (fun k => u (.inl ⟨{i}, k⟩))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single {i}]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos ⟨by simp, by simp⟩]
    simp
    rfl
  · intro J _ hJ
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (fun h => hJ (by simpa using h.2)), zero_mul]
  · simp
end GlobalTheory.KeyKa.KosKer
