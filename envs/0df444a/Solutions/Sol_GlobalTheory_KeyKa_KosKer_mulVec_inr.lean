-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosKer.mulVec_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:31:16.359799+00:00
-- url     : https://prove2.me/submissions/f3892183-5343-4a22-8940-d165f4d40f7d

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
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin d) :
    (kosD m ev *ᵥ u) (.inr a) = (ev 0 *ᵥ (fun k => u (.inl ⟨∅, k⟩))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_sigma, Finset.sum_eq_single ∅]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos rfl]
    rfl
  · intro J _ hJ
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg hJ, zero_mul]
  · simp
end GlobalTheory.KeyKa.KosKer
