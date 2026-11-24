-- Prove2me | solution 1 for GlobalTheory.SimAlg.form_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:10.89478+00:00
-- url     : https://prove2.me/submissions/99d4e74a-307c-499f-b235-f99b6d5a3a09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
import Theorems.Thm_GlobalTheory_SimAlg_form_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg
namespace GlobalTheory.SimAlg
theorem _root_.solution (g : ℕ → ℕ → ℤ) (hg : ∀ i j, g i j = g j i)
    (f h : ℂ[X]) : form g f h = form g h f := by
  set d := max f.natDegree h.natDegree + 1
  rw [form_sum g d f h (by omega) (by omega), form_sum g d h f (by omega) (by omega),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hg]; ring
end GlobalTheory.SimAlg
