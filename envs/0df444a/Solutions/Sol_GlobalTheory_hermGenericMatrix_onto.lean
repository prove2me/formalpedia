-- Prove2me | solution 1 for GlobalTheory.hermGenericMatrix_onto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:59.755487+00:00
-- url     : https://prove2.me/submissions/6786e061-0202-40f1-904f-25f67e0ef542

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwo
import Theorems.Thm_GlobalTheory_hermGenericMatrix_map_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial Matrix
namespace GlobalTheory
theorem _root_.solution {κ : Type} [Field κ] [CharZero κ] (n : ℕ) (e : κ) (he : e ≠ 0)
    (y : Matrix (Fin n) (Fin n) κ) :
    ∃ u : Fin n × Fin n → κ, (hermGenericMatrix n e).map (MvPolynomial.eval u) = y := by
  refine ⟨fun p => (y p.1 p.2 + y p.2 p.1) / 4 + (y p.1 p.2 - y p.2 p.1) / (4 * e), ?_⟩
  rw [hermGenericMatrix_map_eval]
  ext i j
  simp only [Matrix.of_apply]
  field_simp
  ring
end GlobalTheory
