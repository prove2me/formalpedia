-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.last_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:58.201558+00:00
-- url     : https://prove2.me/submissions/eabdf9b0-5967-4a5a-94e9-342cc9fbd9f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Theorems.Thm_GlobalTheory_UnipotentBorder_udl_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
namespace GlobalTheory.UnipotentBorder
theorem _root_.solution {n : ℕ} {U L : Matrix (Fin (n+1)) (Fin (n+1)) O} (hL : IsLU L)
    (D : Fin (n+1) → Oˣ) (i : Fin (n+1)) :
    (U * diagonal (fun k => (D k : O)) * L) i (Fin.last n)
      = U i (Fin.last n) * (D (Fin.last n) : O) := by
  simp only [udl_apply]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [(hL _ _).2 rfl, mul_one]
  · intro k _ hk
    rw [(hL k (Fin.last n)).1 (lt_of_le_of_ne (Fin.le_last k) hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end GlobalTheory.UnipotentBorder
