-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.last_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:58.310794+00:00
-- url     : https://prove2.me/submissions/63355195-6524-4d51-a46f-f28ea45f9385

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
theorem _root_.solution {n : ℕ} {U L : Matrix (Fin (n+1)) (Fin (n+1)) O} (hU : IsUU U)
    (D : Fin (n+1) → Oˣ) (j : Fin (n+1)) :
    (U * diagonal (fun k => (D k : O)) * L) (Fin.last n) j
      = (D (Fin.last n) : O) * L (Fin.last n) j := by
  simp only [udl_apply]
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [(hU _ _).2 rfl, one_mul]
  · intro k _ hk
    rw [(hU (Fin.last n) k).1 (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end GlobalTheory.UnipotentBorder
