-- Prove2me | solution 1 for GlobalTheory.mem_germIdeal_pow_iff_le_order
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:36.186977+00:00
-- url     : https://prove2.me/submissions/65cb4e5e-110c-4d70-a982-36a67e991518

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finsupp
open MvPowerSeries
variable {R σ Λ M : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution [Finite σ] {n : ℕ} {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ n ↔ (n : ℕ∞) ≤ g.order := by
  rw [mem_germIdeal_pow_iff]
  exact ⟨nat_le_order, fun h d hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h)⟩
end GlobalTheory
