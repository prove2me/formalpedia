-- Prove2me | solution 1 for GlobalTheory.LogSubst.coeff_pow_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:27:40.679866+00:00
-- url     : https://prove2.me/submissions/dc077612-6109-4dbe-acd9-70b8cd9ba148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffSubstSumLPowPowMvPowerSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LogSubst
open MvPowerSeries
namespace GlobalTheory.LogSubst
theorem _root_.solution {C σ : Type} [CommRing C] {l : ℕ} (hl : 2 ≤ l)
    {u : MvPowerSeries σ C} (hu : constantCoeff u = 0) {μ : σ →₀ ℕ} {s : ℕ}
    (h : μ.degree ≤ s) : coeff μ (u ^ (l ^ s)) = 0 := by
  apply coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero _ hu)
  have : s < l ^ s := Nat.lt_pow_self (by omega)
  exact_mod_cast lt_of_le_of_lt h this
end GlobalTheory.LogSubst
