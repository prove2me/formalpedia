-- Prove2me | solution 1 for GlobalTheory.FiltrationMultiplicative.coeff_X_mul_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:02:31.075871+00:00
-- url     : https://prove2.me/submissions/0f99e1aa-de14-4e55-a488-2e03373dd322

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_coeff_part

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
variable {O : Type} [CommRing O] [IsLocalRing O]
open Classical
namespace GlobalTheory.FiltrationMultiplicative
theorem _root_.solution {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) (m : Fin a →₀ ℕ) :
    coeff m (X i * part f i) = if IsFirst m i then coeff m f else 0 := by
  rw [X_def, coeff_monomial_mul, one_mul]
  by_cases h : Finsupp.single i 1 ≤ m
  · rw [if_pos h, coeff_part, tsub_add_cancel_of_le h]
  · rw [if_neg h, if_neg]
    intro hf
    apply h
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr hf.1
end GlobalTheory.FiltrationMultiplicative
