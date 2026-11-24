-- Prove2me | solution 1 for GlobalTheory.IdealPowerCoefficients.mem_pow_iff_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:48.497232+00:00
-- url     : https://prove2.me/submissions/bad5e1c6-91ae-438e-aa00-39a2f79d545b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_mem_coeffIdeal
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_pow_le_coeffIdeal
import Theorems.Thm_GlobalTheory_IdealPowerCoefficients_mem_pow_of_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IdealPowerCoefficients
open MvPowerSeries Finsupp
namespace GlobalTheory.IdealPowerCoefficients
theorem _root_.solution {R : Type u_1} [CommRing R] (I : Ideal R) {κ : Type u_2} [Finite κ] (n : ℕ)
    (f : MvPowerSeries κ R) :
    f ∈ (Ideal.map MvPowerSeries.C I ⊔ Ideal.span (Set.range MvPowerSeries.X)) ^ n ↔
      ∀ (e : κ →₀ ℕ), (MvPowerSeries.coeff e : MvPowerSeries κ R → R) f ∈
        I ^ (n - (Finsupp.degree : (κ →₀ ℕ) → ℕ) e) :=
  ⟨fun h => mem_coeffIdeal.1 (pow_le_coeffIdeal I n h), mem_pow_of_coeff I n f⟩
end GlobalTheory.IdealPowerCoefficients
