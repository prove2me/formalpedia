-- Prove2me | solution 1 for GroundTheory.Global.sq_rationalPrimeUnder_le_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:51.356467+00:00
-- url     : https://prove2.me/submissions/c5fad20e-47be-4c75-9f11-2994a0c9fd48

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Theorems.Thm_GroundTheory_Global_rationalPrimeUnder_prime
import Theorems.Thm_GroundTheory_Global_absNorm_eq_rationalPrimeUnder_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution {w : HeightOneSpectrum (𝓞 L)}
    (hw : ¬ (Ideal.absNorm w.asIdeal).Prime) :
    rationalPrimeUnder w ^ 2 ≤ Ideal.absNorm w.asIdeal := by
  have hf := Ideal.inertiaDeg_pos w.asIdeal ℤ
  rw [absNorm_eq_rationalPrimeUnder_pow] at hw ⊢
  have hf1 : w.asIdeal.inertiaDeg ℤ ≠ 1 := by
    intro h
    rw [h, pow_one] at hw
    exact hw (rationalPrimeUnder_prime w)
  exact Nat.pow_le_pow_right (rationalPrimeUnder_prime w).pos (by omega)
end GroundTheory.Global
