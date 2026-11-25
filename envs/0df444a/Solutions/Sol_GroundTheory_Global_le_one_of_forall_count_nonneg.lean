-- Prove2me | solution 1 for GroundTheory.Global.le_one_of_forall_count_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:28:01.026192+00:00
-- url     : https://prove2.me/submissions/1ccd7f47-8418-46e9-b96f-4b69f55233c2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ count K v I) : I ≤ 1 := by
  rw [← finprod_heightOneSpectrum_factorization' (K := K) hI]
  refine finprod_induction (· ≤ 1) le_rfl (fun a b ha hb ↦ ?_) fun v ↦ ?_
  · calc a * b ≤ 1 * b := mul_le_mul_left ha b
      _ = b := one_mul b
      _ ≤ 1 := hb
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
    rw [hn, zpow_natCast, ← coeIdeal_pow]
    exact coeIdeal_le_one
end GroundTheory.Global
