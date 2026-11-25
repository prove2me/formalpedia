-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.natCast_notMem_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:02.845515+00:00
-- url     : https://prove2.me/submissions/a573d3ed-7612-4e09-996d-67475600a49e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]
variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
omit [NeZero m] hp [NumberField K] [IsCyclotomicExtension {m} ℚ K] [P.IsPrime]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (hm : ¬ p ∣ m) : ((m : ℕ) : 𝓞 K) ∉ P := by
  intro h
  have : ((m : ℤ)) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using h
  rw [← Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)}), Ideal.mem_span_singleton] at this
  exact hm (Int.natCast_dvd_natCast.mp this)
end GroundTheory.Global.Cyclotomic
