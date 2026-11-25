-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.IsArithFrobAt.apply_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:45.935811+00:00
-- url     : https://prove2.me/submissions/0cd9f535-0b18-4d30-b669-ecea78c01e46

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Theorems.Thm_GroundTheory_Global_Cyclotomic_card_quotient_under
import Theorems.Thm_GroundTheory_Global_Cyclotomic_natCast_notMem_of_not_dvd

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
omit hp [IsCyclotomicExtension {m} ℚ K] [P.IsPrime]
namespace GroundTheory.Global.Cyclotomic
namespace IsArithFrobAt
theorem _root_.solution (hm : ¬ p ∣ m) {σ : Gal(K/ℚ)}
    (hσ : IsArithFrobAt ℤ σ P) {x : K} (hx : x ^ m = 1) : σ x = x ^ p := by
  have hxi : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne m), ?_⟩
    simp [hx]
  let y : 𝓞 K := ⟨x, hxi⟩
  have hy : y ^ m = 1 := by
    apply RingOfIntegers.ext
    exact hx
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ hy
    (natCast_notMem_of_not_dvd p K P hm)
  rw [card_quotient_under p K P] at h
  exact congrArg (fun z : 𝓞 K => (z : K)) h
end IsArithFrobAt
end GroundTheory.Global.Cyclotomic
