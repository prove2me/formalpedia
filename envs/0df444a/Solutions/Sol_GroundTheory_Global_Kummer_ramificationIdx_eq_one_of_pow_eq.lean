-- Prove2me | solution 1 for GroundTheory.Global.Kummer.ramificationIdx_eq_one_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:45:29.359808+00:00
-- url     : https://prove2.me/submissions/e29ef366-a5d8-44f7-bb31-501f607714aa

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Unramified
import Theorems.Thm_GroundTheory_Global_Kummer_isUnramifiedAt_of_pow_eq

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
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Global.Kummer
variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [Field M] [NumberField M] [Algebra K M]
namespace GroundTheory.Global.Kummer
theorem _root_.solution {n : ℕ} (a : Kˣ) {α : M}
    (hα : α ^ n = algebraMap K M a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)))
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    P.ramificationIdx (𝓞 K) = 1 := by
  have := isUnramifiedAt_of_pow_eq a hα hgen v hnv hav P
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
end GroundTheory.Global.Kummer
