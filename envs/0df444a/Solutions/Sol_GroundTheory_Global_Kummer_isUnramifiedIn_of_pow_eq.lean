-- Prove2me | solution 1 for GroundTheory.Global.Kummer.isUnramifiedIn_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:59.810567+00:00
-- url     : https://prove2.me/submissions/13351322-9233-44db-a2a9-8f57f37e2deb

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
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) :
    Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal := fun P _ _ =>
  isUnramifiedAt_of_pow_eq a hα hgen v hnv hav P
end GroundTheory.Global.Kummer
