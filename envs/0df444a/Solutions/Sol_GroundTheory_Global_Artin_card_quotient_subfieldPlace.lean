-- Prove2me | solution 1 for GroundTheory.Global.Artin.card_quotient_subfieldPlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:05:16.020226+00:00
-- url     : https://prove2.me/submissions/d788ef35-0865-42c4-933a-46f9aeb22fcb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
import Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_inertiaDeg_subfieldPlace

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
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))
namespace GroundTheory.Global.Artin
theorem _root_.solution (x : Gal(L/K)) :
    Nat.card (𝓞 (fixedField H) ⧸ (x • w.asIdeal).under (𝓞 (fixedField H))) =
      Nat.card (𝓞 K ⧸ (x • w.asIdeal).under (𝓞 K)) ^
        frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.asIdeal.inertia Gal(L/K)) x := by
  have hu := inertiaDeg_subfieldPlace H w x
  rw [asIdeal_subfieldPlace] at hu
  have := Ideal.absNorm_pow_inertiaDeg (((x • w.asIdeal).under (𝓞 (fixedField H))).under (𝓞 K))
    ((x • w.asIdeal).under (𝓞 (fixedField H)))
  rw [hu, Ideal.under_under] at this
  rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    ← Ideal.absNorm_apply, this]
end GroundTheory.Global.Artin
