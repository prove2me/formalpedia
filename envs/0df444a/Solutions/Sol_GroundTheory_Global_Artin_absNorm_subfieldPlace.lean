-- Prove2me | solution 1 for GroundTheory.Global.Artin.absNorm_subfieldPlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:31.262522+00:00
-- url     : https://prove2.me/submissions/90fea513-87dd-41b3-90d6-82a37af63bfa

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
theorem _root_.solution [w.asIdeal.LiesOver v.asIdeal] (x : Gal(L/K)) :
    Ideal.absNorm (subfieldPlace H w x).asIdeal = Ideal.absNorm v.asIdeal ^
      frobIndex H (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.asIdeal.inertia Gal(L/K)) x := by
  have := subfieldPlace_liesOver H v w x
  rw [← inertiaDeg_subfieldPlace]
  exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal (subfieldPlace H w x).asIdeal).symm
end GroundTheory.Global.Artin
