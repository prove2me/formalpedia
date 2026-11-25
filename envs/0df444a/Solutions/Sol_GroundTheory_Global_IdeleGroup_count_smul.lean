-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.count_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:28.967285+00:00
-- url     : https://prove2.me/submissions/765f4845-9085-4684-94b0-e7c9c015c712

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
open GroundTheory.Global.IdeleGroup
local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (s : IdeleGroup K) (I : 𝓘) :
    count K v ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) =
      ord v s + count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [smul_def, Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
    count_toFractionalIdeal]
end GroundTheory.Global.IdeleGroup
