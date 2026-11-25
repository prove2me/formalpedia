-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.quotientEquivLocalQuotients_smulQuotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:47.835837+00:00
-- url     : https://prove2.me/submissions/d5e76910-75ca-4f8b-8989-b0d5e137540c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleActionQuotient

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
theorem _root_.solution (s : IdeleGroup K) (I : 𝓘)
    (q : K ⧸ ((I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    quotientEquivLocalQuotients (s • I).ne_zero (smulQuotient s I q) =
      DFinsupp.mapRange.linearEquiv (localMul s I) (quotientEquivLocalQuotients I.ne_zero q) := by
  rw [smulQuotient, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
end GroundTheory.Global.IdeleGroup
