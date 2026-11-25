-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.localMul_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:45.220668+00:00
-- url     : https://prove2.me/submissions/615678f2-34a5-4102-b1a7-b4ef01b3de1c

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
theorem _root_.solution (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K))
    (y : v.adicCompletion K) :
    localMul s I v (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((finiteProj v s : v.adicCompletion K) * y) :=
  rfl
end GroundTheory.Global.IdeleGroup
