-- Prove2me | solution 1 for GroundTheory.Global.quotientEquivLocalQuotients_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:42.936823+00:00
-- url     : https://prove2.me/submissions/bd8cdbec-c1df-4cc9-89e1-555cc524d9a9

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
namespace GroundTheory.Global
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K) :
    quotientEquivLocalQuotients hI (Submodule.Quotient.mk x) = toLocalQuotients hI x :=
  rfl
end GroundTheory.Global
