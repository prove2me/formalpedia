-- Prove2me | solution 1 for GlobalTheory.QSA.nrm_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:33.994843+00:00
-- url     : https://prove2.me/submissions/543d3de6-5c2d-4fd4-b247-1d4476a6bc77

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneMemH0WeightZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Quaternion
open GlobalTheory GlobalTheory.QSA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
variable (F : Type) [Field F] [NumberField F]
variable {F}
namespace GlobalTheory.QSA
theorem _root_.solution {a b : F} (x : ℍ[F, a, b]) : nrm (rat x) = algebraMap F (AF F) (nrm x) := by
  simp [nrm, rat]
end GlobalTheory.QSA
