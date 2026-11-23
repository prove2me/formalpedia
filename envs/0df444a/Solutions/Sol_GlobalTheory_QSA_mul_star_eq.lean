-- Prove2me | solution 1 for GlobalTheory.QSA.mul_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:34.254374+00:00
-- url     : https://prove2.me/submissions/9c78cca4-32a0-4618-95ed-d111b0365368

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
theorem _root_.solution {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : x * star x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring
end GlobalTheory.QSA
