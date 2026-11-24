-- Prove2me | solution 1 for GlobalTheory.QSA.one_mem_H0_weight_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:47:26.174844+00:00
-- url     : https://prove2.me/submissions/045d5fed-a52c-40ee-961c-e66001c4ab76

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
theorem _root_.solution {a b : F} (ε : AF F) : (1 : DA F a b) ∈ H0 ε :=
  ⟨1, by simp [nrm], 1, by simp [nrm], by simp, by ext <;> simp [rat]⟩
end GlobalTheory.QSA
