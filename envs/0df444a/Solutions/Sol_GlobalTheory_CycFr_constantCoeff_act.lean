-- Prove2me | solution 1 for GlobalTheory.CycFr.constantCoeff_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:30:14.516347+00:00
-- url     : https://prove2.me/submissions/350480da-8f30-4c7b-97c6-e5dca5c90d51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_constantCoeff_algHom
import Theorems.Thm_GlobalTheory_CycFr_X_dvd_act_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution (c : ℤ_[l]) (a : O⟦X⟧) : constantCoeff (_root_.GlobalTheory.CycFr.act O c a) = constantCoeff a :=
  _root_.GlobalTheory.CycFr.constantCoeff_algHom _ (_root_.GlobalTheory.CycFr.X_dvd_act_X c) a
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
