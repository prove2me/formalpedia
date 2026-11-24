-- Prove2me | solution 1 for GlobalTheory.TestLat.Model.isLattice_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:55.117639+00:00
-- url     : https://prove2.me/submissions/f8a7bcc4-d760-4e66-9b7a-bb74a9ca892d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.TestLat GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
namespace GlobalTheory.TestLat.Model
theorem _root_.solution : Submodule.IsLattice K (stdLat K n) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [stdLat, Submodule.span_span_of_tower]
    exact (Pi.basisFun K (Fin n)).span_eq
end GlobalTheory.TestLat.Model
