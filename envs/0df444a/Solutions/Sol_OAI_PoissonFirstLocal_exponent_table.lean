-- Prove2me | solution 1 for OAI.PoissonFirstLocal.exponent_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:34:37.432847+00:00
-- url     : https://prove2.me/submissions/3d5d4c07-2ea9-4856-9b6b-4504c8ce22c9

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.PoissonFirstLocal
open scoped Classical
namespace OAI.PoissonFirstLocal
theorem _root_.solution (parityBit ε₁ ε₂ : Bool) :
    totalExp₁ parityBit ε₁ ε₂ % 6 = (if retained parityBit ε₁ ε₂ then 4 else 0) ∧
    totalExp₂ parityBit ε₁ ε₂ % 6 = (if retained parityBit ε₁ ε₂ then 4 else 0) := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide
end OAI.PoissonFirstLocal
