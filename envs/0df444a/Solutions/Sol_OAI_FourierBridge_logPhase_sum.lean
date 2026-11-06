-- Prove2me | solution 1 for OAI.FourierBridge.logPhase_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:10.936585+00:00
-- url     : https://prove2.me/submissions/33977942-cd3f-4979-8363-8b7491f6fa3c

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_logPhase_add
import Theorems.Thm_OAI_FourierBridge_logPhase_zero

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge
namespace OAI.FourierBridge
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ℝ) (z : ι → ℝ) :
    logPhase t (∑ i ∈ s, z i) = ∏ i ∈ s, logPhase t (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logPhase_zero]
  | @insert i s hi ih => simp [hi, logPhase_add, ih]
end OAI.FourierBridge
