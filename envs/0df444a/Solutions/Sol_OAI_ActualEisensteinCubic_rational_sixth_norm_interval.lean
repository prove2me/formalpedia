-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_sixth_norm_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:50:50.179688+00:00
-- url     : https://prove2.me/submissions/194e5a6c-e39b-4bc0-a921-58b06f244732

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_qNat_pow

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
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open OAI.ActualEisensteinCubic
open ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (L r R : ℕ) (hr : r.Prime) (hL : L ≤ r) (hR : r ≤ R) :
    L ^ 12 ≤ qNat ((r : O) ^ 6) ∧
      qNat ((r : O) ^ 6) ≤ R ^ 12 := by
  rw [rational_qNat_pow r 6 hr.ne_zero]
  have hpow : (r ^ 2) ^ 6 = r ^ 12 := by ring
  rw [hpow]
  exact ⟨Nat.pow_le_pow_left hL 12, Nat.pow_le_pow_left hR 12⟩
end OAI.ActualEisensteinCubic
