-- Prove2me | solution 1 for OAI.SevenEighths.Probe.principalScalar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:48.935559+00:00
-- url     : https://prove2.me/submissions/0c4387eb-711c-4cb7-826f-7a59e134dffe

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Basic

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Probe
noncomputable section
namespace OAI.SevenEighths.Probe
theorem _root_.solution {ι : Type*} (slots : Finset ι)
    {Z ℓ : ℝ} {S : ι → ℝ} (hZ : 0 < Z)
    (hS : ∀ i ∈ slots, 0 < S i) : principalScalar slots Z ℓ S ≠ 0 := by
  unfold principalScalar
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ne_of_gt (Real.rpow_pos_of_pos hZ _))
  · exact ne_of_gt (Finset.prod_pos hS)
end OAI.SevenEighths.Probe
