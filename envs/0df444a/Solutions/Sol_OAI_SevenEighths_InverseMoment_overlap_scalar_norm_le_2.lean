-- Prove2me | solution 2 for OAI.SevenEighths.InverseMoment.overlap_scalar_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:15.136249+00:00
-- url     : https://prove2.me/submissions/b48936eb-99a2-4122-a9dc-68f4ada86405

import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Overlap

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open UniqueFactorizationMonoid
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖z ^ 2‖ ≤ 1 := by
  rw [norm_pow]
  simpa using pow_le_pow_left₀ (norm_nonneg z) hz 2
end OAI.SevenEighths.InverseMoment
