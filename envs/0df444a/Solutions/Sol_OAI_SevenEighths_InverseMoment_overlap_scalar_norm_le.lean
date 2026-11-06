-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.overlap_scalar_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:15.568671+00:00
-- url     : https://prove2.me/submissions/18443e8f-83bb-4326-aa0f-6410e92eb3b9

import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Overlap
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open UniqueFactorizationMonoid

theorem solution {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖z ^ 2‖ ≤ 1 := by
  rw [norm_pow]
  simpa using pow_le_pow_left₀ (norm_nonneg z) hz 2
