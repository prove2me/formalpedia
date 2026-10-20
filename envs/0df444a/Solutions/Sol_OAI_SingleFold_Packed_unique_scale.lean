-- Prove2me | solution 1 for OAI.SingleFold.Packed.unique_scale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:08:48.441052+00:00
-- url     : https://prove2.me/submissions/9835aca6-3d0d-49bf-ae30-1a3ab1b479b6

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed

open OAI OAI.SingleFold OAI.SingleFold.Packed


theorem solution {L : ℕ} (hL : 0 < L) : ∃! w : ℕ, 2*L < 2^w ∧ 2^w ≤ 4*L := by
  refine ⟨Nat.log 2 L + 2, ⟨?_, ?_⟩, ?_⟩
  · have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) L
    rw [pow_succ] at this ⊢; omega
  · have := Nat.pow_log_le_self 2 hL.ne'
    rw [pow_succ, pow_succ]; omega
  · rintro w ⟨h1, h2⟩
    have a := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) L
    have b := Nat.pow_log_le_self 2 hL.ne'
    have c1 : 2^w < 2^(Nat.log 2 L + 3) := by rw [pow_succ, pow_succ, pow_succ] at *; omega
    have c2 : 2^(Nat.log 2 L + 1) < 2^w := by rw [pow_succ] at *; omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2:ℕ))).1 c1
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2:ℕ))).1 c2
    omega

