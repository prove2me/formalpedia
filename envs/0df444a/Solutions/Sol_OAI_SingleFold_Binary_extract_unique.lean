-- Prove2me | solution 1 for OAI.SingleFold.Binary.extract_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:10:11.941864+00:00
-- url     : https://prove2.me/submissions/0a101bba-c189-45e2-ac40-aff41067fa68

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

open OAI OAI.SingleFold OAI.SingleFold.Binary


theorem solution {B H N s d r : ℕ} (h : N=s*B*H+d*H+r) (hd : d<B) (hr : r<H) :
    r=N%H ∧ d=N/H%B ∧ s=N/H/B := by
  have hH : 0 < H := by omega
  have hB : 0 < B := by omega
  have h1 : N = (s*B+d)*H + r := by rw [h]; ring
  have hr' : N % H = r := by rw [h1, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have hq : N / H = s*B+d := by
    rw [h1, Nat.mul_comm, Nat.mul_add_div hH, Nat.div_eq_of_lt hr, add_zero]
  refine ⟨hr'.symm, ?_, ?_⟩
  · rw [hq, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hd]
  · rw [hq, Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt hd, add_zero]

