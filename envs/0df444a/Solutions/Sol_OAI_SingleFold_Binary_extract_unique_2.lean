-- Prove2me | solution 2 for OAI.SingleFold.Binary.extract_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:55:02.884077+00:00
-- url     : https://prove2.me/submissions/4789e3c4-f38a-4b6c-bf63-758f2b274eb4

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Binary.lean:L94-L106
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Binary.extract_unique. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.NumberTheory.SingleFold.Binary ----
namespace OAI

namespace SingleFold.Binary

lemma extract_unique {B H N s d r : ℕ} (h : N=s*B*H+d*H+r) (hd : d<B) (hr : r<H) :
    r=N%H ∧ d=N/H%B ∧ s=N/H/B := by
  have hH : 0<H := by omega
  have hB : 0<B := by omega
  have he : N=(s*B+d)*H+r := by nlinarith only [h]
  have hq : N/H=s*B+d := by rw [he, Nat.add_comm, Nat.add_mul_div_right _ _ hH, Nat.div_eq_of_lt hr, zero_add]
  have hm : N%H=r := by rw [he,Nat.add_mod]; simp [Nat.mod_eq_of_lt hr]
  rw [hq]
  constructor
  · exact hm.symm
  constructor
  · simp [Nat.mod_eq_of_lt hd]
  · rw [Nat.add_comm,Nat.add_mul_div_right _ _ hB,Nat.div_eq_of_lt hd,zero_add]

end SingleFold.Binary

namespace SingleFold.Compiler.MapSF
end SingleFold.Compiler.MapSF

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g h : (α → ℕ) → ℕ}
end SingleFold.Compiler.ScalarSF

namespace SingleFold.Binary
open Compiler
end SingleFold.Binary

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Binary


theorem solution : type_of% @_root_.OAI.SingleFold.Binary.extract_unique := @_root_.OAI.SingleFold.Binary.extract_unique
