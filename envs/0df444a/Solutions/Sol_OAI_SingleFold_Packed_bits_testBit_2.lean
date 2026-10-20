-- Prove2me | solution 2 for OAI.SingleFold.Packed.bits_testBit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:57:42.003818+00:00
-- url     : https://prove2.me/submissions/dee56429-b2e2-47bc-a094-a787931b2a8f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Packed.lean:L15-L27
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Packed.bits_testBit. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed

-- ---- from OAI.NumberTheory.SingleFold.Packed ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed

lemma bits_testBit (x y : ℕ) : Bits x y ↔ ∀ i, x.testBit i=true → y.testBit i=true := by
  simp only [Bits,Nat.testBit_eq_decide_div_mod_eq,decide_eq_true_eq]
  constructor
  · intro h i hi
    have := h i
    have := Nat.mod_lt (y/2^i) (by omega : 0 < 2)
    omega
  · intro h i
    have hx := Nat.mod_lt (x/2^i) (by omega : 0 < 2)
    have hy := Nat.mod_lt (y/2^i) (by omega : 0 < 2)
    by_cases hh : x/2^i%2=1
    · have := h i hh; omega
    · omega

end SingleFold.Packed

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Packed


theorem solution : type_of% @_root_.OAI.SingleFold.Packed.bits_testBit := @_root_.OAI.SingleFold.Packed.bits_testBit
