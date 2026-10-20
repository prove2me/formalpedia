-- Prove2me | solution 2 for OAI.SingleFold.PellPower.power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:32:56.771611+00:00
-- url     : https://prove2.me/submissions/0b84b07b-ff40-47ca-88a4-4e3f10a7cecf

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Pell.lean:L20-L34
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.PellPower.power_bounds. The node keeps its source
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

-- ---- from OAI.NumberTheory.SingleFold.Pell ----
namespace OAI

namespace SingleFold.PellPower

variable {a : ℕ} (ha : 1 < a)

lemma step_bounds (n : ℕ) :
    (2*a-1)*Pell.yn ha (n+1) ≤ Pell.yn ha (n+2) ∧
    Pell.yn ha (n+2) ≤ (2*a)*Pell.yn ha (n+1) := by
  have hr := Pell.yn_succ_succ ha n
  have hm := (Pell.strictMono_y ha).monotone (Nat.le_succ n)
  have ha' : 2*a-1+1=2*a := by omega
  constructor <;> nlinarith

lemma power_bounds (n : ℕ) :
    (2*a-1)^n ≤ Pell.yn ha (n+1) ∧ Pell.yn ha (n+1) ≤ (2*a)^n := by
  induction n with
  | zero => simp
  | succ n hn =>
    obtain ⟨hl,hu⟩ := step_bounds ha n
    constructor
    · calc
        (2*a-1)^(n+1)=(2*a-1)*(2*a-1)^n := pow_succ' _ _
        _ ≤ (2*a-1)*Pell.yn ha (n+1) := Nat.mul_le_mul_left _ hn.1
        _ ≤ Pell.yn ha (n+2) := hl
    · calc
        Pell.yn ha (n+2) ≤ (2*a)*Pell.yn ha (n+1) := hu
        _ ≤ (2*a)*(2*a)^n := Nat.mul_le_mul_left _ hn.2
        _ = (2*a)^(n+1) := (pow_succ' _ _).symm

end SingleFold.PellPower

namespace SingleFold.PellAnalytics
end SingleFold.PellAnalytics

namespace SingleFold.PellSystem
end SingleFold.PellSystem

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.PellPower


theorem solution : type_of% @_root_.OAI.SingleFold.PellPower.power_bounds := @_root_.OAI.SingleFold.PellPower.power_bounds
