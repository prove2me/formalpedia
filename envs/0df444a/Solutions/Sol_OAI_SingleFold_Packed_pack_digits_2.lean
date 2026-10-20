-- Prove2me | solution 2 for OAI.SingleFold.Packed.pack_digits
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:59:28.964457+00:00
-- url     : https://prove2.me/submissions/7c42a67d-4f04-475b-b3b5-a5ec77fcf04a

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Packed.lean:L86-L99
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Packed.pack_digits. The node keeps its source
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

lemma pack_cons (B k : ℕ) (f : ℕ → ℕ) : pack B (k+1) f=f 0+B*pack B k (fun t=>f (t+1)) := by
  simp only [pack,Finset.sum_range_succ',pow_zero,mul_one,Finset.mul_sum,pow_succ]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intros; ring
lemma pack_zero (B : ℕ) (f : ℕ → ℕ) : pack B 0 f=0 := by simp [pack]
lemma pack_digits {B k x : ℕ} (hB : 0 < B) (hx : x < B^k) : pack B k (digit B x)=x := by
  induction k generalizing x with
  | zero =>
    have : x=0 := by simpa using hx
    simp [this,pack_zero]
  | succ k ih =>
    rw [pack_cons]
    have he : (fun t=>digit B x (t+1))=digit B (x/B) := by
      funext t
      simp [digit,pow_succ',Nat.div_div_eq_div_mul]
    rw [he,ih]
    · simp [digit,Nat.mod_add_div]
    · rw [pow_succ'] at hx
      exact (Nat.div_lt_iff_lt_mul hB).mpr (by simpa [mul_comm] using hx)

end SingleFold.Packed

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Packed


theorem solution : type_of% @_root_.OAI.SingleFold.Packed.pack_digits := @_root_.OAI.SingleFold.Packed.pack_digits
