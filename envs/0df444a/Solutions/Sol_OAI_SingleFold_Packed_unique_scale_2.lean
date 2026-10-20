-- Prove2me | solution 2 for OAI.SingleFold.Packed.unique_scale
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:02:36.492166+00:00
-- url     : https://prove2.me/submissions/c822f825-1ffa-41d6-8b32-83f926597844

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Packed.lean:L201-L217
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Packed.unique_scale. The node keeps its source
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

lemma unique_scale {L : ℕ} (hL : 0 < L) : ∃! w : ℕ, 2*L < 2^w ∧ 2^w ≤ 4*L := by
  let w:=Nat.log 2 (2*L)+1
  have hl : 2*L < 2^w := Nat.lt_pow_succ_log_self (by omega) (2*L)
  have hu : 2^w ≤ 4*L := by
    have h := Nat.pow_log_le_self 2 (x:=2*L) (by omega)
    dsimp [w]; rw [pow_succ]; omega
  refine ⟨w,⟨hl,hu⟩,?_⟩
  intro v ⟨hv,hv'⟩
  apply le_antisymm
  · by_contra hh
    have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) (show w+1 ≤ v by omega)
    rw [pow_succ] at hpow
    omega
  · by_contra hh
    have hpow := Nat.pow_le_pow_right (by omega : 0 < 2) (show v+1 ≤ w by omega)
    rw [pow_succ] at hpow
    omega

end SingleFold.Packed

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Packed


theorem solution : type_of% @_root_.OAI.SingleFold.Packed.unique_scale := @_root_.OAI.SingleFold.Packed.unique_scale
