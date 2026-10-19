-- Prove2me | solution 1 for OAI.Release075.PermCycles.swap_sameCycle_away
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:42:04.556004+00:00
-- url     : https://prove2.me/submissions/ea7d8fd4-87a1-423d-a055-c5be3281811c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Planarity.lean:L10-L36
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.PermCycles.swap_sameCycle_away. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity

-- ---- from OAI.GroupTheory.Hyperbolic.Planarity ----
namespace OAI

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

/-- A swap supported in other colors leaves this entire orbit unchanged. -/
theorem swap_sameCycle_away {C : Type*} (f : Perm A) (color : A → C)
    (hcolor : ∀ z, color (f z) = color z) (a b x y : A)
    (ha : color x ≠ color a) (hb : color x ≠ color b) :
    (Equiv.swap a b * f).SameCycle x y ↔ f.SameCycle x y := by
  have hp (n : ℕ) : color ((f^n) x) = color x := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ',Perm.mul_apply,hcolor] using ih
  have he (n : ℕ) : ((Equiv.swap a b * f)^n) x = (f^n) x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',Perm.mul_apply,ih,pow_succ',Perm.mul_apply]
      change Equiv.swap a b (f ((f^n) x)) = f ((f^n) x)
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h
        exact ha (((hcolor _).trans (hp n)).symm.trans (congrArg color h))
      · intro h
        exact hb (((hcolor _).trans (hp n)).symm.trans (congrArg color h))
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ),by simpa only [zpow_natCast,he] using hn⟩
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨(n : ℤ),by simpa only [zpow_natCast,he] using hn⟩

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B : Type*} [Fintype A] [Fintype B]

end Release075.PermCycles

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq


theorem solution : type_of% @_root_.OAI.Release075.PermCycles.swap_sameCycle_away := @_root_.OAI.Release075.PermCycles.swap_sameCycle_away
