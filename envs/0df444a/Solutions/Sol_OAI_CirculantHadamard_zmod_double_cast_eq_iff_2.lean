-- Prove2me | solution 2 for OAI.CirculantHadamard.zmod_double_cast_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:18:09.957587+00:00
-- url     : https://prove2.me/submissions/b2878e4d-c626-4f0e-9f12-7485a0b631a2

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/ProjectionPairFiber.lean:L15-L43
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.zmod_double_cast_eq_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection

-- ---- from OAI.LinearAlgebra.CirculantHadamard.ProjectionPairFiber ----
namespace OAI

/-!
# The two fibers of reduction modulo half the order

Reduction from `ZMod (2 * m)` to `ZMod m` has exactly the two usual lifts
of each element when `m` is positive.
-/

namespace CirculantHadamard

/-- The fiber of reduction modulo `m` consists of its two canonical lifts. -/
theorem zmod_double_cast_eq_iff {m : ℕ} (hm : 0 < m) (h : m ∣ 2 * m)
    (x : ZMod (2 * m)) (j : ZMod m) :
    ZMod.castHom h (ZMod m) x = j ↔
      x = (j.val : ZMod (2 * m)) ∨ x = ((j.val + m : ℕ) : ZMod (2 * m)) := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero (2 * m) := ⟨by omega⟩
  have hxlt : x.val < 2 * m := ZMod.val_lt x
  have hjlt : j.val < m := ZMod.val_lt j
  constructor
  · intro hx
    have hmod : x.val % m = j.val := by
      simpa only [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast] using
        congrArg ZMod.val hx
    by_cases hsmall : x.val < m
    · left
      have hval : x.val = j.val := by
        simpa only [Nat.mod_eq_of_lt hsmall] using hmod
      rw [← hval, ZMod.natCast_zmod_val]
    · right
      have hmle : m ≤ x.val := by omega
      have hsub : x.val - m < m := by omega
      rw [Nat.mod_eq_sub_mod hmle, Nat.mod_eq_of_lt hsub] at hmod
      have hval : x.val = j.val + m := by omega
      rw [← hval, ZMod.natCast_zmod_val]
  · rintro (rfl | rfl)
    · simp only [map_natCast, ZMod.natCast_zmod_val]
    · rw [map_natCast]
      simp only [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]

end CirculantHadamard

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard


theorem solution : type_of% @_root_.OAI.CirculantHadamard.zmod_double_cast_eq_iff := @_root_.OAI.CirculantHadamard.zmod_double_cast_eq_iff
