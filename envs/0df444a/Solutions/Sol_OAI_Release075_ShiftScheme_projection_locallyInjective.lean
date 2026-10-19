-- Prove2me | solution 1 for OAI.Release075.ShiftScheme.projection_locallyInjective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:35:02.429289+00:00
-- url     : https://prove2.me/submissions/f74f903b-4c1a-47a5-a8ff-458b3987afbb

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Presentation.lean:L158-L201
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.ShiftScheme.projection_locallyInjective. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation

-- ---- from OAI.GroupTheory.Hyperbolic.Presentation ----
namespace OAI

namespace Release075

/-- The shift by a number in [0,r) remains injective modulo any modulus at least r. -/
theorem fin_natCast_injective (r s : ℕ) (hs : r ≤ s) :
    Function.Injective (fun v : Fin r => (v.val : ZMod s)) := by
  intro v w h
  by_cases hsz : s = 0
  · have : r = 0 := by omega
    exact Fin.elim0 (this ▸ v)
  · let : NeZero s := ⟨hsz⟩
    apply Fin.ext
    have hh := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (v.isLt.trans_le hs),
      Nat.mod_eq_of_lt (w.isLt.trans_le hs)] using hh

namespace ShiftScheme
variable {I P B : Type*} {r : ℕ} {inc : P → Finset I} (d : ShiftScheme I P B r inc)

theorem projection_locallyInjective : LocallyInjective d.projection := by
  intro a b c hab hac heq
  cases a with
  | inl x =>
    cases b with
    | inl y => exact hab.elim
    | inr b =>
      cases c with
      | inl y => exact hac.elim
      | inr c =>
        obtain ⟨i,u,v⟩ := x
        obtain ⟨b,ub,j⟩ := b
        obtain ⟨c,uc,k⟩ := c
        obtain ⟨hi,hui,hj⟩ := hab
        obtain ⟨hi',hui',hk⟩ := hac
        have hbc : d.point b = d.point c := Sum.inr.inj heq
        have hbc' := d.unique b c i hbc hi hi'
        subst c
        have hu : ub = uc := hui.symm.trans hui'
        subst uc
        have hjk : j = k := hj.trans hk.symm
        subst k
        rfl
  | inr l =>
    cases b with
    | inr m => exact hab.elim
    | inl x =>
      cases c with
      | inr m => exact hac.elim
      | inl y =>
        obtain ⟨b,ub,j⟩ := l
        obtain ⟨i,u,v⟩ := x
        obtain ⟨i',u',v'⟩ := y
        have hii : i = i' := Sum.inl.inj heq
        subst i'
        obtain ⟨hi,hu,hj⟩ := hab
        obtain ⟨hi',hu',hj'⟩ := hac
        have huu : u = u' := hu.trans hu'.symm
        subst u'
        have hvv : (v.val : ZMod (d.size b)) = (v'.val : ZMod (d.size b)) :=
          add_left_cancel (hj.symm.trans hj')
        have hv := fin_natCast_injective r (d.size b) (d.size_ge b) hvv
        subst v'
        rfl

end ShiftScheme

end Release075

namespace Release075

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

end BlockPresentation

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

end BlockPresentation
end Release075

namespace Release075
noncomputable section
open scoped BigOperators
attribute [local instance] OAI.Release075.instDecidableEq_oAI
namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.ShiftScheme


theorem solution : type_of% @_root_.OAI.Release075.ShiftScheme.projection_locallyInjective := @_root_.OAI.Release075.ShiftScheme.projection_locallyInjective
