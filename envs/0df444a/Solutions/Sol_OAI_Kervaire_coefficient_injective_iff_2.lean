-- Prove2me | solution 2 for OAI.Kervaire.coefficient_injective_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:16:13.240983+00:00
-- url     : https://prove2.me/submissions/7dddb67b-94d7-4fb1-b2cd-ca4428e6c87c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Reductions.lean:L9-L24
-- (upload_full_project.md Phase 4): solution for node OAI.Kervaire.coefficient_injective_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions

-- ---- from OAI.GroupTheory.Kervaire.Reductions ----
namespace OAI

namespace Kervaire

universe u

/-- The main theorem is exactly the trivial-intersection claim below. -/
theorem coefficient_injective_iff {A : Type u} [Group A] (w : WordGroup A) :
    Function.Injective (coefficientMap w) ↔
      ∀ a : A, Monoid.Coprod.inl a ∈ relatorClosure w → a = 1 := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [eq_bot_iff]
  constructor
  · intro h a ha
    apply h
    change QuotientGroup.mk _ = 1
    exact (QuotientGroup.eq_one_iff _).mpr ha
  · intro h a ha
    change a = 1
    apply h a
    change (QuotientGroup.mk (Monoid.Coprod.inl a) : RelatorQuotient w) = 1 at ha
    exact (QuotientGroup.eq_one_iff _).mp ha

end Kervaire

end OAI

-- ---- platform node ----
open OAI OAI.Kervaire


theorem solution.{u} : type_of% @_root_.OAI.Kervaire.coefficient_injective_iff.{u} := @_root_.OAI.Kervaire.coefficient_injective_iff.{u}
