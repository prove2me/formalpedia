-- Prove2me | solution 1 for OAI.CHObstruction.Domination.countable_exceptions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:20:54.839334+00:00
-- url     : https://prove2.me/submissions/dd1218a6-6e56-4d5f-9b79-adb343ff357c

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Collapse.lean:L137-L152
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Domination.countable_exceptions. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse

-- ---- from OAI.ModelTheory.Categoricity.Collapse ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace TaggedCollapse

variable {Q : Type u} (R : Q → Q → Prop) (wf : WellFounded R)

end TaggedCollapse

namespace Domination

theorem values_eq (a : Alpha.{u}) (b : Beta.{u}) :
    (values a b).val =
      ⨆ g : Prior a b, succ (values ⟨g.val.val, lt_trans g.val.property a.property⟩ b).val := by
  conv_lhs => rw [values, WellFounded.fix_eq]
  rfl

theorem eventually_lt (a : Alpha.{u}) (g : Set.Iio a.val) (b : Beta.{u})
    (hb : (indexEmbedding a g).val < b.val) :
    (values ⟨g.val, lt_trans g.property a.property⟩ b).val < (values a b).val := by
  rw [values_eq a b]
  exact (lt_succ _).trans_le (Ordinal.le_iSup _ (⟨g, hb⟩ : Prior a b))

theorem countable_exceptions (a : Alpha.{u}) (g : Set.Iio a.val) :
    {b : Beta.{u} | (values a b).val ≤ (values ⟨g.val, lt_trans g.property a.property⟩ b).val}.Countable := by
  let bound := succ (indexEmbedding a g).val
  have hb : bound < ω_ 1 :=
    (Cardinal.isSuccLimit_omega 1).succ_lt (indexEmbedding a g).property
  have := countable_Iio hb
  apply Set.countable_coe_iff.1
  let f : {b : Beta.{u} | (values a b).val ≤
      (values ⟨g.val, lt_trans g.property a.property⟩ b).val} → Set.Iio bound :=
    fun b => ⟨b.val.val, Order.lt_succ_iff.2 (le_of_not_gt (fun h =>
      (eventually_lt a g b.val h).not_ge b.property))⟩
  apply Function.Injective.countable (f := f)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : Set.Iio bound => x.val) h

end Domination

namespace CountableClosures

variable {A : Type u} (R : A → A → Prop)
  (separates : ∀ a b, a ≠ b → ∃ w, ¬ (R w a ↔ R w b))

end CountableClosures

namespace TaggedLimit

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
  (F : ι → Type u) (f : ∀ i j, i ≤ j → F i ↪ F j)
  [DirectedSystem F (fun i j h => f i j h)]
  (R : ∀ i, F i → F i → Prop)
  (respect : ∀ i j h x y, R i x y ↔ R j (f i j h x) (f i j h y))
  (ρ : ∀ i, F i → Ordinal.{u})
  (tags : ∀ i j h x, ρ i x = ρ j (f i j h x))

end TaggedLimit

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.Domination
open Cardinal Ordinal Order


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Domination.countable_exceptions.{u} := @_root_.OAI.CHObstruction.Domination.countable_exceptions.{u}
