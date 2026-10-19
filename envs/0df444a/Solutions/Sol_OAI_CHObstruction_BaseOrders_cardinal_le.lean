-- Prove2me | solution 1 for OAI.CHObstruction.BaseOrders.cardinal_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:25:18.542039+00:00
-- url     : https://prove2.me/submissions/507dbc3e-fa32-4ce3-b1ca-f0bfe51c96d4

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/TailBound.lean:L174-L210
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.BaseOrders.cardinal_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound

-- ---- from OAI.ModelTheory.Categoricity.TailBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace TuplePatterns

open Tuples

variable {I : Type u} [LinearOrder I]

variable {C : Type u}

end TuplePatterns

namespace TailBound

open Tuples Diagrams Colors Tests ThresholdArithmetic

variable {I B : Type u} (hCH : CH.{u})

end TailBound

namespace BaseOrders

variable {B : Type u} [LinearOrder B]

theorem initial_bound (h : ∀ b : B, (Set.Iic b).Countable) :
    #B ≤ (ℵ_ 1 : Cardinal.{u}) := by
  classical
  by_cases hsmall : #B ≤ ℵ₀
  · exact hsmall.trans (Cardinal.aleph0_le_aleph 1)
  have hone : (ℵ_ 1 : Cardinal.{u}) ≤ #B := by
    rw [show (ℵ_ (1 : Ordinal) : Cardinal.{u}) = succ ℵ₀ by
      rw [← Cardinal.aleph_zero, Cardinal.succ_aleph]; simp]
    exact Order.succ_le_of_lt (lt_of_not_ge hsmall)
  obtain ⟨e⟩ : Nonempty ((ω_ 1 : Ordinal.{u}).ToType ↪ B) := by
    apply (Cardinal.le_def _ _).1
    simpa only [Cardinal.mk_toType, Ordinal.card_omega] using hone
  have hcof : ∀ b : B, ∃ i, b ≤ e i := by
    intro b
    by_contra! hb
    have he : Function.Injective (fun i => (⟨e i, (hb i).le⟩ : Set.Iic b)) :=
      fun i j hij => e.injective (congrArg Subtype.val hij)
    have := (h b).to_subtype
    have hc := (Cardinal.mk_le_of_injective he).trans (Cardinal.mk_le_aleph0 (α := Set.Iic b))
    rw [Cardinal.mk_toType, Ordinal.card_omega] at hc
    exact (Cardinal.aleph0_lt_aleph.2 (by norm_num : (0 : Ordinal) < 1)).not_ge hc
  choose ix hix using hcof
  let f : B → Σ i : (ω_ 1 : Ordinal.{u}).ToType, Set.Iic (e i) :=
    fun b => ⟨ix b, b, hix b⟩
  have hf : Function.Injective f := by
    intro b c heq
    exact congrArg (fun x : Σ i, Set.Iic (e i) => x.2.val) heq
  apply (Cardinal.mk_le_of_injective hf).trans
  rw [Cardinal.mk_sigma]
  calc
    Cardinal.sum (fun i => #(Set.Iic (e i))) ≤ Cardinal.sum (fun _ : (ω_ 1 : Ordinal.{u}).ToType =>
        (ℵ₀ : Cardinal.{u})) := by
      apply Cardinal.sum_le_sum
      intro i
      have := (h (e i)).to_subtype
      exact Cardinal.mk_le_aleph0
    _ = ℵ_ 1 := by
      rw [Cardinal.sum_const, Cardinal.mk_toType, Ordinal.card_omega, Cardinal.lift_id, Cardinal.lift_id,
        Cardinal.mul_eq_left (Cardinal.aleph0_le_aleph 1) (Cardinal.aleph0_le_aleph 1)
          Cardinal.aleph0_ne_zero]

theorem cardinal_le [Nonempty B] (h : ∀ a b : B, (Set.Icc a b).Countable) :
    #B ≤ (ℵ_ 1 : Cardinal.{u}) := by
  classical
  let p : B := Classical.arbitrary B
  have hup : #(Set.Ici p) ≤ (ℵ_ 1 : Cardinal.{u}) := by
    apply initial_bound
    intro b
    have hinj : Function.Injective (fun x : Set.Iic b =>
        (⟨x.val.val, x.val.property, x.property⟩ : Set.Icc p b.val)) :=
      fun x y heq => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : Set.Icc p b.val => z.val) heq
    have := (h p b).to_subtype
    have : Countable (Set.Iic b) := hinj.countable
    exact Set.to_countable _
  have hdn : #(Set.Iic p) ≤ (ℵ_ 1 : Cardinal.{u}) := by
    apply @initial_bound (OrderDual (Set.Iic p)) _
    intro b
    have hinj : Function.Injective (fun x : Set.Iic b =>
        (⟨x.val.val, x.property, x.val.property⟩ : Set.Icc b.val p)) :=
      fun x y heq => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : Set.Icc b.val p => z.val) heq
    have := (h b.val p).to_subtype
    have : Countable (Set.Iic b) := hinj.countable
    exact Set.to_countable _
  let f : B → Set.Ici p ⊕ Set.Iic p := fun b =>
    if hb : p ≤ b then Sum.inl ⟨b, hb⟩ else Sum.inr ⟨b, (le_of_not_ge hb)⟩
  have hf : Function.Injective f := by
    intro b c heq
    have hv := congrArg (Sum.elim Subtype.val Subtype.val) heq
    simpa [f, apply_dite] using hv
  apply (Cardinal.mk_le_of_injective hf).trans
  simpa only [Cardinal.mk_sum, Cardinal.lift_id,
    Cardinal.add_eq_self (Cardinal.aleph0_le_aleph 1)] using add_le_add hup hdn

end BaseOrders

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.BaseOrders
open Cardinal Ordinal Order


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.BaseOrders.cardinal_le.{u} := @_root_.OAI.CHObstruction.BaseOrders.cardinal_le.{u}
