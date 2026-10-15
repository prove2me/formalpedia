-- Prove2me | solution 1 for OAI.DiscreteFree.MetricBlock.closedBall_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:26:31.087248+00:00
-- url     : https://prove2.me/submissions/5c26ba03-4f49-457d-8fe0-2eca3644f06f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/Attachment.lean:L148-L160
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.MetricBlock.closedBall_card_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Theorems.Thm_OAI_DiscreteFree_MetricBlock_short_finite

-- ---- from OAI.Analysis.LipschitzFree.PortGraphs ----
namespace OAI

/-!
# Port graphs, reduced walks, and capped-distance labels
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree
open scoped BigOperators Classical

namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)

theorem walk_append (x : X) (u v : List D) :
    G.walk x (u ++ v) = G.walk (G.walk x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih _

theorem near_self (n : ℕ) (x : X) : G.Near n x x := ⟨[], by simp, rfl⟩

theorem near_mono {n m : ℕ} {x y : X} (hnm : n ≤ m) (h : G.Near n x y) :
    G.Near m x y := by
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨w, hw.trans hnm, rfl⟩

end PortGraph

namespace BoundedWords
variable {D : Type*}

end BoundedWords

namespace PortGraph
variable {X D : Type*} [Fintype D] (G : PortGraph X D)

end PortGraph
end DiscreteFree

end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.MetricClosure ----
namespace OAI

/-!
# Integer shortest-path metrics and Lipschitz descent
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree.NatMetricClosure
open scoped Classical

variable {X : Type*} (w : X → X → ℕ)

theorem path_relation (P : ℕ → X → X → Prop)
    (hedge : ∀ x y, P (w x y) x y)
    (htrans : ∀ a b x y z, P a x y → P b y z → P (a+b) x z)
    (x y : X) : P (distance w x y) x y := by
  have hcost (u : List X) (a : X) : P (cost w a y u) a y := by
    induction u generalizing a with
    | nil => exact hedge a y
    | cons b u ih => exact htrans _ _ _ _ _ (hedge a b) (ih b)
  obtain ⟨u, hu⟩ := exists_shortest w x y
  simpa [hu] using hcost u x

end DiscreteFree.NatMetricClosure

end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.MetricBlock ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Metric blocks obtained by adjoining finite label anchors
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.MetricBlock
open scoped Classical
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

variable [Fact (0 < R)]

theorem dist_eq (u v : Point G color cap R) : dist u v =
    (NatMetricClosure.distance (weight G color cap R) u v : ℝ) := rfl

end DiscreteFree.MetricBlock
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.Attachment ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Attachment-length estimates and label compatibility
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree
open scoped Classical
namespace PortGraph
variable {X D : Type*} (G : PortGraph X D)
theorem near_trans {m n : ℕ} {x y z : X} (hxy : G.Near m x y) (hyz : G.Near n y z) :
    G.Near (m+n) x z := by
  obtain ⟨u, hu, rfl⟩ := hxy
  obtain ⟨v, hv, rfl⟩ := hyz
  exact ⟨u++v, by simpa only [List.length_append] using Nat.add_le_add hu hv, G.walk_append _ _ _⟩
end PortGraph

namespace MetricBlock
variable {X D C : Type*} [Fintype C] (G : PortGraph X D) (color : X → C) (cap R : ℕ)

omit [Fintype C] in
theorem short_self (n : ℕ) (u : Point G color cap R) : ShortRelation G color cap R n u u := by
  cases u with
  | inl x => exact G.near_self n x
  | inr a => rfl

omit [Fintype C] in
theorem short_trans {m n : ℕ} {u v w : Point G color cap R}
    (huv : ShortRelation G color cap R m u v) (hvw : ShortRelation G color cap R n v w) :
    ShortRelation G color cap R (m+n) u w := by
  cases u <;> cases v <;> cases w <;> simp only [ShortRelation] at *
  · exact G.near_trans huv hvw
  · exact huv.trans hvw

theorem short_edge (hR : 0 < R) (u v : Point G color cap R)
    (h : weight G color cap R u v < R) :
    ShortRelation G color cap R (weight G color cap R u v) u v := by
  by_cases he : u = v
  · subst v
    exact short_self G color cap R _ u
  · cases u with
    | inl x =>
      cases v with
      | inl y =>
        simp only [weight, ite_eq_right he] at h ⊢
        split_ifs at h ⊢ with ha
        · obtain ⟨e, rfl⟩ := ha
          exact ⟨[e], by simp, rfl⟩
        · omega
      | inr a =>
        simp only [weight, ite_eq_right he] at h
        split_ifs at h <;> omega
    | inr a =>
      cases v with
      | inl x =>
        simp only [weight, ite_eq_right he] at h
        split_ifs at h <;> omega
      | inr b =>
        simp only [weight, ite_eq_right he] at h
        omega

theorem short_distance (hR : 0 < R) (u v : Point G color cap R)
    (h : NatMetricClosure.distance (weight G color cap R) u v < R) :
    ShortRelation G color cap R (NatMetricClosure.distance (weight G color cap R) u v) u v := by
  have hp := NatMetricClosure.path_relation (weight G color cap R)
    (fun n x y => n < R → ShortRelation G color cap R n x y)
    (fun x y => short_edge G color cap R hR x y)
    (by
      intro a b x y z hxy hyz hab
      exact short_trans G color cap R (hxy (by omega)) (hyz (by omega))) u v
  exact hp h

omit [Fintype C] in
theorem short_mono {m n : ℕ} (hmn : m ≤ n) {u v : Point G color cap R}
    (h : ShortRelation G color cap R m u v) : ShortRelation G color cap R n u v := by
  cases u <;> cases v <;> simp only [ShortRelation] at *
  · exact G.near_mono hmn h
  · exact h

variable [Fintype D]

omit [Fintype C] in
theorem short_card_le (n : ℕ) (u : Point G color cap R) :
    Nat.card {v : Point G color cap R // ShortRelation G color cap R n u v} ≤
      Fintype.card (BoundedWords D n) := by
  cases u with
  | inl x =>
    let f : BoundedWords D n → {v : Point G color cap R // ShortRelation G color cap R n (Sum.inl x) v} :=
      fun w => ⟨Sum.inl (G.walk x w.val), w.val, w.property, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨(_|a), h⟩
      · obtain ⟨w, hw, rfl⟩ := h
        exact ⟨⟨w, hw⟩, rfl⟩
      · exact False.elim h
    simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective f hf
  | inr a =>
    let f : BoundedWords D n → {v : Point G color cap R // ShortRelation G color cap R n (Sum.inr a) v} :=
      fun _ => ⟨Sum.inr a, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨(x|b), h⟩
      · exact False.elim h
      · change a = b at h
        subst b
        exact ⟨⟨[], by simp⟩, rfl⟩
    simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective f hf

variable [Fact (0 < R)]

theorem closedBall_card_le (n : ℕ) (hn : n < R) (u : Point G color cap R) :
    Nat.card (Metric.closedBall u (n : ℝ)) ≤ Fintype.card (BoundedWords D n) := by
  let f : Metric.closedBall u (n : ℝ) → {v : Point G color cap R // ShortRelation G color cap R n u v} :=
    fun v => ⟨v.val, by
      have hv : NatMetricClosure.distance (weight G color cap R) u v.val ≤ n := by
        have hv' := Metric.mem_closedBall.mp v.property
        rw [dist_comm, dist_eq] at hv'
        exact_mod_cast hv'
      exact short_mono G color cap R hv (short_distance G color cap R Fact.out u v.val (hv.trans_lt hn))⟩
  have : Finite {v : Point G color cap R // ShortRelation G color cap R n u v} :=
    (short_finite G color cap R n u).to_subtype
  exact (Nat.card_le_card_of_injective f (by intro v w h; exact Subtype.ext (congrArg (fun z => z.val) h))).trans
    (short_card_le G color cap R n u)

end MetricBlock
end DiscreteFree
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.MetricBlock
open scoped BigOperators ENNReal
open scoped Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.MetricBlock.closedBall_card_le := @_root_.OAI.DiscreteFree.MetricBlock.closedBall_card_le
