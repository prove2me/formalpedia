-- Prove2me | solution 1 for OAI.TwoWayComplementation.common_pair_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:55:56.455564+00:00
-- url     : https://prove2.me/submissions/a3f4412e-e154-40db-8eed-e09b281fea23

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean:L50-L91
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.common_pair_budget. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_context_surviving
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_corner_through_absorption
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_missing_comp
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_rectangle_cover
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_rectangle_eq_of_related
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_recurrence_idempotent
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_surviving_absorption
import Theorems.Thm_OAI_TwoWayComplementation_feedback_lost_edge

-- ---- from OAI.Combinatorics.TwoWayAutomata.Relations ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem feedback_insert {α : Type*} (E B : SetRel α α) :
    relStar (E ○ B) ○ E ○ relStar (B ○ E) = E ○ relStar (B ○ E) := by
  rw [← comp_relStar_rotate, SetRel.comp_assoc, relStar_comp_self]

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Diagram ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem mem_port_through {m : ℕ} (e : Diagram m) (positive : Bool) (p q : Fin m) :
    ((!positive, p), (positive, q)) ∈ e.portRelation ↔ (p, q) ∈ e.through positive := by
  cases positive <;> rfl

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Classes ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem through_loop_through {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.through positive ○ e.loopClosure positive ○ e.through positive = e.through positive := by
  cases positive
  · exact congrArg backward he
  · exact congrArg forward he

theorem corner_returns {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner) :
    e.left ⊆ z.left ∧ e.right ⊆ z.right := by
  constructor
  · rw [← congrArg left hz.1]
    exact Set.subset_union_left
  · rw [← congrArg right hz.2]
    exact Set.subset_union_left

theorem recurrence_trans {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {x y z : Fin m}
    (hxy : (x, y) ∈ e.recurrence positive) (hyz : (y, z) ∈ e.recurrence positive) :
    (x, z) ∈ e.recurrence positive := by
  rw [← recurrence_idempotent e he positive]
  exact ⟨y, hxy, hyz⟩

theorem class_nonempty {m : ℕ} {e : Diagram m} {c : Bool × Set (Fin m)}
    (hc : c ∈ e.classes) : c.2.Nonempty := by
  obtain ⟨x, hx, hxc⟩ := hc
  exact ⟨x, hxc ▸ ⟨hx, hx⟩⟩

theorem class_related {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c : Bool × Set (Fin m)} (hc : c ∈ e.classes) {x y : Fin m}
    (hx : x ∈ c.2) (hy : y ∈ c.2) :
    (x, y) ∈ e.recurrence c.1 ∧ (y, x) ∈ e.recurrence c.1 := by
  obtain ⟨p, _, hC⟩ := hc
  rw [hC] at hx hy
  exact ⟨recurrence_trans e he hx.2 hy.1, recurrence_trans e he hy.2 hx.1⟩

theorem class_eq_of_mem {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c : Bool × Set (Fin m)} (hc : c ∈ e.classes) {x : Fin m} (hx : x ∈ c.2) :
    c.2 = {y | (x, y) ∈ e.recurrence c.1 ∧ (y, x) ∈ e.recurrence c.1} := by
  ext y
  constructor
  · exact class_related e he hc hx
  · intro hy
    obtain ⟨p, _, hC⟩ := hc
    rw [hC] at hx ⊢
    exact ⟨recurrence_trans e he hx.1 hy.1, recurrence_trans e he hy.2 hx.2⟩

theorem class_eq_of_common {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c d : Bool × Set (Fin m)} (hc : c ∈ e.classes) (hd : d ∈ e.classes)
    (hsign : c.1 = d.1) {x : Fin m} (hx : x ∈ c.2) (hxd : x ∈ d.2) : c = d := by
  apply Prod.ext hsign
  rw [class_eq_of_mem e he hc hx, class_eq_of_mem e he hd hxd, hsign]

theorem surviving_loop_iff {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {c : Bool × Set (Fin m)} (hc : c ∈ e.classes)
    {x y : Fin m} (hx : x ∈ c.2) (hy : y ∈ c.2) :
    (x, x) ∈ e.surviving z c.1 ↔ (y, y) ∈ e.surviving z c.1 := by
  obtain ⟨hxy, hyx⟩ := class_related e he hc hx hy
  obtain ⟨hl, hr⟩ := surviving_absorption e z hz c.1
  exact ⟨fun h => hr ⟨x, hl ⟨x, hyx, h⟩, hxy⟩,
    fun h => hr ⟨y, hl ⟨y, hxy, h⟩, hyx⟩⟩

theorem not_mem_missing_iff {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {c : Bool × Set (Fin m)} (hc : c ∈ e.classes)
    {x : Fin m} (hx : x ∈ c.2) :
    c ∉ e.missing z ↔ (x, x) ∈ e.surviving z c.1 := by
  classical
  change ¬ (c ∈ e.classes ∧ _) ↔ _
  simp only [hc, true_and, not_forall, not_not]
  exact ⟨fun ⟨y, hy, hyy⟩ => (surviving_loop_iff e z he hz hc hy hx).mp hyy,
    fun hxx => ⟨x, hx, hxx⟩⟩

theorem rectangle_subset {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) (p : Fin m) : e.rectangle positive p ⊆ e.through positive := by
  rintro ⟨u, v⟩ ⟨⟨a, hua, hap⟩, ⟨b, hpb, hbv⟩⟩
  rw [← through_loop_through e he positive]
  exact ⟨b, ⟨a, hua, hap.trans hpb⟩, hbv⟩

theorem rectangle_survives {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    {positive : Bool} {p : Fin m} (hp : (p, p) ∈ e.surviving z positive) :
    e.rectangle positive p ⊆ z.through positive := by
  obtain ⟨hl, hr⟩ := corner_through_absorption e z hz positive
  rintro ⟨u, v⟩ ⟨⟨a, hua, hap⟩, ⟨b, hpb, hbv⟩⟩
  obtain ⟨d, ⟨c, hpc, hcd⟩, hdp⟩ := hp
  exact hr ⟨b, ⟨d, hl ⟨c, ⟨a, hua, hap.trans hpc⟩, hcd⟩, hdp.trans hpb⟩, hbv⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Transport ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem classRectangle_subset {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (C : Bool × Set (Fin m)) : e.classRectangle C ⊆ e.portRelation := by
  rintro ⟨⟨s, a⟩, ⟨t, b⟩⟩ ⟨hs, ht, p, _, hab⟩
  change s = !C.1 at hs
  change t = C.1 at ht
  subst s
  subst t
  exact (mem_port_through e C.1 a b).mpr (rectangle_subset e he C.1 p hab)

theorem classRectangle_cross {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {C : Bool × Set (Fin m)} (hC : C ∈ e.classes) {a b c d : Bool × Fin m}
    (hab : (a, b) ∈ e.classRectangle C) (hcd : (c, d) ∈ e.classRectangle C) :
    (a, d) ∈ e.classRectangle C := by
  obtain ⟨ha, _, p, hp, hab⟩ := hab
  obtain ⟨_, hd, q, hq, hcd⟩ := hcd
  obtain ⟨hpq, hqp⟩ := class_related e he hC hp hq
  rw [← rectangle_eq_of_related e he hpq hqp] at hcd
  exact ⟨ha, hd, p, hp, hab.1, hcd.2⟩

theorem classRectangle_survives {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {C : Bool × Set (Fin m)} (hC : C ∈ e.classes)
    (hmissing : C ∉ e.missing z) : e.classRectangle C ⊆ z.portRelation := by
  rintro ⟨⟨s, a⟩, ⟨t, b⟩⟩ ⟨hs, ht, p, hp, hab⟩
  change s = !C.1 at hs
  change t = C.1 at ht
  subst s
  subst t
  have hloop := (not_mem_missing_iff e z he hz hC hp).mp hmissing
  exact (mem_port_through z C.1 a b).mpr (rectangle_survives e z hz hloop hab)

theorem portRelation_covered {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {a b : Bool × Fin m} (hab : (a, b) ∈ e.portRelation) :
    (a, b) ∈ z.portRelation ∨ ∃ C ∈ e.missing z, (a, b) ∈ e.classRectangle C := by
  classical
  have hthrough (positive : Bool) {p q : Fin m} (hpq : (p, q) ∈ e.through positive) :
      ((!positive, p), (positive, q)) ∈ z.portRelation ∨
        ∃ C ∈ e.missing z, ((!positive, p), (positive, q)) ∈ e.classRectangle C := by
    obtain ⟨r, hrr, hrectangle⟩ := rectangle_cover e he hpq
    let C : Bool × Set (Fin m) :=
      (positive, {x | (r, x) ∈ e.recurrence positive ∧ (x, r) ∈ e.recurrence positive})
    have hC : C ∈ e.classes := ⟨r, hrr, rfl⟩
    have hrect : ((!positive, p), (positive, q)) ∈ e.classRectangle C :=
      ⟨rfl, rfl, r, ⟨hrr, hrr⟩, hrectangle⟩
    by_cases hmissing : C ∈ e.missing z
    · exact Or.inr ⟨C, hmissing, hrect⟩
    · exact Or.inl (classRectangle_survives e z he hz hC hmissing hrect)
  obtain ⟨s, p⟩ := a
  obtain ⟨t, q⟩ := b
  cases s <;> cases t
  · exact Or.inl ((corner_returns e z hz).1 hab)
  · exact hthrough true hab
  · exact hthrough false hab
  · exact Or.inl ((corner_returns e z hz).2 hab)

theorem classInfluence_cross {m : ℕ} (e d u v : Diagram m) (he : comp e e = e)
    (positive : Bool) {C : Bool × Set (Fin m)} (hC : C ∈ e.classes) {a b c f : Fin m}
    (hab : (a, b) ∈ e.classInfluence d u v positive C)
    (hcf : (c, f) ∈ e.classInfluence d u v positive C) :
    (a, f) ∈ e.classInfluence d u v positive C := by
  obtain ⟨_, ⟨y, ⟨x, ⟨p, hap, hpx⟩, hxy⟩, _⟩, _⟩ := hab
  obtain ⟨q, ⟨y', ⟨_, ⟨_, _, _⟩, hx'y'⟩, hy'q⟩, hqf⟩ := hcf
  exact ⟨q, ⟨y', ⟨x, ⟨p, hap, hpx⟩, classRectangle_cross e he hC hxy hx'y'⟩, hy'q⟩, hqf⟩

theorem classInfluence_subset {m : ℕ} (e d u v : Diagram m) (he : comp e e = e)
    (hcontext : comp (comp u e) v = d) (positive : Bool) (C : Bool × Set (Fin m)) :
    e.classInfluence d u v positive C ⊆ d.recurrence positive := by
  have hC := classRectangle_subset e he C
  unfold classInfluence
  calc
    _ ⊆ contextEntry d u v positive ○ relStar (e.portRelation ○ bounceRelation u.right v.left) ○
        e.portRelation ○ relStar (bounceRelation u.right v.left ○ e.portRelation) ○
        contextExit d u v positive := by gcongr
    _ = contextEntry d u v positive ○ e.feedback u.right v.left ○ contextExit d u v positive := by
      simpa only [feedback, SetRel.comp_assoc] using
        congrArg (fun R => contextEntry d u v positive ○ R ○ contextExit d u v positive)
          (feedback_insert e.portRelation (bounceRelation u.right v.left))
    _ = d.recurrence positive := by rw [← context_surviving, hcontext]; rfl

theorem transportMarked_card {m : ℕ} (e d u v : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hcontext : comp (comp u e) v = d)
    (J : Set (Bool × Set (Fin m))) (hJ : J ⊆ e.classes) :
    (e.transportMarked d u v J).ncard ≤ 2 * J.ncard := by
  classical
  have hwitness : ∀ D : e.transportMarked d u v J, ∃ C : J,
      ∃ x ∈ D.val.2, (x, x) ∈ e.classInfluence d u v D.val.1 C.val := by
    intro D
    obtain ⟨C, hCJ, x, hx, hloop⟩ := D.property.2
    exact ⟨⟨C, hCJ⟩, x, hx, hloop⟩
  choose color hcolor using hwitness
  let f : e.transportMarked d u v J → Bool × J := fun D => (D.val.1, color D)
  have hinj : Function.Injective f := by
    intro C D hCD
    have hsign : C.val.1 = D.val.1 := congrArg (fun p : Bool × J => p.1) hCD
    have hsame : color C = color D := congrArg Prod.snd hCD
    obtain ⟨x, hx, hxx⟩ := hcolor C
    obtain ⟨y, hy, hyy⟩ := hcolor D
    rw [← hsame, ← hsign] at hyy
    have hsub := classInfluence_subset e d u v he hcontext C.val.1 (color C).val
    have hxy := hsub (classInfluence_cross e d u v he C.val.1 (hJ (color C).property) hxx hyy)
    have hyx := hsub (classInfluence_cross e d u v he C.val.1 (hJ (color C).property) hyy hxx)
    have hyC : y ∈ C.val.2 := by
      rw [class_eq_of_mem d hd C.property.1 hx]
      exact ⟨hxy, hyx⟩
    exact Subtype.ext (class_eq_of_common d hd C.property.1 D.property.1 hsign hyC hy)
  have hBool : Nat.card Bool = 2 := by simp
  simpa only [Nat.card_prod, hBool, Nat.card_coe_set_eq] using
    Nat.card_le_card_of_injective f hinj

theorem missing_context_subset_marked {m : ℕ} (e d u v z : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hcontext : comp (comp u e) v = d)
    (hz : z ∈ e.corner) (J : Set (Bool × Set (Fin m))) (hJz : e.missing z ⊆ J) :
    d.missing (comp (comp u z) v) ⊆ e.transportMarked d u v J := by
  intro D hD
  obtain ⟨x, hx⟩ := class_nonempty hD.1
  have hxx := (class_related d hd hD.1 hx hx).1
  have hloop : (x, x) ∈ d.surviving (comp (comp u e) v) D.1 := by
    rw [hcontext]
    exact hxx
  rw [context_surviving] at hloop
  obtain ⟨q, ⟨p, hentry, hfeedback⟩, hexit⟩ := hloop
  have hnot : (p, q) ∉ z.feedback u.right v.left := by
    intro hnew
    apply hD.2 x hx
    rw [context_surviving]
    exact ⟨q, ⟨p, hentry, hnew⟩, hexit⟩
  obtain ⟨a, b, hpa, hab, hnotab, hbq⟩ :=
    feedback_lost_edge e.portRelation z.portRelation (bounceRelation u.right v.left) hfeedback hnot
  obtain hnew | ⟨C, hC, hrect⟩ := portRelation_covered e z he hz hab
  · exact (hnotab hnew).elim
  · exact ⟨hD.1, C, hJz hC, x, hx,
      q, ⟨b, ⟨a, ⟨p, hentry, hpa⟩, hrect⟩, hbq⟩, hexit⟩

/-- One fixed target set covers every admissible replacement. -/
theorem transport {m : ℕ} (e d u v : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hcontext : comp (comp u e) v = d)
    (J : Set (Bool × Set (Fin m))) (hJ : J ⊆ e.classes) :
    ∃ J' ⊆ d.classes, J'.ncard ≤ 2 * J.ncard ∧
      ∀ z ∈ e.corner, e.missing z ⊆ J → comp (comp u z) v ∈ d.corner →
        d.missing (comp (comp u z) v) ⊆ J' := by
  refine ⟨e.transportMarked d u v J, fun _ h => h.1,
    transportMarked_card e d u v he hd hcontext J hJ, ?_⟩
  intro z hz hJz _
  exact missing_context_subset_marked e d u v z he hd hcontext hz J hJz

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Amplification ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- The image of a monoid lies in the diagram corner of its image identity. -/
theorem map_identity_corner {A : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (a : A) : ι a ∈ (ι 1).corner := by
  constructor
  · change ι 1 * ι a = ι a
    rw [← map_mul, one_mul]
  · change ι a * ι 1 = ι a
    rw [← map_mul, mul_one]

/-- All pair products share one missing-set bound after sandwiching by an idempotent. -/
theorem common_pair_budget {A : Type*} [Monoid A] {m t c : ℕ}
    (ι : A →ₙ* Diagram m) (f : Bool × Fin t → A) (b0 : A) (hb0 : IsIdempotentElem b0)
    (hcost : ∀ p, ((ι 1).missing (ι (f p))).ncard ≤ 2 * c) :
    ∃ J0 ⊆ (ι b0).classes, J0.ncard ≤ 8 * t * c ∧
      ∀ i j, (ι b0).missing (ι (b0 * f (false, i) * f (true, j) * b0)) ⊆ J0 := by
  classical
  let J := ⋃ p, (ι 1).missing (ι (f p))
  have hJ : J ⊆ (ι 1).classes := by
    intro C hC
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hC
    exact hp.1
  have hcard : J.ncard ≤ 4 * t * c := by
    calc
      J.ncard ≤ ∑ p : Bool × Fin t, ((ι 1).missing (ι (f p))).ncard :=
        Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : Bool × Fin t, 2 * c := Finset.sum_le_sum (fun p _ => hcost p)
      _ = 4 * t * c := by simp; ring
  have he : Diagram.comp (ι 1) (ι 1) = ι 1 := (map_identity_corner ι 1).1
  have hd : Diagram.comp (ι b0) (ι b0) = ι b0 :=
    (map_mul ι b0 b0).symm.trans (congrArg ι hb0.eq)
  have hcontext : Diagram.comp (Diagram.comp (ι b0) (ι 1)) (ι b0) = ι b0 := by
    change ι b0 * ι 1 * ι b0 = ι b0
    rw [← map_mul, ← map_mul, mul_one, hb0.eq]
  obtain ⟨J0, hJ0, hcard0, hcover⟩ := Diagram.transport (ι 1) (ι b0) (ι b0) (ι b0)
    he hd hcontext J hJ
  refine ⟨J0, hJ0, by nlinarith, ?_⟩
  intro i j
  have hproduct : (ι 1).missing (ι (f (false, i) * f (true, j))) ⊆ J := by
    rw [map_mul]
    exact (Diagram.missing_comp (ι 1) _ _ he (map_identity_corner ι _)
      (map_identity_corner ι _)).trans (Set.union_subset
        (Set.subset_iUnion (fun p => (ι 1).missing (ι (f p))) (false, i))
        (Set.subset_iUnion (fun p => (ι 1).missing (ι (f p))) (true, j)))
  have hnew : Diagram.comp (Diagram.comp (ι b0) (ι (f (false, i) * f (true, j))))
      (ι b0) ∈ (ι b0).corner := by
    constructor
    · rw [← Diagram.comp_assoc, ← Diagram.comp_assoc, hd]
    · rw [Diagram.comp_assoc, hd]
  have h := hcover _ (map_identity_corner ι _) hproduct hnew
  change (ι b0).missing (ι b0 * ι (f (false, i) * f (true, j)) * ι b0) ⊆ J0 at h
  simpa only [map_mul, mul_assoc] using h

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.common_pair_budget := @_root_.OAI.TwoWayComplementation.common_pair_budget
