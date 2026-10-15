-- Prove2me | solution 1 for OAI.TwoWayComplementation.smaller_relation_instance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:01:16.991532+00:00
-- url     : https://prove2.me/submissions/2ea28462-d361-4eea-9406-029a0767931c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean:L178-L285
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.smaller_relation_instance. The node keeps its source
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
import Theorems.Thm_OAI_TwoWayComplementation_minimal_corner_reflects_units
import Theorems.Thm_OAI_TwoWayComplementation_minimal_idempotent_lift
import Theorems.Thm_OAI_TwoWayComplementation_relation_corner_equiv

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

theorem corner_comp {m : ℕ} {e z w : Diagram m} (hz : z ∈ e.corner)
    (hw : w ∈ e.corner) : comp z w ∈ e.corner := by
  constructor
  · rw [← comp_assoc, hz.1]
  · rw [comp_assoc, hw.2]

theorem corner_pow_succ {m : ℕ} {e z : Diagram m} (hz : z ∈ e.corner) (k : ℕ) :
    z ^ (k + 1) ∈ e.corner := by
  induction k with
  | zero => simpa using hz
  | succ k ih => exact pow_succ z (k + 1) ▸ corner_comp ih hz

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

theorem missing_pow_succ {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (k : ℕ) : e.missing (z ^ (k + 1)) ⊆ e.missing z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (missing_comp e _ z he (corner_pow_succ hz k) hz).trans
      (Set.union_subset ih Set.Subset.rfl)

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

-- ---- from OAI.Combinatorics.TwoWayAutomata.Corners ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- A finite nonempty subsemigroup contains an idempotent. -/
theorem finite_subsemigroup_idempotent {A : Type*} [Semigroup A] [Finite A]
    (S : Set A) (hne : S.Nonempty) (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) :
    ∃ e ∈ S, IsIdempotentElem e := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  exact exists_idempotent_in_compact_subsemigroup (fun _ => continuous_of_discreteTopology)
    S hne (Set.toFinite S).isCompact hmul

/-- Every element of a finite monoid has an idempotent positive power. -/
theorem finite_idempotent_pow {A : Type*} [Monoid A] [Finite A] (a : A) :
    ∃ k : ℕ, 0 < k ∧ IsIdempotentElem (a ^ k) := by
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := finite_subsemigroup_idempotent
    (Set.range (fun k : ℕ => a ^ (k + 1))) ⟨a, 0, by simp⟩ (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact ⟨i + j + 1, by simp only [← pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]⟩)
  exact ⟨k + 1, Nat.succ_pos _, hk⟩

/-- A multiplicative map preserves positive powers without any unitality assumption. -/
theorem map_positive_pow {A B : Type*} [Monoid A] [Monoid B]
    (f : A →ₙ* B) (a : A) (k : ℕ) : f (a ^ (k + 1)) = f a ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, map_mul, ih, ← pow_succ]

theorem cornerMap_surjective {A M : Type*} [Semigroup A] [Semigroup M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) {d : A} {q : M}
    (hd : IsIdempotentElem d) (hq : IsIdempotentElem q) (hθd : θ d = q) :
    Function.Surjective (cornerMap θ hd hq hθd) := by
  intro y
  obtain ⟨x, hx⟩ := hθ y.val
  refine ⟨⟨d * x * d, x, rfl⟩, ?_⟩
  apply Subtype.ext
  change θ (d * x * d) = y.val
  obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hq).mp y.property
  rw [map_mul, map_mul, hθd, hx, hl, hr]

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.RelationMonoid ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Restriction-corner identities.
    The supporting relation `i` can be any idempotent with `iPi = i`. -/
theorem relation_corner_identities {α : Type*} (P i : SetRel α α)
    (hP : P ○ P = P) (hiPi : i ○ P ○ i = i) :
    let Q := P ○ i ○ P
    Q ○ Q = Q ∧ P ○ Q = Q ∧ Q ○ P = Q ∧
    Q ○ i = P ○ i ∧ i ○ Q = i ○ P ∧ i ○ Q ○ i = i := by
  have hPP (R : SetRel α α) : P ○ (P ○ R) = P ○ R := by
    rw [← SetRel.comp_assoc, hP]
  have hiPiR (R : SetRel α α) : i ○ (P ○ (i ○ R)) = i ○ R := by
    rw [← SetRel.comp_assoc i P, ← SetRel.comp_assoc, hiPi]
  dsimp
  simp [SetRel.comp_assoc, hPP, hiPiR, hP, hiPi]

namespace RelationMonoid

end RelationMonoid

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

/-- The cardinality consequence of the uniform transport theorem. -/
theorem missing_context_card {m : ℕ} (e d u v z : Diagram m)
    (he : Diagram.comp e e = e) (hd : Diagram.comp d d = d)
    (hcontext : Diagram.comp (Diagram.comp u e) v = d) (hz : z ∈ e.corner)
    (hnew : Diagram.comp (Diagram.comp u z) v ∈ d.corner) :
    (d.missing (Diagram.comp (Diagram.comp u z) v)).ncard ≤ 2 * (e.missing z).ncard := by
  obtain ⟨J', _, hcard, hcover⟩ := Diagram.transport e d u v he hd hcontext
    (e.missing z) (fun _ h => h.1)
  exact (Set.ncard_le_ncard (hcover z hz Set.Subset.rfl hnew)).trans hcard

/-- Restricting an idempotent sandwich preserves the new pair and supplies all unit lifts. -/
theorem smaller_relation_instance {A H : Type*} [Monoid A] [Finite A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H) (hφ : Function.Surjective φ)
    (b b' : A) (hb : IsIdempotentElem b) (hbb' : b * b' = b') (hb'b : b' * b = b')
    (F : Set H)
    (hiPi : restrictedIdentity F ○ (φ b).toRel ○ restrictedIdentity F = restrictedIdentity F)
    (x y : F)
    (hpair : restrictedIdentity F ○ (φ b').toRel ○ restrictedIdentity F =
      restrictedIdentity F ∪ {(x.val, y.val)}) :
    ∃ d : hb.Corner, ∃ hd : IsIdempotentElem d, ∃ ψ : hd.Corner →* RelationMonoid F,
      Function.Surjective ψ ∧
      (∀ σ : Equiv.Perm F, ∃ p : hd.Cornerˣ, ψ p = (permutationUnit σ).val) ∧
      (∀ w, (ψ w).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ (φ w.val.val).toRel}) ∧
      ∃ v : hd.Corner, IsIdempotentElem v ∧ (ψ v).toRel = SetRel.id ∪ {(x, y)} ∧
        ((ι d.val).missing (ι v.val.val)).ncard ≤ 2 * ((ι b).missing (ι b')).ncard := by
  let P := (φ b).toRel
  let i := restrictedIdentity F
  let Q := P ○ i ○ P
  have hP : IsIdempotentElem (φ b) := by rw [IsIdempotentElem, ← map_mul, hb.eq]
  have hPP : P ○ P = P := congrArg RelationMonoid.toRel hP.eq
  obtain ⟨hQ, ρ, hρ⟩ := relation_corner_equiv P F hPP hiPi
  have hident := relation_corner_identities P i hPP hiPi
  let q : hP.Corner := ⟨.ofRel Q, (Subsemigroup.mem_corner_iff hP).mpr
    ⟨RelationMonoid.ext hident.2.1, RelationMonoid.ext hident.2.2.1⟩⟩
  have hq : IsIdempotentElem q := Subtype.ext hQ.eq
  let θ := cornerMap φ.toMulHom hb hP rfl
  have hθ : Function.Surjective θ := cornerMap_surjective φ.toMulHom hφ hb hP rfl
  obtain ⟨d, hd, hθd, hminimal⟩ := minimal_idempotent_lift θ.toMulHom hθ q hq
  let γ := cornerMap θ.toMulHom hd hq hθd
  let equiv := (cornerFlatten hP q hq).trans ρ
  let ψ := equiv.toMonoidHom.comp γ
  have hψ : Function.Surjective ψ :=
    equiv.surjective.comp (cornerMap_surjective θ.toMulHom hθ hd hq hθd)
  have hψrel (w : hd.Corner) :
      (ψ w).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ (φ w.val.val).toRel} :=
    hρ _
  have hψunits (σ : Equiv.Perm F) : ∃ p : hd.Cornerˣ, ψ p = (permutationUnit σ).val := by
    obtain ⟨w, hw⟩ := hψ (permutationUnit σ).val
    have hunitψ : IsUnit (ψ w) := hw.symm ▸ (permutationUnit σ).isUnit
    have hunitγ : IsUnit (γ w) := by
      have h := hunitψ.map equiv.symm.toMonoidHom
      simpa only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply] using h
    obtain ⟨p, hp⟩ := minimal_corner_reflects_units θ.toMulHom hd hq hθd hminimal w hunitγ
    exact ⟨p, hp ▸ hw⟩
  have hdimage : φ d.val = RelationMonoid.ofRel Q := congrArg Subtype.val hθd
  let b'c : hb.Corner := ⟨b', (Subsemigroup.mem_corner_iff hb).mpr ⟨hbb', hb'b⟩⟩
  let w : hd.Corner := ⟨d * b'c * d, b'c, rfl⟩
  have hwimage : (ψ w).toRel = SetRel.id ∪ {(x, y)} := by
    rw [hψrel]
    change {xy : F × F | (xy.1.val, xy.2.val) ∈ (φ (d.val * b' * d.val)).toRel} = _
    rw [map_mul, map_mul, hdimage, RelationMonoid.toRel_mul, RelationMonoid.toRel_mul,
      RelationMonoid.toRel_ofRel]
    have habsorb : P ○ (φ b').toRel ○ P = (φ b').toRel := by
      change ((φ b * φ b') * φ b).toRel = _
      rw [← map_mul, ← map_mul, hbb', hb'b]
    have hsandwich : i ○ (Q ○ (φ b').toRel ○ Q) ○ i = i ∪ {(x.val, y.val)} := by
      calc
        i ○ (Q ○ (φ b').toRel ○ Q) ○ i =
            (i ○ Q) ○ (φ b').toRel ○ (Q ○ i) := by simp only [SetRel.comp_assoc]
        _ = i ○ (P ○ (φ b').toRel ○ P) ○ i := by
          rw [hident.2.2.2.1, hident.2.2.2.2.1]
          simp only [SetRel.comp_assoc]
        _ = i ∪ {(x.val, y.val)} := by rw [habsorb]; exact hpair
    ext ⟨r, s⟩
    have hmem : (r.val, s.val) ∈ i ○ (Q ○ (φ b').toRel ○ Q) ○ i ↔
        (r.val, s.val) ∈ Q ○ (φ b').toRel ○ Q := by
      simp [i, SetRel.comp, restrictedIdentity, r.property, s.property]
    change (r.val, s.val) ∈ Q ○ (φ b').toRel ○ Q ↔ (r, s) ∈ SetRel.id ∪ {(x, y)}
    rw [← hmem, hsandwich]
    simp [i, restrictedIdentity, SetRel.id, Subtype.ext_iff]
  have hiPair : IsIdempotentElem (ψ w) := by
    apply RelationMonoid.ext
    rw [RelationMonoid.toRel_mul, hwimage]
    ext ⟨r, s⟩
    simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
      SetRel.id, Prod.mk.injEq]
    aesop
  obtain ⟨k, hk, hv⟩ := finite_idempotent_pow w
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  refine ⟨d, hd, ψ, hψ, hψunits, hψrel, w ^ (k + 1), hv, ?_, ?_⟩
  · rw [map_pow, hiPair.pow_succ_eq, hwimage]
  · let ιb : hb.Corner →ₙ* Diagram m := ι.comp (MulMemClass.subtype _)
    let ιd : hd.Corner →ₙ* Diagram m := ιb.comp (MulMemClass.subtype _)
    have hid : Diagram.comp (ι d.val) (ι d.val) = ι d.val :=
      (map_mul ιb d d).symm.trans (congrArg ιb hd.eq)
    have hib : Diagram.comp (ι b) (ι b) = ι b :=
      (map_mul ι b b).symm.trans (congrArg ι hb.eq)
    obtain ⟨hbd, hdb⟩ := (Subsemigroup.mem_corner_iff hb).mp d.property
    have hcontext : Diagram.comp (Diagram.comp (ι d.val) (ι b)) (ι d.val) = ι d.val := by
      change ι d.val * ι b * ι d.val = ι d.val
      rw [← map_mul, hdb]
      exact hid
    have hb' : ι b' ∈ (ι b).corner :=
      ⟨(map_mul ι b b').symm.trans (congrArg ι hbb'),
        (map_mul ι b' b).symm.trans (congrArg ι hb'b)⟩
    have hw : ιd w ∈ (ι d.val).corner := map_identity_corner ιd w
    have htransport := missing_context_card (ι b) (ι d.val) (ι d.val) (ι d.val) (ι b')
      hib hid hcontext hb' (by
        change ι d.val * ι b' * ι d.val ∈ (ι d.val).corner
        rw [← map_mul, ← map_mul]
        exact hw)
    have hpow := Diagram.missing_pow_succ (ι d.val) (ιd w) hid hw k
    rw [← map_positive_pow] at hpow
    apply (Set.ncard_le_ncard hpow).trans
    change ((ι d.val).missing (ι (d.val * b' * d.val))).ncard ≤ _
    rw [map_mul, map_mul]
    exact htransport

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.smaller_relation_instance := @_root_.OAI.TwoWayComplementation.smaller_relation_instance
