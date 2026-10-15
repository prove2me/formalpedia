-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.nested_chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:40:42.520247+00:00
-- url     : https://prove2.me/submissions/27b2248b-e7b3-42f4-bf4c-3c52cc5260da

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean:L265-L346
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.nested_chain_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_class_containment
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_recurrence_idempotent
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_surviving_absorption
import Theorems.Thm_OAI_TwoWayComplementation_weighted_class_bound

-- ---- from OAI.Combinatorics.TwoWayAutomata.Classes ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem nesting_refl {m : ℕ} {e : Diagram m} (he : comp e e = e) :
    (e, e) ∈ nesting m := ⟨he, he, he, he⟩

theorem nesting_trans {m : ℕ} {d e f : Diagram m}
    (hde : (d, e) ∈ nesting m) (hef : (e, f) ∈ nesting m) :
    (d, f) ∈ nesting m := by
  refine ⟨hde.1, hef.2.1, ?_, ?_⟩
  · calc
      comp d f = comp (comp d e) f := by rw [hde.2.2.1]
      _ = comp d e := by rw [comp_assoc, hef.2.2.1]
      _ = d := hde.2.2.1
  · calc
      comp f d = comp f (comp e d) := by rw [hde.2.2.2]
      _ = comp e d := by rw [← comp_assoc, hef.2.2.2]
      _ = d := hde.2.2.2

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

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Nesting ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem loopClosure_subset_of_corner {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) : e.loopClosure positive ⊆ d.loopClosure positive := by
  obtain ⟨hL, hR⟩ := corner_returns e d hd
  cases positive
  · exact relStar_mono (SetRel.comp_subset_comp hR hL)
  · exact relStar_mono (SetRel.comp_subset_comp hL hR)

theorem nested_unprotected_loss {m : ℕ} (e d : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hde : d ∈ e.corner)
    (P : Set (Bool × Fin m)) (hmissing : e.missing d ⊆ e.unprotected P) :
    2 * (d.unprotected P).ncard + (e.missing d).ncard ≤ 2 * (e.unprotected P).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card, Set.ncard_eq_toFinset_card]
  apply weighted_class_bound _ _ _
    (fun c C : Bool × Set (Fin m) => C.1 = c.1 ∧ C.2 ⊆ c.2)
  · simpa only [Set.Finite.toFinset_subset_toFinset] using hmissing
  · intro c hc d' hd' C hC hCc hCd
    obtain ⟨hc, _⟩ := (Set.Finite.mem_toFinset _).mp hc
    obtain ⟨hd', _⟩ := (Set.Finite.mem_toFinset _).mp hd'
    obtain ⟨hC, _⟩ := (Set.Finite.mem_toFinset _).mp hC
    obtain ⟨x, hx⟩ := class_nonempty hC
    exact class_eq_of_common d hd hc hd' (hCc.1.symm.trans hCd.1) (hCc.2 hx) (hCd.2 hx)
  · intro c hc
    obtain ⟨hc, hprotected⟩ := (Set.Finite.mem_toFinset _).mp hc
    have hcontained {C : Bool × Set (Fin m)} (hC : C ∈ e.classes)
        (hsign : C.1 = c.1) (hsub : C.2 ⊆ c.2) : C ∈ e.unprotected P := by
      refine ⟨hC, ?_⟩
      intro x hx
      rw [hsign]
      exact hprotected x (hsub hx)
    rcases nested_class_containment e d he hd hde hc with
      ⟨C, hC, hsign, hsub, hnC⟩ | ⟨C, hC, D, hD, hCD, hsignC, hsignD, hsubC, hsubD⟩
    · exact Or.inl ⟨C, (Set.Finite.mem_toFinset _).mpr (hcontained hC hsign hsub),
        by simpa only [Set.Finite.mem_toFinset] using hnC, hsign, hsub⟩
    · exact Or.inr ⟨C, (Set.Finite.mem_toFinset _).mpr (hcontained hC hsignC hsubC),
        D, (Set.Finite.mem_toFinset _).mpr (hcontained hD hsignD hsubD),
        hCD, ⟨hsignC, hsubC⟩, ⟨hsignD, hsubD⟩⟩

/-- A common initial missing set pays for all later losses. -/
theorem nested_chain_bound {m k : ℕ} (b : ℕ → Diagram m)
    (hidemp : ∀ j ≤ k, comp (b j) (b j) = b j)
    (hnest : ∀ j < k, (b (j + 1), b j) ∈ nesting m)
    (J : Set (Bool × Set (Fin m)))
    (hJ : ∀ j ≤ k, (b 0).missing (b j) ⊆ J) :
    ∑ j ∈ Finset.range k, ((b j).missing (b (j + 1))).ncard ≤ 2 * J.ncard := by
  classical
  have hbase : ∀ j ≤ k, (b j, b 0) ∈ nesting m := by
    intro j
    induction j with
    | zero => intro _; exact nesting_refl (hidemp 0 (Nat.zero_le _))
    | succ j ih =>
      intro hj
      exact nesting_trans (hnest j (by omega)) (ih (by omega))
  have hchoose : ∀ C : ↥((b 0).classes \ J), ∃ x, x ∈ C.val.2 :=
    fun C => class_nonempty C.property.1
  choose pick hpick using hchoose
  let P : Set (Bool × Fin m) := Set.range (fun C : ↥((b 0).classes \ J) => (C.val.1, pick C))
  have hinit : (b 0).unprotected P = J ∩ (b 0).classes := by
    ext C
    constructor
    · rintro ⟨hC, hCP⟩
      refine ⟨?_, hC⟩
      by_contra hnC
      let C' : ↥((b 0).classes \ J) := ⟨C, hC, hnC⟩
      exact hCP (pick C') (hpick C') ⟨C', rfl⟩
    · rintro ⟨hCJ, hC⟩
      refine ⟨hC, ?_⟩
      intro x hx hxP
      obtain ⟨D, hD⟩ := hxP
      have hsign : C.1 = D.val.1 := (congrArg (fun sx : Bool × Fin m => sx.1) hD).symm
      have hlabel : pick D = x := congrArg (fun sx : Bool × Fin m => sx.2) hD
      have heq : C = D.val := class_eq_of_common (b 0) (hidemp 0 (Nat.zero_le _))
        hC D.property.1 hsign hx (hlabel ▸ hpick D)
      exact D.property.2 (heq ▸ hCJ)
  have hprotected (j : ℕ) (hj : j ≤ k) (sx : Bool × Fin m) (hxP : sx ∈ P) :
      (sx.2, sx.2) ∈ (b 0).surviving (b j) sx.1 ∧
      (sx.2, sx.2) ∈ (b j).recurrence sx.1 := by
    obtain ⟨C, rfl⟩ := hxP
    have hcorner : b j ∈ (b 0).corner := ⟨(hbase j hj).2.2.2, (hbase j hj).2.2.1⟩
    have hnotmissing : C.val ∉ (b 0).missing (b j) := fun h => C.property.2 (hJ j hj h)
    have hloop := (not_mem_missing_iff (b 0) (b j) (hidemp 0 (Nat.zero_le _))
      hcorner C.property.1 (hpick C)).mp hnotmissing
    have hK := loopClosure_subset_of_corner (b 0) (b j) hcorner C.val.1
    refine ⟨hloop, ?_⟩
    exact (show (b 0).surviving (b j) C.val.1 ⊆ (b j).recurrence C.val.1 by
      unfold surviving recurrence; gcongr) hloop
  have hstep (j : ℕ) (hj : j < k) :
      2 * ((b (j + 1)).unprotected P).ncard + ((b j).missing (b (j + 1))).ncard ≤
        2 * ((b j).unprotected P).ncard := by
    have hjk : j ≤ k := hj.le
    have hj1k : j + 1 ≤ k := hj
    obtain ⟨_, _, hnextprev, hprevnext⟩ := hnest j hj
    apply nested_unprotected_loss (b j) (b (j + 1)) (hidemp j hjk)
      (hidemp (j + 1) hj1k) ⟨hprevnext, hnextprev⟩ P
    intro C hC
    refine ⟨hC.1, ?_⟩
    intro x hx hxP
    have hloop := (hprotected (j + 1) hj1k (C.1, x) hxP).1
    have hK := loopClosure_subset_of_corner (b 0) (b j)
      ⟨(hbase j hjk).2.2.2, (hbase j hjk).2.2.1⟩ C.1
    apply hC.2 x hx
    exact (show (b 0).surviving (b (j + 1)) C.1 ⊆ (b j).surviving (b (j + 1)) C.1 by
      unfold surviving; gcongr) hloop
  have hbudget : ∀ n ≤ k,
      (∑ j ∈ Finset.range n, ((b j).missing (b (j + 1))).ncard) +
        2 * ((b n).unprotected P).ncard ≤ 2 * ((b 0).unprotected P).ncard := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hs := hstep n (by omega)
      rw [Finset.sum_range_succ]
      omega
  have hi : ((b 0).unprotected P).ncard ≤ J.ncard := by
    rw [hinit]
    exact Set.ncard_le_ncard Set.inter_subset_left
  have hb := hbudget k le_rfl
  omega

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.nested_chain_bound := @_root_.OAI.TwoWayComplementation.Diagram.nested_chain_bound
