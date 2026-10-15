-- Prove2me | solution 1 for OAI.TwoWayComplementation.exists_nested_chain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:42:15.787913+00:00
-- url     : https://prove2.me/submissions/ec434c58-c73f-40ff-a461-6db394129560

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean:L34-L97
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.exists_nested_chain. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_missing_comp
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_chain_bound

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

theorem missing_pow_succ {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (k : ℕ) : e.missing (z ^ (k + 1)) ⊆ e.missing z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (missing_comp e _ z he (corner_pow_succ hz k) hz).trans
      (Set.union_subset ih Set.Subset.rfl)

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

/-- A nested chain with a common missing-set budget. -/
theorem exists_nested_chain {A : Type*} [Monoid A] [Finite A] {m k : ℕ}
    (ι : A →ₙ* Diagram m) (b0 : A) (hb0 : IsIdempotentElem b0) (g : ℕ → A)
    (J : Set (Bool × Set (Fin m)))
    (hg : ∀ j < k, ι (g j) ∈ (ι b0).corner ∧ (ι b0).missing (ι (g j)) ⊆ J) :
    ∃ b : ℕ → A, b 0 = b0 ∧
      (∀ j, IsIdempotentElem (b j)) ∧
      (∀ j, ∃ n : ℕ, b (j + 1) = (b j * g j * b j) ^ (n + 1)) ∧
      (∀ j, (ι (b (j + 1)), ι (b j)) ∈ Diagram.nesting m) ∧
      (∀ j ≤ k, (ι b0).missing (ι (b j)) ⊆ J) ∧
      ∑ j ∈ Finset.range k, ((ι (b j)).missing (ι (b (j + 1)))).ncard ≤ 2 * J.ncard := by
  classical
  choose power hpower using fun a : A => finite_idempotent_pow a
  let b : ℕ → A := Nat.rec b0 (fun j prev => (prev * g j * prev) ^ power (prev * g j * prev))
  have hzero : b 0 = b0 := rfl
  have hsucc (j : ℕ) : b (j + 1) = (b j * g j * b j) ^ power (b j * g j * b j) := rfl
  have hidemp (j : ℕ) : IsIdempotentElem (b j) := by
    cases j with
    | zero => exact hb0
    | succ j => exact (hpower _).2
  have hstep (j : ℕ) : ∃ n : ℕ, b (j + 1) = (b j * g j * b j) ^ (n + 1) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (hpower (b j * g j * b j)).1.ne'
    exact ⟨n, by rw [hsucc, hn]⟩
  have hmapidemp (j : ℕ) : Diagram.comp (ι (b j)) (ι (b j)) = ι (b j) := by
    exact (map_mul ι (b j) (b j)).symm.trans (congrArg ι (hidemp j).eq)
  have hnest (j : ℕ) : (ι (b (j + 1)), ι (b j)) ∈ Diagram.nesting m := by
    obtain ⟨n, hn⟩ := hstep j
    have hcorner : ι (b j * g j * b j) ∈ (ι (b j)).corner := by
      constructor
      · change ι (b j) * ι (b j * g j * b j) = _
        rw [← map_mul, ← mul_assoc, ← mul_assoc, (hidemp j).eq]
      · change ι (b j * g j * b j) * ι (b j) = _
        rw [← map_mul, mul_assoc, (hidemp j).eq]
    have hpow := Diagram.corner_pow_succ hcorner n
    rw [← map_positive_pow, ← hn] at hpow
    exact ⟨hmapidemp (j + 1), hmapidemp j, hpow.2, hpow.1⟩
  have hbase (j : ℕ) : (ι (b j), ι b0) ∈ Diagram.nesting m := by
    induction j with
    | zero => exact Diagram.nesting_refl (hmapidemp 0)
    | succ j ih => exact Diagram.nesting_trans (hnest j) ih
  have hbudget : ∀ j ≤ k, (ι b0).missing (ι (b j)) ⊆ J := by
    intro j
    induction j with
    | zero => intro _; rw [hzero, Diagram.missing_self]; exact Set.empty_subset _
    | succ j ih =>
      intro hj
      obtain ⟨n, hn⟩ := hstep j
      have hb : ι (b j) ∈ (ι b0).corner := ⟨(hbase j).2.2.2, (hbase j).2.2.1⟩
      have hgj := (hg j (by omega)).1
      have hbg := Diagram.corner_comp hb hgj
      have hpow := Diagram.missing_pow_succ (ι b0) (ι (b j * g j * b j))
        (hmapidemp 0) (by rw [map_mul, map_mul]; exact Diagram.corner_comp hbg hb) n
      rw [← map_positive_pow, ← hn] at hpow
      apply hpow.trans
      have hfirst := Diagram.missing_comp (ι b0) (ι (b j)) (ι (g j)) (hmapidemp 0) hb hgj
      have hsecond := Diagram.missing_comp (ι b0) (ι (b j) * ι (g j)) (ι (b j))
        (hmapidemp 0) hbg hb
      rw [map_mul, map_mul]
      exact hsecond.trans
        (Set.union_subset (hfirst.trans (Set.union_subset (ih (by omega)) (hg j (by omega)).2))
          (ih (by omega)))
  exact ⟨b, hzero, hidemp, hstep, hnest, hbudget,
    Diagram.nested_chain_bound (fun j => ι (b j)) (fun j _ => hmapidemp j)
      (fun j _ => hnest j) J (by simpa only [hzero] using hbudget)⟩

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.exists_nested_chain := @_root_.OAI.TwoWayComplementation.exists_nested_chain
