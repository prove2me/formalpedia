-- Prove2me | solution 1 for OAI.HyperedgeComparison.exists_unique_firstRoot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:31:15.840711+00:00
-- url     : https://prove2.me/submissions/9e7ea189-15d7-45d1-b35b-c216369852df

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison

open OAI OAI.HyperedgeComparison
universe uE uI uV
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
variable {V : Type uV} {E : Type uE}
theorem hc_adj_symm {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y : V} (h : OAI.HyperedgeComparison.Adj H ω D x y) :
    OAI.HyperedgeComparison.Adj H ω D y x := by
  obtain ⟨e, h1, h2, h3, h4⟩ := h
  exact ⟨e, h1, h2, h4, h3⟩

theorem hc_conn_symm {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y : V} (h : OAI.HyperedgeComparison.Connected H ω D x y) :
    OAI.HyperedgeComparison.Connected H ω D y x := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (hc_adj_symm hab) ih

theorem hc_conn_trans {V E : Type*} {H : OAI.HyperedgeComparison.Hypergraph V E} {ω : E → Bool}
    {D : Set V} {x y z : V} (h : OAI.HyperedgeComparison.Connected H ω D x y)
    (h' : OAI.HyperedgeComparison.Connected H ω D y z) :
    OAI.HyperedgeComparison.Connected H ω D x z :=
  Relation.ReflTransGen.trans h h'

theorem solution {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (D : Set V) (i : Fin n) : ∃! k, firstRoot H x ω D k i := by
  classical
  have hne : ∃ j, Connected H ω D (x j) (x i) := ⟨i, .refl⟩
  let k := Nat.find (p := fun m => ∃ h : m < n, Connected H ω D (x ⟨m, h⟩) (x i))
    ⟨i.1, i.2, .refl⟩
  have hk : ∃ h : k < n, Connected H ω D (x ⟨k, h⟩) (x i) := Nat.find_spec (p := fun m => ∃ h : m < n, Connected H ω D (x ⟨m, h⟩) (x i)) ⟨i.1, i.2, .refl⟩
  have hmin : ∀ j : Fin n, Connected H ω D (x j) (x i) → k ≤ j.1 := fun j hj =>
    Nat.find_min' (p := fun m => ∃ h : m < n, Connected H ω D (x ⟨m, h⟩) (x i)) _ ⟨j.2, hj⟩
  obtain ⟨hkn, hkc⟩ := hk
  refine ⟨⟨k, hkn⟩, ⟨?_, hkc⟩, ?_⟩
  · rw [Set.disjoint_left]
    rintro y hy ⟨j, hj, rfl⟩
    have := hmin j (hc_conn_trans (hc_conn_symm hy) hkc)
    have : j.1 < k := hj
    omega
  · rintro k' ⟨hd, hc⟩
    have h1 := hmin k' hc
    by_contra hne'
    have hlt : (⟨k, hkn⟩ : Fin n) < k' := by
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact absurd (Fin.ext h.symm) hne'
    exact Set.disjoint_left.mp hd (hc_conn_trans hc (hc_conn_symm hkc) : _) ⟨_, hlt, rfl⟩

