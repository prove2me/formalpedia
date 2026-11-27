-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Hgt.exists_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:07.104064+00:00
-- url     : https://prove2.me/submissions/890ff9fd-4bef-45f6-acc4-dba491c6a09d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_HgtCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Hgt
open scoped NNReal ENNReal
open MeasureTheory Topology
namespace GlobalTheory.ThK.Dbl.Hgt
theorem _root_.solution {A : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (ν : Measure A) [ν.IsAddLeftInvariant]
    {X V Z : Set A} (hV : MeasurableSet V) (h0 : ν V ≠ 0) (hZ : ν Z ≠ ⊤) (hXZ : ∀ x ∈ X, ∀ v ∈ V, x + v ∈ Z) :
    ∃ s : Finset A, s.card * ν V ≤ ν Z ∧ ∀ x ∈ X, ∃ y ∈ s, ∃ v ∈ V, ∃ v' ∈ V, x - y = v - v' := by
  classical
  by_contra! h
  let T : A → Set A := fun x => (fun a => -x + a) ⁻¹' V
  have bd : ∀ s : Finset A, (s : Set A) ⊆ X → (s : Set A).PairwiseDisjoint T → s.card * ν V ≤ ν Z := fun s h1 h2 => by
    have := measure_biUnion_finset (μ := ν) h2 fun b _ => measurable_const_add _ hV
    simp only [T, measure_preimage_add, Finset.sum_const, nsmul_eq_mul] at this
    rw [← this]
    exact measure_mono (Set.iUnion₂_subset fun x hx a ha => by simpa using hXZ x (h1 hx) _ ha)
  obtain ⟨v₀, hv₀⟩ := nonempty_of_measure_ne_zero h0
  have key : ∀ k : ℕ, ∃ s : Finset A, s.card = k ∧ (s : Set A) ⊆ X ∧ (s : Set A).PairwiseDisjoint T := fun k => by
    induction k with
    | zero => exact ⟨∅, rfl, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨s, rfl, h1, h2⟩ := ih
      obtain ⟨x, hx, hx'⟩ := h s (bd s h1 h2)
      refine ⟨insert x s, Finset.card_insert_of_notMem fun hs => hx' x hs v₀ hv₀ v₀ hv₀ (by simp), ?_, ?_⟩
      · rw [Finset.coe_insert]; exact Set.insert_subset hx h1
      · rw [Finset.coe_insert]
        exact h2.insert fun y hy _ => Set.disjoint_left.2 fun a ha hb => hx' y hy (-y + a) hb (-x + a) ha (by rw [add_sub_add_right_eq_sub, neg_sub_neg])
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 hZ
  obtain ⟨s, rfl, h1, h2⟩ := key N
  exact hN.not_ge (bd s h1 h2)
end GlobalTheory.ThK.Dbl.Hgt
