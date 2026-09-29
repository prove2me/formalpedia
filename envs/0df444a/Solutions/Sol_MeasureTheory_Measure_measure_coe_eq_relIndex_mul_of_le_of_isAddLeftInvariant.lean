-- Prove2me | solution 1 for MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a0fe4edd-7613-5ddb-ac6b-96cbb55452a7

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.GroupTheory.Index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant

set_option autoImplicit false

open MeasureTheory

theorem solution
    {G : Type*} [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    (H H' : AddSubgroup G) (hle : H ≤ H') (hH : MeasurableSet (H : Set G)) (hfin : H.relIndex H' ≠ 0) :
    μ (H' : Set G) = (H.relIndex H' : ENNReal) * μ (H : Set G) := by
  classical
  set K : AddSubgroup H' := H.addSubgroupOf H' with hK
  haveI : K.FiniteIndex := ⟨hfin⟩
  haveI : Finite (H' ⧸ K) := AddSubgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (H' ⧸ K) := Fintype.ofFinite _

  let rep : H' ⧸ K → G := fun c => ((Quotient.out c : H') : G)
  let C : H' ⧸ K → Set G := fun c => (fun x : G => -(rep c) + x) ⁻¹' (H : Set G)
  have hmemC : ∀ (c : H' ⧸ K) (x : G), x ∈ C c ↔ -(rep c) + x ∈ H := fun c x => Iff.rfl
  have hrel : ∀ a b : H', (QuotientAddGroup.mk (s := K) a = QuotientAddGroup.mk b) ↔ -(a : G) + b ∈ H := by
    intro a b
    rw [QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]
  have hcover : (H' : Set G) = ⋃ c, C c := by
    ext x
    rw [Set.mem_iUnion]
    constructor
    · intro hx
      refine ⟨QuotientAddGroup.mk (s := K) ⟨x, hx⟩, ?_⟩
      rw [hmemC]
      have h := QuotientAddGroup.out_eq' (QuotientAddGroup.mk (s := K) (⟨x, hx⟩ : H'))
      exact (hrel _ _).mp h
    · rintro ⟨c, hc⟩
      rw [hmemC] at hc
      have hg : rep c ∈ H' := ((Quotient.out c : H')).2
      have hx : x = rep c + (-(rep c) + x) := (add_neg_cancel_left (rep c) x).symm
      rw [SetLike.mem_coe, hx]
      exact H'.add_mem hg (hle hc)
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro c₁ c₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x h₁ h₂
    apply hne
    rw [hmemC] at h₁ h₂
    have hmem : -(rep c₁) + rep c₂ ∈ H := by
      have : -(rep c₁) + rep c₂ = (-(rep c₁) + x) + -(-(rep c₂) + x) := by
        rw [neg_add_rev, neg_neg, add_assoc, add_neg_cancel_left]
      rw [this]
      exact H.add_mem h₁ (H.neg_mem h₂)
    rw [← QuotientAddGroup.out_eq' c₁, ← QuotientAddGroup.out_eq' c₂]
    exact (hrel _ _).mpr hmem
  have hmeas : ∀ c, MeasurableSet (C c) := fun c => hH.preimage (measurable_const_add _)
  have hμC : ∀ c, μ (C c) = μ (H : Set G) := fun c => measure_preimage_add μ _ _
  rw [hcover, measure_iUnion hdisj hmeas, tsum_fintype, Finset.sum_congr rfl (fun c _ => hμC c), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [AddSubgroup.relIndex, AddSubgroup.index, ← hK, Nat.card_eq_fintype_card]

end S_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant
end P2MW
export P2MW.S_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant (solution)
