-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Topology.exists_finset_transversal_of_isCompact_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:35.564912+00:00
-- url     : https://prove2.me/submissions/365b0c5f-5a35-41d6-a7bf-40ef3445c1cc

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCosetRepsOpenInCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Topology
namespace GlobalTheory.CompanionTheory.Topology
theorem _root_.solution
    (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (A L : AddSubgroup X) (hA : IsCompact (A : Set X)) (hL : IsOpen (L : Set X)) (_hLA : L ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ L) := by
  classical
  have hcoset : ∀ x : X, ((↑) : X → X ⧸ L) '' (Homeomorph.addLeft x '' (L : Set X)) =
      {(x : X ⧸ L)} := by
    intro x
    ext q
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      rw [Set.mem_singleton_iff, QuotientAddGroup.eq, Homeomorph.coe_addLeft]
      simpa using L.neg_mem hl
    · rintro rfl
      exact ⟨x, ⟨0, L.zero_mem, by simp⟩, rfl⟩
  have hdisc : DiscreteTopology (X ⧸ L) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [← hcoset x]
      exact QuotientAddGroup.isOpenMap_coe _ ((Homeomorph.addLeft x).isOpenMap _ hL)
  have hfin : (((↑) : X → X ⧸ L) '' (A : Set X)).Finite :=
    (hA.image continuous_quotient_mk').finite_of_discrete
  have hout : ∀ q : X ⧸ L, ((q.out : X) : X ⧸ L) = q := fun q => Quotient.out_eq q
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image] at ht
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := ht
    have h1 : -(a : X ⧸ L).out + a ∈ L := QuotientAddGroup.eq.1 (hout _)
    have h2 : (a : X ⧸ L).out = a - (-(a : X ⧸ L).out + a) := by abel
    rw [h2]
    exact A.sub_mem ha (_hLA h1)
  · intro a ha
    have hmem : (a : X ⧸ L).out ∈ hfin.toFinset.image Quotient.out :=
      Finset.mem_image.2 ⟨(a : X ⧸ L), (Set.Finite.mem_toFinset hfin).2 ⟨a, ha, rfl⟩, rfl⟩
    have hrel : -(a : X ⧸ L).out + a ∈ L := QuotientAddGroup.eq.1 (hout _)
    refine ⟨(a : X ⧸ L).out, ⟨hmem, by rw [sub_eq_neg_add]; exact hrel⟩, ?_⟩
    rintro t' ⟨ht', hat'⟩
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image] at ht'
    obtain ⟨q', -, rfl⟩ := ht'
    have hq : q' = (a : X ⧸ L) := by
      rw [← hout q', QuotientAddGroup.eq]
      rw [sub_eq_neg_add] at hat'
      exact hat'
    rw [hq]
end GlobalTheory.CompanionTheory.Topology
