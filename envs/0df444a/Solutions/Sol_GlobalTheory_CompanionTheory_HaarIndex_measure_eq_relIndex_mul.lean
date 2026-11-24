-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:36:59.890102+00:00
-- url     : https://prove2.me/submissions/93cc6957-6eb8-416a-b4d1-e2424033a61f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSubgroupRelIndexMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarIndex
namespace GlobalTheory.CompanionTheory.HaarIndex
theorem _root_.solution : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K →
    MeasurableSet (H : Set G) → H.relIndex K ≠ 0 →
    μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  intro G _ _ _ μ _ H K hHK hH hn
  classical
  set H' := H.addSubgroupOf K
  have hidx : H.relIndex K = H'.index := rfl
  have : H'.FiniteIndex := ⟨by rw [← hidx]; exact hn⟩
  have : Finite (K ⧸ H') := inferInstance
  letI := Fintype.ofFinite (K ⧸ H')
  let o : K ⧸ H' → G := fun q => ((Quotient.out q : K) : G)
  let S : K ⧸ H' → Set G := fun q => (fun x => -o q + x) ⁻¹' (H : Set G)
  have hS : ∀ q, MeasurableSet (S q) := fun q => (measurable_const_add (-o q)) hH
  have hcover : (K : Set G) = ⋃ q, S q := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨((⟨x, hx⟩ : K) : K ⧸ H'), ?_⟩
      have h1 := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' ((⟨x, hx⟩ : K) : K ⧸ H'))
      rw [AddSubgroup.mem_addSubgroupOf] at h1
      simpa [S, o] using h1
    · rintro ⟨q, hq⟩
      have hq' : -o q + x ∈ H := hq
      have hoK : o q ∈ K := (Quotient.out q).2
      have hx : x = o q + (-o q + x) := (add_neg_cancel_left (o q) x).symm
      rw [hx]
      exact K.add_mem hoK (hHK hq')
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro q r hqr
    rw [Function.onFun, Set.disjoint_left]
    intro x hxq hxr
    apply hqr
    have hq' : -o q + x ∈ H := hxq
    have hr' : -o r + x ∈ H := hxr
    have h2 : -o q + o r ∈ H := by
      have := H.add_mem hq' (H.neg_mem hr')
      simpa [neg_add_rev, add_assoc] using this
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' r]
    apply QuotientAddGroup.eq.mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    simpa [o] using h2
  have hμ : ∀ q, μ (S q) = μ (H : Set G) := fun q => MeasureTheory.measure_preimage_add μ (-o q) _
  rw [hcover, MeasureTheory.measure_iUnion hdisj hS, tsum_fintype]
  simp only [hμ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
end GlobalTheory.CompanionTheory.HaarIndex
