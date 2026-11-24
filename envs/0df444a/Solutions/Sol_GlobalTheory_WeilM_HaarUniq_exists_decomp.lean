-- Prove2me | solution 1 for GlobalTheory.WeilM.HaarUniq.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:06.948146+00:00
-- url     : https://prove2.me/submissions/538b7415-d179-4e41-8375-0b02acf43c3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.WeilM GlobalTheory.WeilM.HaarUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
open MeasureTheory Filter Topology
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
namespace GlobalTheory.WeilM.HaarUniq
namespace _root_.GlobalTheory.WeilM.HaarUniq
theorem _root_.solution [IsTopologicalAddGroup V] (K : OpenAddSubgroup V)
    {φ : V → ℂ} (hc : HasCompactSupport φ) (hinv : ∀ k ∈ K, ∀ x, φ (x + k) = φ x) :
    ∃ S : Finset (V ⧸ K.toAddSubgroup),
      φ = ∑ q ∈ S, φ q.out • (fun x => Set.indicator (K : Set V) (fun _ => (1 : ℂ)) (x + -q.out)) := by
  classical
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun p : V => (fun y => -p + y) ⁻¹' (K : Set V))
    (fun p => K.isOpen.preimage (continuous_const_add (-p)))
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simpa using K.zero_mem⟩)
  refine ⟨t.image (QuotientAddGroup.mk : V → V ⧸ K.toAddSubgroup), ?_⟩
  funext x
  have hmem : ∀ q : V ⧸ K.toAddSubgroup,
      (x + -q.out ∈ (K : Set V)) ↔ q = (QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup) := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, add_comm]
    simp
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_apply, hmem,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hS
  · have h := QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup)
    rw [QuotientAddGroup.eq] at h
    have := hinv _ h ((QuotientAddGroup.mk x : V ⧸ K.toAddSubgroup).out)
    rw [add_neg_cancel_left] at this
    exact this
  · apply image_eq_zero_of_notMem_tsupport
    intro hx
    apply hS
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine Finset.mem_image.2 ⟨p, hp, ?_⟩
    rw [QuotientAddGroup.eq]
    simpa using hxp
end _root_.GlobalTheory.WeilM.HaarUniq
end GlobalTheory.WeilM.HaarUniq
