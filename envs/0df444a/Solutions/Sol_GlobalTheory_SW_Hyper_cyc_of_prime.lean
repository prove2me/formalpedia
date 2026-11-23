-- Prove2me | solution 1 for GlobalTheory.SW.Hyper.cyc_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:09.164013+00:00
-- url     : https://prove2.me/submissions/6c499919-6ec2-40d1-804b-a4825ab9e463

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Hyper
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
namespace GlobalTheory.SW.Hyper
theorem _root_.solution (N : Submodule O M) {q : ℕ} (hq : q.Prime)
    (h : N.toAddSubgroup.index = q) : ∃ v, v ∉ N ∧ ∀ x, ∃ r : O, x - r • v ∈ N := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (M ⧸ N.toAddSubgroup) = q := by
    rw [← AddSubgroup.index_eq_card]; exact h
  have hne : N.toAddSubgroup ≠ ⊤ := by
    intro ht
    rw [ht, AddSubgroup.index_top] at h
    exact hq.one_lt.ne h
  obtain ⟨v, hv⟩ : ∃ v, v ∉ N := by
    by_contra hn
    push Not at hn
    exact hne (eq_top_iff.mpr fun x _ => hn x)
  refine ⟨v, hv, fun x => ?_⟩
  have hv0 : (QuotientAddGroup.mk v : M ⧸ N.toAddSubgroup) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]; exact hv
  have hx : (QuotientAddGroup.mk x : M ⧸ N.toAddSubgroup) ∈
      AddSubgroup.zmultiples (QuotientAddGroup.mk v) := mem_zmultiples_of_prime_card hcard hv0
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  refine ⟨(n : O), ?_⟩
  rw [Int.cast_smul_eq_zsmul]
  have h2 : (QuotientAddGroup.mk (n • v) : M ⧸ N.toAddSubgroup) = QuotientAddGroup.mk x := by
    rw [QuotientAddGroup.mk_zsmul]; exact hn
  rw [QuotientAddGroup.eq] at h2
  rw [sub_eq_neg_add]
  exact h2
end GlobalTheory.SW.Hyper
