-- Prove2me | solution 1 for GlobalTheory.CharForm.apply_eq_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:54.49784+00:00
-- url     : https://prove2.me/submissions/f1b3f5a4-8aee-47c7-92a9-a7f5f054b3de

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEqMulApplyZero
import Theorems.Thm_GlobalTheory_CharForm_cosetInd_mem_SB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
noncomputable section
open scoped Classical Topology
open GlobalTheory GlobalTheory.CharForm
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
namespace GlobalTheory.CharForm
theorem _root_.solution {C : Set (X → ℂ)} (a : (X → ℂ) →ₗ[ℂ] ℂ)
    (ha : ∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g)
    (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X))
    (hUk : ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) (hper : ∀ x, ∀ u ∈ U, g (x + u) = g x) :
    a g = g 0 * a (cosetInd U 0) := by
  haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo
  have hout : ∀ x : X, g ((x : X ⧸ U).out) = g x := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add U x
    rw [hh]; exact hper x h h.2
  have hfin : (QuotientAddGroup.mk '' tsupport g : Set (X ⧸ U)).Finite :=
    (hg.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T : Finset (X ⧸ U) := insert 0 hfin.toFinset with hT
  have hsum : g = ∑ q ∈ T, g q.out • cosetInd U q := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cosetInd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · exact (hout x).symm
    · apply image_eq_zero_of_notMem_tsupport
      intro hxs
      exact hx (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr ⟨x, hxs, rfl⟩))
  have hkill : ∀ q : X ⧸ U, q ≠ 0 → a (cosetInd U q) = 0 := by
    intro q hq
    have hx₀ : q.out ∉ U := by
      intro hm
      apply hq
      rw [← QuotientAddGroup.out_eq' q]
      exact (QuotientAddGroup.eq_zero_iff _).mpr hm
    obtain ⟨χ, hχC, hχU, hχ1⟩ := hUk _ hx₀
    have hmul : (fun x => χ x * cosetInd U q x) = χ q.out • cosetInd U q := by
      funext x
      simp only [cosetInd, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      split_ifs with hxq
      · have hm : -q.out + x ∈ U := by
          rw [← QuotientAddGroup.out_eq' q] at hxq
          exact QuotientAddGroup.eq.mp hxq.symm
        have := hχU _ hm
        rwa [add_neg_cancel_left] at this
      · rfl
    have e := ha χ hχC _ (cosetInd_mem_SB U hUo hUc q)
    rw [hmul, map_smul, smul_eq_mul] at e
    have : (χ q.out - 1) * a (cosetInd U q) = 0 := by rw [sub_mul, e, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hχ1)
  conv_lhs => rw [hsum]
  rw [map_sum, Finset.sum_eq_single (0 : X ⧸ U)]
  · rw [map_smul, smul_eq_mul, ← QuotientAddGroup.mk_zero, hout]
  · intro q _ hq
    rw [map_smul, hkill q hq, smul_zero]
  · intro h
    exact absurd (Finset.mem_insert_self _ _) h
end GlobalTheory.CharForm
