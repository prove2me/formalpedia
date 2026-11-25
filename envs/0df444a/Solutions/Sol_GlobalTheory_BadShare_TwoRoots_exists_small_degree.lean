-- Prove2me | solution 1 for GlobalTheory.BadShare.TwoRoots.exists_small_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:04:47.532776+00:00
-- url     : https://prove2.me/submissions/f44614c2-ebc2-4fbe-9b92-c45a1b1061ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLe
import Theorems.Thm_GlobalTheory_BadShare_TwoRoots_pow_card_pow_natDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.TwoRoots
namespace GlobalTheory.BadShare.TwoRoots
theorem _root_.solution {g : ℕ} [Fact g.Prime] {x y : AlgebraicClosure (ZMod g)} {L : ℕ}
    (hm : minpoly (ZMod g) x = minpoly (ZMod g) y) (hxy : x ≠ y) (h : x ^ L = y ^ L) :
    ∃ e, 1 ≤ e ∧ e ≤ (minpoly (ZMod g) x).natDegree / 2 ∧ (x ^ L) ^ (g ^ e) = x ^ L := by
  have hi : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hz : IsIntegral (ZMod g) (x ^ L) := Algebra.IsIntegral.isIntegral _
  haveI := IntermediateField.adjoin.finiteDimensional hi
  haveI := IntermediateField.adjoin.finiteDimensional hz
  refine ⟨(minpoly (ZMod g) (x ^ L)).natDegree, minpoly.natDegree_pos hz, ?_, pow_card_pow_natDegree _⟩
  have hle : IntermediateField.adjoin (ZMod g) {x ^ L} ≤ IntermediateField.adjoin (ZMod g) {x} := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) _
  have hdvd := IntermediateField.finrank_dvd_of_le_right hle
  have hne : Module.finrank (ZMod g) (IntermediateField.adjoin (ZMod g) {x ^ L}) ≠
      Module.finrank (ZMod g) (IntermediateField.adjoin (ZMod g) {x}) := by
    intro he
    have heq := IntermediateField.eq_of_le_of_finrank_eq hle he
    obtain ⟨σ, hσ⟩ := IsConjRoot.exists_algEquiv (show IsConjRoot (ZMod g) y x from hm.symm)
    have hx : x ∈ IntermediateField.adjoin (ZMod g) {x ^ L} := heq ▸ IntermediateField.mem_adjoin_simple_self _ _
    have hfix : IntermediateField.adjoin (ZMod g) {x ^ L} ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [IntermediateField.adjoin_simple_le_iff, ← IntermediateField.adjoin_simple_le_iff,
        IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.mem_fixingSubgroup_iff]
      intro t ht
      induction ht using IntermediateField.adjoin_induction with
      | mem t ht => rw [Set.mem_singleton_iff.1 ht, map_pow, hσ, h]
      | algebraMap t => exact σ.commutes t
      | add a b _ _ ha hb => rw [map_add, ha, hb]
      | inv a _ ha => rw [map_inv₀, ha]
      | mul a b _ _ ha hb => rw [map_mul, ha, hb]
    have := (IntermediateField.mem_fixedField_iff _ _).1 (hfix hx) σ (Subgroup.mem_zpowers σ)
    exact hxy (this.symm.trans hσ)
  rw [IntermediateField.adjoin.finrank hi, IntermediateField.adjoin.finrank hz] at hdvd hne
  obtain ⟨c, hc⟩ := hdvd
  have hpos := minpoly.natDegree_pos hi
  rw [Nat.le_div_iff_mul_le two_pos, hc]
  apply Nat.mul_le_mul_left
  rcases c with _ | _ | c
  · omega
  · omega
  · omega
end GlobalTheory.BadShare.TwoRoots
