-- Prove2me | solution 1 for GlobalTheory.BI.one_mem_of_integral_combination
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:21:12.598809+00:00
-- url     : https://prove2.me/submissions/bb5cd311-4d3e-4b31-9f48-1be156866b7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsIntRelationOfIsIntegralRelationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_VirtualCharacterInnerEqIntMulCardStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemVirtualCharactersOfIntegralCombination
import Theorems.Thm_GlobalTheory_BI_isChar_one
import Theorems.Thm_GlobalTheory_T_exists_int_relation_of_isIntegral_relation
import Theorems.Thm_GlobalTheory_T_virtualCharacter_inner_eq_int_mul_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (S : AddSubgroup (G → ℂ)), S ≤ Virt ℂ ℂ G → ∀ (ι : Type) [Fintype ι] (r : ι → ℂ) (s : ι → G → ℂ), (∀ i, IsIntegral ℤ (r i)) → (∀ i, s i ∈ S) → (∀ g, ∑ i, r i * s i g = 1) → (1 : G → ℂ) ∈ S := by
  intro G _ _ S hS ι _ r s hr hs hsum
  classical
  have := Fintype.ofFinite G
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_int_relation_of_isIntegral_relation ι r hr
  have hone : (1 : G → ℂ) ∈ Virt ℂ ℂ G := AddSubgroup.subset_closure (isChar_one ℂ ℂ G)
  have hcomb : (∑ i, c i • s i) ∈ S := S.sum_mem fun i _ => S.zsmul_mem (hs i) (c i)
  set f : G → ℂ := (∑ i, c i • s i) - 1 with hf
  have hfV : f ∈ Virt ℂ ℂ G := (Virt ℂ ℂ G).sub_mem (hS hcomb) hone
  have hN : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  choose m hm using fun i => GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card G (s i) f (hS (hs i)) hfV
  obtain ⟨d, hd⟩ := GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card G 1 f hone hfV
  simp only [finsum_eq_sum_of_fintype] at hm hd
  have h1 : ∑ i, r i * (m i : ℂ) = d := by
    apply mul_right_cancel₀ hN
    rw [← hd, Finset.sum_mul]
    simp only [mul_assoc, ← hm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [← mul_assoc, ← Finset.sum_mul, hsum g, Pi.one_apply]
  have h2 : ∑ i, (c i : ℂ) * (m i : ℂ) = d := by exact_mod_cast hc m d h1
  have hfg : ∀ g, f g = ∑ i, (c i : ℂ) * s i g - 1 := by
    intro g
    simp [hf, Finset.sum_apply]
  have h3 : ∑ g, f g * star (f g) = 0 := by
    have e : ∀ g, f g * star (f g) = ∑ i, (c i : ℂ) * (s i g * star (f g)) - (1 : G → ℂ) g * star (f g) := by
      intro g
      conv_lhs => enter [1]; rw [hfg g]
      simp only [sub_mul, Finset.sum_mul, mul_assoc, Pi.one_apply]
    simp only [e, Finset.sum_sub_distrib]
    rw [Finset.sum_comm, hd, ← h2, Finset.sum_mul, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hm, mul_assoc]
  have h4 : ∑ g, Complex.normSq (f g) = 0 := by
    have : ((∑ g, Complex.normSq (f g) : ℝ) : ℂ) = 0 := by
      rw [← h3]; push_cast
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Complex.mul_conj]; rfl
    exact_mod_cast this
  have h5 : f = 0 := by
    funext g
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => Complex.normSq_nonneg (f g))).1 h4 g (Finset.mem_univ g)
    exact Complex.normSq_eq_zero.1 this
  have : (∑ i, c i • s i) = 1 := sub_eq_zero.1 (hf.symm.trans h5)
  exact this ▸ hcomb
end GlobalTheory.BI
