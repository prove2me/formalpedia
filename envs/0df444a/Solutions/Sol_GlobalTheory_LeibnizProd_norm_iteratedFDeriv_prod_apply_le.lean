-- Prove2me | solution 1 for GlobalTheory.LeibnizProd.norm_iteratedFDeriv_prod_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:02:50.442674+00:00
-- url     : https://prove2.me/submissions/7dd35e7d-b6be-4010-a71b-ddab3f11a0ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivProdCoordLeLeibniz
import Theorems.Thm_GlobalTheory_LeibnizProd_countPerms_le_factorial
import Theorems.Thm_GlobalTheory_LeibnizProd_sum_sym_le
import Theorems.Thm_GlobalTheory_LeibnizProd_norm_iteratedFDeriv_comp_apply_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.LeibnizProd
namespace GlobalTheory.LeibnizProd
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (g : ι → ℂ → ℂ) (U : ι → Set ℂ), (∀ i, IsOpen (U i)) →
    (∀ i, ContDiffOn ℝ ∞ (g i) (U i)) → ∀ z : ι → ℂ, (∀ i, z i ∈ U i) → ∀ n : ℕ,
      ‖iteratedFDeriv ℝ n (fun z : ι → ℂ => ∏ i, g i (z i)) z‖ ≤
        n.factorial * ∏ i, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g i) (z i)‖ := by
  intro ι _ g U hU hg z hz n
  classical
  set V : Set (ι → ℂ) := ⋂ i, (fun w : ι → ℂ => w i) ⁻¹' U i with hVdef
  have hV : IsOpen V := isOpen_iInter_of_finite fun i => (hU i).preimage (continuous_apply i)
  have hzV : z ∈ V := Set.mem_iInter.2 hz
  have hf : ∀ i ∈ (Finset.univ : Finset ι), ContDiffOn ℝ ∞ (fun w : ι → ℂ => g i (w i)) V := by
    intro i _
    exact (hg i).comp (contDiff_apply ℝ ℂ i).contDiffOn (fun w hw => Set.mem_iInter.1 hw i)
  have key := norm_iteratedFDerivWithin_prod_le (u := Finset.univ) hf hV.uniqueDiffOn hzV (n := n)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen n hV hzV] at key
  refine key.trans ?_
  calc _ ≤ ∑ p ∈ (Finset.univ : Finset ι).sym n, (n.factorial : ℝ) *
        ∏ j, ‖iteratedFDeriv ℝ ((p : Multiset ι).count j) (g j) (z j)‖ := by
        gcongr with p hp j
        · exact_mod_cast countPerms_le_factorial p
        · rw [iteratedFDerivWithin_of_isOpen _ hV hzV]
          exact norm_iteratedFDeriv_comp_apply_le (g j) (U j) (hU j) (hg j) j z (hz j) _
    _ ≤ _ := by
        rw [← Finset.mul_sum]
        gcongr
        exact sum_sym_le n (fun j k => ‖iteratedFDeriv ℝ k (g j) (z j)‖) (fun _ _ => norm_nonneg _)
end GlobalTheory.LeibnizProd
