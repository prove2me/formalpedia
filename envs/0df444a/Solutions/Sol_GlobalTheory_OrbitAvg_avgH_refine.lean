-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.avgH_refine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:30.337266+00:00
-- url     : https://prove2.me/submissions/4e12805e-00e0-48d2-b124-7048a846376c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
import Theorems.Thm_GlobalTheory_OrbitAvg_cv_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)
namespace GlobalTheory.OrbitAvg
theorem _root_.solution {H H' : Subgroup L} {x : V} (hle : H' ≤ H) (hH : H ≤ stab π L x)
    [H'.FiniteIndex] : avgH π L H' x = avgH π L H x := by
  classical
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_le hle
  have hrel := Subgroup.relIndex_mul_index hle
  haveI : (H'.subgroupOf H).FiniteIndex := by
    refine ⟨?_⟩
    intro h0
    have h4 : H'.index = 0 := by rw [← hrel]; simp [Subgroup.relIndex, h0]
    exact Subgroup.FiniteIndex.index_ne_zero h4
  haveI := Fintype.ofFinite (L ⧸ H)
  haveI := Fintype.ofFinite (L ⧸ H')
  haveI := Fintype.ofFinite (H ⧸ H'.subgroupOf H)
  unfold avgH
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let e := Subgroup.quotientEquivProdOfLE hle
  have hcv : ∀ q : L ⧸ H', cv π L H' x q = cv π L H x (e q).1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cv_mk π L (le_trans hle hH), show (e (QuotientGroup.mk a)).1 = QuotientGroup.mk a from rfl,
        cv_mk π L hH]
  have hsum : ∑ q : L ⧸ H', cv π L H' x q =
      (Fintype.card (H ⧸ H'.subgroupOf H) : ℂ) • ∑ q : L ⧸ H, cv π L H x q := by
    simp_rw [hcv]
    rw [Equiv.sum_comp e (fun p => cv π L H x p.1), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ]
    rw [Finset.smul_sum]
    simp [Nat.cast_smul_eq_nsmul]
  have hc : Fintype.card (H ⧸ H'.subgroupOf H) = H'.relIndex H := by
    rw [Fintype.card_eq_nat_card]; rfl
  rw [hsum, hc, ← hrel, smul_smul]
  congr 1
  have h5 : (H'.relIndex H : ℂ) ≠ 0 := by
    have := Subgroup.FiniteIndex.index_ne_zero (H := H'.subgroupOf H)
    exact_mod_cast this
  push_cast
  field_simp
end GlobalTheory.OrbitAvg
