-- Prove2me | solution 1 for GlobalTheory.RegBound.finrank_extSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:55:15.058495+00:00
-- url     : https://prove2.me/submissions/795c96f3-1882-493b-a169-2c1ac06a110a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
import Theorems.Thm_GlobalTheory_RegBound_contr_smul_map
import Theorems.Thm_GlobalTheory_RegBound_contr_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.RegBound
theorem _root_.solution (W : Submodule K (MvPolynomial σ K)) [Module.Finite K W] :
    finrank L (extSub L W) = finrank K W := by
  classical
  let w := Module.finBasis K W
  let v : Fin (finrank K W) → MvPolynomial σ L := fun i => map (algebraMap K L) (w i)
  have hli : LinearIndependent L v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro φ
    have hw : LinearIndependent K fun i => (w i : MvPolynomial σ K) :=
      w.linearIndependent.map' W.subtype W.ker_subtype
    refine Fintype.linearIndependent_iff.1 hw (fun i => φ (c i)) ?_ i
    ext m
    have := congrArg (fun F => φ (coeff m F)) hc
    simp only [coeff_sum, map_sum, coeff_zero, map_zero] at this ⊢
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← coeff_contr, contr_smul_map]
  have hsp : extSub L W = Submodule.span L (Set.range v) := by
    apply le_antisymm
    · intro F hF
      let b := Basis.ofVectorSpace K L
      have : F = ∑ j ∈ F.support.biUnion fun m => (b.repr (coeff m F)).support,
          b j • map (algebraMap K L) (contr (b.coord j) F) := by
        ext m
        simp only [coeff_sum, coeff_smul, coeff_map, coeff_contr, smul_eq_mul]
        conv_lhs => rw [← b.linearCombination_repr (coeff m F), Finsupp.linearCombination_apply]
        rw [Finsupp.sum_of_support_subset (s := F.support.biUnion
          fun m => (b.repr (coeff m F)).support) _ _ _ (by simp)]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.smul_def, mul_comm, Basis.coord_apply]
        · by_cases hm : m ∈ F.support
          · exact Finset.subset_biUnion_of_mem (fun m => (b.repr (coeff m F)).support) hm
          · simp [notMem_support_iff.1 hm]
      rw [this]
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
      have h1 := congrArg W.subtype (w.sum_repr ⟨_, hF (b.coord j)⟩)
      simp only [map_sum, map_smul, Submodule.subtype_apply] at h1
      rw [← h1, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_eq_C_mul, map_mul, map_C, C_mul']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩ φ
      rw [contr_map]
      exact W.smul_mem _ (w i).2
  rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]
end GlobalTheory.RegBound
