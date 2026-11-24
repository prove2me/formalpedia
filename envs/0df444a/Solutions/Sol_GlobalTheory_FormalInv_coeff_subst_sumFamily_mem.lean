-- Prove2me | solution 1 for GlobalTheory.FormalInv.coeff_subst_sumFamily_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:47:13.782844+00:00
-- url     : https://prove2.me/submissions/6a58167c-f0d9-458e-9c3e-37340eba3fa9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_subst_mem_coeffsIn
import Theorems.Thm_GlobalTheory_FormalInv_constantCoeff_sumFamily
import Theorems.Thm_GlobalTheory_FormalInv_mem_coeffsIn_groupWeight
import Theorems.Thm_GlobalTheory_FormalInv_rename_mem_weightGe
import Theorems.Thm_GlobalTheory_FormalInv_rename_mem_coeffsIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable {σ' τ' : Type*}
namespace GlobalTheory.FormalInv
theorem _root_.solution [Finite σ] [Finite σ'] [Finite τ] [Finite τ'] {S : Subring R}
    {g g' : ℕ} {a : σ → MvPowerSeries τ R} {a' : σ' → MvPowerSeries τ' R}
    (ha : ∀ i, constantCoeff (a i) = 0) (ha' : ∀ j, constantCoeff (a' j) = 0)
    (haS : ∀ i (d : τ →₀ ℕ), d.degree < g → coeff d (a i) ∈ S)
    (haS' : ∀ j (d : τ' →₀ ℕ), d.degree < g' → coeff d (a' j) ∈ S)
    {f : MvPowerSeries (σ ⊕ σ') R}
    (hf : ∀ (α : σ →₀ ℕ) (β : σ' →₀ ℕ), α.degree < g → β.degree < g' →
      coeff (α.sumElim β) f ∈ S)
    (α : τ →₀ ℕ) (β : τ' →₀ ℕ) (hα : α.degree < g) (hβ : β.degree < g') :
    coeff (α.sumElim β) (f.subst (sumFamily a a')) ∈ S := by
  refine mem_coeffsIn_groupWeight.1 (subst_mem_coeffsIn
    (hasSubst_of_constantCoeff_zero (constantCoeff_sumFamily ha ha')) ?_ ?_
    (mem_coeffsIn_groupWeight.2 hf)) α β hα hβ
  · rintro (_ | _) (i | j)
    · exact mem_weightGe_zero _
    · exact rename_mem_weightGe _ (mem_degGe_one.2 (ha' j))
    · exact rename_mem_weightGe _ (mem_degGe_one.2 (ha i))
    · exact mem_weightGe_zero _
  · rintro (i | j)
    · refine rename_mem_coeffsIn _ fun d hd => haS i d ?_
      rw [degree_eq_weight_one]; exact hd true
    · refine rename_mem_coeffsIn _ fun d hd => haS' j d ?_
      rw [degree_eq_weight_one]; exact hd false
end GlobalTheory.FormalInv
