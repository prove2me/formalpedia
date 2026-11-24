-- Prove2me | solution 1 for GlobalTheory.FormalInv.mem_coeffsIn_groupWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:11:57.293339+00:00
-- url     : https://prove2.me/submissions/3d17b75f-5cb6-49ff-b29f-b5115423a0ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_CoeffSubstInvMemOfTwoLeOrder
import Theorems.Thm_GlobalTheory_FormalInv_mem_coeffsIn
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_apply
import Theorems.Thm_GlobalTheory_FormalInv_substAlgEquiv_symm_apply
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inl
import Theorems.Thm_GlobalTheory_FormalInv_sumFamily_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_apply
attribute [local simp] GlobalTheory.FormalInv.substAlgEquiv_symm_apply
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inl
attribute [local simp] GlobalTheory.FormalInv.sumFamily_inr

set_option autoImplicit false
open MvPowerSeries Finsupp
noncomputable section
open GlobalTheory GlobalTheory.FormalInv
variable {σ τ υ ι : Type*} {R : Type*} [CommRing R]
variable {σ' τ' : Type*}
namespace GlobalTheory.FormalInv
theorem _root_.solution [Finite σ] [Finite σ'] {S : Subring R} {g g' : ℕ}
    {f : MvPowerSeries (σ ⊕ σ') R} :
    f ∈ coeffsIn S (groupWeight σ σ') (fun b => bif b then g else g') ↔
      ∀ (α : σ →₀ ℕ) (β : σ' →₀ ℕ), α.degree < g → β.degree < g' →
        coeff (α.sumElim β) f ∈ S := by
  classical
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite σ'
  have h1 : ∀ (α : σ →₀ ℕ) (β : σ' →₀ ℕ),
      weight (groupWeight σ σ' true) (α.sumElim β) = α.degree := fun α β => by
    simp [weight_eq_sum, degree_eq_sum, groupWeight]
  have h2 : ∀ (α : σ →₀ ℕ) (β : σ' →₀ ℕ),
      weight (groupWeight σ σ' false) (α.sumElim β) = β.degree := fun α β => by
    simp [weight_eq_sum, degree_eq_sum, groupWeight]
  rw [mem_coeffsIn]
  constructor
  · intro h α β hα hβ
    refine h _ fun b => ?_
    cases b
    · rwa [h2]
    · rwa [h1]
  · intro h d hd
    obtain ⟨⟨α, β⟩, rfl⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective d
    have ht := hd true
    have hf := hd false
    simp only [sumFinsuppEquivProdFinsupp_symm_apply] at ht hf ⊢
    rw [h1] at ht
    rw [h2] at hf
    exact h α β ht hf
end GlobalTheory.FormalInv
