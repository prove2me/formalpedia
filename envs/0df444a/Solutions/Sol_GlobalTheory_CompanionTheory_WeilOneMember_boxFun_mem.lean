-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilOneMember.boxFun_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:30.159795+00:00
-- url     : https://prove2.me/submissions/fd6fb541-b123-4f09-8efa-51bdcb3ec717

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DblCoordUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilOneMember
namespace GlobalTheory.CompanionTheory.WeilOneMember
theorem _root_.solution {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {κ κ' : Type}
    {φ₁ : (κ → R) → ℂ} {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by
  have h₁' : IsLocallyConstant φ₁ ∧ HasCompactSupport φ₁ := h₁
  have h₂' : IsLocallyConstant φ₂ ∧ HasCompactSupport φ₂ := h₂
  have cl : Continuous fun x : κ ⊕ κ' → R => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → R => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  show IsLocallyConstant (boxFun φ₁ φ₂) ∧ HasCompactSupport (boxFun φ₁ φ₂)
  refine ⟨?_, ?_⟩
  · exact IsLocallyConstant.comp₂ (h₁'.1.comp_continuous cl) (h₂'.1.comp_continuous cr) (· * ·)
  · let S : Set (κ ⊕ κ' → R) :=
      (fun x => x ∘ Sum.inl) ⁻¹' tsupport φ₁ ∩ (fun x => x ∘ Sum.inr) ⁻¹' tsupport φ₂
    let gm : (κ → R) × (κ' → R) → (κ ⊕ κ' → R) := fun p => Sum.elim p.1 p.2
    have hgm : Continuous gm := by
      refine continuous_pi fun i => ?_
      cases i with
      | inl i => exact (continuous_apply i).comp continuous_fst
      | inr i => exact (continuous_apply i).comp continuous_snd
    have hK : IsCompact (gm '' (tsupport φ₁ ×ˢ tsupport φ₂)) := (h₁'.2.prod h₂'.2).image hgm
    have hSc : IsClosed S := (isClosed_tsupport φ₁).preimage cl |>.inter ((isClosed_tsupport φ₂).preimage cr)
    have hsub : tsupport (boxFun φ₁ φ₂) ⊆ S := by
      refine closure_minimal ?_ hSc
      intro x hx
      have hx' : φ₁ (x ∘ Sum.inl) * φ₂ (x ∘ Sum.inr) ≠ 0 := hx
      exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx'), subset_tsupport _ (right_ne_zero_of_mul hx')⟩
    have hSK : S ⊆ gm '' (tsupport φ₁ ×ˢ tsupport φ₂) := by
      intro x hx
      exact ⟨(x ∘ Sum.inl, x ∘ Sum.inr), hx, Sum.elim_comp_inl_inr x⟩
    exact hK.of_isClosed_subset (isClosed_tsupport _) (hsub.trans hSK)
end GlobalTheory.CompanionTheory.WeilOneMember
