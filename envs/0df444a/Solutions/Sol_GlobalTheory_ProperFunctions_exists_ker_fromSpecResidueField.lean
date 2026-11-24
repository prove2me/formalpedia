-- Prove2me | solution 1 for GlobalTheory.ProperFunctions.exists_ker_fromSpecResidueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:46.837566+00:00
-- url     : https://prove2.me/submissions/7e04e460-30fe-40b9-a37b-5015a835251f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X S : Scheme.{u}}
namespace GlobalTheory.ProperFunctions
theorem _root_.solution [IsAffine S] (𝔭 : Ideal Γ(S, ⊤)) (h𝔭 : 𝔭.IsPrime) :
    ∃ s : S, RingHom.ker (S.fromSpecResidueField s).appTop.hom = 𝔭 := by
  obtain ⟨s, hs⟩ := S.isoSpec.hom.surjective ⟨𝔭, h𝔭⟩
  refine ⟨s, Ideal.ext fun r ↦ ?_⟩
  have h1 : s ∈ S.basicOpen r ↔ r ∉ 𝔭 := by
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    change S.isoSpec.hom s ∈ PrimeSpectrum.basicOpen r ↔ _
    rw [hs]
    rfl
  rw [RingHom.mem_ker, ← not_iff_not, ← h1]
  change ¬ (S.fromSpecResidueField s).app ⊤ r = 0 ↔ _
  rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen]
  constructor
  · intro h
    by_contra hs
    refine h (eq_bot_iff.mpr fun x hx ↦ hs ?_)
    have hx' : S.fromSpecResidueField s x ∈ S.basicOpen r := hx
    rwa [Scheme.fromSpecResidueField_apply] at hx'
  · intro h h'
    have : (default : Spec (S.residueField s)) ∈ S.fromSpecResidueField s ⁻¹ᵁ S.basicOpen r := by
      change S.fromSpecResidueField s default ∈ S.basicOpen r
      rwa [Scheme.fromSpecResidueField_apply]
    rw [h'] at this
    exact this
end GlobalTheory.ProperFunctions
