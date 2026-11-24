-- Prove2me | solution 1 for GlobalTheory.FixedPoint.exists_ringHom_of_forall_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:08:01.999285+00:00
-- url     : https://prove2.me/submissions/049149c6-c226-48fe-8e64-fee6337c1e87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FixedPoint
universe u v w
variable {K₀ : Type u} {K₁ : Type v} {L : Type w} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]
namespace GlobalTheory.FixedPoint
theorem _root_.solution {A : Type*} [CommRing A] (φ : A →+* K₁)
    (h : ∀ a, φ a ∈ Set.range (algebraMap K₀ K₁)) :
    ∃ ψ : A →+* K₀, (algebraMap K₀ K₁).comp ψ = φ := by
  choose f hf using h
  have hi := (algebraMap K₀ K₁).injective
  refine ⟨⟨⟨⟨f, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, RingHom.ext hf⟩ <;>
    simp [hf]
end GlobalTheory.FixedPoint
