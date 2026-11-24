-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.eq_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:29.004784+00:00
-- url     : https://prove2.me/submissions/7002514d-d5d2-4efd-9709-81861276270d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) {y : X}
    (hy : y ⤳ genPt ξ) : y = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ h.bij).toMulEquiv
  have hr : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨z, rfl⟩ := hr
  let _ := hF.toField
  have : z = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) :=
    Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genPt ξ))) _ _
  rw [this, Scheme.fromSpecStalk_closedPoint]
end GlobalTheory.CompanionTheory.Ar.CptModel
