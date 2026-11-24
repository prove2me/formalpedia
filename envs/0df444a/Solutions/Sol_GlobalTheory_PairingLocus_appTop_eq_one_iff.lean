-- Prove2me | solution 1 for GlobalTheory.PairingLocus.appTop_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:56.698384+00:00
-- url     : https://prove2.me/submissions/b64546d5-a836-4b09-a7a7-e19c6a5db204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsClopenOfIsLocallyNoetherian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLocus
namespace GlobalTheory.PairingLocus
theorem _root_.solution {X Y : Scheme.{0}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) (h : Y ⟶ X) :
    h.appTop.hom e = 1 ↔ Set.range h ⊆ X.basicOpen e := by
  have p : h ⁻¹ᵁ X.basicOpen e = Y.basicOpen (h.appTop.hom e) := Scheme.preimage_basicOpen h e
  constructor
  · rintro H _ ⟨y, rfl⟩
    have : y ∈ h ⁻¹ᵁ X.basicOpen e := by
      rw [p, H, Scheme.basicOpen_of_isUnit _ isUnit_one]; trivial
    exact this
  · intro H
    have hu : IsUnit (h.appTop.hom e) := by
      refine RingedSpace.isUnit_of_isUnit_germ Y.toRingedSpace ⊤ _ fun y hy => ?_
      have : y ∈ Y.basicOpen (h.appTop.hom e) := by rw [← p]; exact H ⟨y, rfl⟩
      exact (Y.mem_basicOpen _ y hy).1 this
    exact hu.mul_left_cancel ((he.map h.appTop.hom).eq.trans (_root_.mul_one _).symm)
end GlobalTheory.PairingLocus
