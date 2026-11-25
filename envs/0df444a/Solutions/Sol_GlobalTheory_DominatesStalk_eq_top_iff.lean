-- Prove2me | solution 1 for GlobalTheory.DominatesStalk.eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:44:07.028001+00:00
-- url     : https://prove2.me/submissions/634f9860-5035-4092-b2ef-188e7f57420d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {X X' S : Scheme.{u}} [IsIntegral X] [IsIntegral X']
variable {W : ValuationSubring X.functionField} {x : X}
namespace GlobalTheory
namespace DominatesStalk
theorem _root_.solution (h : DominatesStalk W x) : W = ⊤ ↔ x = genericPoint X := by
  constructor
  · rintro rfl
    obtain ⟨l, hl, rfl⟩ := dominatesStalk_iff_exists_hom.mp h
    have hf : IsField (⊤ : ValuationSubring X.functionField) :=
      MulEquiv.isField (Field.toIsField X.functionField) Subring.topEquiv.toMulEquiv
    have e : specAlgebraMap (⊤ : ValuationSubring X.functionField) X.functionField
        (closedPoint X.functionField) = closedPoint (⊤ : ValuationSubring X.functionField) := by
      letI := hf.toField
      exact Subsingleton.elim (α := PrimeSpectrum (⊤ : ValuationSubring X.functionField)) _ _
    rw [← e]
    exact (congrArg (fun l : Spec (.of X.functionField) ⟶ X ↦ l (closedPoint X.functionField))
      hl).trans Scheme.fromSpecStalk_closedPoint
  · rintro rfl
    refine eq_top_iff.mpr fun f _ ↦ ?_
    have e : X.presheaf.stalkSpecializes (specializes_refl (genericPoint X)) f = f :=
      congr($(X.presheaf.stalkSpecializes_refl (genericPoint X)) f)
    have h1 : X.presheaf.stalkSpecializes (specializes_refl (genericPoint X)) f ∈ W := h.1 f
    rwa [e] at h1
end DominatesStalk
end GlobalTheory
