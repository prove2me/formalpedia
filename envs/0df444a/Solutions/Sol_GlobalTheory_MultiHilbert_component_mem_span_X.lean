-- Prove2me | solution 1 for GlobalTheory.MultiHilbert.component_mem_span_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:00:44.730505+00:00
-- url     : https://prove2.me/submissions/3f2f517a-9bc6-4e35-b079-ff1dbd585fc3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {K σ M : Type} [Field K] [AddCancelCommMonoid M] (w : σ → M)
namespace GlobalTheory.MultiHilbert
theorem _root_.solution (s : Set σ) (n : M) {G : MvPolynomial σ K}
    (hG : G ∈ Ideal.span (X '' s : Set (MvPolynomial σ K))) :
    weightedHomogeneousComponent w n G ∈ Ideal.span (X '' s : Set (MvPolynomial σ K)) := by
  classical
  rw [mem_ideal_span_X_image] at hG ⊢
  intro m hm
  refine hG m ?_
  rw [mem_support_iff, coeff_weightedHomogeneousComponent] at hm
  rw [mem_support_iff]
  intro h
  simp [h] at hm
end GlobalTheory.MultiHilbert
