-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WittOrbit.map_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:36:41.442996+00:00
-- url     : https://prove2.me/submissions/b3233bbf-8018-4223-bbc8-c56c34f699ff

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CharacterAugmentationSubspaceQuotientActionTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WittOrbit
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E}
namespace GlobalTheory.CompanionTheory.WittOrbit
theorem _root_.solution {m n : Type} (hc : ∀ z, c (c z) = z) (X : Matrix m n E) : (X.map c).map c = X := by
  ext i j; simp [hc]
end GlobalTheory.CompanionTheory.WittOrbit
