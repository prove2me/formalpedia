-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.IsIso.charpoly_eq_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:47.78836+00:00
-- url     : https://prove2.me/submissions/b352b8af-a6cf-4473-a09a-b0f545b472bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
open GlobalTheory.UnitLemma.Orbit.IsIso
variable {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A}
namespace GlobalTheory.UnitLemma.Orbit.IsIso
theorem _root_.solution (h : IsIso φ) : C.P = B.P := by
  unfold InvAlg.P
  rw [← LinearEquiv.charpoly_conj φ.toLinearEquiv]
  congr 1
  ext y
  simp [LinearEquiv.conj_apply, h.2]
end GlobalTheory.UnitLemma.Orbit.IsIso
