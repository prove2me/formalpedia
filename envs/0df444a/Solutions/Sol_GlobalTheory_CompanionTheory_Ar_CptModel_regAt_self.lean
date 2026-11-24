-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.regAt_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:44.157237+00:00
-- url     : https://prove2.me/submissions/3c6c4ba0-1bea-4716-87f1-c99b620b63e5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CptModel_genMap_self

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
theorem _root_.solution {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ) : regAt ξ (self ξ) = ⊤ := by
  rw [regAt, RingHom.range_eq_top, genMap_self]
  exact h.bij.2
end GlobalTheory.CompanionTheory.Ar.CptModel
