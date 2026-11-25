-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.NormAt.exists_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:33:01.923475+00:00
-- url     : https://prove2.me/submissions/cae5ba27-f36d-4401-ade1-9e66238707ca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_GlueApplyOfNotInFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory
variable {X X' X'' : Scheme.{0}} {Ω Ω' Ω'' : Type} [Field Ω] [Field Ω'] [Field Ω'']
  {E F : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Ω' F]
variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
  {ξ'' : Spec (CommRingCat.of Ω'') ⟶ X''}
namespace GlobalTheory.CompanionTheory.Ar
namespace NormAt
theorem _root_.solution {f : X' ⟶ X} {i : Ω →+* Ω'} {p : Cpt ξ} (h : NormAt ξ' f i p) :
    ∃ p' : Cpt ξ', f p'.1 = p.1 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (integralClosure ((regAt ξ p).map i) Ω').toSubring
  obtain ⟨q, hq, -⟩ := h.existsUnique P hP
  exact ⟨q, hq.1⟩
end NormAt
end GlobalTheory.CompanionTheory.Ar
