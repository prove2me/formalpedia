-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.IsCtrOf.mem_ctrSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:33:54.540819+00:00
-- url     : https://prove2.me/submissions/0470e7a0-8217-429d-b950-d19f19fc4766

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
namespace IsCtrOf
theorem _root_.solution {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω} {M : PModel o x}
    {i : Ω →+* Ω'} {p : Cpt M.ξ} {p' : Cpt ξ'} (h : IsCtrOf i p p') : p' ∈ ctrSet o x i ξ' := by
  obtain ⟨c, hc⟩ := M.tie.cover p
  exact ⟨c, hc.1, fun a ha => h.1 a ((M.tie.ring c hc.1 a).1 ha p hc)⟩
end IsCtrOf
end GlobalTheory.CompanionTheory.Ar
