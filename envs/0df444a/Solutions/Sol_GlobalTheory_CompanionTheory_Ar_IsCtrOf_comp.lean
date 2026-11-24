-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.IsCtrOf.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:20:15.7258+00:00
-- url     : https://prove2.me/submissions/69a29ee0-e5e4-4e71-b67a-a8543151b54b

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
theorem _root_.solution {i : Ω →+* Ω'} {i' : Ω' →+* Ω''} {p : Cpt ξ} {p' : Cpt ξ'} {p'' : Cpt ξ''}
    (h : IsCtrOf i p p') (h' : IsCtrOf i' p' p'') : IsCtrOf (i'.comp i) p p'' :=
  ⟨fun a ha => h'.1 _ (h.1 a ha), fun a ha hu => h.2 a ha (h'.2 _ (h.1 a ha) hu)⟩
end IsCtrOf
end GlobalTheory.CompanionTheory.Ar
