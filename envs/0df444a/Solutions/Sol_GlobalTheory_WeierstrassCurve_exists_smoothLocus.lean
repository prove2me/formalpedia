-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.exists_smoothLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:47.961925+00:00
-- url     : https://prove2.me/submissions/10a4cfa6-0b92-4983-be72-02a45005d9f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TopLePtHomPreimageSmoothOpenIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution (R : Type) [CommRing R] (W : WeierstrassCurve R) :
    ∃ U : (scheme W).Opens, (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k)
      (h : IsUnimodularSol (W.map ρ) P),
        ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) ∧
      SmoothOfRelativeDimension 1 (U.ι ≫ toSpec W) ∧ QuasiCompact (U.ι ≫ toSpec W) ∧
      GeometricallyIntegral (U.ι ≫ toSpec W) :=
  ⟨smoothOpen W, fun _ _ ρ P h => top_le_ptHom_preimage_smoothOpen_iff W ρ P h,
    inferInstance, inferInstance, inferInstance⟩
end GlobalTheory.WeierstrassCurve
