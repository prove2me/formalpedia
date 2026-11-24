-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.IsCoord.natural
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:13:53.789849+00:00
-- url     : https://prove2.me/submissions/a387a1e8-213b-4c20-9fa4-c115d665b78a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Theorems.Thm_GlobalTheory_FieldBaseChange_addHom_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]
namespace GlobalTheory.FieldBaseChange
namespace IsCoord
theorem _root_.solution {V' W' : Type} [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module F W']
    {a : V →ₛₗ[algebraMap K F] W} {a' : V' →ₛₗ[algebraMap K F] W'}
    (h : Submodule.span F (Set.range a) = ⊤) {ℓ : F →ₗ[K] K} {Λ : W →+ V} {Λ' : W' →+ V'}
    (hΛ : IsCoord a ℓ Λ) (hΛ' : IsCoord a' ℓ Λ') (θ : V →ₗ[K] V') (θ' : W →ₗ[F] W')
    (hθ : ∀ v, θ' (a v) = a' (θ v)) (x : W) : Λ' (θ' x) = θ (Λ x) := by
  have key := addHom_ext h (f := Λ'.comp θ'.toAddMonoidHom) (g := θ.toAddMonoidHom.comp Λ)
    (fun c v => by
      show Λ' (θ' (c • a v)) = θ (Λ (c • a v))
      rw [map_smul, hθ, hΛ' c (θ v), hΛ c v, map_smul]) x
  exact key
end IsCoord
end GlobalTheory.FieldBaseChange
