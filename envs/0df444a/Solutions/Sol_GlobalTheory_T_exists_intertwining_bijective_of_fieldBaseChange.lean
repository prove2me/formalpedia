-- Prove2me | solution 1 for GlobalTheory.T.exists_intertwining_bijective_of_fieldBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:22:09.196276+00:00
-- url     : https://prove2.me/submissions/317674ea-49b7-460e-a9de-704586dbabaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntertwiningBijectiveOfFieldBaseChange
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntertwiningBijectiveOfFieldBaseChangeStatement
import Theorems.Thm_GlobalTheory_FieldBaseChange_exists_intertwining_bijective_of_extension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [Infinite K] (V W V' W' : Type) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W'] [FiniteDimensional F V'] (iV : V →ₛₗ[algebraMap K F] V') (iW : W →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension iV → GlobalTheory.FieldBaseChange.IsExtension iW → ∀ (J : Type) (a : J → V →ₗ[K] V) (b : J → W →ₗ[K] W) (a' : J → V' →ₗ[F] V') (b' : J → W' →ₗ[F] W'), (∀ i v, a' i (iV v) = iV (a i v)) → (∀ i w, b' i (iW w) = iW (b i w)) → ∀ E' : V' →ₗ[F] W', Function.Bijective E' → (∀ i v, E' (a' i v) = b' i (E' v)) → ∃ E : V →ₗ[K] W, Function.Bijective E ∧ ∀ i v, E (a i v) = b i (E v) := by
  first | exact @GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | exact GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension | (intros; apply GlobalTheory.FieldBaseChange.exists_intertwining_bijective_of_extension <;> assumption)
end _root_.GlobalTheory.T
