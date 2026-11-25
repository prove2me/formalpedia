-- Prove2me | solution 1 for GlobalTheory.T.exists_kaehler_fibre_equiv_D_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:17:46.745736+00:00
-- url     : https://prove2.me/submissions/a27146cb-1ab7-49af-948b-ac108657f2ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KaehlerFibreEquivPushoutFormallyEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KaehlerFibreEquivPushoutFormallyEtaleStatement
import Theorems.Thm_GlobalTheory_kaehler_fibre_equiv_pushout_formallyEtale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R R' B C B' K : Type) [CommRing R] [CommRing R'] [CommRing B] [CommRing C] [CommRing B'] [Field K] [Algebra R R'] [Algebra R B] [Algebra R C] [Algebra R' C] [Algebra B C] [IsScalarTower R R' C] [IsScalarTower R B C] [Algebra.IsPushout R R' B C] [Algebra C B'] [Algebra R' B'] [IsScalarTower R' C B'] [Algebra.FormallyEtale C B'] [Algebra B' K] [Algebra B K], (∀ x : B, algebraMap B K x = algebraMap B' K (algebraMap C B' (algebraMap B C x))) → ∃ e : (K ⊗[B] Ω[B⁄R]) ≃ₗ[K] (K ⊗[B'] Ω[B'⁄R']), ∀ x : B, e ((1 : K) ⊗ₜ[B] KaehlerDifferential.D R B x) = (1 : K) ⊗ₜ[B'] KaehlerDifferential.D R' B' (algebraMap C B' (algebraMap B C x)) := by
  first | exact @GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale | exact GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale | (intros; apply GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale <;> assumption)
end _root_.GlobalTheory.T
