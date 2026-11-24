-- Prove2me | solution 1 for GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:12.277494+00:00
-- url     : https://prove2.me/submissions/c8e5463f-248f-4dab-a040-7a3b7e3cf908

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsMoreSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KaehlerFibreEquivPushoutFormallyEtale
import Theorems.Thm_GlobalTheory_AuxiliaryLemmaFirst_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
open KaehlerDifferential TensorProduct
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R R' B C B' K : Type) [CommRing R] [CommRing R'] [CommRing B] [CommRing C] [CommRing B'] [Field K] [Algebra R R'] [Algebra R B] [Algebra R C] [Algebra R' C] [Algebra B C] [IsScalarTower R R' C] [IsScalarTower R B C] [Algebra.IsPushout R R' B C] [Algebra C B'] [Algebra R' B'] [IsScalarTower R' C B'] [Algebra.FormallyEtale C B'] [Algebra B' K] [Algebra B K], (∀ x : B, algebraMap B K x = algebraMap B' K (algebraMap C B' (algebraMap B C x))) → ∃ e : (K ⊗[B] Ω[B⁄R]) ≃ₗ[K] (K ⊗[B'] Ω[B'⁄R']), ∀ x : B, e ((1 : K) ⊗ₜ[B] KaehlerDifferential.D R B x) = (1 : K) ⊗ₜ[B'] KaehlerDifferential.D R' B' (algebraMap C B' (algebraMap B C x)) := by
  first
  | exact @_root_.GlobalTheory.AuxiliaryLemmaFirst.main
  | exact _root_.GlobalTheory.AuxiliaryLemmaFirst.main
  | (apply _root_.GlobalTheory.AuxiliaryLemmaFirst.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AuxiliaryLemmaFirst.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AuxiliaryLemmaFirst.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AuxiliaryLemmaFirst.main ..)
end GlobalTheory
