-- Prove2me | solution 1 for GlobalTheory.SS.Dil.exists_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:16:52.363579+00:00
-- url     : https://prove2.me/submissions/0af6e3c0-f952-4773-ac85-43d6030d9e66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization
import Theorems.Thm_GlobalTheory_FiniteFieldCountEstimate_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
namespace GlobalTheory.SS.Dil
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (hπ : Irreducible π)
    (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B] (I : Ideal B) :
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'), Algebra.FiniteType R B' ∧ Module.Flat R B' ∧
      Function.Injective φ ∧ (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧
      (∀ x, algebraMap R B' π * x = 0 → x = 0) ∧ (∀ g ∈ I, ∃ b', algebraMap R B' π * b' = φ g) ∧
      (∀ Q : B' → Prop, (∀ b, Q (φ b)) → (∀ g ∈ I, ∀ b', algebraMap R B' π * b' = φ g → Q b') →
        (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x) := by
  first
  | exact @_root_.GlobalTheory.FiniteFieldCountEstimate.main
  | exact _root_.GlobalTheory.FiniteFieldCountEstimate.main
  | (apply _root_.GlobalTheory.FiniteFieldCountEstimate.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteFieldCountEstimate.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteFieldCountEstimate.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteFieldCountEstimate.main ..)
end GlobalTheory.SS.Dil
