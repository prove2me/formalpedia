-- Prove2me | solution 1 for GlobalTheory.finite_augmented_connected_part_localisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:52.071809+00:00
-- url     : https://prove2.me/submissions/1252bc6c-8bd9-41da-a354-a505892b170e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MonicEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_FiniteAugmentedConnectedPartLocalisation
import Theorems.Thm_GlobalTheory_MonicSeparableProduct_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F : Type) [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W), (∀ a : W, ¬ IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p}) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Finite W A] (aug : A →ₐ[W] W), ∃ s : A, Function.Surjective (algebraMap A (Localization.Away s)) ∧ (∃ m : ℕ, ((RingHom.ker aug).map (algebraMap A (Localization.Away s))) ^ m ≤ Ideal.span {algebraMap W (Localization.Away s) p}) ∧ ∀ (R : Type) [CommRing R] [Algebra W R] (w : A →ₐ[W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) → IsUnit (w s) := by
  first
  | exact @_root_.GlobalTheory.MonicSeparableProduct.main
  | exact _root_.GlobalTheory.MonicSeparableProduct.main
  | (apply _root_.GlobalTheory.MonicSeparableProduct.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicSeparableProduct.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicSeparableProduct.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicSeparableProduct.main ..)
end GlobalTheory
