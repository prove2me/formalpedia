-- Prove2me | solution 1 for GlobalTheory.T.exists_ringHom_limit_of_doublingJets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:22:41.951607+00:00
-- url     : https://prove2.me/submissions/55876ad2-25aa-400d-9c28-c9ffcfdf7276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomLimitOfDoublingJets
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomLimitOfDoublingJetsStatement
import Theorems.Thm_GlobalTheory_Nef_PathJet_limit_of_jets


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ∀ φ : ℕ → A → PowerSeries R, (∀ n, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 2) (φ n)) → (∀ n f, (PowerSeries.X : PowerSeries R) ^ (n + 2) ∣ φ (n + 1) f - φ n f) → ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧ PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧ (PowerSeries.rescale 2).comp γ = γ.comp m := by
  first | exact @GlobalTheory.Nef.PathJet.limit_of_jets | exact GlobalTheory.Nef.PathJet.limit_of_jets | (intros; apply GlobalTheory.Nef.PathJet.limit_of_jets <;> assumption)
end _root_.GlobalTheory.T
