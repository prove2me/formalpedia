-- Prove2me | solution 1 for GlobalTheory.T.hermitianModels_conj_unitary_of_norm_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:20:13.226868+00:00
-- url     : https://prove2.me/submissions/0bd2ed67-071e-4998-8eba-622730a48fca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelsConjUnitaryOfNormClass
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelsConjUnitaryOfNormClassStatement
import Theorems.Thm_GlobalTheory_InertUnitOrb_conj_of_norm_class


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ γ' : Matrix (Fin n) (Fin n) K.E) (x x' v : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ → GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ' → (x' : B.A) = x * (v * B.σ v) → ∃ u : Matrix (Fin n) (Fin n) K.E, (u.map K.c)ᵀ * u = 1 ∧ γ * u = u * γ' := by
  first | exact @GlobalTheory.InertUnitOrb.conj_of_norm_class | exact GlobalTheory.InertUnitOrb.conj_of_norm_class | (intros; apply GlobalTheory.InertUnitOrb.conj_of_norm_class <;> assumption)
end _root_.GlobalTheory.T
