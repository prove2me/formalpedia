-- Prove2me | solution 1 for GlobalTheory.T.hermitianModel_charpoly_eq_and_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:20:09.938811+00:00
-- url     : https://prove2.me/submissions/82984942-c688-41fe-aaa1-a2d7f6dcbfe3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelCharpolyEqAndUnitary
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelCharpolyEqAndUnitaryStatement
import Theorems.Thm_GlobalTheory_ModelCharpoly_model_charpoly_unitary


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
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ → γ.charpoly = B.P ∧ (B.g * B.σ B.g = 1 → (γ.map K.c)ᵀ * γ = 1) := by
  first | exact @GlobalTheory.ModelCharpoly.model_charpoly_unitary | exact GlobalTheory.ModelCharpoly.model_charpoly_unitary | (intros; apply GlobalTheory.ModelCharpoly.model_charpoly_unitary <;> assumption)
end _root_.GlobalTheory.T
