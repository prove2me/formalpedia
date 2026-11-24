-- Prove2me | solution 1 for GlobalTheory.ModelCharpoly.model_charpoly_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:18:22.715353+00:00
-- url     : https://prove2.me/submissions/081c1427-c97c-450f-834b-11df9535bb90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelCharpolyEqAndUnitary
import Theorems.Thm_GlobalTheory_ModelCharpoly_charpoly_eq
import Theorems.Thm_GlobalTheory_ModelCharpoly_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.ModelCharpoly
open GlobalTheory.InertUnitOrb
namespace GlobalTheory.ModelCharpoly
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)),
    GlobalTheory.InertUnitOrb.IsModel B γ x ψ → γ.charpoly = B.P ∧ (B.g * B.σ B.g = 1 → (γ.map K.c)ᵀ * γ = 1) := by
  intro K B n γ x ψ hM
  exact ⟨charpoly_eq K B n γ ψ hM.2.1, unitary K B n γ x ψ hM.2.1 hM.2.2⟩
end GlobalTheory.ModelCharpoly
