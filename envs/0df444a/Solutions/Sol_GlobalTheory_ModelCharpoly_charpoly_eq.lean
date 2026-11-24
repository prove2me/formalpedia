-- Prove2me | solution 1 for GlobalTheory.ModelCharpoly.charpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:58:23.580813+00:00
-- url     : https://prove2.me/submissions/c819fe7e-1244-4c64-a326-198965e0830d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelCharpolyEqAndUnitary

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
theorem _root_.solution (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E)
    (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (h : ∀ y, ψ (B.g * y) = γ *ᵥ ψ y) : γ.charpoly = B.P := by
  let b : Module.Basis (Fin n) K.E B.A := (Pi.basisFun K.E (Fin n)).map ψ.symm
  have hm : LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g) = γ := by
    ext i j
    simp [b, LinearMap.toMatrix_apply, h]
  rw [InvAlg.P, ← LinearMap.charpoly_toMatrix (LinearMap.mulLeft K.E B.g) b, hm]
end GlobalTheory.ModelCharpoly
