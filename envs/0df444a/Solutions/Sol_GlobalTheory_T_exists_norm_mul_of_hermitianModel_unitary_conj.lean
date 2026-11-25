-- Prove2me | solution 1 for GlobalTheory.T.exists_norm_mul_of_hermitianModel_unitary_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:19:10.836647+00:00
-- url     : https://prove2.me/submissions/967fc7b0-59eb-4628-b82b-e545dfc7d753

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNormMulOfHermitianModelUnitaryConj
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNormMulOfHermitianModelUnitaryConjStatement
import Theorems.Thm_GlobalTheory_InertUnitOrb_class_eq_of_conj


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
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ γ' u : Matrix (Fin n) (Fin n) K.E) (x x' : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ → GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ' → (u.map K.c)ᵀ * u = 1 → γ * u = u * γ' → B.P.Separable → ∃ v : B.Aˣ, (x' : B.A) = x * (v * B.σ v) := by
  first | exact @GlobalTheory.InertUnitOrb.class_eq_of_conj | exact GlobalTheory.InertUnitOrb.class_eq_of_conj | (intros; apply GlobalTheory.InertUnitOrb.class_eq_of_conj <;> assumption)
end _root_.GlobalTheory.T
