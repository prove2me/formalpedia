-- Prove2me | solution 1 for GlobalTheory.T.exists_hermitianModel_of_norm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:19:39.94019+00:00
-- url     : https://prove2.me/submissions/17cec902-cd91-4e25-9403-939132f41e8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZeroStatement
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_exists_model


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
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (x : B.Aˣ), Module.finrank K.E B.A = n → B.σ (x : B.A) = x → B.N x ≠ 0 → ∃ (γ : Matrix (Fin n) (Fin n) K.E) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  first | exact @GlobalTheory.InertUnitOrb.ModelOfN.exists_model | exact GlobalTheory.InertUnitOrb.ModelOfN.exists_model | (intros; apply GlobalTheory.InertUnitOrb.ModelOfN.exists_model <;> assumption)
end _root_.GlobalTheory.T
