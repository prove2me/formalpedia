-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.exists_isModel_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:28.554381+00:00
-- url     : https://prove2.me/submissions/12c51d4b-e299-42f7-af44-666204dc26c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsModelOfUnitary
import Theorems.Thm_GlobalTheory_InertUnitOrb_stdH_mulVec_of_unitary
import Theorems.Thm_GlobalTheory_UnitLemma_PairClass_exists_herm_model


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
open GlobalTheory GlobalTheory.InertUnitOrb
namespace GlobalTheory.InertUnitOrb
theorem _root_.solution : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E), (γ.map K.c)ᵀ * γ = 1 → B.g * B.σ B.g = 1 → B.P.Separable → γ.charpoly = B.P → ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  intro K B n γ hγ hg hsep hchar
  obtain ⟨x, e, h1, h2, h3⟩ := PairClass.exists_herm_model K (Fin n → K.E) (stdH K n)
    (fun x y z => by simp [stdH, add_mul, Finset.sum_add_distrib])
    (fun c x z => by simp [stdH, Finset.mul_sum, mul_assoc])
    (fun x y => by
      simp only [stdH, map_sum, map_mul, K.c_c]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _)
    (fun y hy => by
      funext k
      have := hy (Pi.single k 1)
      rw [stdH, Finset.sum_eq_single k] at this
      · simpa using this
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp)
    B (Matrix.toLin' γ) hsep (by rw [Matrix.charpoly_toLin', hchar])
    (Or.inl ⟨hg, fun y z => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, stdH_mulVec_of_unitary K n γ hγ]⟩)
  exact ⟨x, e, h1, fun y => by rw [h2, Matrix.toLin'_apply], h3⟩
end GlobalTheory.InertUnitOrb
