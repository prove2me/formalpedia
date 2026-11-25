-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.exists_sdW_sdHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:35:11.616536+00:00
-- url     : https://prove2.me/submissions/107e6c56-c983-4bd7-8b27-980e2cfb6846

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_pi
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_secondCountable
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_exists_selfDual
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_BR_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_BR_add_right
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_BR_nondeg
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_pairHerm_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_pairHerm_add_right
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_pairHerm_nondeg
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_continuous_BR
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_continuous_pairHerm
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_hasCoord_tens
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_hasCoord_herm
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_hasCoord_ainf
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_exists_functional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualReal_exists_selfDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
namespace GlobalTheory.CompanionTheory.SelfDualInf
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∃ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) n μ) ∧ ∃ ν, SdHerm F E σ (Ainf F) (psiInf F ψ) n ν := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ hψ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ) : E →ₐ[ℚ] ℂ).toRingHom
    apply τ.injective
    rw [hCM.2.2.2, hCM.2.2.2, star_star]
  obtain ⟨L, hLc, hLx, hLn⟩ := exists_functional hCM.1 ψ hψ
  have hA := hasCoord_ainf hCM.1
  have hT := hasCoord_tens (F := F) (E := E) (Ainf F) hA
  have := hT.secondCountable
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  constructor
  · exact ((hT.pi (Fin M)).pi (Fin n)).exists_selfDual (fun X Y => L (BR (Ainf F) σ J X Y))
      (fun X Y Y' => by rw [BR_add_right, map_add])
      (fun X => hLc.comp (continuous_BR (Ainf F) σ J X))
      (fun X Y => by rw [BR_comm (Ainf F) σ hσ hJ.1])
      (fun X h => BR_nondeg (Ainf F) σ L hLn hσ hJ.2 X h) _ (fun X Y => hLx _)
  · exact (hasCoord_herm (Ainf F) σ hA n hσ).exists_selfDual
      (fun S T => L (pairHerm (Ainf F) σ n S T))
      (fun S T T' => by rw [pairHerm_add_right, map_add])
      (fun S => hLc.comp (continuous_pairHerm (Ainf F) σ n S))
      (fun S T => by rw [pairHerm_comm])
      (fun S h => pairHerm_nondeg (Ainf F) σ L hLn hσ n S h) _ (fun S T => hLx _)
end GlobalTheory.CompanionTheory.SelfDualInf
