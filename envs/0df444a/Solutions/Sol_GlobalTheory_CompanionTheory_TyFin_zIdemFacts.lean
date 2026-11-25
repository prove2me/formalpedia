-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.zIdemFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:21:21.021547+00:00
-- url     : https://prove2.me/submissions/b147609e-f05d-42f0-af69-775620278cb1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentAction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_zIdem_act
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_eq_of_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.ZIdemFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Γ _ _ τ hτ
    refine ⟨eq_of_act _ _ fun W hW => ?_, fun a => eq_of_act _ _ fun W hW => ?_⟩
    · rw [map_mul, zIdem_act τ W hτ hW]
      split_ifs <;> simp
    · rw [map_mul, map_mul, zIdem_act τ W hτ hW]
      split_ifs <;> simp
  · intro Γ _ _ τ σ hτ hσ hne
    refine eq_of_act _ _ fun W hW => ?_
    rw [map_mul, map_zero, zIdem_act τ W hτ hW, zIdem_act σ W hσ hW]
    by_cases h1 : Nonempty (τ ≅ W)
    · by_cases h2 : Nonempty (σ ≅ W)
      · exact absurd ⟨h1.some ≪≫ h2.some.symm⟩ hne
      · simp [h2]
    · simp [h1]
  · intro Γ _ _ τ σ hτ hσ hiso
    rw [zIdem_act τ σ hτ hσ, if_pos hiso]
  · intro Γ _ _ I _ V hV hinj hex
    classical
    refine eq_of_act _ _ fun W hW => ?_
    obtain ⟨i₀, ⟨e⟩⟩ := hex W hW
    have hact : ∀ i, Representation.asAlgebraHom W.ρ (zIdem (V i)) =
        if i = i₀ then (1 : Module.End ℂ W) else 0 := by
      intro i
      rw [zIdem_act (V i) W (hV i) hW]
      by_cases hi : i = i₀
      · subst hi
        rw [if_pos ⟨e.symm⟩, if_pos rfl]
      · rw [if_neg (fun ⟨f⟩ => hi (hinj _ _ ⟨f ≪≫ e⟩)), if_neg hi]
    rw [map_sum, map_one, Finset.sum_congr rfl fun i _ => hact i]
    simp
end GlobalTheory.CompanionTheory.TyFin
