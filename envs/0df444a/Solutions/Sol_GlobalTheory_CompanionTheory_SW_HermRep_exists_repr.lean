-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermRep.exists_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:33.352832+00:00
-- url     : https://prove2.me/submissions/d9dc5960-046e-442d-8a1c-c847980c2872

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_EqIdOfFixed
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermRep_sig_sig
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermRep_exists_of_sig_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermRep_hE_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermRep_hE_add_right
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermRep_hE_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermRep
namespace GlobalTheory.CompanionTheory.SW.HermRep
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (T : Matrix (Fin (n + 1)) (Fin (n + 1)) E), IsHermND σ T → ∃ (t : F) (x : Fin (n + 1) → E), t ≠ 0 ∧ hE σ T x x = algebraMap F E t := by
  intro F E _ _ _ _ _ σ hσ n T hT
  obtain ⟨hH, hdet⟩ := hT
  by_cases hd : ∃ i, T i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    obtain ⟨t, ht⟩ := exists_of_sig_fixed hσ (hH i i)
    refine ⟨t, Pi.single i 1, ?_, ?_⟩
    · rintro rfl
      exact hi (by rw [← ht, map_zero])
    · rw [hE_single, ht]; simp
  · push_neg at hd
    obtain ⟨i, j, hij⟩ : ∃ i j, T i j ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hdet (by rw [show T = 0 from Matrix.ext hc, Matrix.det_zero])
    have hne : i ≠ j := by
      rintro rfl
      exact hij (hd i)
    refine ⟨2, Pi.single i (σ (T i j)⁻¹) + Pi.single j 1, two_ne_zero, ?_⟩
    have hji : T j i = σ (T i j) := (hH j i).symm
    have hs : σ (σ (T i j)⁻¹) = (T i j)⁻¹ := sig_sig hσ _
    rw [hE_add_left, hE_add_right, hE_add_right, hE_single, hE_single, hE_single, hE_single,
      hd i, hd j, hs, hji, map_one, map_ofNat, map_inv₀]
    have h1 : σ (T i j) ≠ 0 := (map_ne_zero _).2 hij
    field_simp
    ring
end GlobalTheory.CompanionTheory.SW.HermRep
