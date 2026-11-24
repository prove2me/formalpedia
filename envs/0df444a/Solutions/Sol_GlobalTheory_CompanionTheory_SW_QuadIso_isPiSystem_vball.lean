-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadIso.isPiSystem_vball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:06:41.511419+00:00
-- url     : https://prove2.me/submissions/7a9afbf6-eacc-47e9-a910-23a44551efed

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_vball_eq_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
namespace GlobalTheory.CompanionTheory.SW.QuadIso
theorem _root_.solution :
    IsPiSystem {s : Set K | ∃ (x : K) (γ : ℤᵐ⁰), s = vball x γ ∧ IsRadius K γ} := by
  rintro _ ⟨x, γ, rfl, hγ⟩ _ ⟨y, δ, rfl, hδ⟩ ⟨z, hzx, hzy⟩
  rcases le_total γ δ with h | h
  · refine ⟨x, γ, ?_, hγ⟩
    rw [← vball_eq_of_mem hzx, ← vball_eq_of_mem hzy]
    refine Set.inter_eq_left.2 fun w hw => lt_of_lt_of_le hw h
  · refine ⟨y, δ, ?_, hδ⟩
    rw [← vball_eq_of_mem hzx, ← vball_eq_of_mem hzy]
    refine Set.inter_eq_right.2 fun w hw => lt_of_lt_of_le hw h
end GlobalTheory.CompanionTheory.SW.QuadIso
