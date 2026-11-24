-- Prove2me | solution 1 for GlobalTheory.T.lattice_fundamental_domain_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:20:39.646086+00:00
-- url     : https://prove2.me/submissions/921eb71f-b9a9-4d28-9544-a3a42cb9666f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolumeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ N : ℕ, 0 < N → (∃ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume) ∧ Countable (latR ρ N) ∧ (∀ y, y ∈ latR ρ N ↔ ∃ r : 𝓞 F, y = fun w => ρ w ((N : F) * (r : F))) ∧ ∀ D : Set (InfinitePlace F → ℝ), IsAddFundamentalDomain (latR ρ N) D volume → volume D = ENNReal.ofReal ((N : ℝ) ^ Module.finrank ℚ F * (kap F)⁻¹) ∧ ∀ β : F, β ≠ 0 → (∃ r : 𝓞 F, (r : F) = (N : F) * β) → ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.FD.main | exact GlobalTheory.CompanionTheory.SW.FD.main | (intros; apply GlobalTheory.CompanionTheory.SW.FD.main <;> assumption)
end _root_.GlobalTheory.T
