-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:08:20.031855+00:00
-- url     : https://prove2.me/submissions/e525f2c9-2cf6-4e92-8dbb-b545b1738776

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_inert_case
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_split_case

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimGood
variable {L K : Type} [Field L] [CommRing K] [Algebra L K] (B : Module.Basis (Fin 2) L K)
variable {B} {Δ : L}
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ)
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ)
    (hsq : ∀ x : L, w (x - 1) < 1 → IsSquare x) (h2 : w (2 : L) = 1) (hΔ : w Δ = 1)
    {M : ℕ} (y z : Fin M → K) (hz : z ⬝ᵥ y = 1) :
    ∃ (u : Kˣ) (z' : Fin M → K), (∀ k l, w (B.repr ((u : K) * y k) l) ≤ 1) ∧
      (∀ k l, w (B.repr (z' k) l) ≤ 1) ∧ ∑ k, z' k * ((u : K) * y k) = 1 := by
  by_cases hn : IsSquare Δ
  · obtain ⟨s, hs⟩ := hn
    exact split_case w h0 h1 h2 hΔ hs.symm y z hz
  · exact inert_case w h0 h1 hsq hΔ hn y z hz
end GlobalTheory.CompanionTheory.SW.PrimGood
