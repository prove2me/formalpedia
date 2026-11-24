-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.RatCoord.sigma_hE_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:28:05.774098+00:00
-- url     : https://prove2.me/submissions/b9206191-ac74-4dc4-a2fc-39bd81af1b64

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateBijectionTraceForm
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_sigma_sigma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (y : Fin M → E) :
    σ (hE σ J y y) = hE σ J y y := by
  simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (σ : E →+* E) (y j) = σ (y j) := rfl
  have h2 : (σ : E →+* E) (y i) = σ (y i) := rfl
  rw [h1, h2, sigma_sigma hσ, hJ.1 i j]
  ring
end GlobalTheory.CompanionTheory.SW.BB.RatCoord
