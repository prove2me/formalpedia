-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Pack.finrank_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:49:09.6698+00:00
-- url     : https://prove2.me/submissions/1d36949e-06d0-4ba1-a092-bce4f0de6ace

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBoundStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicBoxLatticeCountRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Pack
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.Pack
theorem _root_.solution (hF : IsTotallyReal F) (d M : ℕ) :
    Module.finrank ℝ (PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ)) =
      d * Module.finrank ℚ F * M := by
  have h : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    simp only [IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
    omega
  rw [(WithLp.linearEquiv 1 ℝ _).finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_prod, Fintype.card_fin, h]
  ring
end GlobalTheory.CompanionTheory.SW.Pack
