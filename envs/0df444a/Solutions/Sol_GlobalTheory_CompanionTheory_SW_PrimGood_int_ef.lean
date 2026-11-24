-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.int_ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:26.862739+00:00
-- url     : https://prove2.me/submissions/fcd324df-5738-4ec7-88a2-6e3c4b1a6e6f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll

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
theorem _root_.solution {e f : K} (he : ∀ l, w (B.repr e l) ≤ 1) (hf : ∀ l, w (B.repr f l) ≤ 1) {α β : L}
    (hα : w α ≤ 1) (hβ : w β ≤ 1) (l : Fin 2) : w (B.repr (α • e + β • f) l) ≤ 1 := by
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  refine (w.map_add _ _).trans (max_le ?_ ?_)
  · rw [map_mul]; exact mul_le_one' hα (he l)
  · rw [map_mul]; exact mul_le_one' hβ (hf l)
end GlobalTheory.CompanionTheory.SW.PrimGood
