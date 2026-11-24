-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.ev_idm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:29:32.841316+00:00
-- url     : https://prove2.me/submissions/60a47e56-193a-48e2-badd-acf51671e204

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_repr_coord

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
theorem _root_.solution (h2 : (2 : L) ≠ 0) {s : L} (hs0 : s ≠ 0) :
    ev B s (idm B s) = 1 ∧ ev B s (idm B (-s)) = 0 := by
  have c1 := repr_coord B (2⁻¹ : L) ((2 * s)⁻¹ : L)
  have c2 := repr_coord B (2⁻¹ : L) ((2 * -s)⁻¹ : L)
  unfold ev idm
  rw [c1.1, c1.2, c2.1, c2.2]
  constructor <;> field_simp <;> ring
end GlobalTheory.CompanionTheory.SW.PrimGood
