-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.idm_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:21.404945+00:00
-- url     : https://prove2.me/submissions/7d695adf-e59d-46f8-b5eb-c2c095fe95b1

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
theorem _root_.solution (h0 : B 0 = 1) (h2 : (2 : L) ≠ 0) {s : L} (hs : s ≠ 0) :
    idm B s + idm B (-s) = 1 := by
  unfold idm
  have e : ((2 * -s)⁻¹ : L) = -(2 * s)⁻¹ := by field_simp
  rw [e, neg_smul, h0, Algebra.smul_def, mul_one]
  have e2 : algebraMap L K (2⁻¹ : L) + algebraMap L K (2⁻¹ : L) = 1 := by
    rw [← map_add, ← map_one (algebraMap L K)]; congr 1; field_simp; norm_num
  linear_combination e2
end GlobalTheory.CompanionTheory.SW.PrimGood
