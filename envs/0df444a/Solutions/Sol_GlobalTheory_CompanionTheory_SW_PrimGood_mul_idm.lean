-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.mul_idm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:28.32422+00:00
-- url     : https://prove2.me/submissions/f9d655d9-59eb-4159-8858-38a2f2afb633

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_coord_eq

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
theorem _root_.solution (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ) (h2 : (2 : L) ≠ 0) {s : L}
    (hs0 : s ≠ 0) (hs : s * s = Δ) (x : K) : x * idm B s = ev B s x • idm B s := by
  have hd : B 1 * idm B s = algebraMap L K s * idm B s := by
    unfold idm
    rw [Algebra.smul_def, Algebra.smul_def, h0, mul_one]
    have e1 : algebraMap L K s * algebraMap L K (2 * s)⁻¹ = algebraMap L K (2⁻¹ : L) := by
      rw [← map_mul]; congr 1; field_simp
    have e2 : algebraMap L K (2 * s)⁻¹ * algebraMap L K Δ =
        algebraMap L K s * algebraMap L K (2⁻¹ : L) := by
      rw [← map_mul, ← map_mul, ← hs]; congr 1; field_simp
    linear_combination (algebraMap L K (2 * s)⁻¹) * h1 + e2 - B 1 * e1
  have hx := coord_eq h0 x
  calc x * idm B s = (algebraMap L K (B.repr x 0) + algebraMap L K (B.repr x 1) * B 1) * idm B s :=
        congrArg (· * idm B s) hx
    _ = ev B s x • idm B s := by
      unfold ev
      rw [Algebra.smul_def, map_add, map_mul]
      linear_combination (algebraMap L K (B.repr x 1)) * hd
end GlobalTheory.CompanionTheory.SW.PrimGood
