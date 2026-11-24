-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:03.683319+00:00
-- url     : https://prove2.me/submissions/52924160-626a-4d29-a4c3-26c646ee253c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_repr_coord
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_coord_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_repr_mul

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
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ) (x : K)
    (hN : nrm B Δ x ≠ 0) : ∃ x', x * x' = 1 := by
  refine ⟨(nrm B Δ x)⁻¹ • (B.repr x 0 • B 0 + (-B.repr x 1) • B 1), ?_⟩
  have hc := repr_coord B (B.repr x 0) (-B.repr x 1)
  obtain ⟨e0, e1⟩ := repr_mul h0 h1 x (B.repr x 0 • B 0 + (-B.repr x 1) • B 1)
  rw [hc.1, hc.2] at e0 e1
  have hxx : x * (B.repr x 0 • B 0 + (-B.repr x 1) • B 1) = algebraMap L K (nrm B Δ x) := by
    rw [coord_eq h0 (x * (B.repr x 0 • B 0 + (-B.repr x 1) • B 1)), e0, e1]
    have : B.repr x 0 * B.repr x 0 + Δ * (B.repr x 1 * -B.repr x 1) = nrm B Δ x := by
      unfold nrm; ring
    have h' : B.repr x 0 * -B.repr x 1 + B.repr x 1 * B.repr x 0 = 0 := by ring
    rw [this, h']; simp
  rw [mul_smul_comm, hxx, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hN, map_one]
end GlobalTheory.CompanionTheory.SW.PrimGood
