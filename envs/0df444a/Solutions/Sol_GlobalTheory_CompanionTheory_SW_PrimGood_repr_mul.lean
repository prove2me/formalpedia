-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimGood.repr_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:45.595695+00:00
-- url     : https://prove2.me/submissions/7ab4d6dc-8153-4066-b74a-71ac691638b5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PrimitiveVectorLatticeRescaleAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimGood_repr_coord
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
namespace GlobalTheory.CompanionTheory.SW.PrimGood
theorem _root_.solution (h0 : B 0 = 1) (h1 : B 1 * B 1 = algebraMap L K Δ) (x y : K) :
    B.repr (x * y) 0 = B.repr x 0 * B.repr y 0 + Δ * (B.repr x 1 * B.repr y 1) ∧
    B.repr (x * y) 1 = B.repr x 0 * B.repr y 1 + B.repr x 1 * B.repr y 0 := by
  have hx := coord_eq h0 x
  have hy := coord_eq h0 y
  have e : x * y = (B.repr x 0 * B.repr y 0 + Δ * (B.repr x 1 * B.repr y 1)) • B 0 +
      (B.repr x 0 * B.repr y 1 + B.repr x 1 * B.repr y 0) • B 1 := by
    have e1 : x * y = (algebraMap L K (B.repr x 0) + algebraMap L K (B.repr x 1) * B 1) *
        (algebraMap L K (B.repr y 0) + algebraMap L K (B.repr y 1) * B 1) :=
      congrArg₂ (· * ·) hx hy
    rw [e1, Algebra.smul_def, Algebra.smul_def, h0]
    simp only [map_add, map_mul]
    linear_combination (algebraMap L K (B.repr x 1) * algebraMap L K (B.repr y 1)) * h1
  have := repr_coord B (B.repr x 0 * B.repr y 0 + Δ * (B.repr x 1 * B.repr y 1))
    (B.repr x 0 * B.repr y 1 + B.repr x 1 * B.repr y 0)
  rw [← e] at this
  exact this
end GlobalTheory.CompanionTheory.SW.PrimGood
