-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.modular_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:48.058708+00:00
-- url     : https://prove2.me/submissions/2e15198c-1831-4464-a2a5-fa7abec5289c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
import Theorems.Thm_GlobalTheory_LevelUnimod_modular_bdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
open GlobalTheory GlobalTheory.LevelUnimod
open scoped Pointwise NNReal ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.LevelUnimod
theorem _root_.solution
    (h : ∀ g : G, ∀ U ∈ nhds (1 : G), ∃ g' ∈ U, Measure.modularCharacter g' = Measure.modularCharacter g) (g : G) :
    Measure.modularCharacter g = 1 := by
  obtain ⟨K, hK, C, hC⟩ := modular_bdd (G := G)
  have hb : ∀ x : G, Measure.modularCharacter x ≤ C := fun x => by
    obtain ⟨e, h1, h2⟩ := h x K hK
    rw [← h2]
    exact hC _ h1
  have hle : ∀ x : G, Measure.modularCharacter x ≤ 1 := fun x => by
    by_contra hx
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.1 hx)
    rw [← map_pow] at hk
    exact absurd (hb _) (not_le.2 hk)
  refine le_antisymm (hle g) ?_
  calc (1 : ℝ≥0) = Measure.modularCharacter g * Measure.modularCharacter g⁻¹ := by
        rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ Measure.modularCharacter g * 1 := by gcongr; exact hle _
    _ = _ := mul_one _
end GlobalTheory.LevelUnimod
