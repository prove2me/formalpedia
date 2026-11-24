-- Prove2me | solution 1 for GlobalTheory.DoubleCosetAdjoint.preimage_preimage_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:48.170608+00:00
-- url     : https://prove2.me/submissions/5e8c32e7-79c6-497d-a635-e955c3f35e4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSumFundamentalDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.DoubleCosetAdjoint
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)
omit [μ.IsMulLeftInvariant] [Countable Γ] [μ.IsMulRightInvariant] [TopologicalSpace H]
  [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
namespace GlobalTheory.DoubleCosetAdjoint
theorem _root_.solution (y : H) :
    (fun h => h * y) ⁻¹' ((fun h => h * y⁻¹) ⁻¹' 𝓕) = 𝓕 := by
  ext h; simp
end GlobalTheory.DoubleCosetAdjoint
