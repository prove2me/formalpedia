-- Prove2me | solution 1 for GlobalTheory.DoubleCosetAdjoint.isFundamentalDomain_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:48.254956+00:00
-- url     : https://prove2.me/submissions/38b0c1ff-1ad4-4eb5-bc0a-4f49f0af4ebc

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
omit [μ.IsMulLeftInvariant] [Countable Γ]
namespace GlobalTheory.DoubleCosetAdjoint
theorem _root_.solution (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : H) :
    IsFundamentalDomain Γ ((fun h => h * y) ⁻¹' 𝓕) μ :=
  h𝓕.preimage_of_equiv (measurePreserving_mul_right μ y).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun g h => by
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc])
end GlobalTheory.DoubleCosetAdjoint
