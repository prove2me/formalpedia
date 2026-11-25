-- Prove2me | solution 1 for GlobalTheory.MassOrth.inv_mem_biInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:50:22.563532+00:00
-- url     : https://prove2.me/submissions/f4acedb4-3b00-4c92-b059-0545b7a2f45a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Theorems.Thm_GlobalTheory_MassOrth_coe_starInt
import Theorems.Thm_GlobalTheory_MassOrth_mem_hcompl_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MassOrth
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.MassOrth
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∈ hcompl (K := K) w.asIdeal) :
    algebraMap (𝓞 K) K s ≠ 0 ∧ (algebraMap (𝓞 K) K s)⁻¹ ∈ biInt (w.valuation K) := by
  obtain ⟨h1, h2⟩ := (mem_hcompl_iff _ w.isPrime s).1 hs
  have v1 : w.valuation K (algebraMap (𝓞 K) K s) = 1 := w.valuation_eq_one_iff_notMem.2 h1
  have v2 : w.valuation K (algebraMap (𝓞 K) K (starInt s)) = 1 := w.valuation_eq_one_iff_notMem.2 h2
  refine ⟨fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at v1; exact zero_ne_one v1
  · rw [map_inv₀, v1, inv_one]
  · rw [star_inv₀, map_inv₀, ← coe_starInt, v2, inv_one]
end GlobalTheory.MassOrth
