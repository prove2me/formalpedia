-- Prove2me | solution 1 for GlobalTheory.MaxLatDet.val_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:01:57.521555+00:00
-- url     : https://prove2.me/submissions/55bdd190-dfb6-42cc-a465-af83ddc87942

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDet
import Theorems.Thm_GlobalTheory_MaxLatDet_mem_locR_iff_le
import Theorems.Thm_GlobalTheory_MassOrth_mem_locR_iff


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
open GlobalTheory GlobalTheory.MaxLatDet
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.MaxLatDet
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (hw : conjIdeal (K := K) w.asIdeal = w.asIdeal)
    (k : K) : w.valuation K (star k) = w.valuation K k := by
  have h1 : ∀ k : K, w.valuation K k ≤ 1 → w.valuation K (star k) ≤ 1 := fun k hk =>
    ((GlobalTheory.MassOrth.mem_locR_iff w k).1 ((mem_locR_iff_le w hw k).2 hk)).2
  have h2 : ∀ k : K, k ≠ 0 → w.valuation K (star k) ≤ w.valuation K k →
      w.valuation K k ≤ w.valuation K (star k) := by
    intro k hk hle
    have p1 : 0 < w.valuation K k := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hk)
    have p2 : 0 < w.valuation K (star k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (star_ne_zero.2 hk))
    have := h1 (star k / k) (by rw [map_div₀, div_le_one₀ p1]; exact hle)
    rwa [star_div₀, star_star, map_div₀, div_le_one₀ p2] at this
  by_cases hk : k = 0
  · rw [hk, star_zero]
  rcases le_total (w.valuation K (star k)) (w.valuation K k) with hle | hle
  · exact le_antisymm hle (h2 k hk hle)
  · refine le_antisymm ?_ hle
    have := h2 (star k) (star_ne_zero.2 hk) (by rwa [star_star])
    rwa [star_star] at this
end GlobalTheory.MaxLatDet
