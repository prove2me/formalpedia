-- Prove2me | solution 1 for GroundTheory.Global.isAddFundamentalDomain_fundamentalSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:43:43.471575+00:00
-- url     : https://prove2.me/submissions/5d660e10-7e6e-4f9b-8401-c4891fdd0016

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Theorems.Thm_GroundTheory_Global_measurableSet_fundamentalSet
import Theorems.Thm_GroundTheory_Global_existsUnique_sub_mem_fundamentalSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (fundamentalSet K)
      (adeleMeasure K) := by
  refine IsAddFundamentalDomain.mk' (measurableSet_fundamentalSet K).nullMeasurableSet fun x ↦ ?_
  obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_fundamentalSet K x
  refine ⟨⟨algebraMap K 𝔸[K] (-k), -k, rfl⟩, ?_, ?_⟩
  · change algebraMap K 𝔸[K] (-k) + x ∈ fundamentalSet K
    rwa [map_neg, neg_add_eq_sub]
  · rintro ⟨_, k', rfl⟩ h
    change algebraMap K 𝔸[K] k' + x ∈ fundamentalSet K at h
    have hk' : -k' = k := huniq (-k') (by
      change x - algebraMap K 𝔸[K] (-k') ∈ fundamentalSet K
      rwa [map_neg, sub_neg_eq_add, add_comm])
    refine Subtype.ext ?_
    change algebraMap K 𝔸[K] k' = algebraMap K 𝔸[K] (-k)
    rw [← hk', neg_neg]
end GroundTheory.Global
