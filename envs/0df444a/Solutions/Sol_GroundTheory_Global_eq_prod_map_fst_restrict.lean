-- Prove2me | solution 1 for GroundTheory.Global.eq_prod_map_fst_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:24:29.854595+00:00
-- url     : https://prove2.me/submissions/a543fff5-b0f1-4fd8-bd3c-0f9ddcbeaaef

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace Real
open scoped NumberField.AdeleRing ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] [LocallyCompactSpace H] [SecondCountableTopology H]
namespace GroundTheory.Global
theorem _root_.solution (lam : Measure (G × H)) [lam.IsHaarMeasure]
    (ν : Measure H) [ν.IsHaarMeasure] {S : Set H} (hν : ν S = 1) :
    lam = (Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ S))).prod ν := by
  rw [map_fst_restrict_eq_smul_haar lam ν hν, Measure.prod_smul_left]
  exact Measure.isMulLeftInvariant_eq_smul lam _
end GroundTheory.Global
