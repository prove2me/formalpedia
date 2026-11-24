-- Prove2me | solution 1 for GlobalTheory.Tw.isQuotMeasure_quotMeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:43:32.44187+00:00
-- url     : https://prove2.me/submissions/5bba671a-4e76-4d82-b8dc-bdc3e4ef49d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
import Theorems.Thm_GlobalTheory_Tw_exists_isCosetCutoff
import Theorems.Thm_GlobalTheory_Tw_IsCosetCutoff_isQuotMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {T : Subgroup G} {μ : Measure G} {μT : Measure T}
variable [LocallyCompactSpace G] [T2Space G] [SFinite μ] [μ.IsMulLeftInvariant] [μT.IsHaarMeasure] [μT.IsInvInvariant]
namespace GlobalTheory.Tw
theorem _root_.solution (hT : IsClosed (T : Set G)) : IsQuotMeasure T μ μT (quotMeas T μ μT) := by
  obtain ⟨β, -, hβ⟩ := exists_isCosetCutoff (μT := μT) hT
  have : LocallyCompactSpace T := hT.locallyCompactSpace
  have : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set G)
  exact Classical.epsilon_spec ⟨_, hβ.isQuotMeasure⟩
end GlobalTheory.Tw
