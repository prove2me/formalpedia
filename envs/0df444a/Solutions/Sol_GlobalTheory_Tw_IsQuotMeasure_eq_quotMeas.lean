-- Prove2me | solution 1 for GlobalTheory.Tw.IsQuotMeasure.eq_quotMeas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:11.872576+00:00
-- url     : https://prove2.me/submissions/1489a43f-4469-475e-a0f8-3094a5f5f6d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
import Theorems.Thm_GlobalTheory_Tw_exists_isCosetCutoff
import Theorems.Thm_GlobalTheory_Tw_IsQuotMeasure_eq_map
import Theorems.Thm_GlobalTheory_Tw_isQuotMeasure_quotMeas

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
namespace IsQuotMeasure
theorem _root_.solution (hT : IsClosed (T : Set G)) {ν : Measure (RCoset T)} (hν : IsQuotMeasure T μ μT ν) :
    ν = quotMeas T μ μT := by
  obtain ⟨β, -, hβ⟩ := exists_isCosetCutoff (μT := μT) hT
  rw [hν.eq_map hβ, (isQuotMeasure_quotMeas hT).eq_map hβ]
end IsQuotMeasure
end GlobalTheory.Tw
