-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.exists_ballLat_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:51.069149+00:00
-- url     : https://prove2.me/submissions/0a732e85-8a66-4b52-9c9f-98d3ccfe017d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UniformLattices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {m : Type} [Fintype m]
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution {V : Set (m → k)} (hV : V ∈ 𝓝 (0 : m → k)) :
    ∃ s : kˣ, (ballLat m s : Set (m → k)) ⊆ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, h⟩ := hV
  obtain ⟨s, hs⟩ := exists_cball_subset (U := ⋂ i, t i) (iInter_mem.2 ht)
  exact ⟨s, fun x hx => h fun i _ => Set.mem_iInter.1 (hs (hx i)) i⟩
end GlobalTheory.RootEx.UniformLattices
