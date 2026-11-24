-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.isCompact_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:29.34535+00:00
-- url     : https://prove2.me/submissions/1ac92be8-7a97-4e59-b940-52b941ee541a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_GlobalTheory_RootEx_UniformLattices_perp_mem_nhds
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LatPair_isClopen_lattice
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_mem_SB_of
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UniformLattices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {m : Type} [Fintype m]
variable {ψ : AddChar k Circle}
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) [DecidableEq m] (L : Submodule 𝒪[k] (m → k))
    (hL : L.IsLattice k) : IsCompact (perp ψ L : Set (m → k)) := by
  have h := ExchangeSupport.mem_SB_of hψ1 ((perp ψ L : Set (m → k)).indicator fun _ => (1 : ℂ)) ?_ ?_
  · have h2 : IsCompact (closure _) := h.2
    rwa [Set.support_indicator, Function.support_const one_ne_zero, Set.inter_univ,
      (AddSubgroup.isClosed_of_isOpen _
        (AddSubgroup.isOpen_of_mem_nhds _ (perp_mem_nhds hψ L hL))).closure_eq] at h2
  · filter_upwards [perp_mem_nhds hψ L hL] with w hw u
    by_cases hu : u ∈ perp ψ L
    · rw [Set.indicator_of_mem (add_mem hu hw), Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem (fun h => hu (by simpa using sub_mem h hw)), Set.indicator_of_notMem hu]
  · filter_upwards [(LatPair.isClopen_lattice L).2.mem_nhds L.zero_mem] with β hβ u
    by_cases hu : u ∈ perp ψ L
    · rw [dotProduct_comm, hu β hβ]; simp
    · rw [Set.indicator_of_notMem hu, mul_zero]
end GlobalTheory.RootEx.UniformLattices
