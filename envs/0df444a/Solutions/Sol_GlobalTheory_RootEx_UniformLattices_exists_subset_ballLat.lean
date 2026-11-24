-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.exists_subset_ballLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:15:19.334366+00:00
-- url     : https://prove2.me/submissions/3a120c18-b0ed-4962-ab76-7774bd0a3141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
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
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution {K : Set (m → k)} (hK : IsCompact K) :
    ∃ s : kˣ, K ⊆ (ballLat m s : Set (m → k)) := by
  have hK' : IsCompact (⋃ i, (fun x : m → k => x i) '' K) :=
    isCompact_iUnion fun i => hK.image (continuous_apply i)
  obtain ⟨s, hs⟩ := hK'.elim_directed_cover (fun s : kˣ => cball s) isOpen_cball (fun x _ => by
    by_cases h : x = 0
    · exact Set.mem_iUnion.2 ⟨1, by simp [cball, h]⟩
    · exact Set.mem_iUnion.2 ⟨Units.mk0 x h, by simp [cball]⟩) fun a b => by
    rcases le_total (valuation k (a : k)) (valuation k (b : k)) with h | h
    · exact ⟨b, fun x (hx : x ∈ cball a) => le_trans (a := valuation k x) (c := valuation k (b : k)) hx h, subset_rfl⟩
    · exact ⟨a, subset_rfl, fun x (hx : x ∈ cball b) => le_trans (a := valuation k x) (c := valuation k (a : k)) hx h⟩
  exact ⟨s, fun x hx i => hs (Set.mem_iUnion.2 ⟨i, x, hx, rfl⟩)⟩
end GlobalTheory.RootEx.UniformLattices
