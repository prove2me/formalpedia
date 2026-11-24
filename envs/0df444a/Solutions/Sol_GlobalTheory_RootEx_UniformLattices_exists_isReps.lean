-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.exists_isReps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:45.581348+00:00
-- url     : https://prove2.me/submissions/df085fbb-8e11-4bcd-a434-44944582d6c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution (D B : AddSubgroup V) (hD : IsCompact (D : Set V)) (hB : IsOpen (B : Set V)) :
    ∃ T, IsReps D B T := by
  classical
  haveI : DiscreteTopology (V ⧸ B) := QuotientAddGroup.discreteTopology hB
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ B) '' D).Finite :=
    (hD.image QuotientAddGroup.continuous_mk).finite_of_discrete
  have hs : ∀ q : V ⧸ B, ∃ v : V, q ∈ (QuotientAddGroup.mk : V → V ⧸ B) '' D →
      v ∈ D ∧ (QuotientAddGroup.mk v : V ⧸ B) = q := fun q => by
    by_cases h : q ∈ (QuotientAddGroup.mk : V → V ⧸ B) '' D
    · obtain ⟨v, hv, e⟩ := h
      exact ⟨v, fun _ => ⟨hv, e⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose s hs using hs
  refine ⟨hfin.toFinset.image s, fun t ht => ?_, fun β hβ => ⟨s β, ⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    exact (hs q (by simpa using hq)).1
  · exact Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 ⟨β, hβ, rfl⟩)
  · exact QuotientAddGroup.eq_iff_sub_mem.1 (hs β ⟨β, hβ, rfl⟩).2.symm
  · rintro t ⟨ht, h⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    rw [QuotientAddGroup.eq_iff_sub_mem.2 h, (hs q (hfin.mem_toFinset.1 hq)).2]
end GlobalTheory.RootEx.UniformLattices
