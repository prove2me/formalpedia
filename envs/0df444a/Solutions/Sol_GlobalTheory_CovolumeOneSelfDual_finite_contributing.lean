-- Prove2me | solution 1 for GlobalTheory.CovolumeOneSelfDual.finite_contributing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:43:46.819384+00:00
-- url     : https://prove2.me/submissions/cfb3ee39-7ab6-45b8-ba7a-af426f9aeb74

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierInversionZeroCompactQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SelfDualOfCovolumeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory GlobalTheory.CovolumeOneSelfDual
namespace GlobalTheory.CovolumeOneSelfDual
theorem _root_.solution {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] (Γ : AddSubgroup G) [DiscreteTopology Γ] {f : G → ℂ} (hs : HasCompactSupport f)
    {C : Set G} (hC : IsCompact C) : {γ : Γ | ∃ x ∈ C, f (γ + x) ≠ 0}.Finite := by
  have hK := (hs.isCompact.prod hC).image (f := fun p : G × G => p.1 - p.2) (by fun_prop)
  have ht : Filter.Tendsto ((↑) : Γ → G) Filter.cofinite (Filter.cocompact G) :=
    AddSubgroup.tendsto_coe_cofinite_of_discrete Γ (isDiscrete_iff_discreteTopology.2 inferInstance)
  have hfin := ht hK.compl_mem_cocompact
  rw [Filter.mem_map, Filter.mem_cofinite] at hfin
  refine hfin.subset ?_
  rintro γ ⟨x, hx, h⟩ hn
  exact hn ⟨(γ + x, x), ⟨subset_tsupport f h, hx⟩, by simp⟩
end GlobalTheory.CovolumeOneSelfDual
