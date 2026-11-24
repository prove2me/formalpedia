-- Prove2me | solution 1 for GlobalTheory.CovolumeOneSelfDual.continuous_periodization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:26.720607+00:00
-- url     : https://prove2.me/submissions/2f04b972-b119-4630-bb0f-0c69d7e710fc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierInversionZeroCompactQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SelfDualOfCovolumeOne
import Theorems.Thm_GlobalTheory_CovolumeOneSelfDual_finite_contributing

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
    [T2Space G] [LocallyCompactSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] {f : G → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) : Continuous fun x : G => ∑' γ : Γ, f (γ + x) := by
  have hlf : LocallyFinite fun γ : Γ => Function.support fun x : G => f (γ + x) := by
    intro x
    obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
    refine ⟨C, hx, (finite_contributing Γ hs hC).subset ?_⟩
    rintro γ ⟨p, h, h1⟩
    exact ⟨p, h1, h⟩
  have h : Continuous fun x : G => ∑ᶠ γ : Γ, f (γ + x) :=
    continuous_finsum (fun γ => by fun_prop) hlf
  refine h.congr fun x => (tsum_eq_finsum ?_).symm
  refine (finite_contributing Γ hs (isCompact_singleton (x := x))).subset ?_
  intro γ hγ
  exact ⟨x, rfl, hγ⟩
end GlobalTheory.CovolumeOneSelfDual
