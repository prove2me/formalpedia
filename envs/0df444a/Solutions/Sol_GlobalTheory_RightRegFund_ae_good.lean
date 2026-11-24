-- Prove2me | solution 1 for GlobalTheory.RightRegFund.ae_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:48.771966+00:00
-- url     : https://prove2.me/submissions/6789a583-db41-499b-8e56-14fc54c80f96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise
open GlobalTheory GlobalTheory.RightRegFund
variable {G : Type} [Group G]
variable {Γ : Subgroup G} {D : Set G} {r : G → G}
variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ]
namespace GlobalTheory.RightRegFund
theorem _root_.solution (hD : IsFundamentalDomain Γ D μ) : ∀ᵐ y ∂μ, Good Γ D y := by
  unfold Good
  refine ae_all_iff.2 fun γ => ae_all_iff.2 fun γ' => ?_
  by_cases h : γ = γ'
  · exact Eventually.of_forall fun _ _ _ => h
  · have h' : γ⁻¹ ≠ γ'⁻¹ := fun e => h (inv_injective e)
    have := hD.aedisjoint h'
    refine (measure_eq_zero_iff_ae_notMem.1 this).mono fun y hy h1 h2 => absurd ?_ hy
    refine ⟨?_, ?_⟩
    · exact mem_inv_smul_set_iff.2 h1
    · exact mem_inv_smul_set_iff.2 h2
end GlobalTheory.RightRegFund
