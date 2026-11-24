-- Prove2me | solution 1 for GlobalTheory.RightRegFund.ae_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:10.96882+00:00
-- url     : https://prove2.me/submissions/00a947f5-4c41-4b0a-ad94-593e83a08484

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
theorem _root_.solution (hDm : MeasurableSet D) (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    {p : G → Prop} (hp : ∀ᵐ x ∂(μ.restrict D), p x) : ∀ᵐ y ∂μ, p (r y) := by
  rw [ae_restrict_iff' hDm] at hp
  have : ∀ᵐ y ∂μ, ∀ γ : Γ, (γ : G) * y ∈ D → p (γ * y) :=
    ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae hp
  refine this.mono fun y hy => ?_
  obtain ⟨γ, h1, h2⟩ := hr y
  rw [h1] at h2 ⊢
  exact hy γ h2
end GlobalTheory.RightRegFund
