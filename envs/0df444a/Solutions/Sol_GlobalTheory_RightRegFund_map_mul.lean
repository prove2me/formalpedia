-- Prove2me | solution 1 for GlobalTheory.RightRegFund.map_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:56:32.871437+00:00
-- url     : https://prove2.me/submissions/851b4ff7-f949-4175-a638-5a516d9a0b31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
import Theorems.Thm_GlobalTheory_RightRegFund_rep_mul
import Theorems.Thm_GlobalTheory_RightRegFund_ae_rep
import Theorems.Thm_GlobalTheory_RightRegFund_ae_good_mul

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
variable [μ.IsMulRightInvariant]
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
namespace GlobalTheory.RightRegFund
theorem _root_.solution (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) (g h : G) :
    R (g * h) = R g * R h := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  have h1 : ∀ᵐ y ∂μ, (R h F : G → ℂ) (r y) = F (r (y * h)) := by
    filter_upwards [ae_rep hDm hr (hR h F), ae_good_mul hD h] with y e1 e2
    obtain ⟨γ, e3, -⟩ := hr y
    rw [e1, e3, mul_assoc, rep_mul hr e2]
  have h2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1
  filter_upwards [hR (g * h) F, hR g (R h F), ae_restrict_of_ae h2] with x e1 e2 e3
  rw [e1, ContinuousLinearMap.mul_apply, e2, e3, mul_assoc]
end GlobalTheory.RightRegFund
