-- Prove2me | solution 1 for GlobalTheory.RightRegFund.lintegral_comp_rep_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:14:59.817859+00:00
-- url     : https://prove2.me/submissions/4b80bd07-e18e-435a-b26a-22816cf6ec5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
import Theorems.Thm_GlobalTheory_RightRegFund_Good_mul
import Theorems.Thm_GlobalTheory_RightRegFund_good_mul_iff
import Theorems.Thm_GlobalTheory_RightRegFund_rep_mul
import Theorems.Thm_GlobalTheory_RightRegFund_ae_good
import Theorems.Thm_GlobalTheory_RightRegFund_ae_rep_eq_self
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
namespace GlobalTheory.RightRegFund
theorem _root_.solution (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) (φ : G → ℝ≥0∞) (g : G) :
    ∫⁻ x in D, φ (r (x * g)) ∂μ = ∫⁻ x in D, φ x ∂μ := by
  classical
  let ψ : G → ℝ≥0∞ := fun y => if Good Γ D y then φ (r y) else 0
  have hψ : ∀ (γ : Γ) (y : G), ψ (γ • y) = ψ y := by
    intro γ y
    change ψ ((γ : G) * y) = ψ y
    by_cases h : Good Γ D y
    · simp only [ψ, if_pos h, if_pos (h.mul γ), rep_mul hr h]
    · simp only [ψ, if_neg h, if_neg (mt (good_mul_iff γ).1 h)]
  have hD' : IsFundamentalDomain Γ ((fun x => x * g⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => by
        change ((γ : G) * x) * g⁻¹ = (γ : G) * (x * g⁻¹)
        rw [mul_assoc]
  have h1 := (measurePreserving_mul_right μ g⁻¹).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulRight g⁻¹) (fun x => ψ (x * g)) D
  simp only [inv_mul_cancel_right] at h1
  calc ∫⁻ x in D, φ (r (x * g)) ∂μ = ∫⁻ x in D, ψ (x * g) ∂μ :=
        lintegral_congr_ae (ae_restrict_of_ae ((ae_good_mul hD g).mono fun y hy => by
          simp only [ψ, if_pos hy]))
    _ = ∫⁻ x in D, ψ x ∂μ := by rw [← h1]; exact hD'.setLIntegral_eq hD ψ hψ
    _ = ∫⁻ x in D, φ x ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (ae_good hD), ae_rep_eq_self hD hDm hr] with y hy h2
        simp only [ψ, if_pos hy, h2]
end GlobalTheory.RightRegFund
