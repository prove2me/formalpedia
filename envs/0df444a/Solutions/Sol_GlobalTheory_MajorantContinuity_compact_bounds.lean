-- Prove2me | solution 1 for GlobalTheory.MajorantContinuity.compact_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:33.241934+00:00
-- url     : https://prove2.me/submissions/56f50bdb-f181-4910-9b10-a0773cce5b0d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable
import Theorems.Thm_GlobalTheory_MajorantContinuity_maj_real_smul
import Theorems.Thm_GlobalTheory_MajorantContinuity_continuousAt_maj
import Theorems.Thm_GlobalTheory_MajorantContinuity_exists_sphere
import Theorems.Thm_GlobalTheory_MajorantContinuity_maj_at_zero
import Theorems.Thm_GlobalTheory_MajorantContinuity_ne_zero_of_sphere
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder
open GlobalTheory GlobalTheory.MajorantContinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MajorantContinuity
theorem _root_.solution {r : ℕ} (X : Data E r) {K : Set (Frame X.Ψ r)} (hK : IsCompact K)
    (hKd : K ⊆ X.dom) : ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2 := by
  classical
  have hKS := hK.prod (isCompact_sphere (0 : Fin r → ℂ) 1)
  have hcont : ∀ τ : X.Ψ, ContinuousOn (fun p : Frame X.Ψ r × (Fin r → ℂ) => X.maj p.1 τ p.2)
      (K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1) :=
    fun τ => continuousOn_of_forall_continuousAt fun p hp => continuousAt_maj X τ (hKd hp.1) p.2
  have hlow : ∀ τ : X.Ψ, ∃ c', 0 < c' ∧ ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1,
      c' ≤ X.maj p.1 τ p.2 :=
    fun τ => hKS.exists_forall_le' (hcont τ) fun p hp => X.maj_pos (hKd hp.1) τ (ne_zero_of_sphere hp.2)
  have hup : ∀ τ : X.Ψ, ∃ C', ∀ p ∈ K ×ˢ Metric.sphere (0 : Fin r → ℂ) 1, ‖X.maj p.1 τ p.2‖ ≤ C' :=
    fun τ => hKS.exists_bound_of_continuousOn (hcont τ)
  choose cτ hcpos hcle using hlow
  choose Cτ hCle using hup
  have hsum : 0 ≤ ∑ σ, (cτ σ)⁻¹ := Finset.sum_nonneg fun σ _ => (inv_pos.2 (hcpos σ)).le
  refine ⟨(1 + ∑ σ, (cτ σ)⁻¹)⁻¹, ∑ σ, |Cτ σ|, inv_pos.2 (by linarith), ?_⟩
  intro x hx τ v
  have hc_le : (1 + ∑ σ, (cτ σ)⁻¹)⁻¹ ≤ cτ τ := by
    have h1 : (cτ τ)⁻¹ ≤ ∑ σ, (cτ σ)⁻¹ :=
      Finset.single_le_sum (f := fun σ => (cτ σ)⁻¹) (fun σ _ => (inv_pos.2 (hcpos σ)).le)
        (Finset.mem_univ τ)
    rw [inv_le_comm₀ (by linarith) (hcpos τ)]
    linarith
  have hC_le : Cτ τ ≤ ∑ σ, |Cτ σ| :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun σ => |Cτ σ|) (fun σ _ => abs_nonneg _)
      (Finset.mem_univ τ))
  rcases eq_or_ne v 0 with rfl | hv
  · simp [maj_at_zero]
  obtain ⟨w, hw, hvw⟩ := exists_sphere hv
  have hm : X.maj x τ v = ‖v‖ ^ 2 * X.maj x τ w := by
    conv_lhs => rw [hvw]
    exact maj_real_smul X x τ _ w
  have hlo : cτ τ ≤ X.maj x τ w := hcle τ (x, w) ⟨hx, hw⟩
  have hhi : X.maj x τ w ≤ Cτ τ := (le_abs_self _).trans
    ((Real.norm_eq_abs _).symm.trans_le (hCle τ (x, w) ⟨hx, hw⟩))
  have ht : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  rw [hm]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left (hc_le.trans hlo) ht]
  · nlinarith [mul_le_mul_of_nonneg_left (hhi.trans hC_le) ht]
end GlobalTheory.MajorantContinuity
