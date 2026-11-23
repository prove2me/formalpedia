-- Prove2me | solution 1 for GlobalTheory.abs_norm_eq_prod_cmType_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:46.190606+00:00
-- url     : https://prove2.me/submissions/1a6f3895-09b0-4580-8195-79127f74b4ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_AbsNormEqProdCmTypeSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (r : ℕ) (X : Data E r) (z : E), ((|Algebra.norm ℚ z| : ℚ) : ℝ) = ∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2) := by
  classical
  intro r X z

  have hall : ((Algebra.norm ℚ z : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ z := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), Algebra.norm_eq_prod_embeddings ℚ ℂ z]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl)

  have hcompl : ∏ σ ∈ X.Ψᶜ, σ z = ∏ τ ∈ X.Ψ, (starRingEnd ℂ) (τ z) := by
    refine Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      have h := X.cmType (ComplexEmbedding.conjugate σ)
      rw [ComplexEmbedding.involutive_conjugate E σ] at h
      exact h.mpr (Finset.mem_compl.mp hσ)
    · intro τ hτ
      exact Finset.mem_compl.mpr ((X.cmType τ).mp hτ)
    · intro σ _
      exact ComplexEmbedding.involutive_conjugate E σ
    · intro τ _
      exact ComplexEmbedding.involutive_conjugate E τ
    · intro σ _
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
  have hC : ((Algebra.norm ℚ z : ℚ) : ℂ) = ((∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2 : ℝ) : ℂ) := by
    rw [hall, ← Finset.prod_mul_prod_compl X.Ψ, hcompl, ← Finset.prod_mul_distrib,
      Finset.prod_coe_sort X.Ψ (fun τ => ‖τ z‖ ^ 2), Complex.ofReal_prod]
    refine Finset.prod_congr rfl (fun τ _ => ?_)
    rw [RCLike.mul_conj]
    push_cast
    rfl
  have hR : ((Algebra.norm ℚ z : ℚ) : ℝ) = ∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_ratCast]
    exact hC
  have hnn : (0 : ℚ) ≤ Algebra.norm ℚ z := by
    have h0 : (0 : ℝ) ≤ ((Algebra.norm ℚ z : ℚ) : ℝ) := by
      rw [hR]
      positivity
    exact_mod_cast h0
  rw [abs_of_nonneg hnn, hR]
end GlobalTheory
