-- Prove2me | solution 1 for GlobalTheory.DeformedSum.Bound.dTerm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:26:30.363852+00:00
-- url     : https://prove2.me/submissions/6c089197-7968-4cb4-b8ef-a1df1e1f334c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DeformedProductDerivativeTermNormLeUniform
import Theorems.Thm_GlobalTheory_DeformedSum_Bound_factor_le
import Theorems.Thm_GlobalTheory_CMVal_TermUnit_prod_norm_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DeformedSum GlobalTheory.DeformedSum.Bound
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.DeformedSum.Bound
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (s : ℕ) (m : I → ℕ) (r : ℝ), r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) → ∀ x : E, x ≠ 0 →
      ‖dTerm φ (2 * s) m z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) := by
  intro E _ _ _ I _ φ hφ s m r hr
  refine ⟨∏ i, (‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (((2 * s : ℕ) : ℂ) + j)‖ * ((1 - r)⁻¹) ^ (2 * s + m i)),
    fun z hz x hx => ?_⟩
  have hN : |(Algebra.norm ℚ x : ℝ)| ^ (-(s : ℝ)) = ∏ i, (‖φ i x‖⁻¹) ^ (2 * s) := by
    rw [← TermUnit.prod_norm_sq hφ x, Real.rpow_neg (Finset.prod_nonneg fun i _ => by positivity), Real.rpow_natCast,
      ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_mul, inv_pow, inv_pow]
  rw [hN, ← Finset.prod_mul_distrib, dTerm, norm_prod]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  exact factor_le φ (2 * s) m z x hx i hr (hz i)
end GlobalTheory.DeformedSum.Bound
