-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.natAbs_norm_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:04.321043+00:00
-- url     : https://prove2.me/submissions/95480edc-91fc-4a80-9acb-ceaccc062314

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.BoundedBasis
theorem _root_.solution {x : 𝓞 E} {a : ℝ} (h : ∀ σ : E →+* ℂ, ‖σ (x : E)‖ ≤ a) :
    ((Algebra.norm ℤ x).natAbs : ℝ) ≤ a ^ finrank ℚ E := by
  have h3 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (x : E))
  have h4 : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (x : E)‖ ≤ a ^ finrank ℚ E := by
    rw [← AlgHom.card ℚ E ℂ, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun σ _ => h σ.toRingHom
  rw [norm_prod, ← Algebra.coe_norm_int] at h3
  refine le_trans (le_of_eq ?_) (h3 ▸ h4)
  simp [Nat.cast_natAbs]
end GlobalTheory.BoundedBasis
