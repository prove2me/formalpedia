-- Prove2me | solution 1 for GlobalTheory.det_conj_strictLower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:50.133672+00:00
-- url     : https://prove2.me/submissions/385c12f0-038b-45c3-ae58-fce11af8f1bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetOfBlockTriangularInjective
import Theorems.Thm_GlobalTheory_det_of_blockTriangular_injective
import Theorems.Thm_GlobalTheory_prod_lowerPairs_fst
import Theorems.Thm_GlobalTheory_prod_lowerPairs_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (r : ℕ) (B : Matrix (Fin r) (Fin r) ℂ), B.det ≠ 0 → (∀ a c : Fin r, c < a → B a c = 0) → (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} => B p.1.1 q.1.1 * B⁻¹ q.1.2 p.1.2).det = ∏ a : Fin r, B a a ^ (2 * (a : ℤ) - ((r : ℤ) - 1))) := by
  intro r B hdet htri
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hu
  have hB : B.BlockTriangular id := fun a c h => htri a c h
  have hBi : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  have hdiag : ∀ a, B a a * B⁻¹ a a = 1 := by
    intro a
    have h1 : (B * B⁻¹) a a = 1 := by rw [Matrix.mul_nonsing_inv B hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · exact h1
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [htri a c h, zero_mul]
      · rw [hBi (i := c) (j := a) h, mul_zero]
    · simp
  have hne : ∀ a, B a a ≠ 0 := fun a => left_ne_zero_of_mul_eq_one (hdiag a)
  have hinv : ∀ a, B⁻¹ a a = (B a a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (hdiag a)
  rw [det_of_blockTriangular_injective _
    (fun p : {p : Fin r × Fin r // p.2 < p.1} => toLex (p.1.1, OrderDual.toDual p.1.2))]
  · simp only [Matrix.of_apply, hinv]
    rw [Finset.prod_mul_distrib, prod_lowerPairs_fst (fun a => B a a),
      prod_lowerPairs_snd (fun a => (B a a)⁻¹), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hne a)]
    congr 1
    have := a.2
    omega
  · intro p q h
    have h' := toLex.injective h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h'
    exact Subtype.ext (Prod.ext h'.1 h'.2)
  · intro p q h
    simp only [Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual] at h
    rcases h with h | ⟨_, h⟩
    · simp [htri _ _ h]
    · simp [hBi (i := q.1.2) (j := p.1.2) h]
end GlobalTheory
