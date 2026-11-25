-- Prove2me | solution 1 for GlobalTheory.SW.exists_short_independent_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:49.558313+00:00
-- url     : https://prove2.me/submissions/cc2f6f5f-923d-440a-b4c3-30b4cf0af69d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Theorems.Thm_GlobalTheory_SW_IsType_finrank_eq
import Theorems.Thm_GlobalTheory_SW_exists_linearIndependent_prod_norm_le
import Theorems.Thm_GlobalTheory_SW_posDef_map_mul_conjTranspose
import Theorems.Thm_GlobalTheory_SW_rowEmb_apply
import Theorems.Thm_GlobalTheory_SW_det_gram_rowEmb
import Theorems.Thm_GlobalTheory_SW_IsType_prod_det_eq_sq
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot


attribute [local simp] GlobalTheory.SW.rowEmb_apply

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ →
      ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (m : Type) [Fintype m] (W : Matrix (Fin N) m E),
        LinearIndependent E (fun i => W i) → ∃ a : Matrix (Fin N) (Fin N) E, IntM a ∧ a.det ≠ 0 ∧
          ∏ i, (∑ τ : Ψ, ∑ j, ‖τ.1 ((a * W) i j)‖ ^ 2) ^ Ψ.card ≤
            C * ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re := by
  classical
  intro E _ _ _ Ψ hΨ N
  set ω : (E →+* ℂ) → E := fun k => integralBasis E (equivReindex E k) with hω
  have hωi : ∀ k, IsIntegral ℤ (ω k) := fun k => by
    rw [hω]; simp only [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  set A : Matrix (E →+* ℂ) (E →+* ℂ) ℂ := Matrix.of fun k σ : E →+* ℂ => σ (ω k) with hA
  have hA0 : A.det ≠ 0 := by
    have : A = basisMatrix E := by
      ext k σ
      simp only [hA, hω, basisMatrix, of_apply, canonicalEmbedding.latticeBasis_apply,
        canonicalEmbedding.apply_at]
    rw [this]; exact det_of_basisMatrix_non_zero E
  set n : ℕ := Fintype.card (Fin N × (E →+* ℂ)) with hn
  have hc : 0 < (n : ℝ) ^ ((n : ℝ) / 2) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · positivity
  have hA1 : 0 < ‖A.det‖ := norm_pos_iff.2 hA0
  refine ⟨(n : ℝ) ^ ((n : ℝ) / 2) * ‖A.det‖ ^ N, by positivity, fun m _ W hW => ?_⟩
  have hpos : 0 < ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re :=
    Finset.prod_pos fun τ _ => (Complex.pos_iff.1 (posDef_map_mul_conjTranspose hW τ.1).det_pos).1
  have hdet : (gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).det =
      (‖A.det‖ ^ N * ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re) ^ 2 := by
    have h := det_gram_rowEmb W ω
    rw [hΨ.prod_det_eq_sq, normSq_eq_norm_sq] at h
    rw [mul_pow, ← pow_mul, mul_comm N, pow_mul]
    exact_mod_cast h
  obtain ⟨a, ha, hai, hle⟩ := exists_linearIndependent_prod_norm_le (E := E) (N := N)
    (by rw [Fintype.card_prod, Fintype.card_fin, Embeddings.card, mul_comm]) (rowEmb W) (fun p : Fin N × (E →+* ℂ) => Pi.single p.1 (ω p.2))
    (det_gram_ne_zero_iff_linearIndependent.1 (by rw [hdet]; positivity))
  refine ⟨Matrix.of a, fun i => ?_, ?_, ?_⟩
  · show ∀ j, IsIntegral ℤ (a i j)
    refine Submodule.span_induction (p := fun t _ => ∀ j, IsIntegral ℤ (t j)) ?_ ?_ ?_ ?_ (hai i)
    · rintro _ ⟨p, rfl⟩ j
      simp only [Pi.single_apply]
      split_ifs
      · exact hωi _
      · exact isIntegral_zero
    · exact fun _ => isIntegral_zero
    · exact fun x y _ _ hx hy j => (hx j).add (hy j)
    · exact fun c x _ hx j => (hx j).smul c
  · exact ((Matrix.isUnit_iff_isUnit_det _).1
      (linearIndependent_rows_iff_isUnit.1 (show LinearIndependent E (Matrix.of a).row from ha))).ne_zero
  · rw [hdet, Real.sqrt_sq (by positivity), ← mul_assoc, hΨ.finrank_eq] at hle
    refine le_trans (Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_) hle
    rw [pow_mul, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [Finset.sum_coe_sort Ψ (fun τ => ∑ j, ‖τ ((Matrix.of a * W) i j)‖ ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Ψ)
      (f := fun τ => ∑ j, ‖τ ((Matrix.of a * W) i j)‖ ^ 2) fun _ _ _ => by positivity
end GlobalTheory.SW
