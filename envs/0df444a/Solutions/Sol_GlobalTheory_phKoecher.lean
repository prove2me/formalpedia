-- Prove2me | solution 1 for GlobalTheory.phKoecher
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:35.411317+00:00
-- url     : https://prove2.me/submissions/34debc0c-abab-48d3-96b1-5d54767f8ff3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Theorems.Thm_GlobalTheory_Koecher_exists_siegel_fourierCoeff
import Theorems.Thm_GlobalTheory_Koecher_exists_lower_bound_of_mul_exp_neg_le
import Theorems.Thm_GlobalTheory_Koecher_posSemidef_of_rat_nonneg
import Theorems.Thm_GlobalTheory_Koecher_sum_mul_nonneg_of_posSemidef
import Theorems.Thm_GlobalTheory_Koecher_abs_apply_le_trace_of_posSemidef
import Theorems.Thm_GlobalTheory_Koecher_summable_exp_neg_mul_sum_abs
import Theorems.Thm_GlobalTheory_Koecher_bound_of_invariant
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_exists_congruence_trace_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key Koecher
namespace GlobalTheory
theorem _root_.solution : PhKoecherStatement := by
  intro g hg N hN F hF hper hinv c hc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  obtain ⟨hbd, a, ha0, ha1, ha2⟩ := exists_siegel_fourierCoeff hN hF hper
  have hc2 : 0 < c / 2 := by positivity
  obtain ⟨M, hM⟩ := hbd ((c / 2) • 1) (Matrix.PosDef.one.smul hc2)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM ((I * (c / 2 : ℝ)) • 1) (by simp [Matrix.IsSymm]) (by
      ext i j
      by_cases hij : i = j <;> simp [hij]))
  set s : ℝ := c / (4 * N) with hs
  have hs0 : 0 < s := by positivity

  have hA : ∀ A : Matrix (Fin g) (Fin g) ℝ, Aᵀ = -A → ∀ m, a m * Real.exp (-(2 * π *
      ∑ q, (m q : ℝ) * (s • (1 : Matrix (Fin g) (Fin g) ℝ) + A) q.1 q.2)) ≤ M := by
    intro A hA
    have e : (N : ℝ) • ((s • (1 : Matrix (Fin g) (Fin g) ℝ) + A) +
        (s • (1 : Matrix (Fin g) (Fin g) ℝ) + A)ᵀ) = (c / 2) • 1 := by
      rw [transpose_add, hA, transpose_smul, transpose_one, add_add_add_comm, add_neg_cancel,
        add_zero, ← add_smul, smul_smul]
      congr 1
      rw [hs]; field_simp; ring
    exact ha1 _ (by rw [e]; exact Matrix.PosDef.one.smul hc2) M (by rw [e]; exact hM)

  have hB : ∀ U : Matrix (Fin g) (Fin g) ℤ, U.det = 1 →
      (∀ i j, (N : ℤ) ∣ U i j - (1 : Matrix (Fin g) (Fin g) ℤ) i j) → ∀ m,
      a m * Real.exp (-(2 * π * ∑ q, (m q : ℝ) *
        (s • (U.map (Int.cast : ℤ → ℝ) * (U.map (Int.cast : ℤ → ℝ))ᵀ)) q.1 q.2)) ≤ M := by
    intro U hU hUN
    have e : (N : ℝ) • (s • (U.map (Int.cast : ℤ → ℝ) * (U.map (Int.cast : ℤ → ℝ))ᵀ) +
        (s • (U.map (Int.cast : ℤ → ℝ) * (U.map (Int.cast : ℤ → ℝ))ᵀ))ᵀ) =
        (c / 2) • (U.map (Int.cast : ℤ → ℝ) * (U.map (Int.cast : ℤ → ℝ))ᵀ) := by
      rw [transpose_smul, transpose_mul, transpose_transpose, ← add_smul, smul_smul]
      congr 1
      rw [hs]; field_simp; ring
    have hunit : IsUnit (U.map (Int.cast : ℤ → ℝ)) := by
      rw [Matrix.isUnit_iff_isUnit_det, ← Int.cast_det, hU]
      simp
    have hpd : (U.map (Int.cast : ℤ → ℝ) * (U.map (Int.cast : ℤ → ℝ))ᵀ).PosDef := by
      have := Matrix.PosDef.mul_conjTranspose_self (U.map (Int.cast : ℤ → ℝ))
        (Matrix.vecMul_injective_of_isUnit hunit)
      rwa [conjTranspose_eq_transpose_of_trivial] at this
    exact ha1 _ (by rw [e]; exact hpd.smul hc2) M
      (by rw [e]; exact bound_of_invariant hU (hinv U hU hUN) hc2 hM)

  have hpsd : ∀ m, 0 < a m →
      ((Matrix.of fun i j => m (i, j)).map (Int.cast : ℤ → ℝ)).PosSemidef := by
    intro m hm
    obtain ⟨B, hBr⟩ := exists_lower_bound_of_mul_exp_neg_le hm M
    set T : Matrix (Fin g) (Fin g) ℤ := Matrix.of fun i j => m (i, j) with hT
    have hsymm : T.IsSymm := by
      by_contra hne
      obtain ⟨i, j, hij⟩ : ∃ i j, m (i, j) ≠ m (j, i) := by
        by_contra hcon
        push Not at hcon
        exact hne (by ext i j; simp [hT, hcon i j])
      have hii : i ≠ j := fun h => hij (by rw [h])
      have hd : ((m (i, j) : ℝ) - m (j, i)) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hij)
      set r₀ : ℝ := ∑ q, (m q : ℝ) * (s • (1 : Matrix (Fin g) (Fin g) ℝ)) q.1 q.2 with hr₀
      set u : ℝ := ((B - 1) / (2 * π) - r₀) / ((m (i, j) : ℝ) - m (j, i)) with hu
      have h := hBr _ (hA (Matrix.single i j u - Matrix.single j i u)
        (by rw [transpose_sub, transpose_single, transpose_single, neg_sub]) m)
      have e : ∑ q, (m q : ℝ) * (s • (1 : Matrix (Fin g) (Fin g) ℝ) +
          (Matrix.single i j u - Matrix.single j i u)) q.1 q.2 =
          r₀ + u * ((m (i, j) : ℝ) - m (j, i)) := by
        have h1 : ∀ k l : Fin g, ∑ q : Fin g × Fin g, (m q : ℝ) * Matrix.single k l u q.1 q.2 =
            m (k, l) * u := fun k l => by
          rw [Finset.sum_eq_single (k, l)]
          · simp
          · rintro ⟨k', l'⟩ _ hq
            rw [Matrix.single_apply_of_ne, mul_zero]
            rintro ⟨rfl, rfl⟩
            exact hq rfl
          · simp
        simp only [Matrix.add_apply, Matrix.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, h1, ← hr₀]
        ring
      rw [e, hu, div_mul_cancel₀ _ hd, add_sub_cancel, mul_div_cancel₀ _ (by positivity)] at h
      linarith
    refine posSemidef_of_rat_nonneg hsymm fun v => ?_
    by_contra hv
    push Not at hv
    obtain ⟨k, hk⟩ := exists_rat_lt (B / (2 * π * s))
    obtain ⟨U, hU, hUN, hlt⟩ := exists_congruence_trace_lt g N hg hN
      (T.map (Int.cast : ℤ → ℚ)) (hsymm.map _) ⟨v, hv⟩ k
    have h := hBr _ (hB U hU hUN m)
    have e : ∑ q, (m q : ℝ) *
        (s • (U.map (Int.cast : ℤ → ℝ) * (U.map (Int.cast : ℤ → ℝ))ᵀ)) q.1 q.2 =
        s * ((((U.map (Int.cast : ℤ → ℚ)).transpose * T.map (Int.cast : ℤ → ℚ) *
          U.map (Int.cast : ℤ → ℚ)).trace : ℚ) : ℝ) := by
      rw [Matrix.trace_mul_cycle]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply (M := _ * _), Matrix.map_apply, hT,
        Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum]
      push_cast
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.mul_apply, transpose_apply, Matrix.map_apply]
      push_cast
      simp only [mul_comm ((U j _ : ℤ) : ℝ)]
      ring
    rw [e] at h
    have hlt' := (Rat.cast_lt (K := ℝ)).2 hlt
    have h3 := hlt'.trans hk
    rw [lt_div_iff₀ (by positivity)] at h3
    linarith

  set ε : ℝ := π * c / (2 * N * g ^ 2) with hε
  have hε0 : 0 < ε := by positivity
  refine ⟨∑' m : Fin g × Fin g → ℤ, M * Real.exp (-(ε * ∑ q, |(m q : ℝ)|)), fun τ hτ hτc =>
    ha2 τ hτ _ ((summable_exp_neg_mul_sum_abs hε0).mul_left M) fun m => ?_⟩
  rcases (ha0 m).eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]; positivity
  have hT := hpsd m h0
  set t : ℝ := ((Matrix.of fun i j => m (i, j)).map (Int.cast : ℤ → ℝ)).trace with ht
  have hone : ∑ q : Fin g × Fin g, (m q : ℝ) * (1 : Matrix (Fin g) (Fin g) ℝ) q.1 q.2 = t := by
    simp [ht, Fintype.sum_prod_type, Matrix.one_apply, Matrix.trace]
  have h1 := hA 0 (by simp) m
  have e1 : ∑ q : Fin g × Fin g, (m q : ℝ) * (s • (1 : Matrix (Fin g) (Fin g) ℝ) + 0) q.1 q.2 =
      s * t := by
    rw [← hone, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [add_zero, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e1] at h1
  have h2 : c * t ≤ ∑ q : Fin g × Fin g, (m q : ℝ) * (τ q.1 q.2).im := by
    have := sum_mul_nonneg_of_posSemidef hT hτc
    rw [← hone, Finset.mul_sum, ← sub_nonneg, ← Finset.sum_sub_distrib]
    refine this.trans_eq (Finset.sum_congr rfl fun q _ => ?_)
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h3 : ∑ q : Fin g × Fin g, |(m q : ℝ)| ≤ g ^ 2 * t := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun q : Fin g × Fin g => |(m q : ℝ)|) t
      fun q _ => abs_apply_le_trace_of_posSemidef hT q.1 q.2
    simpa [sq] using this
  calc a m * Real.exp (-(π / N * ∑ q, (m q : ℝ) * (τ q.1 q.2).im))
      ≤ a m * (Real.exp (-(2 * π * (s * t))) * Real.exp (-(ε * ∑ q, |(m q : ℝ)|))) := by
        rw [← Real.exp_add]
        gcongr
        have h4 : ε * ∑ q, |(m q : ℝ)| ≤ ε * (g ^ 2 * t) := by gcongr
        have h5 : π / N * (c * t) ≤ π / N * ∑ q : Fin g × Fin g, (m q : ℝ) * (τ q.1 q.2).im := by
          gcongr
        have h6 : π / N * (c * t) = 2 * π * (s * t) + ε * (g ^ 2 * t) := by
          rw [hs, hε]; field_simp; ring
        linarith
    _ ≤ M * Real.exp (-(ε * ∑ q, |(m q : ℝ)|)) := by
        rw [← mul_assoc]
        gcongr
end GlobalTheory
