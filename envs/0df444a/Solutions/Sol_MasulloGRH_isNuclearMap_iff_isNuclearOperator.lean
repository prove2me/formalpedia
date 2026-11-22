-- Prove2me | solution 1 for MasulloGRH.isNuclearMap_iff_isNuclearOperator
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:35:37.213001+00:00
-- url     : https://prove2.me/submissions/aa30f4b1-bbd7-47e5-9856-efbdc82f157b

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear
import Definitions.Def_MasulloGRH_NuclearMap

open Filter Topology
set_option autoImplicit false

open MasulloGRH

namespace Sol_MasulloGRH_isNuclearMap_iff_isNuclearOperator

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An equicontinuous sequence of continuous linear functionals on a normed space is bounded
in operator norm. -/
lemma bound_of_equicontinuous (φ : ℕ → StrongDual ℂ H)
    (h : Equicontinuous (fun (n : ℕ) (x : H) => φ n x)) : ∃ C ≥ 0, ∀ n, ‖φ n‖ ≤ C :=
  ((NormedSpace.equicontinuous_TFAE φ).out 1 6).mp h

/-- A uniformly bounded sequence of continuous linear functionals is equicontinuous. -/
lemma equicontinuous_of_bound (φ : ℕ → StrongDual ℂ H) (C : ℝ) (h : ∀ n, ‖φ n‖ ≤ C) :
    Equicontinuous (fun (n : ℕ) (x : H) => φ n x) :=
  ((NormedSpace.equicontinuous_TFAE φ).out 1 5).mpr (⟨C, h⟩ : ∃ C, ∀ n, ‖φ n‖ ≤ C)

lemma norm_normalize_le (v : H) : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ ≤ 1 := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- From a nuclear representation to an absolutely summable rank-one expansion. -/
lemma repr_to_series {T : H →L[ℂ] H} {c : ℕ → ℂ} {φ : ℕ → StrongDual ℂ H} {y : ℕ → H}
    (h : IsNuclearRepr T c φ y) :
    ∃ x : ℕ → H, Summable (fun m => ‖x m‖ * ‖y m‖) ∧
      (∀ m u, inner ℂ (x m) u = c m * φ m u) ∧
      ∀ u : H, HasSum (fun m => inner ℂ (x m) u • y m) (T u) := by
  obtain ⟨hc, heq, ⟨B, hB, hyB⟩, hT⟩ := h
  obtain ⟨C, hC0, hC⟩ := bound_of_equicontinuous φ heq
  have hBb : Bornology.IsBounded B := (NormedSpace.isVonNBounded_iff ℂ).mp hB.2.1
  obtain ⟨R, hR⟩ := hBb.exists_norm_le
  have hy : ∀ n, ‖y n‖ ≤ R := fun n => hR _ (hyB n)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hy 0)
  let x : ℕ → H := fun m => (starRingEnd ℂ (c m)) • (InnerProductSpace.toDual ℂ H).symm (φ m)
  have hx : ∀ m u, inner ℂ (x m) u = c m * φ m u := by
    intro m u
    simp only [x, inner_smul_left, InnerProductSpace.toDual_symm_apply, RCLike.conj_conj]
  refine ⟨x, ?_, hx, ?_⟩
  · refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => ?_) (hc.mul_right (C * R))
    have h1 : ‖x m‖ = ‖c m‖ * ‖φ m‖ := by
      simp only [x, norm_smul, RCLike.norm_conj, LinearIsometryEquiv.norm_map]
    rw [h1, mul_assoc]
    gcongr
    · exact hC m
    · exact hy m
  · intro u
    simpa only [hx] using hT u

/-- The diagonal series of an absolutely summable rank-one expansion in any orthonormal basis
has sum `∑ₘ ⟨xₘ, yₘ⟩`. -/
lemma hasSum_diag_of_series {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (x y : ℕ → H)
    (hs : Summable (fun m => ‖x m‖ * ‖y m‖))
    (hxy : ∀ u : H, HasSum (fun m => inner ℂ (x m) u • y m) (T u)) :
    HasSum (fun i => inner ℂ (b i) (T (b i))) (∑' m, inner ℂ (x m) (y m)) := by
  have hdiag : ∀ i, HasSum (fun m => inner ℂ (x m) (b i) * inner ℂ (b i) (y m))
      (inner ℂ (b i) (T (b i))) := by
    intro i
    have := (hxy (b i)).mapL (innerSL ℂ (b i))
    simpa only [innerSL_apply_apply, inner_smul_right] using this
  have hbound : ∀ (s : Finset ι) (m : ℕ),
      ‖∑ i ∈ s, inner ℂ (x m) (b i) * inner ℂ (b i) (y m)‖ ≤ ‖x m‖ * ‖y m‖ := by
    intro s m
    have hle : ‖∑ i ∈ s, inner ℂ (x m) (b i) * inner ℂ (b i) (y m)‖
        ≤ ∑ i ∈ s, ‖inner ℂ (b i) (x m)‖ * ‖inner ℂ (b i) (y m)‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [norm_mul, norm_inner_symm]
    have h1 := b.orthonormal.sum_inner_products_le (x := x m) (s := s)
    have h2 := b.orthonormal.sum_inner_products_le (x := y m) (s := s)
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖inner ℂ (b i) (x m)‖)
      (fun i => ‖inner ℂ (b i) (y m)‖)
    have h4 : (∑ i ∈ s, ‖inner ℂ (b i) (x m)‖ * ‖inner ℂ (b i) (y m)‖) ^ 2
        ≤ (‖x m‖ * ‖y m‖) ^ 2 := by
      calc _ ≤ _ := h3
        _ ≤ ‖x m‖ ^ 2 * ‖y m‖ ^ 2 :=
          mul_le_mul h1 h2 (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _)
        _ = (‖x m‖ * ‖y m‖) ^ 2 := by ring
    have h5 := (pow_le_pow_iff_left₀
      (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).mp h4
    exact hle.trans h5
  have hpartial : ∀ s : Finset ι, ∑ i ∈ s, inner ℂ (b i) (T (b i)) =
      ∑' m, ∑ i ∈ s, inner ℂ (x m) (b i) * inner ℂ (b i) (y m) := by
    intro s
    exact (hasSum_sum (fun i _ => hdiag i)).tsum_eq.symm
  have hlim : Tendsto (fun s : Finset ι =>
      ∑' m, ∑ i ∈ s, inner ℂ (x m) (b i) * inner ℂ (b i) (y m))
      atTop (𝓝 (∑' m, inner ℂ (x m) (y m))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun m => ?_)
      (Eventually.of_forall (fun s m => hbound s m))
    exact b.hasSum_inner_mul_inner (x m) (y m)
  have hlim' : Tendsto (fun s : Finset ι => ∑ i ∈ s, inner ℂ (b i) (T (b i)))
      atTop (𝓝 (∑' m, inner ℂ (x m) (y m))) := by
    simpa only [hpartial] using hlim
  exact hlim'

lemma operatorTrace_eq_of_series (T : H →L[ℂ] H) (x y : ℕ → H)
    (hs : Summable (fun m => ‖x m‖ * ‖y m‖))
    (hxy : ∀ u : H, HasSum (fun m => inner ℂ (x m) u • y m) (T u)) :
    operatorTrace T = ∑' m, inner ℂ (x m) (y m) :=
  (hasSum_diag_of_series (chosenHilbertBasis H) T x y hs hxy).tsum_eq

lemma isNuclearOperator_of_isNuclearMap {T : H →L[ℂ] H} (h : IsNuclearMap T) :
    IsNuclearOperator T := by
  obtain ⟨c, φ, y, hr⟩ := h
  obtain ⟨x, hs, -, hxy⟩ := repr_to_series hr
  exact ⟨x, y, hs, hxy⟩

/-- The closed unit ball of a Hilbert space is a Banach disc. -/
lemma isBanachDisc_closedBall : IsBanachDisc (Metric.closedBall (0 : H) 1) := by
  refine ⟨⟨0, Metric.mem_closedBall_self zero_le_one⟩,
    NormedSpace.isVonNBounded_closedBall ℂ H 1, balanced_closedBall_zero,
    convex_closedBall 0 1, ?_, ?_⟩
  · intro v _ hv
    rw [gauge_closedBall zero_le_one, div_one] at hv
    exact norm_eq_zero.mp hv
  · intro u _ hu
    have hcau : CauchySeq u := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      have := hN m hm n hn
      rw [gauge_closedBall zero_le_one, div_one] at this
      rwa [dist_eq_norm]
    obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcau
    refine ⟨v, ?_, ?_⟩
    · have hmem : ((‖v‖ + 1)⁻¹ : ℂ) • v ∈ Metric.closedBall (0 : H) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
        have h1 : ‖((‖v‖ + 1 : ℝ) : ℂ)‖ = ‖v‖ + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        have h2 : ((‖v‖ : ℂ) + 1) = ((‖v‖ + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [h2, h1, inv_mul_le_one₀ (by positivity)]
        linarith
      have hv' : v = ((‖v‖ + 1 : ℂ)) • (((‖v‖ + 1)⁻¹ : ℂ) • v) := by
        rw [smul_smul, mul_inv_cancel₀, one_smul]
        intro h0
        have h3 : ((‖v‖ + 1 : ℝ) : ℂ) = 0 := by push_cast; exact h0
        have h4 : (‖v‖ + 1 : ℝ) = 0 := by exact_mod_cast h3
        have : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
        linarith
      rw [hv']
      exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
    · have := (tendsto_iff_norm_sub_tendsto_zero).mp hv
      simpa only [gauge_closedBall zero_le_one, div_one] using this

lemma isNuclearMap_of_isNuclearOperator {T : H →L[ℂ] H} (h : IsNuclearOperator T) :
    IsNuclearMap T := by
  obtain ⟨x, y, hs, hxy⟩ := h
  refine ⟨fun m => ((‖x m‖ * ‖y m‖ : ℝ) : ℂ),
    fun m => innerSL ℂ (((‖x m‖⁻¹ : ℝ) : ℂ) • x m),
    fun m => ((‖y m‖⁻¹ : ℝ) : ℂ) • y m, ?_, ?_, ?_, ?_⟩
  · refine hs.congr (fun m => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · refine equicontinuous_of_bound _ 1 (fun m => ?_)
    rw [innerSL_apply_norm]
    exact norm_normalize_le _
  · exact ⟨_, isBanachDisc_closedBall, fun m => mem_closedBall_zero_iff.mpr (norm_normalize_le _)⟩
  · intro u
    refine (hxy u).congr_fun ?_
    intro m
    simp only [innerSL_apply_apply, inner_smul_left, Complex.conj_ofReal, smul_smul]
    by_cases hx0 : x m = 0
    · simp [hx0]
    by_cases hy0 : y m = 0
    · simp [hy0]
    have hxn : (‖x m‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx0
    have hyn : (‖y m‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy0
    congr 1
    push_cast
    field_simp

end Sol_MasulloGRH_isNuclearMap_iff_isNuclearOperator

open Sol_MasulloGRH_isNuclearMap_iff_isNuclearOperator in
theorem solution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    (IsNuclearMap T ↔ IsNuclearOperator T) ∧
      ∀ (c : ℕ → ℂ) (φ : ℕ → StrongDual ℂ H) (y : ℕ → H), IsNuclearRepr T c φ y →
        Summable (fun m => ‖c m * φ m (y m)‖) ∧
        HasSum (fun m => c m * φ m (y m)) (operatorTrace T) := by
  refine ⟨⟨isNuclearOperator_of_isNuclearMap, isNuclearMap_of_isNuclearOperator⟩, ?_⟩
  intro c φ y hr
  obtain ⟨x, hs, hx, hxy⟩ := repr_to_series hr
  have hterm : ∀ m, c m * φ m (y m) = inner ℂ (x m) (y m) := fun m => (hx m (y m)).symm
  have hsum : Summable (fun m => ‖c m * φ m (y m)‖) := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hs
    rw [hterm m]
    exact norm_inner_le_norm _ _
  refine ⟨hsum, ?_⟩
  have htr : operatorTrace T = ∑' m, inner ℂ (x m) (y m) :=
    operatorTrace_eq_of_series T x y hs hxy
  rw [htr, ← tsum_congr hterm]
  exact (Summable.of_norm hsum).hasSum
