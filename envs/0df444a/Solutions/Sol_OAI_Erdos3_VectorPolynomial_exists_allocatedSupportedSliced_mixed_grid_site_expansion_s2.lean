-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_mixed_grid_site_expansion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:45:57.932663+00:00
-- url     : https://prove2.me/submissions/9922efc1-83a2-4b58-9b09-85a4a715c6d0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B196
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedSupportedSliced_grid_site_expansion_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedSupportedSliced_inactive_grid_site_expansion_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_map {α R S : Type*} [DecidableEq α] [CommRing R] [CommRing S]
    (φ : R →+* S) (f : Finset α → R) (s : Finset α) :
    φ (booleanCoefficient f s) = booleanCoefficient (fun t => φ (f t)) s := by
  simp only [booleanCoefficient, map_sum, map_mul, map_pow, map_neg, map_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_div {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (s : Finset α) (a : ℝ) :
    booleanCoefficient (fun t => f t / a) s = booleanCoefficient f s / a := by
  simp only [booleanCoefficient, ← mul_div_assoc, Finset.sum_div]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem booleanCoefficient_sub_bound {α : Type*} [DecidableEq α]
    (f g : Finset α → ℝ) (s : Finset α) {H : ℝ}
    (h : ∀ t ∈ s.powerset, |f t-g t| ≤ H) :
    |booleanCoefficient f s-booleanCoefficient g s| ≤ (2 : ℝ)^s.card*H := by
  unfold booleanCoefficient
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ s.powerset, |(-1 : ℝ)^(s\t).card*f t-(-1 : ℝ)^(s\t).card*g t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t ∈ s.powerset, |f t-g t| := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← mul_sub, abs_mul, abs_pow]
      norm_num
    _ ≤ ∑ _t ∈ s.powerset, H := Finset.sum_le_sum h
    _ = _ := by simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
namespace OAI

section

namespace Erdos3

theorem regularizationRadius_spec {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    0 < regularizationRadius L ε ∧ regularizationRadius L ε ≤ 1 ∧
      L*regularizationRadius L ε ≤ ε/2 := by
  have hp : 0 < regularizationRadius L ε := by unfold regularizationRadius; positivity
  refine ⟨hp, min_le_left _ _, ?_⟩
  have hs := (le_div_iff₀ (show 0 < 2*(1+L) by positivity)).mp
    (show regularizationRadius L ε ≤ ε/(2*(1+L)) from min_le_right _ _)
  nlinarith

theorem regularizationRadius_inverse_le_exp {L ε P : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) (hP : 0 ≤ P)
    (hLP : L ≤ Real.exp P) (hεP : ε⁻¹ ≤ Real.exp P) :
    (regularizationRadius L ε)⁻¹ ≤ Real.exp (2*P+2) := by
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 2*P+2)
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      (ε/(2*(1+L)))⁻¹ = 2*(1+L)*ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 1*Real.exp (P+1)*Real.exp P := by
        gcongr
        exact one_add_le_exp_succ hP hLP
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem intervalSiteWeight_sum {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : ℝ) (hx : |x| ≤ B) :
    ∑ i, intervalSiteWeight B r i x = 1 := by
  apply regularizedTentPartition_sum _ hr
  obtain ⟨i, hi⟩ := exists_uniformIntervalGrid_approx hB (boxCoverMeshCount_pos B 1 r) x hx
  refine ⟨i, ?_⟩
  have he := boxCoverMeshCount_error (1 : ℝ≥0) hr (B := B)
  simp only [NNReal.coe_one, one_mul] at he
  exact (show dist x (intervalSiteCenter B r i) ≤ 2 * B / boxCoverMeshCount B 1 r from hi).trans he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerRowInterpolationMixture
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {O : Type*} [Fintype O]

theorem integerRowMassTent_range {K : ℝ} (hK : 0 ≤ K) (z : O → ℤ) (x : O → ℝ) :
    0 ≤ integerRowMassTent K z x ∧ integerRowMassTent K z x ≤ K ^ Fintype.card O := by
  refine ⟨Finset.prod_nonneg (fun i _ => (integerMassTent_range K hK (z i) (x i)).1), ?_⟩
  simpa only [integerRowMassTent, Finset.prod_const, Finset.card_univ] using
    Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).1)
      (fun i _ => (integerMassTent_range K hK (z i) (x i)).2)

theorem integerRowMassTent_grid {K : ℝ} (hK : 0 < K) (z k : O → ℤ) :
    integerRowMassTent K z (fun i => (k i : ℝ) / K) =
      if z = k then K ^ Fintype.card O else 0 := by
  classical
  by_cases he : z = k
  · subst z
    simp [integerRowMassTent, integerMassTent_grid K hK]
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ k i := Function.ne_iff.mp he
    have hz : integerMassTent K (z i) ((k i : ℝ) / K) = 0 := by
      rw [integerMassTent_grid K hK]
      simp [Ne.symm hi]
    simp only [he, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem integerRowMassTent_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (z : O → ℤ) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassTent (K : ℝ) z) := by
  have hf (i : O) : LipschitzWith (2 * K ^ 2) (fun x : O → ℝ => integerMassTent K (z i) (x i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ ≤ (2 * (K : ℝ) ^ 2) * |x i - y i| := integerMassTent_difference K K.coe_nonneg (z i) (x i) (y i)
      _ ≤ _ := by
        simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_pow, Real.dist_eq] using
          mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (by positivity : 0 ≤ 2 * (K : ℝ) ^ 2)
  exact (bounded_lipschitz_real_prod _ hK hf (fun i x => by
    rw [abs_of_nonneg (integerMassTent_range K K.coe_nonneg (z i) (x i)).1]
    exact (integerMassTent_range K K.coe_nonneg (z i) (x i)).2)).2

theorem integerRowMassTent_integrable {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    Integrable (fun z => integerRowMassTent K z x) p.toMeasure := by
  apply (integrable_const (K ^ Fintype.card O)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integerRowMassTent_range hK z x).1]
    exact (integerRowMassTent_range hK z x).2)

theorem integerRowMassInterpolation_range {K : ℝ} (hK : 0 ≤ K) (p : PMF (O → ℤ)) (x : O → ℝ) :
    0 ≤ integerRowMassInterpolation K p x ∧ integerRowMassInterpolation K p x ≤ K ^ Fintype.card O := by
  refine ⟨integral_nonneg (fun z => (integerRowMassTent_range hK z x).1), ?_⟩
  have h := integral_mono (integerRowMassTent_integrable hK p x) (integrable_const (K ^ Fintype.card O))
    (fun z => (integerRowMassTent_range hK z x).2)
  simpa only [integerRowMassInterpolation, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul] using h

theorem integerRowMassInterpolation_grid {K : ℝ} (hK : 0 < K) (p : PMF (O → ℤ)) (k : O → ℤ) :
    integerRowMassInterpolation K p (fun i => (k i : ℝ) / K) =
      K ^ Fintype.card O * (p k).toReal := by
  classical
  have he : (fun z => integerRowMassTent K z (fun i => (k i : ℝ) / K)) =
      Set.indicator {k} (fun _ => K ^ Fintype.card O) := by
    funext z
    simp only [integerRowMassTent_grid hK, Set.indicator_apply, Set.mem_singleton_iff]
  rw [integerRowMassInterpolation, he, integral_indicator (measurableSet_singleton k), integral_singleton,
    measureReal_def, PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k), smul_eq_mul, mul_comm]

theorem integerRowMassInterpolation_lipschitz (K : ℝ≥0) (hK : 1 ≤ K) (p : PMF (O → ℤ)) :
    LipschitzWith (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O)
      (integerRowMassInterpolation (K : ℝ) p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖integerRowMassInterpolation (K : ℝ) p x - integerRowMassInterpolation (K : ℝ) p y‖ ≤ _
  rw [integerRowMassInterpolation, integerRowMassInterpolation,
    ← integral_sub (integerRowMassTent_integrable K.coe_nonneg p x) (integerRowMassTent_integrable K.coe_nonneg p y)]
  have h := norm_integral_le_of_norm_le_const (μ := p.toMeasure)
    (f := fun z => integerRowMassTent (K : ℝ) z x - integerRowMassTent (K : ℝ) z y)
    (C := (Fintype.card O * (2 * K ^ 2) * K ^ Fintype.card O : ℝ≥0) * dist x y)
    (Filter.Eventually.of_forall (fun z => by
      simpa only [dist_eq_norm] using (integerRowMassTent_lipschitz K hK z).dist_le_mul x y))
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveAxisScale
namespace OAI

section

namespace Erdos3

theorem inactiveSideLength_lower_power {h K q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (hlarge : 2 * q ≤ K) : K < q * 2 ^ h * inactiveSideLength h K q ^ h := by
  have hpos := inactiveSideLength_pos (K := K) hh hq
  have hnext : K / q < (inactiveSideLength h K q + 1) ^ h := by
    simpa [inactiveSideLength, hlarge] using Nat.lt_pow_nthRoot_add_one hh.ne' (K / q)
  have hdiv : K < q * (K / q + 1) := by
    have hm := Nat.mod_lt K hq
    have he := Nat.mod_add_div K q
    nlinarith
  calc
    K < q * (K / q + 1) := hdiv
    _ ≤ q * (inactiveSideLength h K q + 1) ^ h :=
      Nat.mul_le_mul_left q (Nat.succ_le_of_lt hnext)
    _ ≤ q * (2 * inactiveSideLength h K q) ^ h := by gcongr; omega
    _ = _ := by rw [mul_pow]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedSupportPlateau
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {J : Type*} [Fintype J]

theorem normalizedSupportPlateau_range (H : ℝ) (x : J → ℝ) :
    0 ≤ normalizedSupportPlateau H x ∧ normalizedSupportPlateau H x ≤ 1 :=
  linearCutoff_range _ _ _

theorem normalizedSupportPlateau_one {H : ℝ} (hH : 0 ≤ H) (x : J → ℝ)
    (hx : ∀ j, |x j| ≤ H) : normalizedSupportPlateau H x = 1 := by
  apply linearCutoff_eq_one _ _ (by norm_num)
  exact (pi_norm_le_iff_of_nonneg hH).mpr (by simpa only [Real.norm_eq_abs] using hx)

theorem normalizedSupportPlateau_support {H : ℝ} (x : J → ℝ)
    (hx : normalizedSupportPlateau H x ≠ 0) : ∀ j, |x j| < H + 1 / 4 := by
  have hn : ‖x‖ < H + 1 / 4 := by
    apply lt_of_not_ge
    intro h
    apply hx
    exact linearCutoff_eq_zero H (1 / 4) (by simpa using h)
  intro j
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  exact hj.trans_lt hn

theorem normalizedSupportPlateau_lipschitz (H : ℝ) :
    LipschitzWith 4 (normalizedSupportPlateau (J := J) H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (linearCutoff_lipschitz H (1 / 4) (by norm_num)).dist_le_mul ‖x‖ ‖y‖
  norm_num only [NNReal.coe_inv, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    one_div, inv_inv] at h
  exact h.trans (mul_le_mul_of_nonneg_left (dist_norm_norm_le x y) (by norm_num))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerSupportTorus
namespace OAI

section

namespace Erdos3

theorem integerSupportTorusFactor_pos (H : ℝ) : 0 < integerSupportTorusFactor H := by
  unfold integerSupportTorusFactor
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedBlockTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem blockTorusFactor_pos (q h b : ℕ) (A : ℝ) : 0 < blockTorusFactor q h b A :=
  integerSupportTorusFactor_pos _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedCubePlateau
namespace OAI

section

namespace Erdos3

open scoped BigOperators

instance blockTorusFactor_neZero (q h b : ℕ) (A : ℝ) : NeZero (blockTorusFactor q h b A) :=
  ⟨(blockTorusFactor_pos q h b A).ne'⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeBoundedVariablePatchExpansion
namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

theorem intervalTensorWeight_nonneg {S : Type*} [Fintype S] (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) : 0 ≤ intervalTensorWeight B r k x :=
  Finset.prod_nonneg (fun i _ => (intervalSiteWeight_range B hr (k i) (x i)).1)

theorem intervalTensorWeight_sum {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ∑ k : S → Fin (intervalSiteCount B r), intervalTensorWeight B r k x = 1 := by
  unfold intervalTensorWeight
  rw [← Fintype.prod_sum (fun i k => intervalSiteWeight B r k (x i))]
  simp only [intervalSiteWeight_sum hB hr _ (hx _), Finset.prod_const_one]

theorem intervalTensorWeight_near {S : Type*} [Fintype S] {B r : ℝ} (hr : 0 < r)
    (k : S → Fin (intervalSiteCount B r)) (x : S → ℝ) (hx : 0 < intervalTensorWeight B r k x) :
    dist x (fun i => intervalSiteCenter B r (k i)) ≤ 2 * r := by
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have hp := productPartitionWeight_pos_coordinate (fun _ : S => intervalSiteWeight B r)
    (fun _ j x => (intervalSiteWeight_range B hr j x).1) k x hx i
  exact (intervalSiteWeight_near B r (k i) (x i) hp).le

theorem intervalTensorApprox_error {S : Type*} [Fintype S] [DecidableEq S]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → ℝ) → ℂ) {K : ℝ≥0}
    (hF : LipschitzWith K F) (x : S → ℝ) (hx : ∀ i, |x i| ≤ B) :
    ‖F x - intervalTensorApprox B r F x‖ ≤ 2 * K * r := by
  apply norm_sub_positive_sum_le (fun k => intervalTensorWeight B r k x)
    (fun k => F (fun i => intervalSiteCenter B r (k i))) (F x) _
    (fun k => intervalTensorWeight_nonneg B hr k x) (intervalTensorWeight_sum hB hr x hx)
  intro k hk
  have h := hF.dist_le_mul x (fun i => intervalSiteCenter B r (k i))
  rw [dist_eq_norm] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (intervalTensorWeight_near hr k x hk) K.coe_nonneg).trans_eq (by ring))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GroupedSiteTensor
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {S D : Type*} [Fintype S] [Fintype D]

theorem siteCurry_lipschitz :
    LipschitzWith 1 (fun x : S × D → ℝ => fun s d => x (s, d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro s
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro d
  exact dist_le_pi_dist x y (s, d)

theorem groupedSiteApprox_eq_interval [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ) (x : S → D → ℝ) :
    groupedSiteApprox B r F x =
      intervalTensorApprox B r (fun y : S × D → ℝ => F (fun s d => y (s, d)))
        (fun p => x p.1 p.2) := by
  unfold groupedSiteApprox intervalTensorApprox groupedSiteCoefficient
  apply Finset.sum_congr rfl
  intro k _
  simp only [groupedSiteFactor, vectorIntervalSiteWeight, intervalTensorWeight,
    Complex.ofReal_prod, Fintype.prod_prod_type]
  ring

theorem groupedSiteApprox_error [DecidableEq S] [DecidableEq D]
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r) (F : (S → D → ℝ) → ℂ)
    {K : ℝ≥0} (hF : LipschitzWith K F) (x : S → D → ℝ)
    (hx : ∀ s d, |x s d| ≤ B) :
    ‖F x-groupedSiteApprox B r F x‖ ≤ 2*K*r := by
  rw [groupedSiteApprox_eq_interval]
  exact intervalTensorApprox_error hB hr _
    (by simpa only [mul_one] using hF.comp (siteCurry_lipschitz (S := S) (D := D)))
    (fun p : S × D => x p.1 p.2) (fun p : S × D => hx p.1 p.2)

theorem groupedSiteCoefficient_sum [DecidableEq S] [DecidableEq D]
    (B r : ℝ) (F : (S → D → ℝ) → ℂ)
    {A : ℝ} (hF : ∀ x, ‖F x‖ ≤ A) :
    (∑ k : S × D → Fin (intervalSiteCount B r), ‖groupedSiteCoefficient B r F k‖) ≤
      (intervalSiteCount B r : ℝ)^(Fintype.card S*Fintype.card D)*A := by
  calc
    _ ≤ ∑ _k : S × D → Fin (intervalSiteCount B r), A := Finset.sum_le_sum (fun k _ => hF _)
    _ = _ := by simp [Fintype.card_prod]

omit [Fintype S] in
theorem groupedSiteFactor_bound (B : ℝ) {r : ℝ} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) (x : D → ℝ) :
    ‖groupedSiteFactor B r k s x‖ ≤ 1 :=
  vectorIntervalSiteWeight_bound B hr _ _

omit [Fintype S] in
theorem groupedSiteFactor_lipschitz (B : ℝ) {r : ℝ≥0} (hr : 0 < r)
    (k : S × D → Fin (intervalSiteCount B r)) (s : S) :
    LipschitzWith (Fintype.card D*((2*intervalSiteCount B r+1)/r))
      (groupedSiteFactor B r k s) :=
  vectorIntervalSiteWeight_lipschitz B hr _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.VectorSiteBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem exists_grouped_site_approximation {S D : Type*} [Fintype S] [Fintype D]
    [DecidableEq S] [DecidableEq D]
    (F : (S → D → ℝ) → ℂ) (A K : ℝ≥0) (hA : ∀ x, ‖F x‖ ≤ A)
    (hK : LipschitzWith K F) {B ε P : ℝ} (hB : 0 < B) (hε : 0 < ε) (hP : 0 ≤ P)
    (hBP : B ≤ Real.exp P) (hAP : (A : ℝ) ≤ Real.exp P) (hKP : (K : ℝ) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4*P+8) ∧
      ∃ (c : (S × D → Fin n) → ℂ) (f : (S × D → Fin n) → S → (D → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp ((Fintype.card S*Fintype.card D : ℕ)*(4*P+8)+P) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (Fintype.card D+6*P+12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : S → D → ℝ, (∀ s d, |x s d| ≤ B) →
          ‖F x-∑ k, c k*∏ s, f k s (x s)‖ ≤ ε := by
  let r := regularizationRadius K ε
  have hs := regularizationRadius_spec K.coe_nonneg hε
  have hr : 0 < r := hs.1
  have hi : r⁻¹ ≤ Real.exp (2*P+2) :=
    regularizationRadius_inverse_le_exp K.coe_nonneg hε hP hKP hεP
  have hP' : 0 ≤ 2*P+2 := by positivity
  have hPP' : P ≤ 2*P+2 := by linarith
  have hB' : B ≤ Real.exp (2*P+2) := hBP.trans (Real.exp_le_exp.mpr hPP')
  have hn : (intervalSiteCount B r : ℝ) ≤ Real.exp (4*P+8) := by
    have hb := intervalSiteCount_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have he : 2*(2*P+2)+4 = 4*P+8 := by ring
    simpa only [he] using hb
  have hf : (Fintype.card D : ℝ)*((2*(intervalSiteCount B r : ℝ)+1)/r) ≤
      Real.exp (Fintype.card D+6*P+12) := by
    have hb := intervalSiteLipschitz_le_exp hB.le hr hP' hB' (by simpa only [one_div] using hi)
    have hd : (Fintype.card D : ℝ) ≤ Real.exp (Fintype.card D : ℝ) := by
      linarith [Real.add_one_le_exp (Fintype.card D : ℝ)]
    calc
      _ ≤ Real.exp (Fintype.card D : ℝ)*Real.exp (3*(2*P+2)+6) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨intervalSiteCount B r, hn, groupedSiteCoefficient B r F, groupedSiteFactor B r, ?_,
    (fun k s x => groupedSiteFactor_bound B hr k s x), ?_, ?_⟩
  · apply (groupedSiteCoefficient_sum B r F hA).trans
    calc
      _ ≤ (Real.exp (4*P+8))^(Fintype.card S*Fintype.card D)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]
  · intro k s
    have hl := groupedSiteFactor_lipschitz B (r := ⟨r, hr.le⟩) hr k s
    apply hl.weaken
    exact_mod_cast hf
  · intro x hx
    apply (groupedSiteApprox_error hB hr F hK x hx).trans
    have hs' : (K : ℝ)*r ≤ ε/2 := hs.2.2
    nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SitePlateauCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem scalarSupportPlateau_norm (H x : ℝ) : ‖scalarSupportPlateau H x‖ ≤ 1 := by
  rw [scalarSupportPlateau, Complex.norm_real,
    Real.norm_of_nonneg (normalizedSupportPlateau_range H _).1]
  exact (normalizedSupportPlateau_range H _).2

theorem scalarSupportPlateau_one {H : ℝ} (hH : 0 ≤ H) {x : ℝ} (hx : |x| ≤ H) :
    scalarSupportPlateau H x = 1 := by
  simp only [scalarSupportPlateau, normalizedSupportPlateau_one hH _ (fun _ => hx), Complex.ofReal_one]

theorem scalarSupportPlateau_support (H x : ℝ) (hx : scalarSupportPlateau H x ≠ 0) :
    |x| < H + 1 / 4 := by
  apply normalizedSupportPlateau_support (fun _ : Unit => x) _ ()
  intro hz
  exact hx (by simp only [scalarSupportPlateau, hz, Complex.ofReal_zero])

theorem scalarSupportPlateau_zero {H x : ℝ} (hx : H + 1 / 4 ≤ |x|) :
    scalarSupportPlateau H x = 0 := by
  by_contra hn
  exact (not_lt_of_ge hx) (scalarSupportPlateau_support H x hn)

theorem scalarSupportPlateau_lipschitz (H : ℝ) : LipschitzWith 4 (scalarSupportPlateau H) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (normalizedSupportPlateau_lipschitz (J := Unit) H).dist_le_mul
    (fun _ => x) (fun _ => y)
  rw [dist_pi_const] at h
  simpa only [scalarSupportPlateau, dist_eq_norm,
    ← Complex.ofReal_sub, Complex.norm_real] using h

theorem scalarSupportPlateau_mul_lipschitz (H : ℝ) (f : ℝ → ℂ) {L : ℝ≥0}
    (hL : LipschitzWith L f) (hf : ∀ x, ‖f x‖ ≤ 1) :
    LipschitzWith (L + 4) (fun x => scalarSupportPlateau H x * f x) := by
  simpa only [one_mul] using lipschitz_mul_of_bounds (scalarSupportPlateau H) f
    (scalarSupportPlateau_lipschitz H) hL (Bf := 1) (Bg := 1)
    (scalarSupportPlateau_norm H) hf

theorem finite_site_cutoff_error {T S : Type*} [Fintype T] [Fintype S]
    (target : ℂ) (c : T → ℂ) (f : T → S → ℂ) (χ : S → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (hkeep : target ≠ 0 → ∀ s, χ s = 1)
    (he : (∀ s, χ s ≠ 0) → ‖target - ∑ k, c k * ∏ s, f k s‖ ≤ ε) :
    ‖target - ∑ k, c k * ∏ s, χ s * f k s‖ ≤ ε := by
  have hid : (∑ k, c k * ∏ s, χ s * f k s) =
      (∏ s, χ s) * ∑ k, c k * ∏ s, f k s := by
    simp only [Finset.prod_mul_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have ht : (∏ s, χ s) * target = target := by
    by_cases hz : target = 0
    · simp only [hz, mul_zero]
    · simp only [hkeep hz, Finset.prod_const_one, one_mul]
  rw [hid, ← ht, ← mul_sub, norm_mul]
  by_cases hz : ∃ s, χ s = 0
  · obtain ⟨s, hs⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ s) hs, norm_zero, zero_mul]
    exact hε
  · have hp : ‖∏ s, χ s‖ ≤ 1 := by
      rw [norm_prod]
      exact (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun s _ => hχ s)).trans_eq
        (Finset.prod_const_one)
    exact (mul_le_mul hp (he (fun s hs => hz ⟨s, hs⟩)) (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerBooleanSiteReconstruction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem integer_boolean_reconstruction (y : Finset α → ℤ) (s : Finset α) :
    y s = ∑ t : Finset α, if t ⊆ s then booleanCoefficient y t else 0 := by
  have h := congrArg (fun M : Matrix (Finset α) (Finset α) ℤ => M *ᵥ y)
    (booleanReconstruction_mul_extraction (α := α))
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at h
  have hv : booleanJetExtractionMatrix (id : Finset α → Finset α) *ᵥ y =
      fun t => booleanCoefficient y t := by
    funext t
    exact booleanJetExtractionMatrix_mulVec id y t
  rw [hv] at h
  have hs := congrFun h s
  simpa only [Matrix.mulVec, dotProduct, booleanReconstructionMatrix,
    ite_mul, one_mul, zero_mul] using hs.symm

theorem integer_boolean_reconstruction_rows (y : Finset α → ℤ)
    (rows : Finset (Finset α)) (hrows : ∀ t ∉ rows, booleanCoefficient y t = 0)
    (s : Finset α) :
    y s = ∑ t ∈ rows, if t ⊆ s then booleanCoefficient y t else 0 := by
  rw [integer_boolean_reconstruction y s]
  symm
  apply Finset.sum_subset (Finset.subset_univ rows)
  intro t _ ht
  simp only [hrows t ht, ite_self]

theorem integer_boolean_sites_bound (y : Finset α → ℤ) (rows : Finset (Finset α))
    (hrows : ∀ t ∉ rows, booleanCoefficient y t = 0)
    {H N : ℝ} (hH : 0 ≤ H) (hN : 0 < N)
    (hcoeff : ∀ t ∈ rows, |((booleanCoefficient y t : ℤ) : ℝ)| ≤ H * N) (s : Finset α) :
    |(y s : ℝ) / N| ≤ rows.card * H := by
  have hs : |(y s : ℝ)| ≤ (rows.card : ℝ) * (H * N) := by
    rw [integer_boolean_reconstruction_rows y rows hrows s, Int.cast_sum]
    calc
      _ ≤ ∑ t ∈ rows, |((if t ⊆ s then booleanCoefficient y t else 0 : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ rows, H * N := by
        apply Finset.sum_le_sum
        intro t ht
        split_ifs
        · exact hcoeff t ht
        · simp only [Int.cast_zero, abs_zero]
          positivity
      _ = _ := by simp
  rw [abs_div, abs_of_pos hN]
  apply (div_le_iff₀ hN).mpr
  simpa only [mul_assoc] using hs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3.ScalarSiteExpansion

open scoped NNReal

universe u v

variable {S : Type u} {e : ScalarSiteExpansion.{u,v} S}

theorem Bounds.mono {T D C H T' D' C' H' : ℝ} {L L' : ℝ≥0}
    (h : e.Bounds T D C L H) (hT : T ≤ T') (hD : D ≤ D') (hC : C ≤ C')
    (hL : L ≤ L') (hH : H ≤ H') : e.Bounds T' D' C' L' H' :=
  ⟨h.card_le.trans hT, h.period_pos, fun i => (h.period_le i).trans hD,
    h.coefficient_le.trans hC, h.factor_bound, fun i s r => (h.lipschitz i s r).weaken hL,
    fun i s r x hx => h.support i s r x (hH.trans hx)⟩

end Erdos3.ScalarSiteExpansion

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

variable {α A T : Type*} [Fintype α] [DecidableEq α] [Fintype A] [DecidableEq A]

omit [DecidableEq A] in
theorem selectedBooleanSiteRows_lipschitz (axis : A) (rows : Finset (Finset α)) :
    LipschitzWith ((2 : ℝ≥0) ^ Fintype.card α) (selectedBooleanSiteRows axis rows) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (by positivity)).mpr
  intro t
  change |booleanCoefficient (fun s => x s axis) t - booleanCoefficient (fun s => y s axis) t| ≤ _
  apply (booleanCoefficient_sub_bound _ _ _ (H := dist x y) ?_).trans
  · simp only [NNReal.coe_pow, NNReal.coe_ofNat]
    gcongr
    · norm_num
    · exact Finset.card_le_univ _
  · intro s _
    exact (show |x s axis - y s axis| ≤ dist (x s) (y s) from
      dist_le_pi_dist (x s) (y s) axis).trans (dist_le_pi_dist x y s)

omit [Fintype α] [Fintype A] [DecidableEq A] in
theorem selectedBooleanSiteRows_integer (axis : A) (rows : Finset (Finset α))
    (N : A → ℕ) (y : Finset α → A → ℤ) :
    selectedBooleanSiteRows axis rows (fun s d => (y s d : ℝ) / N d) =
      fun t : rows => ((booleanCoefficient (fun s => y s axis) t : ℤ) : ℝ) / N axis := by
  funext t
  rw [selectedBooleanSiteRows, booleanCoefficient_div]
  congr 1
  exact (booleanCoefficient_map (Int.castRingHom ℝ) (fun s => y s axis) t).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveFixedSupport
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

universe uα

theorem exists_bounded_grid_site_expansion
    {α : Type uα} [Fintype α] [DecidableEq α]
    (rows : Finset (Finset α)) (p : PMF (rows → ℤ)) {K Kmax : ℕ}
    (hK : 0 < K) (hKmax : K ≤ Kmax) {H ε P : ℝ} (hH : 0 ≤ H)
    (hsupport : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / K| ≤ H)
    (hε : 0 < ε) (hP : 0 ≤ P) (hHP : H + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (H + 1 / 4) ∧
      ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((K : ℝ) ^ rows.card * (p (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
          e.integerEval K y‖ ≤ ε := by
  let F (x : Finset α → Unit → ℝ) : ℂ :=
    integerRowMassInterpolation K p (selectedBooleanSiteRows () rows x)
  have hKreal : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hKnn : (1 : ℝ≥0) ≤ K := by exact_mod_cast hK
  have hmax : (K : ℝ≥0) ≤ Kmax := by exact_mod_cast hKmax
  have hF (x) : ‖F x‖ ≤ (Kmax : ℝ≥0) ^ rows.card := by
    dsimp only [F]
    rw [Complex.norm_real, Real.norm_of_nonneg (integerRowMassInterpolation_range hKreal.le p _).1]
    apply (integerRowMassInterpolation_range hKreal.le p _).2.trans
    simpa only [Fintype.card_coe, NNReal.coe_pow, NNReal.coe_natCast] using
      pow_le_pow_left₀ hKreal.le (show (K : ℝ) ≤ Kmax by exact_mod_cast hKmax) rows.card
  have hLF : LipschitzWith
      ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
        (2 : ℝ≥0) ^ Fintype.card α) F := by
    have h := (integerRowMassInterpolation_lipschitz (K : ℝ≥0) hKnn p).comp
      (selectedBooleanSiteRows_lipschitz () rows)
    have hc : LipschitzWith
        ((rows.card * (2 * (K : ℝ≥0) ^ 2) * (K : ℝ≥0) ^ rows.card) *
          (2 : ℝ≥0) ^ Fintype.card α) F := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [F, Function.comp_def, Fintype.card_coe, dist_eq_norm,
        ← Complex.ofReal_sub, Complex.norm_real, NNReal.coe_natCast] using h.dist_le_mul x y
    apply hc.weaken
    gcongr
  obtain ⟨N, hN, c, f, hc, hf, hLf, he⟩ := exists_grouped_site_approximation F
    ((Kmax : ℝ≥0) ^ rows.card) _ hF hLF
    (show 0 < H + 1 / 4 by linarith only [hH]) hε hP hHP
    (by simpa only [NNReal.coe_pow, NNReal.coe_natCast] using hcap) hLip hεP
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := Finset α × Unit → Fin N
      period := fun _ => 1
      coefficient := c
      factor := fun k u _ x => scalarSupportPlateau H x * f k u (fun _ => x) }
  refine ⟨e, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · change (Fintype.card (Finset α × Unit → Fin N) : ℝ) ≤ _
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_unit,
      mul_one, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hN _).trans_eq (Real.exp_nat_mul _ _).symm
  · exact fun _ => zero_lt_one
  · intro k
    norm_num only [e, Nat.cast_one]
  · simpa only [Fintype.card_unit, mul_one] using hc
  · intro k u r x
    change ‖scalarSupportPlateau H x * f k u (fun _ => x)‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u r
    apply scalarSupportPlateau_mul_lipschitz H (fun x => f k u (fun _ => x)) _ (fun x => hf k u _)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Fintype.card_unit, Nat.cast_one, dist_pi_const] using
      (hLf k u).dist_le_mul (fun _ => x) (fun _ => y)
  · intro k u r x hx
    change scalarSupportPlateau H x * f k u (fun _ => x) = 0
    rw [scalarSupportPlateau_zero hx, zero_mul]
  · intro y hy
    let target : ℂ := (((K : ℝ) ^ rows.card * (p (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ)
    have hkeep : target ≠ 0 → ∀ u, scalarSupportPlateau H ((y u : ℝ) / K) = 1 := by
      intro ht u
      have hp : p (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply ht
        simp only [target, hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      exact scalarSupportPlateau_one hH (hsupport y hy hp u)
    apply finite_site_cutoff_error target c (fun k u => f k u (fun _ => (y u : ℝ) / K))
      (fun u => scalarSupportPlateau H ((y u : ℝ) / K)) hε.le
      (fun u => scalarSupportPlateau_norm _ _) hkeep
    intro hcut
    have herr := he (fun u _ => (y u : ℝ) / K)
      (fun u _ => (scalarSupportPlateau_support _ _ (hcut u)).le)
    have heq : F (fun u _ => (y u : ℝ) / K) = target := by
      dsimp only [F, target]
      rw [show selectedBooleanSiteRows () rows (fun u _ => (y u : ℝ) / K) =
        (fun t : rows => ((booleanCoefficient y t : ℤ) : ℝ) / K) by
          simpa only using selectedBooleanSiteRows_integer () rows (fun _ => K) (fun u _ => y u)]
      rw [integerRowMassInterpolation_grid hKreal, Fintype.card_coe]
    rwa [heq] at herr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom

theorem allocatedPrincipalSides_inactive
    (hsmall : height ≤ S.value ^ degree) (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) :
    allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ = side := by
  rw [layerIntegerPrincipalSlots_card]
  change integerAxisSideLength degree height S.value
    (principalProfileSize (R j) (Fintype.card (B ⟨j,Sum.inr i⟩))) = _
  simp only [integerAxisSideLength, Nat.not_lt.mpr hsmall, ite_false]

theorem allocatedSlicedGrid_cases
    (H : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (Q T : ℕ) (hQT : (Q : ℝ) / δ ≤ T) :
    height ≤ allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T ∨
      ((∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩) ∧
        ((S.value ^ degree < height ∧ ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) ∨
         (height ≤ S.value ^ degree ∧ 2 * denom ≤ height ∧
           ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)))) := by
  let K := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
  by_cases hK : height ≤ K
  · exact Or.inl hK
  have hlarge : 2 * denom ≤ height := by
    have : 2 * denom ≤ K := by dsimp [K, allocatedSlicedGridHeightCutoff]; omega
    omega
  have hside_bound {L h : ℕ} (hd : δ * L ≤ (h : ℝ)) (hh : h < Q) : L ≤ T := by
    have hl : (L : ℝ) ≤ (Q : ℝ) / δ := by
      apply (le_div_iff₀ hδ).mpr
      have hh' : (h : ℝ) ≤ Q := Nat.cast_le.mpr hh.le
      simpa only [mul_comm] using hd.trans hh'
    exact_mod_cast hl.trans hQT
  have hsize : ∀ b v, Q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩ := by
    intro b v
    by_contra hh
    have hL := hside_bound (hdense b v) (Nat.lt_of_not_ge hh)
    apply hK
    by_cases ha : S.value ^ degree < height
    · rw [allocatedPrincipalSides_active B U basis S j i ha b v] at hL
      have hb := hgrid.trans (Nat.pow_le_pow_left hL (layerTailDegree m + 1))
      exact hb.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
    · rw [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] at hL
      have hb := (inactiveSideLength_lower_power (Nat.zero_lt_succ j.val) (inactiveDenominator_pos _) hlarge).le
      have hc := hb.trans (Nat.mul_le_mul_left (denom * 2 ^ degree) (Nat.pow_le_pow_left hL degree))
      exact hc.trans (by dsimp [K, allocatedSlicedGridHeightCutoff]; omega)
  refine Or.inr ⟨hsize, ?_⟩
  by_cases ha : S.value ^ degree < height
  · refine Or.inl ⟨ha, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_active B U basis S j i ha b v] using hdense b v
  · refine Or.inr ⟨Nat.le_of_not_gt ha, hlarge, ?_⟩
    intro b v
    simpa only [allocatedPrincipalSides_inactive B U basis S j i (Nat.le_of_not_gt ha) b v] using hdense b v

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedInactiveGridSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j

theorem allocatedSupportedSlicedPhysicalGridPMF_base_independent
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) (x x' : G → IntegerScalarCubeBox α S.value) :
    allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x =
      allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x' := by
  unfold allocatedSupportedSlicedPhysicalGridPMF
  rw [allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2 B U basis hR hσ S q r H step c hH hsubset hcell j i hgrid rows x,
    allocatedSupportedSlicedResidueJetPMF_constant_mixture_s2 B U basis hR hσ S q r H step c hH hsubset hcell j i hgrid rows x']

theorem exists_allocatedSupportedSliced_bounded_grid_site_expansion
    (hσ1 : σ j ≤ 1) (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    (rows : Finset (Finset α)) {Kmax : ℕ} (hKmax : height ≤ Kmax)
    {ε P : ℝ} (hε : 0 < ε) (hP : 0 ≤ P)
    (hHP : rows.card * radius + 1 / 4 ≤ Real.exp P)
    (hcap : (Kmax : ℝ) ^ rows.card ≤ Real.exp P)
    (hLip : ((rows.card * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P)
    (hεP : ε⁻¹ ≤ Real.exp P) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp (Fintype.card (Finset α) * (4 * P + 8))) 1
        (Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P))
        (⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ + 4) (rows.card * radius + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε := by
  let x₀ : G → IntegerScalarCubeBox α S.value := fun _ _ =>
    ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  let p := allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x₀
  have hrad : 0 ≤ radius := by
    have := (hR j).le
    positivity
  have hk : (0 : ℝ) < height := Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
  have hs : ∀ y : Finset α → ℤ, (∀ t ∉ rows, booleanCoefficient y t = 0) →
      p (fun t => booleanCoefficient y t) ≠ 0 → ∀ u, |(y u : ℝ) / height| ≤ rows.card * radius := by
    intro y hy hm u
    apply integer_boolean_sites_bound y rows hy hrad hk _ u
    intro t ht
    have hb := allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2 B U basis hR hσ S q r H step c hH hsubset hcell j i hσ1 rows x₀
      (fun t => booleanCoefficient y t) hm ⟨t, ht⟩
    rw [abs_div, abs_of_pos hk] at hb
    exact (div_le_iff₀ hk).mp hb
  obtain ⟨e, he, herr⟩ := exists_bounded_grid_site_expansion rows p
    (basisAxisScale_pos (basis j) i) hKmax (mul_nonneg (Nat.cast_nonneg _) hrad)
    hs hε hP hHP hcap hLip hεP
  refine ⟨e, he, ?_⟩
  intro x y hy
  rw [allocatedSupportedSlicedPhysicalGridPMF_base_independent B U basis hR hσ S q r H step c hH hsubset hcell j i hgrid rows x x₀]
  exact herr y hy

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedFullGridSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem exists_allocatedSupportedSliced_mixed_grid_site_expansion_s2_oai
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let d := rows.card
    let ta := (layerTailDegree m + 1) * d
    let ti := degree * d
    let Va := ((torusA : ℝ) / (2 * gamma)) / δ ^ degree
    let Vi := (torusI : ℝ) * cost / δ ^ degree
    let Wa := (torusA : ℝ) ^ d / δ ^ ta
    let Wi := ((torusI : ℝ) * cost) ^ d / δ ^ ti
    let ζa := positiveModerateRetainedBias j.val d ta P Va Wa ε
    let ζi := uniformBlockRetainedBias j.val d ti P Vi Wi ε
    let fa := Real.toNNReal (positiveRetainedFrequencyBound j.val d P Va ζa)
    let fi := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val d P Vi ζi)
    let ca := positiveModerateSpectrumCardBudget j.val d ta P Va Wa 1 + 1
    let ci := uniformSpectrumAbsoluteCap j.val d ti P Vi Wi
    let Kmax := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
    let R0 := (d : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j)
    ∀ {Q : ℝ}, 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (ε / (ca + 1))⁻¹ ≤ Real.exp Q → (ε / (ci + 1))⁻¹ ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (d * fa) + 4) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (d * fi) + 4) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      (Kmax : ℝ) ^ d ≤ Real.exp Q →
      ((d * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ d) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      ε⁻¹ ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (max 1 (max (positiveModerateSpectrumCardBudget j.val d ta P Va Wa ε)
          (uniformSpectrumSizeConstant j.val d ti P Vi Wi /
            ε ^ max (majorArcSpectrumExponent j.val d) (majorArcLengthExponent j.val * ti))) *
          Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (max 1 (max (positiveRetainedDenominatorBound j.val d ta P Va Wa ζa)
          (uniformScaledRetainedDenominatorBound j.val d ti P Vi Wi ζi)))
        (max 1 (max ca ci) * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ 2 * ε := by
  intro d ta ti Va Vi Wa Wi ζa ζi fa fi ca ci Kmax R0 Q hQ hRQ hεa hεi hfa hfi hKQ hKLQ hεQ
  rcases allocatedSlicedGrid_cases B U basis S j i H hgrid hδ hdense
      ((Fintype.card α + 1) * q) T hQT with hsmall | ⟨hsize, hcases⟩
  · obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_bounded_grid_site_expansion
      B U basis hR hσ S q r H step c hH hsubset hcell j i hσ1 hgrid rows hsmall hε hQ hRQ hKQ hKLQ hεQ
    refine ⟨e, he.mono ?_ (le_max_left _ _) ?_ le_rfl le_rfl, ?_⟩
    · exact le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left _ _)
    · exact le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left _ _)
    · intro x y hy
      exact (herr x y hy).trans (by linarith)
  · rcases hcases with ⟨ha, hlength⟩ | ⟨hi, hl, hlength⟩
    · let M := torusA * height
      have hM : 0 < M := Nat.mul_pos (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
      let : NeZero M := ⟨hM.ne'⟩
      obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_grid_site_expansion_s2
        B U basis hR hσ S q hq r H step c hH hsubset hcell j i ha hsize hgrid hδ hlength hstep
        A hA P hcP hsP hstride (M := M) rfl rows hrows hBa hε hε1 hσ1 hε hQ hRQ hεa hfa
      refine ⟨e, he.mono ?_ ?_ ?_ le_rfl le_rfl, ?_⟩
      · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · intro x y hy
        simpa only [two_mul] using herr x y hy
    · let M := torusI * height
      have hM : 0 < M := Nat.mul_pos (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (basis j) i)
      let : NeZero M := ⟨hM.ne'⟩
      obtain ⟨e, he, herr⟩ := exists_allocatedSupportedSliced_inactive_grid_site_expansion_s2
        B U basis hR hσ S q hq r H step c hH hsubset hcell j i hsize hgrid hi hl hδ hlength hstep
        A hA P hP hsP hstride (M := M) rfl rows hrows hBi hε hε1 hσ1 hε hQ hRQ hεi hfi
      refine ⟨e, he.mono ?_ ?_ ?_ le_rfl le_rfl, ?_⟩
      · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
      · exact mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) (Real.exp_nonneg _)
      · intro x y hy
        simpa only [two_mul] using herr x y hy

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_mixed_grid_site_expansion_s2_oai.{uα, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_mixed_grid_site_expansion_s2_oai.{uα, u_1, u_2, u_3, u_4}
