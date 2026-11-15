-- Prove2me | solution 1 for LG2021.paper_strong_separation
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T15:15:42.407441+00:00
-- url     : https://prove2.me/submissions/a7a73113-6a8b-4f6e-b760-bf980a58696b

import Mathlib
import Definitions.Def_LG2021_GaussianEstimators
import Theorems.Thm_LG2021_gaussian_surrogate_separation


/- Gaussian projection adapter -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
theorem parameter_gaussian_inner_law {d : ℕ} (q : Space d) :
    (gaussian d).map (fun x => inner ℝ q x) = gaussianReal 0 (‖q‖ ^ 2).toNNReal := by
  change (stdGaussian (Space d)).map (innerSL ℝ q) = _
  rw [IsGaussian.map_eq_gaussianReal]
  simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm]

theorem parameter_gaussian_inner_hasSubgaussianMGF {d : ℕ} (q : Space d) :
    HasSubgaussianMGF (fun x => inner ℝ q x) (‖q‖ ^ 2).toNNReal (gaussian d) := by
  apply (HasSubgaussianMGF.id_map_iff (by fun_prop)).1
  rw [parameter_gaussian_inner_law]
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  simp [mgf_id_gaussianReal]


end LG2021

end
end

/- Finite Gaussian tail union -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The two-sided tail follows from the two one-sided bounds on the same probability space. -/
theorem measure_abs_ge_le_of_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c P) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have heq : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [heq]
  exact (measureReal_union_le _ _).trans (by
    have hp := hX.measure_ge_le hε
    have hn := hX.neg.measure_ge_le hε
    change P.real {ω | ε ≤ -X ω} ≤ _ at hn
    linarith)

/-- A finite family of sub-Gaussian deviations can be controlled simultaneously. -/
theorem measure_exists_abs_ge_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (c : ι → ℝ≥0)
    (ε : ι → ℝ) (hε : ∀ i, 0 ≤ ε i) (hX : ∀ i, HasSubgaussianMGF (X i) (c i) P) :
    P.real {ω | ∃ i, ε i ≤ |X i ω|} ≤
      ∑ i, 2 * Real.exp (-(ε i) ^ 2 / (2 * c i)) := by
  have heq : {ω | ∃ i, ε i ≤ |X i ω|} = ⋃ i, {ω | ε i ≤ |X i ω|} := by
    ext ω
    simp
  rw [heq]
  exact (measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum fun i _ =>
    measure_abs_ge_le_of_hasSubgaussianMGF P (hX i) (hε i))


end LG2021.Concentration

end

/- Euclidean norm tail -/
section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
theorem exists_coordinate_abs_ge_of_norm_gt {d : ℕ} (hd : 0 < d)
    {R : ℝ} (hR : 0 ≤ R) (x : Space d) (hx : R < ‖x‖) :
    ∃ i : Fin d, R / Real.sqrt (d : ℝ) ≤ |x i| := by
  by_contra h
  push_neg at h
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hcoord (i : Fin d) : (x i) ^ 2 ≤ (R / Real.sqrt (d : ℝ)) ^ 2 := by
    nlinarith [h i, sq_abs (x i), abs_nonneg (x i)]
  have hsum : ‖x‖ ^ 2 ≤ (d : ℝ) * (R / Real.sqrt (d : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin d, (R / Real.sqrt (d : ℝ)) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = _ := by simp
  have heq : (d : ℝ) * (R / Real.sqrt (d : ℝ)) ^ 2 = R ^ 2 := by
    rw [div_pow, Real.sq_sqrt hdR.le]
    field_simp [ne_of_gt hdR]
  rw [heq] at hsum
  nlinarith [norm_nonneg x]

/-- Coordinate sub-Gaussian tails imply a Euclidean norm tail without independence. -/
theorem measure_norm_gt_le_of_coordinate_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (hd : 0 < d) (X : Ω → Space d)
    (hX : ∀ i : Fin d, HasSubgaussianMGF (fun ω => X ω i) 1 P)
    {R : ℝ} (hR : 0 ≤ R) :
    P.real {ω | R < ‖X ω‖} ≤ 2 * (d : ℝ) * Real.exp (-R ^ 2 / (2 * (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsub : {ω | R < ‖X ω‖} ⊆
      {ω | ∃ i : Fin d, R / Real.sqrt (d : ℝ) ≤ |X ω i|} :=
    fun ω hω => exists_coordinate_abs_ge_of_norm_gt hd hR (X ω) hω
  have htail := measure_exists_abs_ge_le P (fun i ω => X ω i) (fun _ => 1)
    (fun _ => R / Real.sqrt (d : ℝ)) (fun _ => by positivity) hX
  simp only [NNReal.coe_one, mul_one] at htail
  have heq : -(R / Real.sqrt (d : ℝ)) ^ 2 / 2 =
      -R ^ 2 / (2 * (d : ℝ)) := by
    rw [div_pow, Real.sq_sqrt hdR.le]
    norm_num
    ring
  have hbound := (measureReal_mono hsub).trans htail
  simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbound
  calc
    _ ≤ (d : ℝ) * (2 * Real.exp (-R ^ 2 / (2 * (d : ℝ)))) := hbound
    _ = _ := by ring


end LG2021.Concentration

end

/- Standard Gaussian tail -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

/-- Every standard Gaussian coordinate has variance proxy one. -/
theorem gaussian_coordinate_hasSubgaussianMGF {d : ℕ} (i : Fin d) :
    HasSubgaussianMGF (fun x : Space d => x i) 1 (gaussian d) := by
  have h := LG2021.parameter_gaussian_inner_hasSubgaussianMGF (EuclideanSpace.single i (1 : ℝ))
  have hf : (fun x : Space d => inner ℝ (EuclideanSpace.single i (1 : ℝ)) x) =
      (fun x : Space d => x i) := by funext x; simp [EuclideanSpace.inner_single_left]
  rw [hf] at h
  refine ⟨h.integrable_exp_mul, ?_⟩
  intro t
  have hb := h.mgf_le t
  change mgf (fun x : Space d => x i) (gaussian d) t ≤
    Real.exp (((‖EuclideanSpace.single i (1 : ℝ)‖ ^ 2).toNNReal : ℝ) * t ^ 2 / 2) at hb
  simpa using hb

/-- The standard Gaussian norm has an explicit coordinate-union tail. -/
theorem gaussian_norm_gt_le {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 ≤ R) :
    (gaussian d).real {x | R < ‖x‖} ≤
      2 * (d : ℝ) * Real.exp (-R ^ 2 / (2 * (d : ℝ))) :=
  measure_norm_gt_le_of_coordinate_subgaussian (gaussian d) hd id
    gaussian_coordinate_hasSubgaussianMGF hR



end LG2021.Concentration

end

/- Explicit confidence parameter bounds -/
section

set_option autoImplicit false

namespace LG2021.Concentration

/-- Elementary bounds on the explicit confidence base. -/
theorem parameterBase_bounds (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    (10 ^ 6 : ℝ) ≤ parameterBase d D n ∧
      (d : ℝ) + 1 ≤ parameterBase d D n ∧
      D + 1 ≤ parameterBase d D n ∧
      (n : ℝ) + 1 ≤ parameterBase d D n ∧
      3 * (D + 1) * ((d : ℝ) + 1) ≤ parameterBase d D n := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdn : (1 : ℝ) ≤ ((d : ℝ) + 1) * ((n : ℝ) + 1) := by nlinarith
  have hDn : (1 : ℝ) ≤ (D + 1) * ((n : ℝ) + 1) := by nlinarith
  have hdD : (1 : ℝ) ≤ ((d : ℝ) + 1) * (D + 1) := by nlinarith
  unfold parameterBase
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n : ℝ) + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hDn (show 0 ≤ (d : ℝ) + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdn (show 0 ≤ D + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n : ℝ) + 1 by positivity)]
  · nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith)
      (show 0 ≤ ((d : ℝ) + 1) * (D + 1) by positivity)]

/-- The explicit confidence logarithm is bounded below and above. -/
theorem parameterLog_bounds (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ parameterLog d D n ∧ parameterLog d D n ≤ 32 * parameterBase d D n := by
  have hb := (parameterBase_bounds d n hD).1
  have hA : 0 < parameterBase d D n := by nlinarith
  have hlower : 1 ≤ Real.log (parameterBase d D n) := by
    apply (Real.le_log_iff_exp_le hA).2
    have h := Real.exp_one_lt_three
    nlinarith
  have hupper := Real.log_le_sub_one_of_pos hA
  unfold parameterLog
  constructor <;> linarith

/-- The confidence choice makes the half-exponential error an exact reciprocal polynomial. -/
theorem exp_neg_half_parameterLog (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    Real.exp (-parameterLog d D n / 2) = (parameterBase d D n)⁻¹ ^ 16 := by
  have hA : 0 < parameterBase d D n := by
    have h := (parameterBase_bounds d n hD).1
    nlinarith
  unfold parameterLog
  rw [show -(32 * Real.log (parameterBase d D n)) / 2 =
      (16 : ℝ) * (-Real.log (parameterBase d D n)) by ring]
  have he := Real.exp_nat_mul (-Real.log (parameterBase d D n)) 16
  norm_num at he
  simpa only [mul_neg, Real.exp_neg, Real.exp_log hA] using he


/-- Basic size bounds for the Gaussian scale in the logarithmic regime. -/
theorem paperRadius_bounds {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 ≤ paperRadius d L ∧
      0 < paperRadius d L ∧ paperRadius d L ≤ 2 * 10 ^ 5 * (d : ℝ) ^ 2 * L := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : 1 ≤ Real.sqrt (2 * L) := Real.one_le_sqrt.2 (by linarith)
  have hhi : Real.sqrt (2 * L) ≤ 2 * L := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  unfold paperRadius
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo (show 0 ≤ (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 by positivity)]
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hhi (show 0 ≤ (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 by positivity)]

/-- The contraction parameter is positive and uniformly small. -/
theorem paperLambda_bounds {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    0 < paperLambda d L ∧ paperLambda d L ≤ 1 / 2 ∧
      (d : ℝ) * paperLambda d L ≤ 1 / 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hLpos : 0 < L := by linarith
  have hden : 0 < (4 * 10 ^ 5 : ℝ) * (d : ℝ) * L := by positivity
  unfold paperLambda
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ hden).2
    have h := mul_le_mul hdR hL (by norm_num) (by positivity)
    nlinarith
  · rw [mul_one_div]
    apply (div_le_iff₀ hden).2
    have h := mul_le_mul_of_nonneg_left hL hdpos.le
    nlinarith

/-- The radius and contraction give the exact projection cutoff needed for Gaussian tails. -/
theorem paper_projection_scale {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    paperLambda d L * (paperRadius d L / (2 * (d : ℝ))) =
      1 / (4 * Real.sqrt (2 * L)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : 0 < L := by linarith
  have hs : 0 < Real.sqrt (2 * L) := Real.sqrt_pos.2 (by positivity)
  have hsq : (Real.sqrt (2 * L)) ^ 2 = 2 * L := Real.sq_sqrt (by positivity)
  unfold paperLambda paperRadius
  field_simp [ne_of_gt hdR, ne_of_gt hLpos, ne_of_gt hs]
  nlinarith [Real.sq_sqrt (show 0 ≤ L * 2 by positivity)]

/-- Coarse polynomial bounds suffice to absorb the explicit confidence error. -/
theorem parameter_size_bounds {d n : ℕ} (hd : 0 < d) {D : ℝ} (hD : 0 ≤ D) :
    paperRadius d (parameterLog d D n) ≤ 6400000 * (parameterBase d D n) ^ 3 ∧
    1 / paperLambda d (parameterLog d D n) ≤ 12800000 * (parameterBase d D n) ^ 2 ∧
    paperLipschitz d D (parameterLog d D n) ≤ D ∧
    3 * (1 + paperLipschitz d D (parameterLog d D n)) * ((d : ℝ) + 1) ≤ parameterBase d D n := by
  let A := parameterBase d D n
  let L := parameterLog d D n
  have hb := parameterBase_bounds d n hD
  have hA : 0 < A := by dsimp [A]; nlinarith [hb.1]
  have hdA : (d : ℝ) ≤ A := by dsimp [A]; linarith [hb.2.1]
  have hLb := parameterLog_bounds d n hD
  have hL : 1 ≤ L := hLb.1
  have hLA : L ≤ 32 * A := hLb.2
  have hr := paperRadius_bounds hd hL
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdr : (d : ℝ) ≤ paperRadius d L := by nlinarith [hr.1]
  have hell : paperLipschitz d D L ≤ D := by
    unfold paperLipschitz
    apply (div_le_iff₀ hr.2.1).2
    nlinarith [mul_le_mul_of_nonneg_left hdr hD]
  refine ⟨?_, ?_, hell, ?_⟩
  · calc
      _ ≤ 2 * 10 ^ 5 * (d : ℝ) ^ 2 * L := hr.2.2
      _ ≤ 2 * 10 ^ 5 * A ^ 2 * (32 * A) := by gcongr
      _ = _ := by ring
  · unfold paperLambda
    rw [one_div_one_div]
    calc
      _ ≤ 4 * 10 ^ 5 * A * (32 * A) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ 3 * (1 + D) * ((d : ℝ) + 1) := by gcongr
      _ ≤ A := by simpa only [add_comm] using hb.2.2.2.2



end LG2021.Concentration

end

/- Parameter-specialized separation -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory Concentration

theorem paper_lambda_radius_sq {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    paperLambda d L * (paperRadius d L / (2 * (d : ℝ))) ^ 2 = 12500 * d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : 0 < L := by linarith
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * L by positivity)
  unfold paperLambda paperRadius
  field_simp
  nlinarith [Real.sq_sqrt (show 0 ≤ L * 2 by positivity)]

theorem paper_separation_curvature {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    4 ≤ (paperLambda d L / 2) * Real.exp (-2) *
      (paperRadius d L / (2 * (d : ℝ))) ^ 2 / (64 * (d : ℝ)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hid := paper_lambda_radius_sq hd hL
  have he : Real.exp (2 : ℝ) ≤ 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 : ℝ)]
  have hexp : (1 / 9 : ℝ) ≤ Real.exp (-2) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 2) he
  have hratio : (paperLambda d L / 2) * Real.exp (-2) *
      (paperRadius d L / (2 * (d : ℝ))) ^ 2 / (64 * (d : ℝ)) =
      (12500 / 128 : ℝ) * Real.exp (-2) := by
    have heq : (paperLambda d L / 2) * Real.exp (-2) *
        (paperRadius d L / (2 * (d : ℝ))) ^ 2 =
        (paperLambda d L * (paperRadius d L / (2 * (d : ℝ))) ^ 2) * Real.exp (-2) / 2 := by ring
    rw [heq, hid]
    field_simp
    ring
  rw [hratio]
  linarith

theorem paper_separation_shift {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    (paperLambda d L * (paperRadius d L / (2 * (d : ℝ)))) ^ 2 /
      (2 * (1 - paperLambda d L) ^ 2) ≤ 1 := by
  have hl := paperLambda_bounds hd hL
  have hα : 1 / 2 ≤ 1 - paperLambda d L := by linarith
  have hαsq : 1 / 4 ≤ (1 - paperLambda d L) ^ 2 := by nlinarith
  have hs : (Real.sqrt (2 * L)) ^ 2 = 2 * L := Real.sq_sqrt (by positivity)
  have hLpos : 0 < L := by linarith
  have hsp : 0 < Real.sqrt (2 * L) := Real.sqrt_pos.2 (by positivity)
  rw [paper_projection_scale hd hL]
  apply (div_le_one (by positivity : 0 < 2 * (1 - paperLambda d L) ^ 2)).2
  have hsmall : (1 / (4 * Real.sqrt (2 * L))) ^ 2 ≤ 1 / 32 := by
    rw [div_pow, one_pow, mul_pow, hs]
    apply (div_le_iff₀ (by positivity : 0 < (4 : ℝ) ^ 2 * (2 * L))).2
    nlinarith
  linarith

theorem parameter_exp_log_inverse (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    Real.exp (-parameterLog d D n) = (parameterBase d D n)⁻¹ ^ 32 := by
  have hA : 0 < parameterBase d D n := by unfold parameterBase; positivity
  unfold parameterLog
  rw [show -(32 * Real.log (parameterBase d D n)) =
      (32 : ℝ) * (-Real.log (parameterBase d D n)) by ring]
  have he := Real.exp_nat_mul (-Real.log (parameterBase d D n)) 32
  norm_num at he
  simpa only [mul_neg, Real.exp_neg, Real.exp_log hA] using he

theorem parameter_gaussian_cutoff_tail {d : ℕ} (hd : 0 < d) {D : ℝ}
    (hD : 0 ≤ D) (n : ℕ) :
    (gaussian d).real {x | Real.sqrt (4 * (d : ℝ) * parameterLog d D n) < ‖x‖} ≤
      Real.exp (-parameterLog d D n) := by
  let A := parameterBase d D n
  let L := parameterLog d D n
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hL : 1 ≤ L := (parameterLog_bounds d n hD).1
  have hAmin : (10 ^ 6 : ℝ) ≤ A := (parameterBase_bounds d n hD).1
  have hA : 0 < A := by nlinarith
  have hdA : (d : ℝ) + 1 ≤ A := (parameterBase_bounds d n hD).2.1
  have htail := gaussian_norm_gt_le hd (R := Real.sqrt (4 * (d : ℝ) * L)) (by positivity)
  have hsq : Real.sqrt (4 * (d : ℝ) * L) ^ 2 = 4 * (d : ℝ) * L :=
    Real.sq_sqrt (by positivity)
  have hexponent : -(Real.sqrt (4 * (d : ℝ) * L)) ^ 2 / (2 * (d : ℝ)) = -2 * L := by
    rw [hsq]
    field_simp
    ring
  rw [hexponent] at htail
  apply htail.trans
  have hpower : 2 * (d : ℝ) ≤ A ^ 32 := by
    have hp := pow_le_pow_right₀ (by nlinarith : (1 : ℝ) ≤ A) (by norm_num : 2 ≤ 32)
    nlinarith
  have hsmall : 2 * (d : ℝ) * Real.exp (-L) ≤ 1 := by
    rw [show Real.exp (-L) = A⁻¹ ^ 32 from parameter_exp_log_inverse d n hD,
      inv_pow]
    apply (mul_inv_le_iff₀ (pow_pos hA 32)).2
    simpa only [one_mul] using hpower
  have hexp : Real.exp (-2 * L) = Real.exp (-L) * Real.exp (-L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_right hsmall (Real.exp_pos (-L)).le]

theorem paper_separation_variance {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    ((1 - (1 - paperLambda d L) ^ 2) * (Real.sqrt (4 * (d : ℝ) * L)) ^ 2) /
      (2 * (1 - paperLambda d L) ^ 2) ≤ 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hLpos : 0 < L := by linarith
  have hl := paperLambda_bounds hd hL
  have hα : 1 / 2 ≤ 1 - paperLambda d L := by linarith
  have hαsq : 1 / 4 ≤ (1 - paperLambda d L) ^ 2 := by nlinarith
  have hs : Real.sqrt (4 * (d : ℝ) * L) ^ 2 = 4 * (d : ℝ) * L :=
    Real.sq_sqrt (by positivity)
  have heq : paperLambda d L * (4 * (d : ℝ) * L) = (1 / 100000 : ℝ) := by
    unfold paperLambda
    field_simp
    ring
  have hn : (1 - (1 - paperLambda d L) ^ 2) * (4 * (d : ℝ) * L) ≤
      2 * paperLambda d L * (4 * (d : ℝ) * L) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg (paperLambda d L)]
  rw [hs]
  apply (div_le_one (by positivity : 0 < 2 * (1 - paperLambda d L) ^ 2)).2
  nlinarith

theorem parameter_sqrt_gaussian_tail (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    Real.sqrt ((d : ℝ)*Real.exp (-parameterLog d D n)) =
      Real.sqrt (d : ℝ)*(parameterBase d D n)⁻¹^16 := by
  rw [Real.sqrt_mul (Nat.cast_nonneg d), parameter_exp_log_inverse d n hD]
  have heq : (parameterBase d D n)⁻¹^32 = ((parameterBase d D n)⁻¹^16)^2 := by ring
  rw [heq, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

theorem paper_separation_error {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {K : NNReal}
    (hK : (K : ℝ) ≤ paperLipschitz d D (parameterLog d D n)) :
    ((paperLambda d (parameterLog d D n)/2)*Real.exp (-2)*
      (2*(K : ℝ)*Real.sqrt ((d : ℝ)*Real.exp (-parameterLog d D n))))*
        (paperRadius d (parameterLog d D n)/(2*(d : ℝ)))^2 ≤
      (1/(n : ℝ))/(4096*(d : ℝ)*Real.sqrt (d : ℝ)) := by
  let A := parameterBase d D n
  let L := parameterLog d D n
  let R := paperRadius d L/(2*(d : ℝ))
  let C := 4096*(d : ℝ)*Real.sqrt (d : ℝ)
  let error := ((paperLambda d L/2)*Real.exp (-2)*
    (2*(K : ℝ)*Real.sqrt ((d : ℝ)*Real.exp (-L))))*R^2
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hL : 1 ≤ L := (parameterLog_bounds d n hD).1
  have hbase := parameterBase_bounds d n hD
  have hAmin : (10^6 : ℝ) ≤ A := hbase.1
  have hApos : 0 < A := by nlinarith
  have hA1 : 1 ≤ A := by nlinarith
  have hdA : (d : ℝ) ≤ A := by linarith [hbase.2.1]
  have hDA : D ≤ A := by linarith [hbase.2.2.1]
  have hnA : (n : ℝ) ≤ A := by linarith [hbase.2.2.2.1]
  have hKD : (K : ℝ) ≤ D := hK.trans (parameter_size_bounds hd hD).2.2.1
  have hsmall : 51200000*(d : ℝ)^3*D*(n : ℝ) ≤ A^16 := by
    have hp : A^2 ≤ A^11 := pow_le_pow_right₀ hA1 (by norm_num : 2 ≤ 11)
    have hc : (51200000 : ℝ) ≤ A^11 := by nlinarith
    calc
      _ ≤ 51200000*A^3*A*A := by gcongr
      _ = 51200000*A^5 := by ring
      _ ≤ A^11*A^5 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hsq : Real.sqrt (d : ℝ)^2 = d := Real.sq_sqrt hdpos.le
  have hformula : error*C*(n : ℝ) =
      51200000*(d : ℝ)^3*(K : ℝ)*(n : ℝ)*Real.exp (-2)*A⁻¹^16 := by
    dsimp only [error, C]
    rw [show Real.sqrt ((d : ℝ)*Real.exp (-L)) = Real.sqrt (d : ℝ)*A⁻¹^16 from
      parameter_sqrt_gaussian_tail d n hD]
    calc
      _ = (paperLambda d L*R^2)*4096*(d : ℝ)*(K : ℝ)*(n : ℝ)*
          (Real.sqrt (d : ℝ))^2*Real.exp (-2)*A⁻¹^16 := by ring
      _ = _ := by rw [show paperLambda d L*R^2 = 12500*(d : ℝ) from paper_lambda_radius_sq hd hL, hsq]; ring
  have hexp : Real.exp (-2 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have herr : error*C*(n : ℝ) ≤ 1 := by
    rw [hformula]
    calc
      _ ≤ 51200000*(d : ℝ)^3*D*(n : ℝ)*1*A⁻¹^16 := by gcongr
      _ = (51200000*(d : ℝ)^3*D*(n : ℝ))*A⁻¹^16 := by ring
      _ ≤ A^16*A⁻¹^16 := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hApos.ne', one_pow]
  change error ≤ (1/(n : ℝ))/C
  apply (le_div_iff₀ hCpos).2
  exact (le_div_iff₀ hnpos).2 herr

/-- Parameter-specialized direct replacement for Lemma 5, for every nonsmooth convex
Lipschitz loss. Only universal constants in the separation margin are changed. -/
theorem paper_strong_separation {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {f : Space d → ℝ} {K : NNReal}
    (hK : (K : ℝ) ≤ paperLipschitz d D (parameterLog d D n))
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) :
    (1/24 : ℝ) ≤
      (sphereMeasure d (paperRadius d (parameterLog d D n)/(2*(d : ℝ)))).real {z |
        (gaussianGap (paperRadius d (parameterLog d D n)) f-1/(n : ℝ))/
          (4096*(d : ℝ)*Real.sqrt (d : ℝ)) ≤
        surrogate (paperLambda d (parameterLog d D n)) f z-f 0} := by
  let L := parameterLog d D n
  have hL : 1 ≤ L := (parameterLog_bounds d n hD).1
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hl := paperLambda_bounds hd hL
  have hr := paperRadius_bounds hd hL
  have hgain : 4 ≤ (paperLambda d L/2)*Real.exp (-2)*
      ((paperRadius d L/(2*(d : ℝ)))^2/(64*(d : ℝ))) := by
    convert paper_separation_curvature hd hL using 1 <;> ring
  have h := gaussian_surrogate_separation hd hf hc hl.1 (by linarith : paperLambda d L < 1)
    (div_pos hr.2.1 (by positivity) : 0 < paperRadius d L/(2*(d : ℝ)))
    (Real.sqrt_nonneg (4*(d : ℝ)*L)) (paper_separation_variance hd hL)
    (paper_separation_shift hd hL) (parameter_gaussian_cutoff_tail hd hD n)
    hgain (paper_separation_error hd hn hD hK)
  have hradius : 2*(d : ℝ)*(paperRadius d L/(2*(d : ℝ))) = paperRadius d L := by
    field_simp
  rw [hradius] at h
  exact h

end LG2021

end
end

open LG2021 LG2021.Concentration MeasureTheory ProbabilityTheory

theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {f : Space d → ℝ} {K : NNReal}
    (hK : (K : ℝ) ≤ paperLipschitz d D (parameterLog d D n))
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) :
    (1/24 : ℝ) ≤
      (sphereMeasure d (paperRadius d (parameterLog d D n)/(2*(d : ℝ)))).real {z |
        (gaussianGap (paperRadius d (parameterLog d D n)) f-1/(n : ℝ))/
          (4096*(d : ℝ)*Real.sqrt (d : ℝ)) ≤
        surrogate (paperLambda d (parameterLog d D n)) f z-f 0} := by
  exact LG2021.paper_strong_separation hd hn hD hK hf hc
