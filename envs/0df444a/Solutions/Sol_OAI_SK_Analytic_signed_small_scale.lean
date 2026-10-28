-- Prove2me | solution 1 for OAI.SK.Analytic.signed_small_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:20:46.38723+00:00
-- url     : https://prove2.me/submissions/3d0b968a-2006-4367-8497-05b23a62383e

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S005
import Definitions.Def_OAIQ036S006
import Theorems.Thm_OAI_SK_Analytic_exists_negative_tripleCDF_coefficient
import Theorems.Thm_OAI_SK_Analytic_pairMismatch_pressure_gap
import Theorems.Thm_OAI_SK_Analytic_quenchedPressure_quantitative_finiteInf
import Theorems.Thm_OAI_SK_Analytic_tripleConstrainedPressure_quadratic

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_Basic
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem overlap_comm {n : ℕ} (x y : Config n) : overlap x y = overlap y x := by
  simp only [overlap, mul_comm]

theorem disorder_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun J : Disorder n => J e) (gaussianReal 0 1) (disorderLaw n) := by
  exact (measurePreserving_eval (fun _ : Edge n => gaussianReal 0 1) e).hasLaw

theorem disorder_coordinate_gaussian {n : ℕ} (e : Edge n) :
    HasGaussianLaw (fun J : Disorder n => J e) (disorderLaw n) :=
  (disorder_coordinate_law e).hasGaussianLaw

theorem disorder_independent (n : ℕ) :
    iIndepFun (fun e (J : Disorder n) => J e) (disorderLaw n) := by
  exact iIndepFun_pi (fun _ => aemeasurable_id)

theorem disorder_gaussian (n : ℕ) : HasGaussianLaw (fun J : Disorder n => J) (disorderLaw n) :=
  (disorder_independent n).hasGaussianLaw disorder_coordinate_gaussian

theorem hamiltonian_gaussian {n : ℕ} (x : Config n) :
    HasGaussianLaw (fun J : Disorder n => hamiltonian J x) (disorderLaw n) := by
  have h : HasGaussianLaw
      (fun J : Disorder n => fun e : Edge n =>
        J e * spin (x e.val.1) * spin (x e.val.2)) (disorderLaw n) := by
    have hi : iIndepFun (fun e (J : Disorder n) =>
        J e * spin (x e.val.1) * spin (x e.val.2)) (disorderLaw n) := by
      exact iIndepFun_pi (μ := fun _ : Edge n => gaussianReal 0 1)
        (X := fun e z => z * spin (x e.val.1) * spin (x e.val.2))
        (fun _ => by fun_prop)
    apply hi.hasGaussianLaw
    intro e
    convert (disorder_coordinate_gaussian e).fun_smul
      (spin (x e.val.1) * spin (x e.val.2)) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [smul_eq_mul]
    funext J
    ring
  simpa only [hamiltonian, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    h.fun_sum.fun_smul (Real.sqrt n)⁻¹

theorem disorder_mean_zero {n : ℕ} (e : Edge n) :
    ∫ J : Disorder n, J e ∂disorderLaw n = 0 := by
  rw [disorderLaw, integral_eval]
  exact integral_id_gaussianReal

theorem hamiltonian_mean_zero {n : ℕ} (x : Config n) :
    ∫ J : Disorder n, hamiltonian J x ∂disorderLaw n = 0 := by
  simp only [hamiltonian, div_eq_mul_inv]
  rw [integral_mul_const, integral_finsetSum]
  · simp only [integral_mul_const, disorder_mean_zero, zero_mul, Finset.sum_const_zero]
  · intro e _
    exact ((disorder_coordinate_gaussian e).integrable.mul_const _).mul_const _

theorem disorder_covariance {n : ℕ} (e f : Edge n) :
    cov[fun J : Disorder n => J e, fun J : Disorder n => J f; disorderLaw n] =
      if e = f then 1 else 0 := by
  classical
  by_cases hef : e = f
  · subst f
    rw [covariance_self (disorder_coordinate_gaussian e).aemeasurable, (disorder_coordinate_law e).variance_eq]
    simp
  · rw [(disorder_independent n).indepFun hef |>.covariance_eq_zero
      (disorder_coordinate_gaussian e).memLp_two
      (disorder_coordinate_gaussian f).memLp_two]
    simp [hef]

theorem hamiltonian_covariance_edges {n : ℕ} (x y : Config n) :
    cov[fun J : Disorder n => hamiltonian J x,
      fun J : Disorder n => hamiltonian J y; disorderLaw n] =
    (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
      (spin (y e.val.1) * spin (y e.val.2))) / n := by
  classical
  simp only [hamiltonian, div_eq_mul_inv, covariance_mul_const_left,
    covariance_mul_const_right]
  rw [covariance_fun_sum_fun_sum]
  · simp only [covariance_mul_const_left, covariance_mul_const_right, disorder_covariance]
    have hsum : (∑ e : Edge n, ∑ f : Edge n,
        (if e = f then (1 : ℝ) else 0) * spin (x e.val.1) * spin (x e.val.2) *
          spin (y f.val.1) * spin (y f.val.2)) =
        ∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
          (spin (y e.val.1) * spin (y e.val.2)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_eq_single e]
      · simp [mul_assoc]
      · intro f _ hfe
        simp [Ne.symm hfe]
      · simp
    rw [hsum]
    rw [mul_assoc, ← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg n)]
  · intro e
    exact ((disorder_coordinate_gaussian e).memLp_two.mul_const _).mul_const _
  · intro e
    exact ((disorder_coordinate_gaussian e).memLp_two.mul_const _).mul_const _

theorem sum_edges {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ e : Edge n, f e.val) = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then f (i, j) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (by simp) f]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem sum_sq_eq_edges {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i) ^ 2 = (∑ i, (a i) ^ 2) + 2 * ∑ e : Edge n, a e.val.1 * a e.val.2 := by
  classical
  rw [sum_edges (fun p : Fin n × Fin n => a p.1 * a p.2), pow_two, Fintype.sum_mul_sum]
  have hsplit (i j : Fin n) : a i * a j =
      (if i = j then a i ^ 2 else 0) +
      (if i < j then a i * a j else 0) +
      (if j < i then a i * a j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j
      simp [pow_two]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, a i * a j) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((if i = j then a i ^ 2 else 0) +
        (if i < j then a i * a j else 0) +
        (if j < i then a i * a j else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsplit i j
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hd : (∑ i : Fin n, ∑ j : Fin n, if i = j then a i ^ 2 else 0) =
      ∑ i, a i ^ 2 := by simp
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then a i * a j else 0 := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hd, hs]
  ring

theorem overlap_self {n : ℕ} (hn : 0 < n) (x : Config n) : overlap x x = 1 := by
  simp only [overlap, ← pow_two, spin_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hn.ne')

theorem hamiltonian_covariance {n : ℕ} (hn : 0 < n) (x y : Config n) :
    cov[fun J : Disorder n => hamiltonian J x,
      fun J : Disorder n => hamiltonian J y; disorderLaw n] =
      ((n : ℝ) * overlap x y ^ 2 - 1) / 2 := by
  rw [hamiltonian_covariance_edges]
  have hs := sum_sq_eq_edges (fun i => spin (x i) * spin (y i))
  have hd : (∑ i : Fin n, (spin (x i) * spin (y i)) ^ 2) = (n : ℝ) := by
    simp [mul_pow]
  rw [hd] at hs
  have he : (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
      (spin (y e.val.1) * spin (y e.val.2))) =
      ((∑ i : Fin n, spin (x i) * spin (y i)) ^ 2 - n) / 2 := by
    have hr : (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
        (spin (y e.val.1) * spin (y e.val.2))) =
        ∑ e : Edge n, (spin (x e.val.1) * spin (y e.val.1)) *
          (spin (x e.val.2) * spin (y e.val.2)) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [hr]
    linarith
  rw [he, overlap]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn']

theorem hamiltonian_variance {n : ℕ} (hn : 0 < n) (x : Config n) :
    Var[fun J : Disorder n => hamiltonian J x; disorderLaw n] = ((n : ℝ) - 1) / 2 := by
  rw [← covariance_self (hamiltonian_gaussian x).aemeasurable,
    hamiltonian_covariance hn, overlap_self hn]
  ring

theorem gaussian_exp_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : HasGaussianLaw X μ) (t : ℝ) :
    (∫ ω, Real.exp (t * X ω) ∂μ) =
      Real.exp ((∫ ω, X ω ∂μ) * t + Var[X; μ] * t ^ 2 / 2) := by
  change mgf X μ t = _
  rw [mgf_gaussianReal hX.map_eq_gaussianReal,
    Real.coe_toNNReal _ (variance_nonneg X μ)]

theorem gaussian_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : HasGaussianLaw X μ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  have := hX.isProbabilityMeasure
  rw [← mgf_pos_iff, mgf_gaussianReal hX.map_eq_gaussianReal]
  exact Real.exp_pos _

theorem hamiltonian_exp_integral {n : ℕ} (hn : 0 < n) (x : Config n) (t : ℝ) :
    (∫ J : Disorder n, Real.exp (t * hamiltonian J x) ∂disorderLaw n) =
      Real.exp (t ^ 2 * ((n : ℝ) - 1) / 4) := by
  rw [gaussian_exp_integral (hamiltonian_gaussian x),
    hamiltonian_mean_zero, hamiltonian_variance hn]
  congr 1
  ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_DisorderPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

instance disorderLaw_isGaussian (n : ℕ) : IsGaussian (disorderLaw n) := by
  have h := (disorder_gaussian n).isGaussian_map
  change IsGaussian (Measure.map id (disorderLaw n)) at h
  rwa [Measure.map_id] at h

theorem disorderPair_fst_law (n : ℕ) :
    HasLaw (Prod.fst : Disorder n × Disorder n → Disorder n)
      (disorderLaw n) (disorderPairLaw n) :=
  measurePreserving_fst.hasLaw

theorem disorderPair_snd_law (n : ℕ) :
    HasLaw (Prod.snd : Disorder n × Disorder n → Disorder n)
      (disorderLaw n) (disorderPairLaw n) :=
  measurePreserving_snd.hasLaw

theorem disorderPair_independent (n : ℕ) :
    IndepFun (Prod.fst : Disorder n × Disorder n → Disorder n)
      Prod.snd (disorderPairLaw n) := by
  apply (indepFun_iff_hasLaw_prodMk_prod (disorderPair_fst_law n)
    (disorderPair_snd_law n)).2
  exact HasLaw.id

theorem disorderPair_gaussian (n : ℕ) :
    HasGaussianLaw (fun p : Disorder n × Disorder n => p) (disorderPairLaw n) :=
  (disorderPair_independent n).hasGaussianLaw (disorderPair_fst_law n).hasGaussianLaw
    (disorderPair_snd_law n).hasGaussianLaw

theorem disorderPair_fst_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun p : Disorder n × Disorder n => p.1 e)
      (gaussianReal 0 1) (disorderPairLaw n) :=
  (disorder_coordinate_law e).fun_comp (disorderPair_fst_law n)

theorem disorderPair_snd_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun p : Disorder n × Disorder n => p.2 e)
      (gaussianReal 0 1) (disorderPairLaw n) :=
  (disorder_coordinate_law e).fun_comp (disorderPair_snd_law n)

theorem disorderPair_fst_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.1 e,
      fun p : Disorder n × Disorder n => p.1 f; disorderPairLaw n] =
      if e = f then 1 else 0 := by
  rw [(disorderPair_fst_law n).covariance_fun_comp
    (disorder_coordinate_law e).aemeasurable (disorder_coordinate_law f).aemeasurable]
  exact disorder_covariance e f

theorem disorderPair_snd_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.2 e,
      fun p : Disorder n × Disorder n => p.2 f; disorderPairLaw n] =
      if e = f then 1 else 0 := by
  rw [(disorderPair_snd_law n).covariance_fun_comp
    (disorder_coordinate_law e).aemeasurable (disorder_coordinate_law f).aemeasurable]
  exact disorder_covariance e f

theorem disorderPair_cross_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.1 e,
      fun p : Disorder n × Disorder n => p.2 f; disorderPairLaw n] = 0 := by
  exact ((disorderPair_independent n).comp (measurable_pi_apply e)
    (measurable_pi_apply f)).covariance_eq_zero
      (disorderPair_fst_coordinate_law e).hasGaussianLaw.memLp_two
      (disorderPair_snd_coordinate_law f).hasGaussianLaw.memLp_two

theorem covariance_linear_combination {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y Z W : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) (hW : MemLp W 2 μ)
    (a b c d : ℝ) :
    cov[fun ω => a * X ω + b * Y ω, fun ω => c * Z ω + d * W ω; μ] =
      a * c * cov[X, Z; μ] + a * d * cov[X, W; μ] +
      b * c * cov[Y, Z; μ] + b * d * cov[Y, W; μ] := by
  change cov[(fun ω => a * X ω) + (fun ω => b * Y ω),
    (fun ω => c * Z ω) + (fun ω => d * W ω); μ] = _
  rw [covariance_add_left (hX.const_mul a) (hY.const_mul b)
      ((hZ.const_mul c).add (hW.const_mul d)),
    covariance_add_right (hX.const_mul a) (hZ.const_mul c) (hW.const_mul d),
    covariance_add_right (hY.const_mul b) (hZ.const_mul c) (hW.const_mul d)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

theorem mixDisorder_gaussian (n : ℕ) (a b : ℝ) :
    HasGaussianLaw (mixDisorder (n := n) a b) (disorderPairLaw n) :=
  (disorderPair_gaussian n).map_fun (mixDisorderCLM n a b)

theorem mixDisorder_mean {n : ℕ} (a b : ℝ) (e : Edge n) :
    (∫ p, mixDisorder a b p e ∂disorderPairLaw n) = 0 := by
  change (∫ p : Disorder n × Disorder n, a * p.1 e + b * p.2 e ∂disorderPairLaw n) = 0
  rw [integral_add
    ((disorderPair_fst_coordinate_law e).hasGaussianLaw.integrable.const_mul a)
    ((disorderPair_snd_coordinate_law e).hasGaussianLaw.integrable.const_mul b),
    integral_const_mul, integral_const_mul,
    (disorderPair_fst_coordinate_law e).integral_eq,
    (disorderPair_snd_coordinate_law e).integral_eq]
  simp

theorem mixDisorder_covariance {n : ℕ} (a b c d : ℝ) (e f : Edge n) :
    cov[fun p => mixDisorder a b p e, fun p => mixDisorder c d p f; disorderPairLaw n] =
      (a * c + b * d) * (if e = f then 1 else 0) := by
  change cov[fun p : Disorder n × Disorder n => a * p.1 e + b * p.2 e,
    fun p : Disorder n × Disorder n => c * p.1 f + d * p.2 f; disorderPairLaw n] = _
  rw [covariance_linear_combination
    (disorderPair_fst_coordinate_law e).hasGaussianLaw.memLp_two
    (disorderPair_snd_coordinate_law e).hasGaussianLaw.memLp_two
    (disorderPair_fst_coordinate_law f).hasGaussianLaw.memLp_two
    (disorderPair_snd_coordinate_law f).hasGaussianLaw.memLp_two,
    disorderPair_fst_covariance, disorderPair_snd_covariance, disorderPair_cross_covariance]
  rw [covariance_comm (fun p : Disorder n × Disorder n => p.2 e),
    disorderPair_cross_covariance]
  ring

theorem mixDisorder_coordinate_law {n : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (e : Edge n) :
    HasLaw (fun p => mixDisorder a b p e) (gaussianReal 0 1) (disorderPairLaw n) := by
  have hg := (mixDisorder_gaussian n a b).eval e
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, mixDisorder_mean,
    ← covariance_self hg.aemeasurable, mixDisorder_covariance]
  simp only [ite_true, mul_one]
  have h : a * a + b * b = 1 := by nlinarith [hab]
  rw [h]
  norm_num

theorem mixDisorder_law {n : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    HasLaw (mixDisorder (n := n) a b) (disorderLaw n) (disorderPairLaw n) := by
  apply iIndepFun.hasLaw_pi (fun e => mixDisorder_coordinate_law a b hab e)
  apply (mixDisorder_gaussian n a b).iIndepFun_of_covariance_eq_zero
  intro e f hef
  rw [mixDisorder_covariance, ite_eq_right hef, mul_zero]

theorem rotateDisorder_gaussian (n : ℕ) (θ : ℝ) :
    HasGaussianLaw (rotateDisorder (n := n) θ) (disorderPairLaw n) :=
  (disorderPair_gaussian n).map_fun (rotateDisorderCLM n θ)

theorem rotateDisorder_law (n : ℕ) (θ : ℝ) :
    HasLaw (rotateDisorder (n := n) θ) (disorderPairLaw n) (disorderPairLaw n) := by
  have hind : IndepFun (mixDisorder (n := n) (Real.cos θ) (Real.sin θ))
      (mixDisorder (- Real.sin θ) (Real.cos θ)) (disorderPairLaw n) := by
    apply (rotateDisorder_gaussian n θ).indepFun_of_covariance_eval
    intro e f
    rw [mixDisorder_covariance]
    ring
  exact hind.hasLaw_prod
    (mixDisorder_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))
    (mixDisorder_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))

theorem directionalEnergy_exp_le {n : ℕ} (β ℓ : ℝ) (J K : Disorder n) :
    Real.exp (ℓ * directionalEnergy β J K) ≤
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x) := by
  have h := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := gibbs β J) (p := fun x => ℓ * β * hamiltonian K x)
    (fun x _ => le_of_lt (gibbs_pos β J x)) (gibbs_sum β J)
    (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, ← Finset.mul_sum, directionalEnergy, mul_assoc,
    mul_left_comm (gibbs β J _)] using h

theorem continuous_partition {n : ℕ} (β : ℝ) :
    Continuous (partition (n := n) β) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _ =>
    Real.continuous_exp.comp (continuous_const.mul (continuous_hamiltonian x)))

theorem continuous_gibbs {n : ℕ} (β : ℝ) (x : Config n) :
    Continuous (fun J : Disorder n => gibbs β J x) := by
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_hamiltonian x))).div
    (continuous_partition β) (fun J => ne_of_gt (partition_pos β J))

theorem gibbs_le_one {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) :
    gibbs β J x ≤ 1 := by
  rw [← gibbs_sum β J]
  exact Finset.single_le_sum (fun z _ => le_of_lt (gibbs_pos β J z)) (Finset.mem_univ x)

theorem gibbs_integrable {n : ℕ} (β : ℝ) (x : Config n) :
    Integrable (fun J : Disorder n => gibbs β J x) (disorderLaw n) := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_gibbs β x).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs, abs_of_pos (gibbs_pos β J x)] using gibbs_le_one β J x

theorem continuous_directionalEnergy {n : ℕ} (β : ℝ) :
    Continuous (fun p : Disorder n × Disorder n => directionalEnergy β p.1 p.2) := by
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun x _ =>
    ((continuous_gibbs β x).comp continuous_fst).mul
      ((continuous_hamiltonian x).comp continuous_snd))

theorem directionalEnergy_exp_integrable {n : ℕ} (β ℓ : ℝ) (J : Disorder n) :
    Integrable (fun K : Disorder n => Real.exp (ℓ * directionalEnergy β J K))
      (disorderLaw n) := by
  have hsum : Integrable (fun K : Disorder n =>
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x))
      (disorderLaw n) :=
    integrable_finsetSum _ (fun x _ =>
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _)
  apply hsum.mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_directionalEnergy β).comp (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · filter_upwards [] with K
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ J K

theorem directionalEnergy_exp_integral_le {n : ℕ} (hn : 0 < n)
    (β ℓ : ℝ) (J : Disorder n) :
    (∫ K : Disorder n, Real.exp (ℓ * directionalEnergy β J K) ∂disorderLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hsum (x : Config n) : Integrable (fun K : Disorder n =>
      gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) (disorderLaw n) :=
    (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _
  calc
    _ ≤ ∫ K : Disorder n, (∑ x : Config n,
        gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) ∂disorderLaw n :=
      integral_mono (directionalEnergy_exp_integrable β ℓ J)
        (integrable_finsetSum _ (fun x _ => hsum x)) (directionalEnergy_exp_le β ℓ J)
    _ = _ := by
      rw [integral_finsetSum _ (fun x _ => hsum x)]
      simp_rw [integral_const_mul, hamiltonian_exp_integral hn]
      rw [← Finset.sum_mul, gibbs_sum, one_mul]

theorem directionalEnergy_pair_exp_integrable {n : ℕ} (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) := by
  have hsum : Integrable (fun p : Disorder n × Disorder n =>
      ∑ x : Config n, gibbs β p.1 x * Real.exp (ℓ * β * hamiltonian p.2 x))
      (disorderPairLaw n) := by
    apply integrable_finsetSum
    intro x _
    exact (gibbs_integrable β x).mul_prod
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β))
  apply hsum.mono'
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy β))).aestronglyMeasurable
  · filter_upwards [] with p
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ p.1 p.2

theorem directionalEnergy_pair_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β p.1 p.2) ∂disorderPairLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  rw [disorderPairLaw, integral_prod _ (directionalEnergy_pair_exp_integrable β ℓ)]
  calc
    _ ≤ ∫ _J : Disorder n,
        Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂disorderLaw n :=
      integral_mono (directionalEnergy_pair_exp_integrable β ℓ).integral_prod_left
        (integrable_const _) (directionalEnergy_exp_integral_le hn β ℓ)
    _ = _ := by simp

theorem hamiltonian_mix {n : ℕ} (a b : ℝ) (p : Disorder n × Disorder n) (x : Config n) :
    hamiltonian (mixDisorder a b p) x =
      a * hamiltonian p.1 x + b * hamiltonian p.2 x := by
  simp only [hamiltonian, mixDisorder, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_LogPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem continuous_logPartition {n : ℕ} (β : ℝ) :
    Continuous (logPartition (n := n) β) :=
  (continuous_partition β).log (fun J => ne_of_gt (partition_pos β J))

theorem logPartition_hasDerivAt {n : ℕ} (β : ℝ) (J : ℝ → Disorder n)
    (K : Disorder n) (s : ℝ)
    (hJ : ∀ x, HasDerivAt (fun t => hamiltonian (J t) x) (hamiltonian K x) s) :
    HasDerivAt (fun t => logPartition β (J t)) (directionalEnergy β (J s) K) s := by
  have hp : HasDerivAt (fun t => partition β (J t))
      (∑ x : Config n, Real.exp (β * hamiltonian (J s) x) * (β * hamiltonian K x)) s := by
    exact HasDerivAt.fun_sum (fun x _ => ((hJ x).const_mul β).exp)
  have hl := hp.log (ne_of_gt (partition_pos β (J s)))
  have heq : (∑ x : Config n, Real.exp (β * hamiltonian (J s) x) *
      (β * hamiltonian K x)) / partition β (J s) =
      directionalEnergy β (J s) K := by
    simp only [directionalEnergy, gibbs, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq] at hl
  exact hl

theorem continuous_rotateDisorder (n : ℕ) :
    Continuous (fun q : ℝ × (Disorder n × Disorder n) => rotateDisorder q.1 q.2) := by
  unfold rotateDisorder mixDisorder
  fun_prop

theorem rotation_logPartition_hasDerivAt {n : ℕ} (β θ : ℝ)
    (p : Disorder n × Disorder n) (s : ℝ) :
    HasDerivAt (fun t => logPartition β (rotateDisorder (θ * t) p).1)
      (θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) s := by
  have hd : HasDerivAt (fun t => logPartition β (rotateDisorder t p).1)
      (directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) (θ * s) := by
    apply logPartition_hasDerivAt
    intro x
    simp only [rotateDisorder, hamiltonian_mix]
    exact ((Real.hasDerivAt_cos _).mul_const _).add
      ((Real.hasDerivAt_sin _).mul_const _)
  simpa only [Function.comp_def, mul_one, mul_comm] using
    hd.comp s ((hasDerivAt_id s).const_mul θ)

theorem continuous_rotation_path {n : ℕ} (θ : ℝ) (p : Disorder n × Disorder n) :
    Continuous (fun s : ℝ => rotateDisorder (θ * s) p) := by
  unfold rotateDisorder mixDisorder
  fun_prop

theorem continuous_rotation_energy {n : ℕ} (β θ : ℝ) (p : Disorder n × Disorder n) :
    Continuous (fun s : ℝ => directionalEnergy β (rotateDisorder (θ * s) p).1
      (rotateDisorder (θ * s) p).2) :=
  (continuous_directionalEnergy β).comp (continuous_rotation_path θ p)

theorem rotation_logPartition_integral {n : ℕ} (β θ : ℝ)
    (p : Disorder n × Disorder n) :
    logPartition β (rotateDisorder θ p).1 - logPartition β p.1 =
      ∫ s : ℝ in 0..1,
        θ * directionalEnergy β (rotateDisorder (θ * s) p).1
          (rotateDisorder (θ * s) p).2 := by
  have hc : Continuous (fun s : ℝ =>
      θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => rotation_logPartition_hasDerivAt β θ p s) (hc.intervalIntegrable 0 1)
  simpa only [mul_one, mul_zero, rotateDisorder, mixDisorder, Real.cos_zero,
    Real.sin_zero, zero_smul, one_smul, add_zero] using h.symm

theorem continuous_unitInterval_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f unitIntervalLaw :=
  hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

theorem unitInterval_integral (f : ℝ → ℝ) :
    (∫ s, f s ∂unitIntervalLaw) = ∫ s : ℝ in 0..1, f s := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

theorem rotation_exp_jensen {n : ℕ} (β θ ℓ : ℝ) (p : Disorder n × Disorder n) :
    Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)) ≤
      ∫ s, Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) ∂unitIntervalLaw := by
  have hc : Continuous (fun s : ℝ => ℓ * θ *
      directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _))
    (continuous_unitInterval_integrable hc)
    (continuous_unitInterval_integrable (Real.continuous_exp.comp hc))
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  rw [unitInterval_integral, rotation_logPartition_integral,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

theorem rotated_directionalEnergy_exp_integrable {n : ℕ} (β ℓ s : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2))
      (disorderPairLaw n) := by
  have hp := (rotateDisorder_law n s).measurePreserving (rotateDisorderCLM n s).continuous.measurable
  exact hp.integrable_comp_of_integrable (directionalEnergy_pair_exp_integrable β ℓ)

theorem rotated_directionalEnergy_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ s : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2)
        ∂disorderPairLaw n) ≤ Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hm : AEStronglyMeasurable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy (n := n) β))).aestronglyMeasurable
  have heq := (rotateDisorder_law n s).integral_comp (f := fun p =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) hm
  change (∫ p, ((fun q : Disorder n × Disorder n =>
    Real.exp (ℓ * directionalEnergy β q.1 q.2)) ∘ rotateDisorder s) p
      ∂disorderPairLaw n) ≤ _
  rw [heq]
  exact directionalEnergy_pair_exp_integral_le hn β ℓ

theorem continuous_rotationIntegrand {n : ℕ} (β θ ℓ : ℝ) :
    Continuous (Function.uncurry (rotationIntegrand (n := n) β θ ℓ)) := by
  have hm : Continuous (fun q : ℝ × (Disorder n × Disorder n) => (θ * q.1, q.2)) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hr := (continuous_rotateDisorder n).comp hm
  dsimp only [Function.comp_def] at hr
  have hd : Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
      directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
        (rotateDisorder (θ * q.1) q.2).2) :=
    (continuous_directionalEnergy (n := n) β).comp hr
  change Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
    Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
      (rotateDisorder (θ * q.1) q.2).2))
  exact Real.continuous_exp.comp (continuous_const.mul hd)

theorem rotationIntegrand_integrable {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) := by
  have hm : AEStronglyMeasurable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) :=
    (continuous_rotationIntegrand (n := n) β θ ℓ).aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · exact ae_of_all _ (fun s => rotated_directionalEnergy_exp_integrable β (ℓ * θ) (θ * s))
  · have hmeas := hm.norm.integral_prod_right'
    apply (integrable_const (Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4))).mono' hmeas
    filter_upwards [] with s
    have hn0 : 0 ≤ ∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n :=
      integral_nonneg (fun _ => norm_nonneg _)
    change |∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n| ≤ _
    rw [abs_of_nonneg hn0]
    simp only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s)

theorem rotation_exp_integrable {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
  have hright := (rotationIntegrand_integrable hn β θ ℓ).integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  apply hright.mono' hc.aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Function.uncurry_apply_pair, rotationIntegrand, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using
    rotation_exp_jensen β θ ℓ p

theorem rotation_exp_integral_le {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))
        ∂disorderPairLaw n) ≤
      Real.exp (ℓ ^ 2 * θ ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hf := rotationIntegrand_integrable hn β θ ℓ
  have hright : Integrable (fun p : Disorder n × Disorder n =>
      ∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) (disorderPairLaw n) :=
    hf.integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  have hleft : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
    apply hright.mono' hc.aestronglyMeasurable
    filter_upwards [] with p
    simpa only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using rotation_exp_jensen β θ ℓ p
  calc
    _ ≤ ∫ p, (∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) ∂disorderPairLaw n :=
      integral_mono hleft hright (rotation_exp_jensen β θ ℓ)
    _ = ∫ s, (∫ p, rotationIntegrand β θ ℓ s p ∂disorderPairLaw n) ∂unitIntervalLaw :=
      (integral_integral_swap hf).symm
    _ ≤ ∫ _s, Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂unitIntervalLaw :=
      integral_mono hf.integral_prod_left (integrable_const _)
        (fun s => rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s))
    _ = _ := by
      simp only [integral_const, probReal_univ, one_smul]
      congr 1
      ring

theorem logPartition_difference_exp_integrable {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β p.2 - logPartition β p.1))) (disorderPairLaw n) := by
  simpa only [rotateDisorder_pi_div_two_fst] using
    rotation_exp_integrable hn β (Real.pi / 2) ℓ

theorem logPartition_exp_integrable {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun J : Disorder n => Real.exp (ℓ * logPartition β J)) (disorderLaw n) := by
  have hp := logPartition_difference_exp_integrable hn β ℓ
  obtain ⟨J, hJ⟩ := hp.prod_right_ae.exists
  have hi := hJ.const_mul (Real.exp (ℓ * logPartition β J))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext K
  rw [← Real.exp_add]
  congr 1
  ring

theorem logPartition_integrable {n : ℕ} (hn : 0 < n) (β : ℝ) :
    Integrable (logPartition (n := n) β) (disorderLaw n) := by
  have hp := logPartition_exp_integrable hn β 1
  have hm := logPartition_exp_integrable hn β (-1)
  apply (hp.add hm).mono' (continuous_logPartition β).aestronglyMeasurable
  filter_upwards [] with J
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h := Real.add_one_le_exp (-logPartition β J)
    have he := Real.exp_pos (1 * logPartition β J)
    simp only [Pi.add_apply, one_mul, neg_one_mul] at *
    linarith
  · have h := Real.add_one_le_exp (logPartition β J)
    have he := Real.exp_pos (-1 * logPartition β J)
    simp only [Pi.add_apply, one_mul, neg_one_mul] at *
    linarith

theorem logPartition_centered_exp_jensen {n : ℕ} (hn : 0 < n) (β ℓ : ℝ)
    (J : Disorder n) :
    Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)) ≤
      ∫ K, Real.exp (ℓ * (logPartition β J - logPartition β K)) ∂disorderLaw n := by
  have hl : Integrable (fun K : Disorder n => ℓ * (logPartition β J - logPartition β K))
      (disorderLaw n) := ((integrable_const _).sub (logPartition_integrable hn β)).const_mul ℓ
  have he : Integrable (fun K : Disorder n =>
      Real.exp (ℓ * (logPartition β J - logPartition β K))) (disorderLaw n) := by
    have h := (logPartition_exp_integrable hn β (-ℓ)).const_mul
      (Real.exp (ℓ * logPartition β J))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext K
    rw [← Real.exp_add]
    congr 1
    ring
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _)) hl he
  convert hj using 2
  all_goals try with_reducible_and_instances rfl
  rw [integral_const_mul, integral_sub (integrable_const _) (logPartition_integrable hn β)]
  simp

theorem logPartition_centered_exp_integrable {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun J : Disorder n =>
      Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)))
      (disorderLaw n) := by
  have h := (logPartition_exp_integrable hn β ℓ).const_mul
    (Real.exp (-ℓ * ∫ K, logPartition β K ∂disorderLaw n))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext J
  rw [← Real.exp_add]
  congr 1
  ring

theorem logPartition_centered_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    (∫ J : Disorder n,
      Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)) ∂disorderLaw n) ≤
      Real.exp (ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 16) := by
  have hf : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β p.1 - logPartition β p.2))) (disorderPairLaw n) := by
    convert logPartition_difference_exp_integrable hn β (-ℓ) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    congr 1
    ring
  calc
    _ ≤ ∫ J, (∫ K, Real.exp (ℓ * (logPartition β J - logPartition β K)) ∂disorderLaw n)
        ∂disorderLaw n := integral_mono (logPartition_centered_exp_integrable hn β ℓ)
          hf.integral_prod_left (logPartition_centered_exp_jensen hn β ℓ)
    _ = ∫ p : Disorder n × Disorder n,
        Real.exp ((-ℓ) * (logPartition β (rotateDisorder (Real.pi / 2) p).1 -
          logPartition β p.1)) ∂disorderPairLaw n := by
      rw [← integral_prod _ hf]
      apply integral_congr_ae
      filter_upwards [] with p
      rw [rotateDisorder_pi_div_two_fst]
      congr 1
      ring
    _ ≤ Real.exp ((-ℓ) ^ 2 * (Real.pi / 2) ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) :=
      rotation_exp_integral_le hn β (Real.pi / 2) (-ℓ)
    _ = _ := by congr 1; ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_GaugeSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem logPartition_subGaussian {n : ℕ} (hn : 0 < n) (β : ℝ) :
    HasSubgaussianMGF
      (fun J : Disorder n => logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)
      (logPartitionProxy β n) (disorderLaw n) := by
  refine ⟨logPartition_centered_exp_integrable hn β, fun ℓ => ?_⟩
  apply (logPartition_centered_exp_integral_le hn β ℓ).trans
  apply Real.exp_le_exp.mpr
  change ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 16 ≤
    (Real.pi ^ 2 * β ^ 2 * (n : ℝ) / 8) * ℓ ^ 2 / 2
  have h : 0 ≤ ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 := by positivity
  nlinarith

theorem logPartition_lower_tail {n : ℕ} (hn : 0 < n) (β u : ℝ) (hu : 0 ≤ u) :
    (disorderLaw n).real {J | u ≤ (∫ K, logPartition β K ∂disorderLaw n) - logPartition β J} ≤
      Real.exp (-u ^ 2 / (2 * (logPartitionProxy β n : ℝ))) := by
  simpa only [Pi.neg_apply, neg_sub] using (logPartition_subGaussian hn β).neg.measure_ge_le hu

end SK

end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_EnergyTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem logPartition_lower_tail_linear {N : ℕ} (hN : 0 < N) {β a : ℝ}
    (hβ : β ≠ 0) (ha : 0 ≤ a) :
    (disorderLaw N).real {J | a*(N:ℝ) ≤
      (∫ K, logPartition β K ∂disorderLaw N)-logPartition β J} ≤
      Real.exp (-(4*a^2/(Real.pi^2*β^2))*(N:ℝ)) := by
  have H := logPartition_lower_tail hN β (a*(N:ℝ)) (by positivity)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  change -(4*a^2/(Real.pi^2*β^2))*(N:ℝ) =
    -(a*(N:ℝ))^2/(2*(Real.pi^2*β^2*(N:ℝ)/8))
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_SmoothFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic.SmoothFamily

theorem gibbs_nonneg {n : ℕ} [Model n] (β : ℝ) (J : Disorder n) (x : Config n) :
    0 ≤ gibbs β J x := Model.gibbs_nonneg β J x

theorem gibbs_sum {n : ℕ} [Model n] (β : ℝ) (J : Disorder n) :
    ∑ x, gibbs β J x = 1 := Model.gibbs_sum β J

theorem continuous_gibbs {n : ℕ} [Model n] (β : ℝ) (x : Config n) :
    Continuous (fun J : Disorder n => gibbs β J x) := Model.continuous_gibbs β x

theorem continuous_logPartition {n : ℕ} [Model n] (β : ℝ) :
    Continuous (logPartition (n := n) β) := Model.continuous_logPartition β

theorem directionalEnergy_exp_le {n : ℕ} [Model n] (β ℓ : ℝ) (J K : Disorder n) :
    Real.exp (ℓ * directionalEnergy β J K) ≤
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x) := by
  have h := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := gibbs β J) (p := fun x => ℓ * β * hamiltonian K x)
    (fun x _ => gibbs_nonneg β J x) (gibbs_sum β J)
    (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, ← Finset.mul_sum, directionalEnergy, mul_assoc,
    mul_left_comm (gibbs β J _)] using h

theorem gibbs_le_one {n : ℕ} [Model n] (β : ℝ) (J : Disorder n) (x : Config n) :
    gibbs β J x ≤ 1 := by
  rw [← gibbs_sum β J]
  exact Finset.single_le_sum (fun z _ => gibbs_nonneg β J z) (Finset.mem_univ x)

theorem gibbs_integrable {n : ℕ} [Model n] (β : ℝ) (x : Config n) :
    Integrable (fun J : Disorder n => gibbs β J x) (disorderLaw n) := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_gibbs β x).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs, abs_of_nonneg (gibbs_nonneg β J x)] using gibbs_le_one β J x

theorem continuous_directionalEnergy {n : ℕ} [Model n] (β : ℝ) :
    Continuous (fun p : Disorder n × Disorder n => directionalEnergy β p.1 p.2) := by
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun x _ =>
    ((continuous_gibbs β x).comp continuous_fst).mul
      ((continuous_hamiltonian x).comp continuous_snd))

theorem directionalEnergy_exp_integrable {n : ℕ} [Model n] (β ℓ : ℝ) (J : Disorder n) :
    Integrable (fun K : Disorder n => Real.exp (ℓ * directionalEnergy β J K))
      (disorderLaw n) := by
  have hsum : Integrable (fun K : Disorder n =>
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x))
      (disorderLaw n) :=
    integrable_finsetSum _ (fun x _ =>
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _)
  apply hsum.mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_directionalEnergy β).comp (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · filter_upwards [] with K
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ J K

theorem directionalEnergy_exp_integral_le {n : ℕ} [Model n] (hn : 0 < n)
    (β ℓ : ℝ) (J : Disorder n) :
    (∫ K : Disorder n, Real.exp (ℓ * directionalEnergy β J K) ∂disorderLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hsum (x : Config n) : Integrable (fun K : Disorder n =>
      gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) (disorderLaw n) :=
    (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _
  calc
    _ ≤ ∫ K : Disorder n, (∑ x : Config n,
        gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) ∂disorderLaw n :=
      integral_mono (directionalEnergy_exp_integrable β ℓ J)
        (integrable_finsetSum _ (fun x _ => hsum x)) (directionalEnergy_exp_le β ℓ J)
    _ = _ := by
      rw [integral_finsetSum _ (fun x _ => hsum x)]
      simp_rw [integral_const_mul, hamiltonian_exp_integral hn]
      rw [← Finset.sum_mul, gibbs_sum, one_mul]

theorem directionalEnergy_pair_exp_integrable {n : ℕ} [Model n] (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) := by
  have hsum : Integrable (fun p : Disorder n × Disorder n =>
      ∑ x : Config n, gibbs β p.1 x * Real.exp (ℓ * β * hamiltonian p.2 x))
      (disorderPairLaw n) := by
    apply integrable_finsetSum
    intro x _
    exact (gibbs_integrable β x).mul_prod
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β))
  apply hsum.mono'
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy β))).aestronglyMeasurable
  · filter_upwards [] with p
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ p.1 p.2

theorem directionalEnergy_pair_exp_integral_le {n : ℕ} [Model n] (hn : 0 < n) (β ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β p.1 p.2) ∂disorderPairLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  rw [disorderPairLaw, integral_prod _ (directionalEnergy_pair_exp_integrable β ℓ)]
  calc
    _ ≤ ∫ _J : Disorder n,
        Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂disorderLaw n :=
      integral_mono (directionalEnergy_pair_exp_integrable β ℓ).integral_prod_left
        (integrable_const _) (directionalEnergy_exp_integral_le hn β ℓ)
    _ = _ := by simp

theorem logPartition_hasDerivAt {n : ℕ} [Model n] (β : ℝ) (J : ℝ → Disorder n)
    (K : Disorder n) (s : ℝ)
    (hJ : ∀ x, HasDerivAt (fun t => hamiltonian (J t) x) (hamiltonian K x) s) :
    HasDerivAt (fun t => logPartition β (J t)) (directionalEnergy β (J s) K) s :=
  Model.hasDerivAt β J K s hJ

theorem rotation_logPartition_hasDerivAt {n : ℕ} [Model n] (β θ : ℝ)
    (p : Disorder n × Disorder n) (s : ℝ) :
    HasDerivAt (fun t => logPartition β (rotateDisorder (θ * t) p).1)
      (θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) s := by
  have hd : HasDerivAt (fun t => logPartition β (rotateDisorder t p).1)
      (directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) (θ * s) := by
    apply logPartition_hasDerivAt
    intro x
    simp only [rotateDisorder, hamiltonian_mix]
    exact ((Real.hasDerivAt_cos _).mul_const _).add
      ((Real.hasDerivAt_sin _).mul_const _)
  simpa only [Function.comp_def, mul_one, mul_comm] using
    hd.comp s ((hasDerivAt_id s).const_mul θ)

theorem continuous_rotation_energy {n : ℕ} [Model n] (β θ : ℝ) (p : Disorder n × Disorder n) :
    Continuous (fun s : ℝ => directionalEnergy β (rotateDisorder (θ * s) p).1
      (rotateDisorder (θ * s) p).2) :=
  (continuous_directionalEnergy β).comp (continuous_rotation_path θ p)

theorem rotation_logPartition_integral {n : ℕ} [Model n] (β θ : ℝ)
    (p : Disorder n × Disorder n) :
    logPartition β (rotateDisorder θ p).1 - logPartition β p.1 =
      ∫ s : ℝ in 0..1,
        θ * directionalEnergy β (rotateDisorder (θ * s) p).1
          (rotateDisorder (θ * s) p).2 := by
  have hc : Continuous (fun s : ℝ =>
      θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => rotation_logPartition_hasDerivAt β θ p s) (hc.intervalIntegrable 0 1)
  simpa only [mul_one, mul_zero, rotateDisorder, mixDisorder, Real.cos_zero,
    Real.sin_zero, zero_smul, one_smul, add_zero] using h.symm

theorem rotation_exp_jensen {n : ℕ} [Model n] (β θ ℓ : ℝ) (p : Disorder n × Disorder n) :
    Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)) ≤
      ∫ s, Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) ∂unitIntervalLaw := by
  have hc : Continuous (fun s : ℝ => ℓ * θ *
      directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _))
    (continuous_unitInterval_integrable hc)
    (continuous_unitInterval_integrable (Real.continuous_exp.comp hc))
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  rw [unitInterval_integral, rotation_logPartition_integral,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

theorem rotated_directionalEnergy_exp_integrable {n : ℕ} [Model n] (β ℓ s : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2))
      (disorderPairLaw n) := by
  have hp := (rotateDisorder_law n s).measurePreserving (rotateDisorderCLM n s).continuous.measurable
  exact hp.integrable_comp_of_integrable (directionalEnergy_pair_exp_integrable β ℓ)

theorem rotated_directionalEnergy_exp_integral_le {n : ℕ} [Model n] (hn : 0 < n) (β ℓ s : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2)
        ∂disorderPairLaw n) ≤ Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hm : AEStronglyMeasurable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy (n := n) β))).aestronglyMeasurable
  have heq := (rotateDisorder_law n s).integral_comp (f := fun p =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) hm
  change (∫ p, ((fun q : Disorder n × Disorder n =>
    Real.exp (ℓ * directionalEnergy β q.1 q.2)) ∘ rotateDisorder s) p
      ∂disorderPairLaw n) ≤ _
  rw [heq]
  exact directionalEnergy_pair_exp_integral_le hn β ℓ

theorem continuous_rotationIntegrand {n : ℕ} [Model n] (β θ ℓ : ℝ) :
    Continuous (Function.uncurry (rotationIntegrand (n := n) β θ ℓ)) := by
  have hm : Continuous (fun q : ℝ × (Disorder n × Disorder n) => (θ * q.1, q.2)) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hr := (continuous_rotateDisorder n).comp hm
  dsimp only [Function.comp_def] at hr
  have hd : Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
      directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
        (rotateDisorder (θ * q.1) q.2).2) :=
    (continuous_directionalEnergy (n := n) β).comp hr
  change Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
    Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
      (rotateDisorder (θ * q.1) q.2).2))
  exact Real.continuous_exp.comp (continuous_const.mul hd)

theorem rotationIntegrand_integrable {n : ℕ} [Model n] (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) := by
  have hm : AEStronglyMeasurable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) :=
    (continuous_rotationIntegrand (n := n) β θ ℓ).aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · exact ae_of_all _ (fun s => rotated_directionalEnergy_exp_integrable β (ℓ * θ) (θ * s))
  · have hmeas := hm.norm.integral_prod_right'
    apply (integrable_const (Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4))).mono' hmeas
    filter_upwards [] with s
    have hn0 : 0 ≤ ∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n :=
      integral_nonneg (fun _ => norm_nonneg _)
    change |∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n| ≤ _
    rw [abs_of_nonneg hn0]
    simp only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s)

theorem rotation_exp_integrable {n : ℕ} [Model n] (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
  have hright := (rotationIntegrand_integrable hn β θ ℓ).integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  apply hright.mono' hc.aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Function.uncurry_apply_pair, rotationIntegrand, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using
    rotation_exp_jensen β θ ℓ p

theorem rotation_exp_integral_le {n : ℕ} [Model n] (hn : 0 < n) (β θ ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))
        ∂disorderPairLaw n) ≤
      Real.exp (ℓ ^ 2 * θ ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hf := rotationIntegrand_integrable hn β θ ℓ
  have hright : Integrable (fun p : Disorder n × Disorder n =>
      ∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) (disorderPairLaw n) :=
    hf.integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  have hleft : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
    apply hright.mono' hc.aestronglyMeasurable
    filter_upwards [] with p
    simpa only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using rotation_exp_jensen β θ ℓ p
  calc
    _ ≤ ∫ p, (∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) ∂disorderPairLaw n :=
      integral_mono hleft hright (rotation_exp_jensen β θ ℓ)
    _ = ∫ s, (∫ p, rotationIntegrand β θ ℓ s p ∂disorderPairLaw n) ∂unitIntervalLaw :=
      (integral_integral_swap hf).symm
    _ ≤ ∫ _s, Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂unitIntervalLaw :=
      integral_mono hf.integral_prod_left (integrable_const _)
        (fun s => rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s))
    _ = _ := by
      simp only [integral_const, probReal_univ, one_smul]
      congr 1
      ring

theorem logPartition_difference_exp_integrable {n : ℕ} [Model n] (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β p.2 - logPartition β p.1))) (disorderPairLaw n) := by
  simpa only [rotateDisorder_pi_div_two_fst] using
    rotation_exp_integrable hn β (Real.pi / 2) ℓ

theorem logPartition_exp_integrable {n : ℕ} [Model n] (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun J : Disorder n => Real.exp (ℓ * logPartition β J)) (disorderLaw n) := by
  have hp := logPartition_difference_exp_integrable hn β ℓ
  obtain ⟨J, hJ⟩ := hp.prod_right_ae.exists
  have hi := hJ.const_mul (Real.exp (ℓ * logPartition β J))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext K
  rw [← Real.exp_add]
  congr 1
  ring

theorem logPartition_integrable {n : ℕ} [Model n] (hn : 0 < n) (β : ℝ) :
    Integrable (logPartition (n := n) β) (disorderLaw n) := by
  have hp := logPartition_exp_integrable hn β 1
  have hm := logPartition_exp_integrable hn β (-1)
  apply (hp.add hm).mono' (continuous_logPartition β).aestronglyMeasurable
  filter_upwards [] with J
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h := Real.add_one_le_exp (-logPartition β J)
    have he := Real.exp_pos (1 * logPartition β J)
    simp only [Pi.add_apply, one_mul, neg_one_mul] at *
    linarith
  · have h := Real.add_one_le_exp (logPartition β J)
    have he := Real.exp_pos (-1 * logPartition β J)
    simp only [Pi.add_apply, one_mul, neg_one_mul] at *
    linarith

theorem logPartition_centered_exp_jensen {n : ℕ} [Model n] (hn : 0 < n) (β ℓ : ℝ)
    (J : Disorder n) :
    Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)) ≤
      ∫ K, Real.exp (ℓ * (logPartition β J - logPartition β K)) ∂disorderLaw n := by
  have hl : Integrable (fun K : Disorder n => ℓ * (logPartition β J - logPartition β K))
      (disorderLaw n) := ((integrable_const _).sub (logPartition_integrable hn β)).const_mul ℓ
  have he : Integrable (fun K : Disorder n =>
      Real.exp (ℓ * (logPartition β J - logPartition β K))) (disorderLaw n) := by
    have h := (logPartition_exp_integrable hn β (-ℓ)).const_mul
      (Real.exp (ℓ * logPartition β J))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext K
    rw [← Real.exp_add]
    congr 1
    ring
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _)) hl he
  convert hj using 2
  all_goals try with_reducible_and_instances rfl
  rw [integral_const_mul, integral_sub (integrable_const _) (logPartition_integrable hn β)]
  simp

theorem logPartition_centered_exp_integrable {n : ℕ} [Model n] (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun J : Disorder n =>
      Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)))
      (disorderLaw n) := by
  have h := (logPartition_exp_integrable hn β ℓ).const_mul
    (Real.exp (-ℓ * ∫ K, logPartition β K ∂disorderLaw n))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext J
  rw [← Real.exp_add]
  congr 1
  ring

theorem logPartition_centered_exp_integral_le {n : ℕ} [Model n] (hn : 0 < n) (β ℓ : ℝ) :
    (∫ J : Disorder n,
      Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)) ∂disorderLaw n) ≤
      Real.exp (ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 16) := by
  have hf : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β p.1 - logPartition β p.2))) (disorderPairLaw n) := by
    convert logPartition_difference_exp_integrable hn β (-ℓ) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    congr 1
    ring
  calc
    _ ≤ ∫ J, (∫ K, Real.exp (ℓ * (logPartition β J - logPartition β K)) ∂disorderLaw n)
        ∂disorderLaw n := integral_mono (logPartition_centered_exp_integrable hn β ℓ)
          hf.integral_prod_left (logPartition_centered_exp_jensen hn β ℓ)
    _ = ∫ p : Disorder n × Disorder n,
        Real.exp ((-ℓ) * (logPartition β (rotateDisorder (Real.pi / 2) p).1 -
          logPartition β p.1)) ∂disorderPairLaw n := by
      rw [← integral_prod _ hf]
      apply integral_congr_ae
      filter_upwards [] with p
      rw [rotateDisorder_pi_div_two_fst]
      congr 1
      ring
    _ ≤ Real.exp ((-ℓ) ^ 2 * (Real.pi / 2) ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) :=
      rotation_exp_integral_le hn β (Real.pi / 2) (-ℓ)
    _ = _ := by congr 1; ring

theorem logPartition_subGaussian {n : ℕ} [Model n] (hn : 0 < n) (β : ℝ) :
    HasSubgaussianMGF
      (fun J : Disorder n => logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)
      (logPartitionProxy β n) (disorderLaw n) := by
  refine ⟨logPartition_centered_exp_integrable hn β, fun ℓ => ?_⟩
  apply (logPartition_centered_exp_integral_le hn β ℓ).trans
  apply Real.exp_le_exp.mpr
  change ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 16 ≤
    (Real.pi ^ 2 * β ^ 2 * (n : ℝ) / 8) * ℓ ^ 2 / 2
  have h : 0 ≤ ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 := by positivity
  nlinarith

end SK.Analytic.SmoothFamily

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_RestrictedConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem restrictedLogPartition_subGaussian {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (β : ℝ) {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty) :
    HasSubgaussianMGF (fun J : Disorder n => restrictedLogPartition β S J-
      ∫ K, restrictedLogPartition β S K ∂disorderLaw n)
      (logPartitionProxy (β*(d:ℝ)) n) (disorderLaw n) := by
  let inst : SmoothFamily.Model n := restrictedModel hd S hS
  have H := @SmoothFamily.logPartition_subGaussian n inst hn (β*(d:ℝ))
  change HasSubgaussianMGF (fun J => restrictedLogPartition ((β*(d:ℝ))/(d:ℝ)) S J-
    ∫ K, restrictedLogPartition ((β*(d:ℝ))/(d:ℝ)) S K ∂disorderLaw n)
    (logPartitionProxy (β*(d:ℝ)) n) (disorderLaw n) at H
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simpa only [mul_div_cancel_right₀ _ hd'] using H

theorem restrictedLogPartition_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (β : ℝ) {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty) :
    Integrable (restrictedLogPartition β S) (disorderLaw n) := by
  let inst : SmoothFamily.Model n := restrictedModel hd S hS
  have H := @SmoothFamily.logPartition_integrable n inst hn (β*(d:ℝ))
  change Integrable (restrictedLogPartition ((β*(d:ℝ))/(d:ℝ)) S) (disorderLaw n) at H
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simpa only [mul_div_cancel_right₀ _ hd'] using H

theorem restrictedLogPartition_upper_tail {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (β u : ℝ) {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty) (hu : 0 ≤ u) :
    (disorderLaw n).real {J | u ≤ restrictedLogPartition β S J-
      ∫ K, restrictedLogPartition β S K ∂disorderLaw n} ≤
      Real.exp (-u^2/(2*(logPartitionProxy (β*(d:ℝ)) n:ℝ))) :=
  (restrictedLogPartition_subGaussian hn hd β hS).measure_ge_le hu

theorem replicaGibbsMass_nonneg {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    0 ≤ replicaGibbsMass β J S :=
  Finset.sum_nonneg (fun s _ => Finset.prod_nonneg (fun a _ => (gibbs_pos β J (s a)).le))

theorem replicaGibbsMass_le_one {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J S ≤ 1 := by
  have H : replicaGibbsMass β J S ≤ ∑ s : ReplicaConfig n d, ∏ a, gibbs β J (s a) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun s _ _ => Finset.prod_nonneg (fun a _ => (gibbs_pos β J (s a)).le))
  rw [← Fintype.prod_sum] at H
  simpa only [gibbs_sum,Finset.prod_const_one] using H

theorem replicaGibbsMass_eq_ratio {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J S = restrictedPartition β S J/(partition β J)^d := by
  unfold replicaGibbsMass restrictedPartition
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  simp only [gibbs,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  rw [replicaEnergy,Finset.mul_sum,Real.exp_sum]

theorem replicaGibbsMass_eq_exp {n d : ℕ} (β : ℝ) (J : Disorder n) {S : Finset (ReplicaConfig n d)}
    (hS : S.Nonempty) : replicaGibbsMass β J S =
      Real.exp (restrictedLogPartition β S J-(d:ℝ)*logPartition β J) := by
  rw [replicaGibbsMass_eq_ratio,Real.exp_sub,Real.exp_nat_mul,restrictedLogPartition,logPartition,
    Real.exp_log (restrictedPartition_pos β hS J),Real.exp_log (partition_pos β J)]

theorem continuous_replicaGibbsMass {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) :
    Continuous (fun J : Disorder n => replicaGibbsMass β J S) := by
  apply continuous_finsetSum
  intro s _
  exact continuous_finsetProd _ (fun a _ => continuous_gibbs β (s a))

theorem replicaGibbsMass_integrable {n d : ℕ} (β : ℝ) (S : Finset (ReplicaConfig n d)) :
    Integrable (fun J : Disorder n => replicaGibbsMass β J S) (disorderLaw n) := by
  apply (integrable_const (1:ℝ)).mono' (continuous_replicaGibbsMass β S).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs,abs_of_nonneg (replicaGibbsMass_nonneg β J S)] using
    replicaGibbsMass_le_one β J S

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_PressureGapProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem integral_le_off_exception {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) {A : Set Ω} (hA : MeasurableSet A)
    {r : ℝ} (hr : 0 ≤ r) (h1 : ∀ x, f x ≤ 1)
    (hout : ∀ x ∉ A, f x ≤ r) : ∫ x, f x ∂μ ≤ r+μ.real A := by
  calc
    _ ≤ ∫ x, r+A.indicator (fun _ => (1:ℝ)) x ∂μ := by
      apply integral_mono hf ((integrable_const r).add ((integrable_const (1:ℝ)).indicator hA))
      intro x
      by_cases hx : x ∈ A
      · simp only [Pi.add_apply,Set.indicator_of_mem hx]
        linarith [h1 x]
      · simp only [Pi.add_apply,Set.indicator_of_notMem hx,add_zero]
        exact hout x hx
    _ = _ := by
      rw [integral_add (integrable_const r) ((integrable_const (1:ℝ)).indicator hA),
        integral_const,integral_indicator_const _ hA]
      simp only [probReal_univ,smul_eq_mul,mul_one,one_mul]

theorem restrictedLogPartition_upper_tail_linear {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {β a : ℝ} (hβ : β ≠ 0) (ha : 0 ≤ a)
    {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty) :
    (disorderLaw n).real {J | a*(n:ℝ) ≤ restrictedLogPartition β S J-
      ∫ K, restrictedLogPartition β S K ∂disorderLaw n} ≤
      Real.exp (-(4*a^2/(Real.pi^2*β^2*(d:ℝ)^2))*(n:ℝ)) := by
  have H := restrictedLogPartition_upper_tail hn hd β (a*(n:ℝ)) hS (by positivity)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  change -(4*a^2/(Real.pi^2*β^2*(d:ℝ)^2))*(n:ℝ) =
    -(a*(n:ℝ))^2/(2*(Real.pi^2*(β*(d:ℝ))^2*(n:ℝ)/8))
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

theorem replicaGibbsMass_integral_le_of_mean_gap {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {β η : ℝ} (hβ : β ≠ 0) (hη : 0 ≤ η)
    {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty)
    (hgap : (∫ J, restrictedLogPartition β S J ∂disorderLaw n)-
      (d:ℝ)*(∫ J, logPartition β J ∂disorderLaw n) ≤ -(n:ℝ)*η/2) :
    (∫ J, replicaGibbsMass β J S ∂disorderLaw n) ≤
      Real.exp (-(n:ℝ)*η/4)+2*Real.exp (-(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2)) := by
  let X := restrictedLogPartition β S
  let EX := ∫ J, X J ∂disorderLaw n
  let EY := ∫ J, logPartition β J ∂disorderLaw n
  let A : Set (Disorder n) := {J | (η/8)*(n:ℝ) ≤ X J-EX}
  let B : Set (Disorder n) := {J | (η/(8*(d:ℝ)))*(n:ℝ) ≤ EY-logPartition β J}
  have hA : MeasurableSet A := isClosed_le continuous_const
    ((continuous_restrictedLogPartition β hS).sub continuous_const) |>.measurableSet
  have hB : MeasurableSet B := isClosed_le continuous_const
    (continuous_const.sub (continuous_logPartition β)) |>.measurableSet
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd
  have hdn : (d:ℝ) ≠ 0 := ne_of_gt hd0
  have HA := restrictedLogPartition_upper_tail_linear hn hd hβ (show 0 ≤ η/8 by positivity) hS
  have HB := logPartition_lower_tail_linear hn hβ (show 0 ≤ η/(8*(d:ℝ)) by positivity)
  have heA : -(4*(η/8)^2/(Real.pi^2*β^2*(d:ℝ)^2))*(n:ℝ) =
      -(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2) := by ring
  have heB : -(4*(η/(8*(d:ℝ)))^2/(Real.pi^2*β^2))*(n:ℝ) =
      -(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2) := by field_simp; ring
  rw [heA] at HA
  rw [heB] at HB
  have H := integral_le_off_exception (replicaGibbsMass_integrable β S) (hA.union hB)
    (Real.exp_pos (-(n:ℝ)*η/4)).le (fun J => replicaGibbsMass_le_one β J S) ?_
  · have hAB : (disorderLaw n).real (A∪B) ≤
        2*Real.exp (-(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2)) := by
      apply (measureReal_union_le (μ := disorderLaw n) A B).trans
      change (disorderLaw n).real A ≤ _ at HA
      change (disorderLaw n).real B ≤ _ at HB
      linarith
    linarith
  · intro J hJ
    rw [Set.mem_union,not_or] at hJ
    have ha : X J-EX < (η/8)*(n:ℝ) := lt_of_not_ge hJ.1
    have hb : EY-logPartition β J < (η/(8*(d:ℝ)))*(n:ℝ) := lt_of_not_ge hJ.2
    have hb' := mul_lt_mul_of_pos_left hb hd0
    have he : (d:ℝ)*((η/(8*(d:ℝ)))*(n:ℝ)) = η*(n:ℝ)/8 := by field_simp
    rw [he] at hb'
    rw [replicaGibbsMass_eq_exp β J hS]
    apply Real.exp_le_exp.mpr
    change EX-(d:ℝ)*EY ≤ -(n:ℝ)*η/2 at hgap
    change restrictedLogPartition β S J-EX < _ at ha
    linarith

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_PressureGapFiniteInf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem replicaGibbsMass_integral_le_of_finiteInf_gap {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {β η e : ℝ} (hβ : β ≠ 0) (hη : 0 ≤ η)
    {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty)
    (hlower : finiteParisiInf β-e ≤ quenchedPressure β n)
    (herror : 2*(d:ℝ)*e ≤ η)
    (hpressure : restrictedPressure β S ≤ (d:ℝ)*finiteParisiInf β-η) :
    (∫ J, replicaGibbsMass β J S ∂disorderLaw n) ≤
      Real.exp (-(n:ℝ)*η/4)+2*Real.exp (-(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2)) := by
  apply replicaGibbsMass_integral_le_of_mean_gap hn hd hβ hη hS
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hd0 : 0 ≤ (d:ℝ) := by positivity
  have H := mul_le_mul_of_nonneg_left hlower hd0
  have HP : restrictedPressure β S-(d:ℝ)*quenchedPressure β n ≤ -η/2 := by linarith
  unfold restrictedPressure quenchedPressure at HP
  have HN := mul_le_mul_of_nonneg_right HP hn0.le
  have he : ((∫ J, restrictedLogPartition β S J ∂disorderLaw n)/(n:ℝ)-
      (d:ℝ)*((∫ J, logPartition β J ∂disorderLaw n)/(n:ℝ)))*(n:ℝ) =
      (∫ J, restrictedLogPartition β S J ∂disorderLaw n)-
      (d:ℝ)*(∫ J, logPartition β J ∂disorderLaw n) := by field_simp [ne_of_gt hn0]
  rw [he] at HN
  linarith

theorem eventual_replicaGibbsMass_pressure_gap {β : ℝ} (hβ : 0 < β) (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ (S : Finset (ReplicaConfig n d)) (η : ℝ),
      S.Nonempty → 0 ≤ η → 2*(d:ℝ)*C*(n:ℝ)^(-(1:ℝ)/24) ≤ η →
      restrictedPressure β S ≤ (d:ℝ)*finiteParisiInf β-η →
      (∫ J, replicaGibbsMass β J S ∂disorderLaw n) ≤
        Real.exp (-(n:ℝ)*η/4)+2*Real.exp (-(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2)) := by
  obtain ⟨C,hC,HC⟩ := quenchedPressure_quantitative_finiteInf hβ
  refine ⟨C,hC,?_⟩
  filter_upwards [HC,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro S η hS hη herr hpress
  apply replicaGibbsMass_integral_le_of_finiteInf_gap hn0 hd hβ.ne' hη hS hn.1 _ hpress
  simpa only [mul_assoc] using herr

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHierarchyAverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem BoundedScalar.add {g h : ℝ → ℝ} (hg : BoundedScalar g) (hh : BoundedScalar h) :
    BoundedScalar (fun x => g x+h x) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  obtain ⟨C,hC,hc⟩ := hh.bounded
  exact ⟨hg.continuous.add hh.continuous,B+C,add_nonneg hB hC,
    fun x => (abs_add_le _ _).trans (add_le_add (hb x) (hc x))⟩

theorem BoundedScalar.const_mul {g : ℝ → ℝ} (hg : BoundedScalar g) (c : ℝ) :
    BoundedScalar (fun x => c*g x) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  refine ⟨continuous_const.mul hg.continuous,|c| * B,mul_nonneg (abs_nonneg _) hB,fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

theorem BoundedScalar.sub {g h : ℝ → ℝ} (hg : BoundedScalar g) (hh : BoundedScalar h) :
    BoundedScalar (fun x => g x-h x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hg.add (hh.const_mul (-1))

theorem scalarHierarchyAverage_integrable {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    Integrable (fun z => g (x+coordinateLinear n v z))
      (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) := by
  obtain ⟨B,_,hb⟩ := hg.bounded
  apply hierarchyPathLaw_integrable n m _ _ ((hf.translate x).compCLM (coordinateLinear n v))
    (hg.continuous.comp (continuous_const.add (coordinateLinear n v).continuous))
  exact fun z => hb _

theorem scalarHierarchyAverage_integral {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f g x=
      ∫ z, g (x+coordinateLinear n v z) ∂hierarchyPathLaw n m
        (fun z => f (x+coordinateLinear n v z)) 0 := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  exact scalarHierarchyAverage_eq_integral n m v hf hg.continuous hB hb x

theorem scalarHierarchyAverage_sub {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hh : BoundedScalar h) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f (fun y => g y-h y) x=
      scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f h x := by
  rw [scalarHierarchyAverage_integral hf (hg.sub hh),scalarHierarchyAverage_integral hf hg,
    scalarHierarchyAverage_integral hf hh,integral_sub
    (scalarHierarchyAverage_integrable hf hg n m v x) (scalarHierarchyAverage_integrable hf hh n m v x)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_SmoothedObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarWindow_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (h x : ℝ) :
    HasDerivAt (scalarWindow g h) (scalarWindowDerivative g h x) x := by
  convert (((boundedPrimitive_hasDerivAt hg (x+h)).comp x
    ((hasDerivAt_id x).add_const h)).sub (boundedPrimitive_hasDerivAt hg x)).div_const h using 1 <;>
    first | rfl | exact Subsingleton.elim _ _ | simp only [scalarWindowDerivative,mul_one]

theorem scalarWindowDerivative_continuous {g : ℝ → ℝ} (hg : Continuous g) (h : ℝ) :
    Continuous (scalarWindowDerivative g h) :=
  ((hg.comp (continuous_id.add continuous_const)).sub hg).div_const h

theorem scalarWindow_bound {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindow g h x| ≤ B := by
  have H := (boundedPrimitive_lipschitz hg hB).dist_le_mul (x+h) x
  simp only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at H
  rw [scalarWindow,abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarWindowDerivative_bound {g : ℝ → ℝ} {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindowDerivative g h x| ≤ 2*(B:ℝ)/h := by
  rw [scalarWindowDerivative,abs_div,abs_of_pos hh]
  exact div_le_div_of_nonneg_right ((abs_sub (g (x+h)) (g x)).trans (by linarith [hB (x+h),hB x])) hh.le

theorem scalarWindow_integral {g : ℝ → ℝ} (hg : Continuous g) (h x : ℝ) :
    scalarWindow g h x=(∫ y in x..x+h, g y)/h := by
  have H := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ:=volume) 0 x) (hg.intervalIntegrable (μ:=volume) x (x+h))
  dsimp only [scalarWindow,boundedPrimitive]
  congr 1
  linarith

theorem scalarWindow_approx {g : ℝ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {h : ℝ} (hh : 0<h) (x : ℝ) : |scalarWindow g h x-g x| ≤ (L:ℝ)*h := by
  rw [scalarWindow_integral hg.continuous]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=x) (b:=x+h)
    (f:=fun y => g y-g x) (C:=(L:ℝ)*h) (by
      intro y hy
      rw [uIoc_of_le (by linarith)] at hy
      have H := hg.dist_le_mul y x
      simp only [Real.dist_eq] at H
      rw [abs_of_nonneg (show 0≤y-x by linarith [hy.1])] at H
      rw [Real.norm_eq_abs]
      exact H.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) L.coe_nonneg))
  rw [intervalIntegral.integral_sub (hg.continuous.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,Real.norm_eq_abs,
    abs_of_pos hh] at H
  rw [show (∫ y in x..x+h, g y)/h-g x=((∫ y in x..x+h, g y)-h*g x)/h by field_simp,
    abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarHierarchyAverage_observable_distance {f g a : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (ha : BoundedScalar a)
    {δ : ℝ} (_hδ : 0≤δ) (hga : ∀ z, |g z-a z| ≤ δ)
    (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    |scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f a x| ≤ δ := by
  rw [← scalarHierarchyAverage_sub hf hg ha,
    scalarHierarchyAverage_integral hf (hg.sub ha)]
  have : IsProbabilityMeasure (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  have H := norm_integral_le_of_norm_le_const (μ:=hierarchyPathLaw n m
    (fun z => f (x+coordinateLinear n v z)) 0) (f:=fun z => g (x+coordinateLinear n v z)-a (x+coordinateLinear n v z))
    (C:=δ) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hga (x+coordinateLinear n v z)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem dyadicScalarAverage_tendsto_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B L : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (hB : ∀ z, |g z| ≤ B) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  apply CauchySeq.tendsto_limUnder
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let h := ε/(4*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hh : 0<h := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*h ≤ ε/4 := by
    calc
      _ ≤ ((L:ℝ)+1)*h := mul_le_mul_of_nonneg_right (by linarith) hh.le
      _ = ε/4 := by dsimp [h]; field_simp
  let C : ℝ≥0 := ⟨2*(B:ℝ)/h,div_nonneg (by positivity) hh.le⟩
  have hW := dyadicScalarAverage_tendsto_C1 β hα hmono hf
    (scalarWindow_hasDerivAt hgL.continuous h) (scalarWindowDerivative_continuous hgL.continuous h)
    hfK (scalarWindow_bound hgL.continuous hB hh) (C:=C)
    (scalarWindowDerivative_bound hB hh) s t ht x
  have hc := Metric.cauchySeq_iff.mp hW.cauchySeq (ε/4) (by positivity)
  obtain ⟨N,hN⟩ := hc
  refine ⟨N,fun m hm n hn => ?_⟩
  have he (j : ℕ) : |dyadicScalarAverage β α j s t f g x-
      dyadicScalarAverage β α j s t f (scalarWindow g h) x| ≤ ε/4 := by
    apply (scalarHierarchyAverage_observable_distance hf
      ⟨hgL.continuous,B,B.coe_nonneg,hB⟩
      ⟨continuous_iff_continuousAt.mpr (fun z => (scalarWindow_hasDerivAt hgL.continuous h z).continuousAt),
        B,B.coe_nonneg,scalarWindow_bound hgL.continuous hB hh⟩
      (mul_nonneg L.coe_nonneg hh.le) (fun z => ?_) _ _ _ x).trans hsmall
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hh z
  have hd := hN m hm n hn
  simp only [Real.dist_eq] at hd ⊢
  have H₁ := abs_sub_le (dyadicScalarAverage β α m s t f g x)
    (dyadicScalarAverage β α m s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f g x)
  have H₂ := abs_sub_le (dyadicScalarAverage β α m s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f g x)
  rw [abs_sub_comm (dyadicScalarAverage β α n s t f (scalarWindow g h) x)] at H₂
  linarith [he m,he n]

theorem scalarCDFAverage_observable_distance (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B C L M : ℝ≥0} (hfK : LipschitzWith K f)
    (hgL : LipschitzWith L g) (haM : LipschitzWith M a)
    (hB : ∀ z, |g z| ≤ B) (hC : ∀ z, |a z| ≤ C)
    {δ : ℝ} (hδ : 0≤δ) (hga : ∀ z, |g z-a z| ≤ δ)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β α s t f a x| ≤ δ := by
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK hgL hB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK haM hC s t ht x)).abs
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_observable_distance hf
    ⟨hgL.continuous,B,B.coe_nonneg,hB⟩ ⟨haM.continuous,C,C.coe_nonneg,hC⟩ hδ hga _ _ _ x)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzChainRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarWindowDerivative_lipschitz_bound {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindowDerivative g h x| ≤ L := by
  have H := hg.dist_le_mul (x+h) x
  simp only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at H
  rw [scalarWindowDerivative,abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarWindow_lipschitz {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {h : ℝ} (hh : 0<h) : LipschitzWith L (scalarWindow g h) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarWindow_hasDerivAt hg.continuous h x).differentiableAt)
  intro x
  rw [(scalarWindow_hasDerivAt hg.continuous h x).deriv]
  exact_mod_cast scalarWindowDerivative_lipschitz_bound hg hh x

theorem scalarCDFAverage_eq_chainAverage_lipschitz {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) {K B L : ℝ≥0} (hfK : LipschitzWith K f)
    (hgL : LipschitzWith L g) (hB : ∀ z, |g z| ≤ B)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hdur : chainDuration l=t)
    (hmodel : TimeChainModels α s l) (x : ℝ) :
    scalarCDFAverage β α s t f g x=scalarTimeChainAverage β l f g x := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm ?_ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  let h := ε/(2*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hh : 0<h := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*h ≤ ε/2 := by
    calc
      _ ≤ ((L:ℝ)+1)*h := mul_le_mul_of_nonneg_right (by linarith) hh.le
      _ = ε/2 := by dsimp [h]; field_simp
  have hd (z) : |g z-scalarWindow g h z| ≤ (L:ℝ)*h := by
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hh z
  have H₁ := scalarCDFAverage_observable_distance β hα hmono hf hfK hgL
    (scalarWindow_lipschitz hgL hh) hB (scalarWindow_bound hgL.continuous hB hh)
    (mul_nonneg L.coe_nonneg hh.le) hd s t ht x
  have H₂ := scalarHierarchyAverage_observable_distance hf
    ⟨hgL.continuous,B,B.coe_nonneg,hB⟩
    ⟨(scalarWindow_lipschitz hgL hh).continuous,B,B.coe_nonneg,scalarWindow_bound hgL.continuous hB hh⟩
    (mul_nonneg L.coe_nonneg hh.le) hd l.length (fun i => (l.get i).1)
    (fun i => β*Real.sqrt ((l.get i).2:ℝ)) x
  change |scalarTimeChainAverage β l f g x-scalarTimeChainAverage β l f (scalarWindow g h) x|≤_ at H₂
  have HE := scalarCDFAverage_eq_chainAverage hf
    (scalarWindow_hasDerivAt hgL.continuous h) (scalarWindowDerivative_continuous hgL.continuous h)
    hfK (scalarWindow_bound hgL.continuous hB hh) (scalarWindowDerivative_lipschitz_bound hgL hh)
    β hα hmono l hm s t ht hdur hmodel x
  rw [HE] at H₁
  have H := abs_sub_le (scalarCDFAverage β α s t f g x)
    (scalarTimeChainAverage β l f (scalarWindow g h) x) (scalarTimeChainAverage β l f g x)
  rw [abs_sub_comm (scalarTimeChainAverage β l f (scalarWindow g h) x)] at H
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzCDFStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_cdf_stability_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z∈Icc (0:ℝ) 1) (hγm : Monotone γ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β γ s t f g x| ≤
      2*(scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))/h+
        2*((L:ℝ)+2*(B:ℝ)^2)*h := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let d := ε/(2*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hd : 0<d := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*d ≤ ε/2 := by
    calc
      _ ≤ ((L:ℝ)+1)*d := mul_le_mul_of_nonneg_right (by linarith) hd.le
      _ = ε/2 := by dsimp [d]; field_simp
  have hga (z) : |g z-scalarWindow g d z| ≤ (L:ℝ)*d := by
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hd z
  have Hα := scalarCDFAverage_observable_distance β hα hαm hf hfK hgL
    (scalarWindow_lipschitz hgL hd) hB (scalarWindow_bound hgL.continuous hB hd)
    (mul_nonneg L.coe_nonneg hd.le) hga s t ht x
  have Hγ := scalarCDFAverage_observable_distance β hγ hγm hf hfK hgL
    (scalarWindow_lipschitz hgL hd) hB (scalarWindow_bound hgL.continuous hB hd)
    (mul_nonneg L.coe_nonneg hd.le) hga s t ht x
  have Hc := scalarCDFAverage_cdf_stability_C1 β hα hαm hγ hγm hf
    (scalarWindow_hasDerivAt hgL.continuous d) (scalarWindowDerivative_continuous hgL.continuous d)
    hfK (scalarWindow_bound hgL.continuous hB hd) (scalarWindowDerivative_lipschitz_bound hgL hd)
    s t ht x h hh
  have H₁ := abs_sub_le (scalarCDFAverage β α s t f g x)
    (scalarCDFAverage β α s t f (scalarWindow g d) x) (scalarCDFAverage β γ s t f g x)
  have H₂ := abs_sub_le (scalarCDFAverage β α s t f (scalarWindow g d) x)
    (scalarCDFAverage β γ s t f (scalarWindow g d) x) (scalarCDFAverage β γ s t f g x)
  rw [abs_sub_comm (scalarCDFAverage β γ s t f (scalarWindow g d) x)] at H₂
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzTerminalStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_terminal_stability_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a b : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {K L B A C : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (haA : LipschitzWith A a) (hbC : LipschitzWith C b)
    (haB : ∀ z, |a z| ≤ B) (hbB : ∀ z, |b z| ≤ B)
    {ε δ : ℝ} (hε : 0≤ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    (hab : ∀ z, |a z-b z| ≤ δ) (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f a x-scalarCDFAverage β α s t g b x| ≤
      δ+2*(B:ℝ)*(Real.exp (2*ε)-1) := by
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK haA haB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hmono hg hgL hbC hbB s t ht x)).abs
  apply Eventually.of_forall
  intro n
  apply scalarHierarchyAverage_terminal_stability _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _))
    (fun i j hij => ?_) hf hg hε hfg haA.continuous hbC.continuous B.coe_nonneg haB hbB hab x
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact List.pairwise_iff_get.mp (dyadicIntervals_pairwise hmono n s t) i j hij
  · exact le_rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_PolynomialTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem eventually_const_rpow_le {a b : ℝ} (hab : a<b) (A : ℝ) {B : ℝ} (hB : 0<B) :
    ∀ᶠ n : ℕ in atTop,A*(n:ℝ)^a ≤ B*(n:ℝ)^b := by
  have H := ((tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul A
  have H0 : Tendsto (fun n : ℕ => A*(n:ℝ)^(a-b)) atTop (𝓝 0) := by
    simpa only [neg_sub,mul_zero,Function.comp_apply] using H
  filter_upwards [H0.eventually_le_const hB,eventually_gt_atTop (0:ℕ)] with n hn hn0
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  rw [Real.rpow_sub hp] at hn
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hp b)).mp (by simpa only [mul_div_assoc] using hn)

theorem polynomial_rpow_exp_decay {u c : ℝ} (hu : 0<u) (hc : 0 < c) (d : ℕ) :
    Tendsto (fun n : ℕ => (n:ℝ)^d*Real.exp (-c*(n:ℝ)^u)) atTop (𝓝 0) := by
  have H := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((d:ℝ)/u) c hc).comp
    ((tendsto_rpow_atTop hu).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hp.le,mul_div_cancel₀ _ (ne_of_gt hu),Real.rpow_natCast]

theorem eventual_polynomial_stretched_tail {t u c ε : ℝ} (htu : t<u) (hu : 0<u)
    (hc : 0 < c) (hε : 0<ε) (K : ℝ) (hK : 0≤K) (d : ℕ) :
    ∀ᶠ n : ℕ in atTop,K*((n:ℝ)+1)^d*Real.exp (-c*(n:ℝ)^u) ≤ ε*Real.exp (-(n:ℝ)^t) := by
  have H := (polynomial_rpow_exp_decay hu (half_pos hc) d).const_mul (K*2^d)
  have H0 : Tendsto (fun n : ℕ => (K*2^d)*((n:ℝ)^d*Real.exp (-(c/2)*(n:ℝ)^u))) atTop (𝓝 0) := by
    simpa only [mul_zero] using H
  filter_upwards [eventually_const_rpow_le htu 1 (half_pos hc),
    H0.eventually_le_const hε,eventually_ge_atTop (1:ℕ)] with n hn hsmall hn1
  have hnp : 0≤(n:ℝ) := Nat.cast_nonneg n
  have hn1' : (1:ℝ)≤n := by exact_mod_cast hn1
  have hpow : ((n:ℝ)+1)^d≤2^d*(n:ℝ)^d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hfactor : K*((n:ℝ)+1)^d*Real.exp (-(c/2)*(n:ℝ)^u) ≤ ε :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) (Real.exp_pos _).le).trans
      (by nlinarith only [hsmall])
  have he : Real.exp (-(c/2)*(n:ℝ)^u)≤Real.exp (-(n:ℝ)^t) := by
    apply Real.exp_le_exp.mpr
    linarith only [hn]
  calc
    _ = (K*((n:ℝ)+1)^d*Real.exp (-(c/2)*(n:ℝ)^u))*Real.exp (-(c/2)*(n:ℝ)^u) := by
      rw [mul_assoc (K*((n:ℝ)+1)^d),← Real.exp_add]
      congr 2
      ring
    _ ≤ ε*Real.exp (-(n:ℝ)^t) := mul_le_mul hfactor he (Real.exp_pos _).le hε.le

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixReplicaBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem matrixReplicaSet_nonempty_iff {n d : ℕ} (D : Fin d → Fin d → ℝ) :
    (matrixReplicaSet n d D).Nonempty ↔ Nonempty (MatrixStates n d D) := by
  rw [← Finset.nonempty_coe_sort]
  exact (matrixReplicaEquiv n d D).nonempty_congr.symm

theorem restrictedPressure_matrixReplicaSet (n d : ℕ) (β : ℝ) (D : Fin d → Fin d → ℝ) :
    restrictedPressure β (matrixReplicaSet n d D)=matrixConstrainedPressure n d β D := by
  classical
  unfold restrictedPressure matrixConstrainedPressure
  congr 1
  apply integral_congr_ae
  filter_upwards [] with J
  unfold restrictedLogPartition restrictedPartition replicaEnergy
  congr 1
  rw [← Finset.sum_coe_sort]
  exact ((matrixReplicaEquiv n d D).sum_comp (fun s => Real.exp (β*∑ a,hamiltonian J (s.val a)))).symm

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixMassUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem restrictedPressure_mono {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (β : ℝ)
    {S T : Finset (ReplicaConfig n d)} (hS : S.Nonempty) (hST : S ⊆ T) :
    restrictedPressure β S ≤ restrictedPressure β T := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply integral_mono (restrictedLogPartition_integrable hn hd β hS)
    (restrictedLogPartition_integrable hn hd β (hS.mono hST))
  intro J
  apply Real.log_le_log (restrictedPartition_pos β hS J)
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun s _ _ => (Real.exp_pos _).le)

theorem replicaGibbsMass_integral_code_union {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (β : ℝ) {C : Type} [Fintype C] (code : ReplicaConfig n d → C)
    (hcode : ∀ s t,code s=code t → replicaGram s=replicaGram t)
    (S : Finset (ReplicaConfig n d)) (η E : ℝ) (hE : 0 ≤ E)
    (hgap : ∀ s∈S,matrixConstrainedPressure n d β (replicaGram s) ≤ (d:ℝ)*finiteParisiInf β-η)
    (hprob : ∀ T : Finset (ReplicaConfig n d),T.Nonempty →
      restrictedPressure β T ≤ (d:ℝ)*finiteParisiInf β-η →
      (∫ J,replicaGibbsMass β J T ∂disorderLaw n) ≤ E) :
    (∫ J,replicaGibbsMass β J S ∂disorderLaw n) ≤ (Fintype.card C:ℝ)*E := by
  classical
  let T (c : C) := S.filter (fun s => code s=c)
  have he (J : Disorder n) : replicaGibbsMass β J S=∑ c,replicaGibbsMass β J (T c) := by
    exact (Finset.sum_fiberwise S code (fun s => ∏ a,gibbs β J (s a))).symm
  simp_rw [he]
  rw [integral_finsetSum _ (fun c _ => replicaGibbsMass_integrable β (T c))]
  calc
    _ ≤ ∑ _c : C,E := by
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : (T c).Nonempty
      · obtain ⟨s,hs⟩ := hc
        have hs' := Finset.mem_filter.mp hs
        have hsub : T c ⊆ matrixReplicaSet n d (replicaGram s) := by
          intro t ht
          apply (mem_matrixReplicaSet _ _).mpr
          exact hcode t s ((Finset.mem_filter.mp ht).2.trans hs'.2.symm)
        apply hprob (T c) ⟨s,hs⟩
        exact (restrictedPressure_mono hn hd β ⟨s,hs⟩ hsub).trans
          (by rw [restrictedPressure_matrixReplicaSet]; exact hgap s hs'.1)
      · have ht : T c=∅ := Finset.not_nonempty_iff_eq_empty.mp hc
        simpa only [ht,replicaGibbsMass,Finset.sum_empty,integral_zero] using hE
    _ = _ := by simp

theorem eventual_replicaGibbsMass_code_gap {β : ℝ} (hβ : 0 < β) (d : ℕ) (hd : 0 < d) :
    ∃ K : ℝ,0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ (C : Type) [Fintype C]
      (code : ReplicaConfig n d → C),
      (∀ s t,code s=code t → replicaGram s=replicaGram t) →
      ∀ (S : Finset (ReplicaConfig n d)) (η : ℝ), 0 ≤ η →
      2*(d:ℝ)*K*(n:ℝ)^(-(1:ℝ)/24) ≤ η →
      (∀ s∈S,matrixConstrainedPressure n d β (replicaGram s) ≤ (d:ℝ)*finiteParisiInf β-η) →
      (∫ J,replicaGibbsMass β J S ∂disorderLaw n) ≤ (Fintype.card C:ℝ)*
        (Real.exp (-(n:ℝ)*η/4)+2*Real.exp (-(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2))) := by
  obtain ⟨K,hK,H⟩ := eventual_replicaGibbsMass_pressure_gap hβ d hd
  refine ⟨K,hK,?_⟩
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro C _ code hcode S η hη herr hgap
  exact replicaGibbsMass_integral_code_union hn0 hd β code hcode S η _ (by positivity)
    hgap (fun T hT hP => hn T η hT hη herr hP)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_PolynomialGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem eventual_replicaGibbsMass_polynomial_gap {β c a t ε : ℝ} (hβ : 0<β)
    (d p : ℕ) (hd : 0<d) (hc : 0 < c) (ha : 0≤a) (ha24 : a<1/24)
    (ht : t<1-2*a) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (C : Type) [Fintype C],Fintype.card C≤(n+1)^p →
      ∀ (code : ReplicaConfig n d → C),
      (∀ s t,code s=code t → replicaGram s=replicaGram t) →
      ∀ (S : Finset (ReplicaConfig n d)),
      (∀ s∈S,matrixConstrainedPressure n d β (replicaGram s)≤
        (d:ℝ)*finiteParisiInf β-c*(n:ℝ)^(-a)) →
      (∫ J,replicaGibbsMass β J S ∂disorderLaw n)≤ε*Real.exp (-(n:ℝ)^t) := by
  obtain ⟨K,hK,H⟩ := eventual_replicaGibbsMass_code_gap hβ d hd
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have htail₁ := eventual_polynomial_stretched_tail (by linarith : t<1-a)
    (by linarith : 0<1-a) (by positivity : 0 < c/4) (half_pos hε) 1 (by norm_num) p
  have htail₂ := eventual_polynomial_stretched_tail ht (by linarith : 0<1-2*a)
    (by positivity : 0 < c^2/(16*Real.pi^2*β^2*(d:ℝ)^2)) (half_pos hε) 2 (by norm_num) p
  filter_upwards [H,eventually_const_rpow_le (by linarith : -(1:ℝ)/24 < -a) (2*(d:ℝ)*K) hc,
    htail₁,htail₂,eventually_gt_atTop (0:ℕ)] with n hn herr ht₁ ht₂ hn0
  intro C _ hcard code hcode S hgap
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  have he₁ : -(n:ℝ)*(c*(n:ℝ)^(-a))/4=-(c/4)*(n:ℝ)^(1-a) := by
    rw [Real.rpow_sub hp,Real.rpow_one,Real.rpow_neg hp.le]
    ring
  have he₂ : -(n:ℝ)*(c*(n:ℝ)^(-a))^2/(16*Real.pi^2*β^2*(d:ℝ)^2)=
      -(c^2/(16*Real.pi^2*β^2*(d:ℝ)^2))*(n:ℝ)^(1-2*a) := by
    rw [mul_pow,← Real.rpow_natCast ((n:ℝ)^(-a)) 2,← Real.rpow_mul hp.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-a)*(2:ℝ)= -(2*a) by ring,Real.rpow_neg hp.le,
      Real.rpow_sub hp,Real.rpow_one]
    ring
  have HM := hn C code hcode S (c*(n:ℝ)^(-a)) (by positivity) herr hgap
  rw [he₁,he₂] at HM
  have hcard' : (Fintype.card C:ℝ)≤((n:ℝ)+1)^p := by exact_mod_cast hcard
  have HH := HM.trans (mul_le_mul_of_nonneg_right hcard' (by positivity))
  simp only [one_mul] at ht₁
  nlinarith only [HH,ht₁,ht₂]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_CommonBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem vectorStep_real (m v : ℝ) (f : ℝ → ℝ) : vectorStep m v f=scalarStep m v f := by
  simp only [vectorStep,scalarStep,smul_eq_mul,mul_comm]

theorem vectorStepAverage_real (m v : ℝ) (f g : ℝ → ℝ) : vectorStepAverage m v f g=scalarStepAverage m v f g := by
  funext x
  simp only [vectorStepAverage,scalarStepAverage,gaussianAverage,gaussianStepLaw,smul_eq_mul,mul_comm]

theorem vectorHierarchyAverage_real (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    vectorHierarchyAverage n m v f g=scalarHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => rw [vectorHierarchyAverage,vectorStep_real,vectorStepAverage_real,ih]; rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_VectorBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorIncrementChain_append (l r : List (ℝ × E)) (f : E → ℝ) :
    vectorIncrementChain (l++r) f=vectorIncrementChain l (vectorIncrementChain r f) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,vectorIncrementChain,ih]

theorem vectorIncrementAverage_append (l r : List (ℝ × E)) (f g : E → ℝ) :
    vectorIncrementAverage (l++r) f g=
      vectorIncrementAverage l (vectorIncrementChain r f) (vectorIncrementAverage r f g) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,vectorIncrementAverage,vectorIncrementChain_append,ih]

theorem vectorIncrementAverage_ofFn (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E) (f g : E → ℝ) :
    vectorIncrementAverage (List.ofFn (fun i => (m i,v i))) f g=vectorHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => simp [vectorIncrementAverage,vectorHierarchyAverage]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,vectorIncrementAverage_append]
    exact ih _ _ _ _

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

section Penalty
variable {E : Type} [AddCommMonoid E]

theorem chainPotentialPenalty_append (F : E → ℝ) (l r : List (ℝ × E)) (Q : E) :
    chainPotentialPenalty F (l++r) Q=chainPotentialPenalty F l Q+
      chainPotentialPenalty F r (Q+chainSum l) := by
  induction l generalizing Q with
  | nil => simp [chainPotentialPenalty]
  | cons p l ih => simp only [List.cons_append,chainPotentialPenalty,ih,chainSum_cons,add_assoc]

end Penalty

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleTailValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem vectorIncrementChain_real (l : List (ℝ × ℝ)) (f : ℝ → ℝ) :
    vectorIncrementChain l f=scalarIncrementChain l f := by
  induction l with
  | nil => rfl
  | cons p l ih => rw [vectorIncrementChain,scalarIncrementChain,ih,vectorStep_real]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_IncrementListAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem vectorIncrementAverage_real (l : List (ℝ × ℝ)) (f g : ℝ → ℝ) :
    vectorIncrementAverage l f g=scalarIncrementAverage l f g := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [vectorIncrementAverage,scalarIncrementAverage,vectorIncrementChain_real,ih,vectorStepAverage_real]

theorem scalarIncrementAverage_ofFn (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    scalarIncrementAverage (List.ofFn (fun i => (m i,v i))) f g=scalarHierarchyAverage n m v f g := by
  rw [← vectorIncrementAverage_real,vectorIncrementAverage_ofFn,vectorHierarchyAverage_real]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScheduleScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SK.Analytic

theorem weightedUnderlying_scale (β : ℝ) (w : List (ℝ × (ℝ × ℝ))) :
    weightedUnderlying (scaleIncrementChain β w)=scaleIncrementChain β (weightedUnderlying w) := by
  simp only [weightedUnderlying,scaleIncrementChain,List.map_map,Function.comp_def,Prod.smul_fst]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_ConstantWeightStats
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem constantWeightChain_penalty (κ : ℝ) (l : List (ℝ × ℝ)) (q : ℝ) :
    weightedCrossPenalty (constantWeightChain κ l) (κ*q)=κ^2*rawPenalty l q := by
  induction l generalizing q with
  | nil => simp [weightedCrossPenalty,rawPenalty,constantWeightChain,chainPotentialPenalty]
  | cons p l ih =>
    change p.1*((κ*q+p.2*(κ*p.2))^2-(κ*q)^2)+weightedCrossPenalty (constantWeightChain κ l) (κ*q+p.2*(κ*p.2))=
      κ^2*(p.1*((q+p.2^2)^2-q^2)+rawPenalty l (q+p.2^2))
    rw [show κ*q+p.2*(κ*p.2)=κ*(q+p.2^2) by ring,ih]
    ring

@[simp] theorem constantWeightChain_penalty_zero (κ : ℝ) (l : List (ℝ × ℝ)) :
    weightedCrossPenalty (constantWeightChain κ l) 0=κ^2*rawPenalty l 0 := by
  simpa only [mul_zero] using constantWeightChain_penalty κ l 0

theorem rawPenalty_bounds (l : List (ℝ × ℝ)) {a b q : ℝ}
    (hm : ∀ p∈l,p.1∈Icc a b) (hq : 0 ≤ q) :
    rawPenalty l q∈Icc (a*((q+rawVariance l)^2-q^2)) (b*((q+rawVariance l)^2-q^2)) := by
  induction l generalizing q with
  | nil => simp [rawPenalty,rawVariance,chainPotentialPenalty]
  | cons p l ih =>
    have hp := hm p (List.mem_cons_self ..)
    have H := ih (fun z hz => hm z (List.mem_cons_of_mem _ hz)) (q:=q+p.2^2) (by positivity)
    have hΔ : 0 ≤ (q+p.2^2)^2-q^2 := by nlinarith [sq_nonneg p.2]
    change p.1*((q+p.2^2)^2-q^2)+rawPenalty l (q+p.2^2)∈
      Icc (a*((q+(p.2^2+rawVariance l))^2-q^2)) (b*((q+(p.2^2+rawVariance l))^2-q^2))
    constructor
    · have H' := add_le_add (mul_le_mul_of_nonneg_right hp.1 hΔ) H.1
      convert H' using 1
      all_goals try with_reducible_and_instances rfl
      ring
    · have H' := add_le_add (mul_le_mul_of_nonneg_right hp.2 hΔ) H.2
      convert H' using 1
      all_goals try with_reducible_and_instances rfl
      ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_ListPrefixVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem scalarPrefixVariance_append_cut {A : Type} (l r : List A) (f : A → ℝ) :
    scalarPrefixVariance (l++r).length (fun i => f ((l++r).get i))
      ⟨l.length,by simp only [List.length_append]; omega⟩=(l.map (fun p => (f p)^2)).sum := by
  induction l with
  | nil => simp [scalarPrefixVariance,scalarPrefixVector]
  | cons p l ih =>
    unfold scalarPrefixVariance scalarPrefixVector at *
    change (∑ i : Fin ((l++r).length+1), (if i.val<l.length+1 then f (((p::l)++r).get i) else 0)^2)=_
    rw [Fin.sum_univ_succ]
    simp only [List.cons_append,List.get_eq_getElem,Fin.val_zero,Fin.val_succ,List.getElem_cons_zero,
      List.getElem_cons_succ,Nat.zero_lt_succ,ite_true,Nat.add_lt_add_iff_right,List.map_cons,List.sum_cons]
    rw [← ih]
    rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainExactPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem TimeChainModels.area {α : ℝ → ℝ} (hα : Monotone α) {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) : (l.map (fun p => p.1*(p.2:ℝ))).sum=∫ x in s..s+chainDuration l,α x := by
  induction l generalizing s with
  | nil => simp [chainDuration]
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    have hcell : (∫ x in s..s+d,α x)=m*(d:ℝ) := by
      rw [intervalIntegral.integral_congr_Ioo_of_le (le_add_of_nonneg_right d.coe_nonneg)
        (show (Ioo s (s+d)).EqOn α (fun _ => m) from fun x hx => hc x ⟨hx.1.le,hx.2⟩),intervalIntegral.integral_const]
      simp only [add_sub_cancel_left,smul_eq_mul,mul_comm]
    simp only [List.map_cons,List.sum_cons,chainDuration_cons,NNReal.coe_add]
    rw [ih ht,← add_assoc,← intervalIntegral.integral_add_adjacent_intervals
      (hα.intervalIntegrable (a:=s) (b:=s+d)) (hα.intervalIntegrable (a:=s+d) (b:=s+d+chainDuration l)),hcell]

theorem TimeChainModels.quadraticPenalty {α : ℝ → ℝ} (hα : Monotone α) {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) : chainQuadraticPenalty s l=2*∫ x in s..s+chainDuration l,x*α x := by
  have hi (a b : ℝ) : IntervalIntegrable (fun x => x*α x) volume a b :=
    hα.intervalIntegrable.continuousOn_mul continuous_id.continuousOn
  induction l generalizing s with
  | nil => simp [chainQuadraticPenalty,chainDuration]
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    have hcell : (∫ x in s..s+d,x*α x)=m*((s+d)^2-s^2)/2 := by
      rw [intervalIntegral.integral_congr_Ioo_of_le (le_add_of_nonneg_right d.coe_nonneg)
        (show (Ioo s (s+d)).EqOn (fun x => x*α x) (fun x => x*m) from
          fun x hx => congrArg (fun y : ℝ => x*y) (hc x ⟨hx.1.le,hx.2⟩)),intervalIntegral.integral_mul_const,integral_id]
      ring
    simp only [chainQuadraticPenalty,chainDuration_cons,NNReal.coe_add]
    rw [ih ht,← add_assoc,← intervalIntegral.integral_add_adjacent_intervals (hi s (s+d)) (hi (s+d) (s+d+chainDuration l)),hcell]
    ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeIncrementBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem rawTimeChain_mass (l : List (ℝ × ℝ≥0)) {P : ℝ → Prop} (hm : ∀ p∈l,P p.1) :
    ∀ p∈rawTimeChain l,P p.1 := by
  intro p hp; obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp; exact hm q hq

theorem rawTimeChain_sorted (l : List (ℝ × ℝ≥0)) (hs : l.Pairwise (fun p q => p.1≤q.1)) :
    (rawTimeChain l).Pairwise (fun p q => p.1≤q.1) := by
  simpa only [rawTimeChain,List.pairwise_map] using hs

theorem scalarIncrementChain_rawTimeChain (β : ℝ) (l : List (ℝ × ℝ≥0)) (f : ℝ → ℝ) :
    scalarIncrementChain (scaleIncrementChain β (rawTimeChain l)) f=scalarTimeChain β l f := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change scalarStep p.1 (β*Real.sqrt (p.2:ℝ)) (scalarIncrementChain (scaleIncrementChain β (rawTimeChain l)) f)=_
    rw [ih]
    rfl

theorem scalarIncrementAverage_rawTimeChain (β : ℝ) (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarIncrementAverage (scaleIncrementChain β (rawTimeChain l)) f g=scalarTimeChainAverage β l f g := by
  have he : scaleIncrementChain β (rawTimeChain l)=List.ofFn (fun i : Fin l.length => ((l.get i).1,β*Real.sqrt ((l.get i).2:ℝ))) := by
    simp only [scaleIncrementChain,rawTimeChain,List.map_map]
    conv_lhs => rw [← List.ofFn_get l,List.map_ofFn]
    rfl
  rw [he,scalarIncrementAverage_ofFn]
  rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantile_knots_gap (k : ℕ) (Q : Fin (k+1) → ℝ) (i : Fin (k+1)) :
    Fin.cons (α := fun _ => ℝ) 0 Q i.succ-Fin.cons (α := fun _ => ℝ) 0 Q i.castSucc=cumulativeGapMap k Q i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · rfl

theorem quantile_prefix_chain {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) :
    ∃ l : List (ℝ × ℝ≥0),
      (chainDuration l:ℝ)=Q (Fin.last k) ∧
      (∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) ∧
      TimeChainModels (quantileCDF k Q) 0 l ∧
      ∀ β f, scalarTimeChain β l f=scalarHierarchy (k+1) (quantileMass k)
        (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) f := by
  let q := Fin.cons (α := fun _ => ℝ) 0 Q
  let hq := monotone_cons_zero_quantiles Q hQ h0
  let l := partitionTimeChain (k+1) q hq (quantileMass k)
  refine ⟨l,?_,?_,?_,?_⟩
  · have H := partitionTimeChain_duration (k+1) q hq (quantileMass k)
    simpa only [q,← Fin.succ_last,Fin.cons_succ,Fin.cons_zero,sub_zero] using H
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    change quantileMass k i ∈ Icc (0:ℝ) 1
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
      exact_mod_cast i.isLt.le
  · change TimeChainModels (quantileCDF k Q) (q 0) (partitionTimeChain (k+1) q hq (quantileMass k))
    apply partitionTimeChain_models
    intro i z hz
    exact quantileCDF_on_interval Q hQ i z hz
  · intro β f
    dsimp only [l,partitionTimeChain]
    rw [scalarTimeChain_ofFn]
    congr 2
    funext i
    simp only [NNReal.coe_mk, q]
    rw [quantile_knots_gap]
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFAtomicRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantile_full_chain {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) (h1 : Q (Fin.last k) ≤ 1) :
    ∃ l : List (ℝ × ℝ≥0), chainDuration l=1 ∧
      (∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) ∧ TimeChainModels (quantileCDF k Q) 0 l ∧
      ∀ β, scalarTimeChain β l scalarSpinTerminal 0=atomicScalarValue k β Q := by
  obtain ⟨l,hd,hm,hmodel,he⟩ := quantile_prefix_chain Q hQ h0
  let t := NNReal.mk (1-Q (Fin.last k)) (sub_nonneg.mpr h1)
  refine ⟨l++[(1,t)],?_,?_,?_,?_⟩
  · apply NNReal.coe_injective
    simp only [chainDuration_append,chainDuration_cons,chainDuration_nil,add_zero,
      NNReal.coe_add,hd,t,NNReal.coe_mk,NNReal.coe_one]
    ring
  · intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · exact hm p hp
    · have hp' := List.mem_singleton.mp hp
      subst p
      exact ⟨zero_le_one,le_rfl⟩
  · apply hmodel.append
    constructor
    · intro z hz
      apply quantileCDF_of_last_le Q hQ
      simpa only [zero_add,hd] using hz.1
    · trivial
  · intro β
    rw [scalarTimeChain_append]
    simp only [scalarTimeChain]
    rw [he]
    rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFDerivativeConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem uniform_derivative_convergence {F D : ℕ → ℝ → ℝ} {f d : ℝ → ℝ} (K : ℝ≥0)
    (hD : ∀ n x, HasDerivAt (F n) (D n x) x) (hd : ∀ x, HasDerivAt f (d x) x)
    (hLip : ∀ n, LipschitzWith K (D n)) (hlip : LipschitzWith K d)
    (hF : TendstoUniformly F f atTop) : TendstoUniformly D d atTop := by
  rw [Metric.tendstoUniformly_iff] at hF ⊢
  intro ε hε
  let h : ℝ := ε/(8*((K:ℝ)+1))
  have hh : 0<h := div_pos hε (by positivity)
  have hke : 8*((K:ℝ)+1)*h=ε := by dsimp [h]; field_simp
  let δ : ℝ := ε*h/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [hF δ hδ] with n hn x
  have hb (z : ℝ) : |F n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hn z).le
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (K+K) δ
    (fun z => (hD n z).sub (hd z)) ((hLip n).sub hlip) hb x h hh
  have he : 2*δ/h=ε/4 := by dsimp [δ]; field_simp; ring
  rw [he,NNReal.coe_add] at H
  rw [Real.dist_eq,abs_sub_comm]
  have hk := K.coe_nonneg
  nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSuffixSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantile_suffix_chain {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    ∃ l : List (ℝ × ℝ≥0), chainDuration l=Real.toNNReal (1-s) ∧
      (∀ p∈l, p.1∈Icc (0:ℝ) 1) ∧ TimeChainModels (quantileCDF k Q) s l := by
  obtain ⟨l,hd,hm,hmodel,_⟩ := quantile_full_chain Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2
  have he : chainDuration l=Real.toNNReal s+Real.toNNReal (1-s) := by
    rw [hd]
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal s hs.1,Real.coe_toNNReal (1-s) (sub_nonneg.mpr hs.2),NNReal.coe_one]
    ring
  obtain ⟨_,l₂,_,h₂,_,hm₂,_,hs₂,_⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm 0 hmodel _ _ he
  exact ⟨l₂,h₂,hm₂,by simpa only [zero_add,Real.coe_toNNReal s hs.1] using hs₂⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PositiveTimeChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem positiveTimeChain_mem {l : List (ℝ × ℝ≥0)} {p : ℝ × ℝ≥0} (hp : p∈positiveTimeChain l) :
    p∈l ∧ 0<p.2 := by
  simpa only [positiveTimeChain,List.mem_filter,decide_eq_true_eq,ne_eq,pos_iff_ne_zero] using hp

theorem TimeChainModels.positiveTimeChain {α : ℝ → ℝ} {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) : TimeChainModels α s (positiveTimeChain l) := by
  induction l generalizing s with
  | nil => trivial
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    by_cases hd : d=0
    · simpa [SK.Analytic.positiveTimeChain,hd] using ih ht
    · simp only [SK.Analytic.positiveTimeChain,List.filter_cons,hd,ne_eq,not_false_eq_true,decide_true,ite_true]
      exact ⟨hc,ih ht⟩

theorem TimeChainModels.sorted {α : ℝ → ℝ} (hα : Monotone α) {s : ℝ} {l : List (ℝ × ℝ≥0)}
    (hl : TimeChainModels α s l) (hpos : ∀ p∈l,0<p.2) : l.Pairwise (fun p q => p.1≤q.1) := by
  induction l generalizing s with
  | nil => simp
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    obtain ⟨hc,ht⟩ := hl
    have hd : 0<(d:ℝ) := hpos (m,d) (List.mem_cons_self ..)
    have he : α s=m := hc s ⟨le_rfl,by linarith⟩
    apply List.pairwise_cons.mpr
    constructor
    · intro q hq
      rw [← he]
      exact (hα (le_add_of_nonneg_right d.coe_nonneg)).trans
        (ht.mass_bounds hα hq (hpos q (List.mem_cons_of_mem _ hq))).1
    · exact ih ht (fun q hq => hpos q (List.mem_cons_of_mem _ hq))

theorem quantile_interval_chain {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    ∃ l : List (ℝ × ℝ≥0), (chainDuration l:ℝ)=t-s ∧
      (∀ p∈l,p.1∈Icc (0:ℝ) 1) ∧ (∀ p∈l,0<p.2) ∧ TimeChainModels (quantileCDF k Q) s l := by
  obtain ⟨l,hd,hm,hmodel⟩ := quantile_suffix_chain β Q hQ ⟨hs,hst.trans ht⟩
  have hsplit : chainDuration l=Real.toNNReal (t-s)+Real.toNNReal (1-t) := by
    rw [hd]
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith)]
    ring
  obtain ⟨l₁,_,hd₁,_,hm₁,_,hmodel₁,_,_⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm s hmodel _ _ hsplit
  refine ⟨positiveTimeChain l₁,?_,fun p hp => hm₁ p (positiveTimeChain_mem hp).1,
    fun p hp => (positiveTimeChain_mem hp).2,hmodel₁.positiveTimeChain⟩
  rw [chainDuration_positiveTimeChain,hd₁,Real.coe_toNNReal _ (sub_nonneg.mpr hst)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem TimeChainOn.sorted {α : ℝ → ℝ} (hα : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    l.chain.Pairwise (fun p q => p.1≤q.1) := l.models.sorted hα l.positive

theorem TimeChainOn.raw_mass {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) :
    ∀ p∈rawTimeChain l.chain,p.1∈Icc (0:ℝ) 1 := rawTimeChain_mass _ l.mass

theorem TimeChainOn.raw_sorted {α : ℝ → ℝ} (hα : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    (rawTimeChain l.chain).Pairwise (fun p q => p.1≤q.1) := rawTimeChain_sorted _ (l.sorted hα)

theorem TimeChainOn.raw_mass_lower {α : ℝ → ℝ} (hα : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    ∀ p∈rawTimeChain l.chain,α s ≤ p.1 := by
  apply rawTimeChain_mass
  intro p hp
  exact (l.models.mass_bounds hα hp (l.positive p hp)).1

theorem exists_quantile_TimeChainOn {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    Nonempty (TimeChainOn (quantileCDF k Q) s t) := by
  obtain ⟨l,hd,hm,hp,hmodel⟩ := quantile_interval_chain β Q hQ hs hst ht
  exact ⟨⟨l,hd,hm,hp,hmodel⟩⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFCramer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarCDFValue_rootGradient (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    rootGradient 0 (scalarCDFValue β α s t)=scalarCDFGradient β α s t := by
  funext x
  exact ((scalarCDFValue_regular β ha hm s t ht).1.differentiable (by norm_num) x |>.hasDerivAt).unique
    (scalarCDFValue_hasDerivAt β ha hm s t ht x)

theorem scalarCDFValue_rootHessian (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    rootHessian 0 (scalarCDFValue β α s t)=scalarCDFHessian β α s t := by
  funext x
  have H : HasDerivAt (rootGradient 0 (scalarCDFValue β α s t))
      (rootHessian 0 (scalarCDFValue β α s t) x) x := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using
      rootGradientLine_hasDerivAt 0 (scalarCDFValue_regular β ha hm s t ht) 0 x
  rw [scalarCDFValue_rootGradient β ha hm s t ht] at H
  exact H.unique (scalarCDFGradient_hasDerivAt β ha hm s t ht x)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainOnAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem TimeChainOn.sub_nonneg {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) : 0 ≤ t-s := by
  rw [← l.duration]; positivity

theorem TimeChainOn.nn_duration {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) :
    chainDuration l.chain=Real.toNNReal (t-s) := by
  apply NNReal.coe_injective
  rw [l.duration,Real.coe_toNNReal _ l.sub_nonneg]

theorem TimeChainOn.nn_le_one {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) (h : t-s≤1) :
    Real.toNNReal (t-s)≤1 := by
  rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ l.sub_nonneg,NNReal.coe_one]; exact h

theorem TimeChainOn.scalar_operator (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) {f : ℝ → ℝ} (hf : BoundedDerivs f) {K : ℝ≥0} (hfK : LipschitzWith K f) :
    scalarIncrementChain (scaleIncrementChain β (rawTimeChain l.chain)) f=
      scalarCDFOperator β α s (Real.toNNReal (t-s)) f := by
  rw [scalarIncrementChain_rawTimeChain]
  funext x
  exact (scalarCDFOperator_eq_chain hf hfK β ha hm l.chain l.mass s _ (l.nn_le_one h) l.nn_duration l.models x).symm

theorem TimeChainOn.scalar_value (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) :
    scalarIncrementChain (scaleIncrementChain β (rawTimeChain l.chain)) scalarSpinTerminal=
      scalarCDFValue β α s (Real.toNNReal (t-s)) :=
  l.scalar_operator β ha hm h scalarSpinTerminal_regular scalarSpinTerminal_lipschitz

theorem TimeChainOn.scalar_hessian (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) :
    rootHessian 0 (scalarIncrementChain (scaleIncrementChain β (rawTimeChain l.chain)) scalarSpinTerminal)=
      scalarCDFHessian β α s (Real.toNNReal (t-s)) := by
  rw [l.scalar_value β ha hm h,scalarCDFValue_rootHessian β ha hm s _ (l.nn_le_one h)]

theorem TimeChainOn.scalar_average (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t)
    (h : t-s≤1) {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z,|g z|≤B) :
    scalarIncrementAverage (scaleIncrementChain β (rawTimeChain l.chain)) f g=
      scalarCDFAverage β α s (Real.toNNReal (t-s)) f g := by
  rw [scalarIncrementAverage_rawTimeChain]
  funext x
  exact (scalarCDFAverage_eq_chainAverage_lipschitz hf hfK hgL hB β ha hm l.chain l.mass s _
    (l.nn_le_one h) l.nn_duration l.models x).symm

theorem TimeChainOn.scalar_susceptibility (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) {q : ℝ} (hq : q∈Icc (0:ℝ) 1)
    (l : TimeChainOn α 0 q) (r : TimeChainOn α q 1) :
    scalarIncrementAverage (scaleIncrementChain β (rawTimeChain l.chain))
      (scalarIncrementChain (scaleIncrementChain β (rawTimeChain r.chain)) scalarSpinTerminal)
      (rootHessian 0 (scalarIncrementChain (scaleIncrementChain β (rawTimeChain r.chain)) scalarSpinTerminal)) 0=
      scalarCDFSusceptibilityAverage β α q := by
  have h : 1-q≤1 := by linarith [hq.1]
  rw [r.scalar_hessian β ha hm h,r.scalar_value β ha hm h]
  rw [l.scalar_average β ha hm (by linarith [hq.2])
    (scalarCDFValue_regular β ha hm q _ (r.nn_le_one h))
    (scalarCDFValue_lipschitz β ha hm q _ (r.nn_le_one h))
    (scalarCDFHessian_lipschitz β ha hm q _ (r.nn_le_one h))
    (B:=1) (scalarCDFHessian_abs_le_one β ha hm q _ (r.nn_le_one h))]
  simp only [sub_zero,scalarCDFSusceptibilityAverage]

theorem TimeChainOn.area {α : ℝ → ℝ} (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    rawArea (rawTimeChain l.chain)=∫ x in s..t,α x := by
  rw [rawArea_rawTimeChain,l.models.area hm,l.duration,add_sub_cancel]

theorem TimeChainOn.penalty {α : ℝ → ℝ} (hm : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    rawPenalty (rawTimeChain l.chain) s=2*∫ x in s..t,x*α x := by
  rw [rawPenalty_rawTimeChain,l.models.quadraticPenalty hm,l.duration,add_sub_cancel]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarResponseBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarPrefixVariance_monotone (n : ℕ) (v : Fin n → ℝ) :
    Monotone (scalarPrefixVariance n v) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k _
  unfold scalarPrefixVector
  by_cases h : k.val < i.val
  · rw [ite_eq_left h,ite_eq_left (lt_of_lt_of_le h hij)]
  · rw [ite_eq_right h,zero_pow (by norm_num : 2≠0)]
    exact sq_nonneg _

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedAugment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem weightedCrossPenalty_append (l r : List (ℝ × (ℝ × ℝ))) (g : ℝ) :
    weightedCrossPenalty (l++r) g=weightedCrossPenalty l g+weightedCrossPenalty r (g+weightedCross l) := by
  simp only [weightedCrossPenalty,List.map_append,chainPotentialPenalty_append,chainSum,
    List.map_map,weightedCross,Function.comp_def]

@[simp] theorem weightedCrossPenalty_full (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    weightedCrossPenalty (zeroWeightChain c++w++zeroWeightChain t) 0=weightedCrossPenalty w 0 := by
  simp [weightedCrossPenalty_append]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedBlockFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem blockWeights_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (c a t : List (ℝ × ℝ)) :
    ∀ i, 0 ≤ blockWeights κ c a t i := by
  intro i
  unfold blockWeights
  split_ifs <;> positivity

theorem blockWeights_factor (κ : ℝ) (c a t : List (ℝ × ℝ)) :
    ∀ i, ((zeroWeightChain c++constantWeightChain κ a++zeroWeightChain t).get i).2.2=
      blockWeights κ c a t i*((zeroWeightChain c++constantWeightChain κ a++zeroWeightChain t).get i).2.1 := by
  intro i
  simp only [List.get_eq_getElem]
  have hi := i.isLt
  simp only [List.length_append,zeroWeightChain,constantWeightChain,List.length_map] at hi
  by_cases h0 : i.val < c.length
  · have h01 : i.val < c.length+a.length := by omega
    simp only [blockWeights,zero_mul,zeroWeightChain,constantWeightChain,
      List.getElem_append,List.length_append,List.length_map,h01,h0,dite_true,List.getElem_map,ite_true,zero_mul]
  · by_cases h1 : i.val < c.length+a.length
    · simp only [blockWeights,zeroWeightChain,constantWeightChain,
        List.getElem_append,List.length_append,List.length_map,h1,h0,dite_true,dite_false,List.getElem_map,ite_true,ite_false]
    · simp only [blockWeights,zero_mul,zeroWeightChain,constantWeightChain,
        List.getElem_append,List.length_append,List.length_map,h1,h0,dite_false,List.getElem_map,ite_false,zero_mul]

theorem blockWeights_active (κ : ℝ) (c a t : List (ℝ × ℝ)) :
    ∀ i,blockWeights κ c a t i≠0 →
      scalarPrefixVariance (zeroWeightChain c++constantWeightChain κ a++zeroWeightChain t).length
        (fun j => ((zeroWeightChain c++constantWeightChain κ a++zeroWeightChain t).get j).2.1) i.castSucc ≤
      rawVariance (c++a) := by
  intro i hi
  have hcut : i.val < c.length+a.length := by
    by_contra h
    have h' : ¬i.val < c.length := by omega
    simp only [blockWeights,ite_eq_right h',ite_eq_right h] at hi
    exact hi rfl
  let l := zeroWeightChain c++constantWeightChain κ a
  let r := zeroWeightChain t
  have hlen : l.length=c.length+a.length := by simp [l,zeroWeightChain,constantWeightChain]
  have Hcut := scalarPrefixVariance_append_cut l r (fun p => p.2.1)
  have H := scalarPrefixVariance_monotone (l++r).length (fun j => ((l++r).get j).2.1)
    (show i.castSucc≤(⟨l.length,by simp only [List.length_append]; omega⟩ : Fin ((l++r).length+1)) by
      change i.val≤l.length; rw [hlen]; omega)
  rw [Hcut] at H
  have he : (l.map (fun p => p.2.1^2)).sum=rawVariance (c++a) := by
    have heu : weightedUnderlying l=c++a := by
      change weightedUnderlying (zeroWeightChain c++constantWeightChain κ a)=_
      rw [weightedUnderlying_append,weightedUnderlying_zeroWeight,constantWeightChain_underlying]
    rw [← heu]
    simp only [rawVariance,weightedUnderlying,List.map_map,Function.comp_def]
  exact H.trans_eq he

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem abs_overlap_le_one {n : ℕ} (x y : Config n) : |overlap x y| ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [overlap]
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold overlap
  rw [abs_div,abs_of_pos hnpos]
  apply (div_le_one hnpos).mpr
  calc
    _ ≤ ∑ i : Fin n, |spin (x i)*spin (y i)| := Finset.abs_sum_le_sum_abs _ _
    _ = (n:ℝ) := by
      have hs (i : Fin n) : |spin (x i)*spin (y i)| = 1 := by
        cases hx : x i <;> cases hy : y i <;> norm_num [spin]
      simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic

@[simp] theorem overlap_orient_abs {n : ℕ} (ε : Bool) (x y : Config n) :
    |overlap (orient ε x) y|=|overlap x y| := by
  cases ε
  · simp [orient]
  · change |overlap (flip x) y| = |overlap x y|
    rw [overlap_comm,overlap_flip_right,abs_neg,overlap_comm]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFIntervalConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFValue_tendstoUniformly_interval (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFValue β (αn n) s t)
      (scalarCDFValue β α s t) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have HT : Tendsto (fun n => scalarTimeMassConstant β*cdfDistance (αn n) α) atTop (𝓝 0) := by
    simpa only [mul_zero] using hD.const_mul (scalarTimeMassConstant β)
  filter_upwards [(tendsto_order.mp HT).2 ε hε] with n hn' x
  have H := scalarCDFValue_cdf_lipschitz β (hn n) (hnm n) hα hαm s t ht x
  have HE := cdfDistance_subinterval_le (hnm n) hαm hs hst
  have HB := H.trans (mul_le_mul_of_nonneg_left HE (scalarTimeMassConstant_nonneg β))
  rw [Real.dist_eq,abs_sub_comm]
  exact HB.trans_lt hn'

theorem scalarCDFHessian_tendstoUniformly_interval (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFHessian β (αn n) s t)
      (scalarCDFHessian β α s t) atTop := by
  apply uniform_derivative_convergence susceptibilityLipschitzConstant
    (fun n x => scalarCDFGradient_hasDerivAt β (hn n) (hnm n) s t ht x)
    (scalarCDFGradient_hasDerivAt β hα hαm s t ht)
    (fun n => scalarCDFHessian_lipschitz β (hn n) (hnm n) s t ht)
    (scalarCDFHessian_lipschitz β hα hαm s t ht)
  exact uniform_derivative_convergence 1
    (fun n x => scalarCDFValue_hasDerivAt β (hn n) (hnm n) s t ht x)
    (scalarCDFValue_hasDerivAt β hα hαm s t ht)
    (fun n => scalarCDFGradient_lipschitz β (hn n) (hnm n) s t ht)
    (scalarCDFGradient_lipschitz β hα hαm s t ht)
    (scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD s t ht hs hst)

theorem scalarCDFAverage_tendsto_cdf_lipschitz (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) (x : ℝ) :
    Tendsto (fun n => scalarCDFAverage β (αn n) s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A : ℝ := 2*((L:ℝ)+2*(B:ℝ)^2)
  have hA : 0≤A := by dsimp [A]; positivity
  let h : ℝ := ε/(4*(A+1))
  have hh : 0<h := by dsimp [h]; positivity
  have hsmall : A*h<ε := by
    have HE : 4*(A+1)*h=ε := by dsimp [h]; field_simp
    nlinarith
  have HT : Tendsto (fun n =>
      2*(scalarTimeMassConstantK β (K+B+B)*cdfDistance (αn n) α)/h+A*h) atTop (𝓝 (A*h)) := by
    simpa only [mul_zero,zero_div,zero_add] using
      (((hD.const_mul (scalarTimeMassConstantK β (K+B+B))).const_mul 2).div_const h).add_const (A*h)
  filter_upwards [(tendsto_order.mp HT).2 ε hsmall] with n hbound
  rw [Real.dist_eq]
  have H := scalarCDFAverage_cdf_stability_lipschitz β (hn n) (hnm n) hα hαm
    hf hfK hgL hB s t ht x h hh
  have HD := cdfDistance_subinterval_le (hnm n) hαm hs hst
  apply (H.trans ?_).trans_lt hbound
  exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left HD (scalarTimeMassConstantK_nonneg β _)) (by norm_num : (0:ℝ)≤2)) hh.le) le_rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFParisiContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdfPenalty_integrable {α : ℝ → ℝ} (hαm : Monotone α) :
    IntegrableOn (fun s => s*α s) (Icc (0:ℝ) 1) :=
  IntegrableOn.continuousOn_mul continuousOn_id (MonotoneOn.integrableOn_isCompact isCompact_Icc (hαm.monotoneOn _)) isCompact_Icc

theorem cdfPenalty_lipschitz {α γ : ℝ → ℝ} (hαm : Monotone α) (hγm : Monotone γ) :
    |(∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s)| ≤
      ∫ s in Icc (0:ℝ) 1, |α s-γ s| := by
  rw [← integral_sub (cdfPenalty_integrable hαm) (cdfPenalty_integrable hγm)]
  calc
    _ ≤ ∫ s in Icc (0:ℝ) 1, |s*α s-s*γ s| := abs_integral_le_integral_abs
    _ ≤ _ := setIntegral_mono_on ((cdfPenalty_integrable hαm).sub (cdfPenalty_integrable hγm)).abs
      ((MonotoneOn.integrableOn_isCompact isCompact_Icc (hαm.monotoneOn _)).sub (MonotoneOn.integrableOn_isCompact isCompact_Icc (hγm.monotoneOn _))).abs measurableSet_Icc (by
        intro s hs
        rw [← mul_sub,abs_mul,abs_of_nonneg hs.1]
        exact mul_le_of_le_one_left (abs_nonneg _) hs.2)

theorem scalarCDFParisi_cdf_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ) :
    |scalarCDFParisi β α-scalarCDFParisi β γ| ≤
      (scalarTimeMassConstant β+β^2/2)*(∫ s in Icc (0:ℝ) 1, |α s-γ s|) := by
  have H := scalarCDFValue_cdf_lipschitz β hα hαm hγ hγm 0 1 le_rfl 0
  simp only [NNReal.coe_one,zero_add,intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] at H
  unfold scalarCDFParisi
  calc
    _ = |(scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0)-
        (β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))| := by congr 1; ring
    _ ≤ |scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0|+
        (β^2/2)*|(∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s)| := by
      calc
        _ ≤ |scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0|+
            |(β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))| := by
          simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le
            (scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0) 0
            ((β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))))
        _ = _ := by rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ β^2/2)]
    _ ≤ scalarTimeMassConstant β*(∫ s in Icc (0:ℝ) 1, |α s-γ s|)+
        (β^2/2)*(∫ s in Icc (0:ℝ) 1, |α s-γ s|) :=
      add_le_add H (mul_le_mul_of_nonneg_left (cdfPenalty_lipschitz hαm hγm) (by positivity))
    _ = _ := by ring

theorem scalarCDFParisi_tendsto_of_L1 (β : ℝ) {α : ℝ → ℝ} {αs : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hs : ∀ n z, αs n z ∈ Icc (0:ℝ) 1) (hsm : ∀ n, Monotone (αs n))
    (ht : Tendsto (fun n => ∫ z in Icc (0:ℝ) 1, |αs n z-α z|) atTop (𝓝 0)) :
    Tendsto (fun n => scalarCDFParisi β (αs n)) atTop (𝓝 (scalarCDFParisi β α)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := squeeze_zero (fun _ => abs_nonneg _)
    (fun n => scalarCDFParisi_cdf_lipschitz β (hs n) (hsm n) hα hαm)
    (by simpa only [mul_zero] using ht.const_mul (scalarTimeMassConstant β+β^2/2))
  simpa only [mul_zero,Real.norm_eq_abs] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_SusceptibilityConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFSusceptibilityAverage_tendsto (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    Tendsto (fun n => scalarCDFSusceptibilityAverage β (αn n) r) atTop
      (𝓝 (scalarCDFSusceptibilityAverage β α r)) := by
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr.1]
  have hrs : r+s≤1 := by rw [hs]; linarith
  let f := scalarCDFValue β α r s
  let g := scalarCDFHessian β α r s
  let fn := fun n => scalarCDFValue β (αn n) r s
  let gn := fun n => scalarCDFHessian β (αn n) r s
  have hfU : TendstoUniformly fn f atTop :=
    scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs
  have hgU : TendstoUniformly gn g atTop :=
    scalarCDFHessian_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs
  have hc := scalarCDFAverage_tendsto_cdf_lipschitz β hα hαm hn hnm hD
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
    0 t ht1 le_rfl (by simpa only [zero_add,ht] using hr.2) 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := Real.log (1+ε/8)/2
  have hd : 0<δ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have he : Real.exp (2*δ)-1=ε/8 := by
    rw [show 2*δ=Real.log (1+ε/8) by dsimp [δ]; ring,
      Real.exp_log (by linarith : 0<1+ε/8)]
    ring
  filter_upwards [(Metric.tendstoUniformly_iff.mp hfU) δ hd,
    (Metric.tendstoUniformly_iff.mp hgU) (ε/4) (by positivity),
    (Metric.tendsto_nhds.mp hc) (ε/4) (by positivity)] with n hf hg hcn
  have hfg (z) : |fn n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hf z).le
  have hgg (z) : |gn n z-g z|≤ε/4 := by simpa only [Real.dist_eq,abs_sub_comm] using (hg z).le
  have Ht := scalarCDFAverage_terminal_stability_lipschitz β (hn n) (hnm n)
    (scalarCDFValue_regular β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_abs_le_one β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
    hd.le hfg hgg 0 t ht1 0
  rw [he,NNReal.coe_one] at Ht
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β (αn n) 0 t f g 0|≤_ at Ht
  change dist (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)<ε/4 at hcn
  rw [Real.dist_eq] at hcn
  rw [Real.dist_eq]
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β α 0 t f g 0|<ε
  have H := abs_sub_le (scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0)
    (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleTimeBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

namespace TripleTimeBlocks
variable {α : ℝ → ℝ} {r s₁ s₂ q : ℝ} (B : TripleTimeBlocks α r s₁ s₂ q)

theorem prefix_raw (κ : ℝ) : rawTimeChain B.front.chain=B.c++weightedUnderlying (B.w κ) := by
  simp only [front,TimeChainOn.append,rawTimeChain_append,c,b,a,d,w_underlying,List.append_assoc]

theorem full_raw (κ : ℝ) : rawTimeChain B.full.chain=B.c++weightedUnderlying (B.w κ)++B.t := by
  rw [full,TimeChainOn.append,rawTimeChain_append,B.prefix_raw κ]; rfl

theorem early_raw : rawTimeChain B.early.chain=B.c++B.b++B.a := by
  simp only [early,TimeChainOn.append,rawTimeChain_append,c,b,a]

@[simp] theorem prefix_variance (κ : ℝ) : rawVariance (B.c++weightedUnderlying (B.w κ))=q := by
  rw [← B.prefix_raw κ,rawVariance_rawTimeChain,B.front.duration,sub_zero]
@[simp] theorem full_variance (κ : ℝ) : rawVariance (B.c++weightedUnderlying (B.w κ)++B.t)=1 := by
  rw [← B.full_raw κ,rawVariance_rawTimeChain,B.full.duration,sub_zero]
@[simp] theorem early_variance : rawVariance (B.c++B.b++B.a)=s₂ := by
  rw [← B.early_raw,rawVariance_rawTimeChain,B.early.duration,sub_zero]

theorem w_penalty (κ : ℝ) : weightedCrossPenalty (B.w κ) 0=κ^2*rawPenalty B.a 0 := by
  simp [w,weightedCrossPenalty_append]

theorem normalized_stats (hs : s₁ < s₂) :
    weightedVariance (B.w (s₂-s₁)⁻¹)=(s₂-s₁)⁻¹ ∧
    weightedCross (B.w (s₂-s₁)⁻¹)=1 ∧ weightedAbsCross (B.w (s₂-s₁)⁻¹)=1 := by
  have hpos : 0 < s₂-s₁ := sub_pos.mpr hs
  rw [B.w_variance,B.w_cross,B.w_absCross,abs_of_pos (inv_pos.mpr hpos)]
  field_simp
  simp

theorem normalized_penalty (hm : Monotone α) (hs : s₁ < s₂) :
    weightedCrossPenalty (B.w (s₂-s₁)⁻¹) 0∈Icc (α s₁) 1 := by
  have hpos : 0 < s₂-s₁ := sub_pos.mpr hs
  have H := rawPenalty_bounds B.a (a:=α s₁) (b:=1) (q:=0)
    (fun p hp => ⟨B.active.raw_mass_lower hm p hp,(B.active.raw_mass p hp).2⟩) le_rfl
  simp only [B.a_variance,zero_add,zero_pow (by norm_num : 2≠0),sub_zero] at H
  rw [B.w_penalty]
  have H₁ := mul_le_mul_of_nonneg_left H.1 (sq_nonneg (s₂-s₁)⁻¹)
  have H₂ := mul_le_mul_of_nonneg_left H.2 (sq_nonneg (s₂-s₁)⁻¹)
  constructor
  · convert H₁ using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  · convert H₂ using 1
    all_goals try with_reducible_and_instances rfl
    field_simp

end TripleTimeBlocks

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleTimeAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

namespace TripleTimeBlocks
variable {α : ℝ → ℝ} {r s₁ s₂ q : ℝ} (B : TripleTimeBlocks α r s₁ s₂ q)

theorem full_mass (κ : ℝ) : ∀ p∈B.c++weightedUnderlying (B.w κ)++B.t,p.1∈Icc (0:ℝ) 1 := by
  rw [← B.full_raw κ]; exact B.full.raw_mass

theorem full_sorted (hm : Monotone α) (κ : ℝ) :
    (B.c++weightedUnderlying (B.w κ)++B.t).Pairwise (fun p q => p.1≤q.1) := by
  rw [← B.full_raw κ]; exact B.full.raw_sorted hm

theorem scalar_parisi (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (κ : ℝ) :
    scalarIncrementChain (scaleIncrementChain β (B.c++weightedUnderlying (B.w κ)++B.t)) scalarSpinTerminal 0-
      β^2/4*rawPenalty (B.c++weightedUnderlying (B.w κ)++B.t) 0=scalarCDFParisi β α := by
  rw [← B.full_raw κ,B.full.scalar_value β ha hm (by norm_num),B.full.penalty hm]
  simp only [sub_zero,Real.toNNReal_one,scalarCDFParisi,intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  ring

theorem scalar_root_hessian (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (κ : ℝ) :
    rootHessian 0 (scalarIncrementChain (scaleIncrementChain β (B.c++weightedUnderlying (B.w κ)++B.t)) scalarSpinTerminal) 0=
      scalarCDFHessian β α 0 1 0 := by
  rw [← B.full_raw κ,B.full.scalar_hessian β ha hm (by norm_num)]
  simp only [sub_zero,Real.toNNReal_one]

theorem scalar_susceptibility (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hq : q∈Icc (0:ℝ) 1) (κ : ℝ) :
    tripleSusceptibility (scaleIncrementChain β B.c) (scaleIncrementChain β (B.w κ)) (scaleIncrementChain β B.t)=
      scalarCDFSusceptibilityAverage β α q := by
  have he : scaleIncrementChain β B.c++weightedUnderlying (scaleIncrementChain β (B.w κ))=
      scaleIncrementChain β (rawTimeChain B.front.chain) := by
    rw [B.prefix_raw κ,scaleIncrementChain_append,weightedUnderlying_scale]
  rw [tripleSusceptibility,he]
  exact B.front.scalar_susceptibility β ha hm hq B.tail

theorem tail_area (hm : Monotone α) : rawArea B.t=∫ x in q..1,α x := B.tail.area hm

theorem exists_scaled_factors (β : ℝ) {κ : ℝ} (hκ : 0≤κ) :
    ∃ k : Fin (zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)).length → ℝ,
      (∀ i,0≤k i) ∧
      (∀ i,((zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)).get i).2.2=
        k i*((zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)).get i).2.1) ∧
      (∀ i,k i≠0 → scalarPrefixVariance (zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)).length
        (fun j => ((zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)).get j).2.1) i.castSucc≤β^2*s₂) := by
  have he : zeroWeightChain (scaleIncrementChain β B.c)++scaleIncrementChain β (B.w κ)++zeroWeightChain (scaleIncrementChain β B.t)=
      zeroWeightChain (scaleIncrementChain β (B.c++B.b))++constantWeightChain κ (scaleIncrementChain β B.a)++
        zeroWeightChain (scaleIncrementChain β (B.d++B.t)) := by
    simp only [w,scaleIncrementChain_append,zeroWeightChain_scale,constantWeightChain_scale,zeroWeightChain_append,List.append_assoc]
  rw [he]
  refine ⟨blockWeights κ _ _ _,blockWeights_nonneg hκ _ _ _,blockWeights_factor κ _ _ _,?_⟩
  intro i hi
  have H := blockWeights_active κ (scaleIncrementChain β (B.c++B.b)) (scaleIncrementChain β B.a)
    (scaleIncrementChain β (B.d++B.t)) i hi
  rw [← scaleIncrementChain_append,rawVariance_scale,B.early_variance] at H
  exact H

end TripleTimeBlocks

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleCDFTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem crossPenalty_response_le {J m : ℝ} (hm : 0 ≤ m) (hJ : J∈Icc m 1) (T : ℝ) :
    J*T ≤ m*T+max T 0 := by
  by_cases hT : 0 ≤ T
  · rw [max_eq_left hT]
    have H := mul_le_mul_of_nonneg_right hJ.2 hT
    have H' := mul_nonneg hm hT
    linarith
  · rw [max_eq_right (le_of_not_ge hT),add_zero]
    exact mul_le_mul_of_nonpos_right hJ.1 (le_of_not_ge hT)

namespace TripleTimeBlocks
variable {α : ℝ → ℝ} {r s₁ s₂ q : ℝ} (B : TripleTimeBlocks α r s₁ s₂ q)

theorem common_error (β : ℝ) (hs : s₁ < s₂) :
    tripleCommonError (scaleIncrementChain β B.c) (scaleIncrementChain β (B.w (s₂-s₁)⁻¹))=
      tripleTimeCommonError β (s₂-s₁)⁻¹ r := by
  rcases B.normalized_stats hs with ⟨hK,_,hC⟩
  simp only [tripleCommonError,weightedMomentBound,weightedVariance_scale,weightedAbsCross_scale,
    rawVariance_scale,hK,hC,B.c_variance,mul_one,tripleTimeCommonError]
  ring

theorem coefficient_le (β : ℝ) (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (hq : q∈Icc (0:ℝ) 1) (hs : s₁ < s₂) :
    tripleQuadraticCoefficient β (β^2*s₂) B.c (B.w (s₂-s₁)⁻¹) B.t ≤
      tripleCDFTrialCoefficient β α (s₂-s₁)⁻¹ r s₁ s₂ q := by
  rcases B.normalized_stats hs with ⟨hK,_,hC⟩
  unfold tripleQuadraticCoefficient
  rw [B.scalar_susceptibility β ha hm hq,B.scalar_root_hessian β ha hm,
    B.tail_area hm,hK,B.common_error β hs]
  unfold tripleCDFTrialCoefficient
  change _+β^2*weightedCrossPenalty (B.w (s₂-s₁)⁻¹) 0*tripleCDFResponse β α s₂ q+_ ≤ _
  have H := mul_le_mul_of_nonneg_left (crossPenalty_response_le (ha s₁).1
    (B.normalized_penalty hm hs) (tripleCDFResponse β α s₂ q)) (sq_nonneg β)
  linarith

include B in
theorem pressure_trial {N : ℕ} (hN : 0 < N) (β δ : ℝ)
    (ha : ∀ z,α z∈Icc (0:ℝ) 1) (hm : Monotone α) (hq : q∈Icc (0:ℝ) 1) (hs : s₁ < s₂)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {a : ℝ} (ha0 : 0 < a) (hδ : 4*δ^2 ≤ a) (hδ1 : |δ| ≤ 1)
    (hsmall : a*(4*β^2*(s₂-s₁)⁻¹+(2*β^2)^2) ≤ 1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤
      3*scalarCDFParisi β α+δ^2*tripleCDFTrialCoefficient β α (s₂-s₁)⁻¹ r s₁ s₂ q+
      tripleExpansionConstant a*|δ|^3+β^2*δ^4*((s₂-s₁)⁻¹)^2 := by
  rcases B.normalized_stats hs with ⟨hK,hC,hA⟩
  obtain ⟨k,hk,he,hactive⟩ := B.exists_scaled_factors β (inv_nonneg.mpr (sub_pos.mpr hs).le)
  have hs₂ : 0 ≤ s₂ := by have H := B.early.sub_nonneg; simpa only [sub_zero] using H
  have H := tripleConstrainedPressure_quadratic hN β δ B.c (B.w (s₂-s₁)⁻¹) B.t
    (B.full_mass _) (B.full_sorted hm _) (B.full_variance _) hC
    (by simpa only [B.c_variance,B.prefix_variance] using hD) k hk he
    (mul_nonneg (sq_nonneg β) hs₂) hactive ha0 hδ hδ1 (by simpa only [hK,hA,mul_one] using hsmall)
  rw [B.c_variance,B.prefix_variance,B.scalar_parisi β ha hm,hK] at H
  have HC := mul_le_mul_of_nonneg_left (B.coefficient_le β ha hm hq hs) (sq_nonneg δ)
  linarith

end TripleTimeBlocks

theorem tripleConstrainedPressure_quantile_trial {N k : ℕ} (hN : 0 < N) (β δ : ℝ)
    (Q : Fin (k+1) → ℝ) (hQ : Q∈admissibleQuantiles k)
    {r s₁ s₂ q : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s₁) (hs : s₁ < s₂) (hsq : s₂ ≤ q) (hq : q ≤ 1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {a : ℝ} (ha : 0 < a) (hδ : 4*δ^2 ≤ a) (hδ1 : |δ| ≤ 1)
    (hsmall : a*(4*β^2*(s₂-s₁)⁻¹+(2*β^2)^2) ≤ 1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤
      3*scalarCDFParisi β (quantileCDF k Q)+
      δ^2*tripleCDFTrialCoefficient β (quantileCDF k Q) (s₂-s₁)⁻¹ r s₁ s₂ q+
      tripleExpansionConstant a*|δ|^3+β^2*δ^4*((s₂-s₁)⁻¹)^2 := by
  obtain ⟨c⟩ := exists_quantile_TimeChainOn β Q hQ (s:=0) (t:=r) le_rfl hr (by linarith)
  obtain ⟨b⟩ := exists_quantile_TimeChainOn β Q hQ hr hrs (by linarith)
  obtain ⟨a'⟩ := exists_quantile_TimeChainOn β Q hQ (show 0 ≤ s₁ by linarith) hs.le (by linarith)
  obtain ⟨d⟩ := exists_quantile_TimeChainOn β Q hQ (show 0 ≤ s₂ by linarith) hsq hq
  obtain ⟨t⟩ := exists_quantile_TimeChainOn β Q hQ (show 0 ≤ q by linarith) hq le_rfl
  let B : TripleTimeBlocks (quantileCDF k Q) r s₁ s₂ q := ⟨c,b,a',d,t⟩
  exact B.pressure_trial hN β δ (quantileCDF_bounds k Q) (quantileCDF_monotone k Q)
    ⟨by linarith,hq⟩ hs hD ha hδ hδ1 hsmall

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleContinuumTrial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdfArea_distance_le {α γ : ℝ → ℝ} (hα : Monotone α) (hγ : Monotone γ)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    |(∫ z in q..1, α z)-(∫ z in q..1,γ z)| ≤ cdfDistance α γ := by
  rw [← intervalIntegral.integral_sub hα.intervalIntegrable hγ.intervalIntegrable]
  have H := cdfDistance_subinterval_le hα hγ (t:=Real.toNNReal (1-q)) hq.1
    (by rw [Real.coe_toNNReal _ (sub_nonneg.mpr hq.2)]; linarith)
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hq.2),add_sub_cancel] at H
  exact (intervalIntegral.abs_integral_le_integral_abs hq.2).trans H

theorem cdfArea_tendsto {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : Monotone α) (hn : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => ∫ z in q..1,αn n z) atTop (𝓝 (∫ z in q..1,α z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _)
    (fun n => cdfArea_distance_le (hn n) hα hq) hD

theorem uniformCDFQuantiles_pointwise_tendsto (α : StieltjesFunction ℝ)
    (hα : ∀ z,α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => quantileCDF n (uniformCDFQuantiles n α) s) atTop (𝓝 (α s)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := squeeze_zero (fun _ => abs_nonneg _)
    (fun n => quantileCDF_uniformCDFQuantiles_error n α hα hα1 hs)
    (show Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) by
      simpa only [Nat.cast_add,Nat.cast_one,one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)))
  simpa only [Real.norm_eq_abs] using H

theorem tripleCDFTrialCoefficient_uniform_tendsto (β : ℝ) (α : StieltjesFunction ℝ)
    (hα : ∀ z,α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1)
    (K r s₂ : ℝ) {s₁ q : ℝ} (hs : s₁ ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => tripleCDFTrialCoefficient β (quantileCDF n (uniformCDFQuantiles n α)) K r s₁ s₂ q)
      atTop (𝓝 (tripleCDFTrialCoefficient β α K r s₁ s₂ q)) := by
  let αn := fun n => quantileCDF n (uniformCDFQuantiles n α)
  have hn (n z) : αn n z ∈ Icc (0:ℝ) 1 := quantileCDF_bounds n _ z
  have hnm (n) : Monotone (αn n) := quantileCDF_monotone n _
  have hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0) := uniformCDFQuantiles_L1_tendsto α hα hα1
  have hχ := scalarCDFSusceptibilityAverage_tendsto β hα α.mono hn hnm hD hq
  have hA := cdfArea_tendsto α.mono hnm hD hq
  have hχ0 := (scalarCDFHessian_tendstoUniformly_interval β hα α.mono hn hnm hD 0 1
    le_rfl le_rfl (by norm_num)).tendsto_at 0
  have hm := uniformCDFQuantiles_pointwise_tendsto α hα hα1 hs
  have hT : Tendsto (fun n => tripleCDFResponse β (αn n) s₂ q) atTop
      (𝓝 (tripleCDFResponse β α s₂ q)) := by
    exact (((hχ.const_mul (β^2)).mul ((hχ0.add_const (2*(β^2*s₂))).add_const (4*(β^2*s₂)^2))).sub_const 1)
  exact (((hχ.sub hA).const_mul (β^2*K)).add
    (((hm.mul hT).add (hT.max tendsto_const_nhds)).const_mul (β^2))).add_const (tripleTimeCommonError β K r)

theorem tripleConstrainedPressure_continuum_trial {N : ℕ} (hN : 0 < N) (β δ : ℝ)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1)
    {r s₁ s₂ q : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s₁) (hs : s₁ < s₂) (hsq : s₂ ≤ q) (hq : q ≤ 1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {a : ℝ} (ha : 0 < a) (hδ : 4*δ^2 ≤ a) (hδ1 : |δ| ≤ 1)
    (hsmall : a*(4*β^2*(s₂-s₁)⁻¹+(2*β^2)^2) ≤ 1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤
      3*scalarCDFParisi β α+δ^2*tripleCDFTrialCoefficient β α (s₂-s₁)⁻¹ r s₁ s₂ q+
      tripleExpansionConstant a*|δ|^3+β^2*δ^4*((s₂-s₁)⁻¹)^2 := by
  have hC := tripleCDFTrialCoefficient_uniform_tendsto β α hα hα1 (s₂-s₁)⁻¹ r s₂
    (s₁:=s₁) (q:=q) ⟨by linarith,by linarith⟩ ⟨by linarith,hq⟩
  have hP := scalarCDFParisi_tendsto_of_L1 β hα α.mono
    (fun n => quantileCDF_bounds n (uniformCDFQuantiles n α))
    (fun n => quantileCDF_monotone n (uniformCDFQuantiles n α)) (uniformCDFQuantiles_L1_tendsto α hα hα1)
  apply ge_of_tendsto ((((hP.const_mul 3).add (hC.const_mul (δ^2))).add_const
    (tripleExpansionConstant a*|δ|^3)).add_const (β^2*δ^4*((s₂-s₁)⁻¹)^2))
  exact Eventually.of_forall (fun n => tripleConstrainedPressure_quantile_trial hN β δ
    (uniformCDFQuantiles n α) (uniformCDFQuantiles_admissible n α hα1) hr hrs hs hsq hq hD ha hδ hδ1 hsmall)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFMinimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem supported_probability_cdf_one (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) : cdf (μ : Measure ℝ) 1=1 := by
  have H : (μ : Measure ℝ) (Iic 1)=1 := le_antisymm prob_le_one
    (by rw [← hμ]; exact measure_mono Icc_subset_Iic_self)
  rw [cdf_eq_real,Measure.real,H,ENNReal.toReal_one]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_TripleNegativeCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem continuousAt_small_interval {f : ℝ → ℝ} (hf : ContinuousAt f 0)
    {b L : ℝ} (hb : f 0 < b) (hL : 0 < L) :
    ∃ e ∈ Ioo (0:ℝ) L, ∀ x ∈ Icc (0:ℝ) e, f x < b := by
  obtain ⟨d,hd,hf'⟩ := Metric.eventually_nhds_iff.mp (hf.eventually_lt continuousAt_const hb)
  refine ⟨min L d/2,⟨by positivity,?_⟩,?_⟩
  · have H := min_le_left L d; linarith [lt_min hL hd]
  · intro x hx
    apply hf'
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hx.1]
    have H := min_le_right L d
    linarith [hx.2]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_OverlapCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem overlap_eq_codeOverlap {n : ℕ} (x y : Config n) :
    overlap x y=codeOverlap n (overlapCode x y) := by
  have he (i : Fin n) : spin (x i)*spin (y i)=2*(if x i=y i then (1:ℝ) else 0)-1 := by
    cases hx : x i <;> cases hy : y i <;> norm_num [spin]
  simp only [overlap,he,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  congr 1
  simp [overlapCode,Finset.sum_boole]

theorem replicaGram_pair {n : ℕ} (hn : 0 < n) (s : ReplicaConfig n 2) :
    replicaGram s=pairMatrix 1 (codeOverlap n (pairReplicaCode s)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [replicaGram,pairMatrix,pairReplicaCode,← overlap_eq_codeOverlap,overlap_comm,overlap_self hn]

theorem replicaGram_triple {n : ℕ} (hn : 0 < n) (s : ReplicaConfig n 3) :
    replicaGram s=tripleGram
      ((codeOverlap n (tripleReplicaCode s 0)+codeOverlap n (tripleReplicaCode s 1))/2)
      ((codeOverlap n (tripleReplicaCode s 0)-codeOverlap n (tripleReplicaCode s 1))/2)
      (codeOverlap n (tripleReplicaCode s 2)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [replicaGram,tripleGram,tripleReplicaCode,← overlap_eq_codeOverlap,overlap_comm,overlap_self hn] <;> ring_nf <;> exact overlap_comm _ _

theorem pairReplicaCode_gram {n : ℕ} (hn : 0 < n) {s t : ReplicaConfig n 2}
    (h : pairReplicaCode s=pairReplicaCode t) : replicaGram s=replicaGram t := by
  rw [replicaGram_pair hn,replicaGram_pair hn,h]

theorem tripleReplicaCode_gram {n : ℕ} (hn : 0 < n) {s t : ReplicaConfig n 3}
    (h : tripleReplicaCode s=tripleReplicaCode t) : replicaGram s=replicaGram t := by
  rw [replicaGram_triple hn,replicaGram_triple hn,h]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem replicaGibbsWeight_flip {n d : ℕ} (a : Fin d) (β : ℝ) (J : Disorder n)
    (s : ReplicaConfig n d) : (∏ i,gibbs β J (replicaFlip a s i))=∏ i,gibbs β J (s i) := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i=a <;> simp [replicaFlip,hi]

theorem replicaGibbsMass_flip {n d : ℕ} (a : Fin d) (β : ℝ) (J : Disorder n)
    (S : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J (S.image (replicaFlip a))=replicaGibbsMass β J S := by
  classical
  unfold replicaGibbsMass
  rw [Finset.sum_image (replicaFlip_involutive a).injective.injOn]
  exact Finset.sum_congr rfl (fun s _ => replicaGibbsWeight_flip a β J s)

theorem replicaGibbsMass_mono {n d : ℕ} (β : ℝ) (J : Disorder n)
    {S T : Finset (ReplicaConfig n d)} (h : S ⊆ T) :
    replicaGibbsMass β J S ≤ replicaGibbsMass β J T :=
  Finset.sum_le_sum_of_subset_of_nonneg h
    (fun s _ _ => Finset.prod_nonneg (fun a _ => (gibbs_pos β J (s a)).le))

theorem replicaGibbsMass_union_le {n d : ℕ} (β : ℝ) (J : Disorder n)
    (S T : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J (S∪T) ≤ replicaGibbsMass β J S+replicaGibbsMass β J T := by
  have H := @Finset.sum_union_inter _ ℝ S T _ (fun s : ReplicaConfig n d => ∏ a,gibbs β J (s a)) _
  have H' := replicaGibbsMass_nonneg β J (S∩T)
  change replicaGibbsMass β J (S∪T)+replicaGibbsMass β J (S∩T)=
    replicaGibbsMass β J S+replicaGibbsMass β J T at H
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem replicaGram_triple_overlap {n : ℕ} (hn : 0<n) (s : ReplicaConfig n 3) :
    replicaGram s=tripleGram (tripleR s) (tripleDelta s) (tripleQ s) := by
  simpa [tripleReplicaCode,← overlap_eq_codeOverlap,tripleR,tripleDelta,tripleQ] using
    replicaGram_triple hn s

theorem replicaGram_feasible {n d : ℕ} (s : ReplicaConfig n d) :
    Nonempty (MatrixStates n d (replicaGram s)) :=
  (matrixReplicaSet_nonempty_iff _).mp ⟨s,(mem_matrixReplicaSet _ _).mpr rfl⟩

@[simp] theorem tripleR_flip {n : ℕ} (s : ReplicaConfig n 3) :
    tripleR (replicaFlip 0 s)= -tripleR s := by
  simp only [tripleR,replicaFlip]
  norm_num only [ite_true,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,ite_false]
  rw [overlap_comm (flip (s 0)),overlap_flip_right,
    overlap_comm (flip (s 0)),overlap_flip_right]
  rw [overlap_comm (s 1),overlap_comm (s 2)]
  ring

@[simp] theorem tripleDelta_flip {n : ℕ} (s : ReplicaConfig n 3) :
    tripleDelta (replicaFlip 0 s)= -tripleDelta s := by
  simp only [tripleDelta,replicaFlip]
  norm_num only [ite_true,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,ite_false]
  rw [overlap_comm (flip (s 0)),overlap_flip_right,
    overlap_comm (flip (s 0)),overlap_flip_right]
  rw [overlap_comm (s 1),overlap_comm (s 2)]
  ring

theorem tripleRDelta_abs_le {n : ℕ} (s : ReplicaConfig n 3) {b : ℝ}
    (h₁ : |overlap (s 0) (s 1)|≤b) (h₂ : |overlap (s 0) (s 2)|≤b) :
    |tripleR s|≤b ∧ |tripleDelta s|≤b := by
  have H₁ := (abs_le.mp h₁)
  have H₂ := (abs_le.mp h₂)
  constructor <;> rw [abs_le] <;> dsimp only [tripleR,tripleDelta] <;> constructor <;> linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairGibbsGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem eventual_pairMismatch_polynomial_bound {β A a t ε : ℝ} (hβ : 0<β)
    (hA : 0<A) (ha : 0≤a) (ha48 : a<1/48) (ht : t<1-4*a) (hε : 0<ε)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hmin : scalarCDFParisi β α=finiteParisiInf β) :
    ∀ᶠ n : ℕ in atTop,
      (∫ J,replicaGibbsMass β J (pairMismatchSet n β α (A*(n:ℝ)^(-a))) ∂disorderLaw n)≤
        ε*Real.exp (-(n:ℝ)^t) := by
  have H := eventual_replicaGibbsMass_polynomial_gap (c:=A^2/2) (a:=2*a) (t:=t) hβ
    2 1 (by decide) (by positivity) (by positivity) (by linarith) (by linarith) hε
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with n hn hn0
  apply hn (Fin (n+1)) (by simp) pairReplicaCode (fun s t h => pairReplicaCode_gram hn0 h)
  intro s hs
  have HP := pairMismatch_pressure_gap hn0 β α hα hα1 hmin (by positivity : 0≤A*(n:ℝ)^(-a)) hs
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  have he : (A*(n:ℝ)^(-a))^2/2=A^2/2*(n:ℝ)^(-(2*a)) := by
    rw [mul_pow,← Real.rpow_natCast ((n:ℝ)^(-a)) 2,← Real.rpow_mul hp.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (-a)*2= -(2*a) by ring]
    ring
  simpa only [Nat.cast_ofNat,he] using HP

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaEventSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem replicaGibbsMass_le_or_or_flip {n d : ℕ} (a : Fin d) (β : ℝ) (J : Disorder n)
    (S T P : Finset (ReplicaConfig n d))
    (h : ∀ s∈S,s∈T ∨ replicaFlip a s∈T ∨ s∈P) :
    replicaGibbsMass β J S≤2*replicaGibbsMass β J T+replicaGibbsMass β J P := by
  classical
  have hsub : S⊆(T∪T.image (replicaFlip a))∪P := by
    intro s hs
    rcases h s hs with h|h|h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨replicaFlip a s,h,replicaFlip_involutive a s⟩))
    · exact Finset.mem_union_right _ h
  have H := (replicaGibbsMass_mono β J hsub).trans
    (replicaGibbsMass_union_le β J (T∪T.image (replicaFlip a)) P)
  have H' := replicaGibbsMass_union_le β J T (T.image (replicaFlip a))
  rw [replicaGibbsMass_flip] at H'
  linarith

theorem replicaGibbsMass_integral_or_or_flip {n d : ℕ} (a : Fin d) (β : ℝ)
    (S T P : Finset (ReplicaConfig n d))
    (h : ∀ s∈S,s∈T ∨ replicaFlip a s∈T ∨ s∈P) :
    (∫ J,replicaGibbsMass β J S ∂disorderLaw n)≤
      2*(∫ J,replicaGibbsMass β J T ∂disorderLaw n)+(∫ J,replicaGibbsMass β J P ∂disorderLaw n) := by
  have H := integral_mono (replicaGibbsMass_integrable β S)
    (((replicaGibbsMass_integrable β T).const_mul 2).add (replicaGibbsMass_integrable β P))
    (fun J => replicaGibbsMass_le_or_or_flip a β J S T P h)
  simpa only [Pi.add_apply,integral_add ((replicaGibbsMass_integrable β T).const_mul 2) (replicaGibbsMass_integrable β P),
    integral_const_mul] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem replicaGibbsMass_tail {n d : ℕ} (β : ℝ) (J : Disorder n)
    (S : Finset (ReplicaConfig n d)) :
    replicaGibbsMass β J (Finset.univ.filter (fun s : ReplicaConfig n (d+1) => Fin.tail s∈S))=
      replicaGibbsMass β J S := by
  classical
  unfold replicaGibbsMass
  rw [Finset.sum_filter]
  calc
    _ = ∑ p : Config n × ReplicaConfig n d,if p.2∈S then gibbs β J p.1*∏ a,gibbs β J (p.2 a) else 0 := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (d+1) => Config n)).symm
      intro s
      simp only [Fin.consEquiv_symm_apply,Fin.prod_univ_succ,Fin.tail]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [show ∀ (x : Config n) (s : ReplicaConfig n d),
          (if s∈S then gibbs β J x*∏ a,gibbs β J (s a) else 0)=
          gibbs β J x*(if s∈S then ∏ a,gibbs β J (s a) else 0) by intros; split_ifs <;> simp]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul,gibbs_sum,one_mul,← Finset.sum_filter]
      simp

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_OverlapPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

@[simp] theorem overlap_flip_first {n : ℕ} (x y : Config n) : overlap (flip x) y = -overlap x y := by
  rw [overlap_comm,overlap_flip_right,overlap_comm x y]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleContinuumGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem exists_tripleConstrainedPressure_gap {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0:ℝ) 1)=1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β ∧
      ∃ τ r₀ δ₀ c : ℝ, 0 < τ ∧ 0 < r₀ ∧ 0 < δ₀ ∧ 0 < c ∧
        ∀ (N : ℕ), 0 < N → ∀ r δ q : ℝ,
          r ∈ Icc (0:ℝ) r₀ → |δ| ≤ δ₀ → q ∈ Icc h 1 →
          |q-scalarCDFOverlap β (cdf (μ : Measure ℝ)) q| ≤ τ →
          Nonempty (MatrixStates N 3 (tripleGram r δ q)) →
          matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤ 3*finiteParisiInf β-c*δ^2 := by
  obtain ⟨μ,hμ,hmin,s₁,s₂,τ,r₀,c,hs₁,hs,hs₂,hτ,hr₀,hrs,hc,hC⟩ :=
    exists_negative_tripleCDF_coefficient hβ hh hh1
  let K := (s₂-s₁)⁻¹
  let M := 4*β^2*K+(2*β^2)^2
  obtain ⟨a,ha,hMa⟩ := continuousAt_small_interval
    (show ContinuousAt (fun a : ℝ => a*M) 0 by fun_prop)
    (show (0:ℝ)*M < 1/2 by norm_num) zero_lt_one
  have hsmall : a*M ≤ 1/2 := (hMa a ⟨ha.1.le,le_rfl⟩).le
  obtain ⟨d,hd,hda⟩ := continuousAt_small_interval
    (show ContinuousAt (fun d : ℝ => 4*d^2) 0 by fun_prop)
    (by simpa only [zero_pow (by decide : 2≠0),mul_zero] using ha.1) zero_lt_one
  obtain ⟨δ₀,hδ₀,hrem⟩ := continuousAt_small_interval
    (show ContinuousAt (fun x : ℝ => tripleExpansionConstant a*x+β^2*K^2*x^2) 0 by fun_prop)
    (by simpa only [zero_pow (by decide : 2≠0),mul_zero,add_zero] using half_pos hc) hd.1
  refine ⟨μ,hμ,hmin,τ,r₀,δ₀,c/2,hτ,hr₀,hδ₀.1,half_pos hc,?_⟩
  intro N hN r δ q hr hδ hq he hD
  have hδd : |δ| ≤ d := hδ.trans hδ₀.2.le
  have hδa : 4*δ^2 ≤ a := by
    have H := (hda |δ| ⟨abs_nonneg _,hδd⟩).le
    simpa only [sq_abs] using H
  have hδ1 : |δ| ≤ 1 := hδd.trans hd.2.le
  have H := tripleConstrainedPressure_continuum_trial hN β δ (cdf (μ : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ _,cdf_le_one _ _⟩) (supported_probability_cdf_one μ hμ)
    hr.1 (hr.2.trans hrs.le) hs (hs₂.le.trans hq.1) hq.2 hD ha.1 hδa hδ1 hsmall
  rw [hmin] at H
  have HC := mul_le_mul_of_nonneg_left (hC r q hr hq he) (sq_nonneg δ)
  have HR := mul_le_mul_of_nonneg_left (hrem |δ| ⟨abs_nonneg _,hδ⟩).le (sq_nonneg δ)
  have HE : tripleExpansionConstant a*|δ|^3+β^2*δ^4*K^2 =
      δ^2*(tripleExpansionConstant a*|δ|+β^2*K^2*|δ|^2) := by
    conv_lhs => rw [show |δ|^3=|δ|^2*|δ| by ring,sq_abs]
    rw [sq_abs]
    ring
  change matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤
    3*finiteParisiInf β+δ^2*tripleCDFTrialCoefficient β (cdf (μ : Measure ℝ)) K r s₁ s₂ q+
    tripleExpansionConstant a*|δ|^3+β^2*δ^4*K^2 at H
  have HR' : tripleExpansionConstant a*|δ|^3+β^2*δ^4*K^2 ≤ δ^2*(c/2) := by rw [HE]; exact HR
  nlinarith only [H,HC,HR']

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_SignedLocking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem signedLocking_split {n : ℕ} (β h b τ : ℝ) (hh : 0≤h) (α : ℝ → ℝ)
    {s : ReplicaConfig n 3} (hs : s∈signedLockingSet n h b) :
    s∈orientedLockingSet n β α h b τ ∨ replicaFlip 0 s∈orientedLockingSet n β α h b τ ∨
      Fin.tail s∈pairMismatchSet n β α τ := by
  classical
  obtain ⟨hq,hx,hy,hd⟩ := (Finset.mem_filter.mp hs).2
  have hb := tripleRDelta_abs_le s hx hy
  have hq1 := (abs_le.mp (abs_overlap_le_one (s 1) (s 2))).2
  have hδ : (n:ℝ)^(-(1:ℝ)/100)≤|tripleDelta s| := by
    dsimp only [tripleDelta]
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [hd]
  by_cases hg : |tripleQ s-scalarCDFOverlap β α (tripleQ s)|≤τ
  · by_cases hr : 0≤tripleR s
    · left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨⟨hq,hq1⟩,⟨hr,(abs_le.mp hb.1).2⟩,hb.2,hδ,hg⟩⟩
    · right; left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [tripleQ_flip,tripleR_flip,tripleDelta_flip,abs_neg]
      exact ⟨⟨hq,hq1⟩,⟨by linarith only [hr],by linarith only [(abs_le.mp hb.1).1]⟩,hb.2,hδ,hg⟩
  · right; right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨hh.trans hq,(not_le.mp hg).le⟩⟩

theorem signed_fixed_scale_locking {β h : ℝ} (hβ : 0<β) (hh : 0<h) (hh1 : h≤1) :
    ∃ b : ℝ,0<b ∧ ∀ᶠ n : ℕ in atTop,
      (∫ J,replicaGibbsMass β J (signedLockingSet n h b) ∂disorderLaw n)≤
        Real.exp (-(n:ℝ)^((9:ℝ)/10)) := by
  classical
  obtain ⟨μ,hμ,hmin,τ,r₀,δ₀,c,hτ,hr₀,hδ₀,hc,hgap⟩ := exists_tripleConstrainedPressure_gap hβ hh hh1
  let α := cdf (μ : Measure ℝ)
  have ha (z : ℝ) : α z∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have ha1 : α 1=1 := supported_probability_cdf_one μ hμ
  let b := min r₀ δ₀
  have hb : 0<b := lt_min hr₀ hδ₀
  have HP := eventual_pairMismatch_polynomial_bound (A:=τ) (a:=0) (t:=(9:ℝ)/10) (ε:=1/2)
    hβ hτ le_rfl (by norm_num) (by norm_num) (by norm_num) α ha ha1 hmin
  have HT := eventual_replicaGibbsMass_polynomial_gap (c:=c) (a:=(1:ℝ)/50) (t:=(9:ℝ)/10) (ε:=1/4)
    hβ 3 3 (by decide) hc (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨b,hb,?_⟩
  filter_upwards [HP,HT,eventually_gt_atTop (0:ℕ)] with n hnP hnT hn0
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  let T := orientedLockingSet n β α h b τ
  have HT' : (∫ J,replicaGibbsMass β J T ∂disorderLaw n)≤(1/4)*Real.exp (-(n:ℝ)^((9:ℝ)/10)) := by
    apply hnT (Fin 3 → Fin (n+1)) (by simp) tripleReplicaCode (fun s t H => tripleReplicaCode_gram hn0 H)
    intro s hs
    obtain ⟨hq,hr,hδ,hδlower,hdev⟩ := (Finset.mem_filter.mp hs).2
    have hfeas := replicaGram_feasible s
    rw [replicaGram_triple_overlap hn0] at hfeas ⊢
    have HG := hgap n hn0 (tripleR s) (tripleDelta s) (tripleQ s)
      ⟨hr.1,hr.2.trans (min_le_left _ _)⟩ (hδ.trans (min_le_right _ _)) hq hdev hfeas
    have HD := pow_le_pow_left₀ (Real.rpow_nonneg hp.le _) hδlower 2
    rw [sq_abs] at HD
    have HE : ((n:ℝ)^(-(1:ℝ)/100))^2=(n:ℝ)^(-(1:ℝ)/50) := by
      rw [← Real.rpow_natCast ((n:ℝ)^(-(1:ℝ)/100)) 2,← Real.rpow_mul hp.le]
      norm_num
    rw [HE] at HD
    have HDC := mul_le_mul_of_nonneg_left HD hc.le
    norm_num only [Nat.cast_ofNat]
    linarith only [HG,HDC]
  have Hsplit := replicaGibbsMass_integral_or_or_flip (0:Fin 3) β (signedLockingSet n h b) T
    (Finset.univ.filter (fun s : ReplicaConfig n 3 => Fin.tail s∈pairMismatchSet n β α τ))
    (fun s hs => by
      rcases signedLocking_split β h b τ hh.le α hs with H|H|H
      · exact Or.inl H
      · exact Or.inr (Or.inl H)
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,H⟩)))
  simp_rw [replicaGibbsMass_tail] at Hsplit
  simp only [neg_zero,Real.rpow_zero,mul_one] at hnP
  linarith only [Hsplit,HT',hnP]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_LockingScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem signedLockingSet_mono {n : ℕ} {h b c : ℝ} (hbc : b ≤ c) :
    signedLockingSet n h b⊆signedLockingSet n h c := by
  intro s hs
  obtain ⟨hq,hx,hy,hd⟩ := (Finset.mem_filter.mp hs).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq,hx.trans hbc,hy.trans hbc,hd⟩

 theorem signed_small_scale_oai {β h : ℝ} (hβ : 0<β) (hh : 0<h) (hh1 : h≤1) {e : ℝ} (he : 0<e) :
    ∃b : ℝ,0<b ∧ b<e ∧ ∀ᶠ n : ℕ in atTop,
      (∫J,replicaGibbsMass β J (signedLockingSet n h b) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((9:ℝ)/10)) := by
  obtain ⟨b₀,hb₀,H⟩ := signed_fixed_scale_locking hβ hh hh1
  refine ⟨min b₀ (e/2),lt_min hb₀ (half_pos he),(min_le_right _ _).trans_lt (half_lt_self he),?_⟩
  filter_upwards [H] with n hn
  refine (integral_mono (replicaGibbsMass_integrable β _) (replicaGibbsMass_integrable β _)
    (fun J => replicaGibbsMass_mono β J (signedLockingSet_mono (min_le_left b₀ (e/2))))).trans hn

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.signed_small_scale_oai := @OAI.SK.Analytic.signed_small_scale_oai
