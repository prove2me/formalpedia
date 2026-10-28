-- Prove2me | solution 1 for OAI.SK.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:18:36.113193+00:00
-- url     : https://prove2.me/submissions/c234da59-ab97-4225-a2a3-969ee1490a8e

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004
import Definitions.Def_OAIQ036S005
import Theorems.Thm_OAI_SK_Analytic_exists_scalarCDFParisi_minimizer_locking_data
import Theorems.Thm_OAI_SK_Analytic_identity_main_of_static_locking
import Theorems.Thm_OAI_SK_Analytic_narrowConstrainedPressure_scaled_gap
import Theorems.Thm_OAI_SK_Analytic_pairMismatch_pressure_gap
import Theorems.Thm_OAI_SK_Analytic_quenchedPressure_quantitative_finiteInf
import Theorems.Thm_OAI_SK_Analytic_signed_small_scale
import Theorems.Thm_OAI_SK_Analytic_stretched_uniform_coverage

section
-- module Solutions.OAIQ036_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

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
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageScale
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

theorem stretchedLogScale_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)^kappa) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num [kappa])).comp tendsto_natCast_atTop_atTop

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_HeatBathChoice
attribute [-instance] _root_.OAI.SK.disorderLaw_isGaussian _root_.OAI.SK.disorderLaw_probability _root_.OAI.SK.disorderPairLaw_probability
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

theorem discreteKernel_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (k : ℕ) (x y : Config n) :
    0 ≤ discreteKernel β J k x y := by
  induction k generalizing x y with
  | zero => simp only [discreteKernel]; split_ifs <;> norm_num
  | succ k ih =>
    exact Finset.sum_nonneg (fun z _ => mul_nonneg (heatBath_nonneg β J x z) (ih z y))

theorem discreteKernel_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (k : ℕ) (x : Config n) :
    ∑ y : Config n, discreteKernel β J k x y = 1 := by
  classical
  induction k generalizing x with
  | zero => simp [discreteKernel]
  | succ k ih =>
    simp only [discreteKernel]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,ih,mul_one]
    exact heatBath_sum hn β J x

theorem discreteKernel_le_one {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (k : ℕ) (x y : Config n) : discreteKernel β J k x y ≤ 1 := by
  rw [← discreteKernel_sum hn β J k x]
  exact Finset.single_le_sum (fun z _ => discreteKernel_nonneg β J k x z) (Finset.mem_univ y)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_HeatBathEnergy
attribute [-instance] _root_.OAI.SK.disorderLaw_isGaussian _root_.OAI.SK.disorderPairLaw_probability
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

theorem coupling_comm {n : ℕ} (J : Disorder n) (i j : Fin n) : coupling J i j = coupling J j i := by
  rcases lt_trichotomy i j with h | h | h
  · simp [coupling,h,not_lt_of_ge h.le]
  · subst j; rfl
  · simp [coupling,h,not_lt_of_ge h.le]

theorem interactionSum_eq_edges {n : ℕ} (J : Disorder n) (v : Fin n → ℝ) :
    interactionSum J v = 2*∑ e : Edge n, J e*v e.val.1*v e.val.2 := by
  have hE : (∑ e : Edge n, J e*v e.val.1*v e.val.2) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then coupling J i j*v i*v j else 0 := by
    calc
      _ = ∑ e : Edge n, coupling J e.val.1 e.val.2*v e.val.1*v e.val.2 := by
        apply Finset.sum_congr rfl
        intro e _
        simp only [coupling,dite_eq_left e.property]
      _ = _ := sum_edges (fun p => coupling J p.1 p.2*v p.1*v p.2)
  have ht (i j : Fin n) : coupling J i j*v i*v j =
      (if i < j then coupling J i j*v i*v j else 0)+
      (if j < i then coupling J i j*v i*v j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [h,not_lt_of_ge h.le,ite_true,ite_false,add_zero]
    · subst j; simp
    · simp only [h,not_lt_of_ge h.le,ite_true,ite_false,zero_add]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun j _ => Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun k _ => ht j k))
  unfold interactionSum
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hswap : (∑ i : Fin n, ∑ j : Fin n, if j < i then coupling J i j*v i*v j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then coupling J i j*v i*v j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [coupling_comm J j i]
    split_ifs <;> ring
  rw [hswap,← hE]
  ring

theorem hamiltonian_eq_interactionSum {n : ℕ} (J : Disorder n) (x : Config n) :
    hamiltonian J x = interactionSum J (fun i => spin (x i))/(2*Real.sqrt n) := by
  rw [interactionSum_eq_edges]
  unfold hamiltonian
  ring

theorem interactionSum_update {n : ℕ} (J : Disorder n) (v : Fin n → ℝ) (i : Fin n) (r : ℝ) :
    interactionSum J (Function.update v i r) = interactionSum J v+
      2*(r-v i)*(∑ j, coupling J i j*v j) := by
  classical
  have ht (j k : Fin n) : coupling J j k*Function.update v i r j*Function.update v i r k =
      coupling J j k*v j*v k+
      (if j=i then coupling J i k*(r-v i)*v k else 0)+
      (if k=i then coupling J j i*v j*(r-v i) else 0) := by
    by_cases hj : j=i <;> by_cases hk : k=i
    · subst j; subst k; simp
    · subst j; simp only [Function.update_self,Function.update_of_ne hk,ite_true,ite_eq_right hk,add_zero]; ring
    · subst k; simp only [Function.update_self,Function.update_of_ne hj,ite_true,ite_eq_right hj,add_zero]; ring
    · simp only [Function.update_of_ne hj,Function.update_of_ne hk,ite_false,hj,hk,add_zero]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl
    (fun j _ => Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun k _ => ht j k))
  unfold interactionSum
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have H1 : (∑ j : Fin n, ∑ k : Fin n, if j=i then coupling J i k*(r-v i)*v k else 0) =
      (r-v i)*(∑ k, coupling J i k*v k) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have H2 : (∑ j : Fin n, ∑ k : Fin n, if k=i then coupling J j i*v j*(r-v i) else 0) =
      (r-v i)*(∑ j, coupling J i j*v j) := by
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [coupling_comm J j i]
    ring
  rw [H1,H2]
  ring

theorem hamiltonian_update {n : ℕ} (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) :
    hamiltonian J (Function.update x i b) = hamiltonian J x+
      (spin b-spin (x i))*localField J x i := by
  have hu : (fun j => spin (Function.update x i b j)) =
      Function.update (fun j => spin (x j)) i (spin b) := by
    funext j
    by_cases h : j=i
    · subst j; simp
    · simp [Function.update_of_ne h]
  rw [hamiltonian_eq_interactionSum,hu,interactionSum_update,hamiltonian_eq_interactionSum]
  unfold localField
  ring

theorem localField_update {n : ℕ} (J : Disorder n) (x : Config n) (i : Fin n) (b : Bool) :
    localField J (Function.update x i b) i = localField J x i := by
  unfold localField
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j=i
  · subst j; simp
  · simp only [Function.update_of_ne h]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_HeatBathStationary
attribute [-instance] _root_.OAI.SK.disorderLaw_isGaussian _root_.OAI.SK.disorderPairLaw_probability
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

theorem update_reversible {n : ℕ} (x y : Config n) (i : Fin n)
    (h : Function.update x i (y i) = y) : Function.update y i (x i) = x := by
  classical
  funext j
  by_cases hj : j=i
  · subst j; simp
  · have H := congrFun h j
    simpa only [Function.update_of_ne hj] using H.symm

theorem siteChoice_detailedBalance {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) (i : Fin n)
    (h : Function.update x i (y i) = y) :
    gibbs β J x*siteChoice β J x i (y i) = gibbs β J y*siteChoice β J y i (x i) := by
  have hF : localField J y i = localField J x i := by
    rw [← h]
    exact localField_update J x i (y i)
  have hH : hamiltonian J y = hamiltonian J x+(spin (y i)-spin (x i))*localField J x i := by
    simpa only [h] using hamiltonian_update J x i (y i)
  have he : Real.exp (β*hamiltonian J x)*Real.exp (β*spin (y i)*localField J x i) =
      Real.exp (β*hamiltonian J y)*Real.exp (β*spin (x i)*localField J x i) := by
    rw [← Real.exp_add,← Real.exp_add,hH]
    congr 1
    ring
  unfold gibbs siteChoice
  rw [hF,div_mul_div_comm,div_mul_div_comm,he]

theorem heatBath_detailedBalance {n : ℕ} (β : ℝ) (J : Disorder n) (x y : Config n) :
    gibbs β J x*heatBath β J x y = gibbs β J y*heatBath β J y x := by
  classical
  unfold heatBath
  rw [← mul_div_assoc,← mul_div_assoc,Finset.mul_sum,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : Function.update x i (y i) = y
  · have hr := update_reversible x y i h
    simp only [ite_eq_left h,ite_eq_left hr]
    exact siteChoice_detailedBalance β J x y i h
  · have hr : Function.update y i (x i) ≠ x := fun hy => h (update_reversible y x i hy)
    simp only [ite_eq_right h,ite_eq_right hr,mul_zero]

theorem heatBath_stationary {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (y : Config n) :
    ∑ x : Config n, gibbs β J x*heatBath β J x y = gibbs β J y := by
  simp_rw [heatBath_detailedBalance]
  rw [← Finset.mul_sum,heatBath_sum hn,mul_one]

theorem discreteKernel_stationary {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (k : ℕ) (y : Config n) : ∑ x : Config n, gibbs β J x*discreteKernel β J k x y = gibbs β J y := by
  classical
  induction k with
  | zero => simp [discreteKernel]
  | succ k ih =>
    simp only [discreteKernel,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc,← Finset.sum_mul,heatBath_stationary hn]
    exact ih

theorem overlap_update_le {n : ℕ} (hn : 0 < n) (v x : Config n) (i : Fin n) (b : Bool) :
    |overlap v (Function.update x i b)-overlap v x| ≤ 2/(n:ℝ) := by
  classical
  have H : (∑ j : Fin n, spin (v j)*spin (Function.update x i b j)) =
      (∑ j : Fin n, spin (v j)*spin (x j))+spin (v i)*(spin b-spin (x i)) := by
    have ht (j : Fin n) : spin (v j)*spin (Function.update x i b j) =
        spin (v j)*spin (x j)+(if j=i then spin (v i)*(spin b-spin (x i)) else 0) := by
      by_cases hj : j=i
      · subst j; simp only [Function.update_self,ite_true]; ring
      · simp only [Function.update_of_ne hj,ite_eq_right hj,add_zero]
    simp_rw [ht]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hb : |spin (v i)*(spin b-spin (x i))| ≤ 2 := by
    cases hv : v i <;> cases hx : x i <;> cases b <;> norm_num [spin,hv,hx]
  unfold overlap
  rw [H,add_div,add_sub_cancel_left,abs_div,abs_of_pos (show 0 < (n:ℝ) by exact_mod_cast hn)]
  exact div_le_div_of_nonneg_right hb (by positivity)

theorem heatBath_overlap_step {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n) (v x y : Config n)
    (hxy : 0 < heatBath β J x y) : |overlap v y-overlap v x| ≤ 2/(n:ℝ) := by
  classical
  by_contra h
  have hz : heatBath β J x y = 0 := by
    unfold heatBath
    have HH : ∀ i : Fin n, Function.update x i (y i) ≠ y := by
      intro i hi
      exact h (hi ▸ overlap_update_le hn v x i (y i))
    simp only [HH,ite_false,Finset.sum_const_zero,zero_div]
  linarith

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteLaw
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

namespace FiniteLaw
variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem expect_nonneg (P : FiniteLaw X) {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ P.expect f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (P.nonneg x) (hf x))

theorem expect_mono (P : FiniteLaw X) {f g : X → ℝ} (h : ∀ x, f x ≤ g x) : P.expect f ≤ P.expect g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x))

theorem expect_add (P : FiniteLaw X) (f g : X → ℝ) :
    P.expect (fun x => f x+g x)=P.expect f+P.expect g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

theorem expect_mul_const (P : FiniteLaw X) (f : X → ℝ) (c : ℝ) :
    P.expect (fun x => f x*c)=P.expect f*c := by
  simp only [expect,← mul_assoc,Finset.sum_mul]

theorem expect_const_mul (P : FiniteLaw X) (c : ℝ) (f : X → ℝ) :
    P.expect (fun x => c*f x)=c*P.expect f := by
  simp_rw [mul_comm c]
  exact expect_mul_const P f c

theorem prob_nonneg (P : FiniteLaw X) (E : X → Prop) : 0 ≤ P.prob E :=
  P.expect_nonneg (fun x => by split_ifs <;> norm_num)

theorem prob_mono (P : FiniteLaw X) {E F : X → Prop} (h : ∀ x, E x → F x) : P.prob E ≤ P.prob F := by
  apply P.expect_mono
  intro x
  by_cases he : E x
  · simp only [ite_eq_left he,ite_eq_left (h x he),le_refl]
  · simp only [ite_eq_right he]; split_ifs <;> norm_num

theorem prob_or (P : FiniteLaw X) (E F : X → Prop) :
    P.prob (fun x => E x ∨ F x) ≤ P.prob E+P.prob F := by
  simp only [prob]
  rw [← expect_add]
  apply P.expect_mono
  intro x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he,hf]

theorem prod_expect (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X × Y → ℝ) :
    (P.prod Q).expect f=P.expect (fun x => Q.expect (fun y => f (x,y))) := by
  simp only [expect,prod,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem prod_expect_fst (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X → ℝ) :
    (P.prod Q).expect (fun z => f z.1)=P.expect f := by
  simp only [prod_expect,expect_const]

end FiniteLaw

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic.FiniteLaw
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem iid_expect_equiv (P : FiniteLaw X) (e : I ≃ J) (f : (J → X) → ℝ) :
    (P.iid I).expect (fun z => f (z ∘ e.symm))=(P.iid J).expect f := by
  classical
  unfold expect iid pi
  apply Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl X))
  intro z
  dsimp only [Equiv.arrowCongr_apply,Equiv.coe_refl,Function.comp_def]
  congr 1
  exact (e.symm.prod_comp (fun i => P.weight (z i))).symm

theorem iid_expect_restrict (P : FiniteLaw X) (s : I → Prop)
    (f : ({i // s i} → X) → ℝ) :
    (P.iid I).expect (fun z => f (fun i => z i))=(P.iid {i // s i}).expect f := by
  classical
  let Q := P.iid {i // ¬s i}
  calc
    _ = ((P.iid {i // s i}).prod Q).expect (fun z => f z.1) := by
      unfold expect iid pi prod
      apply Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd s (fun _ => X))
      intro z
      change (∏ i, P.weight (z i))*f (fun i => z i) =
        ((∏ i : {i // s i}, P.weight (z i))*(∏ i : {i // ¬s i}, P.weight (z i)))*f (fun i => z i)
      congr 1
      exact (Fintype.prod_subtype_mul_prod_subtype s (fun i => P.weight (z i))).symm
    _ = _ := prod_expect_fst _ _ f

theorem iid_expect_injective (P : FiniteLaw X) (e : J → I) (he : Function.Injective e)
    (f : (J → X) → ℝ) :
    (P.iid I).expect (fun z => f (z ∘ e))=(P.iid J).expect f := by
  classical
  let : Fintype {i // i∈Set.range e} := Subtype.fintype _
  let k := Equiv.ofInjective e he
  have H := P.iid_expect_restrict (fun i => i∈Set.range e) (fun z => f (z ∘ k))
  have H' := P.iid_expect_equiv k.symm f
  apply H.trans
  unfold expect iid pi at H' ⊢
  simp only [Equiv.symm_symm] at H'
  refine Eq.trans ?_ H'
  apply Finset.sum_congr
  · ext z; simp
  · intro z _
    congr 1
    apply Finset.prod_congr
    · ext i; simp
    · intros; rfl

theorem iid_expect_single (P : FiniteLaw X) (i : I) (f : X → ℝ) :
    (P.iid I).expect (fun z => f (z i))=P.expect f := by
  classical
  have H := P.iid_expect_injective (fun _ : Unit => i)
    (fun _ _ _ => Subsingleton.elim _ _) (fun z => f (z ()))
  change (P.iid I).expect (fun z => f ((z ∘ (fun _ : Unit => i)) ())) = _
  rw [H]
  unfold expect iid pi
  simp only [Fintype.prod_unique]
  apply Fintype.sum_equiv (Equiv.funUnique Unit X)
  intro z
  rfl

theorem iid_expect_fin_succ (P : FiniteLaw X) (p : ℕ) (f : (Fin (p+1) → X) → ℝ) :
    (P.iid (Fin (p+1))).expect f=
      (P.iid (Fin p)).expect (fun z => P.expect (fun a => f (Fin.snoc z a))) := by
  classical
  unfold expect iid pi
  calc
    _ = ∑ z : (Fin p → X) × X, (∏ i, P.weight (z.1 i))*P.weight z.2*f (Fin.snoc z.1 z.2) := by
      apply Fintype.sum_equiv ((Fin.snocEquiv (fun _ : Fin (p+1) => X)).symm.trans (Equiv.prodComm _ _))
      intro z
      simp only [Equiv.trans_apply,Equiv.prodComm_apply,Fin.snocEquiv_symm_apply,Prod.swap,Fin.prod_univ_castSucc]
      simp only [Fin.snoc_init_self,Fin.init]
    _ = _ := by simp only [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

end SK.Analytic.FiniteLaw

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteIndicators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Classical
namespace SK.Analytic.FiniteLaw
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
theorem expect_indicator_eq_prob (P : FiniteLaw X) (E : X → Prop) [DecidablePred E] :
    P.expect (fun x => if E x then 1 else 0)=P.prob E := by
  unfold prob
  congr 1
  funext x
  split_ifs <;> rfl

end SK.Analytic.FiniteLaw

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FiniteSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Classical
namespace SK.Analytic.FiniteLaw
variable {X Y I J : Type*} [Fintype X] [Fintype Y] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem expect_expect_comm (P : FiniteLaw X) (Q : FiniteLaw Y) (f : X → Y → ℝ) :
    P.expect (fun x => Q.expect (f x))=Q.expect (fun y => P.expect (fun x => f x y)) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end SK.Analytic.FiniteLaw

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

theorem iid_gibbs_replica {n d : ℕ} (β : ℝ) (J : Disorder n) (S : Finset (ReplicaConfig n d)) :
    ((gibbsFiniteLaw β J).iid (Fin d)).prob (fun z => z∈S)=replicaGibbsMass β J S := by
  classical
  unfold FiniteLaw.prob FiniteLaw.expect FiniteLaw.iid FiniteLaw.pi gibbsFiniteLaw replicaGibbsMass
  simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowCDFMass
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

theorem cdf_sub_le_real_Icc (μ : ProbabilityMeasure ℝ) {a b : ℝ} (hab : a≤b) :
    cdf (μ : Measure ℝ) b-cdf (μ : Measure ℝ) a≤(μ : Measure ℝ).real (Icc a b) := by
  have H := (cdf (μ : Measure ℝ)).measure_Ioc a b
  rw [measure_cdf] at H
  have He : (μ : Measure ℝ).real (Ioc a b)=cdf (μ : Measure ℝ) b-cdf (μ : Measure ℝ) a := by
    rw [measureReal_def,H,ENNReal.toReal_ofReal (sub_nonneg.mpr ((cdf (μ : Measure ℝ)).mono hab))]
  rw [← He]
  exact measureReal_mono Ioc_subset_Icc_self

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
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFZeroSupport
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

theorem cdf_pos_of_zero_mem_support (μ : ProbabilityMeasure ℝ)
    (h0 : (0:ℝ)∈(μ : Measure ℝ).support) {s : ℝ} (hs : 0 < s) :
    0 < cdf (μ : Measure ℝ) s := by
  have H : 0<(μ : Measure ℝ) (Iic s) :=
    (Measure.mem_support_iff_forall (μ:=(μ : Measure ℝ)) 0).mp h0 _ (Iic_mem_nhds hs)
  rw [cdf_eq_real,measureReal_def]
  exact ENNReal.toReal_pos H.ne' (measure_ne_top _ _)

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
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_NarrowGibbsGap
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

theorem narrowLocking_pressure_gap {β t₀ : ℝ} (hβ : β≠0)
    (ht₀ : 0<t₀) (ht₁ : 3*t₀<1) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    (h0 : (0:ℝ)∈(μ : Measure ℝ).support)
    (hS : ∀ q∈Icc (0:ℝ) 1,scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) q=
      (∫ x in q..1,cdf (μ : Measure ℝ) x)+cdf (μ : Measure ℝ) q*(q-scalarCDFOverlap β (cdf (μ : Measure ℝ)) q))
    (hΓ : ∀ r∈Ioo (t₀/2) (3*t₀),scalarCDFOverlap β (cdf (μ : Measure ℝ)) r=r) :
    ∃ ρ₀ c : ℝ,0<ρ₀ ∧ 0 < c ∧ ∀ (n : ℕ),0<n → ∀ ρ : ℝ,0<ρ → ρ≤ρ₀ →
      ∀ s∈narrowLockingSet n μ t₀ ρ,
        |tripleQ s-scalarCDFOverlap β (cdf (μ : Measure ℝ)) (tripleQ s)|≤ρ^13 →
        matrixConstrainedPressure n 3 β (replicaGram s)≤3*finiteParisiInf β-c*ρ^43 := by
  let α := cdf (μ : Measure ℝ)
  have hα (z) : α z∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have hm : 0<α (t₀/2) := cdf_pos_of_zero_mem_support μ h0 (half_pos ht₀)
  obtain ⟨r₀,c,hr₀,hc,H⟩ := narrowConstrainedPressure_scaled_gap hβ hm
  refine ⟨min r₀ (min 1 (t₀/2)),c,lt_min hr₀ (lt_min zero_lt_one (half_pos ht₀)),hc,?_⟩
  intro n hn ρ hρ hρ₀ s hs hdev
  obtain ⟨hr,hmass,hrq,hδ,hδ'⟩ := (Finset.mem_filter.mp hs).2
  have hρ1 : ρ≤1 := (le_min_iff.mp (le_min_iff.mp hρ₀).2).1
  have hρt : ρ≤t₀/2 := (le_min_iff.mp (le_min_iff.mp hρ₀).2).2
  have hpow : ρ^8≤ρ := pow_le_of_le_one hρ.le hρ1 (by decide)
  have hq₁ : tripleQ s≤1 := (abs_le.mp (abs_overlap_le_one (s 1) (s 2))).2
  have hq₀ : 0≤tripleQ s := by linarith only [hr.1,hrq,hρ,ht₀]
  let u := (tripleR s+3*t₀)/2
  have hru : tripleR s<u := by dsimp only [u]; linarith only [hr.2]
  have hu : u<3*t₀ := by dsimp only [u]; linarith only [hr.2]
  have HG := H α hα (supported_probability_cdf_one μ hμ) n hn ρ (tripleR s) (tripleQ s) u (tripleDelta s)
    hρ (le_min_iff.mp hρ₀).1 (hpow.trans (hρt.trans hr.1.le)) hrq hq₁ hru (hu.le.trans ht₁.le)
    (fun x hx => hΓ x ⟨hr.1.trans_le hx.1,hx.2.trans_lt hu⟩)
    (α.mono hr.1.le) (hS _ ⟨hq₀,hq₁⟩) hdev
    ((cdf_sub_le_real_Icc μ (by linarith only [pow_nonneg hρ.le 8])).trans hmass) hδ'
    (by rw [← replicaGram_triple_overlap hn]; exact replicaGram_feasible s)
  rw [hmin,← replicaGram_triple_overlap hn] at HG
  have HD := pow_le_pow_left₀ (pow_nonneg hρ.le 20) hδ 2
  rw [sq_abs] at HD
  have HC := mul_le_mul_of_nonneg_left HD (show 0 ≤ c*ρ^3 by positivity)
  have HE : c*ρ^3*(ρ^20)^2=c*ρ^43 := by ring
  rw [HE] at HC
  linarith only [HG,HC]

theorem narrow_annulus_locking {β t₀ : ℝ} (hβ : 0<β)
    (ht₀ : 0<t₀) (ht₁ : 3*t₀<1) (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    (h0 : (0:ℝ)∈(μ : Measure ℝ).support)
    (hS : ∀ q∈Icc (0:ℝ) 1,scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) q=
      (∫ x in q..1,cdf (μ : Measure ℝ) x)+cdf (μ : Measure ℝ) q*(q-scalarCDFOverlap β (cdf (μ : Measure ℝ)) q))
    (hΓ : ∀ r∈Ioo (t₀/2) (3*t₀),scalarCDFOverlap β (cdf (μ : Measure ℝ)) r=r) :
    ∀ᶠ n : ℕ in atTop,
      (∫ J,replicaGibbsMass β J (narrowLockingSet n μ t₀ ((n:ℝ)^(-kappa))) ∂disorderLaw n)≤
        Real.exp (-(n:ℝ)^((4:ℝ)/5)) := by
  classical
  let α := cdf (μ : Measure ℝ)
  have hα (z) : α z∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  obtain ⟨ρ₀,c,hρ₀,hc,Hgap⟩ := narrowLocking_pressure_gap hβ.ne' ht₀ ht₁ μ hμ hmin h0 hS hΓ
  have HP := eventual_pairMismatch_polynomial_bound (A:=1) (a:=13*kappa) (t:=(4:ℝ)/5) (ε:=1/2)
    hβ zero_lt_one (by norm_num [kappa]) (by norm_num [kappa]) (by norm_num [kappa]) (by norm_num)
    α hα (supported_probability_cdf_one μ hμ) hmin
  have HT := eventual_replicaGibbsMass_polynomial_gap (c:=c) (a:=43*kappa) (t:=(4:ℝ)/5) (ε:=1/4)
    hβ 3 3 (by decide) hc (by norm_num [kappa]) (by norm_num [kappa]) (by norm_num [kappa]) (by norm_num)
  have Hρ := (tendsto_rpow_neg_atTop (by norm_num [kappa] : 0<kappa)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [HP,HT,Hρ.eventually_le_const hρ₀,eventually_gt_atTop (0:ℕ)] with n hnP hnT hρn hn0
  have hp : (0:ℝ)<n := by exact_mod_cast hn0
  let ρ := (n:ℝ)^(-kappa)
  have hρ : 0<ρ := Real.rpow_pos_of_pos hp _
  have Hpow (k : ℕ) : ρ^k=(n:ℝ)^(-((k:ℝ)*kappa)) := by
    rw [← Real.rpow_natCast ρ k,← Real.rpow_mul hp.le]
    congr 1
    ring
  let S := narrowLockingSet n μ t₀ ρ
  let T := S.filter (fun s => |tripleQ s-scalarCDFOverlap β α (tripleQ s)|≤ρ^13)
  have HT' : (∫ J,replicaGibbsMass β J T ∂disorderLaw n)≤(1/4)*Real.exp (-(n:ℝ)^((4:ℝ)/5)) := by
    apply hnT (Fin 3 → Fin (n+1)) (by simp) tripleReplicaCode (fun s t H => tripleReplicaCode_gram hn0 H)
    intro s hs
    have HH := Finset.mem_filter.mp hs
    have HG := Hgap n hn0 ρ hρ hρn s HH.1 HH.2
    simpa only [Hpow 43,Nat.cast_ofNat] using HG
  have Hsplit := replicaGibbsMass_integral_or_or_flip (0:Fin 3) β S T
    (Finset.univ.filter (fun s : ReplicaConfig n 3 => Fin.tail s∈pairMismatchSet n β α (ρ^13)))
    (fun s hs => by
      by_cases hg : |tripleQ s-scalarCDFOverlap β α (tripleQ s)|≤ρ^13
      · exact Or.inl (Finset.mem_filter.mpr ⟨hs,hg⟩)
      · right; right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,(not_le.mp hg).le⟩⟩
        obtain ⟨hr,hm,hrq,hd⟩ := (Finset.mem_filter.mp hs).2
        change 0≤tripleQ s
        linarith only [hr.1,hrq,hρ,ht₀])
  simp_rw [replicaGibbsMass_tail,Hpow 13] at Hsplit
  norm_num only [Nat.cast_ofNat,one_mul] at Hsplit hnP
  linarith only [Hsplit,HT',hnP]

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
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_CoverageSchedule
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

 theorem gibbs_prob_eq_finiteMass {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (gibbsFiniteLaw β J).prob E=finiteMass (gibbs β J) (Finset.univ.filter E) := by
  unfold FiniteLaw.prob FiniteLaw.expect gibbsFiniteLaw finiteMass
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_filter]

 theorem gibbs_coverage_predicate {n : ℕ} (β : ℝ) (J : Disorder n) (q a δ : ℝ)
    (h : ∀ S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
      finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<a))<δ)
    (E : Config n → Prop) :
    (gibbsFiniteLaw β J).prob (fun x => E x ∧ (gibbsFiniteLaw β J).prob (fun y => E y ∧ q≤|overlap x y|)<a)≤δ := by
  have H := h (Finset.univ.filter E)
  simp_rw [Finset.filter_filter] at H
  refine le_trans ?_ H.le
  apply le_of_eq
  rw [gibbs_prob_eq_finiteMass]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,gibbs_prob_eq_finiteMass]
  apply and_congr_right
  intro _
  apply Iff.of_eq
  apply congrArg (fun r : ℝ => r<a)
  apply congrArg (finiteMass (gibbs β J))
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_FiniteCoverageMixing
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
namespace FiniteLaw

 theorem cover_mixed_mass {X Y : Type*} [Fintype X] [Fintype Y]
    (P : FiniteLaw X) (Q : FiniteLaw Y) (R : X → Y → Prop) (E : X → Prop)
    {a δ : ℝ} (ha : 0<a) (hcov : P.prob (fun x => Q.prob (R x)<a)≤δ) :
    P.prob E≤δ+Q.expect (fun y => P.prob (fun x => E x ∧ R x y))/a := by
  have H := P.expect_mono (f:=fun x => a*(if E x then 1 else 0))
    (g:=fun x => a*(if Q.prob (R x)<a then 1 else 0)+Q.prob (fun y => E x ∧ R x y)) (fun x => by
      by_cases hx : E x
      · simp only [hx,true_and,ite_true,mul_one]
        by_cases hc : Q.prob (R x)<a
        · simp only [ite_eq_left hc,mul_one]
          linarith only [Q.prob_nonneg (R x)]
        · simp only [ite_eq_right hc,mul_zero,zero_add]
          exact le_of_not_gt hc
      · simp only [hx,false_and,ite_false,mul_zero,prob_false,add_zero]
        split_ifs <;> simp only [mul_one,mul_zero] <;> linarith only [ha])
  rw [expect_const_mul,expect_add,expect_const_mul] at H
  simp only [expect_indicator_eq_prob] at H
  have he : P.expect (fun x => Q.prob (fun y => E x ∧ R x y))=
      Q.expect (fun y => P.prob (fun x => E x ∧ R x y)) := P.expect_expect_comm Q _
  rw [he] at H
  have HC := mul_le_mul_of_nonneg_left hcov ha.le
  apply (mul_le_mul_iff_right₀ ha).mp
  rw [mul_add,mul_div_cancel₀ _ ha.ne']
  nlinarith only [H,HC]

 theorem expect_involution {X : Type*} [Fintype X] (P : FiniteLaw X)
    (T : X → X) (hT : Function.Involutive T) (hP : ∀x,P.weight (T x)=P.weight x) (f : X → ℝ) :
    P.expect (fun x => f (T x))=P.expect f := by
  let e : X ≃ X := ⟨T,T,hT,hT⟩
  apply Fintype.sum_equiv e
  intro x
  change P.weight x*f (T x)=P.weight (T x)*f (T x)
  rw [hP]

 theorem iid_pair_expect {X : Type*} [Fintype X] (P : FiniteLaw X) (f : X → X → ℝ) :
    (P.iid (Fin 2)).expect (fun s => f (s 0) (s 1))=P.expect (fun x => P.expect (f x)) := by
  rw [iid_expect_fin_succ P 1]
  change (P.iid (Fin 1)).expect (fun s => P.expect (fun y => f (s 0) y))=P.expect (fun x => P.expect (f x))
  exact iid_expect_single P (0:Fin 1) (fun x => P.expect (f x))

end FiniteLaw

 theorem gibbs_prob_eq_sum {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (gibbsFiniteLaw β J).prob E=∑x,if E x then gibbs β J x else 0 := by
  simp only [FiniteLaw.prob,FiniteLaw.expect,gibbsFiniteLaw,mul_ite,mul_one,mul_zero]

 theorem gibbs_expect_flip {n : ℕ} (β : ℝ) (J : Disorder n) (f : Config n → ℝ) :
    (gibbsFiniteLaw β J).expect (fun v => f (flip v))=(gibbsFiniteLaw β J).expect f :=
  (gibbsFiniteLaw β J).expect_involution flip flip_flip (gibbs_flip β J) f

 theorem mixed_abs_neighbor_le_signed {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop)
    {q a₁ : ℝ} (haq : a₁<q) (v : Config n) :
    (gibbsFiniteLaw β J).prob (fun x => E x ∧ q≤|overlap x v|)≤
      (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ E x)+
        (gibbsFiniteLaw β J).prob (fun x => a₁<overlap (flip v) x ∧ E x) := by
  refine ((gibbsFiniteLaw β J).prob_mono (fun x hx => ?_)).trans ((gibbsFiniteLaw β J).prob_or _ _)
  rw [overlap_comm] at hx
  rcases le_abs.mp hx.2 with h|h
  · exact Or.inl ⟨haq.trans_le h,hx.1⟩
  · apply Or.inr
    refine ⟨?_,hx.1⟩
    rw [overlap_comm,overlap_flip_right,overlap_comm]
    linarith only [haq,h]

 theorem covered_mixed_mass_le_signed_average {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop)
    {q a₁ a δ : ℝ} (haq : a₁<q) (ha : 0<a)
    (hcov : (gibbsFiniteLaw β J).prob (fun x => (gibbsFiniteLaw β J).prob (fun y => q≤|overlap x y|)<a)≤δ) :
    (gibbsFiniteLaw β J).prob E≤δ+(2/a)*(gibbsFiniteLaw β J).expect (fun v =>
      (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ E x)) := by
  have H := (gibbsFiniteLaw β J).cover_mixed_mass (gibbsFiniteLaw β J) (fun x y => q≤|overlap x y|) E ha hcov
  have HB := (gibbsFiniteLaw β J).expect_mono (fun v => mixed_abs_neighbor_le_signed β J E haq v)
  rw [FiniteLaw.expect_add] at HB
  have HF := gibbs_expect_flip β J (fun v => (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ E x))
  rw [HF] at HB
  refine H.trans ?_
  apply add_le_add_right
  have HD := div_le_div_of_nonneg_right HB ha.le
  refine HD.trans_eq ?_
  ring

 theorem pairStrip_expect {n : ℕ} (β : ℝ) (J : Disorder n) (a₀ a₁ : ℝ) :
    (gibbsFiniteLaw β J).expect (fun v => (gibbsFiniteLaw β J).prob (fun x => a₀≤overlap v x ∧ overlap v x≤a₁))=
      replicaGibbsMass β J (pairStripSet n a₀ a₁) := by
  rw [← iid_gibbs_replica β J (pairStripSet n a₀ a₁)]
  simp only [pairStripSet,Finset.mem_filter,Finset.mem_univ,true_and,FiniteLaw.prob]
  convert ((gibbsFiniteLaw β J).iid_pair_expect (fun v x => if a₀≤overlap v x ∧ overlap v x≤a₁ then 1 else 0)).symm using 1
  all_goals try with_reducible_and_instances rfl
  all_goals congr 1
  · funext v
    congr 1
    funext x
    split_ifs <;> rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_HighProbability
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

theorem high_probability_inter (C D : (n : ℕ) → Set (Disorder n))
    (hD : ∀n,MeasurableSet (D n))
    (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (hD1 : Tendsto (fun n => (disorderLaw n).real (D n)) atTop (𝓝 1)) :
    Tendsto (fun n => (disorderLaw n).real (C n ∩ D n)) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g:=fun n => (disorderLaw n).real (C n)+(disorderLaw n).real (D n)-1)
    (h:=fun _ => (1:ℝ))
  · convert (hC1.add hD1).sub_const 1 using 1; norm_num
  · exact tendsto_const_nhds
  · intro n
    have H := measureReal_union_add_inter (μ:=disorderLaw n) (s:=C n) (hD n)
    have H1 : (disorderLaw n).real (C n ∪ D n)≤1 := measureReal_le_one
    linarith only [H,H1]
  · intro n; exact measureReal_le_one

 theorem real_markov_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hm : Measurable f) (h0 : ∀x,0≤f x)
    {a : ℝ} (ha : 0<a) : μ.real {x | a<f x}≤(∫x,f x ∂μ)/a := by
  have hA : MeasurableSet {x | a<f x} := measurableSet_lt measurable_const hm
  apply (le_div_iff₀ ha).mpr
  have H : (∫x,({x | a<f x}).indicator (fun _ => a) x ∂μ)≤∫x,f x ∂μ := by
    apply integral_mono ((integrable_const a).indicator hA) hf
    intro x
    by_cases hx : a<f x
    · simpa only [Set.indicator_of_mem (show x∈{x | a<f x} from hx)] using hx.le
    · simpa only [Set.indicator_of_notMem (show x∉{x | a<f x} from hx)] using h0 x
  simpa only [integral_indicator_const _ hA,smul_eq_mul,mul_comm] using H

 theorem stretched_exp_decay {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => Real.exp (-c*levelLogScale n)) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp (stretchedLogScale_tendsto.const_mul_atTop_of_neg (neg_neg_of_pos hc))

 theorem faster_stretched_decay {u : ℝ} (hu : kappa<u) (A K : ℝ) :
    Tendsto (fun n : ℕ => K*Real.exp (A*levelLogScale n-(n:ℝ)^u)) atTop (𝓝 0) := by
  have hu0 : 0<u := (by norm_num [kappa] : (0:ℝ)<kappa).trans hu
  have H : Tendsto (fun n : ℕ => Real.exp (-(1/2:ℝ)*(n:ℝ)^u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (((tendsto_rpow_atTop hu0).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul_atTop_of_neg (by norm_num))
  have H0 : Tendsto (fun n : ℕ => Real.exp (A*levelLogScale n-(n:ℝ)^u)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => (Real.exp_pos _).le)) _ H
    filter_upwards [eventually_const_rpow_le hu A (by norm_num : (0:ℝ)<1/2)] with n hn
    apply Real.exp_le_exp.mpr
    change A*(n:ℝ)^kappa-(n:ℝ)^u≤-(1/2:ℝ)*(n:ℝ)^u
    linarith only [hn]
  simpa only [mul_zero] using H0.const_mul K

 theorem high_probability_small_replica {d : ℕ} (β : ℝ) (S : (n : ℕ) → Finset (ReplicaConfig n d))
    {u : ℝ} (hu : kappa<u) (K A : ℝ)
    (h : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (S n) ∂disorderLaw n)≤K*Real.exp (-(n:ℝ)^u)) :
    Tendsto (fun n => (disorderLaw n).real {J | replicaGibbsMass β J (S n)≤Real.exp (-A*levelLogScale n)}) atTop (𝓝 1) := by
  have HC : Tendsto (fun n => (disorderLaw n).real {J | Real.exp (-A*levelLogScale n) < replicaGibbsMass β J (S n)}) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => measureReal_nonneg)) _ (faster_stretched_decay hu A K)
    filter_upwards [h] with n hn
    refine (real_markov_bound (disorderLaw n) (replicaGibbsMass_integrable β (S n))
      (continuous_replicaGibbsMass β (S n)).measurable (fun J => replicaGibbsMass_nonneg β J (S n)) (Real.exp_pos _)).trans ?_
    calc
      _ ≤ (K*Real.exp (-(n:ℝ)^u))/Real.exp (-A*levelLogScale n) := div_le_div_of_nonneg_right hn (Real.exp_pos _).le
      _ = K*Real.exp (A*levelLogScale n-(n:ℝ)^u) := by rw [mul_div_assoc,← Real.exp_sub]; congr 2; ring
  have H := (tendsto_const_nhds (x:=(1:ℝ))).sub HC
  convert H using 1
  · funext n
    have hM : MeasurableSet {J | Real.exp (-A*levelLogScale n) < replicaGibbsMass β J (S n)} :=
      measurableSet_lt measurable_const (continuous_replicaGibbsMass β (S n)).measurable
    rw [← probReal_compl_eq_one_sub hM]
    congr 1
    ext J
    simp only [mem_ofPred_eq,mem_compl_iff,not_lt]
  · norm_num

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_KernelEvents
attribute [-instance] _root_.OAI.SK.disorderLaw_isGaussian _root_.OAI.SK.disorderPairLaw_probability
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

theorem kernelEvent_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : 0 ≤ kernelEvent β J A k x := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact discreteKernel_nonneg β J k x y
  · exact le_rfl

theorem kernelEvent_le_one {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] (k : ℕ) (x : Config n) : kernelEvent β J A k x ≤ 1 := by
  rw [← discreteKernel_sum hn β J k x]
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact le_rfl
  · exact discreteKernel_nonneg β J k x y

theorem kernelEvent_zero {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (x : Config n) : kernelEvent β J A 0 x = if A x then 1 else 0 := by
  classical
  unfold kernelEvent
  simp only [discreteKernel]
  by_cases h : A x
  · rw [ite_eq_left h]
    have he (y : Config n) : (if A y then if x=y then (1:ℝ) else 0 else 0) = if x=y then 1 else 0 := by
      by_cases hxy : x=y
      · subst y; simp only [h,ite_true]
      · simp only [ite_eq_right hxy,ite_self]
    simp_rw [he]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hxy : x=y
    · subst y; simp only [ite_eq_right h]
    · simp only [ite_eq_right hxy,ite_self]

theorem kernelEvent_succ {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : kernelEvent β J A (k+1) x =
      ∑ z : Config n, heatBath β J x z*kernelEvent β J A k z := by
  unfold kernelEvent
  simp only [discreteKernel,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp only [Finset.sum_const_zero]

theorem kernelEvent_stationary {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] (k : ℕ) :
    (∑ x : Config n, gibbs β J x*kernelEvent β J A k x) =
      ∑ y : Config n, if A y then gibbs β J y else 0 := by
  unfold kernelEvent
  simp only [Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs
  · exact discreteKernel_stationary hn β J k y
  · exact Finset.sum_const_zero

theorem occupation_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : 0 ≤ occupation β J A k x :=
  Finset.sum_nonneg (fun i _ => kernelEvent_nonneg β J A i x)

theorem one_le_occupation {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) (hx : A x) : 1 ≤ occupation β J A k x := by
  have H := Finset.single_le_sum (f := fun i => kernelEvent β J A i x)
    (fun i (_ : i ∈ Finset.range (k+1)) => kernelEvent_nonneg β J A i x)
    (show 0 ∈ Finset.range (k+1) by simp)
  simpa only [kernelEvent_zero,ite_eq_left hx,occupation] using H

theorem occupation_recursion {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    (k : ℕ) (x : Config n) : occupation β J A (k+1) x =
      kernelEvent β J A 0 x+∑ z : Config n, heatBath β J x z*occupation β J A k z := by
  unfold occupation
  rw [Finset.sum_range_succ']
  simp_rw [kernelEvent_succ,Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem occupation_stationary {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] (k : ℕ) :
    (∑ x : Config n, gibbs β J x*occupation β J A k x) =
      ((k+1:ℕ):ℝ)*(∑ y : Config n, if A y then gibbs β J y else 0) := by
  unfold occupation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [kernelEvent_stationary hn]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [Finset.mul_sum]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_TVSignBridge
attribute [-instance] _root_.OAI.SK.disorderLaw_isGaussian _root_.OAI.SK.disorderPairLaw_probability
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

theorem finite_event_le_tv {Ω : Type*} [Fintype Ω] (p q : Ω → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) (A : Ω → Prop) [DecidablePred A] :
    (∑ x, if A x then q x else 0)-(∑ x, if A x then p x else 0) ≤
      (1/2:ℝ)*∑ x, |p x-q x| := by
  have hsum : ∑ x, (q x-p x) = 0 := by rw [Finset.sum_sub_distrib,hq,hp,sub_self]
  have ht (x : Ω) : 2*(if A x then q x-p x else 0)-(q x-p x) ≤ |q x-p x| := by
    by_cases hx : A x
    · simp only [ite_eq_left hx]
      linarith [le_abs_self (q x-p x)]
    · simp only [ite_eq_right hx,mul_zero,zero_sub]
      exact neg_le_abs (q x-p x)
  have H := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset Ω)) => ht x)
  have he : (∑ x, if A x then q x-p x else 0) =
      (∑ x, if A x then q x else 0)-(∑ x, if A x then p x else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,hsum,sub_zero,he] at H
  have ha : (∑ x, |q x-p x|) = ∑ x, |p x-q x| := by
    apply Finset.sum_congr rfl
    intro x _
    exact abs_sub_comm _ _
  rw [ha] at H
  linarith

theorem gibbs_nonpositive_overlap_mass {n : ℕ} (β : ℝ) (J : Disorder n) (v : Config n) :
    (1/2:ℝ) ≤ ∑ y : Config n, if overlap v y ≤ 0 then gibbs β J y else 0 := by
  classical
  let e : Config n ≃ Config n := ⟨flip,flip,flip_flip,flip_flip⟩
  have he : (∑ y : Config n, if -overlap v y ≤ 0 then gibbs β J y else 0) =
      ∑ y : Config n, if overlap v y ≤ 0 then gibbs β J y else 0 := by
    calc
      _ = ∑ y : Config n, if overlap v (e y) ≤ 0 then gibbs β J (e y) else 0 := by
        change _ = ∑ y : Config n, if overlap v (flip y) ≤ 0 then gibbs β J (flip y) else 0
        simp only [overlap_flip_right,gibbs_flip]
      _ = _ := Equiv.sum_comp e (fun y => if overlap v y ≤ 0 then gibbs β J y else 0)
  have ht (y : Config n) : gibbs β J y ≤
      (if overlap v y ≤ 0 then gibbs β J y else 0)+
      (if -overlap v y ≤ 0 then gibbs β J y else 0) := by
    by_cases h : overlap v y ≤ 0
    · simp only [ite_eq_left h]
      split_ifs <;> linarith [gibbs_pos β J y]
    · have h' : -overlap v y ≤ 0 := by linarith [lt_of_not_ge h]
      simp only [ite_eq_right h,ite_eq_left h',zero_add,le_refl]
  have H := Finset.sum_le_sum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) => ht y)
  rw [gibbs_sum,Finset.sum_add_distrib,he] at H
  linarith

theorem discrete_sign_mass_of_tv {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (x v : Config n) (k : ℕ) (hTV : discreteDistance β J x k ≤ (1/4:ℝ)) :
    (1/4:ℝ) ≤ ∑ y : Config n, if overlap v y ≤ 0 then discreteKernel β J k x y else 0 := by
  have H := finite_event_le_tv (discreteKernel β J k x) (gibbs β J)
    (discreteKernel_sum hn β J k x) (gibbs_sum β J) (fun y => overlap v y ≤ 0)
  have HG := gibbs_nonpositive_overlap_mass β J v
  change _ ≤ discreteDistance β J x k at H
  linarith

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_BarrierCrossing
attribute [-instance] _root_.OAI.SK.disorderLaw_isGaussian _root_.OAI.SK.disorderPairLaw_probability
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

theorem signEvent_le_stripOccupation {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀)
    (k : ℕ) (x : Config n) (hx : a₁ < overlap v x) :
    kernelEvent β J (fun y => overlap v y ≤ 0) k x ≤
      occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) k x := by
  have ha₁ : 0 < a₁ := by
    have : 0 < (2:ℝ)/(n:ℝ) := by positivity
    linarith
  induction k generalizing x with
  | zero =>
    rw [kernelEvent_zero,ite_eq_right (by linarith : ¬overlap v x ≤ 0)]
    exact occupation_nonneg _ _ _ _ _
  | succ k ih =>
    rw [kernelEvent_succ,occupation_recursion]
    have HH : (∑ z : Config n, heatBath β J x z*kernelEvent β J (fun y => overlap v y ≤ 0) k z) ≤
        ∑ z : Config n, heatBath β J x z*occupation β J
          (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) k z := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hlow : overlap v z < a₀
      · have hz : heatBath β J x z = 0 := by
          by_contra hne
          have hp := lt_of_le_of_ne (heatBath_nonneg β J x z) (Ne.symm hne)
          have hs := heatBath_overlap_step hn β J v x z hp
          have hs' := neg_le_abs (overlap v z-overlap v x)
          linarith
        simp only [hz,zero_mul,le_refl]
      · by_cases hhigh : a₁ < overlap v z
        · exact mul_le_mul_of_nonneg_left (ih z hhigh) (heatBath_nonneg β J x z)
        · have hz : a₀ ≤ overlap v z ∧ overlap v z ≤ a₁ := ⟨le_of_not_gt hlow,le_of_not_gt hhigh⟩
          exact mul_le_mul_of_nonneg_left ((kernelEvent_le_one hn β J _ k z).trans
            (one_le_occupation β J _ k z hz)) (heatBath_nonneg β J x z)
    exact HH.trans (le_add_of_nonneg_left (kernelEvent_nonneg _ _ _ _ _))

theorem quarter_le_stripOccupation_of_tv {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀)
    (k : ℕ) (x : Config n) (hx : a₁ < overlap v x)
    (hTV : discreteDistance β J x k ≤ (1/4:ℝ)) :
    (1/4:ℝ) ≤ occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) k x :=
  (discrete_sign_mass_of_tv hn β J x v k hTV).trans
    (signEvent_le_stripOccupation hn β J v ha₀ hgap k x hx)

theorem mass_mixed_high_le_strip {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀) (k : ℕ) :
    (∑ x : Config n, if a₁ < overlap v x ∧ discreteDistance β J x k ≤ (1/4:ℝ)
      then gibbs β J x else 0) ≤ 4*((k+1:ℕ):ℝ)*
        (∑ y : Config n, if a₀ ≤ overlap v y ∧ overlap v y ≤ a₁ then gibbs β J y else 0) := by
  have HH := Finset.sum_le_sum (s := (Finset.univ : Finset (Config n)))
    (f := fun x => if a₁ < overlap v x ∧ discreteDistance β J x k ≤ (1/4:ℝ) then gibbs β J x else 0)
    (g := fun x => 4*(gibbs β J x*occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) k x))
    (fun x _ => show _ ≤ _ from by
      split_ifs with hx
      · have H := quarter_le_stripOccupation_of_tv hn β J v ha₀ hgap k x hx.1 hx.2
        nlinarith [mul_le_mul_of_nonneg_left H (le_of_lt (gibbs_pos β J x))]
      · exact mul_nonneg (by norm_num) (mul_nonneg (le_of_lt (gibbs_pos β J x))
          (occupation_nonneg _ _ _ _ _)))
  rw [← Finset.mul_sum,occupation_stationary hn] at HH
  simpa only [mul_assoc] using HH

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_Uniformization
attribute [-instance] _root_.OAI.SK.disorderLaw_isGaussian _root_.OAI.SK.disorderPairLaw_probability
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

theorem clockWeight_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ clockWeight a k := by
  unfold clockWeight
  positivity

theorem clockWeight_hasSum (a : ℝ) : HasSum (clockWeight a) 1 := by
  have H := (NormedSpace.expSeries_div_hasSum_exp a).mul_left (Real.exp (-a))
  rw [← Real.exp_eq_exp_ℝ,← Real.exp_add,neg_add_cancel,Real.exp_zero] at H
  unfold clockWeight
  simpa only [mul_div_assoc] using H

theorem clockWeight_sum (a : ℝ) : ∑' k : ℕ, clockWeight a k = 1 := (clockWeight_hasSum a).tsum_eq

theorem uniformization_summable {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    {t : ℝ} (ht : 0 ≤ t) (x y : Config n) :
    Summable (fun k : ℕ => clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (clockWeight_nonneg (by positivity) k)
    (discreteKernel_nonneg β J k x y)) (fun k => ?_) (clockWeight_hasSum ((n:ℝ)*t)).summable
  exact mul_le_of_le_one_right (clockWeight_nonneg (by positivity) k) (discreteKernel_le_one hn β J k x y)

theorem continuousKernel_eq_clock {n : ℕ} (β : ℝ) (J : Disorder n) (t : ℝ)
    (x y : Config n) : continuousKernel β J t x y =
      ∑' k : ℕ, clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y := by
  simp only [continuousKernel,clockWeight,neg_mul]

theorem continuousKernel_sum {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    {t : ℝ} (ht : 0 ≤ t) (x : Config n) : ∑ y : Config n, continuousKernel β J t x y = 1 := by
  classical
  simp_rw [continuousKernel_eq_clock]
  rw [← Summable.tsum_finsetSum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) =>
    uniformization_summable hn β J ht x y)]
  simp_rw [← Finset.mul_sum,discreteKernel_sum hn,mul_one]
  exact clockWeight_sum _

theorem continuous_sign_mass_of_tv {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (x v : Config n) {t : ℝ} (ht : 0 ≤ t) (hTV : continuousDistance β J x t ≤ (1/4:ℝ)) :
    (1/4:ℝ) ≤ ∑ y : Config n, if overlap v y ≤ 0 then continuousKernel β J t x y else 0 := by
  have H := finite_event_le_tv (continuousKernel β J t x) (gibbs β J)
    (continuousKernel_sum hn β J ht x) (gibbs_sum β J) (fun y => overlap v y ≤ 0)
  have HG := gibbs_nonpositive_overlap_mass β J v
  change _ ≤ continuousDistance β J x t at H
  linarith

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ClockTail
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

theorem clockWeight_succ_mul (a : ℝ) (k : ℕ) :
    ((k+1:ℕ):ℝ)*clockWeight a (k+1) = a*clockWeight a k := by
  unfold clockWeight
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  have h1 : (k:ℝ)+1 ≠ 0 := by positivity
  have h2 : (k.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp

theorem clockWeight_mean_hasSum (a : ℝ) : HasSum (fun k : ℕ => (k:ℝ)*clockWeight a k) a := by
  have H := (clockWeight_hasSum a).mul_left a
  rw [mul_one] at H
  have HH : HasSum (fun k : ℕ => ((k+1:ℕ):ℝ)*clockWeight a (k+1)) a := by
    simpa only [clockWeight_succ_mul] using H
  have HHH := (hasSum_nat_add_iff (f := fun k : ℕ => (k:ℝ)*clockWeight a k) (g := a) 1).mp HH
  simpa only [Finset.sum_range_one,Nat.cast_zero,zero_mul,add_zero] using HHH

theorem clockWeight_tail_summable {a : ℝ} (ha : 0 ≤ a) (m : ℕ) :
    Summable (fun k : ℕ => if m < k then clockWeight a k else 0) := by
  apply Summable.of_nonneg_of_le _ _ (clockWeight_hasSum a).summable
  · intro k; split_ifs
    · exact clockWeight_nonneg ha k
    · exact le_refl 0
  · intro k; split_ifs
    · exact le_refl _
    · exact clockWeight_nonneg ha k

theorem clockWeight_tail_le {a : ℝ} (ha : 0 ≤ a) {m : ℕ} (hm : 0 < m) :
    (∑' k : ℕ, if m < k then clockWeight a k else 0) ≤ a/(m:ℝ) := by
  have H := ((clockWeight_tail_summable ha m).mul_left (m:ℝ)).tsum_le_tsum
    (fun k => show (m:ℝ)*(if m < k then clockWeight a k else 0) ≤ (k:ℝ)*clockWeight a k from by
      split_ifs with hk
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_of_lt hk) (clockWeight_nonneg ha k)
      · simp only [mul_zero]; exact mul_nonneg (by positivity) (clockWeight_nonneg ha k))
    (clockWeight_mean_hasSum a).summable
  rw [tsum_mul_left,(clockWeight_mean_hasSum a).tsum_eq] at H
  exact (le_div_iff₀ (show (0:ℝ) < m by exact_mod_cast hm)).mpr (by simpa only [mul_comm] using H)

theorem attempt_horizon_tail (n : ℕ) (L : ℝ) :
    (∑' k : ℕ, if ⌈Real.exp (2*L)⌉₊ < k then clockWeight ((n:ℝ)*Real.exp L) k else 0) ≤
      (n:ℝ)*Real.exp (-L) := by
  have hExp := Real.exp_pos (2*L)
  have hm : 0 < ⌈Real.exp (2*L)⌉₊ := Nat.ceil_pos.mpr hExp
  have hceil : Real.exp (2*L) ≤ (⌈Real.exp (2*L)⌉₊:ℝ) := Nat.le_ceil _
  calc
    _ ≤ ((n:ℝ)*Real.exp L)/(⌈Real.exp (2*L)⌉₊:ℝ) := clockWeight_tail_le (by positivity) hm
    _ ≤ ((n:ℝ)*Real.exp L)/Real.exp (2*L) := div_le_div_of_nonneg_left (by positivity) hExp hceil
    _ = (n:ℝ)*Real.exp (-L) := by
      rw [mul_div_assoc,← Real.exp_sub]
      congr 2
      ring

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ContinuousCrossing
attribute [-instance] _root_.OAI.SK.disorderLaw_isGaussian _root_.OAI.SK.disorderPairLaw_probability
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

theorem occupation_mono {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    {k m : ℕ} (hkm : k ≤ m) (x : Config n) : occupation β J A k x ≤ occupation β J A m x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hkm 1))
  intro i _ _
  exact kernelEvent_nonneg _ _ _ _ _

theorem clock_kernelEvent_summable {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] {a : ℝ} (ha : 0 ≤ a) (x : Config n) :
    Summable (fun k : ℕ => clockWeight a k*kernelEvent β J A k x) := by
  apply Summable.of_nonneg_of_le _ _ (clockWeight_hasSum a).summable
  · intro k
    exact mul_nonneg (clockWeight_nonneg ha k) (kernelEvent_nonneg _ _ _ _ _)
  · intro k
    exact mul_le_of_le_one_right (clockWeight_nonneg ha k) (kernelEvent_le_one hn β J A k x)

theorem continuous_event_eq_clock {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] {t : ℝ} (ht : 0 ≤ t) (x : Config n) :
    (∑ y : Config n, if A y then continuousKernel β J t x y else 0) =
      ∑' k : ℕ, clockWeight ((n:ℝ)*t) k*kernelEvent β J A k x := by
  have he (y : Config n) : (if A y then continuousKernel β J t x y else 0) =
      ∑' k : ℕ, if A y then clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y else 0 := by
    by_cases hy : A y
    · simp only [ite_eq_left hy,continuousKernel_eq_clock]
    · simp only [ite_eq_right hy,tsum_zero]
  have hs (y : Config n) : Summable (fun k : ℕ =>
      if A y then clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y else 0) := by
    by_cases hy : A y
    · simp only [ite_eq_left hy]
      exact uniformization_summable hn β J ht x y
    · simp only [ite_eq_right hy]
      exact summable_zero
  simp_rw [he]
  rw [← Summable.tsum_finsetSum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) => hs y)]
  simp only [kernelEvent,Finset.mul_sum,mul_ite,mul_zero]

theorem continuous_sign_le_stripOccupation_tail {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (x : Config n) (hx : a₁ < overlap v x) :
    (∑ y : Config n, if overlap v y ≤ 0 then continuousKernel β J t x y else 0) ≤
      occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) m x +
        ∑' k : ℕ, if m < k then clockWeight ((n:ℝ)*t) k else 0 := by
  rw [continuous_event_eq_clock hn β J _ ht]
  have ha : 0 ≤ (n:ℝ)*t := by positivity
  let O := occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) m x
  have hO : 0 ≤ O := occupation_nonneg _ _ _ _ _
  have H := (clock_kernelEvent_summable hn β J (fun y => overlap v y ≤ 0) ha x).tsum_le_tsum
    (g := fun k => clockWeight ((n:ℝ)*t) k*O+(if m < k then clockWeight ((n:ℝ)*t) k else 0))
    (fun k => show _ ≤ _ from by
      by_cases hk : m < k
      · simp only [ite_eq_left hk]
        have HH := mul_le_of_le_one_right (clockWeight_nonneg ha k) (kernelEvent_le_one hn β J (fun y => overlap v y ≤ 0) k x)
        linarith [mul_nonneg (clockWeight_nonneg ha k) hO]
      · simp only [ite_eq_right hk,add_zero]
        exact mul_le_mul_of_nonneg_left ((signEvent_le_stripOccupation hn β J v ha₀ hgap k x hx).trans
          (occupation_mono β J _ (le_of_not_gt hk) x)) (clockWeight_nonneg ha k))
    (((clockWeight_hasSum ((n:ℝ)*t)).summable.mul_right O).add (clockWeight_tail_summable ha m))
  rw [Summable.tsum_add ((clockWeight_hasSum ((n:ℝ)*t)).summable.mul_right O)
    (clockWeight_tail_summable ha m),tsum_mul_right,clockWeight_sum,one_mul] at H
  exact H

theorem eighth_le_stripOccupation_of_continuous_tv {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀)
    (L : ℝ) (hL : (n:ℝ)*Real.exp (-L) ≤ (1/8:ℝ)) (x : Config n) (hx : a₁ < overlap v x)
    (hTV : continuousDistance β J x (Real.exp L) ≤ (1/4:ℝ)) :
    (1/8:ℝ) ≤ occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁)
      ⌈Real.exp (2*L)⌉₊ x := by
  have H₁ := continuous_sign_mass_of_tv hn β J x v (le_of_lt (Real.exp_pos L)) hTV
  have H₂ := continuous_sign_le_stripOccupation_tail hn β J v ha₀ hgap
    (le_of_lt (Real.exp_pos L)) ⌈Real.exp (2*L)⌉₊ x hx
  have H₃ := attempt_horizon_tail n L
  linarith

theorem mass_continuous_mixed_high_le_strip {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀)
    (L : ℝ) (hL : (n:ℝ)*Real.exp (-L) ≤ (1/8:ℝ)) :
    (∑ x : Config n, if a₁ < overlap v x ∧ continuousDistance β J x (Real.exp L) ≤ (1/4:ℝ)
      then gibbs β J x else 0) ≤ 8*((⌈Real.exp (2*L)⌉₊+1:ℕ):ℝ)*
        (∑ y : Config n, if a₀ ≤ overlap v y ∧ overlap v y ≤ a₁ then gibbs β J y else 0) := by
  have HH := Finset.sum_le_sum (s := (Finset.univ : Finset (Config n)))
    (f := fun x => if a₁ < overlap v x ∧ continuousDistance β J x (Real.exp L) ≤ (1/4:ℝ)
      then gibbs β J x else 0)
    (g := fun x => 8*(gibbs β J x*occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁)
      ⌈Real.exp (2*L)⌉₊ x))
    (fun x _ => show _ ≤ _ from by
      split_ifs with hx
      · have H := eighth_le_stripOccupation_of_continuous_tv hn β J v ha₀ hgap L hL x hx.1 hx.2
        nlinarith [mul_le_mul_of_nonneg_left H (le_of_lt (gibbs_pos β J x))]
      · exact mul_nonneg (by norm_num) (mul_nonneg (le_of_lt (gibbs_pos β J x))
          (occupation_nonneg _ _ _ _ _)))
  rw [← Finset.mul_sum,occupation_stationary hn] at HH
  simpa only [mul_assoc] using HH

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_DynamicsMeasurable
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

theorem continuous_coupling {n : ℕ} (i j : Fin n) : Continuous (fun J : Disorder n => coupling J i j) := by
  unfold coupling
  split_ifs <;> first | exact continuous_apply _ | exact continuous_const

theorem continuous_localField {n : ℕ} (x : Config n) (i : Fin n) : Continuous (fun J : Disorder n => localField J x i) := by
  unfold localField
  apply Continuous.div_const
  exact continuous_finsetSum _ (fun j _ => (continuous_coupling i j).mul continuous_const)

theorem continuous_heatBath {n : ℕ} (β : ℝ) (x y : Config n) : Continuous (fun J : Disorder n => heatBath β J x y) := by
  unfold heatBath
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  split_ifs
  · apply Continuous.div
    · exact (continuous_const.mul (continuous_localField x i)).rexp
    · exact continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul (continuous_localField x i)))
    · intro J; exact mul_ne_zero (by norm_num) (Real.cosh_pos _).ne'
  · exact continuous_const

theorem continuous_discreteKernel {n : ℕ} (β : ℝ) (k : ℕ) (x y : Config n) :
    Continuous (fun J : Disorder n => discreteKernel β J k x y) := by
  induction k generalizing x y with
  | zero => exact continuous_const
  | succ k ih =>
    exact continuous_finsetSum _ (fun z _ => (continuous_heatBath β x z).mul (ih z y))

theorem measurable_continuousKernel {n : ℕ} (β : ℝ) (t : ℝ) (x y : Config n) :
    Measurable (fun J : Disorder n => continuousKernel β J t x y) := by
  exact Measurable.tsum (fun k => measurable_const.mul (continuous_discreteKernel β k x y).measurable)

theorem continuous_discreteDistance {n : ℕ} (β : ℝ) (k : ℕ) (x : Config n) :
    Continuous (fun J : Disorder n => discreteDistance β J x k) := by
  exact continuous_const.mul (continuous_finsetSum _ (fun y _ => ((continuous_discreteKernel β k x y).sub (continuous_gibbs β y)).abs))

theorem measurable_continuousDistance {n : ℕ} (β : ℝ) (t : ℝ) (x : Config n) :
    Measurable (fun J : Disorder n => continuousDistance β J x t) := by
  exact measurable_const.mul (Finset.measurable_sum _ (fun y _ => ((measurable_continuousKernel β t x y).sub (continuous_gibbs β y).measurable).abs))

theorem measurable_gibbs_predicate_mass {n : ℕ} (β : ℝ) (E : Disorder n → Config n → Prop)
    (hE : ∀x,MeasurableSet {J | E J x}) :
    Measurable (fun J => ∑x,if E J x then gibbs β J x else 0) := by
  exact Finset.measurable_sum _ (fun x _ => Measurable.ite (hE x) (continuous_gibbs β x).measurable measurable_const)

theorem gibbs_predicate_mass_nonneg {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    0≤∑x,if E x then gibbs β J x else 0 := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> first | exact (gibbs_pos β J x).le | exact le_rfl

theorem gibbs_predicate_mass_le_one {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (∑x,if E x then gibbs β J x else 0)≤1 := by
  rw [← gibbs_sum β J]
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> first | exact le_rfl | exact (gibbs_pos β J x).le

theorem integrable_gibbs_predicate_mass {n : ℕ} (β : ℝ) (E : Disorder n → Config n → Prop)
    (hE : ∀x,MeasurableSet {J | E J x}) :
    Integrable (fun J => ∑x,if E J x then gibbs β J x else 0) (disorderLaw n) := by
  apply (integrable_const (1:ℝ)).mono' (measurable_gibbs_predicate_mass β E hE).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs,abs_of_nonneg (gibbs_predicate_mass_nonneg β J _)] using gibbs_predicate_mass_le_one β J (E J)

theorem discreteMixedMass_integrable (n : ℕ) (β : ℝ) (k : ℕ) :
    Integrable (fun J : Disorder n => discreteMixedMass β J k) (disorderLaw n) :=
  integrable_gibbs_predicate_mass β _ (fun x => measurableSet_le (continuous_discreteDistance β k x).measurable measurable_const)

theorem continuousMixedMass_integrable (n : ℕ) (β : ℝ) (t : ℝ) :
    Integrable (fun J : Disorder n => continuousMixedMass β J t) (disorderLaw n) :=
  integrable_gibbs_predicate_mass β _ (fun x => measurableSet_le (measurable_continuousDistance β t x) measurable_const)

theorem gibbs_predicate_mass_compl {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (∑x,if ¬E x then gibbs β J x else 0)=1-∑x,if E x then gibbs β J x else 0 := by
  rw [← gibbs_sum β J,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp_all

theorem discreteBadMass_eq_one_sub (β : ℝ) (n : ℕ) :
    discreteBadMass β n=1-∫J,discreteMixedMass β J ⌊timeScale n⌋₊ ∂disorderLaw n := by
  have he (J : Disorder n) : (∑x,if (1/4:ℝ)<discreteDistance β J x ⌊timeScale n⌋₊ then gibbs β J x else 0)=
      1-discreteMixedMass β J ⌊timeScale n⌋₊ := by
    simpa only [not_le,discreteMixedMass] using gibbs_predicate_mass_compl β J (fun x => discreteDistance β J x ⌊timeScale n⌋₊≤(1/4:ℝ))
  unfold discreteBadMass
  simp_rw [he]
  rw [integral_sub (integrable_const 1) (discreteMixedMass_integrable n β _)]
  simp

theorem continuousBadMass_eq_one_sub (β : ℝ) (n : ℕ) :
    continuousBadMass β n=1-∫J,continuousMixedMass β J (timeScale n) ∂disorderLaw n := by
  have he (J : Disorder n) : (∑x,if (1/4:ℝ) < continuousDistance β J x (timeScale n) then gibbs β J x else 0)=
      1-continuousMixedMass β J (timeScale n) := by
    simpa only [not_le,continuousMixedMass] using gibbs_predicate_mass_compl β J (fun x => continuousDistance β J x (timeScale n)≤(1/4:ℝ))
  unfold continuousBadMass
  simp_rw [he]
  rw [integral_sub (integrable_const 1) (continuousMixedMass_integrable n β _)]
  simp

theorem main_of_quenched_mixed_bounds (β : ℝ) (C : (n : ℕ) → Set (Disorder n))
    (hC : ∀n,MeasurableSet (C n)) (hC1 : Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1))
    (e : ℕ → ℝ) (he : ∀n,0≤e n) (he0 : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n : ℕ in atTop,∀J∈C n,continuousMixedMass β J (timeScale n)≤e n ∧
      discreteMixedMass β J ⌊timeScale n⌋₊≤e n) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧ Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  have hcomp : Tendsto (fun n => (disorderLaw n).real (C n)ᶜ) atTop (𝓝 0) := by
    have H := (tendsto_const_nhds (x:=(1:ℝ))).sub hC1
    simpa only [measureReal_compl (hC _),probReal_univ,sub_self] using H
  have hlim := he0.add hcomp
  simp only [add_zero] at hlim
  have HC : Tendsto (fun n => ∫J,continuousMixedMass β J (timeScale n) ∂disorderLaw n) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun J => gibbs_predicate_mass_nonneg β J _))) _ hlim
    filter_upwards [hbound] with n hn
    apply integral_le_off_exception (continuousMixedMass_integrable n β _) (hC n).compl (he n)
      (fun J => gibbs_predicate_mass_le_one β J _)
    intro J hJ
    exact (hn J (by simpa only [mem_compl_iff,not_not] using hJ)).1
  have HD : Tendsto (fun n => ∫J,discreteMixedMass β J ⌊timeScale n⌋₊ ∂disorderLaw n) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun J => gibbs_predicate_mass_nonneg β J _))) _ hlim
    filter_upwards [hbound] with n hn
    apply integral_le_off_exception (discreteMixedMass_integrable n β _) (hC n).compl (he n)
      (fun J => gibbs_predicate_mass_le_one β J _)
    intro J hJ
    exact (hn J (by simpa only [mem_compl_iff,not_not] using hJ)).2
  constructor
  · have H := (tendsto_const_nhds (x:=(1:ℝ))).sub HC
    simpa only [← continuousBadMass_eq_one_sub,sub_zero] using H
  · have H := (tendsto_const_nhds (x:=(1:ℝ))).sub HD
    simpa only [← discreteBadMass_eq_one_sub,sub_zero] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_GreedyEventual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory Filter Set
namespace SK.Analytic

 theorem horizon_size_bound {L : ℝ} (hL : 0≤L) : (⌈Real.exp (2*L)⌉₊:ℝ)+1≤3*Real.exp (2*L) := by
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (2*L)).le
  have hh : 1≤Real.exp (2*L) := Real.one_le_exp_iff.mpr (by positivity)
  linarith only [hc,hh]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ForbiddenDynamics
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

 theorem mixedMass_le_pairStrip {n : ℕ} (hn : 0<n) (β : ℝ) (J : Disorder n)
    {a₀ a₁ q a δ L : ℝ} (ha₀ : 0<a₀) (haq : a₁<q) (ha : 0<a)
    (hgap : 2/(n:ℝ)<a₁-a₀) (hL : 0≤L) (htail : (n:ℝ)*Real.exp (-L)≤(1/8:ℝ))
    (hcov : (gibbsFiniteLaw β J).prob (fun x => (gibbsFiniteLaw β J).prob (fun y => q≤|overlap x y|)<a)≤δ) :
    continuousMixedMass β J (Real.exp L)≤δ+(16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/a)*replicaGibbsMass β J (pairStripSet n a₀ a₁) ∧
    discreteMixedMass β J ⌊Real.exp L⌋₊≤δ+(16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/a)*replicaGibbsMass β J (pairStripSet n a₀ a₁) := by
  have hnum : (⌊Real.exp L⌋₊:ℝ)+1≤(⌈Real.exp (2*L)⌉₊:ℝ)+1 := by
    have H : ⌊Real.exp L⌋₊≤⌈Real.exp (2*L)⌉₊ :=
      (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith only [hL]))).trans (Nat.floor_le_ceil _)
    exact_mod_cast Nat.add_le_add_right H 1
  have HC (v : Config n) :
      (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ continuousDistance β J x (Real.exp L)≤(1/4:ℝ))≤
        (8*((⌈Real.exp (2*L)⌉₊:ℝ)+1))*(gibbsFiniteLaw β J).prob (fun x => a₀≤overlap v x ∧ overlap v x≤a₁) := by
    convert mass_continuous_mixed_high_le_strip hn β J v ha₀ hgap L htail using 1 <;> simp only [gibbs_prob_eq_sum,Nat.cast_add,Nat.cast_one]
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
    · congr 1
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> rfl
  have HD (v : Config n) :
      (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ discreteDistance β J x ⌊Real.exp L⌋₊≤(1/4:ℝ))≤
        (8*((⌈Real.exp (2*L)⌉₊:ℝ)+1))*(gibbsFiniteLaw β J).prob (fun x => a₀≤overlap v x ∧ overlap v x≤a₁) := by
    have H := mass_mixed_high_le_strip hn β J v ha₀ hgap ⌊Real.exp L⌋₊
    have HH : (gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ discreteDistance β J x ⌊Real.exp L⌋₊≤(1/4:ℝ))≤
        (4*((⌊Real.exp L⌋₊:ℝ)+1))*(gibbsFiniteLaw β J).prob (fun x => a₀≤overlap v x ∧ overlap v x≤a₁) := by
      convert H using 1 <;> simp only [gibbs_prob_eq_sum,Nat.cast_add,Nat.cast_one]
      · apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> rfl
      · congr 1
        apply Finset.sum_congr rfl
        intro x _
        split_ifs <;> rfl
    refine HH.trans (mul_le_mul_of_nonneg_right ?_ ((gibbsFiniteLaw β J).prob_nonneg _))
    nlinarith only [hnum,(Nat.cast_nonneg (⌈Real.exp (2*L)⌉₊) : (0:ℝ)≤_)]
  have general (E : Config n → Prop)
      (HE : ∀v,(gibbsFiniteLaw β J).prob (fun x => a₁<overlap v x ∧ E x)≤
        (8*((⌈Real.exp (2*L)⌉₊:ℝ)+1))*(gibbsFiniteLaw β J).prob (fun x => a₀≤overlap v x ∧ overlap v x≤a₁)) :
      (gibbsFiniteLaw β J).prob E≤δ+(16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/a)*replicaGibbsMass β J (pairStripSet n a₀ a₁) := by
    have H := covered_mixed_mass_le_signed_average β J E haq ha hcov
    have HB := (gibbsFiniteLaw β J).expect_mono HE
    rw [FiniteLaw.expect_const_mul,pairStrip_expect] at HB
    refine H.trans (add_le_add_right ((mul_le_mul_of_nonneg_left HB (by positivity : 0≤2/a)).trans_eq ?_) δ)
    ring
  constructor
  · simpa only [gibbs_prob_eq_sum,continuousMixedMass] using general _ HC
  · simpa only [gibbs_prob_eq_sum,discreteMixedMass] using general _ HD

 theorem pairStrip_numerical_error {L c v : ℝ} (hL : 0≤L) (hv : v≤Real.exp (-(c+10)*L)) :
    Real.exp (-3*L)+(16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/Real.exp (-c*L))*v≤
      Real.exp (-3*L)+48*Real.exp (-8*L) := by
  apply add_le_add_right
  have HM := horizon_size_bound hL
  have HN : 0≤16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/Real.exp (-c*L) := by positivity
  calc
    _ ≤ (16*((⌈Real.exp (2*L)⌉₊:ℝ)+1)/Real.exp (-c*L))*Real.exp (-(c+10)*L) := mul_le_mul_of_nonneg_left hv HN
    _ ≤ (16*(3*Real.exp (2*L))/Real.exp (-c*L))*Real.exp (-(c+10)*L) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left HM (by norm_num)) (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc 16 3,show (16:ℝ)*3=48 by norm_num,mul_div_assoc,← Real.exp_sub,mul_assoc,← Real.exp_add]
      congr 2
      ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ForbiddenInterval
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

 theorem exists_forbidden_interval {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0:ℝ) 1))
    {l u : ℝ} (hl : 0≤l) (hu : u≤1) (h : ¬∀x∈Ioo l u,f x=x) :
    ∃a₀ a₁ d : ℝ,l<a₀ ∧ a₀<a₁ ∧ a₁<u ∧ 0<d ∧ ∀x∈Icc a₀ a₁,d≤|x-f x| := by
  push Not at h
  obtain ⟨z,hz,hfZ⟩ := h
  have hz0 : 0<z := hl.trans_lt hz.1
  have hz1 : z<1 := hz.2.trans_le hu
  have hc : ContinuousAt (fun x => |x-f x|) z :=
    (continuousAt_id.sub ((hf z ⟨hz0.le,hz1.le⟩).continuousAt (Icc_mem_nhds hz0 hz1))).abs
  have hd : 0 < |z-f z| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hfZ))
  have hznhds : ∀ᶠ x in 𝓝 z,x∈Ioo l u := Ioo_mem_nhds hz.1 hz.2
  have hh : ∀ᶠ x in 𝓝 z,x∈Ioo l u ∧ |z-f z|/2≤|x-f x| :=
    hznhds.and (Filter.Tendsto.eventually_const_le (half_lt_self hd) hc)
  obtain ⟨r,hr,hrball⟩ := Metric.mem_nhds_iff.mp hh
  let a₀ := z-r/2
  let a₁ := z+r/2
  have hleft : a₀∈Metric.ball z r := by
    rw [Metric.mem_ball,Real.dist_eq]
    dsimp only [a₀]
    rw [sub_sub_cancel_left,abs_neg,abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  have hright : a₁∈Metric.ball z r := by
    rw [Metric.mem_ball,Real.dist_eq]
    dsimp only [a₁]
    rw [add_sub_cancel_left,abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  refine ⟨a₀,a₁,|z-f z|/2,(hrball hleft).1.1,?_,(hrball hright).1.2,half_pos hd,?_⟩
  · dsimp only [a₀,a₁]; linarith only [hr]
  · intro x hx
    apply (hrball ?_).2
    rw [Metric.mem_ball,Real.dist_eq]
    have H : |x-z| ≤ r/2 := abs_le.mpr (by dsimp only [a₀,a₁] at hx; constructor <;> linarith only [hx.1,hx.2])
    exact H.trans_lt (half_lt_self hr)

 theorem pairStrip_annealed_bound {β : ℝ} (hβ : 0<β)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    {a₀ a₁ d : ℝ} (ha₀ : 0≤a₀) (hd : 0<d)
    (hgap : ∀x∈Icc a₀ a₁,d≤|x-scalarCDFOverlap β (cdf (μ : Measure ℝ)) x|) :
    ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (pairStripSet n a₀ a₁) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((4:ℝ)/5)) := by
  have H := eventual_pairMismatch_polynomial_bound (A:=d) (a:=0) (t:=(4:ℝ)/5) (ε:=1)
    hβ hd le_rfl (by norm_num) (by norm_num) zero_lt_one
    (cdf (μ : Measure ℝ)) (fun x => ⟨cdf_nonneg _ _,cdf_le_one _ _⟩) (supported_probability_cdf_one μ hμ) hmin
  simp only [neg_zero,Real.rpow_zero,mul_one,one_mul] at H
  filter_upwards [H] with n hn
  refine (integral_mono (replicaGibbsMass_integrable β _) (replicaGibbsMass_integrable β _)
    (fun J => replicaGibbsMass_mono β J ?_)).trans hn
  intro s hs
  have hh := (Finset.mem_filter.mp hs).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha₀.trans hh.1,hgap _ hh⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_PathEndpoint
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

@[simp] theorem extendPath_at {n m : ℕ} (s : Fin (m+1) → Config n) (k : Fin (m+1)) :
    extendPath s k.val=s k := by simp only [extendPath,dite_eq_left (show k.val ≤ m by omega)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_IdentityMain
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

 theorem site_clock_tail_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-levelLogScale n)) atTop (𝓝 0) := by
  simpa only [pow_one,neg_one_mul,levelLogScale] using
    polynomial_rpow_exp_decay (by norm_num [kappa] : 0<kappa) zero_lt_one 1

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Dynamics_ForbiddenMain
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

 theorem forbiddenEndpointError_tendsto : Tendsto forbiddenEndpointError atTop (𝓝 0) := by
  have H := (stretched_exp_decay (by norm_num : (0:ℝ)<3)).add ((stretched_exp_decay (by norm_num : (0:ℝ)<8)).const_mul 48)
  change Tendsto (fun n => Real.exp (-3*levelLogScale n)+48*Real.exp (-8*levelLogScale n)) atTop (𝓝 0)
  simpa only [mul_zero,add_zero] using H

 theorem forbidden_main_of_static_gap (β : ℝ) {q a₀ a₁ : ℝ}
    (ha₀ : 0<a₀) (ha : a₀<a₁) (haq : a₁<q)
    (hcov : ∀D : ℝ,0<D → ∃c : ℝ,0 < c ∧ ∃C : (n : ℕ) → Set (Disorder n),
      (∀n,MeasurableSet (C n)) ∧ Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
      ∀n J,J∈C n → ∀S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
        finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<Real.exp (-c*levelLogScale n)))<Real.exp (-D*levelLogScale n))
    (hstatic : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (pairStripSet n a₀ a₁) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((4:ℝ)/5))) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧ Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  obtain ⟨c,hc,C,hC,hC1,hcovC⟩ := hcov 3 (by norm_num)
  let V (n : ℕ) : Set (Disorder n) := {J | replicaGibbsMass β J (pairStripSet n a₀ a₁)≤Real.exp (-(c+10)*levelLogScale n)}
  let D (n : ℕ) : Set (Disorder n) := C n ∩ V n
  have hV (n : ℕ) : MeasurableSet (V n) := measurableSet_le (continuous_replicaGibbsMass β _).measurable measurable_const
  have hV1 : Tendsto (fun n => (disorderLaw n).real (V n)) atTop (𝓝 1) := by
    apply high_probability_small_replica β _ (by norm_num [kappa] : kappa<(4:ℝ)/5) 1 (c+10)
    simpa only [one_mul] using hstatic
  have hD (n : ℕ) : MeasurableSet (D n) := (hC n).inter (hV n)
  have hD1 : Tendsto (fun n => (disorderLaw n).real (D n)) atTop (𝓝 1) := high_probability_inter _ _ hV hC1 hV1
  apply main_of_quenched_mixed_bounds β D hD hD1 forbiddenEndpointError
    (fun n => by unfold forbiddenEndpointError; positivity) forbiddenEndpointError_tendsto
  have Hgap : Tendsto (fun n : ℕ => 2/(n:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul 2
  filter_upwards [eventually_gt_atTop (0:ℕ),Hgap.eventually_lt_const (sub_pos.mpr ha),
    site_clock_tail_tendsto.eventually_le_const (by norm_num : (0:ℝ)<1/8)] with n hn hgap htail
  intro J hJ
  have hcovJ := gibbs_coverage_predicate β J q _ _ (hcovC n J hJ.1) (fun _ => True)
  simp only [true_and] at hcovJ
  have H := mixedMass_le_pairStrip hn β J ha₀ haq (Real.exp_pos _) hgap
    (show 0≤levelLogScale n by unfold levelLogScale; positivity) htail hcovJ
  have Hnum := pairStrip_numerical_error (show 0≤levelLogScale n by unfold levelLogScale; positivity) hJ.2
  exact ⟨H.1.trans Hnum,H.2.trans Hnum⟩

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

 theorem choose_dynamics_scale {q b b' : ℝ} (hq : 0<q) (hb : 0<b) (hb' : 0<b') :
    ∃t : ℝ,0<t ∧ 3*t<1 ∧ 3*t<b^2/2 ∧ 3*t<b ∧ 2*t<b' ∧ 3*t<q := by
  let a : ℝ := min (1/3) (min (b^2/6) (min (b/3) (min (b'/2) (q/3))))
  have ha : 0<a := by dsimp only [a]; positivity
  refine ⟨a/2,half_pos ha,?_,?_,?_,?_,?_⟩
  all_goals have hat : a/2<a := half_lt_self ha
  · have H : a≤1/3 := min_le_left _ _
    linarith only [hat,H]
  · have H : a≤b^2/6 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [hat,H]
  · have H : a≤b/3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [hat,H]
  · have H : a≤b'/2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith only [hat,H]
  · have H : a≤q/3 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith only [hat,H]

 theorem lockingUnion_annealed_bound (β : ℝ) (μ : ProbabilityMeasure ℝ) (t q b b' : ℝ)
    (hs : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (signedLockingSet n q b) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((9:ℝ)/10)))
    (hs' : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (signedLockingSet n b b') ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((9:ℝ)/10)))
    (hnar : ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (narrowLockingSet n μ t (levelRho n)) ∂disorderLaw n)≤Real.exp (-(n:ℝ)^((4:ℝ)/5))) :
    ∀ᶠ n : ℕ in atTop,(∫J,replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b') ∂disorderLaw n)≤3*Real.exp (-(n:ℝ)^((4:ℝ)/5)) := by
  filter_upwards [hs,hs',hnar,eventually_ge_atTop (1:ℕ)] with n hns hns' hnn hn1
  have H := integral_mono (replicaGibbsMass_integrable β (lockingUnion n μ t (levelRho n) q b b'))
    (((replicaGibbsMass_integrable β (signedLockingSet n q b)).add
      (replicaGibbsMass_integrable β (signedLockingSet n b b'))).add
      (replicaGibbsMass_integrable β (narrowLockingSet n μ t (levelRho n)))) (fun J => by
      have H1 := replicaGibbsMass_union_le β J (signedLockingSet n q b ∪ signedLockingSet n b b') (narrowLockingSet n μ t (levelRho n))
      have H2 := replicaGibbsMass_union_le β J (signedLockingSet n q b) (signedLockingSet n b b')
      change replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b')≤_
      dsimp only [lockingUnion, Pi.add_apply] at *
      linarith only [H1,H2])
  simp only [Pi.add_apply] at H
  have HI1 := integral_add ((replicaGibbsMass_integrable β (signedLockingSet n q b)).add
    (replicaGibbsMass_integrable β (signedLockingSet n b b'))) (replicaGibbsMass_integrable β (narrowLockingSet n μ t (levelRho n)))
  have HI2 := integral_add (replicaGibbsMass_integrable β (signedLockingSet n q b)) (replicaGibbsMass_integrable β (signedLockingSet n b b'))
  simp only [Pi.add_apply] at HI1 HI2
  rw [HI1,HI2] at H
  have HE : Real.exp (-(n:ℝ)^((9:ℝ)/10))≤Real.exp (-(n:ℝ)^((4:ℝ)/5)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num))
  linarith only [H,hns,hns',hnn,HE]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK

theorem main_oai (β : ℝ) (hβ : 1<β) :
    Tendsto (continuousBadMass β) atTop (𝓝 1) ∧
      Tendsto (discreteBadMass β) atTop (𝓝 1) := by
  have hβ0 : 0<β := zero_lt_one.trans hβ
  obtain ⟨q,hq,hq1,Hcov⟩ := Analytic.stretched_uniform_coverage hβ
  obtain ⟨b,hb,hb1,Hb⟩ := Analytic.signed_small_scale hβ0 hq hq1.le zero_lt_one
  obtain ⟨b',hb',hb'b,Hb'⟩ := Analytic.signed_small_scale hβ0 hb hb1.le hb
  obtain ⟨t,ht,ht1,htpack,htb,htb',htq⟩ := Analytic.choose_dynamics_scale hq hb hb'
  obtain ⟨μ,hμ,hmin,h0,hH,hA,hstrict,hS⟩ := Analytic.exists_scalarCDFParisi_minimizer_locking_data hβ0.ne'
  by_cases hΓ : ∀r∈Ioo (t/2) (3*t),Analytic.scalarCDFOverlap β (cdf (μ : Measure ℝ)) r=r
  · have Hnarrow := Analytic.narrow_annulus_locking hβ0 ht ht1 μ hμ hmin h0 hS hΓ
    have Hstatic := Analytic.lockingUnion_annealed_bound β μ t q b b' Hb Hb' Hnarrow
    exact Analytic.identity_main_of_static_locking β μ ht hb htpack htb htb' (by linarith only [htq,ht]) Hcov Hstatic
  · have Hcont := Analytic.scalarCDFOverlap_continuousOn β (cdf (μ : Measure ℝ))
      (fun x => ⟨cdf_nonneg _ _,cdf_le_one _ _⟩) (Analytic.supported_probability_cdf_one μ hμ)
    obtain ⟨a₀,a₁,d,ha₀,ha,ha₁,hd,Hd⟩ := Analytic.exists_forbidden_interval Hcont (half_pos ht).le ht1.le hΓ
    have ha₀0 : 0<a₀ := (half_pos ht).trans ha₀
    have Hstatic := Analytic.pairStrip_annealed_bound hβ0 μ hμ hmin ha₀0.le hd Hd
    exact Analytic.forbidden_main_of_static_gap β ha₀0 ha (ha₁.trans htq) Hcov Hstatic

end SK

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.main_oai := @OAI.SK.main_oai
