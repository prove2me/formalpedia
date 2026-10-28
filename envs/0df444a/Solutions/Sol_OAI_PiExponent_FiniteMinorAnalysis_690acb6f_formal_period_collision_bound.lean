-- Prove2me | solution 1 for OAI.PiExponent.FiniteMinorAnalysis_690acb6f.formal_period_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T18:53:30.573081+00:00
-- url     : https://prove2.me/submissions/9cf7f54e-f16d-4226-ac0e-e029ac71b256

import Theorems.Thm_OAI_PiExponent_PeriodCollisionSeries_713626a7_period_coefficient_hasSum
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis_690acb6f
open OAI.PiExponent.PeriodCollisionSeries_713626a7
open Filter Topology
open scoped BigOperators

/- The determinant/combinatorial argument is proved here. The sole Open
   dependency is a scalar coefficient identity, without determinants or groups.
   Source route: OpenAI/math adc7f124, Analysis/{CollisionCombinatorics,
   CollisionGeometricSum,FiniteDeterminantCollision,CollisionLimit,
   CollisionExponential,AnalyticCollision,PeriodAnalytic}.lean. -/
namespace OAI.PiExponent.PeriodCollisionProof_713626a7

theorem choose_card_le_sum (s : Finset ℕ) :
    s.card.choose 2 ≤ ∑ d ∈ s, d := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := by
      intro h
      exact (lt_irrefl a) (hmax a h)
    have hsub : s ⊆ Finset.range a := by
      intro x hx
      exact Finset.mem_range.mpr (hmax x hx)
    have hcard : s.card ≤ a := by simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    rw [show s.card + 1 = s.card.succ from rfl,
      Nat.choose_succ_succ s.card 1, Nat.choose_one_right]
    exact Nat.add_le_add hcard ih

theorem sum_multiplicity {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (group : ι → κ) :
    ∑ A, multiplicity group A = Fintype.card ι := by
  classical
  simp only [FiniteMinorAnalysis_690acb6f.multiplicity, Finset.card_filter]
  rw [Finset.sum_comm]
  simp
theorem sum_choose_le_sum_degree {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (group : ι → κ) (degree : ι → ℕ)
    (hinj : Function.Injective (fun i => (group i, degree i))) :
    (∑ A, (multiplicity group A).choose 2) ≤ ∑ i, degree i := by
  classical
  calc
    _ ≤ ∑ A, ∑ i ∈ (Finset.univ : Finset ι).filter
          (fun i => group i = A), degree i := by
      apply Finset.sum_le_sum
      intro A _
      let rows := (Finset.univ : Finset ι).filter (fun i => group i = A)
      have hi : Set.InjOn degree (rows : Set ι) := by
        intro i hi j hj hd
        apply hinj
        exact Prod.ext ((Finset.mem_filter.mp hi).2.trans
          (Finset.mem_filter.mp hj).2.symm) hd
      have hb := choose_card_le_sum (rows.image degree)
      rw [Finset.card_image_of_injOn hi, Finset.sum_image hi] at hb
      exact hb
    _ = _ := Finset.sum_fiberwise_of_maps_to (by simp) degree

theorem twice_collision_count {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (group : ι → κ) :
    2 * ((∑ A, (multiplicity group A).choose 2 : ℕ) : ℝ) =
      (∑ A, (multiplicity group A : ℝ) ^ 2) - Fintype.card ι := by
  have hs : (∑ A, (multiplicity group A : ℝ)) = Fintype.card ι := by
    exact_mod_cast sum_multiplicity group
  push_cast
  rw [Finset.mul_sum]
  calc
    _ = ∑ A, ((multiplicity group A : ℝ) ^ 2 -
        (multiplicity group A : ℝ)) := by
      apply Finset.sum_congr rfl
      intro A _
      rw [Nat.cast_choose_two]
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, hs]

theorem sum_pow_fin_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ k : Fin N, s ^ (k : ℕ)) ≤ (1 - s)⁻¹ := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => s ^ k), ← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hs1)).2
  rw [geom_sum_mul_neg]
  exact sub_le_self 1 (pow_nonneg hs0 N)

theorem sum_pow_assignments_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ))) ≤
      ((1 - s)⁻¹) ^ Fintype.card ι := by
  have he : (∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ))) =
      (∑ k : Fin N, s ^ (k : ℕ)) ^ Fintype.card ι := by
    simp_rw [← Finset.prod_pow_eq_pow_sum]
    rw [← Fintype.prod_sum (fun (_ : ι) (k : Fin N) => s ^ (k : ℕ))]
    simp
  rw [he]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => pow_nonneg hs0 _)
    (sum_pow_fin_le hs0 hs1 N) _

theorem collision_geometric_sum_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ f ∈ (Finset.univ : Finset (ι → Fin N)).filter
        (fun f => Function.Injective (fun i => (group i, (f i : ℕ)))),
      (s * s) ^ (∑ i, (f i : ℕ))) ≤
      s ^ (∑ A, (multiplicity group A).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  let good := (Finset.univ : Finset (ι → Fin N)).filter
    (fun f => Function.Injective (fun i => (group i, (f i : ℕ))))
  let C := ∑ A, (multiplicity group A).choose 2
  have hp : ∀ f ∈ good,
      (s * s) ^ (∑ i, (f i : ℕ)) ≤ s ^ C * s ^ (∑ i, (f i : ℕ)) := by
    intro f hf
    have hd : C ≤ ∑ i, (f i : ℕ) :=
      sum_choose_le_sum_degree group (fun i => (f i : ℕ))
        (Finset.mem_filter.mp hf).2
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0 hs1.le hd)
      (pow_nonneg hs0 _)
  calc
    _ ≤ ∑ f ∈ good, s ^ C * s ^ (∑ i, (f i : ℕ)) := Finset.sum_le_sum hp
    _ = s ^ C * ∑ f ∈ good, s ^ (∑ i, (f i : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ s ^ C * ∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs0 C)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro f _ _
      exact pow_nonneg hs0 _
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_pow_assignments_le hs0 hs1 N)
      (pow_nonneg hs0 C)

theorem det_finite_row_sum {ι κ δ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype δ] (group : ι → κ) (B : ι → δ → ℂ) (C : κ → δ → ι → ℂ) :
    Matrix.det (fun i j => ∑ d, B i d * C (group i) d j) =
      ∑ f : ι → δ, (∏ i, B i (f i)) *
        Matrix.det (fun i j => C (group i) (f i) j) := by
  classical
  have hm := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum
    (fun i d => B i d • C (group i) d)
  calc
    _ = Matrix.det (fun i => ∑ d, B i d • C (group i) d) := by
      congr 1
      funext i j
      simp
    _ = ∑ f : ι → δ, Matrix.det (fun i => B i (f i) • C (group i) (f i)) := hm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      exact Matrix.det_mul_column (fun i => B i (f i)) (fun i j => C (group i) (f i) j)

theorem norm_det_le_factorial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {D : ℝ} (hD : 0 ≤ D) (hA : ∀ i j, ‖A i j‖ ≤ D) :
    ‖A.det‖ ≤ (Fintype.card ι).factorial * D ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖σ.sign • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖A (σ i) i‖ := by
      apply Finset.sum_congr rfl
      intro σ _
      rcases Int.units_eq_one_or σ.sign with hs | hs <;> simp [hs, norm_prod]
    _ ≤ ∑ _σ : Equiv.Perm ι, D ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _index : ι, |D| := Finset.prod_le_prod
          (fun index _ => norm_nonneg _)
          (fun index _ => (hA (σ index) index).trans (le_abs_self D))
        _ = D ^ Fintype.card ι := by simp [abs_of_nonneg hD]
    _ = _ := by simp [Fintype.card_perm]

theorem finite_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ i, 0 ≤ L i) (hC : ∀ A d j, ‖C A d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ d) (N : ℕ) :
    ‖Matrix.det (fun i j => ∑ d : Fin N, B i d * C (group i) d j)‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ (∑ A, (multiplicity group A).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  let good := (Finset.univ : Finset (ι → Fin N)).filter
    (fun f => Function.Injective (fun i => (group i, (f i : ℕ))))
  let Q := (Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _))
      (Finset.prod_nonneg fun i _ => hL i)
  have he : Matrix.det (fun i j => ∑ d : Fin N, B i d * C (group i) d j) =
      ∑ f ∈ good, (∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j) := by
    rw [det_finite_row_sum group (fun i (d : Fin N) => B i d)
      (fun A (d : Fin N) j => C A d j)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    have hn : ¬ Function.Injective (fun i => (group i, (f i : ℕ))) := by
      simpa [good] using hf
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hn
    have hg : group i = group j := congrArg Prod.fst hij
    have hd : (f i : ℕ) = (f j : ℕ) := congrArg Prod.snd hij
    have hz : Matrix.det (fun r c => C (group r) (f r) c) = 0 := by
      apply Matrix.det_zero_of_row_eq hne
      funext c
      simp only [hg, hd]
    simp [hz]
  have ht (f : ι → Fin N) :
      ‖(∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j)‖ ≤
        Q * (s * s) ^ (∑ i, (f i : ℕ)) := by
    have hb : (∏ i, ‖B i (f i)‖) ≤ ∏ i, L i * (s * s) ^ (f i : ℕ) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hB i (f i))
    have hc := norm_det_le_factorial
      (fun i j => C (group i) (f i) j) hD (fun i j => hC _ _ _)
    rw [norm_mul, norm_prod]
    calc
      _ ≤ (∏ i, L i * (s * s) ^ (f i : ℕ)) *
          ((Fintype.card ι).factorial * D ^ Fintype.card ι) :=
        mul_le_mul hb hc (norm_nonneg _) (Finset.prod_nonneg fun i _ =>
          mul_nonneg (hL i) (pow_nonneg (mul_self_nonneg s) _))
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        dsimp [Q]
        ring
  rw [he]
  calc
    _ ≤ ∑ f ∈ good,
        ‖(∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ f ∈ good, Q * (s * s) ^ (∑ i, (f i : ℕ)) :=
      Finset.sum_le_sum (fun f _ => ht f)
    _ = Q * ∑ f ∈ good, (s * s) ^ (∑ i, (f i : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ Q * (s ^ (∑ A, (multiplicity group A).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι) :=
      mul_le_mul_of_nonneg_left (collision_geometric_sum_le group hs0 hs1 N) hQ
    _ = _ := by dsimp [Q]; ring

theorem infinite_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ i, 0 ≤ L i) (hC : ∀ A d j, ‖C A d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ d)
    (T : Matrix ι ι ℂ)
    (hsum : ∀ i j, HasSum (fun d => B i d * C (group i) d j) (T i j)) :
    ‖T.det‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ (∑ A, (multiplicity group A).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  let Tn : ℕ → Matrix ι ι ℂ := fun N i j => ∑ d ∈ Finset.range N,
    B i d * C (group i) d j
  have hm : Tendsto Tn atTop (𝓝 T) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact (hsum i j).tendsto_sum_nat
  have hd : Tendsto (fun N => (Tn N).det) atTop (𝓝 T.det) :=
    (continuous_id.matrix_det.tendsto T).comp hm
  apply le_of_tendsto' hd.norm
  intro N
  have he : Tn N = (fun i j => ∑ d : Fin N, B i d * C (group i) d j) := by
    funext i j
    exact (Fin.sum_univ_eq_sum_range (fun d : ℕ => B i d * C (group i) d j) N).symm
  rw [he]
  exact finite_collision_bound group B C D s L hD hs0 hs1 hL hC hB N

noncomputable def ratio : ℝ := Real.exp (-Real.log 2 / 2)

theorem ratio_pos : 0 < ratio := Real.exp_pos _

theorem ratio_lt_one : ratio < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

theorem ratio_mul_self : ratio * ratio = 1 / 2 := by
  unfold ratio
  rw [← Real.exp_add]
  have he : -Real.log 2 / 2 + -Real.log 2 / 2 = -Real.log 2 := by ring
  rw [he, Real.exp_neg, Real.exp_log (by norm_num)]
  simp only [one_div]

theorem factorial_le_exp (M : ℕ) :
    (M.factorial : ℝ) ≤ Real.exp ((M : ℝ) * Real.log M) := by
  by_cases hM : M = 0
  · subst M
    norm_num
  · rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hM)]
    exact_mod_cast Nat.factorial_le_pow M

theorem collision_factor_le_exp (M C ell : ℕ) {H A v S : ℝ}
    (hH : 0 < H) (hell : (ell : ℝ) ≤ (M : ℝ) * H / v)
    (hC : 2 * (C : ℝ) = S - M) :
    ((M.factorial : ℝ) * (Real.exp (H * A)) ^ M * (2 : ℝ) ^ ell) *
      ratio ^ C * ((1 - ratio)⁻¹) ^ M ≤
      Real.exp (-(Real.log 2 / 4) * S + (M : ℝ) * H *
        (A + Real.log 2 / v + collisionRemainder M H)) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hr : 0 < 1 - ratio := sub_pos.mpr ratio_lt_one
  have ht : (2 : ℝ) ^ ell ≤ Real.exp ((M : ℝ) * H / v * Real.log 2) := by
    calc
      _ = Real.exp ((ell : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hell hlog2)
  calc
    _ ≤ (Real.exp ((M : ℝ) * Real.log M) * (Real.exp (H * A)) ^ M *
        Real.exp ((M : ℝ) * H / v * Real.log 2)) *
        ratio ^ C * ((1 - ratio)⁻¹) ^ M := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hr.le) M)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ratio_pos.le C)
      apply mul_le_mul _ ht (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (factorial_le_exp M) (by positivity)
    _ = Real.exp (-(Real.log 2 / 4) * S + (M : ℝ) * H * (A + Real.log 2 / v) +
        (M : ℝ) * (Real.log M + Real.log 2 / 4 - Real.log (1 - ratio))) := by
      have hq : ratio ^ C = Real.exp ((C : ℝ) * (-Real.log 2 / 2)) := by
        rw [ratio, Real.exp_nat_mul]
      have hi : ((1 - ratio)⁻¹) ^ M = Real.exp ((M : ℝ) * (-Real.log (1 - ratio))) := by
        rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hr]
      rw [← Real.exp_nat_mul, hq, hi]
      simp only [← Real.exp_add]
      congr 1
      have hc : (C : ℝ) = (S - M) / 2 := by linarith
      rw [hc]
      ring
    _ = _ := by
      congr 1
      have hrH : H * collisionRemainder M H =
          Real.log M + Real.log 2 / 4 - Real.log (1 - ratio) := by
        unfold collisionRemainder ratio
        exact mul_div_cancel₀ _ (ne_of_gt hH)
      rw [← hrH]
      ring

theorem norm_cauchy_half_le {f : ℂ → ℂ} {D : ℝ}
    (hf : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), ‖f z‖ ≤ D) (ell : ℕ) :
    ‖cauchyPowerSeries f 0 (1 / 2) ell (fun _ => 1)‖ ≤ (2 : ℝ) ^ ell * D := by
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ (1 / 2 : ℝ) * (2 ^ ell * (2 * D)) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num)
      intro z hz
      have hzR : ‖z‖ = (1 / 2 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hzR]
      norm_num only [one_div, inv_div, div_one]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hf z hz) (by norm_num))
        (by positivity)
    _ = _ := by ring

theorem norm_rowFactor_le {R : ℝ} (hR : 0 < R) {j : ℕ}
    (hc : ‖(j : ℂ) * period‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) :
    ‖rowFactor R j ell d‖ ≤ (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by
  have hf : ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2),
      ‖(((j : ℂ) * period + Complex.log (1 + t)) / (R : ℂ)) ^ d‖ ≤
        (1 / 2 : ℝ) ^ d := by
    intro t ht
    have ht' : ‖t‖ ≤ (1 / 2 : ℝ) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ht.le
    rw [norm_pow]
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    apply (div_le_iff₀ hR).mpr
    have hl := Complex.norm_log_one_add_half_le_self ht'
    have htri := norm_add_le ((j : ℂ) * period) (Complex.log (1 + t))
    nlinarith
  unfold rowFactor
  exact norm_cauchy_half_le hf ell

theorem period_center_bound {K j : ℕ} (hK : 0 < K) (hj : j < K) :
    ‖(j : ℂ) * period‖ + 3 / 4 ≤ (100 * (K : ℝ)) / 2 := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj.le
  have hn : ‖(j : ℂ) * period‖ = (j : ℝ) * (2 * Real.pi) := by
    simp [period, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hn]
  have hp : 2 * Real.pi ≤ (8 : ℝ) := by nlinarith [Real.pi_le_four]
  have hb : (j : ℝ) * (2 * Real.pi) ≤ (K : ℝ) * 8 :=
    mul_le_mul hjK hp (by positivity) (by positivity)
  linarith

theorem norm_columnFunction_le {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) (w : Fin m → ℝ) {R H w0 wmin : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hwmin : 0 < wmin)
    (hw : ∀ i, wmin ≤ w i)
    (hcol : w0 * h + ∑ i, w i * a i ≤ H) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖columnFunction h a A z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wmin)) := by
  have hwpos (i : Fin m) : 0 ≤ w i := hwmin.le.trans (hw i)
  have hs0 : 0 ≤ ∑ i, w i * a i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hwpos i) (Nat.cast_nonneg _)
  have hh : ‖(h : ℂ)‖ ≤ H / w0 := by
    rw [Complex.norm_natCast, le_div_iff₀ hw0]
    nlinarith
  have htot : (((∑ i, a i : ℕ) : ℝ)) ≤ H / wmin := by
    rw [le_div_iff₀ hwmin]
    have hs : wmin * ∑ i, (a i : ℝ) ≤ ∑ i, w i * a i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
    have hcast : ((∑ i, a i : ℕ) : ℝ) = ∑ i, (a i : ℝ) := by push_cast; rfl
    rw [hcast]
    nlinarith [mul_nonneg hw0.le (Nat.cast_nonneg h)]
  have hb : ‖((∏ i, (a i).choose (A i) : ℕ) : ℂ)‖ ≤ (2 : ℝ) ^ (∑ i, a i) := by
    rw [Complex.norm_natCast]
    have hn : (∏ i, (a i).choose (A i) : ℕ) ≤ 2 ^ (∑ i, a i) := by
      calc
        _ ≤ ∏ i, 2 ^ a i := Finset.prod_le_prod
          (fun i _ => Nat.zero_le _) (fun i _ => Nat.choose_le_two_pow _ _)
        _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
    exact_mod_cast hn
  have hd : (∑ i, (a i - A i)) ≤ ∑ i, a i :=
    Finset.sum_le_sum fun i _ => Nat.sub_le _ _
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have h2R : 0 < 2 * R := by positivity
  have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  unfold columnFunction
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ ‖((∏ i, (a i).choose (A i) : ℕ) : ℂ)‖ *
        Real.exp (‖(h : ℂ)‖ * R) * R ^ (∑ i, (a i - A i)) := by
      apply mul_le_mul
      · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (Complex.norm_exp_le_exp_norm _).trans
          (Real.exp_le_exp.mpr (by simpa only [norm_mul] using
            mul_le_mul_of_nonneg_left hz (norm_nonneg (h : ℂ))))
      · exact pow_le_pow_left₀ (norm_nonneg z) hz _
      · positivity
      · positivity
    _ ≤ (2 : ℝ) ^ (∑ i, a i) * Real.exp ((H / w0) * R) * R ^ (∑ i, a i) := by
      apply mul_le_mul
      · exact mul_le_mul hb (Real.exp_le_exp.mpr
          (mul_le_mul hh le_rfl hR0 (div_nonneg hH hw0.le)))
          (Real.exp_pos _).le (by positivity)
      · exact pow_le_pow_right₀ hR hd
      · positivity
      · positivity
    _ = Real.exp ((H / w0) * R + ((∑ i, a i : ℕ) : ℝ) * Real.log (2 * R)) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log h2R, mul_pow]
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ha := mul_le_mul_of_nonneg_right htot hlog
      calc
        _ ≤ (H / w0) * R + (H / wmin) * Real.log (2 * R) := add_le_add le_rfl ha
        _ = _ := by ring

theorem norm_columnFactor_le {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) (w : Fin m → ℝ) {R H w0 wmin : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hwmin : 0 < wmin)
    (hw : ∀ i, wmin ≤ w i) (hcol : w0 * h + ∑ i, w i * a i ≤ H) (d : ℕ) :
    ‖columnFactor R h a A d‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wmin)) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  unfold columnFactor
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ R * (R⁻¹ * Real.exp (H * (R / w0 + Real.log (2 * R) / wmin))) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hRpos.le
      intro z hz
      have hzR : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hRpos, norm_inv, hzR, div_self (ne_of_gt hRpos),
        one_pow, one_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_columnFunction_le h a A w hR hH hw0 hwmin hw hcol hzR.le)
        (inv_nonneg.mpr hRpos.le)
    _ = _ := by field_simp

end OAI.PiExponent.PeriodCollisionProof_713626a7

theorem solution
    {m : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (transverse : κ → Fin m →₀ ℕ)
    (j ell : ι → ℕ) (h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    {K : ℕ} {H w0 v0 wmin : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hw0 : 0 < w0) (hwmin0 : 0 < wmin)
    (hw : ∀ i, wmin ≤ w i) (hj : ∀ r, j r < K)
    (hcol : ∀ c, w0 * h c + ∑ i, w i * a c i ≤ H)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v0) :
    ‖Matrix.det (fun r c => PowerSeries.coeff (ell r)
      ((OAI.PiExponent.FiniteMinorAnalysis_690acb6f.periodMonomial (j r) (h c) (a c)).coeff
        (transverse (group r))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A : κ,
          (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity group A : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.holomorphicError K w0 v0 wmin +
            OAI.PiExponent.FiniteMinorAnalysis_690acb6f.collisionRemainder (Fintype.card ι) H)) := by
  let R : ℝ := 100 * (K : ℝ)
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    dsimp [R]
    linarith
  have hc (r : ι) : ‖(j r : ℂ) * period‖ + 3 / 4 ≤ R / 2 :=
    PeriodCollisionProof_713626a7.period_center_bound hK (hj r)
  let A : ℝ := R / w0 + Real.log (2 * R) / wmin
  have hb := PeriodCollisionProof_713626a7.infinite_collision_bound group
    (fun r d => rowFactor R (j r) (ell r) d)
    (fun A d c => columnFactor R (h c) (a c) (transverse A) d)
    (Real.exp (H * A)) PeriodCollisionProof_713626a7.ratio (fun r => (2 : ℝ) ^ ell r)
    (Real.exp_pos _).le PeriodCollisionProof_713626a7.ratio_pos.le
    PeriodCollisionProof_713626a7.ratio_lt_one (fun _ => by positivity)
    (fun A d c => PeriodCollisionProof_713626a7.norm_columnFactor_le
      (h c) (a c) (transverse A) w hR1 hH.le hw0 hwmin0 hw (hcol c) d)
    (fun r d => by
      rw [PeriodCollisionProof_713626a7.ratio_mul_self]
      exact PeriodCollisionProof_713626a7.norm_rowFactor_le hR (hc r) (ell r) d)
    (fun r c => PowerSeries.coeff (ell r) ((periodMonomial (j r) (h c) (a c)).coeff
      (transverse (group r))))
    (fun r c => period_coefficient_hasSum R (j r) (h c) (ell r) (a c)
      (transverse (group r)) hR (hc r))
  simp only [Finset.prod_pow_eq_pow_sum] at hb
  have hn := PeriodCollisionProof_713626a7.collision_factor_le_exp
    (Fintype.card ι) (∑ A, (multiplicity group A).choose 2) (∑ r, ell r)
    (A := A) hH hell (PeriodCollisionProof_713626a7.twice_collision_count group)
  have he : A + Real.log 2 / v0 = holomorphicError K w0 v0 wmin := by
    dsimp [A, R, holomorphicError]
    rw [show (2 : ℝ) * (100 * K) = 200 * K by ring]
    ring
  rw [he] at hn
  exact hb.trans hn
