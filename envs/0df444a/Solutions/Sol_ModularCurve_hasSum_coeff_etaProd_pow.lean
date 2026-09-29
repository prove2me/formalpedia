-- Prove2me | solution 1 for ModularCurve.hasSum_coeff_etaProd_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3d47c8ce-f3f4-54b8-ae81-186ddc4cde29

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasSum_coeff_etaProd_pow
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_hasSum_coeff_etaProd_pow.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "etaProd"
p2m_open "ModularCurve"
namespace EtaQSeries

open Filter Topology Polynomial
open scoped PowerSeries.WithPiTopology

def f (N : ℕ) : PowerSeries ℤ := ∏ n ∈ Finset.range N, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))

def Cong (m : ℕ) (G : PowerSeries ℤ) : Prop := (PowerSeries.X : PowerSeries ℤ) ^ (m + 1) ∣ G - 1

theorem Cong.mul {m : ℕ} {G H : PowerSeries ℤ} (hG : Cong m G) (hH : Cong m H) : Cong m (G * H) := by
  have : G * H - 1 = (G - 1) * H + (H - 1) := by ring
  rw [Cong, this]
  exact dvd_add (hG.mul_right _) hH

theorem Cong.one (m : ℕ) : Cong m 1 := by simp [Cong]

theorem Cong.pow {m : ℕ} {G : PowerSeries ℤ} (hG : Cong m G) (a : ℕ) : Cong m (G ^ a) := by
  induction a with
  | zero => simpa using Cong.one m
  | succ a ih => rw [pow_succ]; exact ih.mul hG

theorem Cong.prod {m : ℕ} {ι : Type*} (s : Finset ι) {g : ι → PowerSeries ℤ} (hg : ∀ i ∈ s, Cong m (g i)) :
    Cong m (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cong.one m
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hg i (Finset.mem_insert_self i s)).mul (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem Cong.one_sub_X_pow {m n : ℕ} (hn : m + 1 ≤ n + 1) : Cong m (1 - PowerSeries.X ^ (n + 1)) := by
  rw [Cong, sub_sub_cancel_left, dvd_neg]
  exact pow_dvd_pow _ hn

theorem coeff_mul_of_cong {m : ℕ} {G : PowerSeries ℤ} (hG : Cong m G) (H : PowerSeries ℤ) :
    PowerSeries.coeff m (H * G) = PowerSeries.coeff m H := by
  obtain ⟨K, hK⟩ := hG
  have : G = 1 + PowerSeries.X ^ (m + 1) * K := by rw [← hK]; ring
  rw [this, mul_add, mul_one, map_add, ← mul_assoc, mul_comm H, mul_assoc, PowerSeries.coeff_X_pow_mul',
    if_neg (by omega), add_zero]

theorem coeff_prod_pow_eq (a m : ℕ) (s : Finset ℕ) (hs : Finset.range (m + 1) ⊆ s) :
    PowerSeries.coeff m ((∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) ^ a) =
      PowerSeries.coeff m (f (m + 1) ^ a) := by
  rw [← Finset.prod_sdiff hs, mul_pow, mul_comm, f]
  apply coeff_mul_of_cong
  apply Cong.pow
  apply Cong.prod
  intro n hn
  rw [Finset.mem_sdiff, Finset.mem_range, not_lt] at hn
  exact Cong.one_sub_X_pow (by omega)

theorem coeff_etaProd_pow (a m : ℕ) :
    PowerSeries.coeff m (etaProd ^ a) = PowerSeries.coeff m (f (m + 1) ^ a) := by
  have hmult := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ
  have h1 : Tendsto (fun s : Finset ℕ => ∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) atTop
      (𝓝 etaProd) := hmult.hasProd
  have h2 : Tendsto (fun s : Finset ℕ =>
      PowerSeries.coeff m ((∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) ^ a)) atTop
      (𝓝 (PowerSeries.coeff m (etaProd ^ a))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℤ m).tendsto _).comp (h1.pow a)
  have h3 : Tendsto (fun s : Finset ℕ =>
      PowerSeries.coeff m ((∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) ^ a)) atTop
      (𝓝 (PowerSeries.coeff m (f (m + 1) ^ a))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (Finset.range (m + 1))] with s hs
    exact (coeff_prod_pow_eq a m s hs).symm
  exact tendsto_nhds_unique h2 h3

theorem coeff_etaProd_pow_eq_coeff_f (a m N : ℕ) (hN : m < N) :
    PowerSeries.coeff m (etaProd ^ a) = PowerSeries.coeff m (f N ^ a) := by
  rw [coeff_etaProd_pow]
  exact (coeff_prod_pow_eq a m (Finset.range N) (Finset.range_subset_range.mpr hN)).symm

def p (N : ℕ) : Polynomial ℤ := ∏ n ∈ Finset.range N, ((1 : Polynomial ℤ) - Polynomial.X ^ (n + 1))

theorem coe_p (N : ℕ) : ((p N : Polynomial ℤ) : PowerSeries ℤ) = f N := by
  rw [p, f, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl (fun n _ => ?_)
  rw [map_sub, map_one, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem coeff_f_pow (a N m : ℕ) : PowerSeries.coeff m (f N ^ a) = (p N ^ a).coeff m := by
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow, coe_p]

theorem eval₂_p_pow (a N : ℕ) (q : ℂ) :
    (p N ^ a).eval₂ (Int.castRingHom ℂ) q = (∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ a := by
  rw [Polynomial.eval₂_pow, p, Polynomial.eval₂_finsetProd]
  simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow]

theorem hasSum_partial (a N : ℕ) (q : ℂ) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (f N ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ a) := by
  rw [← eval₂_p_pow, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  simp_rw [coeff_f_pow]
  apply hasSum_sum_of_ne_finset_zero
  intro m hm
  rw [Polynomial.notMem_support_iff.mp hm, Int.cast_zero, zero_mul]

def Maj (φ : Polynomial ℤ) (Φ : Polynomial ℝ) : Prop := ∀ m, |((φ.coeff m : ℤ) : ℝ)| ≤ Φ.coeff m

theorem Maj.nonneg {φ : Polynomial ℤ} {Φ : Polynomial ℝ} (h : Maj φ Φ) (m : ℕ) : 0 ≤ Φ.coeff m :=
  (abs_nonneg _).trans (h m)

theorem Maj.mul {φ ψ : Polynomial ℤ} {Φ Ψ : Polynomial ℝ} (hφ : Maj φ Φ) (hψ : Maj ψ Ψ) : Maj (φ * ψ) (Φ * Ψ) := by
  intro m
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul, Int.cast_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [Int.cast_mul, abs_mul]
  exact mul_le_mul (hφ _) (hψ _) (abs_nonneg _) (hφ.nonneg _)

theorem Maj.one : Maj 1 1 := by
  intro m
  rw [Polynomial.coeff_one, Polynomial.coeff_one]
  split_ifs <;> simp

theorem Maj.pow {φ : Polynomial ℤ} {Φ : Polynomial ℝ} (h : Maj φ Φ) (a : ℕ) : Maj (φ ^ a) (Φ ^ a) := by
  induction a with
  | zero => simpa using Maj.one
  | succ a ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem Maj.prod {ι : Type*} (s : Finset ι) {φ : ι → Polynomial ℤ} {Φ : ι → Polynomial ℝ}
    (h : ∀ i ∈ s, Maj (φ i) (Φ i)) : Maj (∏ i ∈ s, φ i) (∏ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Maj.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem Maj.one_sub_X_pow (k : ℕ) : Maj (1 - Polynomial.X ^ k) (1 + Polynomial.X ^ k) := by
  intro m
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_pow, Int.cast_sub]
  refine (abs_sub _ _).trans ?_
  split_ifs <;> simp

def P (N : ℕ) : Polynomial ℝ := ∏ n ∈ Finset.range N, ((1 : Polynomial ℝ) + Polynomial.X ^ (n + 1))

theorem maj_p_pow (a N : ℕ) : Maj (p N ^ a) (P N ^ a) :=
  (Maj.prod (Finset.range N) fun n _ => Maj.one_sub_X_pow (n + 1)).pow a

theorem eval_P_pow (a N : ℕ) (r : ℝ) : (P N ^ a).eval r = (∏ n ∈ Finset.range N, (1 + r ^ (n + 1))) ^ a := by
  rw [Polynomial.eval_pow, P, Polynomial.eval_prod]
  simp

theorem coeff_mul_pow_le_eval {Φ : Polynomial ℝ} (hΦ : ∀ m, 0 ≤ Φ.coeff m) {r : ℝ} (hr : 0 ≤ r) (m : ℕ) :
    Φ.coeff m * r ^ m ≤ Φ.eval r := by
  rw [Polynomial.eval_eq_sum_range' (n := max (Φ.natDegree + 1) (m + 1)) (lt_max_of_lt_left (Nat.lt_succ_self _))]
  refine Finset.single_le_sum (f := fun i => Φ.coeff i * r ^ i) (fun i _ => mul_nonneg (hΦ i) (pow_nonneg hr i))
    (Finset.mem_range.mpr (lt_max_of_lt_right (Nat.lt_succ_self m)))

theorem prod_one_add_le_exp {N : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∏ n ∈ Finset.range N, (1 + r ^ (n + 1)) ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) := by
  have hsum : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
  calc ∏ n ∈ Finset.range N, (1 + r ^ (n + 1)) ≤ ∏ n ∈ Finset.range N, Real.exp (r ^ (n + 1)) :=
        Finset.prod_le_prod (fun n _ => by positivity) (fun n _ => by
          have := Real.add_one_le_exp (r ^ (n + 1)); linarith)
    _ = Real.exp (∑ n ∈ Finset.range N, r ^ (n + 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) :=
        Real.exp_le_exp.mpr (hsum.sum_le_tsum _ (fun n _ => pow_nonneg hr0 _))

theorem norm_coeff_f_pow_mul_le (a N m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * r ^ m ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) ^ a := by
  have hmaj := maj_p_pow a N
  calc |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * r ^ m ≤ (P N ^ a).coeff m * r ^ m := by
        rw [coeff_f_pow]; exact mul_le_mul_of_nonneg_right (hmaj m) (pow_nonneg hr0 m)
    _ ≤ (P N ^ a).eval r := coeff_mul_pow_le_eval hmaj.nonneg hr0 m
    _ = (∏ n ∈ Finset.range N, (1 + r ^ (n + 1))) ^ a := eval_P_pow a N r
    _ ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) ^ a :=
        pow_le_pow_left₀ (Finset.prod_nonneg fun n _ => by positivity) (prod_one_add_le_exp hr0 hr1) a

theorem main (a : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a) := by

  set r : ℝ := (‖q‖ + 1) / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hqr : ‖q‖ < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg q) hqr
  set ρ : ℝ := ‖q‖ / r with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (norm_nonneg q) hr0
  have hρ1 : ρ < 1 := (div_lt_one hrpos).mpr hqr
  set C : ℝ := Real.exp (∑' n : ℕ, r ^ (n + 1)) ^ a with hC

  let F : ℕ → ℕ → ℂ := fun N m => ((PowerSeries.coeff m (f N ^ a) : ℤ) : ℂ) * q ^ m
  let g : ℕ → ℂ := fun m => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m
  have hbound : ∀ N m, ‖F N m‖ ≤ C * ρ ^ m := by
    intro N m
    have h1 := norm_coeff_f_pow_mul_le a N m hr0 hr1
    have hqm : ‖q‖ ^ m = r ^ m * ρ ^ m := by
      rw [← mul_pow, hρ, mul_div_cancel₀ _ hrpos.ne']
    calc ‖F N m‖ = |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * ‖q‖ ^ m := by
          simp only [F, norm_mul, norm_pow, Complex.norm_intCast]
      _ = |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * r ^ m * ρ ^ m := by rw [hqm, mul_assoc]
      _ ≤ C * ρ ^ m := mul_le_mul_of_nonneg_right h1 (pow_nonneg hρ0 m)
  have hsumm : Summable (fun m : ℕ => C * ρ ^ m) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left C
  have hlim : ∀ m, Tendsto (fun N => F N m) atTop (𝓝 (g m)) := by
    intro m
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop m] with N hN
    simp only [F, g, coeff_etaProd_pow_eq_coeff_f a m N hN]

  have hT : Tendsto (fun N => ∑' m, F N m) atTop (𝓝 (∑' m, g m)) :=
    tendsto_tsum_of_dominated_convergence hsumm hlim (Eventually.of_forall hbound)

  have hP : ∀ N, ∑' m, F N m = (∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ a :=
    fun N => (hasSum_partial a N q).tsum_eq
  have hA : Tendsto (fun N => ∑' m, F N m) atTop (𝓝 ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a)) := by
    simp_rw [hP]
    exact ((ModularForm.multipliable_one_sub_pow hq).hasProd.tendsto_prod_nat).pow a
  have heq : ∑' m, g m = (∏' n : ℕ, (1 - q ^ (n + 1))) ^ a := tendsto_nhds_unique hT hA

  have hg : Summable g := by
    refine Summable.of_norm_bounded hsumm (fun m => ?_)
    have := hbound (m + 1) m
    simpa only [F, g, coeff_etaProd_pow_eq_coeff_f a m (m + 1) (Nat.lt_succ_self m)] using this
  rw [← heq]
  exact hg.hasSum

end EtaQSeries
end ModularCurve

end

theorem solution (a : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a) :=
  ModularCurve.EtaQSeries.main a hq

end S_ModularCurve_hasSum_coeff_etaProd_pow
end P2MW
export P2MW.S_ModularCurve_hasSum_coeff_etaProd_pow (solution)
