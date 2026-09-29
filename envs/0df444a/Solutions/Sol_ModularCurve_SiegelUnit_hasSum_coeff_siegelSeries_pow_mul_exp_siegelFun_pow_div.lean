-- Prove2me | solution 1 for ModularCurve.SiegelUnit.hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8e61b3a2-f913-5fc2-a528-27536399f76d

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Definitions.Def_ModularCurve_LevelFunctionField
import Theorems.Thm_ModularCurve_hasSum_qParam_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div

set_option autoImplicit false

noncomputable section

open Filter Topology Polynomial
open scoped PowerSeries.WithPiTopology

namespace ModularCurve
p2m_export "ModularCurve" "siegelFun siegelFun_def zetaQ zetaQ_pow zetaSubring zetaQ_mem_zetaSubring multipliable_one_sub_C_mul_X_pow siegelExponent siegelConstExponent siegelSeriesInt multipliable_siegelFactor_left multipliable_siegelFactor_right siegelSeries hasSum_qParam_mul"
namespace SiegelUnit
namespace L2
p2m_open "ModularCurve"

namespace EulerProdFam

section Formal

variable {R : Type*} [CommRing R]

def fac (P : ℕ → R[X]) (n : ℕ) : PowerSeries R :=
  ((Polynomial.expand R (n + 1) (P n) : R[X]) : PowerSeries R)

def pp (P : ℕ → R[X]) (N : ℕ) : R[X] := ∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n)

theorem pp_zero (P : ℕ → R[X]) : pp P 0 = 1 := Finset.prod_range_zero _

theorem pp_succ (P : ℕ → R[X]) (N : ℕ) : pp P (N + 1) = pp P N * Polynomial.expand R (N + 1) (P N) :=
  Finset.prod_range_succ _ _

theorem coe_pp (P : ℕ → R[X]) (N : ℕ) :
    ((pp P N : R[X]) : PowerSeries R) = ∏ n ∈ Finset.range N, fac P n := by
  show Polynomial.coeToPowerSeries.ringHom (∏ n ∈ Finset.range N, Polynomial.expand R (n + 1) (P n))
    = _
  rw [map_prod]
  rfl

variable {P : ℕ → R[X]}

theorem fac_sub_one (P : ℕ → R[X]) (n : ℕ) :
    fac P n - 1 = ((Polynomial.expand R (n + 1) (P n - 1) : R[X]) : PowerSeries R) := by
  unfold fac
  rw [map_sub, map_one, Polynomial.coe_sub, Polynomial.coe_one]

theorem coeff_fac_sub_one (hP : ∀ n, (P n).coeff 0 = 1) (n i : ℕ) (hi : i < n + 1) :
    PowerSeries.coeff i (fac P n - 1) = 0 := by
  rw [fac_sub_one, Polynomial.coeff_coe, Polynomial.coeff_expand (Nat.succ_pos n)]
  split_ifs with hd
  · rw [Nat.eq_zero_of_dvd_of_lt hd hi, Nat.zero_div, Polynomial.coeff_sub,
      Polynomial.coeff_one_zero, hP n, sub_self]
  · rfl

theorem order_fac_sub_one (hP : ∀ n, (P n).coeff 0 = 1) (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (fac P n - 1).order :=
  PowerSeries.nat_le_order _ _ fun i hi => coeff_fac_sub_one hP n i hi

theorem coeff_mul_fac_of_le (hP : ∀ n, (P n).coeff 0 = 1) {m n : ℕ} (h : m ≤ n) (φ : PowerSeries R) :
    PowerSeries.coeff m (φ * fac P n) = PowerSeries.coeff m φ := by
  have : φ * fac P n = φ + φ * (fac P n - 1) := by ring
  rw [this, map_add, PowerSeries.coeff_mul_of_lt_order, add_zero]
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le h) (order_fac_sub_one hP n)

theorem coeff_prod_range_fac (hP : ∀ n, (P n).coeff 0 = 1) (m N : ℕ) (hN : m ≤ N) :
    PowerSeries.coeff m (∏ n ∈ Finset.range N, fac P n) =
      PowerSeries.coeff m (∏ n ∈ Finset.range m, fac P n) := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hmN ih => rw [Finset.prod_range_succ, coeff_mul_fac_of_le hP hmN, ih]

theorem coeff_pp_stable (hP : ∀ n, (P n).coeff 0 = 1) {m N : ℕ} (h : m ≤ N) :
    (pp P N).coeff m = (pp P m).coeff m := by
  have := coeff_prod_range_fac hP m N h
  rwa [← coe_pp, ← coe_pp, Polynomial.coeff_coe, Polynomial.coeff_coe] at this

theorem map_fac {S : Type*} [CommRing S] (φ : R →+* S) (P : ℕ → R[X]) (n : ℕ) :
    PowerSeries.map φ (fac P n) = fac (fun k => (P k).map φ) n := by
  ext i
  rw [PowerSeries.coeff_map, fac, fac, Polynomial.coeff_coe, Polynomial.coeff_coe,
    ← Polynomial.map_expand, Polynomial.coeff_map]

section Topological

variable [TopologicalSpace R]

def W (P : ℕ → R[X]) : PowerSeries R := ∏' n : ℕ, fac P n

theorem multipliable_fac (hP : ∀ n, (P n).coeff 0 = 1) : Multipliable (fac P) := by
  have h : Multipliable (fun n => 1 + (fac P n - 1)) := by
    apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun m => Filter.eventually_atTop.mpr
      ⟨m, fun n hn => ?_⟩
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hn) (order_fac_sub_one hP n)
  exact h.congr fun n => add_sub_cancel 1 (fac P n)

theorem coeff_W [T2Space R] (hP : ∀ n, (P n).coeff 0 = 1) {m N : ℕ} (h : m ≤ N) :
    PowerSeries.coeff m (W P) = (pp P N).coeff m := by
  rw [coeff_pp_stable hP h, ← Polynomial.coeff_coe, coe_pp]
  have ht : Tendsto (fun N => PowerSeries.coeff m (∏ n ∈ Finset.range N, fac P n)) atTop
      (𝓝 (PowerSeries.coeff m (W P))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff R m).tendsto _).comp
      (multipliable_fac hP).tendsto_prod_tprod_nat
  have hc : Tendsto (fun N => PowerSeries.coeff m (∏ n ∈ Finset.range N, fac P n)) atTop
      (𝓝 (PowerSeries.coeff m (∏ n ∈ Finset.range m, fac P n))) :=
    tendsto_const_nhds.congr' (Filter.eventuallyEq_of_mem (Filter.Ici_mem_atTop m)
      fun N hN => (coeff_prod_range_fac hP m N hN).symm)
  exact tendsto_nhds_unique ht hc

theorem continuous_map {S : Type*} [CommRing S] [TopologicalSpace S] (φ : R →+* S)
    (hφ : Continuous φ) : Continuous (PowerSeries.map (R := R) φ) := by
  refine continuous_iff_continuousAt.mpr fun f => ?_
  change Tendsto (PowerSeries.map φ) (𝓝 f) (𝓝 (PowerSeries.map φ f))
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  simp only [PowerSeries.coeff_map]
  exact (hφ.tendsto _).comp (PowerSeries.WithPiTopology.continuous_coeff R d).continuousAt

theorem map_W {S : Type*} [CommRing S] [TopologicalSpace S] [T2Space S] (φ : R →+* S)
    (hφ : Continuous φ) (hP : ∀ n, (P n).coeff 0 = 1) :
    PowerSeries.map φ (W P) = W (fun k => (P k).map φ) := by
  have h1 : HasProd (fac P) (W P) := (multipliable_fac hP).hasProd
  have h2 := h1.map (PowerSeries.map φ) (continuous_map φ hφ)
  have hfun : (⇑(PowerSeries.map φ) ∘ fac P) = fac (fun k => (P k).map φ) := funext fun n => map_fac φ P n
  rw [hfun] at h2
  exact h2.tprod_eq.symm

theorem constantCoeff_W [T2Space R] (hP : ∀ n, (P n).coeff 0 = 1) :
    PowerSeries.constantCoeff (W P) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_W hP (le_refl 0), pp_zero,
    Polynomial.coeff_one_zero]

end Topological

end Formal

section Analytic

variable {P : ℕ → ℂ[X]} {M : ℂ[X]}

def Pabs (M : ℂ[X]) : ℝ[X] := ∑ k ∈ M.support, Polynomial.monomial k ‖M.coeff k‖

def Cst (M : ℂ[X]) : ℝ := ∑ k ∈ M.support, ‖M.coeff k‖

theorem Cst_nonneg (M : ℂ[X]) : 0 ≤ Cst M := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem coeff_Pabs (M : ℂ[X]) (k : ℕ) : (Pabs M).coeff k = ‖M.coeff k‖ := by
  classical
  rw [Pabs, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Polynomial.mem_support_iff, ne_eq]
  split_ifs with h
  · rw [h, norm_zero]
  · rfl

theorem coeff_Pabs_zero (hM : M.coeff 0 = 1) : (Pabs M).coeff 0 = 1 := by
  rw [coeff_Pabs, hM, norm_one]

theorem coeff_Pabs_nonneg (M : ℂ[X]) (k : ℕ) : 0 ≤ (Pabs M).coeff k := by
  rw [coeff_Pabs]; exact norm_nonneg _

theorem zero_mem_support {Q : ℂ[X]} (hQ : Q.coeff 0 = 1) : (0 : ℕ) ∈ Q.support :=
  Polynomial.mem_support_iff.mpr (by rw [hQ]; exact one_ne_zero)

theorem eval_sub_one_eq {Q : ℂ[X]} (hQ : Q.coeff 0 = 1) (x : ℂ) :
    Q.eval x - 1 = ∑ k ∈ Q.support.erase 0, Q.coeff k * x ^ k := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, ← Finset.add_sum_erase _ _ (zero_mem_support hQ),
    hQ, pow_zero, one_mul, add_sub_cancel_left]

theorem norm_eval_sub_one_le {Q : ℂ[X]} (hQ : Q.coeff 0 = 1) (hdom : ∀ k, ‖Q.coeff k‖ ≤ ‖M.coeff k‖)
    {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖Q.eval x - 1‖ ≤ Cst M * ‖x‖ := by
  rw [eval_sub_one_eq hQ]
  refine (norm_sum_le _ _).trans ?_
  have hsub : Q.support.erase 0 ⊆ M.support := by
    intro k hk
    have hk' : Q.coeff k ≠ 0 := Polynomial.mem_support_iff.mp (Finset.mem_of_mem_erase hk)
    refine Polynomial.mem_support_iff.mpr fun h0 => hk' ?_
    have := hdom k
    rw [h0, norm_zero] at this
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
  calc ∑ k ∈ Q.support.erase 0, ‖Q.coeff k * x ^ k‖
      ≤ ∑ k ∈ Q.support.erase 0, ‖M.coeff k‖ * ‖x‖ := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [norm_mul, norm_pow]
        refine mul_le_mul (hdom k) ?_ (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase hk)
        calc ‖x‖ ^ k ≤ ‖x‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hx hk1
          _ = ‖x‖ := pow_one _
    _ ≤ ∑ k ∈ M.support, ‖M.coeff k‖ * ‖x‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun k _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    _ = Cst M * ‖x‖ := by rw [Cst, Finset.sum_mul]

theorem eval_Pabs (M : ℂ[X]) (r : ℝ) :
    (Pabs M).eval r = ∑ k ∈ M.support, ‖M.coeff k‖ * r ^ k := by
  rw [Pabs, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]

theorem eval_Pabs_sub_one_eq (hM : M.coeff 0 = 1) (r : ℝ) :
    (Pabs M).eval r - 1 = ∑ k ∈ M.support.erase 0, ‖M.coeff k‖ * r ^ k := by
  rw [eval_Pabs, ← Finset.add_sum_erase _ _ (zero_mem_support hM), hM, norm_one, pow_zero,
    one_mul, add_sub_cancel_left]

theorem one_le_eval_Pabs (hM : M.coeff 0 = 1) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ (Pabs M).eval r := by
  have h := eval_Pabs_sub_one_eq hM r
  have h0 : 0 ≤ ∑ k ∈ M.support.erase 0, ‖M.coeff k‖ * r ^ k :=
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr _)
  linarith

theorem eval_Pabs_sub_one_le (hM : M.coeff 0 = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (Pabs M).eval r - 1 ≤ Cst M * r := by
  rw [eval_Pabs_sub_one_eq hM]
  calc ∑ k ∈ M.support.erase 0, ‖M.coeff k‖ * r ^ k
      ≤ ∑ k ∈ M.support.erase 0, ‖M.coeff k‖ * r := by
        refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase hk)
        calc r ^ k ≤ r ^ 1 := pow_le_pow_of_le_one hr hr1 hk1
          _ = r := pow_one _
    _ ≤ ∑ k ∈ M.support, ‖M.coeff k‖ * r :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          fun k _ _ => mul_nonneg (norm_nonneg _) hr
    _ = Cst M * r := by rw [Cst, Finset.sum_mul]

def Mfam (M : ℂ[X]) : ℕ → ℝ[X] := fun _ => Pabs M

@[scoped simp] theorem Mfam_apply (M : ℂ[X]) (n : ℕ) : Mfam M n = Pabs M := rfl

theorem norm_coeff_mul_le {f g : ℂ[X]} {F G : ℝ[X]} (hf : ∀ k, ‖f.coeff k‖ ≤ F.coeff k)
    (hg : ∀ k, ‖g.coeff k‖ ≤ G.coeff k) (k : ℕ) : ‖(f * g).coeff k‖ ≤ (F * G).coeff k := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) ((norm_nonneg _).trans (hf _))

theorem norm_coeff_expand_le {f : ℂ[X]} {F : ℝ[X]} (hf : ∀ k, ‖f.coeff k‖ ≤ F.coeff k)
    {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ‖(Polynomial.expand ℂ m f).coeff k‖ ≤ (Polynomial.expand ℝ m F).coeff k := by
  rw [Polynomial.coeff_expand hm, Polynomial.coeff_expand hm]
  split_ifs
  · exact hf _
  · rw [norm_zero]

theorem norm_coeff_pp_le (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖) (N k : ℕ) :
    ‖(pp P N).coeff k‖ ≤ (pp (Mfam M) N).coeff k := by
  induction N generalizing k with
  | zero =>
    rw [pp_zero, pp_zero, Polynomial.coeff_one, Polynomial.coeff_one]
    split_ifs
    · rw [norm_one]
    · rw [norm_zero]
  | succ N ih =>
    rw [pp_succ, pp_succ]
    exact norm_coeff_mul_le ih
      (norm_coeff_expand_le (fun j => (hdom N j).trans (coeff_Pabs M j).symm.le) (Nat.succ_pos N)) k

theorem coeff_pp_Mfam_nonneg (M : ℂ[X]) (N k : ℕ) : 0 ≤ (pp (Mfam M) N).coeff k := by
  induction N generalizing k with
  | zero =>
    rw [pp_zero, Polynomial.coeff_one]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  | succ N ih =>
    rw [pp_succ, Polynomial.coeff_mul]
    refine Finset.sum_nonneg fun x _ => mul_nonneg (ih _) ?_
    rw [Mfam_apply, Polynomial.coeff_expand (Nat.succ_pos N)]
    split_ifs
    · exact coeff_Pabs_nonneg M _
    · exact le_rfl

theorem coeff_le_coeff_mul {F G : ℝ[X]} (hF : ∀ k, 0 ≤ F.coeff k) (hG : ∀ k, 0 ≤ G.coeff k)
    (hG0 : G.coeff 0 = 1) (k : ℕ) : F.coeff k ≤ (F * G).coeff k := by
  rw [Polynomial.coeff_mul]
  have hmem : (k, 0) ∈ Finset.HasAntidiagonal.antidiagonal k := by simp
  refine le_trans ?_ (Finset.single_le_sum (fun x _ => mul_nonneg (hF _) (hG _)) hmem)
  show F.coeff k ≤ F.coeff k * G.coeff 0
  rw [hG0, mul_one]

theorem coeff_expand_Pabs_nonneg (M : ℂ[X]) {m : ℕ} (hm : 0 < m) (k : ℕ) :
    0 ≤ (Polynomial.expand ℝ m (Pabs M)).coeff k := by
  rw [Polynomial.coeff_expand hm]
  split_ifs
  · exact coeff_Pabs_nonneg M _
  · exact le_rfl

theorem coeff_expand_Pabs_zero (hM : M.coeff 0 = 1) {m : ℕ} (hm : 0 < m) :
    (Polynomial.expand ℝ m (Pabs M)).coeff 0 = 1 := by
  rw [Polynomial.coeff_expand hm, if_pos (dvd_zero m), Nat.zero_div, coeff_Pabs_zero hM]

theorem coeff_pp_Mfam_mono (hM : M.coeff 0 = 1) {N N' : ℕ} (h : N ≤ N') (k : ℕ) :
    (pp (Mfam M) N).coeff k ≤ (pp (Mfam M) N').coeff k := by
  induction N', h using Nat.le_induction with
  | base => exact le_rfl
  | succ N' hN ih =>
    rw [pp_succ]
    exact ih.trans (coeff_le_coeff_mul (coeff_pp_Mfam_nonneg M N')
      (coeff_expand_Pabs_nonneg M (Nat.succ_pos N')) (coeff_expand_Pabs_zero hM (Nat.succ_pos N')) k)

def dom (M : ℂ[X]) (k : ℕ) : ℝ := (pp (Mfam M) k).coeff k

theorem Mfam_coeff_zero (hM : M.coeff 0 = 1) : ∀ n, (Mfam M n).coeff 0 = 1 :=
  fun _ => coeff_Pabs_zero hM

theorem norm_coeff_pp_le_dom (hM : M.coeff 0 = 1) (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖)
    (N k : ℕ) : ‖(pp P N).coeff k‖ ≤ dom M k := by
  refine (norm_coeff_pp_le hdom N k).trans ?_
  unfold dom
  rcases le_total N k with h | h
  · exact coeff_pp_Mfam_mono hM h k
  · exact (coeff_pp_stable (Mfam_coeff_zero hM) h).le

theorem sum_coeff_le_eval {Q : ℝ[X]} (hQ : ∀ k, 0 ≤ Q.coeff k) {r : ℝ} (hr : 0 ≤ r)
    (s : Finset ℕ) : ∑ k ∈ s, Q.coeff k * r ^ k ≤ Q.eval r := by
  classical
  have h1 : ∑ k ∈ s, Q.coeff k * r ^ k
      = ∑ k ∈ s.filter (fun k => k ∈ Q.support), Q.coeff k * r ^ k := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with h
    · rfl
    · rw [Polynomial.notMem_support_iff.mp h, zero_mul]
  have h2 : s.filter (fun k => k ∈ Q.support) ⊆ Q.support := fun k hk => (Finset.mem_filter.mp hk).2
  rw [h1, Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.sum_le_sum_of_subset_of_nonneg h2 fun k _ _ => mul_nonneg (hQ k) (pow_nonneg hr k)

theorem eval_pp {R : Type*} [CommRing R] (Q : ℕ → R[X]) (N : ℕ) (r : R) :
    (pp Q N).eval r = ∏ n ∈ Finset.range N, (Q n).eval (r ^ (n + 1)) := by
  rw [pp, Polynomial.eval_prod]
  simp only [Polynomial.expand_eval]

def Bd (M : ℂ[X]) (r : ℝ) : ℝ := Real.exp (Cst M * ∑' n : ℕ, r ^ (n + 1))

theorem summable_pow_succ {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : Summable fun n : ℕ => r ^ (n + 1) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr hr1)

theorem prod_eval_Pabs_le (hM : M.coeff 0 = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∏ n ∈ Finset.range N, (Mfam M n).eval (r ^ (n + 1)) ≤ Bd M r := by
  simp only [Mfam_apply]
  have hfac : ∀ n : ℕ, (Pabs M).eval (r ^ (n + 1)) = 1 + ((Pabs M).eval (r ^ (n + 1)) - 1) :=
    fun n => by ring
  have hnn : ∀ n : ℕ, 0 ≤ (Pabs M).eval (r ^ (n + 1)) - 1 :=
    fun n => sub_nonneg.mpr (one_le_eval_Pabs hM (pow_nonneg hr _))
  calc ∏ n ∈ Finset.range N, (Pabs M).eval (r ^ (n + 1))
      = ∏ n ∈ Finset.range N, (1 + ((Pabs M).eval (r ^ (n + 1)) - 1)) :=
        Finset.prod_congr rfl fun n _ => hfac n
    _ ≤ Real.exp (∑ n ∈ Finset.range N, ((Pabs M).eval (r ^ (n + 1)) - 1)) :=
        Real.prod_one_add_le_exp_sum _ hnn
    _ ≤ Real.exp (∑ n ∈ Finset.range N, Cst M * r ^ (n + 1)) := by
        refine Real.exp_le_exp.mpr (Finset.sum_le_sum fun n _ => ?_)
        exact eval_Pabs_sub_one_le hM (pow_nonneg hr _) (pow_le_one₀ hr hr1.le)
    _ ≤ Bd M r := by
        refine Real.exp_le_exp.mpr ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (Cst_nonneg M)
        exact (summable_pow_succ hr hr1).sum_le_tsum _ fun n _ => pow_nonneg hr _

theorem summable_dom (hM : M.coeff 0 = 1) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ => dom M k * r ^ k := by
  refine summable_of_sum_range_le (c := Bd M r)
    (fun k => mul_nonneg (coeff_pp_Mfam_nonneg M k k) (pow_nonneg hr k)) fun N => ?_
  calc ∑ k ∈ Finset.range N, dom M k * r ^ k
      ≤ ∑ k ∈ Finset.range N, (pp (Mfam M) N).coeff k * r ^ k := by
        refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (pow_nonneg hr k)
        exact coeff_pp_Mfam_mono hM (Finset.mem_range.mp hk).le k
    _ ≤ (pp (Mfam M) N).eval r := sum_coeff_le_eval (coeff_pp_Mfam_nonneg M N) hr _
    _ = ∏ n ∈ Finset.range N, (Mfam M n).eval (r ^ (n + 1)) := eval_pp _ _ _
    _ ≤ Bd M r := prod_eval_Pabs_le hM hr hr1 N

theorem summable_norm_eval_sub_one (hP : ∀ n, (P n).coeff 0 = 1)
    (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖(P n).eval (q ^ (n + 1)) - 1‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)).mul_left
      (Cst M))
  have h := norm_eval_sub_one_le (hP n) (hdom n) (x := q ^ (n + 1))
    (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hq.le)
  rwa [norm_pow] at h

theorem multipliable_eval (hP : ∀ n, (P n).coeff 0 = 1)
    (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖) {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => (P n).eval (q ^ (n + 1)) :=
  (multipliable_one_add_of_summable (summable_norm_eval_sub_one hP hdom hq)).congr
    fun _ => add_sub_cancel 1 _

theorem tprod_eval_ne_zero (hP : ∀ n, (P n).coeff 0 = 1)
    (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖) {q : ℂ} (hq : ‖q‖ < 1)
    (hne : ∀ n : ℕ, (P n).eval (q ^ (n + 1)) ≠ 0) : (∏' n : ℕ, (P n).eval (q ^ (n + 1))) ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => (P n).eval (q ^ (n + 1)) - 1)
    (fun n => by rw [add_sub_cancel]; exact hne n) (summable_norm_eval_sub_one hP hdom hq)
  simpa only [add_sub_cancel] using h

theorem tsum_coeff_pp_mul_pow (P : ℕ → ℂ[X]) (N : ℕ) (q : ℂ) :
    ∑' m : ℕ, (pp P N).coeff m * q ^ m = ∏ n ∈ Finset.range N, (P n).eval (q ^ (n + 1)) := by
  rw [← eval_pp, Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact tsum_eq_sum fun m hm => by rw [Polynomial.notMem_support_iff.mp hm, zero_mul]

theorem hasSum_coeff_W (hP : ∀ n, (P n).coeff 0 = 1) (hM : M.coeff 0 = 1)
    (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => PowerSeries.coeff m (W P) * q ^ m) (∏' n : ℕ, (P n).eval (q ^ (n + 1))) := by
  have hc : ∀ m, PowerSeries.coeff m (W P) = (pp P m).coeff m := fun m => coeff_W hP le_rfl
  have hsum : Summable fun m : ℕ => dom M m * ‖q‖ ^ m := summable_dom hM (norm_nonneg q) hq
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N m : ℕ) => (pp P N).coeff m * q ^ m)
    (g := fun m : ℕ => PowerSeries.coeff m (W P) * q ^ m) hsum ?_ ?_
  rotate_left
  · intro m
    refine tendsto_const_nhds.congr' (Filter.eventuallyEq_of_mem (Filter.Ici_mem_atTop m)
      fun N hN => ?_)
    show PowerSeries.coeff m (W P) * q ^ m = (pp P N).coeff m * q ^ m
    rw [hc m, coeff_pp_stable hP (show m ≤ N from hN)]
  · refine Eventually.of_forall fun N m => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (norm_coeff_pp_le_dom hM hdom N m) (pow_nonneg (norm_nonneg _) _)
  simp_rw [tsum_coeff_pp_mul_pow] at hT
  have heq : (∑' m : ℕ, PowerSeries.coeff m (W P) * q ^ m) = ∏' n : ℕ, (P n).eval (q ^ (n + 1)) :=
    tendsto_nhds_unique hT (multipliable_eval hP hdom hq).tendsto_prod_tprod_nat
  have hs : Summable fun m : ℕ => PowerSeries.coeff m (W P) * q ^ m :=
    Summable.of_norm_bounded hsum fun m => by
      rw [norm_mul, norm_pow, hc m]
      exact mul_le_mul_of_nonneg_right (norm_coeff_pp_le_dom hM hdom m m) (pow_nonneg (norm_nonneg _) _)
  rw [← heq]
  exact hs.hasSum

end Analytic

end EulerProdFam
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam"

section
open Complex
open scoped Real

namespace ArchSkel

abbrev R₀ : Type := integralClosure ℤ ℂ

example : CommRing R₀ := inferInstance
example : TopologicalSpace R₀ := inferInstance
example : T2Space R₀ := inferInstance
example : TopologicalSpace (PowerSeries R₀) := inferInstance
example : Continuous (algebraMap R₀ ℂ) := continuous_subtype_val

theorem isIntegral_zeta (N : ℕ) (hN : 0 < N) (s : ℤ) :
    IsIntegral ℤ (cexp (2 * π * I * (s : ℂ) / (N : ℂ))) := by
  refine IsIntegral.of_pow hN ?_
  have : cexp (2 * π * I * (s : ℂ) / (N : ℂ)) ^ N = 1 := by
    rw [← Complex.exp_nat_mul]
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [show (N : ℂ) * (2 * π * I * (s : ℂ) / (N : ℂ)) = s * (2 * π * I) by field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I s
  rw [this]; exact isIntegral_one

def zeta0 (N : ℕ) (hN : 0 < N) (s : ℤ) : R₀ := ⟨_, isIntegral_zeta N hN s⟩

def Pz (N : ℕ) [NeZero N] (r : ℕ) (u v : R₀) (k : ℕ) : R₀[X] :=
  (if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then 1 - Polynomial.C u * Polynomial.X else 1) *
  (if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N) then 1 - Polynomial.C v * Polynomial.X else 1)

theorem Pz_coeff_zero (N : ℕ) [NeZero N] (r : ℕ) (u v : R₀) (k : ℕ) : (Pz N r u v k).coeff 0 = 1 := by
  unfold Pz; split_ifs <;> simp

def qN (N : ℕ) (τ : UpperHalfPlane) : ℂ := cexp (2 * π * I * (τ : ℂ) / (N : ℂ))

theorem qN_eq_qParam (N : ℕ) (τ : UpperHalfPlane) :
    qN N τ = Function.Periodic.qParam (N : ℝ) (τ : ℂ) := by
  unfold qN Function.Periodic.qParam; push_cast; ring_nf

theorem qN_ne_zero (N : ℕ) (τ : UpperHalfPlane) : qN N τ ≠ 0 := Complex.exp_ne_zero _

theorem norm_qN_lt_one (N : ℕ) (hN : 0 < N) (τ : UpperHalfPlane) : ‖qN N τ‖ < 1 := by
  rw [qN_eq_qParam, Function.Periodic.norm_qParam, ← Real.exp_zero, Real.exp_lt_exp]
  have h1 : 0 < (τ : ℂ).im := τ.2
  have h2 : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : 0 < 2 * π * (τ : ℂ).im / N := by positivity
  have h4 : -2 * π * (τ : ℂ).im / N = -(2 * π * (τ : ℂ).im / N) := by ring
  linarith

theorem tendsto_qN (N : ℕ) (hN : 0 < N) : Tendsto (qN N) UpperHalfPlane.atImInfty (𝓝 0) := by
  have := UpperHalfPlane.qParam_tendsto_atImInfty (h := (N : ℝ)) (by exact_mod_cast hN)
  exact this.congr fun τ => (qN_eq_qParam N τ).symm

theorem exists_qN_eq (N : ℕ) (hN : 0 < N) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ τ : UpperHalfPlane, qN N τ = ρ := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have him : 0 < (Function.Periodic.invQParam (N : ℝ) (ρ : ℂ)).im := by
    rw [Function.Periodic.im_invQParam, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]
    have hlog : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
    have h2 : (0 : ℝ) < N := by exact_mod_cast hN
    have : -(N : ℝ) / (2 * π) < 0 := by
      rw [neg_div]; exact neg_neg_of_pos (by positivity)
    exact mul_pos_of_neg_of_neg this hlog
  refine ⟨UpperHalfPlane.mk _ him, ?_⟩
  rw [qN_eq_qParam, UpperHalfPlane.coe_mk]
  exact Function.Periodic.qParam_right_inv hNr (by exact_mod_cast hρ0.ne')

theorem rho_pow (N : ℕ) (hN : 0 < N) (r s : ℕ) :
    (-cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2)) ^ (12 * N) =
      cexp (2 * π * I * ((6 * s * r : ℕ) : ℂ) / (N : ℂ)) := by
  rw [Even.neg_pow ⟨6 * N, by ring⟩, ← Complex.exp_nat_mul]
  refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨-(6 * s : ℤ), ?_⟩
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp
  ring

theorem N_mul_inv_one_sub (N : ℕ) (ζ : ℂ) (hζN : ζ ^ N = 1) (hζ : ζ ≠ 1) :
    (N : ℂ) * (1 - ζ)⁻¹ = ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ζ ^ j := by
  have hne : (1 - ζ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ)
  have hgeom : ∑ k ∈ Finset.range N, ζ ^ k = 0 := by
    have h := mul_geom_sum ζ N
    rw [hζN, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hζ)
  have key : (1 - ζ) * ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ζ ^ j = N := by
    rw [Finset.mul_sum]
    have hk : ∀ k : ℕ, (1 - ζ) * ∑ j ∈ Finset.range (k + 1), ζ ^ j = 1 - ζ ^ (k + 1) := fun k => by
      have h := mul_geom_sum ζ (k + 1)
      linear_combination -h
    simp_rw [hk, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : ∑ k ∈ Finset.range N, ζ ^ (k + 1) = ζ * ∑ k ∈ Finset.range N, ζ ^ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hgeom, mul_zero, sub_zero]
  calc (N : ℂ) * (1 - ζ)⁻¹ = ((1 - ζ) * ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ζ ^ j) *
        (1 - ζ)⁻¹ := by rw [key]
    _ = _ := by field_simp

theorem isIntegral_exp_of_pow (N : ℕ) (hN : 0 < N) (s : ℤ) :
    IsIntegral ℤ (cexp (2 * π * I * (s : ℂ) / (N : ℂ))) := by
  refine IsIntegral.of_pow hN ?_
  have : cexp (2 * π * I * (s : ℂ) / (N : ℂ)) ^ N = 1 := by
    rw [← Complex.exp_nat_mul]
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [show (N : ℂ) * (2 * π * I * (s : ℂ) / (N : ℂ)) = s * (2 * π * I) by field_simp]
    exact Complex.exp_int_mul_two_pi_mul_I s
  rw [this]; exact isIntegral_one

theorem isIntegral_N_mul_inv_one_sub (N : ℕ) (ζ : ℂ) (hζi : IsIntegral ℤ ζ) (hζN : ζ ^ N = 1)
    (hζ : ζ ≠ 1) : IsIntegral ℤ ((N : ℂ) * (1 - ζ)⁻¹) := by
  rw [N_mul_inv_one_sub N ζ hζN hζ]
  exact IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun j _ => hζi.pow j

theorem q_eq (N : ℕ) (hN : 0 < N) (τ : UpperHalfPlane) :
    cexp (2 * π * I * (τ : ℂ)) = qN N τ ^ N := by
  rw [qN, ← Complex.exp_nat_mul]; congr 1
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem qa_eq (N : ℕ) (hN : 0 < N) (r : ℕ) (s : ℤ) (τ : UpperHalfPlane) :
    cexp (2 * π * I * ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (N : ℂ)) =
      cexp (2 * π * I * (s : ℂ) / (N : ℂ)) * qN N τ ^ r := by
  rw [qN, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp; ring

theorem qpow_mul_qa (N : ℕ) (hN : 0 < N) (r : ℕ) (s : ℤ) (τ : UpperHalfPlane) (n : ℕ) :
    cexp (2 * π * I * (τ : ℂ)) ^ (n + 1) * cexp (2 * π * I * ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (N : ℂ)) =
      cexp (2 * π * I * (s : ℂ) / (N : ℂ)) * qN N τ ^ ((n + 1) * N + r) := by
  rw [q_eq N hN, qa_eq N hN, ← pow_mul', pow_add]; ring

theorem qpow_mul_qa_inv (N : ℕ) (hN : 0 < N) (r : ℕ) (hr : r < N) (s : ℤ) (τ : UpperHalfPlane)
    (n : ℕ) :
    cexp (2 * π * I * (τ : ℂ)) ^ (n + 1) * (cexp (2 * π * I * ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (N : ℂ)))⁻¹ =
      (cexp (2 * π * I * (s : ℂ) / (N : ℂ)))⁻¹ * qN N τ ^ (n * N + (N - r)) := by
  rw [q_eq N hN, qa_eq N hN, ← pow_mul']
  have hq : qN N τ ≠ 0 := qN_ne_zero N τ
  have hz : cexp (2 * π * I * (s : ℂ) / (N : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hsplit : (n + 1) * N = (n * N + (N - r)) + r := by
    rw [Nat.succ_mul]; omega
  rw [hsplit, pow_add]
  field_simp

theorem pref_eq (N : ℕ) (hN : 0 < N) (r : ℕ) (s : ℤ) (z : ℂ) :
    -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
        cexp (2 * π * I * (6 * (r : ℂ) ^ 2 - 6 * (r : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * z /
          (12 * (N : ℂ) ^ 2)) =
      -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
        cexp (π * I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * z) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  congr 2
  field_simp
  ring

theorem E_pow (N : ℕ) (hN : 0 < N) (r e : ℕ) (τ : ℂ) :
    cexp (2 * π * I * (6 * (r : ℂ) ^ 2 - 6 * (r : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * τ / (12 * (N : ℂ) ^ 2)) ^ (12 * N * e) =
      cexp (2 * π * I * (((e : ℤ) * (6 * (r : ℤ) ^ 2 - 6 * (N : ℤ) * (r : ℤ) + (N : ℤ) ^ 2) : ℤ) : ℂ) * τ / (N : ℂ)) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

theorem multipliable_one_sub_mul_pow {w : ℂ} (hw : ‖w‖ < 1) (c : ℂ) (a : ℕ → ℕ)
    (ha : ∀ n, n ≤ a n) : Multipliable fun n : ℕ => 1 - c * w ^ (a n) := by
  have hs : Summable fun n : ℕ => ‖-(c * w ^ (a n))‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (norm_nonneg _) hw).mul_left ‖c‖)
    rw [norm_neg, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg _) hw.le (ha n))
      (norm_nonneg _)
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

theorem tprod_ite_natCast_eq (N r : ℕ) (hr0 : 0 < r) (hrN : r < N) (f : ℕ → ℂ) :
    ∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then f (k + 1) else 1) =
      ∏' n : ℕ, f (n * N + r) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le r) hrN
  set F : ℕ → ℂ := fun k => if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then f (k + 1) else 1
    with hF
  set g : ℕ → ℕ := fun n => n * N + r - 1 with hg
  have hg1 : ∀ n, g n + 1 = n * N + r := fun n => by simp only [hg]; omega
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := hg1 a
    have h2 := hg1 b
    have : a * N = b * N := by omega
    exact Nat.eq_of_mul_eq_mul_right hN this
  have hcond : ∀ n, ((g n + 1 : ℕ) : ZMod N) = (r : ZMod N) := fun n => by
    rw [hg1]; push_cast; simp
  have hsupp : Function.mulSupport F ⊆ Set.range g := by
    intro k hk
    rw [Function.mem_mulSupport] at hk
    have hc : ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) := by
      by_contra hc
      exact hk (by simp only [hF, if_neg hc])
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hrN] at hc
    have hdm := Nat.div_add_mod (k + 1) N
    rw [hc] at hdm
    refine ⟨(k + 1) / N, ?_⟩
    show (k + 1) / N * N + r - 1 = k
    rw [Nat.mul_comm ((k + 1) / N) N]
    generalize N * ((k + 1) / N) = t at hdm ⊢
    omega
  calc ∏' k, F k = ∏' n, F (g n) := (hginj.tprod_eq hsupp).symm
    _ = ∏' n, f (n * N + r) := tprod_congr fun n => by
        show (if ((g n + 1 : ℕ) : ZMod N) = (r : ZMod N) then f (g n + 1) else 1) = _
        rw [if_pos (hcond n), hg1]

theorem tprod_ite_natCast_eq_zero (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ) :
    ∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = 0 then f (k + 1) else 1) =
      ∏' n : ℕ, f ((n + 1) * N) := by
  set F : ℕ → ℂ := fun k => if ((k + 1 : ℕ) : ZMod N) = 0 then f (k + 1) else 1 with hF
  set g : ℕ → ℕ := fun n => n * N + (N - 1) with hg
  have hg1 : ∀ n, g n + 1 = (n + 1) * N := fun n => by
    simp only [hg]; rw [Nat.succ_mul]; omega
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := hg1 a
    have h2 := hg1 b
    rw [Nat.succ_mul] at h1 h2
    have : a * N = b * N := by omega
    exact Nat.eq_of_mul_eq_mul_right hN this
  have hcond : ∀ n, ((g n + 1 : ℕ) : ZMod N) = 0 := fun n => by
    rw [hg1]; push_cast; simp
  have hsupp : Function.mulSupport F ⊆ Set.range g := by
    intro k hk
    rw [Function.mem_mulSupport] at hk
    have hc : ((k + 1 : ℕ) : ZMod N) = 0 := by
      by_contra hc
      exact hk (by simp only [hF, if_neg hc])
    rw [ZMod.natCast_eq_zero_iff] at hc
    obtain ⟨d, hd⟩ := hc
    have hd1 : 1 ≤ d := by
      rcases d with _ | d
      · simp at hd
      · omega
    refine ⟨d - 1, ?_⟩
    have : g (d - 1) + 1 = k + 1 := by
      rw [hg1, Nat.sub_add_cancel hd1, Nat.mul_comm, ← hd]
    omega
  calc ∏' k, F k = ∏' n, F (g n) := (hginj.tprod_eq hsupp).symm
    _ = ∏' n, f ((n + 1) * N) := tprod_congr fun n => by
        show (if ((g n + 1 : ℕ) : ZMod N) = 0 then f (g n + 1) else 1) = _
        rw [if_pos (hcond n), hg1]

theorem neg_natCast_eq (N r : ℕ) (hrN : r ≤ N) : -(r : ZMod N) = ((N - r : ℕ) : ZMod N) := by
  rw [Nat.cast_sub hrN, ZMod.natCast_self, zero_sub]

theorem siegel_streams (N r : ℕ) (hrN : r < N) (ζ ζ' w : ℂ) (hw : ‖w‖ < 1) :
    (if r = 0 then (1 : ℂ) else (1 - ζ * w ^ r)) *
      ∏' n : ℕ, ((1 - ζ * w ^ ((n + 1) * N + r)) * (1 - ζ' * w ^ (n * N + (N - r)))) =
    (∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then (1 - ζ * w ^ (k + 1)) else 1)) *
    (∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N) then (1 - ζ' * w ^ (k + 1)) else 1)) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le r) hrN
  haveI : NeZero N := ⟨hN.ne'⟩

  have hA : Multipliable fun n : ℕ => 1 - ζ * w ^ ((n + 1) * N + r) :=
    multipliable_one_sub_mul_pow hw ζ _ fun n => by nlinarith
  have hB : Multipliable fun n : ℕ => 1 - ζ' * w ^ (n * N + (N - r)) :=
    multipliable_one_sub_mul_pow hw ζ' _ fun n => by
      have : N - r ≥ 1 := by omega
      nlinarith
  rw [hA.tprod_mul hB]

  have hBeq : (∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N) then (1 - ζ' * w ^ (k + 1)) else 1))
      = ∏' n : ℕ, (1 - ζ' * w ^ (n * N + (N - r))) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0
      simp only [Nat.cast_zero, neg_zero, Nat.sub_zero]
      rw [tprod_ite_natCast_eq_zero N hN (fun m => 1 - ζ' * w ^ m)]
      exact tprod_congr fun n => by rw [Nat.succ_mul]
    · rw [neg_natCast_eq N r hrN.le,
        tprod_ite_natCast_eq N (N - r) (by omega) (by omega) (fun m => 1 - ζ' * w ^ m)]

  have hAeq : (∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then (1 - ζ * w ^ (k + 1)) else 1))
      = (if r = 0 then (1 : ℂ) else (1 - ζ * w ^ r)) * ∏' n : ℕ, (1 - ζ * w ^ ((n + 1) * N + r)) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0
      simp only [Nat.cast_zero, if_true, one_mul, Nat.add_zero]
      exact tprod_ite_natCast_eq_zero N hN (fun m => 1 - ζ * w ^ m)
    · rw [if_neg hr0.ne', tprod_ite_natCast_eq N r hr0 hrN (fun m => 1 - ζ * w ^ m)]

      have hA' : Multipliable fun n : ℕ => 1 - ζ * w ^ ((n + 1) * N + r) := hA
      have := tprod_eq_zero_mul' (f := fun n : ℕ => 1 - ζ * w ^ (n * N + r)) (by
        simpa using hA')
      simpa using this
  rw [hAeq, hBeq, mul_assoc]

theorem siegelFun_div_eq_streams (N r : ℕ) (hrN : r < N) (s : ℤ) (τ : UpperHalfPlane) :
    ModularCurve.siegelFun N (r : ℤ) s (τ : ℂ) /
        (-cexp (π * I * (s : ℂ) * (((r : ℤ) : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
          cexp (2 * π * I * (6 * ((r : ℤ) : ℂ) ^ 2 - 6 * ((r : ℤ) : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) *
            (τ : ℂ) / (12 * (N : ℂ) ^ 2))) =
      (if r = 0 then (1 - cexp (2 * π * I * (s : ℂ) / (N : ℂ))) else 1) *
      ((∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N)
          then (1 - cexp (2 * π * I * (s : ℂ) / (N : ℂ)) * qN N τ ^ (k + 1)) else 1)) *
       (∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N)
          then (1 - (cexp (2 * π * I * (s : ℂ) / (N : ℂ)))⁻¹ * qN N τ ^ (k + 1)) else 1))) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le r) hrN
  have hw : ‖qN N τ‖ < 1 := norm_qN_lt_one N hN τ
  rw [← siegel_streams N r hrN _ _ (qN N τ) hw, ModularCurve.siegelFun_def]
  simp only [Int.cast_natCast]
  rw [pref_eq N hN r s (τ : ℂ)]
  simp_rw [qpow_mul_qa N hN r s τ, qpow_mul_qa_inv N hN r hrN s τ]
  rw [qa_eq N hN r s τ]
  have hP : -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
      cexp (π * I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * (τ : ℂ)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
  rw [div_eq_iff hP]
  split_ifs with h
  · subst h; simp only [pow_zero, mul_one]; ring
  · ring

theorem tprod_Pc_eval (N : ℕ) (hN : 0 < N) (r : ℕ) (hr : r < N) (u v : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    (if r = 0 then 1 - u else 1) *
      ∏' k : ℕ, ((if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then 1 - u * x ^ (k + 1) else 1) *
                 (if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N) then 1 - v * x ^ (k + 1) else 1)) =
    (1 - u * x ^ r) * ∏' n : ℕ, ((1 - u * x ^ ((n + 1) * N + r)) * (1 - v * x ^ (n * N + (N - r)))) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hA : Multipliable fun k : ℕ =>
      (if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then 1 - u * x ^ (k + 1) else (1 : ℂ)) := by
    have hs : Summable fun k : ℕ => ‖(if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N)
        then 1 - u * x ^ (k + 1) else (1 : ℂ)) - 1‖ := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
        (((summable_geometric_of_lt_one (norm_nonneg _) hx).mul_left ‖u‖).comp_injective
          (add_left_injective 1))
      split_ifs
      · simp [norm_mul, norm_pow]
      · rw [sub_self, norm_zero]; exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    simpa using multipliable_one_add_of_summable hs
  have hB : Multipliable fun k : ℕ =>
      (if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N) then 1 - v * x ^ (k + 1) else (1 : ℂ)) := by
    have hs : Summable fun k : ℕ => ‖(if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N)
        then 1 - v * x ^ (k + 1) else (1 : ℂ)) - 1‖ := by
      refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
        (((summable_geometric_of_lt_one (norm_nonneg _) hx).mul_left ‖v‖).comp_injective
          (add_left_injective 1))
      split_ifs
      · simp [norm_mul, norm_pow]
      · rw [sub_self, norm_zero]; exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    simpa using multipliable_one_add_of_summable hs
  rw [hA.tprod_mul hB, ← siegel_streams N r hr u v x hx]
  split_ifs with h
  · subst h; simp only [pow_zero, mul_one]; ring
  · ring

end ArchSkel
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam"

end
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam"

section Siegel

open Complex EulerProdFam
open scoped Real

def zeta (N : ℕ) (s : ℤ) : ℂ := cexp (2 * π * I * (s : ℂ) / (N : ℂ))

theorem zeta_ne_zero (N : ℕ) (s : ℤ) : zeta N s ≠ 0 := Complex.exp_ne_zero _

theorem norm_zeta (N : ℕ) (s : ℤ) : ‖zeta N s‖ = 1 := by
  unfold zeta
  rw [show 2 * (π : ℂ) * I * (s : ℂ) / (N : ℂ) = ((2 * π * s / N : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_zeta_inv (N : ℕ) (s : ℤ) : ‖(zeta N s)⁻¹‖ = 1 := by
  rw [norm_inv, norm_zeta, inv_one]

theorem zeta_pow (N : ℕ) (hN : 0 < N) (s : ℤ) : zeta N s ^ N = 1 := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (N : ℂ) * (2 * π * I * (s : ℂ) / (N : ℂ)) = s * (2 * π * I) by field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I s

theorem isIntegral_zeta (N : ℕ) (hN : 0 < N) (s : ℤ) : IsIntegral ℤ (zeta N s) := by
  refine IsIntegral.of_pow hN ?_
  rw [zeta_pow N hN s]
  exact isIntegral_one

theorem zeta_inv_eq_pow (N : ℕ) (hN : 0 < N) (s : ℤ) : (zeta N s)⁻¹ = zeta N s ^ (N - 1) := by
  have h := zeta_pow N hN s
  have h' : zeta N s ^ (N - 1) * zeta N s = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hN, h]
  exact (eq_inv_of_mul_eq_one_left h').symm

theorem isIntegral_zeta_inv (N : ℕ) (hN : 0 < N) (s : ℤ) : IsIntegral ℤ (zeta N s)⁻¹ := by
  rw [zeta_inv_eq_pow N hN s]
  exact (isIntegral_zeta N hN s).pow _

def Pc (N : ℕ) (r : ℕ) (u v : ℂ) (k : ℕ) : ℂ[X] :=
  (if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then 1 - C u * X else 1) *
    (if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N) then 1 - C v * X else 1)

def M2 : ℂ[X] := (1 + X) ^ 2

theorem coeff_one_sub_C_mul_X (u : ℂ) (j : ℕ) :
    ((1 : ℂ[X]) - C u * X).coeff j = if j = 0 then 1 else if j = 1 then -u else 0 := by
  rcases j with _ | _ | j <;> simp [Polynomial.coeff_one, Polynomial.coeff_X]

theorem Pc_coeff_zero (N r : ℕ) (u v : ℂ) (k : ℕ) : (Pc N r u v k).coeff 0 = 1 := by
  unfold Pc
  split_ifs <;> simp [Polynomial.coeff_one, Polynomial.mul_coeff_zero]

theorem M2_coeff_zero : M2.coeff 0 = 1 := by
  simp [M2, Polynomial.coeff_one_add_X_pow]

theorem Pc_eval (N r : ℕ) (u v : ℂ) (k : ℕ) (x : ℂ) :
    (Pc N r u v k).eval x =
      (if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then 1 - u * x else 1) *
        (if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N) then 1 - v * x else 1) := by
  unfold Pc
  split_ifs <;> simp

theorem norm_coeff_ite_le (p : Prop) [Decidable p] (u : ℂ) (hu : ‖u‖ ≤ 1) (j : ℕ) :
    ‖(if p then (1 : ℂ[X]) - C u * X else 1).coeff j‖ ≤ ((1 : ℝ[X]) + X).coeff j := by
  have h1X : ((1 : ℝ[X]) + X).coeff j = if j = 0 then 1 else if j = 1 then 1 else 0 := by
    rcases j with _ | _ | j <;> simp [Polynomial.coeff_one, Polynomial.coeff_X]
  rw [h1X]
  split_ifs with hp h0 h1 h0 h1
  · rw [coeff_one_sub_C_mul_X, if_pos h0, norm_one]
  · rw [coeff_one_sub_C_mul_X, if_neg h0, if_pos h1, norm_neg]; exact hu
  · rw [coeff_one_sub_C_mul_X, if_neg h0, if_neg h1, norm_zero]
  · rw [Polynomial.coeff_one, if_pos h0, norm_one]
  · rw [Polynomial.coeff_one, if_neg h0, norm_zero]; exact zero_le_one
  · rw [Polynomial.coeff_one, if_neg h0, norm_zero]

theorem Pc_dom (N r : ℕ) {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (k j : ℕ) :
    ‖(Pc N r u v k).coeff j‖ ≤ ‖M2.coeff j‖ := by
  have h := norm_coeff_mul_le (norm_coeff_ite_le (((k + 1 : ℕ) : ZMod N) = (r : ZMod N)) u hu)
    (norm_coeff_ite_le (((k + 1 : ℕ) : ZMod N) = -(r : ZMod N)) v hv) j
  have hR : ((1 + X : ℝ[X]) * (1 + X)).coeff j = (Nat.choose 2 j : ℝ) := by
    rw [← pow_two, Polynomial.coeff_one_add_X_pow]
  have hC : ‖M2.coeff j‖ = (Nat.choose 2 j : ℝ) := by
    rw [M2, Polynomial.coeff_one_add_X_pow, Complex.norm_natCast]
  rw [hC, ← hR]
  exact h

def CoeffInt (p : ℂ[X]) : Prop := ∀ j, p.coeff j ∈ integralClosure ℤ ℂ

theorem CoeffInt.one : CoeffInt (1 : ℂ[X]) := fun j => by
  rw [Polynomial.coeff_one]; split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

theorem CoeffInt.mul {p q : ℂ[X]} (hp : CoeffInt p) (hq : CoeffInt q) : CoeffInt (p * q) := fun j => by
  rw [Polynomial.coeff_mul]
  exact Subalgebra.sum_mem _ fun x _ => Subalgebra.mul_mem _ (hp _) (hq _)

theorem CoeffInt.expand {p : ℂ[X]} (hp : CoeffInt p) {m : ℕ} (hm : 0 < m) :
    CoeffInt (Polynomial.expand ℂ m p) := fun j => by
  rw [Polynomial.coeff_expand hm]; split_ifs
  · exact hp _
  · exact Subalgebra.zero_mem _

theorem CoeffInt.one_sub_C_mul_X {u : ℂ} (hu : IsIntegral ℤ u) : CoeffInt (1 - C u * X) := fun j => by
  rw [coeff_one_sub_C_mul_X]; split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.neg_mem _ hu
  · exact Subalgebra.zero_mem _

theorem CoeffInt.ite (p : Prop) [Decidable p] {a b : ℂ[X]} (ha : CoeffInt a) (hb : CoeffInt b) :
    CoeffInt (if p then a else b) := by
  split_ifs <;> assumption

theorem coeffInt_Pc (N r : ℕ) {u v : ℂ} (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v) (k : ℕ) :
    CoeffInt (Pc N r u v k) :=
  (CoeffInt.ite _ (CoeffInt.one_sub_C_mul_X hu) CoeffInt.one).mul
    (CoeffInt.ite _ (CoeffInt.one_sub_C_mul_X hv) CoeffInt.one)

theorem coeffInt_pp (N r : ℕ) {u v : ℂ} (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v) (n : ℕ) :
    CoeffInt (pp (Pc N r u v) n) := by
  induction n with
  | zero => rw [pp_zero]; exact CoeffInt.one
  | succ n ih => rw [pp_succ]; exact ih.mul ((coeffInt_Pc N r hu hv n).expand (Nat.succ_pos n))

theorem isIntegral_coeff_W (N r : ℕ) {u v : ℂ} (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v) (m : ℕ) :
    IsIntegral ℤ (PowerSeries.coeff m (W (Pc N r u v))) := by
  rw [coeff_W (Pc_coeff_zero N r u v) le_rfl]
  exact coeffInt_pp N r hu hv m m

private theorem _root_.ModularCurve.SiegelUnit.L2.tprod_Pc_eval (N : ℕ) (hN : 0 < N) (r : ℕ) (hr : r < N) (u v : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    (if r = 0 then 1 - u else 1) * ∏' k : ℕ, (Pc N r u v k).eval (x ^ (k + 1)) =
      (1 - u * x ^ r) *
        ∏' n : ℕ, ((1 - u * x ^ ((n + 1) * N + r)) * (1 - v * x ^ (n * N + (N - r)))) := by
  rw [show (∏' k : ℕ, (Pc N r u v k).eval (x ^ (k + 1))) =
      ∏' k : ℕ, ((if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then 1 - u * x ^ (k + 1) else 1) *
        (if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N) then 1 - v * x ^ (k + 1) else 1))
    from tprod_congr fun k => Pc_eval N r u v k (x ^ (k + 1))]
  exact ArchSkel.tprod_Pc_eval N hN r hr u v hx

p2m_export "ModularCurve.SiegelUnit.L2" "tprod_Pc_eval"

theorem siegelFun_div_eq (N : ℕ) (hN : 0 < N) (r : ℕ) (hr : r < N) (s : ℤ) (τ : UpperHalfPlane) :
    siegelFun N r s (τ : ℂ) /
        (-cexp (π * I * (s : ℂ) * (((r : ℤ) : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
          cexp (2 * π * I * (6 * ((r : ℤ) : ℂ) ^ 2 - 6 * ((r : ℤ) : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * (τ : ℂ) /
            (12 * (N : ℂ) ^ 2))) =
      (1 - zeta N s * ArchSkel.qN N τ ^ r) *
        ∏' n : ℕ, ((1 - zeta N s * ArchSkel.qN N τ ^ ((n + 1) * N + r)) *
          (1 - (zeta N s)⁻¹ * ArchSkel.qN N τ ^ (n * N + (N - r)))) := by
  rw [ModularCurve.siegelFun_def]
  simp only [Int.cast_natCast]
  rw [ArchSkel.pref_eq N hN r s]
  have hA : -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
      cexp (π * I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * (τ : ℂ)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
  rw [mul_assoc (_ * _) (1 - _) _, mul_div_cancel_left₀ _ hA]
  congr 1
  · rw [ArchSkel.qa_eq N hN r s τ]; rfl
  · refine tprod_congr fun n => ?_
    rw [ArchSkel.qpow_mul_qa N hN r s τ n, ArchSkel.qpow_mul_qa_inv N hN r hr s τ n]; rfl

def coef (N r : ℕ) (s : ℤ) (m : ℕ) : ℂ :=
  (if r = 0 then 1 - zeta N s else 1) * PowerSeries.coeff m (W (Pc N r (zeta N s) (zeta N s)⁻¹))

theorem hasSum_coef (N : ℕ) (hN : 0 < N) (r : ℕ) (hr : r < N) (s : ℤ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => coef N r s m * ArchSkel.qN N τ ^ m)
      (siegelFun N r s (τ : ℂ) /
        (-cexp (π * I * (s : ℂ) * (((r : ℤ) : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
          cexp (2 * π * I * (6 * ((r : ℤ) : ℂ) ^ 2 - 6 * ((r : ℤ) : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * (τ : ℂ) /
            (12 * (N : ℂ) ^ 2)))) := by
  rw [siegelFun_div_eq N hN r hr s τ, ← tprod_Pc_eval N hN r hr _ _ (ArchSkel.norm_qN_lt_one N hN τ)]
  simp_rw [coef, mul_assoc]
  exact (hasSum_coeff_W (Pc_coeff_zero N r _ _) M2_coeff_zero
    (Pc_dom N r (norm_zeta N s).le (norm_zeta_inv N s).le) (ArchSkel.norm_qN_lt_one N hN τ)).mul_left _

theorem isIntegral_coef (N : ℕ) (hN : 0 < N) (r : ℕ) (s : ℤ) (m : ℕ) : IsIntegral ℤ (coef N r s m) := by
  unfold coef
  refine IsIntegral.mul ?_ (isIntegral_coeff_W N r (isIntegral_zeta N hN s) (isIntegral_zeta_inv N hN s) m)
  split_ifs
  · exact isIntegral_one.sub (isIntegral_zeta N hN s)
  · exact isIntegral_one

theorem coef_zero (N r : ℕ) (s : ℤ) : coef N r s 0 = if r = 0 then 1 - zeta N s else 1 := by
  rw [coef, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_W (Pc_coeff_zero N r _ _),
    mul_one]

theorem zeta_ne_one (N : ℕ) (hN : 0 < N) (s : ℤ) (hs : ¬ (N : ℤ) ∣ s) : zeta N s ≠ 1 := by
  intro h
  unfold zeta at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hπ : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [div_eq_iff hN'] at hn
  have h2 : (2 * π * I : ℂ) * (s : ℂ) = (2 * π * I) * ((n : ℂ) * (N : ℂ)) := by
    linear_combination hn
  have h3 : (s : ℂ) = (n : ℂ) * (N : ℂ) := mul_left_cancel₀ hπ h2
  have h4 : ((s : ℤ) : ℂ) = ((n * N : ℤ) : ℂ) := by push_cast; exact h3
  exact hs (Dvd.intro_left n (Int.cast_injective h4).symm)

theorem isIntegral_N_mul_inv_coef_zero (N : ℕ) (hN : 0 < N) (r : ℕ) (s : ℤ)
    (hs : r = 0 → ¬ (N : ℤ) ∣ s) : IsIntegral ℤ ((N : ℂ) * (coef N r s 0)⁻¹) := by
  rw [coef_zero]
  split_ifs with h
  · exact ArchSkel.isIntegral_N_mul_inv_one_sub N (zeta N s) (isIntegral_zeta N hN s) (zeta_pow N hN s)
      (zeta_ne_one N hN s (hs h))
  · rw [inv_one, mul_one]
    have hN1 : IsIntegral ℤ ((N : ℤ) : ℂ) := isIntegral_algebraMap
    exact_mod_cast hN1

end Siegel
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam"

section FormalRegroup

open EulerProdFam ArchSkel

theorem tprod_ite_natCast_eq_gen {α : Type*} [CommMonoid α] [TopologicalSpace α] (N r : ℕ) (hr0 : 0 < r) (hrN : r < N)
    (f : ℕ → α) :
    ∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then f (k + 1) else 1) =
      ∏' n : ℕ, f (n * N + r) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le r) hrN
  set F : ℕ → α := fun k => if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then f (k + 1) else 1
    with hF
  set g : ℕ → ℕ := fun n => n * N + r - 1 with hg
  have hg1 : ∀ n, g n + 1 = n * N + r := fun n => by simp only [hg]; omega
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := hg1 a
    have h2 := hg1 b
    have : a * N = b * N := by omega
    exact Nat.eq_of_mul_eq_mul_right hN this
  have hcond : ∀ n, ((g n + 1 : ℕ) : ZMod N) = (r : ZMod N) := fun n => by
    rw [hg1]; push_cast; simp
  have hsupp : Function.mulSupport F ⊆ Set.range g := by
    intro k hk
    rw [Function.mem_mulSupport] at hk
    have hc : ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) := by
      by_contra hc
      exact hk (by simp only [hF, if_neg hc])
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hrN] at hc
    have hdm := Nat.div_add_mod (k + 1) N
    rw [hc] at hdm
    refine ⟨(k + 1) / N, ?_⟩
    show (k + 1) / N * N + r - 1 = k
    rw [Nat.mul_comm ((k + 1) / N) N]
    generalize N * ((k + 1) / N) = t at hdm ⊢
    omega
  calc ∏' k, F k = ∏' n, F (g n) := (hginj.tprod_eq hsupp).symm
    _ = ∏' n, f (n * N + r) := tprod_congr fun n => by
        show (if ((g n + 1 : ℕ) : ZMod N) = (r : ZMod N) then f (g n + 1) else 1) = _
        rw [if_pos (hcond n), hg1]

theorem tprod_ite_natCast_eq_zero_gen {α : Type*} [CommMonoid α] [TopologicalSpace α] (N : ℕ) (hN : 0 < N) (f : ℕ → α) :
    ∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = 0 then f (k + 1) else 1) =
      ∏' n : ℕ, f ((n + 1) * N) := by
  set F : ℕ → α := fun k => if ((k + 1 : ℕ) : ZMod N) = 0 then f (k + 1) else 1 with hF
  set g : ℕ → ℕ := fun n => n * N + (N - 1) with hg
  have hg1 : ∀ n, g n + 1 = (n + 1) * N := fun n => by
    simp only [hg]; rw [Nat.succ_mul]; omega
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := hg1 a
    have h2 := hg1 b
    rw [Nat.succ_mul] at h1 h2
    have : a * N = b * N := by omega
    exact Nat.eq_of_mul_eq_mul_right hN this
  have hcond : ∀ n, ((g n + 1 : ℕ) : ZMod N) = 0 := fun n => by
    rw [hg1]; push_cast; simp
  have hsupp : Function.mulSupport F ⊆ Set.range g := by
    intro k hk
    rw [Function.mem_mulSupport] at hk
    have hc : ((k + 1 : ℕ) : ZMod N) = 0 := by
      by_contra hc
      exact hk (by simp only [hF, if_neg hc])
    rw [ZMod.natCast_eq_zero_iff] at hc
    obtain ⟨d, hd⟩ := hc
    have hd1 : 1 ≤ d := by
      rcases d with _ | d
      · simp at hd
      · omega
    refine ⟨d - 1, ?_⟩
    have : g (d - 1) + 1 = k + 1 := by
      rw [hg1, Nat.sub_add_cancel hd1, Nat.mul_comm, ← hd]
    omega
  calc ∏' k, F k = ∏' n, F (g n) := (hginj.tprod_eq hsupp).symm
    _ = ∏' n, f ((n + 1) * N) := tprod_congr fun n => by
        show (if ((g n + 1 : ℕ) : ZMod N) = 0 then f (g n + 1) else 1) = _
        rw [if_pos (hcond n), hg1]

def Pu (N r : ℕ) (u : ℂ) (k : ℕ) : ℂ[X] := if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then 1 - Polynomial.C u * Polynomial.X else 1

def Pv (N r : ℕ) (v : ℂ) (k : ℕ) : ℂ[X] := if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N) then 1 - Polynomial.C v * Polynomial.X else 1

theorem Pc_eq_Pu_mul_Pv (N r : ℕ) (u v : ℂ) (k : ℕ) : Pc N r u v k = Pu N r u k * Pv N r v k := rfl

theorem Pu_coeff_zero (N r : ℕ) (u : ℂ) (k : ℕ) : (Pu N r u k).coeff 0 = 1 := by
  unfold Pu; split_ifs <;> simp [Polynomial.coeff_one]

theorem Pv_coeff_zero (N r : ℕ) (v : ℂ) (k : ℕ) : (Pv N r v k).coeff 0 = 1 := by
  unfold Pv; split_ifs <;> simp [Polynomial.coeff_one]

theorem fac_one_sub_C_mul_X (u : ℂ) (k : ℕ) :
    fac (fun _ : ℕ => (1 - Polynomial.C u * Polynomial.X : ℂ[X])) k = (1 - PowerSeries.C u * PowerSeries.X ^ (k + 1) : PowerSeries ℂ) := by
  unfold fac
  rw [map_sub, map_one, map_mul, Polynomial.expand_C, Polynomial.expand_X, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]

theorem fac_Pu (N r : ℕ) (u : ℂ) (k : ℕ) :
    fac (Pu N r u) k = if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N) then (1 - PowerSeries.C u * PowerSeries.X ^ (k + 1) : PowerSeries ℂ) else 1 := by
  by_cases h : ((k + 1 : ℕ) : ZMod N) = (r : ZMod N)
  · rw [if_pos h, ← fac_one_sub_C_mul_X u k]
    unfold fac Pu
    rw [if_pos h]
  · rw [if_neg h]
    unfold fac Pu
    rw [if_neg h, map_one, Polynomial.coe_one]

theorem fac_Pv (N r : ℕ) (v : ℂ) (k : ℕ) :
    fac (Pv N r v) k = if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N) then (1 - PowerSeries.C v * PowerSeries.X ^ (k + 1) : PowerSeries ℂ) else 1 := by
  by_cases h : ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N)
  · rw [if_pos h, ← fac_one_sub_C_mul_X v k]
    unfold fac Pv
    rw [if_pos h]
  · rw [if_neg h]
    unfold fac Pv
    rw [if_neg h, map_one, Polynomial.coe_one]

theorem W_Pc_eq (N r : ℕ) (u v : ℂ) : W (Pc N r u v) = W (Pu N r u) * W (Pv N r v) := by
  unfold W
  rw [← (multipliable_fac (Pu_coeff_zero N r u)).tprod_mul (multipliable_fac (Pv_coeff_zero N r v))]
  refine tprod_congr fun k => ?_
  show fac (Pc N r u v) k = fac (Pu N r u) k * fac (Pv N r v) k
  unfold fac
  rw [Pc_eq_Pu_mul_Pv, map_mul, Polynomial.coe_mul]

theorem W_Pu_eq (N r : ℕ) (hrN : r < N) (u : ℂ) :
    (if r = 0 then (1 : PowerSeries ℂ) else (1 - PowerSeries.C u * PowerSeries.X ^ r)) *
        ∏' n : ℕ, (1 - PowerSeries.C u * PowerSeries.X ^ (N * (n + 1) + r) : PowerSeries ℂ) =
      W (Pu N r u) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le r) hrN
  have hW : W (Pu N r u) = ∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = (r : ZMod N)
      then (1 - PowerSeries.C u * PowerSeries.X ^ (k + 1) : PowerSeries ℂ) else 1) := tprod_congr fun k => fac_Pu N r u k
  rw [hW]
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    rw [if_pos rfl, one_mul, Nat.cast_zero,
      tprod_ite_natCast_eq_zero_gen N hN (fun m => (1 - PowerSeries.C u * PowerSeries.X ^ m : PowerSeries ℂ))]
    exact tprod_congr fun n => by rw [Nat.mul_comm, Nat.add_zero]
  · rw [if_neg hr0.ne', tprod_ite_natCast_eq_gen N r hr0 hrN (fun m => (1 - PowerSeries.C u * PowerSeries.X ^ m : PowerSeries ℂ))]
    have hA' : Multipliable fun n : ℕ => (1 - PowerSeries.C u * PowerSeries.X ^ ((n + 1) * N + r) : PowerSeries ℂ) :=
      multipliable_one_sub_C_mul_X_pow u _ fun n => by nlinarith
    have hsplit := tprod_eq_zero_mul' (f := fun n : ℕ => (1 - PowerSeries.C u * PowerSeries.X ^ (n * N + r) : PowerSeries ℂ)) (by
      simpa using hA')
    simp only [zero_mul, zero_add] at hsplit
    rw [hsplit]
    congr 1
    exact tprod_congr fun n => by rw [Nat.mul_comm N (n + 1)]

theorem W_Pv_eq (N r : ℕ) (hrN : r < N) (v : ℂ) :
    ∏' n : ℕ, (1 - PowerSeries.C v * PowerSeries.X ^ (N * (n + 1) - r) : PowerSeries ℂ) = W (Pv N r v) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le r) hrN
  have hW : W (Pv N r v) = ∏' k : ℕ, (if ((k + 1 : ℕ) : ZMod N) = -(r : ZMod N)
      then (1 - PowerSeries.C v * PowerSeries.X ^ (k + 1) : PowerSeries ℂ) else 1) := tprod_congr fun k => fac_Pv N r v k
  rw [hW]
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    rw [Nat.cast_zero, neg_zero,
      tprod_ite_natCast_eq_zero_gen N hN (fun m => (1 - PowerSeries.C v * PowerSeries.X ^ m : PowerSeries ℂ))]
    exact tprod_congr fun n => by rw [Nat.mul_comm, Nat.sub_zero]
  · rw [neg_natCast_eq N r hrN.le, tprod_ite_natCast_eq_gen N (N - r) (by omega) (by omega)
      (fun m => (1 - PowerSeries.C v * PowerSeries.X ^ m : PowerSeries ℂ))]
    refine tprod_congr fun n => ?_
    have : N * (n + 1) - r = n * N + (N - r) := by
      rw [Nat.mul_comm N (n + 1), Nat.succ_mul]
      omega
    rw [this]

end FormalRegroup
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam"

section Assembly

open EulerProdFam ArchSkel

variable (q : ℕ) [Fact q.Prime]

def phi (ι : CyclotomicField q ℚ →+* ℂ) : zetaSubring q →+* ℂ := ι.comp (algebraMap (zetaSubring q) (CyclotomicField q ℚ))

theorem phi_zpow (ι : CyclotomicField q ℚ →+* ℂ) (n : ℕ) :
    phi q ι (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ n) = ι (zetaQ q) ^ n := by
  rw [map_pow]; rfl

theorem map_siegelSeriesInt (a : Fin 2 → ZMod q) (ι : CyclotomicField q ℚ →+* ℂ) :
    PowerSeries.map (phi q ι) (siegelSeriesInt q a) =
      (1 - PowerSeries.C (ι (zetaQ q) ^ (a 1).val) * PowerSeries.X ^ (a 0).val) *
        ((∏' n : ℕ, (1 - PowerSeries.C (ι (zetaQ q) ^ (a 1).val) * PowerSeries.X ^ (q * (n + 1) + (a 0).val) : PowerSeries ℂ)) *
          ∏' n : ℕ, (1 - PowerSeries.C (ι (zetaQ q) ^ (q - (a 1).val)) * PowerSeries.X ^ (q * (n + 1) - (a 0).val) : PowerSeries ℂ)) := by
  letI : TopologicalSpace (zetaSubring q) := ⊥
  haveI : DiscreteTopology (zetaSubring q) := ⟨rfl⟩
  have hφ : Continuous (phi q ι) := continuous_of_discreteTopology
  have hcont := continuous_map (R := zetaSubring q) (phi q ι) hφ
  have e1 : ∀ (n k : ℕ), PowerSeries.map (phi q ι) (1 - PowerSeries.C (⟨zetaQ q, zetaQ_mem_zetaSubring q⟩ ^ n) * PowerSeries.X ^ k) =
      1 - PowerSeries.C (ι (zetaQ q) ^ n) * PowerSeries.X ^ k := by
    intro n k
    rw [map_sub, map_one, map_mul, PowerSeries.map_C, map_pow (PowerSeries.map (phi q ι)) PowerSeries.X k, PowerSeries.map_X, phi_zpow]
  unfold siegelSeriesInt
  rw [map_mul, map_mul, e1,
    ← ((multipliable_siegelFactor_left q a).hasProd.map (PowerSeries.map (phi q ι)) hcont).tprod_eq,
    ← ((multipliable_siegelFactor_right q a).hasProd.map (PowerSeries.map (phi q ι)) hcont).tprod_eq]
  congr 2
  · exact tprod_congr fun n => e1 _ _
  · exact tprod_congr fun n => e1 _ _

theorem map_siegelSeriesInt_eq_C_mul_W (a : Fin 2 → ZMod q) (ι : CyclotomicField q ℚ →+* ℂ) :
    PowerSeries.map (phi q ι) (siegelSeriesInt q a) =
      PowerSeries.C (if (a 0).val = 0 then 1 - ι (zetaQ q) ^ (a 1).val else 1) *
        W (Pc q (a 0).val (ι (zetaQ q) ^ (a 1).val) (ι (zetaQ q) ^ (q - (a 1).val))) := by
  have hr : (a 0).val < q := (a 0).val_lt
  rw [map_siegelSeriesInt, W_Pc_eq, ← W_Pu_eq q (a 0).val hr, ← W_Pv_eq q (a 0).val hr]
  by_cases h0 : (a 0).val = 0
  · rw [if_pos h0, if_pos h0, one_mul, h0, pow_zero, mul_one, map_sub, map_one]
  · rw [if_neg h0, if_neg h0, map_one, one_mul, mul_assoc]

theorem iota_zeta_pow_eq (ι : CyclotomicField q ℚ →+* ℂ) (hι : ι (zetaQ q) = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))) (s : ℕ) :
    ι (zetaQ q) ^ s = zeta q (s : ℤ) := by
  rw [hι, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem iota_zeta_pow_sub_eq (ι : CyclotomicField q ℚ →+* ℂ) (hι : ι (zetaQ q) = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))) (s : ℕ) (hs : s ≤ q) :
    ι (zetaQ q) ^ (q - s) = (zeta q (s : ℤ))⁻¹ := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have h1 : ι (zetaQ q) ^ (q - s) * ι (zetaQ q) ^ s = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hs, ← map_pow, zetaQ_pow, map_one]
  rw [iota_zeta_pow_eq q ι hι s] at h1
  exact eq_inv_of_mul_eq_one_left h1

theorem hasSum_coeff_pow (N : ℕ) (hN : 0 < N) (A : PowerSeries ℂ) (F : UpperHalfPlane → ℂ)
    (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m A * qN N τ ^ m) (F τ)) (k : ℕ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => PowerSeries.coeff m (A ^ k) * qN N τ ^ m) (F τ ^ k) := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  induction k generalizing τ with
  | zero =>
    simp only [pow_zero]
    have : (fun m : ℕ => PowerSeries.coeff m (1 : PowerSeries ℂ) * qN N τ ^ m) = fun m => if m = 0 then 1 else 0 := by
      funext m
      rw [PowerSeries.coeff_one]
      split_ifs with h
      · rw [h, pow_zero, mul_one]
      · rw [zero_mul]
    rw [this]
    exact hasSum_ite_eq 0 1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    have h := ModularCurve.hasSum_qParam_mul (N : ℝ) hN' (A ^ k) A (fun τ => F τ ^ k) F
      (fun τ => by simpa only [qN_eq_qParam] using ih τ) (fun τ => by simpa only [qN_eq_qParam] using hA τ) τ
    simpa only [qN_eq_qParam] using h

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam"

end ModularCurve.SiegelUnit.L2
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2"
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit"
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2.EulerProdFam P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve.SiegelUnit.L2"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div.ModularCurve ModularCurve.SiegelUnit.L2 ModularCurve.SiegelUnit.L2.EulerProdFam ModularCurve.SiegelUnit.L2.ArchSkel in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (a : Fin 2 → ZMod q)
    (ι : CyclotomicField q ℚ →+* ℂ) (hι : ι (zetaQ q) = Complex.exp (2 * Real.pi * Complex.I / (q : ℂ)))
    (τ : UpperHalfPlane) :
    HasSum
      (fun n : ℕ => ι (PowerSeries.coeff n (siegelSeries q a ^ (12 * q))) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (q : ℂ)))
      (siegelFun q ((a 0).val : ℤ) ((a 1).val : ℤ) (τ : ℂ) ^ (12 * q) /
        (ι (zetaQ q ^ siegelConstExponent q a) *
          Complex.exp (2 * Real.pi * Complex.I * ((siegelExponent q a : ℤ) : ℂ) * (τ : ℂ) / (q : ℂ)))) := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  set r : ℕ := (a 0).val with hr_def
  set s : ℕ := (a 1).val with hs_def
  have hr : r < q := (a 0).val_lt
  have hs : s ≤ q := (a 1).val_lt.le
  set u : ℂ := ι (zetaQ q) ^ s with hu_def
  have hu : u = zeta q (s : ℤ) := iota_zeta_pow_eq q ι hι s
  have hv : ι (zetaQ q) ^ (q - s) = (zeta q (s : ℤ))⁻¹ := iota_zeta_pow_sub_eq q ι hι s hs

  set A : PowerSeries ℂ := PowerSeries.map (phi q ι) (siegelSeriesInt q a) with hA_def
  have hA : A = PowerSeries.C (if r = 0 then 1 - zeta q (s : ℤ) else 1) * W (Pc q r (zeta q (s : ℤ)) (zeta q (s : ℤ))⁻¹) := by
    rw [hA_def, map_siegelSeriesInt_eq_C_mul_W, ← hu_def, hu, hv]

  have hcoefA : ∀ m, PowerSeries.coeff m A = coef q r (s : ℤ) m := by
    intro m
    rw [hA, PowerSeries.coeff_C_mul, coef]

  have hQ : ∀ τ' : UpperHalfPlane, HasSum (fun m : ℕ => PowerSeries.coeff m A * qN q τ' ^ m)
      (siegelFun q r (s : ℤ) ((τ' : UpperHalfPlane) : ℂ) /
        (-Complex.exp (Real.pi * Complex.I * ((s : ℤ) : ℂ) * (((r : ℤ) : ℂ) - (q : ℂ)) / (q : ℂ) ^ 2) *
          Complex.exp (2 * Real.pi * Complex.I * (6 * ((r : ℤ) : ℂ) ^ 2 - 6 * ((r : ℤ) : ℂ) * (q : ℂ) + (q : ℂ) ^ 2) * ((τ' : UpperHalfPlane) : ℂ) /
            (12 * (q : ℂ) ^ 2)))) := by
    intro τ'
    simp_rw [hcoefA]
    exact hasSum_coef q hq r hr (s : ℤ) τ'
  have hpow := hasSum_coeff_pow q hq A (fun τ' : UpperHalfPlane => (siegelFun q r (s : ℤ) ((τ' : UpperHalfPlane) : ℂ) /
        (-Complex.exp (Real.pi * Complex.I * ((s : ℤ) : ℂ) * (((r : ℤ) : ℂ) - (q : ℂ)) / (q : ℂ) ^ 2) *
          Complex.exp (2 * Real.pi * Complex.I * (6 * ((r : ℤ) : ℂ) ^ 2 - 6 * ((r : ℤ) : ℂ) * (q : ℂ) + (q : ℂ) ^ 2) * ((τ' : UpperHalfPlane) : ℂ) /
            (12 * (q : ℂ) ^ 2))))) hQ (12 * q) τ

  have hsummand : (fun m : ℕ => PowerSeries.coeff m (A ^ (12 * q)) * qN q τ ^ m) =
      fun n : ℕ => ι (PowerSeries.coeff n (siegelSeries q a ^ (12 * q))) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (q : ℂ)) := by
    funext m
    congr 1
    · rw [hA_def, ← map_pow, PowerSeries.coeff_map, siegelSeries, ← map_pow, PowerSeries.coeff_map]
      rfl
    · rw [qN, ← Complex.exp_nat_mul]
      congr 1
      ring

  have hval : (siegelFun q r (s : ℤ) ((τ : UpperHalfPlane) : ℂ) /
        (-Complex.exp (Real.pi * Complex.I * ((s : ℤ) : ℂ) * (((r : ℤ) : ℂ) - (q : ℂ)) / (q : ℂ) ^ 2) *
          Complex.exp (2 * Real.pi * Complex.I * (6 * ((r : ℤ) : ℂ) ^ 2 - 6 * ((r : ℤ) : ℂ) * (q : ℂ) + (q : ℂ) ^ 2) * ((τ : UpperHalfPlane) : ℂ) /
            (12 * (q : ℂ) ^ 2)))) ^ (12 * q) = siegelFun q ((a 0).val : ℤ) ((a 1).val : ℤ) (τ : ℂ) ^ (12 * q) /
        (ι (zetaQ q ^ siegelConstExponent q a) *
          Complex.exp (2 * Real.pi * Complex.I * ((siegelExponent q a : ℤ) : ℂ) * (τ : ℂ) / (q : ℂ))) := by
    rw [div_pow, mul_pow]
    congr 1
    have h1 : (-Complex.exp (Real.pi * Complex.I * ((s : ℤ) : ℂ) * (((r : ℤ) : ℂ) - (q : ℂ)) / (q : ℂ) ^ 2)) ^ (12 * q) =
        ι (zetaQ q ^ siegelConstExponent q a) := by
      have := rho_pow q hq r s
      simp only [Int.cast_natCast] at this ⊢
      rw [this, map_pow, siegelConstExponent, ← hr_def, ← hs_def, hι, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h2 : Complex.exp (2 * Real.pi * Complex.I * (6 * ((r : ℤ) : ℂ) ^ 2 - 6 * ((r : ℤ) : ℂ) * (q : ℂ) + (q : ℂ) ^ 2) * (τ : ℂ) /
            (12 * (q : ℂ) ^ 2)) ^ (12 * q) =
        Complex.exp (2 * Real.pi * Complex.I * ((siegelExponent q a : ℤ) : ℂ) * (τ : ℂ) / (q : ℂ)) := by
      have := E_pow q hq r 1 (τ : ℂ)
      simp only [Int.cast_natCast, mul_one] at this ⊢
      rw [this, siegelExponent, ← hr_def]
      congr 1
      push_cast
      ring
    rw [h1, h2]
  rw [hsummand] at hpow
  simpa only [hval] using hpow

#print axioms solution

end S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div (solution)
