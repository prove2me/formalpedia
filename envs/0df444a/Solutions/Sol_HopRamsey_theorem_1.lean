-- Prove2me | solution 1 for HopRamsey.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:39:19.487145+00:00
-- url     : https://prove2.me/submissions/67a88ab8-0ed8-48a3-a7d0-18458787c88b

import Mathlib
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_IsStochRamseyEmbedding
import Definitions.Def_HopRamsey_augmentComplete
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_hopStochEmbedding
import Definitions.Def_HopRamsey_polylogBound
import Definitions.Def_HopRamsey_truncGeom
import Theorems.Thm_HopRamsey_finite_case
import Theorems.Thm_HopRamsey_finite_case_parameters
import Theorems.Thm_HopRamsey_remove_finite_diameter

open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey

variable {V : Type}

lemma walkWeight_append (G : WGraph V) {u v w : V} (p : G.graph.Walk u v) (q : G.graph.Walk v w) :
    G.walkWeight (p.append q) = G.walkWeight p + G.walkWeight q := by
  simp [WGraph.walkWeight, SimpleGraph.Walk.edges_append, List.map_append, List.sum_append]

lemma walkWeight_reverse (G : WGraph V) {u v : V} (p : G.graph.Walk u v) :
    G.walkWeight p.reverse = G.walkWeight p := by
  simp [WGraph.walkWeight, SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]

lemma hopDist_mono (G : WGraph V) {a b : ℕ} (hab : a ≤ b) (u v : V) :
    hopDist G b u v ≤ hopDist G a u v := by
  unfold hopDist
  refine le_iInf fun p => le_iInf fun hp => ?_
  exact iInf_le_of_le p (iInf_le_of_le (le_trans hp hab) le_rfl)

lemma hopDist_le_walk (G : WGraph V) {a : ℕ} {u v : V} (p : G.graph.Walk u v) (hp : p.length ≤ a) :
    hopDist G a u v ≤ G.walkWeight p :=
  iInf_le_of_le p (iInf_le_of_le hp le_rfl)

lemma hopDist_self (G : WGraph V) (a : ℕ) (u : V) : hopDist G a u u = 0 := by
  refine le_antisymm ?_ (by positivity)
  calc hopDist G a u u ≤ G.walkWeight (SimpleGraph.Walk.nil : G.graph.Walk u u) :=
        hopDist_le_walk G _ (by simp)
    _ = 0 := by simp [WGraph.walkWeight]

lemma hopDist_symm (G : WGraph V) (a : ℕ) (u v : V) : hopDist G a u v = hopDist G a v u := by
  have key : ∀ x y : V, hopDist G a y x ≤ hopDist G a x y := by
    intro x y
    unfold hopDist
    refine le_iInf fun p => le_iInf fun hp => ?_
    refine iInf_le_of_le p.reverse (iInf_le_of_le (by simpa using hp) ?_)
    rw [walkWeight_reverse]
  exact le_antisymm (key v u) (key u v)

lemma hopDist_triangle (G : WGraph V) (a b : ℕ) (u v w : V) :
    hopDist G (a + b) u w ≤ hopDist G a u v + hopDist G b v w := by
  unfold hopDist
  rw [ENNReal.iInf_add]
  refine le_iInf fun p => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hp => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun q => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hq => ?_
  refine iInf_le_of_le (p.append q) (iInf_le_of_le ?_ ?_)
  · simp [SimpleGraph.Walk.length_append]; omega
  · rw [walkWeight_append]

/-- With all edge weights at least `m`, distinct vertices are at hop-distance at least `m`. -/
lemma hopDist_ge_of_ne (G : WGraph V) {m : ℝ} (hm : ∀ e ∈ G.graph.edgeSet, m ≤ G.w e) (a : ℕ)
    {u v : V} (huv : u ≠ v) : ENNReal.ofReal m ≤ hopDist G a u v := by
  unfold hopDist
  refine le_iInf fun p => le_iInf fun _ => ?_
  cases p with
  | nil => exact absurd rfl huv
  | cons hadj q =>
    simp only [WGraph.walkWeight, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons]
    exact le_trans (ENNReal.ofReal_le_ofReal (hm _ hadj)) le_self_add

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

/-- Expectation of a `[0,∞]`-valued function under a PMF. -/
noncomputable def ex {α : Type*} (p : PMF α) (F : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * F a

lemma ex_bind {α β : Type*} (p : PMF α) (f : α → PMF β) (F : β → ℝ≥0∞) :
    ex (p.bind f) F = ex p (fun a => ex (f a) F) := by
  unfold ex
  simp only [PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, mul_assoc]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

lemma ex_pure {α : Type*} (a : α) (F : α → ℝ≥0∞) : ex (PMF.pure a) F = F a := by
  unfold ex
  rw [tsum_eq_single a]
  · simp
  · intro b hb; simp [PMF.pure_apply, hb]

lemma ex_map {α β : Type*} (p : PMF α) (g : α → β) (F : β → ℝ≥0∞) :
    ex (p.map g) F = ex p (fun a => F (g a)) := by
  rw [← PMF.bind_pure_comp, ex_bind]
  simp [ex_pure]

lemma ex_mono {α : Type*} (p : PMF α) {F G : α → ℝ≥0∞} (h : ∀ a ∈ p.support, F a ≤ G a) :
    ex p F ≤ ex p G := by
  unfold ex
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_right (h a ha) _
  · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]

lemma ex_le_of_le {α : Type*} (p : PMF α) {F : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ a ∈ p.support, F a ≤ c) :
    ex p F ≤ c := by
  calc ex p F ≤ ex p (fun _ => c) := ex_mono p h
    _ = c := by unfold ex; rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma ex_const {α : Type*} (p : PMF α) (c : ℝ≥0∞) : ex p (fun _ => c) = c := by
  unfold ex; rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

lemma ex_add {α : Type*} (p : PMF α) (F G : α → ℝ≥0∞) :
    ex p (fun a => F a + G a) = ex p F + ex p G := by
  unfold ex; simp_rw [mul_add]; exact ENNReal.tsum_add

lemma ex_mul_const {α : Type*} (p : PMF α) (F : α → ℝ≥0∞) (c : ℝ≥0∞) :
    ex p (fun a => F a * c) = ex p F * c := by
  unfold ex; simp_rw [← mul_assoc]; exact ENNReal.tsum_mul_right

lemma ex_const_mul {α : Type*} (p : PMF α) (F : α → ℝ≥0∞) (c : ℝ≥0∞) :
    ex p (fun a => c * F a) = c * ex p F := by
  unfold ex; simp_rw [mul_left_comm _ c]; exact ENNReal.tsum_mul_left

lemma toOuterMeasure_eq_ex {α : Type*} (p : PMF α) (s : Set α) [DecidablePred (· ∈ s)] :
    p.toOuterMeasure s = ex p (fun a => if a ∈ s then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  unfold ex
  congr 1; ext a
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

/-- Weight of the geometric law, real form. -/
noncomputable def gw (p : ℝ) (r : ℕ) : ℝ := (1 - p) ^ r * p

lemma truncGeom_support {p : ℝ} {k : ℕ} (hk : 0 < k) (hp : 0 < p) :
    ∀ r ∈ (truncGeom p k).support, r < k := by
  intro r hr
  unfold truncGeom at hr
  rw [dif_pos ⟨hk, hp⟩] at hr
  rw [PMF.support_map] at hr
  obtain ⟨R, -, rfl⟩ := hr
  exact R.isLt

lemma sum_gw (p : ℝ) (m : ℕ) : ∑ r ∈ Finset.range m, gw p r = 1 - (1 - p) ^ m := by
  unfold gw
  rw [← Finset.sum_mul]
  rcases eq_or_ne p 0 with h0 | h0
  · subst h0; simp
  have := geom_sum_mul (1 - p) m
  have h' : (1 - p) - 1 = -p := by ring
  rw [h'] at this
  linear_combination -this

lemma gw_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (r : ℕ) : 0 ≤ gw p r :=
  mul_nonneg (pow_nonneg (by linarith) _) hp0

/-- The expectation under the truncated geometric law. -/
lemma ex_truncGeom {p : ℝ} {k : ℕ} (hk : 0 < k) (hp0 : 0 < p) (hp1 : p ≤ 1) (F : ℕ → ℝ≥0∞) :
    ex (truncGeom p k) F =
      (∑ r ∈ Finset.range k, ENNReal.ofReal (gw p r) * F r) / ENNReal.ofReal (1 - (1 - p) ^ k) := by
  unfold truncGeom
  rw [dif_pos ⟨hk, hp0⟩, ex_map]
  unfold ex
  simp only [PMF.normalize_apply]
  rw [tsum_fintype]
  have hZ : (∑' R : Fin k, truncGeomWeight p k R) = ENNReal.ofReal (1 - (1 - p) ^ k) := by
    rw [tsum_fintype]
    unfold truncGeomWeight
    rw [Fin.sum_univ_eq_sum_range (fun r => ENNReal.ofReal ((1 - p) ^ r * p)) k]
    rw [← sum_gw p k, ENNReal.ofReal_sum_of_nonneg (fun R _ => gw_nonneg hp0.le hp1 R)]
    rfl
  rw [hZ, div_eq_mul_inv, Finset.sum_mul]
  rw [← Fin.sum_univ_eq_sum_range (fun r => ENNReal.ofReal (gw p r) * F r * (ENNReal.ofReal (1 - (1 - p) ^ k))⁻¹) k]
  refine Finset.sum_congr rfl fun R _ => ?_
  unfold truncGeomWeight gw
  ring

end HopRamsey.FZ


namespace HopRamsey.FZ

open HopRamsey

namespace P2

variable (P : Fig2Params)

lemma logN1_gt_one (hN : 2 ≤ P.N) : 1 < Real.logb 2 ((P.N : ℝ) + 1) := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
  have : (2 : ℝ) ≤ P.N := by exact_mod_cast hN
  simp; linarith

lemma L_pos (hN : 2 ≤ P.N) : 1 ≤ P.L := by
  unfold Fig2Params.L
  rw [Nat.one_le_iff_ne_zero, ne_eq, Nat.ceil_eq_zero, not_le]
  exact Real.logb_pos (by norm_num) (logN1_gt_one P hN)

lemma L_le (hN : 2 ≤ P.N) : (P.L : ℝ) < Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1)) + 1 := by
  unfold Fig2Params.L
  exact Nat.ceil_lt_add_one (Real.logb_pos (by norm_num) (logN1_gt_one P hN)).le

lemma L_ge : Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1)) ≤ P.L := by
  unfold Fig2Params.L; exact Nat.le_ceil _

lemma two_pow_L_ge (hN : 2 ≤ P.N) : Real.logb 2 ((P.N : ℝ) + 1) ≤ 2 ^ P.L := by
  have h1 := L_ge P
  have hx := logN1_gt_one P hN
  calc Real.logb 2 ((P.N : ℝ) + 1) = (2 : ℝ) ^ (Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1))) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
    _ ≤ (2 : ℝ) ^ (P.L : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = 2 ^ P.L := by norm_cast

lemma two_pow_Lsub1_lt (hN : 2 ≤ P.N) : (2 : ℝ) ^ (P.L - 1) < Real.logb 2 ((P.N : ℝ) + 1) := by
  have h1 := L_le P hN
  have hL := L_pos P hN
  have hx := logN1_gt_one P hN
  have : ((P.L - 1 : ℕ) : ℝ) < Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1)) := by
    push_cast [hL]; linarith
  calc (2 : ℝ) ^ (P.L - 1) = (2 : ℝ) ^ (((P.L - 1 : ℕ)) : ℝ) := by norm_cast
    _ < (2 : ℝ) ^ (Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1))) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) this
    _ = _ := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)

lemma mu_cast (ℓ : ℕ) : ((P.mu ℓ : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ (P.L - ℓ)) := by
  unfold Fig2Params.mu; push_cast; ring

lemma mu_ge_two (ℓ : ℕ) (hℓ : ℓ ≤ P.L) : (2 : ℝ) ≤ P.mu ℓ := by
  rw [mu_cast]
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ (P.L - ℓ)) := pow_le_pow_right₀ (by norm_num) (Nat.one_le_two_pow)

lemma mu_pos (ℓ : ℕ) : (0 : ℝ) < P.mu ℓ := by rw [mu_cast]; positivity

lemma mu_L : P.mu P.L = 2 := by unfold Fig2Params.mu; simp

lemma mu_sq (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) : (P.mu (ℓ - 1) : ℝ) = (P.mu ℓ : ℝ) ^ 2 := by
  rw [mu_cast, mu_cast, ← pow_mul]
  congr 1
  have : P.L - (ℓ - 1) = (P.L - ℓ) + 1 := by omega
  rw [this, pow_succ]

lemma mu_zero_gt (hN : 2 ≤ P.N) : (P.N : ℝ) < P.mu 0 := by
  rw [mu_cast]
  have h := two_pow_L_ge P hN
  have hx := logN1_gt_one P hN
  calc (P.N : ℝ) < P.N + 1 := by linarith
    _ = (2 : ℝ) ^ (Real.logb 2 ((P.N : ℝ) + 1)) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    _ ≤ (2 : ℝ) ^ ((2 ^ (P.L - 0) : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        push_cast; simpa using h
    _ = _ := by norm_cast

lemma mu_le_of_one_le (hN : 2 ≤ P.N) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : (P.mu ℓ : ℝ) < P.N + 1 := by
  rw [mu_cast]
  have h := two_pow_Lsub1_lt P hN
  calc (2 : ℝ) ^ (2 ^ (P.L - ℓ)) ≤ (2 : ℝ) ^ (2 ^ (P.L - 1)) := by
        apply pow_le_pow_right₀ (by norm_num)
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 : ℝ) ^ (((2 ^ (P.L - 1) : ℕ)) : ℝ) := by norm_cast
    _ < (2 : ℝ) ^ (Real.logb 2 ((P.N : ℝ) + 1)) := by
        apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        push_cast; exact h
    _ = _ := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)

lemma delta_pos (hN : 2 ≤ P.N) : 0 < P.delta := by
  unfold Fig2Params.delta; have := logN1_gt_one P hN; positivity

lemma delta_lt_one (hN : 2 ≤ P.N) : P.delta < 1 := by
  unfold Fig2Params.delta
  have := logN1_gt_one P hN
  rw [inv_lt_one₀ (by positivity)]
  nlinarith

lemma delta_eq (hN : 2 ≤ P.N) :
    Real.log (1 / P.delta) = 2 * Real.log (Real.logb 2 ((P.N : ℝ) + 1)) := by
  unfold Fig2Params.delta
  rw [one_div, inv_inv, Real.log_pow]; push_cast; ring

/-- `L·δ ≤ 1`. -/
lemma L_delta_le (hN : 2 ≤ P.N) : (P.L : ℝ) * P.delta ≤ 1 := by
  set x := Real.logb 2 ((P.N : ℝ) + 1) with hx
  have hx1 : 1 < x := logN1_gt_one P hN
  have hL := L_le P hN
  have hlog : Real.logb 2 x ≤ 2 * (x - 1) := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < x)
    have h2 : (1:ℝ)/2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    nlinarith
  have hd : P.delta = (x ^ 2)⁻¹ := rfl
  rw [hd, ← div_eq_mul_inv, div_le_one (by positivity)]
  nlinarith

lemma k_ge (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ) :
    4 * (Real.log P.N + Real.log (2 / P.delta)) ≤ (P.k : ℝ) := by
  have hδ0 := delta_pos P hN
  have hδ1 := delta_lt_one P hN
  have hlogΦ : 1 ≤ Real.logb 2 P.Φ := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hΦ
  have hl2 : 0 ≤ Real.log (2 / P.delta) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hlN : 0 ≤ Real.log P.N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P.N))
  have hpow : 1 ≤ (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) :=
    Real.one_le_rpow (by linarith) (by linarith)
  unfold Fig2Params.k
  refine le_trans ?_ (Nat.le_ceil _)
  set B := Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ
  have hB : Real.log P.N + Real.log (2 / P.delta) ≤ B := by
    simp only [B]; nlinarith
  have hB0 : 0 ≤ B := by linarith
  have h4 : 4 ≤ 4 / P.ε := by rw [le_div_iff₀ hε]; linarith
  calc 4 * (Real.log P.N + Real.log (2 / P.delta)) ≤ 4 * B := by linarith
    _ ≤ (4 / P.ε) * B := by nlinarith
    _ ≤ (4 / P.ε) * (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) * B := by
        have : 0 ≤ 4 / P.ε := by positivity
        have := mul_le_mul_of_nonneg_left hpow (mul_nonneg this hB0)
        nlinarith


section Std

set_option linter.unusedSectionVars false
variable (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ)
include hN hε hε1 hΦ

lemma log2_delta_nonneg : 0 ≤ Real.log (2 / P.delta) :=
  Real.log_nonneg (by rw [le_div_iff₀ (delta_pos P hN)]; linarith [delta_lt_one P hN])

lemma k_pos : 0 < P.k := by
  have h := k_ge P hN hε hε1 hΦ
  have hl2 := log2_delta_nonneg P hN hε hε1 hΦ
  have hlN : 0 < Real.log P.N := Real.log_pos (by exact_mod_cast (by omega : 1 < P.N))
  have : (0 : ℝ) < P.k := by linarith
  exact_mod_cast this

lemma log_mu_arg_pos (ℓ : ℕ) (hℓ : ℓ ≤ P.L) : 0 < Real.log (2 * (P.mu ℓ : ℝ) / P.delta) := by
  apply Real.log_pos
  have := mu_ge_two P ℓ hℓ
  have hd := delta_pos P hN
  have hd1 := delta_lt_one P hN
  rw [lt_div_iff₀ hd]; nlinarith

lemma p_pos (ℓ : ℕ) (hℓ : ℓ ≤ P.L) : 0 < P.p ℓ := by
  unfold Fig2Params.p
  have := log_mu_arg_pos P hN hε hε1 hΦ ℓ hℓ
  have : (0 : ℝ) < P.k := by exact_mod_cast k_pos P hN hε hε1 hΦ
  positivity

lemma pk_eq (ℓ : ℕ) : P.p ℓ * P.k = 2 * Real.log (2 * (P.mu ℓ : ℝ) / P.delta) := by
  have : (P.k : ℝ) ≠ 0 := by exact_mod_cast (k_pos P hN hε hε1 hΦ).ne'
  unfold Fig2Params.p; field_simp

lemma p_le_one (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) : P.p ℓ ≤ 1 := by
  have hk : (0 : ℝ) < P.k := by exact_mod_cast k_pos P hN hε hε1 hΦ
  have hpk := pk_eq P hN hε hε1 hΦ ℓ
  have hkge := k_ge P hN hε hε1 hΦ
  have hd := delta_pos P hN
  have hd1 := delta_lt_one P hN
  have hmu := mu_le_of_one_le P hN ℓ h1
  have hmu2 := mu_ge_two P ℓ hℓ
  have hNr : (2 : ℝ) ≤ P.N := by exact_mod_cast hN
  -- 2 ln(2μ/δ) ≤ 2 ln 2 + 2 ln (N+1) + 2 ln (1/δ) ≤ 4 ln N + 4 ln (2/δ) ≤ k
  have e1 : Real.log (2 * (P.mu ℓ : ℝ) / P.delta) =
      Real.log 2 + Real.log (P.mu ℓ) + Real.log (1 / P.delta) := by
    rw [mul_div_assoc, Real.log_mul (by norm_num) (by positivity),
      div_eq_mul_one_div (P.mu ℓ : ℝ), Real.log_mul (by positivity) (by positivity)]; ring
  have e2 : Real.log (2 / P.delta) = Real.log 2 + Real.log (1 / P.delta) := by
    rw [div_eq_mul_one_div 2, Real.log_mul (by norm_num) (by positivity)]
  have e3 : Real.log (P.mu ℓ) ≤ Real.log ((P.N : ℝ) + 1) :=
    Real.log_le_log (by positivity) hmu.le
  have e4 : Real.log ((P.N : ℝ) + 1) ≤ 2 * Real.log P.N := by
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    norm_num; nlinarith
  have e5 : 0 ≤ Real.log (1 / P.delta) := Real.log_nonneg (by rw [le_div_iff₀ hd]; linarith)
  have e6 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [← mul_le_mul_iff_of_pos_right hk, one_mul, hpk]
  linarith

/-- `θ_ℓ = (1-p_ℓ)^k ≤ (δ/(2μ_ℓ))^2`. -/
lemma theta_le (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) :
    (1 - P.p ℓ) ^ P.k ≤ (P.delta / (2 * P.mu ℓ)) ^ 2 := by
  have hp0 := p_pos P hN hε hε1 hΦ ℓ hℓ
  have hp1 := p_le_one P hN hε hε1 hΦ ℓ h1 hℓ
  have hpk := pk_eq P hN hε hε1 hΦ ℓ
  have hd := delta_pos P hN
  have hmu := mu_pos P ℓ
  calc (1 - P.p ℓ) ^ P.k ≤ (Real.exp (-P.p ℓ)) ^ P.k := by
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp (-P.p ℓ); linarith
    _ = Real.exp (-(P.p ℓ * P.k)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ = (P.delta / (2 * P.mu ℓ)) ^ 2 := by
        rw [hpk, show -(2 * Real.log (2 * (P.mu ℓ : ℝ) / P.delta)) =
          Real.log (((2 * (P.mu ℓ : ℝ) / P.delta))⁻¹) * 2 by rw [Real.log_inv]; ring]
        rw [Real.exp_mul, Real.exp_log (by positivity)]
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rw [inv_div]

/-- The truncation correction factor `ψ_ℓ = 1/(1-(1-p_ℓ)^k)`. -/
noncomputable def psi (ℓ : ℕ) : ℝ := 1 / (1 - (1 - P.p ℓ) ^ P.k)

lemma theta_small (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) : (1 - P.p ℓ) ^ P.k ≤ 1 / 16 := by
  have h := theta_le P hN hε hε1 hΦ ℓ h1 hℓ
  have hd := delta_pos P hN
  have hd1 := delta_lt_one P hN
  have hmu := mu_ge_two P ℓ hℓ
  refine le_trans h ?_
  rw [div_pow, div_le_iff₀ (by positivity)]
  nlinarith

lemma psi_ge_one (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) : 1 ≤ psi P ℓ := by
  have h := theta_small P hN hε hε1 hΦ ℓ h1 hℓ
  have hp0 := p_pos P hN hε hε1 hΦ ℓ hℓ
  have hp1 := p_le_one P hN hε hε1 hΦ ℓ h1 hℓ
  have : 0 ≤ (1 - P.p ℓ) ^ P.k := pow_nonneg (by linarith) _
  unfold psi; rw [one_le_div (by linarith)]; linarith

lemma psi_mul (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) : psi P ℓ * (1 - (1 - P.p ℓ) ^ P.k) = 1 := by
  have h := theta_small P hN hε hε1 hΦ ℓ h1 hℓ
  unfold psi; rw [one_div, inv_mul_cancel₀]; linarith

lemma psi_pow_le (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) :
    psi P ℓ ^ (P.mu (ℓ - 1)) ≤ Real.exp (P.delta ^ 2 / 2) := by
  have hθ := theta_le P hN hε hε1 hΦ ℓ h1 hℓ
  have hs := theta_small P hN hε hε1 hΦ ℓ h1 hℓ
  have hp0 := p_pos P hN hε hε1 hΦ ℓ hℓ
  have hp1 := p_le_one P hN hε hε1 hΦ ℓ h1 hℓ
  set θ := (1 - P.p ℓ) ^ P.k with hθdef
  have hθ0 : 0 ≤ θ := pow_nonneg (by linarith) _
  have hpsi : psi P ℓ ≤ 1 + 2 * θ := by
    unfold psi; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hmu := mu_sq P ℓ h1 hℓ
  have hmu2 := mu_ge_two P ℓ hℓ
  calc psi P ℓ ^ (P.mu (ℓ - 1)) ≤ (1 + 2 * θ) ^ (P.mu (ℓ - 1)) :=
        pow_le_pow_left₀ (by linarith [psi_ge_one P hN hε hε1 hΦ ℓ h1 hℓ]) hpsi _
    _ ≤ (Real.exp (2 * θ)) ^ (P.mu (ℓ - 1)) := by
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp (2 * θ); linarith
    _ = Real.exp (2 * θ * (P.mu (ℓ - 1) : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (P.delta ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        rw [hmu]
        have : θ * (P.mu ℓ : ℝ) ^ 2 ≤ P.delta ^ 2 / 4 := by
          calc θ * (P.mu ℓ : ℝ) ^ 2 ≤ (P.delta / (2 * P.mu ℓ)) ^ 2 * (P.mu ℓ : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_right hθ (by positivity)
            _ = P.delta ^ 2 / 4 := by field_simp; ring
        nlinarith

/-- The product of truncation factors over the phases is at most `1 + 2δ`. -/
lemma prod_psi_le :
    ∏ j ∈ Finset.Icc 1 P.L, psi P j ^ (P.mu (j - 1)) ≤ 1 + 2 * P.delta := by
  have hd := delta_pos P hN
  have hd1 := delta_lt_one P hN
  have hLd := L_delta_le P hN
  calc ∏ j ∈ Finset.Icc 1 P.L, psi P j ^ (P.mu (j - 1))
      ≤ ∏ _j ∈ Finset.Icc 1 P.L, Real.exp (P.delta ^ 2 / 2) := by
        apply Finset.prod_le_prod
        · intro j hj; rw [Finset.mem_Icc] at hj
          exact pow_nonneg (by linarith [psi_ge_one P hN hε hε1 hΦ j hj.1 hj.2]) _
        · intro j hj; rw [Finset.mem_Icc] at hj
          exact psi_pow_le P hN hε hε1 hΦ j hj.1 hj.2
    _ = Real.exp (P.L * (P.delta ^ 2 / 2)) := by
        rw [Finset.prod_const, Nat.card_Icc, ← Real.exp_nat_mul]; simp
    _ ≤ Real.exp (P.delta / 2) := by
        apply Real.exp_le_exp.mpr
        have : (P.L : ℝ) * P.delta ^ 2 ≤ P.delta := by nlinarith
        linarith
    _ ≤ 1 + 2 * P.delta := by
        have := Real.exp_bound_div_one_sub_of_interval' (x := P.delta / 2) (by linarith) (by linarith)
        refine le_trans this.le ?_
        rw [div_le_iff₀ (by linarith)]; nlinarith

end Std


section Radius

lemma radius_closed (L : ℕ) (Δ : ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ L) :
    radius L Δ ℓ = Δ * (2 ^ (ℓ + 1) - 1) / 2 ^ (L + 4) + ℓ * (Δ / (8 * L)) := by
  induction ℓ with
  | zero => simp [radius]; ring
  | succ j ih =>
    rw [radius, ih (by omega)]
    have : (2 : ℝ) ^ (L - (j + 1) + 4) = 2 ^ (L + 4) / 2 ^ (j + 1) := by
      rw [eq_div_iff (by positivity), ← pow_add]; congr 1; omega
    rw [this]; push_cast; field_simp; ring

lemma radius_nonneg (L : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) (ℓ : ℕ) : 0 ≤ radius L Δ ℓ := by
  induction ℓ with
  | zero => simp [radius]; positivity
  | succ j ih => rw [radius]; positivity

lemma radius_mono (L : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) {a b : ℕ} (hab : a ≤ b) :
    radius L Δ a ≤ radius L Δ b := by
  induction b with
  | zero => rw [Nat.le_zero.mp hab]
  | succ j ih =>
    rcases Nat.of_le_succ hab with h | h
    · rw [radius]; have := ih h; have : 0 ≤ Δ / 2 ^ (L - (j + 1) + 4) := by positivity
      have : 0 ≤ Δ / (8 * L) := by positivity
      linarith
    · rw [h]

lemma radius_L_le (L : ℕ) (hL : 1 ≤ L) {Δ : ℝ} (hΔ : 0 ≤ Δ) : radius L Δ L ≤ Δ / 4 := by
  rw [radius_closed L Δ L le_rfl]
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have : (L : ℝ) * (Δ / (8 * L)) = Δ / 8 := by field_simp
  rw [this]
  have h2 : Δ * (2 ^ (L + 1) - 1) / 2 ^ (L + 4) ≤ Δ / 8 := by
    rw [div_le_iff₀ (by positivity), pow_add, pow_add]
    have : (0:ℝ) < 2 ^ L := by positivity
    nlinarith
  linarith

lemma radius_succ_sub (L : ℕ) (Δ : ℝ) (j : ℕ) :
    radius L Δ (j + 1) - radius L Δ j = Δ / 2 ^ (L - (j + 1) + 4) + Δ / (8 * L) := by
  rw [radius]; ring

end Radius

section Std2

set_option linter.unusedSectionVars false
variable (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ)
include hN hε hε1 hΦ

lemma k_ne_zero_real : (P.k : ℝ) ≠ 0 := by exact_mod_cast (k_pos P hN hε hε1 hΦ).ne'

lemma r_add_kq (Δ : ℝ) (ℓ : ℕ) (h1 : 1 ≤ ℓ) : P.r Δ (ℓ - 1) + P.k * P.q Δ ℓ = P.r Δ ℓ := by
  have := k_ne_zero_real P hN hε hε1 hΦ
  unfold Fig2Params.q; field_simp; ring

lemma q_ge (Δ : ℝ) (hΔ : 0 ≤ Δ) (ℓ : ℕ) (h1 : 1 ≤ ℓ) :
    Δ / (8 * P.L * P.k) ≤ P.q Δ ℓ := by
  have hk : (0:ℝ) < P.k := by exact_mod_cast k_pos P hN hε hε1 hΦ
  unfold Fig2Params.q Fig2Params.r
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [radius_succ_sub]
  rw [← div_div]
  apply div_le_div_of_nonneg_right _ hk.le
  have : 0 ≤ Δ / 2 ^ (P.L - (j + 1) + 4) := by positivity
  linarith


lemma logb_mu (ℓ : ℕ) : Real.logb 2 (P.mu ℓ : ℝ) = 2 ^ (P.L - ℓ) := by
  rw [mu_cast, Real.logb_pow]; simp

lemma log_mu_eq (ℓ : ℕ) : Real.log (P.mu ℓ : ℝ) = 2 ^ (P.L - ℓ) * Real.log 2 := by
  rw [mu_cast, Real.log_pow]; push_cast; ring

lemma log_inv_delta_le : Real.log (1 / P.delta) ≤ 2 * P.L * Real.log 2 := by
  rw [delta_eq P hN]
  have h := two_pow_L_ge P hN
  have hx := logN1_gt_one P hN
  have : Real.log (Real.logb 2 ((P.N : ℝ) + 1)) ≤ Real.log ((2:ℝ) ^ P.L) :=
    Real.log_le_log (by linarith) h
  rw [Real.log_pow] at this
  linarith

lemma log_arg_split (ℓ : ℕ) : Real.log (2 * (P.mu ℓ : ℝ) / P.delta) =
    Real.log (2 / P.delta) + Real.log (P.mu ℓ) := by
  have hd := delta_pos P hN
  have := mu_pos P ℓ
  rw [mul_comm, mul_div_assoc, Real.log_mul (by positivity) (by positivity)]; ring

/-- The pair inequality `p_ℓ·Δ ≤ 2^7·L·log₂ µ_ℓ·q_ℓ` (from inequality (#)). -/
lemma pair_ineq (Δ : ℝ) (hΔ : 0 ≤ Δ) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) :
    P.p ℓ * Δ ≤ 2 ^ 7 * P.L * Real.logb 2 (P.mu ℓ : ℝ) * P.q Δ ℓ := by
  have hk : (0:ℝ) < P.k := by exact_mod_cast k_pos P hN hε hε1 hΦ
  have hL : (1:ℝ) ≤ P.L := by exact_mod_cast L_pos P hN
  have hd := delta_pos P hN
  have hd1 := delta_lt_one P hN
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv := log_inv_delta_le P hN hε hε1 hΦ
  have e2 : Real.log (2 / P.delta) = Real.log 2 + Real.log (1 / P.delta) := by
    rw [div_eq_mul_one_div 2, Real.log_mul (by norm_num) (by positivity)]
  have hsplit := log_arg_split P hN hε hε1 hΦ ℓ
  have hmu := log_mu_eq P hN hε hε1 hΦ ℓ
  rw [logb_mu P hN hε hε1 hΦ]
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  unfold Fig2Params.p Fig2Params.q Fig2Params.r
  simp only [Nat.add_sub_cancel]
  rw [radius_succ_sub]
  set J := P.L - (j + 1) with hJ
  have hpow : (2:ℝ) ^ (J + 4) = 2 ^ J * 16 := by rw [pow_add]; norm_num
  rw [hpow]
  have h2J : (1:ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
  -- reduce to ln(2μ/δ) ≤ 4L + 8·2^J
  have key : Real.log (2 * (P.mu (j + 1) : ℝ) / P.delta) ≤ 4 * P.L + 8 * 2 ^ J := by
    rw [hsplit, e2, hmu]
    nlinarith
  have hLpos : (0:ℝ) < P.L := by linarith
  have hlog0 : 0 ≤ Real.log (2 * (P.mu (j + 1) : ℝ) / P.delta) :=
    (log_mu_arg_pos P hN hε hε1 hΦ (j+1) hℓ).le
  rw [show 2 / (P.k : ℝ) * Real.log (2 * (P.mu (j + 1) : ℝ) / P.delta) * Δ =
      (2 * Real.log (2 * (P.mu (j + 1) : ℝ) / P.delta) * Δ) / P.k by ring]
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hk]
  have e : 2 ^ 7 * (P.L : ℝ) * 2 ^ J * (Δ / (2 ^ J * 16) + Δ / (8 * P.L)) =
      Δ * (8 * P.L + 16 * 2 ^ J) := by field_simp; ring
  rw [e]
  nlinarith

end Std2

end P2

end HopRamsey.FZ


namespace HopRamsey.FZ

open HopRamsey

lemma logb3_ge : (25 / 16 : ℝ) ≤ Real.logb 2 3 := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]
  have h : ((2:ℝ) ^ ((25 / 16 : ℝ))) ^ (16:ℕ) = 2 ^ (25:ℕ) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]; norm_num
  by_contra hc
  push Not at hc
  have := pow_lt_pow_left₀ hc (by norm_num) (by norm_num : (16:ℕ) ≠ 0)
  rw [h] at this
  norm_num at this

lemma one_add_two_delta_le (P : Fig2Params) (hN : 2 ≤ P.N) :
    1 + 2 * P.delta ≤ (2:ℝ) ^ ((9 / 10 : ℝ)) := by
  have hℓ : (25 / 16 : ℝ) ≤ Real.logb 2 ((P.N : ℝ) + 1) := by
    refine le_trans logb3_ge (Real.logb_le_logb_of_le (by norm_num) (by norm_num) ?_)
    have : (2:ℝ) ≤ P.N := by exact_mod_cast hN
    linarith
  have hd : P.delta ≤ 41 / 100 := by
    unfold Fig2Params.delta
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hd0 := P2.delta_pos P hN
  have h10 : (1 + 2 * P.delta) ^ (10:ℕ) ≤ ((2:ℝ) ^ ((9 / 10 : ℝ))) ^ (10:ℕ) := by
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
    calc (1 + 2 * P.delta) ^ 10 ≤ (182 / 100 : ℝ) ^ 10 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 10
      _ ≤ 512 := by norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h10

/-- The fixed-point inequality used to choose the augmentation weight `ω = N^{20c+300}`. -/
theorem fixpt (c : ℕ) (P : Fig2Params) (hN : 2 ≤ P.N) (hε : 1 / (2 * (P.N : ℝ)) ≤ P.ε)
    (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ) (hΦa : P.Φ ≤ (P.N : ℝ) ^ (20 * c + 300)) :
    32 * (P.k : ℝ) * P.L * (P.N : ℝ) ^ (c + 1) ≤ (P.N : ℝ) ^ (20 * c + 300) := by
  have hn2 : (2:ℝ) ≤ (P.N : ℝ) := by exact_mod_cast hN
  have hNle : (P.N : ℝ) ≤ 2 ^ P.N := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hN1le : (P.N : ℝ) + 1 ≤ 2 ^ P.N := by exact_mod_cast Nat.lt_two_pow_self
  have ha3 : (1:ℝ) ≤ ((20 * c + 300 : ℕ) : ℝ) := by push_cast; linarith [(by positivity : (0:ℝ) ≤ (c:ℝ))]
  have h800 : 800 * ((20 * c + 300 : ℕ) : ℝ) ≤ 2 ^ (c + 24) := by
    have : ((c:ℝ) + 1) ≤ 2 ^ c := by exact_mod_cast Nat.lt_two_pow_self
    rw [pow_add]; push_cast; nlinarith
  have hexp : (9 / 10 : ℝ) * ((20 * c + 300 : ℕ) : ℝ) + ((2 * c + 30 : ℕ) : ℝ) =
      ((20 * c + 300 : ℕ) : ℝ) := by push_cast; ring
  generalize hA : 20 * c + 300 = a at *
  generalize hn : (P.N : ℝ) = n at *
  have hn0 : 0 < n := by linarith
  have hε0 : 0 < P.ε := lt_of_lt_of_le (by positivity) hε
  have hd0 := P2.delta_pos P hN
  have hln2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set x := Real.logb 2 P.Φ with hxdef
  have hx1 : 1 ≤ x := by
    rw [hxdef, Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hΦ
  have hlog2n : Real.logb 2 n ≤ n := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) hn0, ← hn, Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self).le
  have hlog2n0 : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by linarith)
  have hx : x ≤ a * Real.logb 2 n := by
    have : x ≤ Real.logb 2 (n ^ a) := Real.logb_le_logb_of_le (by norm_num) (by linarith) hΦa
    rwa [Real.logb_pow] at this
  -- the power bound
  have hy : (1 + 2 * P.delta) ^ x ≤ n ^ ((9 / 10 : ℝ) * a) := by
    calc (1 + 2 * P.delta) ^ x ≤ ((2:ℝ) ^ ((9 / 10 : ℝ))) ^ x :=
          Real.rpow_le_rpow (by linarith) (one_add_two_delta_le P hN) (by linarith)
      _ = (2:ℝ) ^ ((9 / 10 : ℝ) * x) := by rw [← Real.rpow_mul (by norm_num)]
      _ ≤ (2:ℝ) ^ ((9 / 10 : ℝ) * (a * Real.logb 2 n)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = n ^ ((9 / 10 : ℝ) * a) := by
          rw [show (9 / 10 : ℝ) * (a * Real.logb 2 n) = Real.logb 2 n * ((9 / 10 : ℝ) * a) by ring,
            Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0]
  have hy0 : 0 ≤ (1 + 2 * P.delta) ^ x := by positivity
  set Y := n ^ ((9 / 10 : ℝ) * a) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow (by linarith) (by positivity)
  -- k bound
  have hlnn : Real.log n ≤ n := by have := Real.log_le_sub_one_of_pos hn0; linarith
  have hlnn0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  set ℓ := Real.logb 2 ((P.N : ℝ) + 1) with hℓ
  have hℓ1 : 1 < ℓ := P2.logN1_gt_one P hN
  have hℓn : ℓ ≤ n := by
    rw [hℓ, Real.logb_le_iff_le_rpow (by norm_num) (by positivity), ← hn, Real.rpow_natCast]
    exact_mod_cast Nat.lt_two_pow_self
  have hl2d : Real.log (2 / P.delta) ≤ 2 * n := by
    have e : Real.log (2 / P.delta) = Real.log 2 + 2 * Real.log ℓ := by
      have hdef : P.delta = (ℓ ^ 2)⁻¹ := rfl
      rw [hdef, div_inv_eq_mul, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    have h1 := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < ℓ)
    have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    rw [e]; linarith
  have hl2d0 : 0 ≤ Real.log (2 / P.delta) := P2.log2_delta_nonneg P hN hε0 hε1 hΦ
  have ha1 : (1:ℝ) ≤ a := ha3
  have hT : Real.log n + Real.log (2 / P.delta) * x ≤ 3 * a * n ^ 2 := by
    have : Real.log (2 / P.delta) * x ≤ 2 * n * (a * n) :=
      mul_le_mul hl2d (le_trans hx (mul_le_mul_of_nonneg_left hlog2n (by linarith))) (by linarith)
        (by linarith)
    nlinarith
  have hT0 : 0 ≤ Real.log n + Real.log (2 / P.delta) * x := by
    have : 0 ≤ Real.log (2 / P.delta) * x := mul_nonneg hl2d0 (by linarith)
    linarith
  have h4e : 4 / P.ε ≤ 8 * n := by
    rw [div_le_iff₀ hε0]
    rw [div_le_iff₀ (by positivity)] at hε
    nlinarith
  have hk : (P.k : ℝ) ≤ 25 * a * n ^ 3 * Y := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ (4 / P.ε) * (1 + 2 * P.delta) ^ x *
        (Real.log n + Real.log (2 / P.delta) * x) by positivity)
    have hk' : (P.k : ℝ) < (4 / P.ε) * (1 + 2 * P.delta) ^ x *
        (Real.log n + Real.log (2 / P.delta) * x) + 1 := by
      unfold Fig2Params.k; rw [hn]; exact hc
    have h1 : (4 / P.ε) * (1 + 2 * P.delta) ^ x * (Real.log n + Real.log (2 / P.delta) * x) ≤
        (8 * n) * Y * (3 * a * n ^ 2) := by
      apply mul_le_mul (mul_le_mul h4e hy hy0 (by positivity)) hT hT0 (by positivity)
    have h2 : (1:ℝ) ≤ a * n ^ 3 * Y := by
      have : (1:ℝ) ≤ n ^ 3 := one_le_pow₀ (by linarith)
      have h5 : (1:ℝ) ≤ a * n ^ 3 := by
        have := mul_le_mul ha1 this zero_le_one (by linarith); linarith
      have := mul_le_mul h5 hY1 zero_le_one (by linarith); linarith
    have e : (8 * n) * Y * (3 * a * n ^ 2) = 24 * (a * n ^ 3 * Y) := by ring
    have h3 := lt_of_lt_of_le hk' (add_le_add_left h1 1)
    rw [e] at h3
    have e2 : 25 * (a:ℝ) * n ^ 3 * Y = 25 * (a * n ^ 3 * Y) := by ring
    rw [e2]
    linarith only [h3, h2]
  -- L bound
  have hL : (P.L : ℝ) ≤ n ^ 2 := by
    have h1 := P2.L_delta_le P hN
    have hdef : P.delta = (ℓ ^ 2)⁻¹ := rfl
    rw [hdef, ← div_eq_mul_inv, div_le_one (by positivity)] at h1
    have : ℓ ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ (by linarith) hℓn 2
    linarith
  have hL0 : (0:ℝ) ≤ P.L := by positivity
  have hk0 : (0:ℝ) ≤ P.k := by positivity
  -- combine
  have hfin : 800 * (a:ℝ) * n ^ (c + 6) ≤ n ^ (2 * c + 30) := by
    have h1 : n ^ (2 * c + 30) = n ^ (c + 6) * n ^ (c + 24) := by rw [← pow_add]; ring_nf
    have h2 : (2:ℝ) ^ (c + 24) ≤ n ^ (c + 24) := pow_le_pow_left₀ (by norm_num) hn2 _
    have h3 : 800 * (a:ℝ) ≤ 2 ^ (c + 24) := h800
    rw [h1]
    have : 0 ≤ n ^ (c + 6) := by positivity
    nlinarith
  have hsplit : n ^ (a : ℕ) = Y * n ^ (2 * c + 30) := by
    rw [hY, ← Real.rpow_natCast n (2 * c + 30), ← Real.rpow_add hn0, ← Real.rpow_natCast]
    congr 1; exact hexp.symm
  calc 32 * (P.k : ℝ) * P.L * n ^ (c + 1) ≤ 32 * (25 * a * n ^ 3 * Y) * n ^ 2 * n ^ (c + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul (by linarith) hL hL0 (by positivity)
    _ = Y * (800 * a * n ^ (c + 6)) := by ring
    _ ≤ Y * n ^ (2 * c + 30) := mul_le_mul_of_nonneg_left hfin (by linarith)
    _ = n ^ a := hsplit.symm

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

lemma fin_bind {α β : Type*} {p : PMF α} {f : α → PMF β} (hp : p.support.Finite)
    (hf : ∀ a ∈ p.support, (f a).support.Finite) : (p.bind f).support.Finite := by
  rw [PMF.support_bind]; exact hp.biUnion hf

lemma fin_map {α β : Type*} {p : PMF α} (g : α → β) (hp : p.support.Finite) :
    (p.map g).support.Finite := by
  rw [PMF.support_map]; exact hp.image g

lemma fin_pure {α : Type*} (a : α) : (PMF.pure a).support.Finite := by
  rw [PMF.support_pure]; exact Set.finite_singleton a

lemma truncGeom_fin (p : ℝ) (k : ℕ) : (truncGeom p k).support.Finite := by
  unfold truncGeom
  split_ifs
  · exact fin_map _ (Set.toFinite _)
  · exact fin_pure 0

variable (P : Fig2Params) (G : WGraph V) (h : ℕ) (rule : CenterRule V)

lemma phaseLoop_fin (X M : Finset V) (Δ : ℝ) (ℓ : ℕ) :
    ∀ fuel s, (phaseLoop P G h rule X M Δ ℓ fuel s).support.Finite := by
  intro fuel
  induction fuel with
  | zero => intro s; exact fin_pure s
  | succ fuel ih =>
    intro s
    rw [phaseLoop]
    split_ifs
    · exact fin_bind (truncGeom_fin _ _) (fun _ _ => ih _)
    · exact fin_pure s

lemma phasesFrom_fin (X M : Finset V) (Δ : ℝ) :
    ∀ ℓ s, (phasesFrom P G h rule X M Δ ℓ s).support.Finite := by
  intro ℓ
  induction ℓ with
  | zero => intro s; exact fin_pure s
  | succ j ih => intro s; exact fin_bind (phaseLoop_fin P G h rule X M Δ _ _ _) (fun _ _ => ih _)

lemma ssp_fin (X M : Finset V) (Δ : ℝ) :
    (singleScalePartition P G h rule X M Δ).support.Finite :=
  fin_map _ (phasesFrom_fin P G h rule X M Δ _ _)

lemma seqPMF_fin {α : Type} : ∀ (ps : List (PMF α)), (∀ p ∈ ps, p.support.Finite) →
    (seqPMF ps).support.Finite := by
  intro ps
  induction ps with
  | nil => intro _; exact fin_pure _
  | cons p ps ih =>
    intro hps
    exact fin_bind (hps p List.mem_cons_self) (fun a _ =>
      fin_map _ (ih fun q hq => hps q (List.mem_cons_of_mem p hq)))

lemma hseFuel_fin : ∀ fuel X M Δ, (hseFuel P G h rule fuel X M Δ).support.Finite := by
  intro fuel
  induction fuel with
  | zero => intro X M Δ; rw [hseFuel]; split_ifs <;> exact fin_pure _
  | succ fuel ih =>
    intro X M Δ
    rw [hseFuel]
    split_ifs
    · exact fin_pure _
    · exact fin_bind (ssp_fin P G h rule X M Δ) (fun C _ => fin_map _ (seqPMF_fin _ (by
        intro p hp
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hp
        exact ih _ _ _)))

theorem hopStochEmbedding_fin (X M : Finset V) (Δ : ℝ) :
    (hopStochEmbedding P G h rule X M Δ).support.Finite :=
  hseFuel_fin P G h rule _ X M Δ

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey

variable {V : Type}

/-- `G` with all weights multiplied by `s > 0`. -/
def scaleG (G : WGraph V) (s : ℝ) (hs : 0 < s) : WGraph V where
  graph := G.graph
  w := fun e => s * G.w e
  w_pos := fun e he => mul_pos hs (G.w_pos e he)

lemma walkWeight_scaleG (G : WGraph V) {s : ℝ} (hs : 0 < s) {u v : V} (p : G.graph.Walk u v) :
    (scaleG G s hs).walkWeight p = ENNReal.ofReal s * G.walkWeight p := by
  unfold WGraph.walkWeight
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [scaleG]
  rw [ENNReal.ofReal_mul hs.le]

lemma hopDist_scaleG (G : WGraph V) {s : ℝ} (hs : 0 < s) (a : ℕ) (u v : V) :
    hopDist (scaleG G s hs) a u v = ENNReal.ofReal s * hopDist G a u v := by
  have h0 : ENNReal.ofReal s ≠ 0 := by simpa using hs
  unfold hopDist
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  congr 1; ext p
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  congr 1; ext _
  exact walkWeight_scaleG G hs p

/-- An HST with all labels multiplied by `c ≠ 0`. -/
noncomputable def scaleHST (c : ℝ≥0∞) (hc : c ≠ 0) (U : HST V) : HST V where
  leaves := U.leaves
  ρ := fun x y => c * U.ρ x y
  self := fun x hx => by simp [U.self x hx]
  symm := fun x y => by rw [U.symm x y]
  ultra := by
    intro x hx y hy z hz
    have := U.ultra x hx y hy z hz
    rcases le_total (U.ρ x y) (U.ρ y z) with h' | h'
    · rw [max_eq_right h'] at this
      exact le_trans (mul_le_mul_right this c) (le_max_right _ _)
    · rw [max_eq_left h'] at this
      exact le_trans (mul_le_mul_right this c) (le_max_left _ _)
  off := fun u v huv => by rw [U.off u v huv, ENNReal.mul_top hc]

theorem embed_unscale [Fintype V] [DecidableEq V] (G : WGraph V) {s : ℝ} (hs : 0 < s) (h : ℕ)
    (D : PMF (HST V × Finset V)) (β : ℕ) (k p t : ℝ)
    (hD : IsStochRamseyEmbedding (scaleG G s hs) h D β k p t) :
    IsStochRamseyEmbedding G h
      (D.map fun x => (scaleHST (ENNReal.ofReal (1 / s)) (by simpa using hs) x.1, x.2)) β k p t := by
  obtain ⟨hH, hDi, hE, hX⟩ := hD
  set c := ENNReal.ofReal (1 / s)
  have hc0 : c ≠ 0 := by simp only [c]; simpa using hs
  have hcs : c * ENNReal.ofReal s = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hs.ne', ENNReal.ofReal_one]
  have cancel : ∀ y : ℝ≥0∞, c * (ENNReal.ofReal s * y) = y := fun y => by
    rw [← mul_assoc, hcs, one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx u v
    rw [PMF.support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hH y hy u v
    rw [hopDist_scaleG] at this
    simp only [scaleHST]
    rw [← cancel (hopDist G (β * h) u v)]
    exact mul_le_mul_right this c
  · intro x hx u hu v
    rw [PMF.support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := hDi y hy u hu v
    rw [hopDist_scaleG] at this
    simp only [scaleHST]
    calc c * y.1.ρ v u ≤ c * (ENNReal.ofReal k * (ENNReal.ofReal s * hopDist G h u v)) :=
          mul_le_mul_right this c
      _ = ENNReal.ofReal k * hopDist G h u v := by
          rw [mul_left_comm, cancel]
  · intro v
    rw [PMF.toOuterMeasure_map_apply]
    exact hE v
  · intro u v
    have e := ex_map D (fun x => (scaleHST c hc0 x.1, x.2))
      (fun x => if u ∈ x.2 ∧ v ∈ x.2 then x.1.ρ u v else 0)
    unfold ex at e
    rw [e]
    have := hX u v
    rw [hopDist_scaleG] at this
    calc ∑' y, D y * (if u ∈ (scaleHST c hc0 y.1, y.2).2 ∧
            v ∈ (scaleHST c hc0 y.1, y.2).2 then
            (scaleHST c hc0 y.1, y.2).1.ρ u v else 0)
        = c * ∑' y, D y * (if u ∈ y.2 ∧ v ∈ y.2 then y.1.ρ u v else 0) := by
          rw [← ENNReal.tsum_mul_left]
          congr 1; ext y
          simp only [scaleHST]
          split_ifs <;> ring
      _ ≤ c * (ENNReal.ofReal t * (ENNReal.ofReal s * hopDist G h u v)) := mul_le_mul_right this c
      _ = ENNReal.ofReal t * hopDist G h u v := by rw [mul_left_comm, cancel]

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey

set_option linter.unusedSectionVars false
set_option linter.deprecated false
variable {V : Type} [Fintype V] [DecidableEq V]

theorem embed_mono {G : WGraph V} {h : ℕ} {D : PMF (HST V × Finset V)} {β : ℕ} {k p t k' p' t' : ℝ}
    (hD : IsStochRamseyEmbedding G h D β k p t) (hk : k ≤ k') (hp : p ≤ p') (ht : t ≤ t') :
    IsStochRamseyEmbedding G h D β k' p' t' := by
  obtain ⟨h1, h2, h3, h4⟩ := hD
  refine ⟨h1, fun x hx u hu v => le_trans (h2 x hx u hu v)
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal hk) _),
    fun v => le_trans (h3 v) (ENNReal.ofReal_le_ofReal hp),
    fun u v => le_trans (h4 u v) (mul_le_mul_left (ENNReal.ofReal_le_ofReal ht) _)⟩

theorem embed_condition (G : WGraph V) (h : ℕ) (D : PMF (HST V × Finset V)) (β : ℕ)
    (k ε0 t : ℝ) (hD : IsStochRamseyEmbedding G h D β k ε0 t)
    (hε0 : (Fintype.card V : ℝ) * ε0 ≤ 1 / 2) (ε : ℝ) :
    ∃ D' : PMF (HST V × Finset V), (∀ x ∈ D'.support, x ∈ D.support) ∧
      IsStochRamseyEmbedding G h D' β k ε (2 * t) := by
  classical
  obtain ⟨hH, hDi, hEx, hX⟩ := hD
  set E : Set (HST V × Finset V) := {x | x.2 = Finset.univ}
  have hcomp : D.toOuterMeasure Eᶜ ≤ ENNReal.ofReal (1 / 2) := by
    have hsub : Eᶜ ⊆ ⋃ v : V, {x : HST V × Finset V | v ∉ x.2} := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, E] at hx
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      by_contra hc; push Not at hc
      exact hx (Finset.eq_univ_iff_forall.mpr hc)
    calc D.toOuterMeasure Eᶜ ≤ D.toOuterMeasure (⋃ v : V, {x : HST V × Finset V | v ∉ x.2}) :=
          MeasureTheory.measure_mono hsub
      _ ≤ ∑ v : V, D.toOuterMeasure {x : HST V × Finset V | v ∉ x.2} :=
          MeasureTheory.measure_iUnion_fintype_le _ _
      _ ≤ ∑ _v : V, ENNReal.ofReal ε0 := Finset.sum_le_sum fun v _ => hEx v
      _ = ENNReal.ofReal ((Fintype.card V : ℝ) * ε0) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          by_cases he : 0 ≤ ε0
          · rw [ENNReal.ofReal_mul (by positivity)]; simp
          · push Not at he
            rw [ENNReal.ofReal_eq_zero.mpr he.le, ENNReal.ofReal_eq_zero.mpr]
            · simp
            · nlinarith [(by positivity : (0:ℝ) ≤ Fintype.card V)]
      _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hε0
  have hsum : D.toOuterMeasure E + D.toOuterMeasure Eᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    simp_rw [Set.indicator_self_add_compl_apply]
    exact PMF.tsum_coe D
  have hE : ENNReal.ofReal (1 / 2) ≤ D.toOuterMeasure E := by
    have h1 : ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) = 1 := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    have h0 : 1 ≤ D.toOuterMeasure E + ENNReal.ofReal (1 / 2) := hsum ▸ add_le_add le_rfl hcomp
    by_contra hc; push Not at hc
    have h2 := ENNReal.add_lt_add_right (ENNReal.ofReal_ne_top (r := 1 / 2)) hc
    rw [h1] at h2
    exact absurd (lt_of_le_of_lt h0 h2) (lt_irrefl 1)
  have hne : ∃ a ∈ E, a ∈ D.support := by
    by_contra hc; push Not at hc
    have : D.toOuterMeasure E = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro a ha ha'; exact hc a ha' ha
    rw [this] at hE
    simp at hE
  set D' := D.filter E hne
  have hle : ∀ a, D' a ≤ 2 * D a := by
    intro a
    simp only [D', PMF.filter_apply]
    have hZ : (∑' a', E.indicator D a') = D.toOuterMeasure E := (PMF.toOuterMeasure_apply D E).symm
    rw [hZ]
    have hinv : (D.toOuterMeasure E)⁻¹ ≤ 2 := by
      rw [ENNReal.inv_le_iff_inv_le]
      refine le_trans (le_of_eq ?_) hE
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    calc E.indicator D a * (D.toOuterMeasure E)⁻¹ ≤ D a * 2 :=
          mul_le_mul' (Set.indicator_le_self E D a) hinv
      _ = 2 * D a := mul_comm _ _
  have hsupp : ∀ x ∈ D'.support, x ∈ E ∧ x ∈ D.support := fun x hx =>
    (PMF.mem_support_filter_iff hne).mp hx
  refine ⟨D', fun x hx => (hsupp x hx).2, ?_, ?_, ?_, ?_⟩
  · exact fun x hx => hH x (hsupp x hx).2
  · exact fun x hx => hDi x (hsupp x hx).2
  · intro v
    have : D'.toOuterMeasure {x | v ∉ x.2} = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
      intro x hx hv
      change v ∉ x.2 at hv
      have := (hsupp x hx).1
      simp only [E, Set.mem_setOf_eq] at this
      rw [this] at hv; exact hv (Finset.mem_univ v)
    rw [this]; exact bot_le
  · intro u v
    calc ∑' x, D' x * (if u ∈ x.2 ∧ v ∈ x.2 then x.1.ρ u v else 0)
        ≤ ∑' x, 2 * (D x * (if u ∈ x.2 ∧ v ∈ x.2 then x.1.ρ u v else 0)) :=
          ENNReal.tsum_le_tsum fun x => by rw [← mul_assoc]; exact mul_le_mul_left (hle x) _
      _ = 2 * ∑' x, D x * (if u ∈ x.2 ∧ v ∈ x.2 then x.1.ρ u v else 0) := ENNReal.tsum_mul_left
      _ ≤ 2 * (ENNReal.ofReal t * hopDist G h u v) := mul_le_mul_right (hX u v) _
      _ = ENNReal.ofReal (2 * t) * hopDist G h u v := by
          rw [ENNReal.ofReal_mul (by norm_num), ← mul_assoc]; simp

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey

variable {V : Type}

lemma aug_w_of_edge (G : WGraph V) {ω : ℝ} (hω : 0 < ω) {e : Sym2 V} (he : e ∈ G.graph.edgeSet) :
    (augmentComplete G ω hω).w e = G.w e := by
  classical
  unfold augmentComplete; simp only; rw [if_pos he]

lemma aug_w_of_not_edge (G : WGraph V) {ω : ℝ} (hω : 0 < ω) {e : Sym2 V}
    (he : e ∉ G.graph.edgeSet) : (augmentComplete G ω hω).w e = ω := by
  classical
  unfold augmentComplete; simp only; rw [if_neg he]


variable [Fintype V] [DecidableEq V]

lemma hopDist_le_hopDiam (G : WGraph V) (a : ℕ) {X : Finset V} {u v : V} (hu : u ∈ X)
    (hv : v ∈ X) : hopDist G a u v ≤ hopDiam G a X := by
  unfold hopDiam
  exact le_trans (Finset.le_sup (f := fun v => hopDist G a u v) hv)
    (Finset.le_sup (f := fun u => X.sup fun v => hopDist G a u v) hu)

lemma hopDiam_le (G : WGraph V) (a : ℕ) {X : Finset V} {c : ℝ≥0∞}
    (h : ∀ u ∈ X, ∀ v ∈ X, hopDist G a u v ≤ c) : hopDiam G a X ≤ c := by
  unfold hopDiam
  exact Finset.sup_le fun u hu => Finset.sup_le fun v hv => h u hu v hv

/-- The discrete HST on `V` (all distinct pairs at distance `∞`). -/
def discreteHST : HST V where
  leaves := Set.univ
  ρ := fun x y => if x = y then 0 else ⊤
  self := by intro x _; simp
  symm := by intro x y; by_cases hxy : x = y <;> simp [hxy, eq_comm]
  ultra := by
    intro x _ y _ z _
    by_cases hxz : x = z
    · simp [hxz]
    · rw [if_neg hxz]
      by_cases hxy : x = y
      · subst hxy; simp [hxz]
      · simp [hxy]
  off := by intro u v huv; simp at huv


end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

open Classical in
/-- A valid center rule: any eligible vertex, if one exists. -/
noncomputable def rule0 (P : Fig2Params) (G : WGraph V) (h : ℕ) (v0 : V) : CenterRule V :=
  fun X₀ _ Δ ℓ s => if hx : ∃ x, Eligible P G h Δ X₀.card s.active ℓ x then hx.choose else v0

lemma rule0_valid (P : Fig2Params) (G : WGraph V) (h : ℕ) (v0 : V) :
    IsValidRule P G h (rule0 P G h v0) := by
  intro X₀ M₀ Δ ℓ s hx
  unfold rule0
  rw [dif_pos hx]
  exact hx.choose_spec

lemma HST_eq {U U' : HST V} (h1 : U.leaves = U'.leaves) (h2 : U.ρ = U'.ρ) : U = U' := by
  cases U; cases U'; simp only at h1 h2; subst h1; subst h2; rfl

/-- Finite support of a law whose image under `(U, M) ↦ (ρ_U, M)` has finite support, when all
HSTs in the support have leaf set `V`. -/
lemma support_finite_of_map {D : PMF (HST V × Finset V)}
    (hleaves : ∀ x ∈ D.support, x.1.leaves = Set.univ)
    (hfin : (D.map (fun x => (x.1.ρ, x.2))).support.Finite) : D.support.Finite := by
  rw [PMF.support_map] at hfin
  refine Set.Finite.of_finite_image hfin ?_
  intro x hx y hy hxy
  simp only [Prod.mk.injEq] at hxy
  exact Prod.ext (HST_eq ((hleaves x hx).trans (hleaves y hy).symm) hxy.1) hxy.2

/-! ### The augmented graph -/

lemma aug_edge_ge (G : WGraph V) {ω : ℝ} (hω : 0 < ω) (hω2 : 2 ≤ ω)
    (hw : ∀ e ∈ G.graph.edgeSet, 2 ≤ G.w e) :
    ∀ e ∈ (augmentComplete G ω hω).graph.edgeSet, 2 ≤ (augmentComplete G ω hω).w e := by
  intro e _
  by_cases he : e ∈ G.graph.edgeSet
  · rw [aug_w_of_edge G hω he]; exact hw e he
  · rw [aug_w_of_not_edge G hω he]; exact hω2

lemma aug_hopDist_le (G : WGraph V) {ω W : ℝ} (hω : 0 < ω) (hWω : W ≤ ω)
    (hw : ∀ e ∈ G.graph.edgeSet, G.w e ≤ W) {h : ℕ} (hh : 1 ≤ h) (u v : V) :
    hopDist (augmentComplete G ω hω) h u v ≤ ENNReal.ofReal ω := by
  by_cases huv : u = v
  · subst huv; rw [hopDist_self]; exact bot_le
  · have hadj : (augmentComplete G ω hω).graph.Adj u v := by
      unfold augmentComplete; simpa using huv
    let p : (augmentComplete G ω hω).graph.Walk u v := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
    refine le_trans (hopDist_le_walk _ p (by simp [p]; exact hh)) ?_
    simp only [p, WGraph.walkWeight, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    apply ENNReal.ofReal_le_ofReal
    by_cases he : s(u, v) ∈ G.graph.edgeSet
    · rw [aug_w_of_edge G hω he]; exact le_trans (hw _ he) hWω
    · rw [aug_w_of_not_edge G hω he]

lemma walkWeight_le_length (G : WGraph V) {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ e ∈ G.graph.edgeSet, G.w e ≤ W) {u v : V} (p : G.graph.Walk u v) :
    G.walkWeight p ≤ p.length * ENNReal.ofReal W := by
  unfold WGraph.walkWeight
  rw [← SimpleGraph.Walk.length_edges]
  have := List.sum_le_card_nsmul (p.edges.map fun e => ENNReal.ofReal (G.w e)) (ENNReal.ofReal W)
    (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      exact ENNReal.ofReal_le_ofReal (hw e (p.edges_subset_edgeSet he)))
  rw [List.length_map, nsmul_eq_mul] at this
  exact this

lemma maxFinite_le (G : WGraph V) {W : ℝ} (hW : 0 ≤ W) (hw : ∀ e ∈ G.graph.edgeSet, G.w e ≤ W)
    (h : ℕ) : maxFiniteHopDist G h ≤ ENNReal.ofReal (h * W) := by
  unfold maxFiniteHopDist
  refine Finset.sup_le fun u _ => Finset.sup_le fun v _ => ?_
  split_ifs with hlt
  · unfold hopDist at hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨p, hp⟩ := hlt
    rw [iInf_lt_iff] at hp
    obtain ⟨hpl, -⟩ := hp
    refine le_trans (hopDist_le_walk G p hpl) (le_trans (walkWeight_le_length G hW hw p) ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    exact mul_le_mul_left (by exact_mod_cast hpl) _
  · exact bot_le

theorem core (c : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (h : ℕ) (ε : ℝ),
      2 ≤ Fintype.card V →
      (∀ e ∈ G.graph.edgeSet, ∀ e' ∈ G.graph.edgeSet,
        G.w e ≤ (Fintype.card V : ℝ) ^ c * G.w e') →
      1 ≤ h → h ≤ Fintype.card V → 1 / (2 * (Fintype.card V : ℝ)) ≤ ε → ε < 1 →
      ∃ D : PMF (HST V × Finset V), D.support.Finite ∧
        (∀ x ∈ D.support, x.1.leaves = Set.univ) ∧
        ∃ β : ℕ, (β : ℝ) ≤ C * polylogBound K (Fintype.card V) / ε ∧
          IsStochRamseyEmbedding G h D β (C * polylogBound K (Fintype.card V) / ε) ε
            (C * polylogBound K (Fintype.card V)) := by
  obtain ⟨C, hC, K, hpar⟩ := HopRamsey.finite_case_parameters (20 * c + 300)
  refine ⟨C, hC, K, ?_⟩
  intro V _ _ G h ε hn hpoly hh hhn hε hε1
  have hn2 : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hn0 : (0:ℝ) < Fintype.card V := by linarith
  have hε0 : 0 < ε := lt_of_lt_of_le (by positivity) hε
  -- scaling to minimum weight `2`
  obtain ⟨s, hs, hsw⟩ : ∃ s : ℝ, 0 < s ∧ ∀ e ∈ G.graph.edgeSet,
      2 ≤ s * G.w e ∧ s * G.w e ≤ 2 * (Fintype.card V : ℝ) ^ c := by
    by_cases hne : G.graph.edgeSet.Nonempty
    · obtain ⟨e0, he0, hmin⟩ := Set.exists_min_image G.graph.edgeSet G.w (Set.toFinite _) hne
      have hw0 := G.w_pos e0 he0
      refine ⟨2 / G.w e0, div_pos two_pos hw0, fun e he => ⟨?_, ?_⟩⟩
      · rw [div_mul_eq_mul_div, le_div_iff₀ hw0]; nlinarith [hmin e he]
      · rw [div_mul_eq_mul_div, div_le_iff₀ hw0]; nlinarith [hpoly e he e0 he0]
    · exact ⟨1, one_pos, fun e he => absurd ⟨e, he⟩ hne⟩
  set Gs := scaleG G s hs with hGsdef
  have hGs : ∀ e ∈ Gs.graph.edgeSet, 2 ≤ Gs.w e ∧ Gs.w e ≤ 2 * (Fintype.card V : ℝ) ^ c := hsw
  set ω : ℝ := (Fintype.card V : ℝ) ^ (20 * c + 300) with hωdef
  have hω : 0 < ω := by positivity
  have hω2nc : 2 * (Fintype.card V : ℝ) ^ c ≤ ω := by
    rw [hωdef, show 20 * c + 300 = c + (19 * c + 300) by ring, pow_add]
    have : (2:ℝ) ≤ (Fintype.card V : ℝ) ^ (19 * c + 300) :=
      le_trans hn2 (le_self_pow₀ (by linarith) (by omega))
    have : (0:ℝ) ≤ (Fintype.card V : ℝ) ^ c := by positivity
    nlinarith
  have hω2 : 2 ≤ ω := by
    have : (1:ℝ) ≤ (Fintype.card V : ℝ) ^ c := one_le_pow₀ (by linarith)
    linarith
  set G' := augmentComplete Gs ω hω with hG'def
  have hw' : ∀ e ∈ G'.graph.edgeSet, 2 ≤ G'.w e :=
    aug_edge_ge Gs hω hω2 (fun e he => (hGs e he).1)
  have hdist_le : ∀ u v, hopDist G' h u v ≤ ENNReal.ofReal ω :=
    aug_hopDist_le Gs hω hω2nc (fun e he => (hGs e he).2) hh
  have hdiam_le : hopDiam G' h Finset.univ ≤ ENNReal.ofReal ω :=
    hopDiam_le G' h (fun u _ v _ => hdist_le u v)
  have hΦfin : hopDiam G' h Finset.univ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hdiam_le
  set Φ := (hopDiam G' h Finset.univ).toReal with hΦdef
  have hΦω : Φ ≤ ω := ENNReal.toReal_le_of_le_ofReal hω.le hdiam_le
  obtain ⟨u0, v0, huv0⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  have hΦ2 : 2 ≤ Φ := by
    have h1 := hopDist_ge_of_ne G' hw' h huv0
    have h2 := le_trans h1 (hopDist_le_hopDiam G' h (Finset.mem_univ u0) (Finset.mem_univ v0))
    rw [hΦdef]
    exact (ENNReal.ofReal_le_iff_le_toReal hΦfin).mp h2
  let P : Fig2Params := ⟨Fintype.card V, Φ, ε⟩
  have hS : Standing P G' h := ⟨rfl, hn, hw', hΦ2, hε0, hε1, hh⟩
  obtain ⟨D', hleaves', hmap', hH', hDi', hEx', hfe, hX'⟩ :=
    HopRamsey.finite_case P G' h (rule0 P G' h u0) hS (rule0_valid P G' h u0) hΦfin rfl
  have hemb' : IsStochRamseyEmbedding G' h D' (2 * P.k * (P.L + 1)) ((P.k : ℝ) * 8 * P.L) ε
      (P.g P.N P.Φ) := ⟨hH', hDi', fun v => le_trans (hEx' v) (ENNReal.ofReal_le_ofReal hfe), hX'⟩
  have hΦa : P.Φ ≤ (P.N : ℝ) ^ (20 * c + 300) := hΦω
  have hfix := fixpt c P hn hε hε1 hΦ2 hΦa
  have hk1 : (1:ℝ) ≤ P.k := by exact_mod_cast P2.k_pos P hn hε0 hε1 hΦ2
  have hL1 : (1:ℝ) ≤ P.L := by exact_mod_cast P2.L_pos P hn
  have hρ1 : 1 ≤ (P.k : ℝ) * 8 * P.L := by nlinarith
  have hωΦ : ENNReal.ofReal (2 * ((P.k : ℝ) * 8 * P.L)) * maxFiniteHopDist Gs h ≤
      ENNReal.ofReal ω := by
    have hW : (0:ℝ) ≤ 2 * (Fintype.card V : ℝ) ^ c := by positivity
    have h1 := maxFinite_le Gs hW (fun e he => (hGs e he).2) h
    have h2 : (h : ℝ) * (2 * (Fintype.card V : ℝ) ^ c) ≤ 2 * (Fintype.card V : ℝ) ^ (c + 1) := by
      have : (h : ℝ) ≤ Fintype.card V := by exact_mod_cast hhn
      rw [pow_succ]; nlinarith [(by positivity : (0:ℝ) ≤ (Fintype.card V : ℝ) ^ c)]
    calc ENNReal.ofReal (2 * ((P.k : ℝ) * 8 * P.L)) * maxFiniteHopDist Gs h
        ≤ ENNReal.ofReal (2 * ((P.k : ℝ) * 8 * P.L)) *
            ENNReal.ofReal (2 * (Fintype.card V : ℝ) ^ (c + 1)) :=
          mul_le_mul_right (h1.trans (ENNReal.ofReal_le_ofReal h2)) _
      _ = ENNReal.ofReal (32 * (P.k : ℝ) * P.L * (P.N : ℝ) ^ (c + 1)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      _ ≤ ENNReal.ofReal ω := ENNReal.ofReal_le_ofReal hfix
  obtain ⟨hleaves1, hemb1⟩ := HopRamsey.remove_finite_diameter Gs h _ _ ε _ ω hρ1 hω hωΦ D' hleaves' hemb'
  have hemb2 := embed_unscale G hs h _ _ _ _ _ hemb1
  obtain ⟨b1, b2, b3⟩ := hpar P hn hε0 hε1 hΦ2 hΦa
  have hfinD' : D'.support.Finite := by
    apply support_finite_of_map hleaves'
    rw [hmap']; exact hopStochEmbedding_fin _ _ _ _ _ _ _
  refine ⟨_, fin_map _ (fin_map _ hfinD'), ?_, 2 * P.k * (P.L + 1), ?_,
    embed_mono hemb2 b2 le_rfl b3⟩
  · intro x hx
    rw [PMF.support_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hleaves1 y hy
  · push_cast; exact b1

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey

lemma polylog_nonneg (K n : ℕ) : 0 ≤ polylogBound K n := by
  unfold polylogBound
  have h1 : 0 ≤ Real.logb 2 ((n : ℝ) + 1) := Real.logb_nonneg (by norm_num) (by
    have : (0:ℝ) ≤ n := by positivity
    linarith)
  have h2 : 0 ≤ Real.logb 2 (1 + Real.logb 2 ((n : ℝ) + 1)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  positivity

lemma one_point {V : Type} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 1) (G : WGraph V)
    (h : ℕ) (k p t : ℝ) (hp : 0 ≤ p) :
    IsStochRamseyEmbedding G h (PMF.pure ((discreteHST : HST V), Finset.univ)) 0 k p t := by
  have uniq : ∀ u v : V, u = v := fun u v => Fintype.card_le_one_iff.mp (by omega) u v
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx u v
    rw [PMF.support_pure, Set.mem_singleton_iff] at hx; subst hx
    rw [uniq u v, hopDist_self]; exact bot_le
  · intro x hx u _ v
    rw [PMF.support_pure, Set.mem_singleton_iff] at hx; subst hx
    rw [uniq v u]; simp [discreteHST]
  · intro v
    have : (PMF.pure ((discreteHST : HST V), (Finset.univ : Finset V))).toOuterMeasure
        {x | v ∉ x.2} = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff, PMF.support_pure, Set.disjoint_singleton_left]
      simp
    rw [this]; exact bot_le
  · intro u v
    rw [uniq u v]
    rw [tsum_eq_single ((discreteHST : HST V), (Finset.univ : Finset V))]
    · simp [discreteHST]
    · intro b hb; simp [PMF.pure_apply, hb]

theorem theorem_1' :
    ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (h : ℕ) (ε : ℝ),
        1 ≤ Fintype.card V →
        (∀ e ∈ G.graph.edgeSet, ∀ e' ∈ G.graph.edgeSet,
          G.w e ≤ (Fintype.card V : ℝ) ^ c * G.w e') →
        1 ≤ h → h ≤ Fintype.card V → 0 < ε → ε < 1 →
        ∃ D : PMF (HST V × Finset V), D.support.Finite ∧
          (∀ x ∈ D.support, x.1.leaves = Set.univ) ∧
          ∃ β : ℕ, (β : ℝ) ≤ C * polylogBound K (Fintype.card V) / ε ∧
            IsStochRamseyEmbedding G h D β (C * polylogBound K (Fintype.card V) / ε) ε
              (C * polylogBound K (Fintype.card V)) := by
  intro c
  obtain ⟨C, hC, K, hcore⟩ := core c
  refine ⟨2 * C, by positivity, K, ?_⟩
  intro V _ _ G h ε hn1 hpoly hh hhn hε hε1
  have hΛ := polylog_nonneg K (Fintype.card V)
  set Λ := polylogBound K (Fintype.card V)
  rcases Nat.lt_or_ge (Fintype.card V) 2 with hn | hn
  · -- a single vertex
    have hV : Fintype.card V = 1 := by omega
    refine ⟨PMF.pure (discreteHST, Finset.univ), by rw [PMF.support_pure]; exact Set.finite_singleton _,
      ?_, 0, by push_cast; positivity, one_point hV G h _ _ _ hε.le⟩
    intro x hx; rw [PMF.support_pure, Set.mem_singleton_iff] at hx; subst hx; rfl
  · have hn0 : (0:ℝ) < Fintype.card V := by
      have : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
      linarith
    set ε0 := 1 / (2 * (Fintype.card V : ℝ)) with hε0
    have hε0lt : ε0 < 1 := by
      rw [hε0, div_lt_one (by positivity)]
      have : (2:ℝ) ≤ Fintype.card V := by exact_mod_cast hn
      linarith
    have hε0pos : 0 < ε0 := by positivity
    by_cases hbig : ε0 ≤ ε
    · obtain ⟨D, hfin, hleaves, β, hβ, hemb⟩ := hcore V G h ε hn hpoly hh hhn hbig hε1
      have h1 : C * Λ / ε ≤ 2 * C * Λ / ε := by
        apply div_le_div_of_nonneg_right _ hε.le; nlinarith
      refine ⟨D, hfin, hleaves, β, le_trans hβ h1, embed_mono hemb h1 le_rfl (by nlinarith)⟩
    · push Not at hbig
      obtain ⟨D, hfin, hleaves, β, hβ, hemb⟩ := hcore V G h ε0 hn hpoly hh hhn le_rfl hε0lt
      have hcard : (Fintype.card V : ℝ) * ε0 ≤ 1 / 2 := by
        rw [hε0]; field_simp; norm_num
      obtain ⟨D', hsub, hemb'⟩ := embed_condition G h D β _ _ _ hemb hcard ε
      have h1 : C * Λ / ε0 ≤ 2 * C * Λ / ε := by
        calc C * Λ / ε0 ≤ C * Λ / ε :=
              div_le_div_of_nonneg_left (by positivity) hε hbig.le
          _ ≤ 2 * C * Λ / ε := by apply div_le_div_of_nonneg_right _ hε.le; nlinarith
      refine ⟨D', hfin.subset hsub, fun x hx => hleaves x (hsub x hx), β, le_trans hβ h1,
        embed_mono hemb' h1 le_rfl (by linarith)⟩

end HopRamsey.FZ


open scoped ENNReal
open ARTreeCover HopRamsey

theorem solution :
    ∀ c : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V) (h : ℕ) (ε : ℝ),
        1 ≤ Fintype.card V →
        (∀ e ∈ G.graph.edgeSet, ∀ e' ∈ G.graph.edgeSet,
          G.w e ≤ (Fintype.card V : ℝ) ^ c * G.w e') →
        1 ≤ h → h ≤ Fintype.card V → 0 < ε → ε < 1 →
        ∃ D : PMF (HST V × Finset V), D.support.Finite ∧
          (∀ x ∈ D.support, x.1.leaves = Set.univ) ∧
          ∃ β : ℕ, (β : ℝ) ≤ C * polylogBound K (Fintype.card V) / ε ∧
            IsStochRamseyEmbedding G h D β (C * polylogBound K (Fintype.card V) / ε) ε
              (C * polylogBound K (Fintype.card V)) := by
  exact HopRamsey.FZ.theorem_1'
