-- Prove2me | solution 1 for HopRamsey.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:42:28.404874+00:00
-- url     : https://prove2.me/submissions/fb6bd0ab-c88e-4956-ad1a-603e74dc6811

import Mathlib
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_CallInv
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_IsStochRamseyEmbedding
import Definitions.Def_HopRamsey_hopDist
import Definitions.Def_HopRamsey_hopStochEmbedding
import Definitions.Def_HopRamsey_singleScalePartition
import Definitions.Def_HopRamsey_truncGeom

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


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey

set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Membership in the ball `A_ℓ(x, R)` ignoring the active set. -/
def memB (P : Fig2Params) (G : WGraph V) (h : ℕ) (Δ : ℝ) (ℓ : ℕ) (x : V) (R : ℤ) (u : V) : Prop :=
  InHopBall G ((((P.k : ℤ) * ℓ + R).toNat) * h) x (P.r Δ (ℓ - 1) + (R : ℝ) * P.q Δ ℓ) u

lemma mem_ballA {P : Fig2Params} {G : WGraph V} {h : ℕ} {Δ : ℝ} {X : Finset V} {ℓ : ℕ} {x : V}
    {R : ℤ} {u : V} : u ∈ ballA P G h Δ X ℓ x R ↔ u ∈ X ∧ memB P G h Δ ℓ x R u := by
  classical
  unfold ballA memB; rw [Finset.mem_filter]

section Std
variable (P : Fig2Params) (G : WGraph V) (h : ℕ) (Δ : ℝ)

/-- Standing numeric facts used by the ball lemmas. -/
structure NumOK : Prop where
  N2 : 2 ≤ P.N
  eps0 : 0 < P.ε
  eps1 : P.ε < 1
  Phi2 : 2 ≤ P.Φ
  Δ0 : 0 ≤ Δ

variable {P G h Δ}

lemma NumOK.kpos (hP : NumOK P Δ) : 0 < P.k := P2.k_pos P hP.N2 hP.eps0 hP.eps1 hP.Phi2
lemma NumOK.Lpos (hP : NumOK P Δ) : 1 ≤ P.L := P2.L_pos P hP.N2

lemma NumOK.q_nonneg (hP : NumOK P Δ) (ℓ : ℕ) : 0 ≤ P.q Δ ℓ := by
  unfold Fig2Params.q Fig2Params.r
  have : radius P.L Δ (ℓ - 1) ≤ radius P.L Δ ℓ := P2.radius_mono P.L hP.Δ0 (by omega)
  have : (0:ℝ) ≤ P.k := by positivity
  exact div_nonneg (by linarith) this

lemma NumOK.r_nonneg (hP : NumOK P Δ) (ℓ : ℕ) : 0 ≤ P.r Δ ℓ := P2.radius_nonneg P.L hP.Δ0 ℓ

lemma memB_mono (hP : NumOK P Δ) {ℓ : ℕ} {x : V} {R R' : ℤ} (hR : R ≤ R') {u : V}
    (hu : memB P G h Δ ℓ x R u) : memB P G h Δ ℓ x R' u := by
  unfold memB InHopBall at *
  have hq := hP.q_nonneg ℓ
  have hRR : (R : ℝ) ≤ R' := by exact_mod_cast hR
  refine ⟨by nlinarith [hu.1], ?_⟩
  refine le_trans (hopDist_mono G ?_ u x) (le_trans hu.2 (ENNReal.ofReal_le_ofReal (by nlinarith)))
  exact Nat.mul_le_mul_right _ (Int.toNat_le_toNat (by omega))

lemma memB_self (hP : NumOK P Δ) {ℓ : ℕ} (x : V) {R : ℤ} (hR : 0 ≤ R) :
    memB P G h Δ ℓ x R x := by
  unfold memB InHopBall
  have hq := hP.q_nonneg ℓ
  have hr := hP.r_nonneg (ℓ - 1)
  have : (0:ℝ) ≤ R := by exact_mod_cast hR
  refine ⟨by positivity, ?_⟩
  rw [hopDist_self]; exact bot_le

lemma memB_step (hP : NumOK P Δ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {x : V} {R : ℤ} (hR : -1 ≤ R) {u v : V}
    (hu : memB P G h Δ ℓ x R u) (j : ℕ) (hj : 1 ≤ j)
    (huv : hopDist G h u v ≤ ENNReal.ofReal (j * P.q Δ ℓ)) :
    memB P G h Δ ℓ x (R + j) v := by
  unfold memB InHopBall at *
  have hq := hP.q_nonneg ℓ
  have hk := hP.kpos
  have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
  refine ⟨by push_cast; nlinarith [hu.1], ?_⟩
  have hkl : (1 : ℤ) ≤ (P.k : ℤ) * ℓ := by
    have : (1:ℤ) ≤ P.k := by exact_mod_cast hk
    have : (1:ℤ) ≤ ℓ := by exact_mod_cast hℓ
    nlinarith
  have hhops : h + ((P.k : ℤ) * ℓ + R).toNat * h ≤ ((P.k : ℤ) * ℓ + (R + j)).toNat * h := by
    rw [show h + ((P.k : ℤ) * ℓ + R).toNat * h = (((P.k : ℤ) * ℓ + R).toNat + 1) * h by ring]
    apply Nat.mul_le_mul_right
    omega
  calc hopDist G (((P.k : ℤ) * ℓ + (R + (j:ℤ))).toNat * h) v x
      ≤ hopDist G (h + ((P.k : ℤ) * ℓ + R).toNat * h) v x := hopDist_mono G hhops v x
    _ ≤ hopDist G h v u + hopDist G (((P.k : ℤ) * ℓ + R).toNat * h) u x :=
        hopDist_triangle G _ _ v u x
    _ ≤ ENNReal.ofReal (j * P.q Δ ℓ) + ENNReal.ofReal (P.r Δ (ℓ - 1) + R * P.q Δ ℓ) := by
        rw [hopDist_symm G h v u]; exact add_le_add huv hu.2
    _ = ENNReal.ofReal (P.r Δ (ℓ - 1) + ((R + (j:ℤ) : ℤ) : ℝ) * P.q Δ ℓ) := by
        rw [← ENNReal.ofReal_add (by positivity) hu.1]; congr 1; push_cast; ring

/-- Points of a ball `A_ℓ(x,R)` with `0 ≤ R < k`, `1 ≤ ℓ ≤ L` are within `r_L` of `x` with
`k(L+1)h` hops. -/
lemma memB_dist (hP : NumOK P Δ) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) {x : V} {R : ℕ}
    (hR : R < P.k) {u : V} (hu : memB P G h Δ ℓ x R u) :
    hopDist G (P.k * (P.L + 1) * h) u x ≤ ENNReal.ofReal (P.r Δ P.L) := by
  unfold memB InHopBall at hu
  have hq := hP.q_nonneg ℓ
  refine le_trans (hopDist_mono G ?_ u x) (le_trans hu.2 (ENNReal.ofReal_le_ofReal ?_))
  · apply Nat.mul_le_mul_right
    have : ((P.k : ℤ) * ℓ + (R : ℤ)).toNat = P.k * ℓ + R := by omega
    rw [this]; nlinarith
  · have h1 := P2.r_add_kq P hP.N2 hP.eps0 hP.eps1 hP.Phi2 Δ ℓ hℓ1
    have h2 : P.r Δ ℓ ≤ P.r Δ P.L := P2.radius_mono P.L hP.Δ0 hℓ
    have : (R : ℝ) ≤ P.k := by exact_mod_cast hR.le
    push_cast
    nlinarith

end Std

/-- Separation at the padding scale. -/
def Sep (P : Fig2Params) (G : WGraph V) (h : ℕ) (Δ : ℝ) (u w : V) : Prop :=
  ENNReal.ofReal (Δ / (8 * P.L * P.k)) < hopDist G h u w

/-- Invariant of the states of Algorithm 2 on input `(X, M)`. -/
structure SInv (P : Fig2Params) (G : WGraph V) (h : ℕ) (Δ : ℝ) (X M : Finset V) (s : SSPState V) :
    Prop where
  act_sub : s.active ⊆ X
  pad_sub : s.padded ⊆ s.active
  pad_M : s.padded ⊆ M
  cover : ∀ u ∈ X, u ∈ s.active ∨ ∃ c ∈ s.carved, u ∈ c.cluster
  pw : s.carved.Pairwise (fun a b => Disjoint a.cluster b.cluster)
  c_act : ∀ c ∈ s.carved, Disjoint c.cluster s.active
  c_sub : ∀ c ∈ s.carved, c.cluster ⊆ X
  c_ne : ∀ c ∈ s.carved, c.cluster.Nonempty
  c_pad : ∀ c ∈ s.carved, c.padded ⊆ c.cluster
  c_padM : ∀ c ∈ s.carved, c.padded ⊆ M
  c_ball : ∀ c ∈ s.carved, 1 ≤ c.phase ∧ c.phase ≤ P.L ∧ c.radius < P.k ∧
    ∀ u ∈ c.cluster, memB P G h Δ c.phase c.center c.radius u
  c_size : ∀ c ∈ s.carved, (c.cluster.card : ℝ) ≤ (X.card : ℝ) / (P.mu c.phase : ℝ)
  sep_act : ∀ u ∈ s.padded, ∀ w ∈ X, w ∉ s.active → Sep P G h Δ u w
  sep_c : ∀ c ∈ s.carved, ∀ u ∈ c.padded, ∀ w ∈ X, w ∉ c.cluster → Sep P G h Δ u w

variable {P : Fig2Params} {G : WGraph V} {h : ℕ} {Δ : ℝ}

lemma SInv.init {X M : Finset V} (hM : M ⊆ X) : SInv P G h Δ X M ⟨X, M, []⟩ where
  act_sub := le_rfl
  pad_sub := hM
  pad_M := le_rfl
  cover := fun u hu => Or.inl hu
  pw := List.Pairwise.nil
  c_act := by simp
  c_sub := by simp
  c_ne := by simp
  c_pad := by simp
  c_padM := by simp
  c_ball := by simp
  c_size := by simp
  sep_act := fun u _ w hw hw' => absurd hw hw'
  sep_c := by simp

lemma not_sep_le (hP : NumOK P Δ) {u w : V} (h' : ¬ Sep P G h Δ u w) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    hopDist G h u w ≤ ENNReal.ofReal (((1 : ℕ) : ℝ) * P.q Δ ℓ) := by
  unfold Sep at h'; rw [not_lt] at h'
  refine le_trans h' (ENNReal.ofReal_le_ofReal ?_)
  simpa using P2.q_ge P hP.N2 hP.eps0 hP.eps1 hP.Phi2 Δ hP.Δ0 ℓ hℓ

lemma SInv.step (hP : NumOK P Δ) {X M : Finset V} {s : SSPState V} (hI : SInv P G h Δ X M s)
    {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) {x : V}
    (hx : Eligible P G h Δ X.card s.active ℓ x) {R : ℕ} (hR : R < P.k) :
    SInv P G h Δ X M (carveStep P G h Δ ℓ s x R) := by
  obtain ⟨hxa, -, -, hxk⟩ := hx
  set A := ballA P G h Δ s.active ℓ x (R : ℤ) with hA
  set A1 := ballA P G h Δ s.active ℓ x ((R : ℤ) + 1) with hA1
  set A0 := ballA P G h Δ s.active ℓ x ((R : ℤ) - 1) with hA0
  have hAsub : A ⊆ s.active := fun u hu => (mem_ballA.mp hu).1
  have hAA1 : A ⊆ A1 := fun u hu => by
    rw [mem_ballA] at hu ⊢; exact ⟨hu.1, memB_mono hP (by omega) hu.2⟩
  -- key separation facts
  have keyA : ∀ u ∈ A0, ∀ w ∈ s.active, ¬ Sep P G h Δ u w → w ∈ A := by
    intro u hu w hw hns
    rw [mem_ballA] at hu ⊢
    refine ⟨hw, ?_⟩
    have := memB_step hP hℓ1 (by omega) hu.2 1 le_rfl (not_sep_le hP hns ℓ hℓ1)
    simpa using this
  have keyA1 : ∀ w ∈ A, ∀ u ∈ s.active, ¬ Sep P G h Δ u w → u ∈ A1 := by
    intro w hw u hu hns
    rw [mem_ballA] at hw ⊢
    refine ⟨hu, ?_⟩
    have hns' : hopDist G h w u ≤ ENNReal.ofReal (((1 : ℕ) : ℝ) * P.q Δ ℓ) := by
      rw [hopDist_symm]; exact not_sep_le hP hns ℓ hℓ1
    have := memB_step hP hℓ1 (by omega) hw.2 1 le_rfl hns'
    simpa using this
  have hcard : (A.card : ℝ) ≤ (X.card : ℝ) / (P.mu ℓ : ℝ) := by
    refine le_trans ?_ hxk
    exact_mod_cast Finset.card_le_card (fun u hu => by
      rw [mem_ballA] at hu ⊢; exact ⟨hu.1, memB_mono hP (by exact_mod_cast hR.le) hu.2⟩)
  have hxA : x ∈ A := by rw [mem_ballA]; exact ⟨hxa, memB_self hP x (by omega)⟩
  refine
    { act_sub := fun u hu => hI.act_sub (Finset.mem_sdiff.mp hu).1
      pad_sub := ?_
      pad_M := fun u hu => hI.pad_M (Finset.mem_sdiff.mp hu).1
      cover := ?_
      pw := ?_
      c_act := ?_
      c_sub := ?_
      c_ne := ?_
      c_pad := ?_
      c_padM := ?_
      c_ball := ?_
      c_size := ?_
      sep_act := ?_
      sep_c := ?_ }
  · intro u hu
    simp only [carveStep, Finset.mem_sdiff] at hu ⊢
    exact ⟨hI.pad_sub hu.1, fun h' => hu.2 (hAA1 h')⟩
  · intro u hu
    rcases hI.cover u hu with h' | ⟨c, hc, huc⟩
    · by_cases huA : u ∈ A
      · right; exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), huA⟩
      · left; simp only [carveStep, Finset.mem_sdiff]; exact ⟨h', huA⟩
    · right; exact ⟨c, List.mem_append_left _ hc, huc⟩
  · simp only [carveStep]
    rw [List.pairwise_append]
    refine ⟨hI.pw, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb; subst hb
    exact Finset.disjoint_of_subset_right hAsub (hI.c_act a ha)
  · intro c hc
    simp only [carveStep] at hc ⊢
    rcases List.mem_append.mp hc with hc | hc
    · exact Finset.disjoint_of_subset_right Finset.sdiff_subset (hI.c_act c hc)
    · rw [List.mem_singleton] at hc; subst hc; exact Finset.disjoint_sdiff
  · intro c hc
    simp only [carveStep] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hI.c_sub c hc
    · rw [List.mem_singleton] at hc; subst hc; exact hAsub.trans hI.act_sub
  · intro c hc
    simp only [carveStep] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hI.c_ne c hc
    · rw [List.mem_singleton] at hc; subst hc; exact ⟨x, hxA⟩
  · intro c hc
    simp only [carveStep] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hI.c_pad c hc
    · rw [List.mem_singleton] at hc; subst hc
      intro u hu
      rw [Finset.mem_inter] at hu
      rw [mem_ballA] at hu ⊢
      exact ⟨hu.1.1, memB_mono hP (by omega) hu.1.2⟩
  · intro c hc
    simp only [carveStep] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hI.c_padM c hc
    · rw [List.mem_singleton] at hc; subst hc
      exact fun u hu => hI.pad_M (Finset.mem_inter.mp hu).2
  · intro c hc
    simp only [carveStep] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hI.c_ball c hc
    · rw [List.mem_singleton] at hc; subst hc
      exact ⟨hℓ1, hℓ, hR, fun u hu => (mem_ballA.mp hu).2⟩
  · intro c hc
    simp only [carveStep] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hI.c_size c hc
    · rw [List.mem_singleton] at hc; subst hc; exact hcard
  · intro u hu w hwX hw
    simp only [carveStep, Finset.mem_sdiff, not_and, not_not] at hu hw
    by_cases hwa : w ∈ s.active
    · by_contra hns
      exact hu.2 (keyA1 w (hw hwa) u (hI.pad_sub hu.1) hns)
    · exact hI.sep_act u hu.1 w hwX hwa
  · intro c hc
    simp only [carveStep] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hI.sep_c c hc
    · rw [List.mem_singleton] at hc; subst hc
      intro u hu w hwX hw
      rw [Finset.mem_inter] at hu
      by_cases hwa : w ∈ s.active
      · by_contra hns
        exact hw (keyA u hu.1 w hwa hns)
      · exact hI.sep_act u hu.2 w hwX hwa

end HopRamsey.FZ

namespace HopRamsey.FZ
open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable {P : Fig2Params} {G : WGraph V} {h : ℕ} {Δ : ℝ}

lemma truncGeom_lt (hP : NumOK P Δ) {ℓ : ℕ} (hℓ : ℓ ≤ P.L) :
    ∀ R ∈ (truncGeom (P.p ℓ) P.k).support, R < P.k :=
  truncGeom_support hP.kpos (P2.p_pos P hP.N2 hP.eps0 hP.eps1 hP.Phi2 ℓ hℓ)

lemma center_mem (hP : NumOK P Δ) {s : SSPState V} {ℓ : ℕ} {x : V} {X : Finset V}
    (hx : Eligible P G h Δ X.card s.active ℓ x) (R : ℕ) :
    x ∈ ballA P G h Δ s.active ℓ x (R : ℤ) := by
  rw [mem_ballA]; exact ⟨hx.1, memB_self hP x (by omega)⟩

lemma carve_active_lt (hP : NumOK P Δ) {s : SSPState V} {ℓ : ℕ} {x : V} {X : Finset V}
    (hx : Eligible P G h Δ X.card s.active ℓ x) (R : ℕ) :
    (carveStep P G h Δ ℓ s x R).active.card < s.active.card := by
  simp only [carveStep]
  apply Finset.card_lt_card
  refine ⟨Finset.sdiff_subset, fun hsub => ?_⟩
  have := hsub hx.1
  rw [Finset.mem_sdiff] at this
  exact this.2 (center_mem hP hx R)

lemma phaseLoop_inv (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) :
    ∀ (fuel : ℕ) (s : SSPState V), SInv P G h Δ X M s →
      ∀ s' ∈ (phaseLoop P G h rule X M Δ ℓ fuel s).support,
        SInv P G h Δ X M s' ∧ s'.active ⊆ s.active ∧
        (s.active.card < fuel → ¬ ∃ x, Eligible P G h Δ X.card s'.active ℓ x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs s' hs'
    simp only [phaseLoop, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'
    exact ⟨hs, le_rfl, fun h' => absurd h' (Nat.not_lt_zero _)⟩
  | succ fuel ih =>
    intro s hs s' hs'
    rw [phaseLoop] at hs'
    split_ifs at hs' with hel
    · rw [PMF.mem_support_bind_iff] at hs'
      obtain ⟨R, hR, hs'⟩ := hs'
      have hx := hrule X M Δ ℓ s hel
      have hRk := truncGeom_lt hP hℓ R hR
      have hI' := SInv.step hP hs hℓ1 hℓ hx hRk
      obtain ⟨h1, h2, h3⟩ := ih _ hI' s' hs'
      have hlt := carve_active_lt hP hx R
      refine ⟨h1, h2.trans (by simp only [carveStep]; exact Finset.sdiff_subset), fun hc => h3 ?_⟩
      omega
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      exact ⟨hs, le_rfl, fun _ => hel⟩

lemma phasesFrom_inv (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} :
    ∀ (ℓ : ℕ), ℓ ≤ P.L → ∀ (s : SSPState V), SInv P G h Δ X M s →
      ∀ s' ∈ (phasesFrom P G h rule X M Δ ℓ s).support,
        SInv P G h Δ X M s' ∧ s'.active ⊆ s.active := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _ s hs s' hs'
    simp only [phasesFrom, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'; exact ⟨hs, le_rfl⟩
  | succ j ih =>
    intro hj s hs s' hs'
    rw [phasesFrom, PMF.mem_support_bind_iff] at hs'
    obtain ⟨S, hS, hs'⟩ := hs'
    obtain ⟨h1, h2, -⟩ := phaseLoop_inv hP hrule (by omega) hj _ s hs S hS
    obtain ⟨h3, h4⟩ := ih (by omega) S h1 s' hs'
    exact ⟨h3, h4.trans h2⟩

lemma sspRun_inv (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} (hM : M ⊆ X) :
    ∀ s ∈ (sspRun P G h rule X M Δ).support, SInv P G h Δ X M s :=
  fun s hs => (phasesFrom_inv hP hrule P.L le_rfl _ (SInv.init hM) s hs).1

lemma memB_shift (hP : NumOK P Δ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {z u : V}
    (hu : memB P G h Δ ℓ z (P.k : ℤ) u) : memB P G h Δ (ℓ + 1) z 0 u := by
  unfold memB at *
  have h1 := P2.r_add_kq P hP.N2 hP.eps0 hP.eps1 hP.Phi2 Δ ℓ hℓ
  have e1 : ((P.k : ℤ) * ((ℓ + 1 : ℕ) : ℤ) + 0).toNat = ((P.k : ℤ) * ℓ + P.k).toNat := by
    congr 1
  rw [e1]
  simp only [Nat.add_sub_cancel, Int.cast_zero, zero_mul, add_zero]
  convert hu using 2
  push_cast; linarith

lemma memB_dist_k (hP : NumOK P Δ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {z u : V}
    (hu : memB P G h Δ ℓ z (P.k : ℤ) u) :
    hopDist G (P.k * (ℓ + 1) * h) u z ≤ ENNReal.ofReal (P.r Δ ℓ) := by
  unfold memB InHopBall at hu
  have h1 := P2.r_add_kq P hP.N2 hP.eps0 hP.eps1 hP.Phi2 Δ ℓ hℓ
  have e1 : ((P.k : ℤ) * ℓ + P.k).toNat * h = P.k * (ℓ + 1) * h := by
    congr 1
  rw [e1] at hu
  refine le_trans hu.2 (le_of_eq ?_)
  congr 1

/-- Claim 1 core: after the phases `ℓ, ℓ-1, …, 1`, every surviving vertex `z` has a large
`A_ℓ(z, k)` ball at the end of phase `ℓ`. -/
lemma phasesFrom_dense (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} (hXN : X.card ≤ P.N) :
    ∀ (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ P.L → ∀ (s : SSPState V), SInv P G h Δ X M s →
      ∀ sf ∈ (phasesFrom P G h rule X M Δ ℓ s).support,
        ∃ S ∈ (phaseLoop P G h rule X M Δ ℓ (X.card + 1) s).support,
          sf.active ⊆ S.active ∧ S.active ⊆ X ∧
          ∀ z ∈ sf.active, (X.card : ℝ) / (P.mu ℓ : ℝ) <
            ((ballA P G h Δ S.active ℓ z (P.k : ℤ)).card : ℝ) := by
  intro ℓ
  induction ℓ with
  | zero => intro h0; omega
  | succ j ih =>
    intro _ hj s hs sf hsf
    rw [phasesFrom, PMF.mem_support_bind_iff] at hsf
    obtain ⟨S, hS, hsf⟩ := hsf
    obtain ⟨hSI, hSs, hSne⟩ := phaseLoop_inv hP hrule (by omega) hj _ s hs S hS
    have hne := hSne (by have := Finset.card_le_card (hs.act_sub); omega)
    have hsfS : sf.active ⊆ S.active := (phasesFrom_inv hP hrule j (by omega) S hSI sf hsf).2
    refine ⟨S, hS, hsfS, hSI.act_sub, fun z hz => ?_⟩
    have hzS := hsfS hz
    -- lower bound for |A_{j+1}(z,0)|
    have hlow : (X.card : ℝ) / (P.mu (j + 1 - 1) : ℝ) ≤
        ((ballA P G h Δ S.active (j + 1) z 0).card : ℝ) := by
      simp only [Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        have hmu := P2.mu_zero_gt P hP.N2
        have h1 : (1 : ℝ) ≤ ((ballA P G h Δ S.active (0 + 1) z 0).card : ℝ) := by
          have : z ∈ ballA P G h Δ S.active (0 + 1) z 0 := by
            rw [mem_ballA]; exact ⟨hzS, memB_self hP z le_rfl⟩
          exact_mod_cast Finset.card_pos.mpr ⟨z, this⟩
        refine le_trans ?_ h1
        rw [div_le_one (P2.mu_pos P 0)]
        have : (X.card : ℝ) ≤ P.N := by exact_mod_cast hXN
        linarith
      · obtain ⟨S', hS', hsfS', -, hbig⟩ := ih hj0 (by omega) S hSI sf hsf
        refine le_trans (hbig z hz).le ?_
        exact_mod_cast Finset.card_le_card (fun u hu => by
          rw [mem_ballA] at hu ⊢
          obtain ⟨-, hS'S, -⟩ := phaseLoop_inv hP hrule hj0 (by omega) _ S hSI S' hS'
          exact ⟨hS'S hu.1, memB_shift hP hj0 hu.2⟩)
    by_contra hcon
    push Not at hcon
    apply hne
    refine ⟨z, hzS, hlow, ?_, hcon⟩
    exact Finset.card_le_card (fun u hu => by
      rw [mem_ballA] at hu ⊢; exact ⟨hu.1, memB_mono hP (by omega) hu.2⟩)

/-- Claim 1: the last cluster has `diam^{(2k(L+1)h)} ≤ 2 r_L`. -/
lemma sspRun_last_diam (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} (hM : M ⊆ X) (hXN : X.card ≤ P.N) :
    ∀ sf ∈ (sspRun P G h rule X M Δ).support, ∀ z ∈ sf.active, ∀ z' ∈ sf.active,
      hopDist G (2 * P.k * (P.L + 1) * h) z z' ≤ ENNReal.ofReal (2 * P.r Δ P.L) := by
  intro sf hsf z hz z' hz'
  obtain ⟨S, -, hsfS, hSX, hbig⟩ :=
    phasesFrom_dense hP hrule hXN P.L hP.Lpos le_rfl _ (SInv.init hM) sf hsf
  have hb1 := hbig z hz
  have hb2 := hbig z' hz'
  rw [P2.mu_L] at hb1 hb2
  set B1 := ballA P G h Δ S.active P.L z (P.k : ℤ)
  set B2 := ballA P G h Δ S.active P.L z' (P.k : ℤ)
  have hsub1 : B1 ⊆ X := fun u hu => hSX (mem_ballA.mp hu).1
  have hsub2 : B2 ⊆ X := fun u hu => hSX (mem_ballA.mp hu).1
  have hint : (B1 ∩ B2).Nonempty := by
    by_contra hem
    rw [Finset.not_nonempty_iff_eq_empty] at hem
    have hU := Finset.card_union_add_card_inter B1 B2
    rw [hem, Finset.card_empty, add_zero] at hU
    have : (B1 ∪ B2).card ≤ X.card := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
    have : ((B1.card + B2.card : ℕ) : ℝ) ≤ X.card := by exact_mod_cast hU ▸ this
    push_cast at this
    linarith
  obtain ⟨w, hw⟩ := hint
  rw [Finset.mem_inter, mem_ballA, mem_ballA] at hw
  have d1 := memB_dist_k hP hP.Lpos hw.1.2
  have d2 := memB_dist_k hP hP.Lpos hw.2.2
  have hr := hP.r_nonneg P.L
  calc hopDist G (2 * P.k * (P.L + 1) * h) z z'
      = hopDist G (P.k * (P.L + 1) * h + P.k * (P.L + 1) * h) z z' := by congr 1; ring
    _ ≤ hopDist G (P.k * (P.L + 1) * h) z w + hopDist G (P.k * (P.L + 1) * h) w z' :=
        hopDist_triangle G _ _ z w z'
    _ ≤ ENNReal.ofReal (P.r Δ P.L) + ENNReal.ofReal (P.r Δ P.L) := by
        rw [hopDist_symm G _ z w]; exact add_le_add d1 d2
    _ = ENNReal.ofReal (2 * P.r Δ P.L) := by rw [← ENNReal.ofReal_add hr hr]; ring_nf


/-- Properties of an output of `Single-Scale-Partition` on `(X, M)`. -/
structure OutOK (P : Fig2Params) (G : WGraph V) (h : ℕ) (Δ : ℝ) (X M : Finset V)
    (C : List (Finset V × Finset V)) : Prop where
  sub : ∀ c ∈ C, c.1 ⊆ X
  ne : ∀ c ∈ C, c.1.Nonempty
  pad : ∀ c ∈ C, c.2 ⊆ c.1
  padM : ∀ c ∈ C, c.2 ⊆ M
  pw : C.Pairwise (fun a b => Disjoint a.1 b.1)
  cover : ∀ u ∈ X, ∃ c ∈ C, u ∈ c.1
  diam : ∀ c ∈ C, ∀ u ∈ c.1, ∀ w ∈ c.1,
    hopDist G (2 * P.k * (P.L + 1) * h) u w ≤ ENNReal.ofReal (Δ / 2)
  sep : ∀ c ∈ C, ∀ u ∈ c.2, ∀ w ∈ X, w ∉ c.1 → Sep P G h Δ u w

lemma carved_diam (hP : NumOK P Δ) {X M : Finset V} {s : SSPState V} (hI : SInv P G h Δ X M s)
    {c : Carve V} (hc : c ∈ s.carved) {u w : V} (hu : u ∈ c.cluster) (hw : w ∈ c.cluster) :
    hopDist G (2 * P.k * (P.L + 1) * h) u w ≤ ENNReal.ofReal (2 * P.r Δ P.L) := by
  obtain ⟨h1, h2, h3, h4⟩ := hI.c_ball c hc
  have d1 := memB_dist hP h1 h2 h3 (h4 u hu)
  have d2 := memB_dist hP h1 h2 h3 (h4 w hw)
  have hr := hP.r_nonneg P.L
  calc hopDist G (2 * P.k * (P.L + 1) * h) u w
      = hopDist G (P.k * (P.L + 1) * h + P.k * (P.L + 1) * h) u w := by congr 1; ring
    _ ≤ hopDist G (P.k * (P.L + 1) * h) u c.center + hopDist G (P.k * (P.L + 1) * h) c.center w :=
        hopDist_triangle G _ _ u c.center w
    _ ≤ ENNReal.ofReal (P.r Δ P.L) + ENNReal.ofReal (P.r Δ P.L) := by
        rw [hopDist_symm G _ c.center w]; exact add_le_add d1 d2
    _ = ENNReal.ofReal (2 * P.r Δ P.L) := by rw [← ENNReal.ofReal_add hr hr]; ring_nf

lemma two_rL_le (hP : NumOK P Δ) : 2 * P.r Δ P.L ≤ Δ / 2 := by
  have := P2.radius_L_le P.L hP.Lpos hP.Δ0
  unfold Fig2Params.r; linarith

lemma ssp_outOK (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} (hM : M ⊆ X) (hXN : X.card ≤ P.N) :
    ∀ C ∈ (singleScalePartition P G h rule X M Δ).support, OutOK P G h Δ X M C := by
  intro C hC
  unfold singleScalePartition at hC
  rw [PMF.support_map] at hC
  obtain ⟨sf, hsf, rfl⟩ := hC
  have hI := sspRun_inv hP hrule hM sf hsf
  have hlast := sspRun_last_diam hP hrule hM hXN sf hsf
  have h2r := two_rL_le hP
  unfold sspOutput
  -- membership in the output list
  have memo : ∀ c ∈ (sf.carved.map (fun c => (c.cluster, c.padded)) ++
      (if sf.active.Nonempty then [(sf.active, sf.padded)] else [])),
      (∃ d ∈ sf.carved, c = (d.cluster, d.padded)) ∨
        (c = (sf.active, sf.padded) ∧ sf.active.Nonempty) := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · left; obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc; exact ⟨d, hd, rfl⟩
    · right; split_ifs at hc with hne
      · exact ⟨List.mem_singleton.mp hc, hne⟩
      · simp at hc
  refine
    { sub := ?_, ne := ?_, pad := ?_, padM := ?_, pw := ?_, cover := ?_, diam := ?_, sep := ?_ }
  · intro c hc
    rcases memo c hc with ⟨d, hd, rfl⟩ | ⟨rfl, -⟩
    · exact hI.c_sub d hd
    · exact hI.act_sub
  · intro c hc
    rcases memo c hc with ⟨d, hd, rfl⟩ | ⟨rfl, hne⟩
    · exact hI.c_ne d hd
    · exact hne
  · intro c hc
    rcases memo c hc with ⟨d, hd, rfl⟩ | ⟨rfl, -⟩
    · exact hI.c_pad d hd
    · exact hI.pad_sub
  · intro c hc
    rcases memo c hc with ⟨d, hd, rfl⟩ | ⟨rfl, -⟩
    · exact hI.c_padM d hd
    · exact hI.pad_M
  · rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]; exact hI.pw
    · split_ifs <;> simp
    · intro a ha b hb
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
      split_ifs at hb
      · rw [List.mem_singleton] at hb; subst hb; exact hI.c_act d hd
      · simp at hb
  · intro u hu
    rcases hI.cover u hu with h' | ⟨d, hd, hud⟩
    · refine ⟨(sf.active, sf.padded), List.mem_append_right _ ?_, h'⟩
      rw [if_pos ⟨u, h'⟩]; exact List.mem_singleton_self _
    · exact ⟨(d.cluster, d.padded), List.mem_append_left _ (List.mem_map_of_mem hd), hud⟩
  · intro c hc u hu w hw
    rcases memo c hc with ⟨d, hd, rfl⟩ | ⟨rfl, -⟩
    · exact le_trans (carved_diam hP hI hd hu hw) (ENNReal.ofReal_le_ofReal h2r)
    · exact le_trans (hlast u hu w hw) (ENNReal.ofReal_le_ofReal h2r)
  · intro c hc u hu w hwX hw
    rcases memo c hc with ⟨d, hd, rfl⟩ | ⟨rfl, -⟩
    · exact hI.sep_c d hd u hu w hwX hw
    · exact hI.sep_act u hu w hwX hw

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable {P : Fig2Params} {G : WGraph V} {h : ℕ} {Δ : ℝ}

lemma phaseLoop_ex (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) (Pot : SSPState V → ℝ≥0∞)
    (hstep : ∀ s, SInv P G h Δ X M s → (∃ x, Eligible P G h Δ X.card s.active ℓ x) →
      ex (truncGeom (P.p ℓ) P.k) (fun R => Pot (carveStep P G h Δ ℓ s (rule X M Δ ℓ s) R))
        ≤ Pot s) :
    ∀ (fuel : ℕ) (s : SSPState V), SInv P G h Δ X M s →
      ex (phaseLoop P G h rule X M Δ ℓ fuel s) Pot ≤ Pot s := by
  intro fuel
  induction fuel with
  | zero => intro s _; simp [phaseLoop, ex_pure]
  | succ fuel ih =>
    intro s hs
    rw [phaseLoop]
    split_ifs with hel
    · rw [ex_bind]
      refine le_trans (ex_mono _ (fun R hR => ih _ ?_)) (hstep s hs hel)
      exact SInv.step hP hs hℓ1 hℓ (hrule X M Δ ℓ s hel) (truncGeom_lt hP hℓ R hR)
    · rw [ex_pure]

lemma phasesFrom_ex (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} (Pot : ℕ → SSPState V → ℝ≥0∞)
    (hstep : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.L → ∀ s, SInv P G h Δ X M s →
      (∃ x, Eligible P G h Δ X.card s.active ℓ x) →
      ex (truncGeom (P.p ℓ) P.k) (fun R => Pot ℓ (carveStep P G h Δ ℓ s (rule X M Δ ℓ s) R))
        ≤ Pot ℓ s)
    (hdown : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.L → ∀ s, SInv P G h Δ X M s → Pot (ℓ - 1) s ≤ Pot ℓ s) :
    ∀ ℓ, ℓ ≤ P.L → ∀ s, SInv P G h Δ X M s →
      ex (phasesFrom P G h rule X M Δ ℓ s) (Pot 0) ≤ Pot ℓ s := by
  intro ℓ
  induction ℓ with
  | zero => intro _ s _; simp [phasesFrom, ex_pure]
  | succ j ih =>
    intro hj s hs
    rw [phasesFrom, ex_bind]
    calc ex (phaseLoop P G h rule X M Δ (j + 1) (X.card + 1) s)
          (fun a => ex (phasesFrom P G h rule X M Δ j a) (Pot 0))
        ≤ ex (phaseLoop P G h rule X M Δ (j + 1) (X.card + 1) s) (Pot (j + 1)) := by
          apply ex_mono
          intro S hS
          have hSI := (phaseLoop_inv hP hrule (by omega) hj _ s hs S hS).1
          exact le_trans (ih (by omega) S hSI) (by simpa using hdown (j + 1) (by omega) hj S hSI)
      _ ≤ Pot (j + 1) s :=
          phaseLoop_ex hP hrule (by omega) hj (Pot (j + 1)) (hstep (j + 1) (by omega) hj) _ s hs

/-- Potential method for Algorithm 2. -/
lemma ssp_ex_le (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} (hM : M ⊆ X) (Pot : ℕ → SSPState V → ℝ≥0∞)
    (F : List (Finset V × Finset V) → ℝ≥0∞)
    (hstep : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.L → ∀ s, SInv P G h Δ X M s →
      (∃ x, Eligible P G h Δ X.card s.active ℓ x) →
      ex (truncGeom (P.p ℓ) P.k) (fun R => Pot ℓ (carveStep P G h Δ ℓ s (rule X M Δ ℓ s) R))
        ≤ Pot ℓ s)
    (hdown : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.L → ∀ s, SInv P G h Δ X M s → Pot (ℓ - 1) s ≤ Pot ℓ s)
    (hfin : ∀ s, SInv P G h Δ X M s → F (sspOutput s) ≤ Pot 0 s) :
    ex (singleScalePartition P G h rule X M Δ) F ≤ Pot P.L ⟨X, M, []⟩ := by
  unfold singleScalePartition sspRun
  rw [ex_map]
  refine le_trans (ex_mono _ (fun s hs => hfin s ?_)) ?_
  · exact (phasesFrom_inv hP hrule P.L le_rfl _ (SInv.init hM) s hs).1
  · exact phasesFrom_ex hP hrule Pot hstep hdown P.L le_rfl _ (SInv.init hM)

/-! ### The abstract one-ball inequality -/

lemma gw_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m r : ℕ} (hr : m ≤ r) :
    gw p r ≤ p * (1 - p) ^ m := by
  unfold gw
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ hp0
  exact pow_le_pow_of_le_one (by linarith) (by linarith) hr

lemma sum_gw_Ico {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m k : ℕ) :
    ∑ r ∈ Finset.Ico m k, gw p r ≤ (1 - p) ^ m := by
  rcases le_or_gt m k with hmk | hmk
  · rw [Finset.sum_Ico_eq_sub _ hmk, sum_gw, sum_gw]
    have : 0 ≤ (1 - p) ^ k := pow_nonneg (by linarith) _
    linarith
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    exact pow_nonneg (by linarith) _

lemma step_abstract {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) (val : ℕ → ℝ)
    (A Tv : ℝ) (hA : 0 ≤ A) (hTA : Tv ≤ A) (m : ℕ) (hun : ∀ r < m, val r ≤ A)
    (htouch : ∑ r ∈ Finset.Ico m k, gw p r * val r ≤ (1 - p) ^ m * Tv) :
    ∑ r ∈ Finset.range k, gw p r * val r ≤ A := by
  have hq0 : 0 ≤ 1 - p := by linarith
  rcases le_or_gt m k with hmk | hmk
  · rw [← Finset.sum_range_add_sum_Ico _ hmk]
    have h1 : ∑ r ∈ Finset.range m, gw p r * val r ≤ ∑ r ∈ Finset.range m, gw p r * A :=
      Finset.sum_le_sum fun r hr =>
        mul_le_mul_of_nonneg_left (hun r (Finset.mem_range.mp hr)) (gw_nonneg hp0 hp1 r)
    rw [← Finset.sum_mul, sum_gw] at h1
    have h2 : (1 - p) ^ m * Tv ≤ (1 - p) ^ m * A :=
      mul_le_mul_of_nonneg_left hTA (pow_nonneg hq0 _)
    nlinarith
  · have h1 : ∑ r ∈ Finset.range k, gw p r * val r ≤ ∑ r ∈ Finset.range k, gw p r * A :=
      Finset.sum_le_sum fun r hr =>
        mul_le_mul_of_nonneg_left (hun r (by have := Finset.mem_range.mp hr; omega))
          (gw_nonneg hp0 hp1 r)
    rw [← Finset.sum_mul, sum_gw] at h1
    have : 0 ≤ (1 - p) ^ k := pow_nonneg hq0 _
    nlinarith

/-- Converting the truncated-geometric expectation of a real potential. -/
lemma ex_truncGeom_le {p : ℝ} {k : ℕ} (hk : 0 < k) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hθ : (1 - p) ^ k < 1) (val : ℕ → ℝ) (hval : ∀ r < k, 0 ≤ val r) (B : ℝ)
    (hB : ∑ r ∈ Finset.range k, gw p r * val r ≤ B * (1 - (1 - p) ^ k)) :
    ex (truncGeom p k) (fun r => ENNReal.ofReal (val r)) ≤ ENNReal.ofReal B := by
  rw [ex_truncGeom hk hp0 hp1]
  have hZ : 0 < 1 - (1 - p) ^ k := by linarith
  rw [ENNReal.div_le_iff (by simpa using hZ) ENNReal.ofReal_ne_top]
  rw [← ENNReal.ofReal_mul' hZ.le]
  calc ∑ r ∈ Finset.range k, ENNReal.ofReal (gw p r) * ENNReal.ofReal (val r)
      = ENNReal.ofReal (∑ r ∈ Finset.range k, gw p r * val r) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun r hr => mul_nonneg (gw_nonneg hp0.le hp1 r)
          (hval r (Finset.mem_range.mp hr)))]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [ENNReal.ofReal_mul (gw_nonneg hp0.le hp1 r)]
    _ ≤ ENNReal.ofReal (B * (1 - (1 - p) ^ k)) := ENNReal.ofReal_le_ofReal hB


/-- The first radius at which a ball touches `v` (`v ∈ A(R+1)`). -/
lemma touch_index (hP : NumOK P Δ) (ℓ : ℕ) (x v : V) :
    ∃ m : ℕ, (∀ r < m, ¬ memB P G h Δ ℓ x ((r : ℤ) + 1) v) ∧
      (∀ r, m ≤ r → r < P.k → memB P G h Δ ℓ x ((r : ℤ) + 1) v) ∧
      (∀ r, m + 2 ≤ r → r < P.k → memB P G h Δ ℓ x ((r : ℤ) - 1) v) := by
  classical
  by_cases hex : ∃ r : ℕ, memB P G h Δ ℓ x ((r : ℤ) + 1) v
  · refine ⟨Nat.find hex, fun r hr => Nat.find_min hex hr, fun r hr _ => ?_, fun r hr _ => ?_⟩
    · exact memB_mono hP (by omega) (Nat.find_spec hex)
    · exact memB_mono hP (by omega) (Nat.find_spec hex)
  · push Not at hex
    exact ⟨P.k, fun r _ => hex r, fun r hr hr' => absurd hr' (by omega),
      fun r hr hr' => absurd hr' (by omega)⟩

end HopRamsey.FZ


namespace HopRamsey.FZ

open HopRamsey

namespace EA

variable (P : Fig2Params) (Δ : ℝ) (n : ℕ)

noncomputable def a : ℝ := 4 / P.k
noncomputable def B : ℝ := (1 + 2 * P.delta) ^ (Real.logb 2 Δ - 1)
noncomputable def lam : ℝ := Real.log (2 / P.delta)
noncomputable def Lam0 : ℝ := Real.log n + lam P * (Real.logb 2 Δ - 1)
noncomputable def T : ℝ := a P * B P Δ * (Lam0 P Δ n + lam P)

set_option linter.unusedSectionVars false
variable (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ) (hΔ : 2 ≤ Δ)
include hN hε hε1 hΦ hΔ

lemma logΔ_ge : 1 ≤ Real.logb 2 Δ := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hΔ

lemma a_pos : 0 < a P := by
  unfold a; have : (0:ℝ) < P.k := by exact_mod_cast P2.k_pos P hN hε hε1 hΦ
  positivity

lemma B_ge : 1 ≤ B P Δ := by
  unfold B
  have := P2.delta_pos P hN
  exact Real.one_le_rpow (by linarith) (by linarith [logΔ_ge P Δ hN hε hε1 hΦ hΔ])

lemma lam_nonneg : 0 ≤ lam P := P2.log2_delta_nonneg P hN hε hε1 hΦ

lemma logb_half : Real.logb 2 (Δ / 2) = Real.logb 2 Δ - 1 := by
  rw [Real.logb_div (by linarith) (by norm_num), Real.logb_self_eq_one (by norm_num)]

lemma f_half (m : ℕ) : P.f m (Δ / 2) = a P * B P Δ * (Real.log m + lam P * (Real.logb 2 Δ - 1)) := by
  unfold Fig2Params.f a B lam
  rw [logb_half P Δ hN hε hε1 hΦ hΔ]

lemma f_full : P.f n Δ = T P Δ n * (1 + 2 * P.delta) := by
  unfold Fig2Params.f T a B Lam0 lam
  have hd := P2.delta_pos P hN
  rw [Real.rpow_sub_one (by linarith)]
  field_simp
  ring

lemma T_nonneg (hn : 1 ≤ n) : 0 ≤ T P Δ n := by
  unfold T Lam0
  have := a_pos P Δ hN hε hε1 hΦ hΔ
  have := B_ge P Δ hN hε hε1 hΦ hΔ
  have := lam_nonneg P Δ hN hε hε1 hΦ hΔ
  have := logΔ_ge P Δ hN hε hε1 hΦ hΔ
  have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have : 0 ≤ lam P * (Real.logb 2 Δ - 1) := mul_nonneg (by assumption) (by linarith)
  positivity

lemma f_half_nonneg (m : ℕ) (hm : 1 ≤ m) : 0 ≤ P.f m (Δ / 2) := by
  rw [f_half P Δ hN hε hε1 hΦ hΔ]
  have := a_pos P Δ hN hε hε1 hΦ hΔ
  have := B_ge P Δ hN hε hε1 hΦ hΔ
  have := lam_nonneg P Δ hN hε hε1 hΦ hΔ
  have := logΔ_ge P Δ hN hε hε1 hΦ hΔ
  have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have : 0 ≤ lam P * (Real.logb 2 Δ - 1) := mul_nonneg (by assumption) (by linarith)
  positivity

lemma f_half_le_T (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) : P.f m (Δ / 2) ≤ T P Δ n := by
  rw [f_half P Δ hN hε hε1 hΦ hΔ]
  unfold T Lam0
  have := a_pos P Δ hN hε hε1 hΦ hΔ
  have := B_ge P Δ hN hε hε1 hΦ hΔ
  have := lam_nonneg P Δ hN hε hε1 hΦ hΔ
  have : Real.log m ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmn)
  have hab : 0 ≤ a P * B P Δ := by positivity
  nlinarith

/-- The captured value: a cluster of size `m ≤ n/µ_ℓ`. -/
noncomputable def S (ℓ : ℕ) : ℝ := a P * B P Δ * (Lam0 P Δ n - Real.log (P.mu ℓ))

lemma f_half_le_S (ℓ : ℕ) (m : ℕ) (hm : 1 ≤ m) (hmn : (m : ℝ) ≤ n / P.mu ℓ) :
    P.f m (Δ / 2) ≤ S P Δ n ℓ := by
  rw [f_half P Δ hN hε hε1 hΦ hΔ]
  unfold S Lam0
  have := a_pos P Δ hN hε hε1 hΦ hΔ
  have := B_ge P Δ hN hε hε1 hΦ hΔ
  have hmu := P2.mu_pos P ℓ
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have : Real.log m ≤ Real.log n - Real.log (P.mu ℓ) := by
    rw [← Real.log_div]
    · apply Real.log_le_log (by linarith); exact hmn
    · have : (0:ℝ) < n := by
        have := (le_div_iff₀ hmu).mp (le_trans hm1 hmn); nlinarith
      exact this.ne'
    · exact hmu.ne'
  have hab : 0 ≤ a P * B P Δ := by positivity
  nlinarith

lemma two_p_add_S_le (ℓ : ℕ) (hℓ : ℓ ≤ P.L) :
    2 * P.p ℓ + S P Δ n ℓ ≤ T P Δ n := by
  have hsplit := P2.log_arg_split P hN hε hε1 hΦ ℓ
  have h2p : 2 * P.p ℓ = a P * (lam P + Real.log (P.mu ℓ)) := by
    unfold Fig2Params.p a lam; rw [hsplit]; ring
  rw [h2p]
  unfold S T
  have := a_pos P Δ hN hε hε1 hΦ hΔ
  have := B_ge P Δ hN hε hε1 hΦ hΔ
  have := lam_nonneg P Δ hN hε hε1 hΦ hΔ
  have : 0 ≤ Real.log (P.mu ℓ) :=
    Real.log_nonneg (by have := P2.mu_ge_two P ℓ hℓ; linarith)
  have hx : 0 ≤ lam P + Real.log (P.mu ℓ) := by linarith
  have key : a P * (lam P + Real.log (P.mu ℓ)) ≤ a P * B P Δ * (lam P + Real.log (P.mu ℓ)) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hx
  nlinarith [key]

lemma S_nonneg (ℓ : ℕ) (m : ℕ) (hm : 1 ≤ m) (hmn : (m : ℝ) ≤ n / P.mu ℓ) : 0 ≤ S P Δ n ℓ :=
  le_trans (f_half_nonneg P Δ hN hε hε1 hΦ hΔ m hm) (f_half_le_S P Δ n hN hε hε1 hΦ hΔ ℓ m hm hmn)

end EA

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

namespace Excl

variable (P : Fig2Params) (Δ : ℝ) (X : Finset V) (v : V)

noncomputable def Fx (s : SSPState V) : ℝ :=
  (s.carved.map (fun c => if v ∈ c.padded then P.f c.cluster.card (Δ / 2) else 0)).sum +
    (if ∀ c ∈ s.carved, v ∉ c.padded then 1 else 0)

noncomputable def budget (ℓ : ℕ) (s : SSPState V) : ℕ :=
  if ℓ = 0 then 0 else ⌊(s.active.card : ℝ) * P.mu (ℓ - 1) / X.card⌋₊

noncomputable def W (ℓ b : ℕ) : ℝ :=
  EA.T P Δ X.card * P2.psi P ℓ ^ b * ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1)

noncomputable def potR (ℓ : ℕ) (s : SSPState V) : ℝ :=
  if v ∈ s.padded then W P Δ X ℓ (budget P X ℓ s) else Fx P Δ v s

/-- The per-scale exclusion functional of an output list. -/
noncomputable def F1 (C : List (Finset V × Finset V)) : ℝ≥0∞ :=
  (C.map (fun c => if v ∈ c.2 then ENNReal.ofReal (P.f c.1.card (Δ / 2)) else 0)).sum +
    (if ∀ c ∈ C, v ∉ c.2 then 1 else 0)


lemma ite_forall_append {α : Type*} (l : List α) (a : α) (p : α → Prop) [DecidablePred p]
    {β : Type*} (x y : β) :
    (if ∀ c ∈ l ++ [a], p c then x else y) = if (∀ c ∈ l, p c) ∧ p a then x else y := by
  by_cases hA : ∀ c ∈ l ++ [a], p c
  · have hB : (∀ c ∈ l, p c) ∧ p a :=
      ⟨fun c hc => hA c (List.mem_append_left _ hc), hA a (by simp)⟩
    rw [if_pos hA, if_pos hB]
  · have hB : ¬ ((∀ c ∈ l, p c) ∧ p a) := fun hB => hA (fun c hc => by
      rcases List.mem_append.mp hc with h | h
      · exact hB.1 c h
      · rw [List.mem_singleton.mp h]; exact hB.2)
    rw [if_neg hA, if_neg hB]

variable {P : Fig2Params} {G : WGraph V} {h : ℕ} {Δ : ℝ}

lemma not_mem_old_padded {X M : Finset V} {s : SSPState V} (hI : SInv P G h Δ X M s) {v : V}
    (hv : v ∈ s.active) : ∀ c ∈ s.carved, v ∉ c.padded := by
  intro c hc hvc
  exact Finset.disjoint_left.mp (hI.c_act c hc) (hI.c_pad c hc hvc) hv

lemma Fx_carve_notin {s : SSPState V} {v : V} (hv : v ∉ s.padded) (ℓ : ℕ) (x : V) (r : ℕ) :
    Fx P Δ v (carveStep P G h Δ ℓ s x r) = Fx P Δ v s := by
  unfold Fx carveStep
  have hn : v ∉ ballA P G h Δ s.active ℓ x ((r : ℤ) - 1) ∩ s.padded := by
    rw [Finset.mem_inter]; exact fun h' => hv h'.2
  rw [ite_forall_append]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hn, if_false, add_zero, not_false_eq_true, and_true]

lemma Fx_carve_captured {X M : Finset V} {s : SSPState V} (hI : SInv P G h Δ X M s) {v : V}
    (hv : v ∈ s.padded) {ℓ : ℕ} {x : V} {r : ℕ} (hr : memB P G h Δ ℓ x ((r : ℤ) - 1) v) :
    Fx P Δ v (carveStep P G h Δ ℓ s x r) =
      P.f (ballA P G h Δ s.active ℓ x r).card (Δ / 2) := by
  have hold := not_mem_old_padded hI (hI.pad_sub hv)
  have hin : v ∈ ballA P G h Δ s.active ℓ x ((r : ℤ) - 1) ∩ s.padded := by
    rw [Finset.mem_inter, mem_ballA]; exact ⟨⟨hI.pad_sub hv, hr⟩, hv⟩
  unfold Fx carveStep
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hin, if_true, add_zero, List.mem_append, List.mem_singleton]
  have h0 : (s.carved.map (fun c => if v ∈ c.padded then P.f c.cluster.card (Δ / 2) else 0)).sum
      = 0 := by
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    simp [hold c hc]
  rw [h0, zero_add, ite_forall_append, if_neg (fun hh => hh.2 hin), add_zero]

lemma Fx_carve_fail {X M : Finset V} {s : SSPState V} (hI : SInv P G h Δ X M s) {v : V}
    (hv : v ∈ s.padded) {ℓ : ℕ} {x : V} {r : ℕ} (hr : ¬ memB P G h Δ ℓ x ((r : ℤ) - 1) v) :
    Fx P Δ v (carveStep P G h Δ ℓ s x r) = 1 := by
  have hold := not_mem_old_padded hI (hI.pad_sub hv)
  have hn : v ∉ ballA P G h Δ s.active ℓ x ((r : ℤ) - 1) ∩ s.padded := by
    rw [Finset.mem_inter, mem_ballA]; exact fun h' => hr h'.1.2
  unfold Fx carveStep
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hn, if_false, add_zero, List.mem_append, List.mem_singleton]
  have h0 : (s.carved.map (fun c => if v ∈ c.padded then P.f c.cluster.card (Δ / 2) else 0)).sum
      = 0 := by
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    simp [hold c hc]
  rw [h0, zero_add, ite_forall_append, if_pos ⟨hold, hn⟩]

lemma padded_carve_untouched {s : SSPState V} {v : V} (hv : v ∈ s.padded) {ℓ : ℕ} {x : V} {r : ℕ}
    (hr : ¬ memB P G h Δ ℓ x ((r : ℤ) + 1) v) : v ∈ (carveStep P G h Δ ℓ s x r).padded := by
  simp only [carveStep, Finset.mem_sdiff, mem_ballA, not_and]
  exact ⟨hv, fun _ => hr⟩

lemma padded_carve_touched {s : SSPState V} {v : V} {ℓ : ℕ} {x : V} {r : ℕ}
    (hva : v ∈ s.active) (hr : memB P G h Δ ℓ x ((r : ℤ) + 1) v) :
    v ∉ (carveStep P G h Δ ℓ s x r).padded := by
  simp only [carveStep, Finset.mem_sdiff, mem_ballA, not_and]
  exact fun _ hh => hh hva hr

lemma budget_carve (hP : NumOK P Δ) {X : Finset V} {s : SSPState V} (hsX : s.active ⊆ X)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {x : V} (hx : Eligible P G h Δ X.card s.active ℓ x) (r : ℕ) :
    budget P X ℓ (carveStep P G h Δ ℓ s x r) + 1 ≤ budget P X ℓ s := by
  unfold budget
  rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨hxa, hA0, -, -⟩ := hx
  have hmu := P2.mu_pos P (ℓ - 1)
  have hXpos : (0 : ℝ) < X.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x, hsX hxa⟩
  set A0 := ballA P G h Δ s.active ℓ x 0
  have hsub : A0 ⊆ ballA P G h Δ s.active ℓ x (r : ℤ) := fun u hu => by
    rw [mem_ballA] at hu ⊢; exact ⟨hu.1, memB_mono hP (by omega) hu.2⟩
  have hA0s : A0 ⊆ s.active := fun u hu => (mem_ballA.mp hu).1
  have hcard : ((carveStep P G h Δ ℓ s x r).active.card : ℝ) + A0.card ≤ s.active.card := by
    have h1 : (carveStep P G h Δ ℓ s x r).active ⊆ s.active \ A0 := by
      simp only [carveStep]; exact Finset.sdiff_subset_sdiff le_rfl hsub
    have h2 := Finset.card_le_card h1
    rw [Finset.card_sdiff_of_subset hA0s] at h2
    have h3 := Finset.card_le_card hA0s
    have : (carveStep P G h Δ ℓ s x r).active.card + A0.card ≤ s.active.card := by omega
    exact_mod_cast this
  set y := ((carveStep P G h Δ ℓ s x r).active.card : ℝ) * P.mu (ℓ - 1) / X.card
  have hy0 : 0 ≤ y := by positivity
  have hy : y + 1 ≤ (s.active.card : ℝ) * P.mu (ℓ - 1) / X.card := by
    simp only [y]
    rw [div_add_one hXpos.ne', div_le_div_iff_of_pos_right hXpos]
    have : (X.card : ℝ) ≤ A0.card * P.mu (ℓ - 1) := by
      rw [div_le_iff₀ hmu] at hA0; exact hA0
    nlinarith
  rw [← Nat.floor_add_one hy0]
  exact Nat.floor_le_floor hy

section WLemmas
variable (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ)
include hN hε hε1 hΦ

lemma prod_psi_ge_one (ℓ : ℕ) (hℓ : ℓ ≤ P.L + 1) :
    1 ≤ ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by
  calc (1 : ℝ) = ∏ j ∈ Finset.Ico 1 ℓ, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j hj => by
        rw [Finset.mem_Ico] at hj
        exact one_le_pow₀ (P2.psi_ge_one P hN hε hε1 hΦ j hj.1 (by omega)))

lemma W_mono {X : Finset V} (hT : 0 ≤ EA.T P Δ X.card) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L)
    {b b' : ℕ} (hb : b ≤ b') : W P Δ X ℓ b ≤ W P Δ X ℓ b' := by
  unfold W
  have hp := prod_psi_ge_one hN hε hε1 hΦ ℓ (by omega)
  have hψ := P2.psi_ge_one P hN hε hε1 hΦ ℓ h1 hℓ
  have : P2.psi P ℓ ^ b ≤ P2.psi P ℓ ^ b' := pow_le_pow_right₀ hψ hb
  have h0 : 0 ≤ ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hT) h0

lemma T_le_W {X : Finset V} (hT : 0 ≤ EA.T P Δ X.card) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L)
    (b : ℕ) : EA.T P Δ X.card ≤ W P Δ X ℓ b := by
  unfold W
  have hp := prod_psi_ge_one hN hε hε1 hΦ ℓ (by omega)
  have hψ := P2.psi_ge_one P hN hε hε1 hΦ ℓ h1 hℓ
  have : 1 ≤ P2.psi P ℓ ^ b := one_le_pow₀ hψ
  have h2 : 1 ≤ P2.psi P ℓ ^ b * ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by nlinarith
  calc EA.T P Δ X.card = EA.T P Δ X.card * 1 := by ring
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hT

lemma W_succ {X : Finset V} {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) (b : ℕ) :
    W P Δ X ℓ (b + 1) * (1 - (1 - P.p ℓ) ^ P.k) = W P Δ X ℓ b := by
  unfold W
  have := P2.psi_mul P hN hε hε1 hΦ ℓ h1 hℓ
  set Q := ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1)
  rw [pow_succ]
  calc EA.T P Δ X.card * (P2.psi P ℓ ^ b * P2.psi P ℓ) * Q * (1 - (1 - P.p ℓ) ^ P.k)
      = EA.T P Δ X.card * P2.psi P ℓ ^ b * Q * (P2.psi P ℓ * (1 - (1 - P.p ℓ) ^ P.k)) := by ring
    _ = _ := by rw [this, mul_one]

end WLemmas

lemma sum_ind_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m k : ℕ) :
    ∑ r ∈ Finset.Ico m k, gw p r * (if r < m + 2 then 1 else 0) ≤ 2 * p * (1 - p) ^ m := by
  calc ∑ r ∈ Finset.Ico m k, gw p r * (if r < m + 2 then 1 else 0)
      ≤ ∑ r ∈ Finset.Ico m k, (if r < m + 2 then p * (1 - p) ^ m else 0) := by
        apply Finset.sum_le_sum; intro r hr
        rw [Finset.mem_Ico] at hr
        split_ifs
        · rw [mul_one]; exact gw_le hp0 hp1 hr.1
        · simp
    _ = ∑ r ∈ (Finset.Ico m k).filter (fun r => r < m + 2), p * (1 - p) ^ m := by
        rw [Finset.sum_filter]
    _ ≤ ∑ r ∈ Finset.Ico m (m + 2), p * (1 - p) ^ m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_Ico] at hr ⊢; omega
        · intro _ _ _; exact mul_nonneg hp0 (pow_nonneg (by linarith) _)
    _ = 2 * p * (1 - p) ^ m := by simp; ring

lemma potR_nonneg (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) {X M : Finset V} {v : V} {s : SSPState V}
    (hI : SInv P G h Δ X M s) (hX : 1 ≤ X.card) (ℓ : ℕ) (hℓ : ℓ ≤ P.L) :
    0 ≤ potR P Δ X v ℓ s := by
  have hT := EA.T_nonneg P Δ X.card hP.N2 hP.eps0 hP.eps1 hP.Phi2 hΔ hX
  unfold potR
  split_ifs
  · rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · subst h0; unfold W budget; simp [hT]
    · exact le_trans hT (T_le_W hP.N2 hP.eps0 hP.eps1 hP.Phi2 hT h0 hℓ _)
  · unfold Fx
    apply add_nonneg
    · apply List.sum_nonneg
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      split_ifs with hvc
      · apply EA.f_half_nonneg P Δ hP.N2 hP.eps0 hP.eps1 hP.Phi2 hΔ
        exact Finset.card_pos.mpr ⟨v, hI.c_pad c hc hvc⟩
      · exact le_rfl
    · split_ifs <;> norm_num

lemma excl_step (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) {rule : CenterRule V}
    (hrule : IsValidRule P G h rule) {X M : Finset V} {v : V} {ℓ : ℕ} (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.L) (s : SSPState V) (hI : SInv P G h Δ X M s)
    (hel : ∃ x, Eligible P G h Δ X.card s.active ℓ x) :
    ex (truncGeom (P.p ℓ) P.k)
        (fun R => ENNReal.ofReal (potR P Δ X v ℓ (carveStep P G h Δ ℓ s (rule X M Δ ℓ s) R)))
      ≤ ENNReal.ofReal (potR P Δ X v ℓ s) := by
  set x := rule X M Δ ℓ s with hxdef
  have hx := hrule X M Δ ℓ s hel
  have hk := hP.kpos
  have hN := hP.N2; have hε := hP.eps0; have hε1 := hP.eps1; have hΦ := hP.Phi2
  have hp0 := P2.p_pos P hN hε hε1 hΦ ℓ hℓ
  have hp1 := P2.p_le_one P hN hε hε1 hΦ ℓ h1 hℓ
  have hθs := P2.theta_small P hN hε hε1 hΦ ℓ h1 hℓ
  have hθ : (1 - P.p ℓ) ^ P.k < 1 := by linarith
  have hXc : 1 ≤ X.card := Finset.card_pos.mpr ⟨x, hI.act_sub hx.1⟩
  have hT := EA.T_nonneg P Δ X.card hN hε hε1 hΦ hΔ hXc
  by_cases hv : v ∈ s.padded
  · have hva := hI.pad_sub hv
    set b := budget P X ℓ s with hbdef
    have hb : ∀ r, budget P X ℓ (carveStep P G h Δ ℓ s x r) + 1 ≤ b :=
      budget_carve hP hI.act_sub h1 hx
    have hb1 : 1 ≤ b := by have := hb 0; omega
    have hpot : potR P Δ X v ℓ s = W P Δ X ℓ b := by unfold potR; rw [if_pos hv]
    rw [hpot]
    apply ex_truncGeom_le hk hp0 hp1 hθ
    · intro r hr
      exact potR_nonneg hP hΔ (SInv.step hP hI h1 hℓ hx hr) hXc ℓ hℓ
    rw [show b = (b - 1) + 1 by omega, W_succ hN hε hε1 hΦ h1 hℓ]
    obtain ⟨m, hm1, hm2, hm3⟩ := touch_index hP (G := G) (h := h) ℓ x v
    -- cluster sizes and the captured bound
    set S := EA.S P Δ X.card ℓ
    have hAk : ∀ r < P.k, 1 ≤ (ballA P G h Δ s.active ℓ x r).card ∧
        ((ballA P G h Δ s.active ℓ x r).card : ℝ) ≤ X.card / P.mu ℓ := by
      intro r hr
      refine ⟨Finset.card_pos.mpr ⟨x, center_mem hP hx r⟩, le_trans ?_ hx.2.2.2⟩
      exact_mod_cast Finset.card_le_card (fun u hu => by
        rw [mem_ballA] at hu ⊢; exact ⟨hu.1, memB_mono hP (by exact_mod_cast hr.le) hu.2⟩)
    have hS0 : 0 ≤ S := EA.S_nonneg P Δ X.card hN hε hε1 hΦ hΔ ℓ _ (hAk 0 hk).1 (hAk 0 hk).2
    apply step_abstract hp0.le hp1 P.k _ (W P Δ X ℓ (b - 1)) (EA.T P Δ X.card)
      (le_trans hT (T_le_W hN hε hε1 hΦ hT h1 hℓ _)) (T_le_W hN hε hε1 hΦ hT h1 hℓ _) m
    · intro r hr
      have hvp := padded_carve_untouched hv (hm1 r hr) (G := G) (h := h) (Δ := Δ)
      unfold potR; rw [if_pos hvp]
      exact W_mono hN hε hε1 hΦ hT h1 hℓ (by have := hb r; omega)
    · have hval : ∀ r ∈ Finset.Ico m P.k,
          potR P Δ X v ℓ (carveStep P G h Δ ℓ s x r) ≤ S + (if r < m + 2 then 1 else 0) := by
        intro r hr
        rw [Finset.mem_Ico] at hr
        have hnp := padded_carve_touched hva (hm2 r hr.1 hr.2) (G := G) (h := h) (Δ := Δ)
        unfold potR; rw [if_neg hnp]
        by_cases hc : memB P G h Δ ℓ x ((r : ℤ) - 1) v
        · rw [Fx_carve_captured hI hv hc]
          have := EA.f_half_le_S P Δ X.card hN hε hε1 hΦ hΔ ℓ _ (hAk r hr.2).1 (hAk r hr.2).2
          split_ifs <;> linarith
        · rw [Fx_carve_fail hI hv hc]
          have : r < m + 2 := by
            by_contra hcon; exact hc (hm3 r (by omega) hr.2)
          rw [if_pos this]; linarith
      calc ∑ r ∈ Finset.Ico m P.k, gw (P.p ℓ) r * potR P Δ X v ℓ (carveStep P G h Δ ℓ s x r)
          ≤ ∑ r ∈ Finset.Ico m P.k, gw (P.p ℓ) r * (S + (if r < m + 2 then 1 else 0)) :=
            Finset.sum_le_sum fun r hr =>
              mul_le_mul_of_nonneg_left (hval r hr) (gw_nonneg hp0.le hp1 r)
        _ = S * ∑ r ∈ Finset.Ico m P.k, gw (P.p ℓ) r +
              ∑ r ∈ Finset.Ico m P.k, gw (P.p ℓ) r * (if r < m + 2 then 1 else 0) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun r _ => by ring
        _ ≤ S * (1 - P.p ℓ) ^ m + 2 * P.p ℓ * (1 - P.p ℓ) ^ m := by
            have h1' := sum_gw_Ico hp0.le hp1 m P.k
            have h2' := sum_ind_le hp0.le hp1 m P.k
            nlinarith
        _ = (1 - P.p ℓ) ^ m * (2 * P.p ℓ + S) := by ring
        _ ≤ (1 - P.p ℓ) ^ m * EA.T P Δ X.card :=
            mul_le_mul_of_nonneg_left (EA.two_p_add_S_le P Δ X.card hN hε hε1 hΦ hΔ ℓ hℓ)
              (pow_nonneg (by linarith) _)
  · -- `v` already decided
    have hpot : potR P Δ X v ℓ s = Fx P Δ v s := by unfold potR; rw [if_neg hv]
    rw [hpot]
    apply ex_le_of_le
    intro R _
    have hnp : v ∉ (carveStep P G h Δ ℓ s x R).padded := by
      simp only [carveStep, Finset.mem_sdiff]; exact fun h' => hv h'.1
    unfold potR; rw [if_neg hnp, Fx_carve_notin hv]

lemma ofReal_list_sum {α : Type*} (l : List α) (φ : α → ℝ) (hφ : ∀ a ∈ l, 0 ≤ φ a) :
    (l.map (fun c => ENNReal.ofReal (φ c))).sum = ENNReal.ofReal ((l.map φ).sum) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih (fun b hb => hφ b (List.mem_cons_of_mem a hb)),
      ENNReal.ofReal_add (hφ a List.mem_cons_self)
        (List.sum_nonneg (fun y hy => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy; exact hφ c (List.mem_cons_of_mem a hc)))]

lemma budget_le (P : Fig2Params) {X : Finset V} {s : SSPState V} (hsX : s.active ⊆ X) (ℓ : ℕ) :
    budget P X ℓ s ≤ P.mu (ℓ - 1) := by
  unfold budget
  split_ifs
  · exact Nat.zero_le _
  · rcases Nat.eq_zero_or_pos X.card with h0 | h0
    · simp [h0]
    · have hX : (0:ℝ) < X.card := by exact_mod_cast h0
      have : (s.active.card : ℝ) * P.mu (ℓ - 1) / X.card ≤ (P.mu (ℓ - 1) : ℕ) := by
        rw [div_le_iff₀ hX]
        have : (s.active.card : ℝ) ≤ X.card := by exact_mod_cast Finset.card_le_card hsX
        have := P2.mu_pos P (ℓ - 1)
        nlinarith
      exact le_trans (Nat.floor_le_floor this) (by rw [Nat.floor_natCast])

lemma W_zero {X : Finset V} (s : SSPState V) : W P Δ X 0 (budget P X 0 s) = EA.T P Δ X.card := by
  unfold W budget; simp

lemma excl_down (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) {X M : Finset V} {v : V} {ℓ : ℕ} (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.L) (s : SSPState V) (hI : SInv P G h Δ X M s) (hXc : 1 ≤ X.card) :
    potR P Δ X v (ℓ - 1) s ≤ potR P Δ X v ℓ s := by
  have hN := hP.N2; have hε := hP.eps0; have hε1 := hP.eps1; have hΦ := hP.Phi2
  have hT := EA.T_nonneg P Δ X.card hN hε hε1 hΦ hΔ hXc
  unfold potR
  split_ifs with hv
  · rcases Nat.lt_or_ge ℓ 2 with hl | hl
    · have : ℓ - 1 = 0 := by omega
      rw [this, W_zero]
      exact T_le_W hN hε hε1 hΦ hT h1 hℓ (budget P X ℓ s)
    · have hb := budget_le P hI.act_sub (ℓ - 1)
      have hl1 : 1 ≤ ℓ - 1 := by omega
      calc W P Δ X (ℓ - 1) (budget P X (ℓ - 1) s)
          ≤ W P Δ X (ℓ - 1) (P.mu (ℓ - 1 - 1)) :=
            W_mono hN hε hε1 hΦ hT hl1 (by omega) hb
        _ = EA.T P Δ X.card * ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by
            unfold W
            conv_rhs => rw [show ℓ = (ℓ - 1) + 1 by omega, Finset.prod_Ico_succ_top hl1]
            ring
        _ ≤ W P Δ X ℓ (budget P X ℓ s) := by
            unfold W
            have hp := prod_psi_ge_one hN hε hε1 hΦ ℓ (by omega)
            have : 1 ≤ P2.psi P ℓ ^ budget P X ℓ s :=
              one_le_pow₀ (P2.psi_ge_one P hN hε hε1 hΦ ℓ h1 hℓ)
            have h0 : 0 ≤ ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by linarith
            calc EA.T P Δ X.card * ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1)
                = EA.T P Δ X.card * 1 * ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hT) h0
  · exact le_rfl

lemma Fx_eq_sum {X M : Finset V} {v : V} (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) (s : SSPState V)
    (hI : SInv P G h Δ X M s) :
    ENNReal.ofReal (Fx P Δ v s) =
      (s.carved.map (fun c => if v ∈ c.padded then ENNReal.ofReal (P.f c.cluster.card (Δ / 2))
        else 0)).sum + (if ∀ c ∈ s.carved, v ∉ c.padded then 1 else 0) := by
  have hN := hP.N2; have hε := hP.eps0; have hε1 := hP.eps1; have hΦ := hP.Phi2
  have hnn : ∀ c ∈ s.carved, 0 ≤ (if v ∈ c.padded then P.f c.cluster.card (Δ / 2) else 0) := by
    intro c hc; split_ifs with hvc
    · exact EA.f_half_nonneg P Δ hN hε hε1 hΦ hΔ _ (Finset.card_pos.mpr ⟨v, hI.c_pad c hc hvc⟩)
    · exact le_rfl
  unfold Fx
  rw [ENNReal.ofReal_add (List.sum_nonneg (fun y hy => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy; exact hnn c hc)) (by split_ifs <;> norm_num)]
  rw [← ofReal_list_sum _ _ hnn]
  congr 1
  · congr 1; apply List.map_congr_left; intro c _; split_ifs <;> simp
  · split_ifs <;> simp

lemma excl_fin (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) {X M : Finset V} {v : V} (s : SSPState V)
    (hI : SInv P G h Δ X M s) :
    F1 P Δ v (sspOutput s) ≤ ENNReal.ofReal (potR P Δ X v 0 s) := by
  have hN := hP.N2; have hε := hP.eps0; have hε1 := hP.eps1; have hΦ := hP.Phi2
  have e : ∀ C : List (Finset V × Finset V),
      (∀ c ∈ s.carved.map (fun c : Carve V => (c.cluster, c.padded)) ++ C, v ∉ c.2) ↔
        (∀ c ∈ s.carved, v ∉ c.padded) ∧ ∀ c ∈ C, v ∉ c.2 := by
    intro C; simp only [List.mem_append, List.mem_map]; constructor
    · intro hh; exact ⟨fun c hc => hh _ (Or.inl ⟨c, hc, rfl⟩), fun c hc => hh c (Or.inr hc)⟩
    · rintro ⟨h1, h2⟩ c (⟨d, hd, rfl⟩ | hc)
      · exact h1 d hd
      · exact h2 c hc
  have hsum : (s.carved.map (fun c : Carve V => (c.cluster, c.padded))).map
      (fun c : Finset V × Finset V => if v ∈ c.2 then ENNReal.ofReal (P.f c.1.card (Δ / 2)) else 0)
      = s.carved.map (fun c => if v ∈ c.padded then ENNReal.ofReal (P.f c.cluster.card (Δ / 2))
        else 0) := by rw [List.map_map]; rfl
  unfold F1 sspOutput potR
  rw [List.map_append, List.sum_append, hsum]
  by_cases hv : v ∈ s.padded
  · have hne : s.active.Nonempty := ⟨v, hI.pad_sub hv⟩
    have hold := not_mem_old_padded hI (hI.pad_sub hv)
    rw [if_pos hne, if_pos hv]
    have h0 : (s.carved.map (fun c => if v ∈ c.padded then
        ENNReal.ofReal (P.f c.cluster.card (Δ / 2)) else 0)).sum = 0 := by
      apply List.sum_eq_zero
      intro y hy; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      simp [hold c hc]
    rw [h0, zero_add, if_neg (fun hh => ((e _).mp hh).2 _ (List.mem_singleton_self _) hv)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hv, if_true, add_zero]
    apply ENNReal.ofReal_le_ofReal
    rw [W_zero]
    exact EA.f_half_le_T P Δ X.card hN hε hε1 hΦ hΔ _
      (Finset.card_pos.mpr hne) (Finset.card_le_card hI.act_sub)
  · rw [if_neg hv, Fx_eq_sum hP hΔ s hI]
    by_cases hne : s.active.Nonempty
    · rw [if_pos hne]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hv, if_false,
        add_zero]
      apply le_of_eq; congr 1
      by_cases hall : ∀ c ∈ s.carved, v ∉ c.padded
      · rw [if_pos ((e _).mpr ⟨hall, by simpa using hv⟩), if_pos hall]
      · rw [if_neg (fun hh => hall ((e _).mp hh).1), if_neg hall]
    · rw [if_neg hne]
      simp only [List.map_nil, List.sum_nil, add_zero, List.append_nil]
      apply le_of_eq; congr 1
      by_cases hall : ∀ c ∈ s.carved, v ∉ c.padded
      · rw [if_pos (by simpa using ((e []).mpr ⟨hall, by simp⟩)), if_pos hall]
      · rw [if_neg (fun hh => hall ((e []).mp (by simpa using hh)).1), if_neg hall]

/-- **Per-scale exclusion bound** (the inductive step of Lemma 1). -/
theorem excl_ssp (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) {rule : CenterRule V}
    (hrule : IsValidRule P G h rule) {X M : Finset V} (hM : M ⊆ X) {v : V} (hv : v ∈ M) :
    ex (singleScalePartition P G h rule X M Δ) (F1 P Δ v) ≤ ENNReal.ofReal (P.f X.card Δ) := by
  have hN := hP.N2; have hε := hP.eps0; have hε1 := hP.eps1; have hΦ := hP.Phi2
  have hXc : 1 ≤ X.card := Finset.card_pos.mpr ⟨v, hM hv⟩
  have hT := EA.T_nonneg P Δ X.card hN hε hε1 hΦ hΔ hXc
  refine le_trans (ssp_ex_le hP hrule hM (fun ℓ s => ENNReal.ofReal (potR P Δ X v ℓ s)) _
    (fun ℓ h1 hℓ s hs hel => excl_step hP hΔ hrule h1 hℓ s hs hel)
    (fun ℓ h1 hℓ s hs => ENNReal.ofReal_le_ofReal (excl_down hP hΔ h1 hℓ s hs hXc))
    (fun s hs => excl_fin hP hΔ s hs)) ?_
  apply ENNReal.ofReal_le_ofReal
  unfold potR
  rw [if_pos hv]
  have hL := hP.Lpos
  have hb : budget P X P.L ⟨X, M, []⟩ = P.mu (P.L - 1) := by
    unfold budget
    rw [if_neg (by omega)]
    have : (X.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : X.card ≠ 0)
    simp only
    rw [mul_div_assoc, mul_comm, div_mul_cancel₀ _ this, Nat.floor_natCast]
  rw [hb, EA.f_full P Δ X.card hN hε hε1 hΦ hΔ]
  unfold W
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hT
  have := P2.prod_psi_le P hN hε hε1 hΦ
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (by omega)] at this
  linarith

end Excl

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Generic potential `T · ψ_ℓ^b · ∏_{1 ≤ j < ℓ} ψ_j^{µ_{j-1}}`. -/
noncomputable def Wg (P : Fig2Params) (T : ℝ) (ℓ b : ℕ) : ℝ :=
  T * P2.psi P ℓ ^ b * ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1)

variable {P : Fig2Params}

section WLemmas
variable (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ)
include hN hε hε1 hΦ

lemma prod_psi_ge_one (ℓ : ℕ) (hℓ : ℓ ≤ P.L + 1) :
    1 ≤ ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by
  calc (1 : ℝ) = ∏ j ∈ Finset.Ico 1 ℓ, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j hj => by
        rw [Finset.mem_Ico] at hj
        exact one_le_pow₀ (P2.psi_ge_one P hN hε hε1 hΦ j hj.1 (by omega)))

lemma Wg_mono {T : ℝ} (hT : 0 ≤ T) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L)
    {b b' : ℕ} (hb : b ≤ b') : Wg P T ℓ b ≤ Wg P T ℓ b' := by
  unfold Wg
  have hp := prod_psi_ge_one hN hε hε1 hΦ ℓ (by omega)
  have hψ := P2.psi_ge_one P hN hε hε1 hΦ ℓ h1 hℓ
  have : P2.psi P ℓ ^ b ≤ P2.psi P ℓ ^ b' := pow_le_pow_right₀ hψ hb
  have h0 : 0 ≤ ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hT) h0

lemma T_le_Wg {T : ℝ} (hT : 0 ≤ T) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L)
    (b : ℕ) : T ≤ Wg P T ℓ b := by
  unfold Wg
  have hp := prod_psi_ge_one hN hε hε1 hΦ ℓ (by omega)
  have hψ := P2.psi_ge_one P hN hε hε1 hΦ ℓ h1 hℓ
  have : 1 ≤ P2.psi P ℓ ^ b := one_le_pow₀ hψ
  have h2 : 1 ≤ P2.psi P ℓ ^ b * ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by nlinarith
  calc T = T * 1 := by ring
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 hT

lemma Wg_succ {T : ℝ} {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) (b : ℕ) :
    Wg P T ℓ (b + 1) * (1 - (1 - P.p ℓ) ^ P.k) = Wg P T ℓ b := by
  unfold Wg
  have := P2.psi_mul P hN hε hε1 hΦ ℓ h1 hℓ
  set Q := ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1)
  rw [pow_succ]
  calc T * (P2.psi P ℓ ^ b * P2.psi P ℓ) * Q * (1 - (1 - P.p ℓ) ^ P.k)
      = T * P2.psi P ℓ ^ b * Q * (P2.psi P ℓ * (1 - (1 - P.p ℓ) ^ P.k)) := by ring
    _ = _ := by rw [this, mul_one]

end WLemmas

lemma Wg_zero (T : ℝ) (b : ℕ) : Wg P T 0 0 = T := by unfold Wg; simp

section WLemmas2
variable (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ)
include hN hε hε1 hΦ

lemma Wg_down {T : ℝ} (hT : 0 ≤ T) {X : Finset V} {s : SSPState V} (hsX : s.active ⊆ X)
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) :
    Wg P T (ℓ - 1) (Excl.budget P X (ℓ - 1) s) ≤ Wg P T ℓ (Excl.budget P X ℓ s) := by
  rcases Nat.lt_or_ge ℓ 2 with hl | hl
  · have : ℓ - 1 = 0 := by omega
    rw [this, show Excl.budget P X 0 s = 0 by unfold Excl.budget; simp, Wg_zero T 0]
    exact T_le_Wg hN hε hε1 hΦ hT h1 hℓ _
  · have hb := Excl.budget_le P hsX (ℓ - 1)
    have hl1 : 1 ≤ ℓ - 1 := by omega
    calc Wg P T (ℓ - 1) (Excl.budget P X (ℓ - 1) s)
        ≤ Wg P T (ℓ - 1) (P.mu (ℓ - 1 - 1)) := Wg_mono hN hε hε1 hΦ hT hl1 (by omega) hb
      _ = T * ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by
          unfold Wg
          conv_rhs => rw [show ℓ = (ℓ - 1) + 1 by omega, Finset.prod_Ico_succ_top hl1]
          ring
      _ ≤ Wg P T ℓ (Excl.budget P X ℓ s) := by
          unfold Wg
          have hp := prod_psi_ge_one hN hε hε1 hΦ ℓ (by omega)
          have : 1 ≤ P2.psi P ℓ ^ Excl.budget P X ℓ s :=
            one_le_pow₀ (P2.psi_ge_one P hN hε hε1 hΦ ℓ h1 hℓ)
          have h0 : 0 ≤ ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by linarith
          calc T * ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1)
              = T * 1 * ∏ j ∈ Finset.Ico 1 ℓ, P2.psi P j ^ P.mu (j - 1) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hT) h0

lemma Wg_init {T : ℝ} (hT : 0 ≤ T) {X M : Finset V} (hX : 1 ≤ X.card) :
    Wg P T P.L (Excl.budget P X P.L ⟨X, M, []⟩) ≤ T * (1 + 2 * P.delta) := by
  have hL := P2.L_pos P hN
  have hb : Excl.budget P X P.L ⟨X, M, []⟩ = P.mu (P.L - 1) := by
    unfold Excl.budget
    rw [if_neg (by omega)]
    have : (X.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : X.card ≠ 0)
    simp only
    rw [mul_div_assoc, mul_comm, div_mul_cancel₀ _ this, Nat.floor_natCast]
  rw [hb]
  unfold Wg
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hT
  have := P2.prod_psi_le P hN hε hε1 hΦ
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (by omega)] at this
  linarith

end WLemmas2

end HopRamsey.FZ


namespace HopRamsey.FZ

open HopRamsey

namespace DA

variable (P : Fig2Params) (Δ : ℝ) (n : ℕ)

noncomputable def G0 : ℝ := 2 ^ 8 * P.L * (1 + 2 * P.delta) ^ (Real.logb 2 Δ - 1)

set_option linter.unusedSectionVars false
variable (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ) (hΔ : 2 ≤ Δ)
include hN hε hε1 hΦ hΔ

lemma G0_ge : 2 ^ 8 * (P.L : ℝ) ≤ G0 P Δ := by
  unfold G0
  have := EA.B_ge P Δ hN hε hε1 hΦ hΔ
  unfold EA.B at this
  have : (0:ℝ) ≤ 2 ^ 8 * P.L := by positivity
  nlinarith

lemma G0_nonneg : 0 ≤ G0 P Δ := le_trans (by positivity) (G0_ge P Δ hN hε hε1 hΦ hΔ)

lemma g_half (m : ℕ) : P.g m (Δ / 2) = G0 P Δ * Real.logb 2 m := by
  unfold Fig2Params.g G0
  rw [EA.logb_half P Δ hN hε hε1 hΦ hΔ]; ring

lemma g_full : P.g n Δ = G0 P Δ * Real.logb 2 n * (1 + 2 * P.delta) := by
  unfold Fig2Params.g G0
  have hd := P2.delta_pos P hN
  rw [Real.rpow_sub_one (by linarith)]
  field_simp

lemma g_half_nonneg (m : ℕ) (hm : 1 ≤ m) : 0 ≤ P.g m (Δ / 2) := by
  rw [g_half P Δ hN hε hε1 hΦ hΔ]
  have := G0_nonneg P Δ hN hε hε1 hΦ hΔ
  have : 0 ≤ Real.logb 2 m := Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
  positivity

lemma g_half_le (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    P.g m (Δ / 2) ≤ G0 P Δ * Real.logb 2 n := by
  rw [g_half P Δ hN hε hε1 hΦ hΔ]
  apply mul_le_mul_of_nonneg_left _ (G0_nonneg P Δ hN hε hε1 hΦ hΔ)
  exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hm) (by exact_mod_cast hmn)

lemma g_half_le_cap (ℓ : ℕ) (m : ℕ) (hm : 1 ≤ m) (hmn : (m : ℝ) ≤ n / P.mu ℓ) :
    P.g m (Δ / 2) ≤ G0 P Δ * (Real.logb 2 n - Real.logb 2 (P.mu ℓ)) := by
  rw [g_half P Δ hN hε hε1 hΦ hΔ]
  apply mul_le_mul_of_nonneg_left _ (G0_nonneg P Δ hN hε hε1 hΦ hΔ)
  have hmu := P2.mu_pos P ℓ
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hn : (0:ℝ) < n := by
    have := (le_div_iff₀ hmu).mp (le_trans hm1 hmn); nlinarith
  rw [← Real.logb_div hn.ne' hmu.ne']
  exact Real.logb_le_logb_of_le (by norm_num) (by linarith) hmn

lemma cap_nonneg (ℓ : ℕ) (m : ℕ) (hm : 1 ≤ m) (hmn : (m : ℝ) ≤ n / P.mu ℓ) :
    0 ≤ G0 P Δ * (Real.logb 2 n - Real.logb 2 (P.mu ℓ)) :=
  le_trans (g_half_nonneg P Δ hN hε hε1 hΦ hΔ m hm) (g_half_le_cap P Δ n hN hε hε1 hΦ hΔ ℓ m hm hmn)

/-- The touched-part inequality for pairs. -/
lemma pair_touch (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) (dR : ℝ) (hd : 0 ≤ dR) (cnt : ℝ)
    (hcnt : cnt ≤ dR / P.q Δ ℓ) (hc0 : 0 ≤ cnt) :
    Δ * P.p ℓ * cnt + G0 P Δ * (Real.logb 2 n - Real.logb 2 (P.mu ℓ)) * dR ≤
      G0 P Δ * Real.logb 2 n * dR := by
  have hq : 0 < P.q Δ ℓ := by
    have := P2.q_ge P hN hε hε1 hΦ Δ (by linarith) ℓ h1
    have hk : (0:ℝ) < P.k := by exact_mod_cast P2.k_pos P hN hε hε1 hΦ
    have hL : (0:ℝ) < P.L := by exact_mod_cast (P2.L_pos P hN)
    have : 0 < Δ / (8 * P.L * P.k) := by apply div_pos <;> positivity
    linarith
  have hpi := P2.pair_ineq P hN hε hε1 hΦ Δ (by linarith) ℓ h1 hℓ
  have hp0 := P2.p_pos P hN hε hε1 hΦ ℓ hℓ
  have hG := G0_ge P Δ hN hε hε1 hΦ hΔ
  have hlogmu : 0 ≤ Real.logb 2 (P.mu ℓ : ℝ) :=
    Real.logb_nonneg (by norm_num) (by have := P2.mu_ge_two P ℓ hℓ; linarith)
  -- Δ p cnt ≤ Δ p dR / q ≤ 2^7 L logμ dR
  have h1' : Δ * P.p ℓ * cnt ≤ 2 ^ 7 * P.L * Real.logb 2 (P.mu ℓ) * dR := by
    have hΔp : 0 ≤ Δ * P.p ℓ := by positivity
    calc Δ * P.p ℓ * cnt ≤ Δ * P.p ℓ * (dR / P.q Δ ℓ) := mul_le_mul_of_nonneg_left hcnt hΔp
      _ = (P.p ℓ * Δ) * dR / P.q Δ ℓ := by ring
      _ ≤ (2 ^ 7 * P.L * Real.logb 2 (P.mu ℓ) * P.q Δ ℓ) * dR / P.q Δ ℓ := by
          apply div_le_div_of_nonneg_right _ hq.le
          exact mul_le_mul_of_nonneg_right hpi hd
      _ = 2 ^ 7 * P.L * Real.logb 2 (P.mu ℓ) * dR := by field_simp
  have h2' : 2 ^ 7 * (P.L : ℝ) * Real.logb 2 (P.mu ℓ) * dR ≤
      G0 P Δ * Real.logb 2 (P.mu ℓ) * dR := by
    apply mul_le_mul_of_nonneg_right _ hd
    apply mul_le_mul_of_nonneg_right _ hlogmu
    have : (0:ℝ) ≤ P.L := by positivity
    linarith
  nlinarith

end DA

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

namespace Dist

variable (P : Fig2Params) (Δ : ℝ) (X : Finset V) (u v : V) (dR : ℝ)

noncomputable def Fy (s : SSPState V) : ℝ :=
  (s.carved.map (fun c => if u ∈ c.padded ∧ v ∈ c.padded then
      P.g c.cluster.card (Δ / 2) * dR else 0)).sum +
    (if (∀ c ∈ s.carved, ¬ (u ∈ c.cluster ∧ v ∈ c.cluster)) ∧
        (u ∈ s.padded ∨ ∃ c ∈ s.carved, u ∈ c.padded) ∧
        (v ∈ s.padded ∨ ∃ c ∈ s.carved, v ∈ c.padded) then Δ else 0)

noncomputable def T2 : ℝ := DA.G0 P Δ * Real.logb 2 X.card * dR

noncomputable def potR (ℓ : ℕ) (s : SSPState V) : ℝ :=
  if u ∈ s.padded ∧ v ∈ s.padded then Wg P (T2 P Δ X dR) ℓ (Excl.budget P X ℓ s)
  else Fy P Δ u v dR s

/-- The per-scale expected-distortion functional of an output list. -/
noncomputable def F2 (d : ℝ≥0∞) (C : List (Finset V × Finset V)) : ℝ≥0∞ :=
  (C.map (fun c => if u ∈ c.2 ∧ v ∈ c.2 then ENNReal.ofReal (P.g c.1.card (Δ / 2)) * d
      else 0)).sum +
    (if (¬ ∃ c ∈ C, u ∈ c.1 ∧ v ∈ c.1) ∧ (∃ c ∈ C, u ∈ c.2) ∧ (∃ c ∈ C, v ∈ c.2)
      then ENNReal.ofReal Δ else 0)

variable {P : Fig2Params} {G : WGraph V} {h : ℕ} {Δ : ℝ}

/-- Splitting radius: one of the pair is padded inside, the other untouched. -/
def split (P : Fig2Params) (G : WGraph V) (h : ℕ) (Δ : ℝ) (ℓ : ℕ) (x u v : V) (r : ℕ) : Prop :=
  (memB P G h Δ ℓ x ((r : ℤ) - 1) u ∧ ¬ memB P G h Δ ℓ x ((r : ℤ) + 1) v) ∨
    (memB P G h Δ ℓ x ((r : ℤ) - 1) v ∧ ¬ memB P G h Δ ℓ x ((r : ℤ) + 1) u)

lemma split_gap (hP : NumOK P Δ) {ℓ : ℕ} (h1 : 1 ≤ ℓ) {x u v : V} {J : ℕ} (hJ : 1 ≤ J)
    (huv : hopDist G h u v ≤ ENNReal.ofReal (J * P.q Δ ℓ)) {r1 r2 : ℕ}
    (s1 : split P G h Δ ℓ x u v r1) (s2 : split P G h Δ ℓ x u v r2) : r2 + 3 ≤ r1 + J := by
  have hvu : hopDist G h v u ≤ ENNReal.ofReal (J * P.q Δ ℓ) := by rwa [hopDist_symm]
  -- monotonicity contrapositive
  have mono : ∀ {w : V} {a b : ℤ}, memB P G h Δ ℓ x a w → ¬ memB P G h Δ ℓ x b w → b < a :=
    fun ha hb => by by_contra hc; push Not at hc; exact hb (memB_mono hP hc ha)
  rcases s1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases s2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
  · have := memB_step hP h1 (by omega) a1 J hJ huv
    have := mono this b2; omega
  · have := mono a1 b2; have := mono a2 b1; omega
  · have := mono a1 b2; have := mono a2 b1; omega
  · have := memB_step hP h1 (by omega) a1 J hJ hvu
    have := mono this b2; omega

lemma q_pos (hP : NumOK P Δ) (hΔ : 0 < Δ) {ℓ : ℕ} (h1 : 1 ≤ ℓ) : 0 < P.q Δ ℓ := by
  have := P2.q_ge P hP.N2 hP.eps0 hP.eps1 hP.Phi2 Δ hP.Δ0 ℓ h1
  have hk : (0:ℝ) < P.k := by exact_mod_cast hP.kpos
  have hL : (0:ℝ) < P.L := by exact_mod_cast hP.Lpos
  have : 0 < Δ / (8 * P.L * P.k) := by apply div_pos hΔ; positivity
  linarith

lemma card_split_le (hP : NumOK P Δ) (hΔ : 0 < Δ) {ℓ : ℕ} (h1 : 1 ≤ ℓ) {x u v : V} {dR : ℝ} (hd : 0 ≤ dR)
    (huv : hopDist G h u v ≤ ENNReal.ofReal dR) (F : Finset ℕ)
    (hF : ∀ r ∈ F, split P G h Δ ℓ x u v r) : (F.card : ℝ) ≤ dR / P.q Δ ℓ := by
  have hq : 0 < P.q Δ ℓ := q_pos hP hΔ h1
  set J := max 1 ⌈dR / P.q Δ ℓ⌉₊ with hJdef
  have hJ1 : 1 ≤ J := le_max_left _ _
  have hJq : dR ≤ J * P.q Δ ℓ := by
    have : dR / P.q Δ ℓ ≤ J := le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)
    rwa [div_le_iff₀ hq] at this
  have huv' : hopDist G h u v ≤ ENNReal.ofReal (J * P.q Δ ℓ) :=
    le_trans huv (ENNReal.ofReal_le_ofReal hJq)
  rcases F.eq_empty_or_nonempty with hF0 | hFne
  · rw [hF0]; simp; positivity
  · set a := F.min' hFne
    have ha : a ∈ F := F.min'_mem hFne
    have hgap := fun r hr => split_gap hP h1 hJ1 huv' (hF a ha) (hF r hr)
    have hJ3 : 3 ≤ J := by have := hgap a ha; omega
    have hsub : F ⊆ Finset.Ico a (a + (J - 2)) := by
      intro r hr
      rw [Finset.mem_Ico]
      exact ⟨F.min'_le r hr, by have := hgap r hr; omega⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hc
    have hJeq : J = ⌈dR / P.q Δ ℓ⌉₊ := by
      rcases le_total 1 ⌈dR / P.q Δ ℓ⌉₊ with h' | h'
      · exact max_eq_right h'
      · exfalso; have : J = 1 := max_eq_left h'; omega
    have hceil : (J : ℝ) < dR / P.q Δ ℓ + 1 := by
      rw [hJeq]; exact Nat.ceil_lt_add_one (by positivity)
    have : (F.card : ℝ) ≤ (J : ℝ) - 2 := by
      have : F.card ≤ J - 2 := by omega
      have h2 : ((J - 2 : ℕ) : ℝ) = (J : ℝ) - 2 := by push_cast [show 2 ≤ J by omega]; ring
      rw [← h2]; exact_mod_cast this
    linarith

lemma ite_le_ite_of_imp {p q : Prop} [Decidable p] [Decidable q] {a : ℝ} (ha : 0 ≤ a)
    (hpq : p → q) : (if p then a else 0) ≤ (if q then a else 0) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (hpq hp)]
  · rw [if_neg hp]; split_ifs <;> linarith

lemma ite_congr_inst {p : Prop} (i1 i2 : Decidable p) {a : ℝ} :
    @ite ℝ p i1 a 0 ≤ @ite ℝ p i2 a 0 := by
  by_cases hp : p
  · rw [@if_pos _ i1 hp, @if_pos _ i2 hp]
  · rw [@if_neg _ i1 hp, @if_neg _ i2 hp]

lemma Fy_carve_decided (hΔ0 : 0 ≤ Δ) {s : SSPState V} {u v : V}
    (hnot : ¬ (u ∈ s.padded ∧ v ∈ s.padded)) (ℓ : ℕ) (x : V) (r : ℕ) :
    Fy P Δ u v dR (carveStep P G h Δ ℓ s x r) ≤ Fy P Δ u v dR s ∧
      ¬ (u ∈ (carveStep P G h Δ ℓ s x r).padded ∧ v ∈ (carveStep P G h Δ ℓ s x r).padded) := by
  have hpad : (carveStep P G h Δ ℓ s x r).padded ⊆ s.padded := by
    simp only [carveStep]; exact Finset.sdiff_subset
  have hnew : ¬ (u ∈ ballA P G h Δ s.active ℓ x ((r : ℤ) - 1) ∩ s.padded ∧
      v ∈ ballA P G h Δ s.active ℓ x ((r : ℤ) - 1) ∩ s.padded) := by
    rw [Finset.mem_inter, Finset.mem_inter]; exact fun hh => hnot ⟨hh.1.2, hh.2.2⟩
  refine ⟨?_, fun hh => hnot ⟨hpad hh.1, hpad hh.2⟩⟩
  unfold Fy
  simp only [carveStep, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hnew, if_false, add_zero]
  apply add_le_add_right
  apply ite_le_ite_of_imp hΔ0
  rintro ⟨hc, hu, hv⟩
  refine ⟨fun c hc' => hc c (List.mem_append_left _ hc'), ?_, ?_⟩
  · rcases hu with hu | ⟨c, hc', huc⟩
    · exact Or.inl (Finset.mem_sdiff.mp hu).1
    · rcases List.mem_append.mp hc' with hc' | hc'
      · exact Or.inr ⟨c, hc', huc⟩
      · rw [List.mem_singleton] at hc'; subst hc'; exact Or.inl (Finset.mem_inter.mp huc).2
  · rcases hv with hv | ⟨c, hc', hvc⟩
    · exact Or.inl (Finset.mem_sdiff.mp hv).1
    · rcases List.mem_append.mp hc' with hc' | hc'
      · exact Or.inr ⟨c, hc', hvc⟩
      · rw [List.mem_singleton] at hc'; subst hc'; exact Or.inl (Finset.mem_inter.mp hvc).2

open Classical in
lemma Fy_carve_touched (hP : NumOK P Δ) (hd : 0 ≤ dR) {X M : Finset V} {s : SSPState V}
    (hI : SInv P G h Δ X M s) {u v : V} (hu : u ∈ s.padded) (hv : v ∈ s.padded) {ℓ : ℕ} {x : V}
    {r : ℕ} (htouch : memB P G h Δ ℓ x ((r : ℤ) + 1) u ∨ memB P G h Δ ℓ x ((r : ℤ) + 1) v) :
    Fy P Δ u v dR (carveStep P G h Δ ℓ s x r) ≤
      (if split P G h Δ ℓ x u v r then Δ else 0) +
        (if memB P G h Δ ℓ x ((r : ℤ) - 1) u ∧ memB P G h Δ ℓ x ((r : ℤ) - 1) v then
          P.g (ballA P G h Δ s.active ℓ x r).card (Δ / 2) * dR else 0) := by
  classical
  have hua := hI.pad_sub hu
  have hva := hI.pad_sub hv
  have hold := Excl.not_mem_old_padded hI hua
  have hnewu : u ∈ ballA P G h Δ s.active ℓ x ((r : ℤ) - 1) ∩ s.padded ↔
      memB P G h Δ ℓ x ((r : ℤ) - 1) u := by
    rw [Finset.mem_inter, mem_ballA]; exact ⟨fun hh => hh.1.2, fun hh => ⟨⟨hua, hh⟩, hu⟩⟩
  have hnewv : v ∈ ballA P G h Δ s.active ℓ x ((r : ℤ) - 1) ∩ s.padded ↔
      memB P G h Δ ℓ x ((r : ℤ) - 1) v := by
    rw [Finset.mem_inter, mem_ballA]; exact ⟨fun hh => hh.1.2, fun hh => ⟨⟨hva, hh⟩, hv⟩⟩
  unfold Fy
  simp only [carveStep, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, hnewu, hnewv]
  have h0 : (s.carved.map (fun c => if u ∈ c.padded ∧ v ∈ c.padded then
      P.g c.cluster.card (Δ / 2) * dR else 0)).sum = 0 := by
    apply List.sum_eq_zero
    intro y hy; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    simp [hold c hc]
  rw [h0, zero_add, add_comm]
  refine add_le_add (ite_le_ite_of_imp hP.Δ0 ?_) (ite_congr_inst _ _)
  rintro ⟨hcl, hU, hV⟩
  have hU' : ¬ memB P G h Δ ℓ x ((r : ℤ) + 1) u ∨ memB P G h Δ ℓ x ((r : ℤ) - 1) u := by
    rcases hU with hU | ⟨c, hc', huc⟩
    · left; simp only [Finset.mem_sdiff, mem_ballA, not_and] at hU; exact hU.2 hua
    · rcases List.mem_append.mp hc' with hc' | hc'
      · exact absurd huc (hold c hc')
      · rw [List.mem_singleton] at hc'; subst hc'; right; exact hnewu.mp huc
  have hV' : ¬ memB P G h Δ ℓ x ((r : ℤ) + 1) v ∨ memB P G h Δ ℓ x ((r : ℤ) - 1) v := by
    rcases hV with hV | ⟨c, hc', hvc⟩
    · left; simp only [Finset.mem_sdiff, mem_ballA, not_and] at hV; exact hV.2 hva
    · rcases List.mem_append.mp hc' with hc' | hc'
      · exact absurd hvc (Excl.not_mem_old_padded hI hva c hc')
      · rw [List.mem_singleton] at hc'; subst hc'; right; exact hnewv.mp hvc
  have hnc := hcl _ (List.mem_append_right _ (List.mem_singleton_self _))
  simp only [mem_ballA] at hnc
  unfold split
  rcases hU' with hU' | hU' <;> rcases hV' with hV' | hV'
  · exfalso; rcases htouch with ht | ht
    · exact hU' ht
    · exact hV' ht
  · right; exact ⟨hV', hU'⟩
  · left; exact ⟨hU', hV'⟩
  · exfalso; exact hnc ⟨⟨hua, memB_mono hP (by omega) hU'⟩, ⟨hva, memB_mono hP (by omega) hV'⟩⟩

lemma pair_touch_index (hP : NumOK P Δ) (ℓ : ℕ) (x u v : V) :
    ∃ m : ℕ, (∀ r < m, ¬ memB P G h Δ ℓ x ((r : ℤ) + 1) u ∧ ¬ memB P G h Δ ℓ x ((r : ℤ) + 1) v) ∧
      (∀ r, m ≤ r → r < P.k →
        memB P G h Δ ℓ x ((r : ℤ) + 1) u ∨ memB P G h Δ ℓ x ((r : ℤ) + 1) v) := by
  classical
  by_cases hex : ∃ r : ℕ, memB P G h Δ ℓ x ((r : ℤ) + 1) u ∨ memB P G h Δ ℓ x ((r : ℤ) + 1) v
  · refine ⟨Nat.find hex, fun r hr => ?_, fun r hr _ => ?_⟩
    · have := Nat.find_min hex hr; push Not at this; exact this
    · rcases Nat.find_spec hex with h' | h'
      · exact Or.inl (memB_mono hP (by omega) h')
      · exact Or.inr (memB_mono hP (by omega) h')
  · push Not at hex
    exact ⟨P.k, fun r _ => hex r, fun r hr hr' => absurd hr' (by omega)⟩

lemma potR_nonneg (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) (hd : 0 ≤ dR) {X M : Finset V} {u v : V}
    {s : SSPState V} (hI : SInv P G h Δ X M s) (hX : 1 ≤ X.card) (ℓ : ℕ) (hℓ : ℓ ≤ P.L) :
    0 ≤ potR P Δ X u v dR ℓ s := by
  have hN := hP.N2; have hε := hP.eps0; have hε1 := hP.eps1; have hΦ := hP.Phi2
  have hT : 0 ≤ T2 P Δ X dR := by
    unfold T2
    have := DA.G0_nonneg P Δ hN hε hε1 hΦ hΔ
    have : 0 ≤ Real.logb 2 X.card := Real.logb_nonneg (by norm_num) (by exact_mod_cast hX)
    positivity
  unfold potR
  split_ifs
  · rcases Nat.eq_zero_or_pos ℓ with h0 | h0
    · subst h0; rw [show Excl.budget P X 0 s = 0 by unfold Excl.budget; simp, Wg_zero _ 0]; exact hT
    · exact le_trans hT (T_le_Wg hN hε hε1 hΦ hT h0 hℓ _)
  · unfold Fy
    apply add_nonneg
    · apply List.sum_nonneg
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      split_ifs with hvc
      · exact mul_nonneg (DA.g_half_nonneg P Δ hN hε hε1 hΦ hΔ _
          (Finset.card_pos.mpr ⟨u, hI.c_pad c hc hvc.1⟩)) hd
      · exact le_rfl
    · split_ifs <;> linarith

lemma pair_step (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) {rule : CenterRule V}
    (hrule : IsValidRule P G h rule) {X M : Finset V} {u v : V} (hd0 : 0 ≤ dR)
    (hd : hopDist G h u v ≤ ENNReal.ofReal dR) {ℓ : ℕ} (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.L) (s : SSPState V) (hI : SInv P G h Δ X M s)
    (hel : ∃ x, Eligible P G h Δ X.card s.active ℓ x) :
    ex (truncGeom (P.p ℓ) P.k)
        (fun R => ENNReal.ofReal (potR P Δ X u v dR ℓ (carveStep P G h Δ ℓ s (rule X M Δ ℓ s) R)))
      ≤ ENNReal.ofReal (potR P Δ X u v dR ℓ s) := by
  classical
  set x := rule X M Δ ℓ s with hxdef
  have hx := hrule X M Δ ℓ s hel
  have hk := hP.kpos
  have hN := hP.N2; have hε := hP.eps0; have hε1 := hP.eps1; have hΦ := hP.Phi2
  have hp0 := P2.p_pos P hN hε hε1 hΦ ℓ hℓ
  have hp1 := P2.p_le_one P hN hε hε1 hΦ ℓ h1 hℓ
  have hθs := P2.theta_small P hN hε hε1 hΦ ℓ h1 hℓ
  have hθ : (1 - P.p ℓ) ^ P.k < 1 := by linarith
  have hXc : 1 ≤ X.card := Finset.card_pos.mpr ⟨x, hI.act_sub hx.1⟩
  have hT : 0 ≤ T2 P Δ X dR := by
    unfold T2
    have := DA.G0_nonneg P Δ hN hε hε1 hΦ hΔ
    have : 0 ≤ Real.logb 2 X.card := Real.logb_nonneg (by norm_num) (by exact_mod_cast hXc)
    positivity
  by_cases huv : u ∈ s.padded ∧ v ∈ s.padded
  · obtain ⟨hu, hv⟩ := huv
    have hua := hI.pad_sub hu
    have hva := hI.pad_sub hv
    set b := Excl.budget P X ℓ s with hbdef
    have hb : ∀ r, Excl.budget P X ℓ (carveStep P G h Δ ℓ s x r) + 1 ≤ b :=
      Excl.budget_carve hP hI.act_sub h1 hx
    have hb1 : 1 ≤ b := by have := hb 0; omega
    have hpot : potR P Δ X u v dR ℓ s = Wg P (T2 P Δ X dR) ℓ b := by
      unfold potR; rw [if_pos ⟨hu, hv⟩]
    rw [hpot]
    apply ex_truncGeom_le hk hp0 hp1 hθ
    · intro r hr
      exact potR_nonneg dR hP hΔ hd0 (SInv.step hP hI h1 hℓ hx hr) hXc ℓ hℓ
    rw [show b = (b - 1) + 1 by omega, Wg_succ hN hε hε1 hΦ h1 hℓ]
    obtain ⟨m, hm1, hm2⟩ := pair_touch_index hP (G := G) (h := h) ℓ x u v
    have hAk : ∀ r < P.k, 1 ≤ (ballA P G h Δ s.active ℓ x r).card ∧
        ((ballA P G h Δ s.active ℓ x r).card : ℝ) ≤ X.card / P.mu ℓ := by
      intro r hr
      refine ⟨Finset.card_pos.mpr ⟨x, center_mem hP hx r⟩, le_trans ?_ hx.2.2.2⟩
      exact_mod_cast Finset.card_le_card (fun w hw => by
        rw [mem_ballA] at hw ⊢; exact ⟨hw.1, memB_mono hP (by exact_mod_cast hr.le) hw.2⟩)
    set Cap := DA.G0 P Δ * (Real.logb 2 X.card - Real.logb 2 (P.mu ℓ)) * dR
    have hCap0 : 0 ≤ Cap :=
      mul_nonneg (DA.cap_nonneg P Δ X.card hN hε hε1 hΦ hΔ ℓ _ (hAk 0 hk).1 (hAk 0 hk).2) hd0
    apply step_abstract hp0.le hp1 P.k _ (Wg P (T2 P Δ X dR) ℓ (b - 1)) (T2 P Δ X dR)
      (le_trans hT (T_le_Wg hN hε hε1 hΦ hT h1 hℓ _)) (T_le_Wg hN hε hε1 hΦ hT h1 hℓ _) m
    · intro r hr
      have hu' := Excl.padded_carve_untouched hu (hm1 r hr).1 (G := G) (h := h) (Δ := Δ)
      have hv' := Excl.padded_carve_untouched hv (hm1 r hr).2 (G := G) (h := h) (Δ := Δ)
      unfold potR; rw [if_pos ⟨hu', hv'⟩]
      exact Wg_mono hN hε hε1 hΦ hT h1 hℓ (by have := hb r; omega)
    · have hval : ∀ r ∈ Finset.Ico m P.k, potR P Δ X u v dR ℓ (carveStep P G h Δ ℓ s x r) ≤
          (if split P G h Δ ℓ x u v r then Δ else 0) + Cap := by
        intro r hr
        rw [Finset.mem_Ico] at hr
        have ht := hm2 r hr.1 hr.2
        have hnp : ¬ (u ∈ (carveStep P G h Δ ℓ s x r).padded ∧
            v ∈ (carveStep P G h Δ ℓ s x r).padded) := by
          rintro ⟨h1', h2'⟩
          rcases ht with ht | ht
          · exact Excl.padded_carve_touched hua ht h1'
          · exact Excl.padded_carve_touched hva ht h2'
        unfold potR; rw [if_neg hnp]
        refine le_trans (Fy_carve_touched dR hP hd0 hI hu hv ht) (add_le_add le_rfl ?_)
        split_ifs
        · exact mul_le_mul_of_nonneg_right
            (DA.g_half_le_cap P Δ X.card hN hε hε1 hΦ hΔ ℓ _ (hAk r hr.2).1 (hAk r hr.2).2) hd0
        · exact hCap0
      set F := (Finset.Ico m P.k).filter (fun r => split P G h Δ ℓ x u v r)
      have hcnt : (F.card : ℝ) ≤ dR / P.q Δ ℓ :=
        card_split_le hP (by linarith) h1 hd0 hd F (fun r hr => (Finset.mem_filter.mp hr).2)
      have hsplit : ∑ r ∈ Finset.Ico m P.k, gw (P.p ℓ) r * (if split P G h Δ ℓ x u v r then Δ else 0)
          ≤ Δ * P.p ℓ * (1 - P.p ℓ) ^ m * F.card := by
        calc ∑ r ∈ Finset.Ico m P.k, gw (P.p ℓ) r * (if split P G h Δ ℓ x u v r then Δ else 0)
            = ∑ r ∈ F, gw (P.p ℓ) r * Δ := by
              rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun r _ => ?_
              split_ifs <;> simp
          _ ≤ ∑ r ∈ F, P.p ℓ * (1 - P.p ℓ) ^ m * Δ := by
              apply Finset.sum_le_sum; intro r hr
              have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hr).1).1
              exact mul_le_mul_of_nonneg_right (gw_le hp0.le hp1 this) (by linarith)
          _ = Δ * P.p ℓ * (1 - P.p ℓ) ^ m * F.card := by rw [Finset.sum_const]; simp; ring
      have hq0 : 0 ≤ (1 - P.p ℓ) ^ m := pow_nonneg (by linarith) _
      have hpt := DA.pair_touch P Δ X.card hN hε hε1 hΦ hΔ ℓ h1 hℓ dR hd0 F.card hcnt
        (by positivity)
      calc ∑ r ∈ Finset.Ico m P.k, gw (P.p ℓ) r * potR P Δ X u v dR ℓ (carveStep P G h Δ ℓ s x r)
          ≤ ∑ r ∈ Finset.Ico m P.k, gw (P.p ℓ) r *
              ((if split P G h Δ ℓ x u v r then Δ else 0) + Cap) :=
            Finset.sum_le_sum fun r hr =>
              mul_le_mul_of_nonneg_left (hval r hr) (gw_nonneg hp0.le hp1 r)
        _ = ∑ r ∈ Finset.Ico m P.k, gw (P.p ℓ) r * (if split P G h Δ ℓ x u v r then Δ else 0) +
              Cap * ∑ r ∈ Finset.Ico m P.k, gw (P.p ℓ) r := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun r _ => by ring
        _ ≤ Δ * P.p ℓ * (1 - P.p ℓ) ^ m * F.card + Cap * (1 - P.p ℓ) ^ m := by
            have := sum_gw_Ico hp0.le hp1 m P.k
            have := mul_le_mul_of_nonneg_left this hCap0
            linarith
        _ = (1 - P.p ℓ) ^ m * (Δ * P.p ℓ * F.card +
              DA.G0 P Δ * (Real.logb 2 X.card - Real.logb 2 (P.mu ℓ)) * dR) := by ring
        _ ≤ (1 - P.p ℓ) ^ m * T2 P Δ X dR := by
            unfold T2; exact mul_le_mul_of_nonneg_left hpt hq0
  · have hpot : potR P Δ X u v dR ℓ s = Fy P Δ u v dR s := by unfold potR; rw [if_neg huv]
    rw [hpot]
    apply ex_le_of_le
    intro R _
    obtain ⟨hle, hn⟩ := Fy_carve_decided dR hP.Δ0 huv ℓ x R (G := G) (h := h)
    unfold potR; rw [if_neg hn]
    exact ENNReal.ofReal_le_ofReal hle

lemma pair_down (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) (hd : 0 ≤ dR) {X M : Finset V} {u v : V} {ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) (s : SSPState V) (hI : SInv P G h Δ X M s) (hXc : 1 ≤ X.card) :
    potR P Δ X u v dR (ℓ - 1) s ≤ potR P Δ X u v dR ℓ s := by
  have hN := hP.N2; have hε := hP.eps0; have hε1 := hP.eps1; have hΦ := hP.Phi2
  have hT : 0 ≤ T2 P Δ X dR := by
    unfold T2
    have := DA.G0_nonneg P Δ hN hε hε1 hΦ hΔ
    have : 0 ≤ Real.logb 2 X.card := Real.logb_nonneg (by norm_num) (by exact_mod_cast hXc)
    positivity
  unfold potR
  split_ifs
  · exact Wg_down hN hε hε1 hΦ hT hI.act_sub h1 hℓ
  · exact le_rfl

lemma pair_fin (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) (hd : 0 ≤ dR) {X M : Finset V} {u v : V}
    (s : SSPState V) (hI : SInv P G h Δ X M s) :
    F2 P Δ u v (ENNReal.ofReal dR) (sspOutput s) ≤ ENNReal.ofReal (potR P Δ X u v dR 0 s) := by
  classical
  have hN := hP.N2; have hε := hP.eps0; have hε1 := hP.eps1; have hΦ := hP.Phi2
  have hnn : ∀ c ∈ s.carved, 0 ≤ (if u ∈ c.padded ∧ v ∈ c.padded then
      P.g c.cluster.card (Δ / 2) * dR else 0) := by
    intro c hc; split_ifs with hvc
    · exact mul_nonneg (DA.g_half_nonneg P Δ hN hε hε1 hΦ hΔ _
        (Finset.card_pos.mpr ⟨u, hI.c_pad c hc hvc.1⟩)) hd
    · exact le_rfl
  have hsum : ((s.carved.map (fun c : Carve V => (c.cluster, c.padded))).map
      (fun c : Finset V × Finset V => if u ∈ c.2 ∧ v ∈ c.2 then
        ENNReal.ofReal (P.g c.1.card (Δ / 2)) * ENNReal.ofReal dR else 0)).sum =
      ENNReal.ofReal ((s.carved.map (fun c => if u ∈ c.padded ∧ v ∈ c.padded then
        P.g c.cluster.card (Δ / 2) * dR else 0)).sum) := by
    rw [List.map_map, ← Excl.ofReal_list_sum _ _ hnn]
    congr 1; apply List.map_congr_left; intro c hc
    simp only [Function.comp]
    split_ifs with hvc
    · rw [ENNReal.ofReal_mul (DA.g_half_nonneg P Δ hN hε hε1 hΦ hΔ _
        (Finset.card_pos.mpr ⟨u, hI.c_pad c hc hvc.1⟩))]
    · simp
  unfold F2 sspOutput potR
  rw [List.map_append, List.sum_append, hsum]
  by_cases huv : u ∈ s.padded ∧ v ∈ s.padded
  · obtain ⟨hu, hv⟩ := huv
    have hne : s.active.Nonempty := ⟨u, hI.pad_sub hu⟩
    have hold := Excl.not_mem_old_padded hI (hI.pad_sub hu)
    rw [if_pos hne]
    have h0 : (s.carved.map (fun c => if u ∈ c.padded ∧ v ∈ c.padded then
        P.g c.cluster.card (Δ / 2) * dR else 0)).sum = 0 := by
      apply List.sum_eq_zero
      intro y hy; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      simp [hold c hc]
    rw [h0, ENNReal.ofReal_zero, zero_add]
    have hind : ¬ ((¬ ∃ c ∈ s.carved.map (fun c : Carve V => (c.cluster, c.padded)) ++
        [(s.active, s.padded)], u ∈ c.1 ∧ v ∈ c.1) ∧
        (∃ c ∈ s.carved.map (fun c : Carve V => (c.cluster, c.padded)) ++
          [(s.active, s.padded)], u ∈ c.2) ∧
        (∃ c ∈ s.carved.map (fun c : Carve V => (c.cluster, c.padded)) ++
          [(s.active, s.padded)], v ∈ c.2)) := fun hh =>
      hh.1 ⟨(s.active, s.padded), List.mem_append_right _ (List.mem_singleton_self _),
        hI.pad_sub hu, hI.pad_sub hv⟩
    rw [if_neg hind, add_zero]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hu, hv, and_self,
      if_true, add_zero]
    rw [← ENNReal.ofReal_mul (DA.g_half_nonneg P Δ hN hε hε1 hΦ hΔ _ (Finset.card_pos.mpr hne))]
    apply ENNReal.ofReal_le_ofReal
    rw [show Excl.budget P X 0 s = 0 by unfold Excl.budget; simp, Wg_zero _ 0]
    unfold T2
    exact mul_le_mul_of_nonneg_right (DA.g_half_le P Δ X.card hN hε hε1 hΦ hΔ _
      (Finset.card_pos.mpr hne) (Finset.card_le_card hI.act_sub)) hd
  · rw [if_neg huv]
    unfold Fy
    have hs0 : 0 ≤ (s.carved.map (fun c => if u ∈ c.padded ∧ v ∈ c.padded then
        P.g c.cluster.card (Δ / 2) * dR else 0)).sum :=
      List.sum_nonneg (fun y hy => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy; exact hnn c hc)
    rw [ENNReal.ofReal_add hs0 (by split_ifs <;> linarith)]
    have hlast : ∀ L' : List (Finset V × Finset V), L' = [] ∨ L' = [(s.active, s.padded)] →
        (L'.map (fun c : Finset V × Finset V => if u ∈ c.2 ∧ v ∈ c.2 then
          ENNReal.ofReal (P.g c.1.card (Δ / 2)) * ENNReal.ofReal dR else 0)).sum = 0 := by
      rintro L' (rfl | rfl)
      · simp
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        rw [if_neg huv]
    have hL' : (if s.active.Nonempty then [(s.active, s.padded)] else []) = [] ∨
        (if s.active.Nonempty then [(s.active, s.padded)] else []) = [(s.active, s.padded)] := by
      split_ifs <;> simp
    rw [hlast _ hL', add_zero]
    apply add_le_add le_rfl
    -- the split indicator
    by_cases hc : (¬ ∃ c ∈ s.carved.map (fun c : Carve V => (c.cluster, c.padded)) ++
        (if s.active.Nonempty then [(s.active, s.padded)] else []), u ∈ c.1 ∧ v ∈ c.1) ∧
        (∃ c ∈ s.carved.map (fun c : Carve V => (c.cluster, c.padded)) ++
          (if s.active.Nonempty then [(s.active, s.padded)] else []), u ∈ c.2) ∧
        (∃ c ∈ s.carved.map (fun c : Carve V => (c.cluster, c.padded)) ++
          (if s.active.Nonempty then [(s.active, s.padded)] else []), v ∈ c.2)
    · rw [if_pos hc]
      have hc' : (∀ c ∈ s.carved, ¬ (u ∈ c.cluster ∧ v ∈ c.cluster)) ∧
          (u ∈ s.padded ∨ ∃ c ∈ s.carved, u ∈ c.padded) ∧
          (v ∈ s.padded ∨ ∃ c ∈ s.carved, v ∈ c.padded) := by
        obtain ⟨h1, ⟨cu, hcu, hucu⟩, ⟨cv, hcv, hvcv⟩⟩ := hc
        refine ⟨fun c hc hh => h1 ⟨(c.cluster, c.padded),
          List.mem_append_left _ (List.mem_map_of_mem hc), hh⟩, ?_, ?_⟩
        · rcases List.mem_append.mp hcu with hcu | hcu
          · obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hcu; exact Or.inr ⟨d, hd', hucu⟩
          · split_ifs at hcu
            · rw [List.mem_singleton] at hcu; subst hcu; exact Or.inl hucu
            · simp at hcu
        · rcases List.mem_append.mp hcv with hcv | hcv
          · obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hcv; exact Or.inr ⟨d, hd', hvcv⟩
          · split_ifs at hcv
            · rw [List.mem_singleton] at hcv; subst hcv; exact Or.inl hvcv
            · simp at hcv
      rw [if_pos hc']
    · rw [if_neg hc]; exact bot_le

/-- **Per-scale expected-distortion bound** (the inductive step of Lemma 2). -/
theorem dist_ssp (hP : NumOK P Δ) (hΔ : 2 ≤ Δ) {rule : CenterRule V}
    (hrule : IsValidRule P G h rule) {X M : Finset V} (hM : M ⊆ X) {u v : V} (hu : u ∈ X)
    (hd0 : 0 ≤ dR) (hd : hopDist G h u v ≤ ENNReal.ofReal dR) :
    ex (singleScalePartition P G h rule X M Δ) (F2 P Δ u v (ENNReal.ofReal dR)) ≤
      ENNReal.ofReal (P.g X.card Δ) * ENNReal.ofReal dR := by
  have hN := hP.N2; have hε := hP.eps0; have hε1 := hP.eps1; have hΦ := hP.Phi2
  have hXc : 1 ≤ X.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hT : 0 ≤ T2 P Δ X dR := by
    unfold T2
    have := DA.G0_nonneg P Δ hN hε hε1 hΦ hΔ
    have : 0 ≤ Real.logb 2 X.card := Real.logb_nonneg (by norm_num) (by exact_mod_cast hXc)
    positivity
  refine le_trans (ssp_ex_le hP hrule hM (fun ℓ s => ENNReal.ofReal (potR P Δ X u v dR ℓ s)) _
    (fun ℓ h1 hℓ s hs hel => pair_step dR hP hΔ hrule hd0 hd h1 hℓ s hs hel)
    (fun ℓ h1 hℓ s hs => ENNReal.ofReal_le_ofReal (pair_down dR hP hΔ hd0 h1 hℓ s hs hXc))
    (fun s hs => pair_fin dR hP hΔ hd0 s hs)) ?_
  have hg0 : 0 ≤ P.g X.card Δ := by
    rw [DA.g_full P Δ X.card hN hε hε1 hΦ hΔ]
    have := DA.G0_nonneg P Δ hN hε hε1 hΦ hΔ
    have : 0 ≤ Real.logb 2 X.card := Real.logb_nonneg (by norm_num) (by exact_mod_cast hXc)
    have := P2.delta_pos P hN
    positivity
  rw [← ENNReal.ofReal_mul hg0]
  apply ENNReal.ofReal_le_ofReal
  unfold potR
  split_ifs with huv
  · refine le_trans (Wg_init hN hε hε1 hΦ hT hXc) (le_of_eq ?_)
    rw [DA.g_full P Δ X.card hN hε hε1 hΦ hΔ]; unfold T2; ring
  · unfold Fy
    simp only [List.map_nil, List.sum_nil, zero_add]
    rw [if_neg (by rintro ⟨-, hu', hv'⟩; exact huv ⟨by simpa using hu', by simpa using hv'⟩)]
    rw [DA.g_full P Δ X.card hN hε hε1 hΦ hΔ]
    have := DA.G0_nonneg P Δ hN hε hε1 hΦ hΔ
    have : 0 ≤ Real.logb 2 X.card := Real.logb_nonneg (by norm_num) (by exact_mod_cast hXc)
    have := P2.delta_pos P hN
    positivity

end Dist

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Independent sampling of a list -/

lemma seqPMF_support {α β : Type} (C : List α) (f : α → PMF β) :
    ∀ outs ∈ (seqPMF (C.map f)).support,
      outs.length = C.length ∧ ∀ p ∈ C.zip outs, p.2 ∈ (f p.1).support := by
  induction C with
  | nil =>
    intro outs h
    simp only [List.map_nil, seqPMF, PMF.support_pure, Set.mem_singleton_iff] at h
    subst h; simp
  | cons c C ih =>
    intro outs h
    simp only [List.map_cons, seqPMF] at h
    rw [PMF.mem_support_bind_iff] at h
    obtain ⟨a, ha, h⟩ := h
    rw [PMF.support_map] at h
    obtain ⟨l, hl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih l hl
    refine ⟨by simp [h1], ?_⟩
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ha
    · exact h2 p hp

lemma ex_seq_sum {α β : Type} (C : List α) (f : α → PMF β) (φ : α → β → ℝ≥0∞) :
    ex (seqPMF (C.map f)) (fun outs => ((C.zip outs).map (fun p => φ p.1 p.2)).sum) =
      (C.map (fun c => ex (f c) (φ c))).sum := by
  induction C with
  | nil => simp [seqPMF, ex_pure]
  | cons c C ih =>
    simp only [List.map_cons, seqPMF, List.sum_cons]
    rw [ex_bind]
    simp_rw [ex_map]
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    simp_rw [ex_add, ex_const, ih]

/-! ### The saved set of `combine` -/

lemma mem_foldr_union {γ δ : Type} (cs : List (γ × (δ × Finset V))) (x : V) :
    x ∈ cs.foldr (fun c acc => c.2.2 ∪ acc) ∅ ↔ ∃ c ∈ cs, x ∈ c.2.2 := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [List.foldr_cons, Finset.mem_union, ih]

lemma pw_unique {γ : Type} (l : List γ) (S : γ → Finset V)
    (hpw : l.Pairwise (fun a b => Disjoint (S a) (S b))) {a b : γ} (ha : a ∈ l) (hb : b ∈ l)
    {x : V} (hxa : x ∈ S a) (hxb : x ∈ S b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons c t ih =>
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd hxb (Finset.disjoint_left.mp (hpw.1 b hb') hxa)
    · subst hb'; exact absurd hxa (Finset.disjoint_left.mp (hpw.1 a ha') hxb)
    · exact ih hpw.2 ha' hb'

section Combine
variable {X : Finset V} {Δ : ℝ}

abbrev Zt (V : Type) := (Finset V × Finset V) × ((V → V → ℝ≥0∞) × Finset V)

lemma zip_pw {C : List (Finset V × Finset V)} {outs : List ((V → V → ℝ≥0∞) × Finset V)}
    (hlen : outs.length = C.length) (hpw : C.Pairwise (fun a b => Disjoint a.1 b.1)) :
    (C.zip outs).Pairwise (fun a b => Disjoint a.1.1 b.1.1) := by
  have : (C.zip outs).map Prod.fst = C := List.map_fst_zip (by omega)
  rw [← this, List.pairwise_map] at hpw
  exact hpw

lemma zip_exists {C : List (Finset V × Finset V)} {outs : List ((V → V → ℝ≥0∞) × Finset V)}
    (hlen : outs.length = C.length) {c : Finset V × Finset V} (hc : c ∈ C) :
    ∃ p ∈ C.zip outs, p.1 = c := by
  have : (C.zip outs).map Prod.fst = C := List.map_fst_zip (by omega)
  rw [← this] at hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  exact ⟨p, hp, rfl⟩

lemma combine_val_mem {Z : List (Zt V)} (hpw : Z.Pairwise (fun a b => Disjoint a.1.1 b.1.1))
    {u v : V} (hu : u ∈ X) (hv : v ∈ X) {p : Zt V} (hp : p ∈ Z) (hup : u ∈ p.1.1)
    (hvp : v ∈ p.1.1) : (combine X Δ Z).1 u v = p.2.1 u v := by
  unfold combine
  simp only [hu, hv, and_self, if_true]
  cases hq : Z.find? (fun c => decide (u ∈ c.1.1 ∧ v ∈ c.1.1)) with
  | none =>
    rw [List.find?_eq_none] at hq
    exact absurd (decide_eq_true ⟨hup, hvp⟩) (hq p hp)
  | some q =>
    simp only
    have hqZ := List.mem_of_find?_eq_some hq
    have hqp := List.find?_some hq
    simp only [decide_eq_true_eq] at hqp
    rw [pw_unique Z (fun a => a.1.1) hpw hqZ hp hqp.1 hup]

lemma combine_val_none {Z : List (Zt V)} {u v : V} (hu : u ∈ X) (hv : v ∈ X)
    (hnone : ∀ p ∈ Z, ¬ (u ∈ p.1.1 ∧ v ∈ p.1.1)) : (combine X Δ Z).1 u v = ENNReal.ofReal Δ := by
  unfold combine
  simp only [hu, hv, and_self, if_true]
  have : Z.find? (fun c => decide (u ∈ c.1.1 ∧ v ∈ c.1.1)) = none := by
    rw [List.find?_eq_none]; intro p hp; simpa using hnone p hp
  rw [this]

lemma combine_val_off {Z : List (Zt V)} {u v : V} (h : ¬ (u ∈ X ∧ v ∈ X)) :
    (combine X Δ Z).1 u v = ⊤ := by
  unfold combine; simp only [h, if_false]

lemma combine_saved {Z : List (Zt V)} (x : V) :
    x ∈ (combine X Δ Z).2 ↔ ∃ p ∈ Z, x ∈ p.2.2 := by
  unfold combine; exact mem_foldr_union Z x

end Combine

lemma hopDist_le_hopDiam (G : WGraph V) (a : ℕ) {X : Finset V} {u v : V} (hu : u ∈ X)
    (hv : v ∈ X) : hopDist G a u v ≤ hopDiam G a X := by
  unfold hopDiam
  exact le_trans (Finset.le_sup (f := fun v => hopDist G a u v) hv)
    (Finset.le_sup (f := fun u => X.sup fun v => hopDist G a u v) hu)

lemma hopDiam_le (G : WGraph V) (a : ℕ) {X : Finset V} {c : ℝ≥0∞}
    (h : ∀ u ∈ X, ∀ v ∈ X, hopDist G a u v ≤ c) : hopDiam G a X ≤ c := by
  unfold hopDiam
  exact Finset.sup_le fun u hu => Finset.sup_le fun v hv => h u hu v hv

lemma two_le_of_card {G : WGraph V} (hw : ∀ e ∈ G.graph.edgeSet, 2 ≤ G.w e) {a : ℕ}
    {X : Finset V} {Δ : ℝ} (hΔ : 0 ≤ Δ) (hX : 2 ≤ X.card) (hdiam : hopDiam G a X ≤ ENNReal.ofReal Δ) :
    2 ≤ Δ := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
  have h1 := hopDist_ge_of_ne G hw a huv
  have h2 := le_trans h1 (le_trans (hopDist_le_hopDiam G a hu hv) hdiam)
  rwa [ENNReal.ofReal_le_ofReal_iff hΔ] at h2

/-- Support invariants of a call of Algorithm 1. -/
structure RecOK (P : Fig2Params) (G : WGraph V) (h : ℕ) (X M : Finset V) (Δ : ℝ)
    (o : (V → V → ℝ≥0∞) × Finset V) : Prop where
  sav : o.2 ⊆ M
  off : ∀ u v, ¬ (u ∈ X ∧ v ∈ X) → o.1 u v = ⊤
  self : ∀ x ∈ X, o.1 x x = 0
  symm : ∀ u v, o.1 u v = o.1 v u
  ultra : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, o.1 x z ≤ max (o.1 x y) (o.1 y z)
  le : ∀ u ∈ X, ∀ v ∈ X, o.1 u v ≤ ENNReal.ofReal Δ
  hop : ∀ u ∈ X, ∀ v ∈ X, hopDist G (2 * P.k * (P.L + 1) * h) u v ≤ o.1 u v
  dist : ∀ u ∈ o.2, ∀ v ∈ X, o.1 u v ≤ ENNReal.ofReal ((P.k : ℝ) * 8 * P.L) * hopDist G h u v

lemma Sep.le_mul {P : Fig2Params} {G : WGraph V} {h : ℕ} {Δ : ℝ} (hP : NumOK P Δ) {u w : V}
    (hs : Sep P G h Δ u w) :
    ENNReal.ofReal Δ ≤ ENNReal.ofReal ((P.k : ℝ) * 8 * P.L) * hopDist G h u w := by
  unfold Sep at hs
  have hk : (0:ℝ) < P.k := by exact_mod_cast hP.kpos
  have hL : (0:ℝ) < P.L := by exact_mod_cast hP.Lpos
  have e : ENNReal.ofReal Δ =
      ENNReal.ofReal ((P.k : ℝ) * 8 * P.L) * ENNReal.ofReal (Δ / (8 * P.L * P.k)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
  rw [e]; exact mul_le_mul_right hs.le _

lemma leaf_ok {P : Fig2Params} {G : WGraph V} {h : ℕ} {X M : Finset V} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hX : X.card ≤ 1) (hM : M ⊆ X) : RecOK P G h X M Δ (leafMetric X, M) := by
  have uniq : ∀ u ∈ X, ∀ v ∈ X, u = v := fun u hu v hv => Finset.card_le_one.mp hX u hu v hv
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv; simp [leafMetric, huv]
  · intro x hx; simp [leafMetric, hx]
  · intro u v; unfold leafMetric; by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;> simp [hu, hv]
  · intro x hx y hy z hz; simp [leafMetric, hx, hz]
  · intro u hu v hv; simp [leafMetric, hu, hv]
  · intro u hu v hv; rw [uniq u hu v hv, hopDist_self]; exact bot_le
  · intro u hu v hv; rw [uniq u (hM hu) v hv]; simp [leafMetric, hv]

lemma combine_ok {P : Fig2Params} {G : WGraph V} {h : ℕ} {X M : Finset V} {Δ : ℝ}
    (hP : NumOK P Δ) {C : List (Finset V × Finset V)} (hC : OutOK P G h Δ X M C)
    {outs : List ((V → V → ℝ≥0∞) × Finset V)} (hlen : outs.length = C.length)
    (hch : ∀ p ∈ C.zip outs, RecOK P G h p.1.1 p.1.2 (Δ / 2) p.2)
    (hdiam : hopDiam G (2 * P.k * (P.L + 1) * h) X ≤ ENNReal.ofReal Δ) :
    RecOK P G h X M Δ (combine X Δ (C.zip outs)) := by
  set Z := C.zip outs
  have hpw : Z.Pairwise (fun a b => Disjoint a.1.1 b.1.1) := zip_pw hlen hC.pw
  have hZC : ∀ p ∈ Z, p.1 ∈ C := fun p hp => (List.of_mem_zip hp).1
  have cl : ∀ x ∈ X, ∃ p ∈ Z, x ∈ p.1.1 := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hC.cover x hx
    obtain ⟨p, hp, rfl⟩ := zip_exists hlen hc
    exact ⟨p, hp, hxc⟩
  have hΔ2 : ENNReal.ofReal (Δ / 2) ≤ ENNReal.ofReal Δ :=
    ENNReal.ofReal_le_ofReal (by linarith [hP.Δ0])
  -- value of `combine` in terms of the cluster of `u`
  have val : ∀ u ∈ X, ∀ v ∈ X, ∀ p ∈ Z, u ∈ p.1.1 →
      (combine X Δ Z).1 u v = if v ∈ p.1.1 then p.2.1 u v else ENNReal.ofReal Δ := by
    intro u hu v hv p hp hup
    split_ifs with hvp
    · exact combine_val_mem hpw hu hv hp hup hvp
    · apply combine_val_none hu hv
      intro q hq hh
      exact hvp (pw_unique Z (fun a => a.1.1) hpw hq hp hh.1 hup ▸ hh.2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := (combine_saved x).mp hx
    exact hC.padM p.1 (hZC p hp) ((hch p hp).sav hxp)
  · intro u v huv; exact combine_val_off huv
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := cl x hx
    rw [combine_val_mem hpw hx hx hp hxp hxp]; exact (hch p hp).self x hxp
  · intro u v
    by_cases huv : u ∈ X ∧ v ∈ X
    · obtain ⟨p, hp, hup⟩ := cl u huv.1
      rw [val u huv.1 v huv.2 p hp hup]
      by_cases hvp : v ∈ p.1.1
      · rw [if_pos hvp, val v huv.2 u huv.1 p hp hvp, if_pos hup]; exact (hch p hp).symm u v
      · rw [if_neg hvp]
        obtain ⟨q, hq, hvq⟩ := cl v huv.2
        rw [val v huv.2 u huv.1 q hq hvq, if_neg]
        intro huq; exact hvp (pw_unique Z (fun a => a.1.1) hpw hq hp huq hup ▸ hvq)
    · rw [combine_val_off huv, combine_val_off (fun hh => huv ⟨hh.2, hh.1⟩)]
  · intro x hx y hy z hz
    obtain ⟨p, hp, hxp⟩ := cl x hx
    obtain ⟨q, hq, hyq⟩ := cl y hy
    rw [val x hx z hz p hp hxp, val x hx y hy p hp hxp, val y hy z hz q hq hyq]
    by_cases hzp : z ∈ p.1.1
    · rw [if_pos hzp]
      by_cases hyp : y ∈ p.1.1
      · have hqp : q = p := pw_unique Z (fun a => a.1.1) hpw hq hp hyq hyp
        subst hqp
        rw [if_pos hyp, if_pos hzp]; exact (hch q hq).ultra x hxp y hyp z hzp
      · rw [if_neg hyp]
        exact le_trans (le_trans ((hch p hp).le x hxp z hzp) hΔ2) (le_max_left _ _)
    · rw [if_neg hzp]
      by_cases hyp : y ∈ p.1.1
      · have hqp : q = p := pw_unique Z (fun a => a.1.1) hpw hq hp hyq hyp
        subst hqp
        rw [if_neg hzp]; exact le_max_right _ _
      · rw [if_neg hyp]; exact le_max_left _ _
  · intro u hu v hv
    obtain ⟨p, hp, hup⟩ := cl u hu
    rw [val u hu v hv p hp hup]
    split_ifs with hvp
    · exact le_trans ((hch p hp).le u hup v hvp) hΔ2
    · exact le_rfl
  · intro u hu v hv
    obtain ⟨p, hp, hup⟩ := cl u hu
    rw [val u hu v hv p hp hup]
    split_ifs with hvp
    · exact (hch p hp).hop u hup v hvp
    · exact le_trans (hopDist_le_hopDiam G _ hu hv) hdiam
  · intro u hu v hv
    obtain ⟨p, hp, hup⟩ := (combine_saved u).mp hu
    have hupc : u ∈ p.1.2 := (hch p hp).sav hup
    have hup1 : u ∈ p.1.1 := hC.pad p.1 (hZC p hp) hupc
    have huX : u ∈ X := hC.sub p.1 (hZC p hp) hup1
    rw [val u huX v hv p hp hup1]
    split_ifs with hvp
    · exact (hch p hp).dist u hup v hvp
    · exact Sep.le_mul hP (hC.sep p.1 (hZC p hp) u hupc v hv hvp)

theorem rec_ok {P : Fig2Params} {G : WGraph V} {h : ℕ} (hN : 2 ≤ P.N) (hε : 0 < P.ε)
    (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ) (hw : ∀ e ∈ G.graph.edgeSet, 2 ≤ G.w e) {rule : CenterRule V}
    (hrule : IsValidRule P G h rule) :
    ∀ (fuel : ℕ) (X M : Finset V) (Δ : ℝ), M ⊆ X → X.card ≤ P.N → 0 ≤ Δ → Δ < 2 ^ fuel →
      hopDiam G (2 * P.k * (P.L + 1) * h) X ≤ ENNReal.ofReal Δ →
      ∀ o ∈ (hseFuel P G h rule fuel X M Δ).support, RecOK P G h X M Δ o := by
  have hNum : ∀ Δ : ℝ, 0 ≤ Δ → NumOK P Δ := fun Δ hΔ => ⟨hN, hε, hε1, hΦ, hΔ⟩
  intro fuel
  induction fuel with
  | zero =>
    intro X M Δ hM hXN hΔ hΔf hdiam o ho
    rw [hseFuel] at ho
    split_ifs at ho with hX
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho; exact leaf_ok hΔ hX hM
    · exfalso
      have := two_le_of_card hw hΔ (by omega) hdiam
      simp at hΔf; linarith
  | succ fuel ih =>
    intro X M Δ hM hXN hΔ hΔf hdiam o ho
    rw [hseFuel] at ho
    split_ifs at ho with hX
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho; exact leaf_ok hΔ hX hM
    · rw [PMF.mem_support_bind_iff] at ho
      obtain ⟨C, hC, ho⟩ := ho
      rw [PMF.support_map] at ho
      obtain ⟨outs, houts, rfl⟩ := ho
      have hCok := ssp_outOK (hNum Δ hΔ) hrule hM hXN C hC
      obtain ⟨hlen, hsupp⟩ := seqPMF_support C _ outs houts
      apply combine_ok (hNum Δ hΔ) hCok hlen _ hdiam
      intro p hp
      have hpC : p.1 ∈ C := (List.of_mem_zip hp).1
      refine ih p.1.1 p.1.2 (Δ / 2) (hCok.pad p.1 hpC)
        (le_trans (Finset.card_le_card (hCok.sub p.1 hpC)) hXN) (by linarith)
        (by rw [pow_succ] at hΔf; linarith)
        (hopDiam_le G _ (hCok.diam p.1 hpC)) p.2 (hsupp p hp)

end HopRamsey.FZ



open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

lemma list_sum_le {α : Type*} (l : List α) (f g : α → ℝ≥0∞) (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem a hb))

lemma le_list_sum {α : Type*} (l : List α) (f : α → ℝ≥0∞) {a : α} (ha : a ∈ l) :
    f a ≤ (l.map f).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem ha)

variable {P : Fig2Params} {G : WGraph V} {h : ℕ}

/-- The recursion of Lemma 1. -/
theorem lemma1_rec (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ)
    (hw : ∀ e ∈ G.graph.edgeSet, 2 ≤ G.w e) {rule : CenterRule V}
    (hrule : IsValidRule P G h rule) :
    ∀ (fuel : ℕ) (X M : Finset V) (Δ : ℝ), M ⊆ X → X.card ≤ P.N → 0 ≤ Δ → Δ < 2 ^ fuel →
      hopDiam G (2 * P.k * (P.L + 1) * h) X ≤ ENNReal.ofReal Δ → ∀ v ∈ M,
      ex (hseFuel P G h rule fuel X M Δ) (fun o => if v ∈ o.2 then 0 else 1) ≤
        ENNReal.ofReal (P.f X.card Δ) := by
  have hNum : ∀ Δ : ℝ, 0 ≤ Δ → NumOK P Δ := fun Δ hΔ => ⟨hN, hε, hε1, hΦ, hΔ⟩
  intro fuel
  induction fuel with
  | zero =>
    intro X M Δ hM hXN hΔ hΔf hdiam v hv
    rw [hseFuel]
    split_ifs with hX
    · rw [ex_pure]; simp [hv]
    · exfalso
      have := two_le_of_card hw hΔ (by omega) hdiam
      simp at hΔf; linarith
  | succ fuel ih =>
    intro X M Δ hM hXN hΔ hΔf hdiam v hv
    rw [hseFuel]
    split_ifs with hX
    · rw [ex_pure]; simp [hv]
    · have hΔ2 := two_le_of_card hw hΔ (by omega) hdiam
      rw [ex_bind]
      refine le_trans (ex_mono _ (fun C hC => ?_)) (Excl.excl_ssp (hNum Δ hΔ) hΔ2 hrule hM hv)
      have hCok := ssp_outOK (hNum Δ hΔ) hrule hM hXN C hC
      rw [ex_map]
      set rec := fun c : Finset V × Finset V => hseFuel P G h rule fuel c.1 c.2 (Δ / 2)
      -- pointwise bound
      have hpt : ∀ outs ∈ (seqPMF (C.map rec)).support,
          (if v ∈ (combine X Δ (C.zip outs)).2 then (0 : ℝ≥0∞) else 1) ≤
            ((C.zip outs).map (fun p => if v ∈ p.1.2 then
              (if v ∈ p.2.2 then (0 : ℝ≥0∞) else 1) else 0)).sum +
            (if ∀ c ∈ C, v ∉ c.2 then 1 else 0) := by
        intro outs houts
        obtain ⟨hlen, -⟩ := seqPMF_support C rec outs houts
        by_cases h1 : v ∈ (combine X Δ (C.zip outs)).2
        · rw [if_pos h1]; exact bot_le
        · rw [if_neg h1]
          by_cases h2 : ∀ c ∈ C, v ∉ c.2
          · rw [if_pos h2]; exact le_add_self
          · rw [if_neg h2, add_zero]
            push Not at h2
            obtain ⟨c, hc, hvc⟩ := h2
            obtain ⟨p, hp, rfl⟩ := zip_exists hlen hc
            have hvp : v ∉ p.2.2 := fun hh => h1 ((combine_saved v).mpr ⟨p, hp, hh⟩)
            refine le_trans ?_ (le_list_sum _ _ hp)
            simp [hvc, hvp]
      refine le_trans (ex_mono _ hpt) ?_
      rw [ex_add, ex_const, ex_seq_sum C rec (fun c o => if v ∈ c.2 then
        (if v ∈ o.2 then (0 : ℝ≥0∞) else 1) else 0)]
      unfold Excl.F1
      apply add_le_add _ le_rfl
      apply list_sum_le
      intro c hc
      split_ifs with hvc
      · have hcX : c.1 ⊆ X := hCok.sub c hc
        refine le_trans (le_of_eq ?_) (ih c.1 c.2 (Δ / 2) (hCok.pad c hc)
          (le_trans (Finset.card_le_card hcX) hXN) (by linarith)
          (by rw [pow_succ] at hΔf; linarith) (hopDiam_le G _ (hCok.diam c hc)) v hvc)
        unfold ex; congr 1
      · unfold ex; simp

lemma g_pos {P : Fig2Params} (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ)
    {Δ : ℝ} (hΔ : 2 ≤ Δ) {n : ℕ} (hn : 2 ≤ n) : 0 < P.g n Δ := by
  rw [DA.g_full P Δ n hN hε hε1 hΦ hΔ]
  have h1 : 2 ^ 8 * (P.L : ℝ) ≤ DA.G0 P Δ := DA.G0_ge P Δ hN hε hε1 hΦ hΔ
  have hL : (1:ℝ) ≤ P.L := by exact_mod_cast P2.L_pos P hN
  have h2 : 0 < Real.logb 2 n := Real.logb_pos (by norm_num) (by exact_mod_cast hn)
  have := P2.delta_pos P hN
  have : 0 < DA.G0 P Δ := by linarith
  positivity

/-- The recursion of Lemma 2. -/
theorem lemma2_rec (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ)
    (hw : ∀ e ∈ G.graph.edgeSet, 2 ≤ G.w e) {rule : CenterRule V}
    (hrule : IsValidRule P G h rule) :
    ∀ (fuel : ℕ) (X M : Finset V) (Δ : ℝ), M ⊆ X → X.card ≤ P.N → 0 ≤ Δ → Δ < 2 ^ fuel →
      hopDiam G (2 * P.k * (P.L + 1) * h) X ≤ ENNReal.ofReal Δ → ∀ u ∈ X, ∀ v ∈ X,
      ex (hseFuel P G h rule fuel X M Δ) (fun o => if u ∈ o.2 ∧ v ∈ o.2 then o.1 u v else 0) ≤
        ENNReal.ofReal (P.g X.card Δ) * hopDist G h u v := by
  have hNum : ∀ Δ : ℝ, 0 ≤ Δ → NumOK P Δ := fun Δ hΔ => ⟨hN, hε, hε1, hΦ, hΔ⟩
  have leafcase : ∀ (X M : Finset V) (Δ : ℝ), X.card ≤ 1 → ∀ u ∈ X, ∀ v ∈ X,
      ex (PMF.pure (leafMetric X, M)) (fun o => if u ∈ o.2 ∧ v ∈ o.2 then o.1 u v else 0) = 0 := by
    intro X M Δ hX u hu v hv
    rw [ex_pure]
    have := Finset.card_le_one.mp hX u hu v hv
    subst this; simp [leafMetric, hu]
  intro fuel
  induction fuel with
  | zero =>
    intro X M Δ hM hXN hΔ hΔf hdiam u hu v hv
    rw [hseFuel]
    split_ifs with hX
    · rw [leafcase X M Δ hX u hu v hv]; exact bot_le
    · exfalso
      have := two_le_of_card hw hΔ (by omega) hdiam
      simp at hΔf; linarith
  | succ fuel ih =>
    intro X M Δ hM hXN hΔ hΔf hdiam u hu v hv
    rw [hseFuel]
    split_ifs with hX
    · rw [leafcase X M Δ hX u hu v hv]; exact bot_le
    · have hΔ2 := two_le_of_card hw hΔ (by omega) hdiam
      by_cases htop : hopDist G h u v = ⊤
      · rw [htop, ENNReal.mul_top (by
          simpa using g_pos hN hε hε1 hΦ hΔ2 (by omega : 2 ≤ X.card))]
        exact le_top
      set dR := (hopDist G h u v).toReal
      have hdeq : hopDist G h u v = ENNReal.ofReal dR := (ENNReal.ofReal_toReal htop).symm
      have hd0 : 0 ≤ dR := ENNReal.toReal_nonneg
      rw [hdeq, ex_bind]
      refine le_trans (ex_mono _ (fun C hC => ?_))
        (Dist.dist_ssp dR (hNum Δ hΔ) hΔ2 hrule hM hu hd0 hdeq.le)
      have hCok := ssp_outOK (hNum Δ hΔ) hrule hM hXN C hC
      rw [ex_map]
      set rec := fun c : Finset V × Finset V => hseFuel P G h rule fuel c.1 c.2 (Δ / 2)
      have hchild : ∀ c ∈ C, ∀ o ∈ (rec c).support, RecOK P G h c.1 c.2 (Δ / 2) o := by
        intro c hc o ho
        exact rec_ok hN hε hε1 hΦ hw hrule fuel c.1 c.2 (Δ / 2) (hCok.pad c hc)
          (le_trans (Finset.card_le_card (hCok.sub c hc)) hXN) (by linarith)
          (by rw [pow_succ] at hΔf; linarith) (hopDiam_le G _ (hCok.diam c hc)) o ho
      set ψ : Finset V × Finset V → (V → V → ℝ≥0∞) × Finset V → ℝ≥0∞ := fun c o =>
        if u ∈ c.1 ∧ v ∈ c.1 then (if u ∈ o.2 ∧ v ∈ o.2 then o.1 u v else 0) else 0
      have hpt : ∀ outs ∈ (seqPMF (C.map rec)).support,
          (if u ∈ (combine X Δ (C.zip outs)).2 ∧ v ∈ (combine X Δ (C.zip outs)).2 then
            (combine X Δ (C.zip outs)).1 u v else 0) ≤
            ((C.zip outs).map (fun p => ψ p.1 p.2)).sum +
            (if (¬ ∃ c ∈ C, u ∈ c.1 ∧ v ∈ c.1) ∧ (∃ c ∈ C, u ∈ c.2) ∧ (∃ c ∈ C, v ∈ c.2)
              then ENNReal.ofReal Δ else 0) := by
        intro outs houts
        obtain ⟨hlen, hsupp⟩ := seqPMF_support C rec outs houts
        set Z := C.zip outs
        have hpw : Z.Pairwise (fun a b => Disjoint a.1.1 b.1.1) := zip_pw hlen hCok.pw
        have hZC : ∀ p ∈ Z, p.1 ∈ C := fun p hp => (List.of_mem_zip hp).1
        have hok : ∀ p ∈ Z, RecOK P G h p.1.1 p.1.2 (Δ / 2) p.2 :=
          fun p hp => hchild p.1 (hZC p hp) p.2 (hsupp p hp)
        by_cases hsav : u ∈ (combine X Δ Z).2 ∧ v ∈ (combine X Δ Z).2
        · rw [if_pos hsav]
          obtain ⟨pu, hpu, hupu⟩ := (combine_saved u).mp hsav.1
          obtain ⟨pv, hpv, hvpv⟩ := (combine_saved v).mp hsav.2
          have hu1 : u ∈ pu.1.1 := hCok.pad pu.1 (hZC pu hpu) ((hok pu hpu).sav hupu)
          have hv1 : v ∈ pv.1.1 := hCok.pad pv.1 (hZC pv hpv) ((hok pv hpv).sav hvpv)
          by_cases hvu : v ∈ pu.1.1
          · have hpq : pv = pu := pw_unique Z (fun a => a.1.1) hpw hpv hpu hv1 hvu
            subst hpq
            rw [combine_val_mem hpw hu hv hpu hu1 hv1]
            refine le_trans ?_ le_self_add
            refine le_trans (le_of_eq ?_) (le_list_sum _ (fun p => ψ p.1 p.2) hpu)
            simp only [ψ, hu1, hv1, and_self, if_true, hupu, hvpv]
          · have hnone : ∀ p ∈ Z, ¬ (u ∈ p.1.1 ∧ v ∈ p.1.1) := by
              intro p hp hh
              have := pw_unique Z (fun a => a.1.1) hpw hp hpu hh.1 hu1
              subst this; exact hvu hh.2
            rw [combine_val_none hu hv hnone]
            refine le_trans ?_ le_add_self
            rw [if_pos]
            refine ⟨?_, ⟨pu.1, hZC pu hpu, (hok pu hpu).sav hupu⟩,
              ⟨pv.1, hZC pv hpv, (hok pv hpv).sav hvpv⟩⟩
            rintro ⟨c, hc, hh⟩
            obtain ⟨p, hp, rfl⟩ := zip_exists hlen hc
            exact hnone p hp hh
        · rw [if_neg hsav]; exact bot_le
      refine le_trans (ex_mono _ hpt) ?_
      rw [ex_add, ex_const, ex_seq_sum C rec ψ]
      unfold Dist.F2
      apply add_le_add _ le_rfl
      apply list_sum_le
      intro c hc
      by_cases huv1 : u ∈ c.1 ∧ v ∈ c.1
      · have hcX : c.1 ⊆ X := hCok.sub c hc
        have hIH := ih c.1 c.2 (Δ / 2) (hCok.pad c hc)
          (le_trans (Finset.card_le_card hcX) hXN) (by linarith)
          (by rw [pow_succ] at hΔf; linarith) (hopDiam_le G _ (hCok.diam c hc)) u huv1.1 v huv1.2
        rw [hdeq] at hIH
        have hψ : ex (rec c) (ψ c) =
            ex (rec c) (fun o => if u ∈ o.2 ∧ v ∈ o.2 then o.1 u v else 0) := by
          unfold ex; congr 1; ext o; simp only [ψ, huv1, and_self, if_true]
        rw [hψ]
        by_cases huv2 : u ∈ c.2 ∧ v ∈ c.2
        · rw [if_pos huv2]; exact hIH
        · rw [if_neg huv2]
          apply ex_le_of_le
          intro o ho
          have := (hchild c hc o ho).sav
          rw [if_neg (fun hh => huv2 ⟨this hh.1, this hh.2⟩)]
      · have : ex (rec c) (ψ c) = 0 := by
          unfold ex; simp [ψ, huv1]
        rw [this]; exact bot_le

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable {P : Fig2Params} {G : WGraph V} {h : ℕ}

lemma fuel_ok {Δ : ℝ} (hΔ : 1 ≤ Δ) : Δ < 2 ^ (⌈Real.logb 2 Δ⌉₊ + 2) := by
  have h0 : 0 ≤ Real.logb 2 Δ := Real.logb_nonneg (by norm_num) hΔ
  calc Δ = (2 : ℝ) ^ (Real.logb 2 Δ) := (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
    _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 Δ⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
    _ = 2 ^ ⌈Real.logb 2 Δ⌉₊ := by norm_cast
    _ < 2 ^ (⌈Real.logb 2 Δ⌉₊ + 2) := pow_lt_pow_right₀ (by norm_num) (by omega)

structure StdHyp (P : Fig2Params) (G : WGraph V) (h : ℕ) : Prop where
  N2 : 2 ≤ P.N
  eps0 : 0 < P.ε
  eps1 : P.ε < 1
  Phi2 : 2 ≤ P.Φ
  w2 : ∀ e ∈ G.graph.edgeSet, 2 ≤ G.w e
  NV : P.N = Fintype.card V

lemma StdHyp.of (hS : Standing P G h) : StdHyp P G h :=
  ⟨hS.2.1, hS.2.2.2.2.1, hS.2.2.2.2.2.1, hS.2.2.2.1, hS.2.2.1, hS.1⟩

lemma StdHyp.card_le (hS : StdHyp P G h) (X : Finset V) : X.card ≤ P.N := by
  rw [hS.NV]; exact Finset.card_le_univ X

theorem lemma_1' (hS : Standing P G h) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    (X M : Finset V) (Δ : ℝ) (hX : CallInv P G h X M Δ) (v : V) (hv : v ∈ M) :
    (hopStochEmbedding P G h rule X M Δ).toOuterMeasure {o | v ∉ o.2} ≤
      ENNReal.ofReal (P.f X.card Δ) := by
  classical
  have hs := StdHyp.of hS
  obtain ⟨-, hM, hΔ, hdiam⟩ := hX
  rw [toOuterMeasure_eq_ex]
  unfold hopStochEmbedding
  refine le_trans (le_of_eq ?_) (lemma1_rec hs.N2 hs.eps0 hs.eps1 hs.Phi2 hs.w2 hrule _ X M Δ hM
    (hs.card_le X) (by linarith) (fuel_ok hΔ) hdiam v hv)
  unfold ex; congr 1; ext o; by_cases hvo : v ∈ o.2 <;> simp [hvo]

theorem lemma_2' (hS : Standing P G h) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    (X M : Finset V) (Δ : ℝ) (hX : CallInv P G h X M Δ) (u v : V) (hu : u ∈ X) (hv : v ∈ X) :
    (∑' o, (hopStochEmbedding P G h rule X M Δ) o * (if u ∈ o.2 ∧ v ∈ o.2 then o.1 u v else 0)) ≤
      ENNReal.ofReal (P.g X.card Δ) * hopDist G h u v := by
  have hs := StdHyp.of hS
  obtain ⟨-, hM, hΔ, hdiam⟩ := hX
  exact lemma2_rec hs.N2 hs.eps0 hs.eps1 hs.Phi2 hs.w2 hrule _ X M Δ hM
    (hs.card_le X) (by linarith) (fuel_ok hΔ) hdiam u hu v hv

theorem rec_ok' (hS : Standing P G h) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    (X M : Finset V) (Δ : ℝ) (hX : CallInv P G h X M Δ) :
    ∀ o ∈ (hopStochEmbedding P G h rule X M Δ).support, RecOK P G h X M Δ o := by
  have hs := StdHyp.of hS
  obtain ⟨-, hM, hΔ, hdiam⟩ := hX
  exact rec_ok hs.N2 hs.eps0 hs.eps1 hs.Phi2 hs.w2 hrule _ X M Δ hM
    (hs.card_le X) (by linarith) (fuel_ok hΔ) hdiam

theorem claim_2' (hS : Standing P G h) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    (X M : Finset V) (Δ : ℝ) (hX : CallInv P G h X M Δ) :
    ∀ o ∈ (hopStochEmbedding P G h rule X M Δ).support, ∀ u ∈ o.2, ∀ v ∈ X,
      o.1 u v ≤ ENNReal.ofReal ((P.k : ℝ) * 8 * P.L) * hopDist G h u v :=
  fun o ho => (rec_ok' hS hrule X M Δ hX o ho).dist

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
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

def IsUlt (ρ : V → V → ℝ≥0∞) : Prop :=
  (∀ x, ρ x x = 0) ∧ (∀ x y, ρ x y = ρ y x) ∧ (∀ x y z, ρ x z ≤ max (ρ x y) (ρ y z))

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

open Classical in
/-- The HST with leaf set `V` and leaf ultrametric `ρ` (when `ρ` is one). -/
noncomputable def toHST (ρ : V → V → ℝ≥0∞) : HST V :=
  if hρ : IsUlt ρ then
    { leaves := Set.univ
      ρ := ρ
      self := fun x _ => hρ.1 x
      symm := hρ.2.1
      ultra := fun x _ y _ z _ => hρ.2.2 x y z
      off := by intro u v huv; simp at huv }
  else discreteHST

lemma toHST_leaves (ρ : V → V → ℝ≥0∞) : (toHST ρ).leaves = Set.univ := by
  unfold toHST; split_ifs <;> rfl

lemma toHST_rho {ρ : V → V → ℝ≥0∞} (hρ : IsUlt ρ) : (toHST ρ).ρ = ρ := by
  unfold toHST; rw [dif_pos hρ]

lemma PMF.map_congr_support {α β : Type*} (p : PMF α) {f g : α → β}
    (hfg : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  congr 1; ext a
  by_cases ha : a ∈ p.support
  · rw [hfg a ha]
  · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]

lemma hopDiam_mono (G : WGraph V) {a b : ℕ} (hab : a ≤ b) (X : Finset V) :
    hopDiam G b X ≤ hopDiam G a X := by
  unfold hopDiam
  exact Finset.sup_mono_fun fun u _ => Finset.sup_mono_fun fun v _ => hopDist_mono G hab u v

variable {P : Fig2Params} {G : WGraph V} {h : ℕ}

lemma f_le_eps (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ) :
    P.f P.N P.Φ ≤ P.ε := by
  have hk : (0:ℝ) < P.k := by exact_mod_cast P2.k_pos P hN hε hε1 hΦ
  have hkge : (4 / P.ε) * (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) *
      (Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ) ≤ P.k := Nat.le_ceil _
  unfold Fig2Params.f
  set A := (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) *
      (Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ)
  have e1 : 4 / (P.k : ℝ) * (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) *
      (Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ) = 4 * A / P.k := by
    simp only [A]; ring
  have e2 : (4 / P.ε) * (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) *
      (Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ) = 4 * A / P.ε := by
    simp only [A]; ring
  rw [e1]; rw [e2] at hkge
  rw [div_le_iff₀ hk]
  rw [div_le_iff₀ hε] at hkge
  linarith

theorem finite_case' (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (hΦfin : hopDiam G h Finset.univ ≠ ⊤) (hΦ : P.Φ = (hopDiam G h Finset.univ).toReal) :
    ∃ D : PMF (HST V × Finset V), (∀ x ∈ D.support, x.1.leaves = Set.univ) ∧
      D.map (fun x => (x.1.ρ, x.2)) =
        hopStochEmbedding P G h rule Finset.univ Finset.univ P.Φ ∧
      HasHopStretch G h D (2 * P.k * (P.L + 1)) ∧
      HasDistortion G h D ((P.k : ℝ) * 8 * P.L) ∧
      HasExclusion D (P.f P.N P.Φ) ∧ P.f P.N P.Φ ≤ P.ε ∧
      HasExpectedDistortion G h D (P.g P.N P.Φ) := by
  have hs := StdHyp.of hS
  have hcard : (Finset.univ : Finset V).card = P.N := by rw [hs.NV]; rfl
  have hinv : CallInv P G h Finset.univ Finset.univ P.Φ := by
    refine ⟨?_, le_rfl, by linarith [hs.Phi2], ?_⟩
    · rw [Finset.univ_nonempty_iff]
      have : 0 < Fintype.card V := by rw [← hs.NV]; linarith [hs.N2]
      exact Fintype.card_pos_iff.mp this
    · refine le_trans (hopDiam_mono G (a := h) ?_ _) ?_
      · have := P2.k_pos P hs.N2 hs.eps0 hs.eps1 hs.Phi2
        have : 1 ≤ 2 * P.k * (P.L + 1) := by nlinarith
        nlinarith
      · rw [hΦ, ENNReal.ofReal_toReal hΦfin]
  set E := hopStochEmbedding P G h rule Finset.univ Finset.univ P.Φ with hE
  have hok := rec_ok' hS hrule _ _ _ hinv
  have hult : ∀ o ∈ E.support, IsUlt o.1 := by
    intro o ho
    obtain hr := hok o ho
    exact ⟨fun x => hr.self x (Finset.mem_univ x), hr.symm,
      fun x y z => hr.ultra x (Finset.mem_univ x) y (Finset.mem_univ y) z (Finset.mem_univ z)⟩
  refine ⟨E.map (fun o => (toHST o.1, o.2)), ?_, ?_, ?_, ?_, ?_, f_le_eps hs.N2 hs.eps0 hs.eps1
    hs.Phi2, ?_⟩
  · intro x hx
    rw [PMF.support_map] at hx
    obtain ⟨o, -, rfl⟩ := hx
    exact toHST_leaves _
  · rw [PMF.map_comp]
    conv_rhs => rw [← PMF.map_id E]
    apply PMF.map_congr_support
    intro o ho
    simp only [Function.comp, toHST_rho (hult o ho), id]
  · intro x hx u v
    rw [PMF.support_map] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    simp only [toHST_rho (hult o ho)]
    rw [hopDist_symm, show 2 * P.k * (P.L + 1) * h = 2 * P.k * (P.L + 1) * h from rfl]
    exact (hok o ho).hop v (Finset.mem_univ v) u (Finset.mem_univ u)
  · intro x hx u hu v
    rw [PMF.support_map] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    simp only [toHST_rho (hult o ho)] at hu ⊢
    rw [(hok o ho).symm]
    exact (hok o ho).dist u hu v (Finset.mem_univ v)
  · intro v
    rw [PMF.toOuterMeasure_map_apply]
    have := lemma_1' hS hrule _ _ _ hinv v (Finset.mem_univ v)
    rw [hcard] at this
    exact le_trans (le_of_eq (by congr 1)) this
  · intro u v
    have := lemma_2' hS hrule _ _ _ hinv u v (Finset.mem_univ u) (Finset.mem_univ v)
    rw [hcard] at this
    refine le_trans (le_of_eq ?_) this
    have := ex_map E (fun o => (toHST o.1, o.2))
      (fun x => if u ∈ x.2 ∧ v ∈ x.2 then x.1.ρ u v else 0)
    unfold ex at this
    rw [this]
    congr 1; ext o
    by_cases ho : o ∈ E.support
    · simp only [toHST_rho (hult o ho)]; rfl
    · rw [PMF.mem_support_iff, not_not] at ho; simp [ho]; exact fun _ _ => Or.inl ho

end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]
variable {P : Fig2Params} {G : WGraph V} {h : ℕ} {Δ : ℝ}

/-- Light invariant of Algorithm 2 (no assumption on the padded set). -/
def SInvL (P : Fig2Params) (G : WGraph V) (h : ℕ) (Δ : ℝ) (X : Finset V) (s : SSPState V) : Prop :=
  s.active ⊆ X ∧ ∀ c ∈ s.carved, 1 ≤ c.phase ∧ c.phase ≤ P.L ∧ c.radius < P.k ∧
    ∀ u ∈ c.cluster, memB P G h Δ c.phase c.center c.radius u

lemma SInvL.init {X M : Finset V} : SInvL P G h Δ X ⟨X, M, []⟩ := ⟨le_rfl, by simp⟩

lemma SInvL.step (hP : NumOK P Δ) {X : Finset V} {s : SSPState V} (hI : SInvL P G h Δ X s)
    {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) {x : V}
    (_hx : Eligible P G h Δ X.card s.active ℓ x) {R : ℕ} (hR : R < P.k) :
    SInvL P G h Δ X (carveStep P G h Δ ℓ s x R) := by
  refine ⟨fun u hu => hI.1 (Finset.mem_sdiff.mp hu).1, ?_⟩
  intro c hc
  simp only [carveStep] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hI.2 c hc
  · rw [List.mem_singleton] at hc; subst hc
    exact ⟨hℓ1, hℓ, hR, fun u hu => (mem_ballA.mp hu).2⟩

lemma phaseLoop_invL (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) :
    ∀ (fuel : ℕ) (s : SSPState V), SInvL P G h Δ X s →
      ∀ s' ∈ (phaseLoop P G h rule X M Δ ℓ fuel s).support,
        SInvL P G h Δ X s' ∧ s'.active ⊆ s.active ∧
        (s.active.card < fuel → ¬ ∃ x, Eligible P G h Δ X.card s'.active ℓ x) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs s' hs'
    simp only [phaseLoop, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'
    exact ⟨hs, le_rfl, fun h' => absurd h' (Nat.not_lt_zero _)⟩
  | succ fuel ih =>
    intro s hs s' hs'
    rw [phaseLoop] at hs'
    split_ifs at hs' with hel
    · rw [PMF.mem_support_bind_iff] at hs'
      obtain ⟨R, hR, hs'⟩ := hs'
      have hx := hrule X M Δ ℓ s hel
      have hRk := truncGeom_lt hP hℓ R hR
      have hI' := SInvL.step hP hs hℓ1 hℓ hx hRk
      obtain ⟨h1, h2, h3⟩ := ih _ hI' s' hs'
      have hlt := carve_active_lt hP hx R
      refine ⟨h1, h2.trans (by simp only [carveStep]; exact Finset.sdiff_subset), fun hc => h3 ?_⟩
      omega
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      exact ⟨hs, le_rfl, fun _ => hel⟩

lemma phasesFrom_invL (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} :
    ∀ (ℓ : ℕ), ℓ ≤ P.L → ∀ (s : SSPState V), SInvL P G h Δ X s →
      ∀ s' ∈ (phasesFrom P G h rule X M Δ ℓ s).support,
        SInvL P G h Δ X s' ∧ s'.active ⊆ s.active := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro _ s hs s' hs'
    simp only [phasesFrom, PMF.support_pure, Set.mem_singleton_iff] at hs'
    subst hs'; exact ⟨hs, le_rfl⟩
  | succ j ih =>
    intro hj s hs s' hs'
    rw [phasesFrom, PMF.mem_support_bind_iff] at hs'
    obtain ⟨S, hS, hs'⟩ := hs'
    obtain ⟨h1, h2, -⟩ := phaseLoop_invL hP hrule (by omega) hj _ s hs S hS
    obtain ⟨h3, h4⟩ := ih (by omega) S h1 s' hs'
    exact ⟨h3, h4.trans h2⟩

lemma phasesFrom_denseL (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} (hXN : X.card ≤ P.N) :
    ∀ (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ P.L → ∀ (s : SSPState V), SInvL P G h Δ X s →
      ∀ sf ∈ (phasesFrom P G h rule X M Δ ℓ s).support,
        ∃ S ∈ (phaseLoop P G h rule X M Δ ℓ (X.card + 1) s).support,
          sf.active ⊆ S.active ∧ S.active ⊆ X ∧
          ∀ z ∈ sf.active, (X.card : ℝ) / (P.mu ℓ : ℝ) <
            ((ballA P G h Δ S.active ℓ z (P.k : ℤ)).card : ℝ) := by
  intro ℓ
  induction ℓ with
  | zero => intro h0; omega
  | succ j ih =>
    intro _ hj s hs sf hsf
    rw [phasesFrom, PMF.mem_support_bind_iff] at hsf
    obtain ⟨S, hS, hsf⟩ := hsf
    obtain ⟨hSI, hSs, hSne⟩ := phaseLoop_invL hP hrule (by omega) hj _ s hs S hS
    have hne := hSne (by have := Finset.card_le_card (hs.1); omega)
    have hsfS : sf.active ⊆ S.active := (phasesFrom_invL hP hrule j (by omega) S hSI sf hsf).2
    refine ⟨S, hS, hsfS, hSI.1, fun z hz => ?_⟩
    have hzS := hsfS hz
    -- lower bound for |A_{j+1}(z,0)|
    have hlow : (X.card : ℝ) / (P.mu (j + 1 - 1) : ℝ) ≤
        ((ballA P G h Δ S.active (j + 1) z 0).card : ℝ) := by
      simp only [Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        have hmu := P2.mu_zero_gt P hP.N2
        have h1 : (1 : ℝ) ≤ ((ballA P G h Δ S.active (0 + 1) z 0).card : ℝ) := by
          have : z ∈ ballA P G h Δ S.active (0 + 1) z 0 := by
            rw [mem_ballA]; exact ⟨hzS, memB_self hP z le_rfl⟩
          exact_mod_cast Finset.card_pos.mpr ⟨z, this⟩
        refine le_trans ?_ h1
        rw [div_le_one (P2.mu_pos P 0)]
        have : (X.card : ℝ) ≤ P.N := by exact_mod_cast hXN
        linarith
      · obtain ⟨S', hS', hsfS', -, hbig⟩ := ih hj0 (by omega) S hSI sf hsf
        refine le_trans (hbig z hz).le ?_
        exact_mod_cast Finset.card_le_card (fun u hu => by
          rw [mem_ballA] at hu ⊢
          obtain ⟨-, hS'S, -⟩ := phaseLoop_invL hP hrule hj0 (by omega) _ S hSI S' hS'
          exact ⟨hS'S hu.1, memB_shift hP hj0 hu.2⟩)
    by_contra hcon
    push Not at hcon
    apply hne
    refine ⟨z, hzS, hlow, ?_, hcon⟩
    exact Finset.card_le_card (fun u hu => by
      rw [mem_ballA] at hu ⊢; exact ⟨hu.1, memB_mono hP (by omega) hu.2⟩)

/-- Claim 1: the last cluster has `diam^{(2k(L+1)h)} ≤ 2 r_L`. -/
lemma sspRun_last_diamL (hP : NumOK P Δ) {rule : CenterRule V} (hrule : IsValidRule P G h rule)
    {X M : Finset V} (hXN : X.card ≤ P.N) :
    ∀ sf ∈ (sspRun P G h rule X M Δ).support, ∀ z ∈ sf.active, ∀ z' ∈ sf.active,
      hopDist G (2 * P.k * (P.L + 1) * h) z z' ≤ ENNReal.ofReal (2 * P.r Δ P.L) := by
  intro sf hsf z hz z' hz'
  obtain ⟨S, -, hsfS, hSX, hbig⟩ :=
    phasesFrom_denseL hP hrule hXN P.L hP.Lpos le_rfl _ (SInvL.init) sf hsf
  have hb1 := hbig z hz
  have hb2 := hbig z' hz'
  rw [P2.mu_L] at hb1 hb2
  set B1 := ballA P G h Δ S.active P.L z (P.k : ℤ)
  set B2 := ballA P G h Δ S.active P.L z' (P.k : ℤ)
  have hsub1 : B1 ⊆ X := fun u hu => hSX (mem_ballA.mp hu).1
  have hsub2 : B2 ⊆ X := fun u hu => hSX (mem_ballA.mp hu).1
  have hint : (B1 ∩ B2).Nonempty := by
    by_contra hem
    rw [Finset.not_nonempty_iff_eq_empty] at hem
    have hU := Finset.card_union_add_card_inter B1 B2
    rw [hem, Finset.card_empty, add_zero] at hU
    have : (B1 ∪ B2).card ≤ X.card := Finset.card_le_card (Finset.union_subset hsub1 hsub2)
    have : ((B1.card + B2.card : ℕ) : ℝ) ≤ X.card := by exact_mod_cast hU ▸ this
    push_cast at this
    linarith
  obtain ⟨w, hw⟩ := hint
  rw [Finset.mem_inter, mem_ballA, mem_ballA] at hw
  have d1 := memB_dist_k hP hP.Lpos hw.1.2
  have d2 := memB_dist_k hP hP.Lpos hw.2.2
  have hr := hP.r_nonneg P.L
  calc hopDist G (2 * P.k * (P.L + 1) * h) z z'
      = hopDist G (P.k * (P.L + 1) * h + P.k * (P.L + 1) * h) z z' := by congr 1; ring
    _ ≤ hopDist G (P.k * (P.L + 1) * h) z w + hopDist G (P.k * (P.L + 1) * h) w z' :=
        hopDist_triangle G _ _ z w z'
    _ ≤ ENNReal.ofReal (P.r Δ P.L) + ENNReal.ofReal (P.r Δ P.L) := by
        rw [hopDist_symm G _ z w]; exact add_le_add d1 d2
    _ = ENNReal.ofReal (2 * P.r Δ P.L) := by rw [← ENNReal.ofReal_add hr hr]; ring_nf



end HopRamsey.FZ


open scoped ENNReal

namespace HopRamsey.FZ

open ARTreeCover HopRamsey
set_option linter.unusedSectionVars false
variable {V : Type} [Fintype V] [DecidableEq V]

theorem claim_1' (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (X M : Finset V) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∀ s ∈ (sspRun P G h rule X M Δ).support, s.active.Nonempty →
      hopDiam G (2 * P.k * (P.L + 1) * h) s.active ≤ ENNReal.ofReal (2 * P.r Δ P.L) ∧
        2 * P.r Δ P.L ≤ Δ / 2 := by
  have hs := StdHyp.of hS
  have hP : NumOK P Δ := ⟨hs.N2, hs.eps0, hs.eps1, hs.Phi2, hΔ.le⟩
  intro s hs' _
  exact ⟨hopDiam_le G _ (sspRun_last_diamL hP hrule (hs.card_le X) s hs'), two_rL_le hP⟩

theorem corollary_1' (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (hΦfin : hopDiam G h Finset.univ ≠ ⊤) (hΦ : P.Φ = (hopDiam G h Finset.univ).toReal) :
    CallInv P G h Finset.univ Finset.univ P.Φ ∧
    (∀ (X M : Finset V) (Δ : ℝ), 0 < Δ →
      ∀ C ∈ (singleScalePartition P G h rule X M Δ).support, ∀ c ∈ C,
        hopDiam G (2 * P.k * (P.L + 1) * h) c.1 ≤ ENNReal.ofReal (Δ / 2)) ∧
    (∀ o ∈ (hopStochEmbedding P G h rule Finset.univ Finset.univ P.Φ).support, ∀ u v : V,
      hopDist G (2 * P.k * (P.L + 1) * h) u v ≤ o.1 u v) := by
  have hs := StdHyp.of hS
  have hinv : CallInv P G h Finset.univ Finset.univ P.Φ := by
    refine ⟨?_, le_rfl, by linarith [hs.Phi2], ?_⟩
    · rw [Finset.univ_nonempty_iff]
      have : 0 < Fintype.card V := by rw [← hs.NV]; linarith [hs.N2]
      exact Fintype.card_pos_iff.mp this
    · refine le_trans (hopDiam_mono G (a := h) ?_ _) ?_
      · have := P2.k_pos P hs.N2 hs.eps0 hs.eps1 hs.Phi2
        have : 1 ≤ 2 * P.k * (P.L + 1) := by nlinarith
        nlinarith
      · rw [hΦ, ENNReal.ofReal_toReal hΦfin]
  refine ⟨hinv, ?_, ?_⟩
  · intro X M Δ hΔ C hC c hc
    have hP : NumOK P Δ := ⟨hs.N2, hs.eps0, hs.eps1, hs.Phi2, hΔ.le⟩
    unfold singleScalePartition at hC
    rw [PMF.support_map] at hC
    obtain ⟨sf, hsf, rfl⟩ := hC
    have hI : SInvL P G h Δ X sf := (phasesFrom_invL hP hrule P.L le_rfl _ SInvL.init sf hsf).1
    have h2r := two_rL_le hP
    apply hopDiam_le G
    intro u hu w hw
    unfold sspOutput at hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
      obtain ⟨h1, h2, h3, h4⟩ := hI.2 d hd
      have d1 := memB_dist hP h1 h2 h3 (h4 u hu)
      have d2 := memB_dist hP h1 h2 h3 (h4 w hw)
      have hr := hP.r_nonneg P.L
      calc hopDist G (2 * P.k * (P.L + 1) * h) u w
          = hopDist G (P.k * (P.L + 1) * h + P.k * (P.L + 1) * h) u w := by congr 1; ring
        _ ≤ hopDist G (P.k * (P.L + 1) * h) u d.center +
              hopDist G (P.k * (P.L + 1) * h) d.center w := hopDist_triangle G _ _ u d.center w
        _ ≤ ENNReal.ofReal (P.r Δ P.L) + ENNReal.ofReal (P.r Δ P.L) := by
            rw [hopDist_symm G _ d.center w]; exact add_le_add d1 d2
        _ = ENNReal.ofReal (2 * P.r Δ P.L) := by rw [← ENNReal.ofReal_add hr hr]; ring_nf
        _ ≤ ENNReal.ofReal (Δ / 2) := ENNReal.ofReal_le_ofReal h2r
    · split_ifs at hc with hne
      · rw [List.mem_singleton] at hc; subst hc
        exact le_trans (sspRun_last_diamL hP hrule (hs.card_le X) sf hsf u hu w hw)
          (ENNReal.ofReal_le_ofReal h2r)
      · simp at hc
  · intro o ho u v
    exact (rec_ok' hS hrule _ _ _ hinv o ho).hop u (Finset.mem_univ u) v (Finset.mem_univ v)

end HopRamsey.FZ


open scoped ENNReal
open ARTreeCover HopRamsey

theorem solution {V : Type} [Fintype V] [DecidableEq V] (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (hS : Standing P G h) (hrule : IsValidRule P G h rule)
    (hΦfin : hopDiam G h Finset.univ ≠ ⊤) (hΦ : P.Φ = (hopDiam G h Finset.univ).toReal) :
    CallInv P G h Finset.univ Finset.univ P.Φ ∧
    (∀ (X M : Finset V) (Δ : ℝ), 0 < Δ →
      ∀ C ∈ (singleScalePartition P G h rule X M Δ).support, ∀ c ∈ C,
        hopDiam G (2 * P.k * (P.L + 1) * h) c.1 ≤ ENNReal.ofReal (Δ / 2)) ∧
    (∀ o ∈ (hopStochEmbedding P G h rule Finset.univ Finset.univ P.Φ).support, ∀ u v : V,
      hopDist G (2 * P.k * (P.L + 1) * h) u v ≤ o.1 u v) := by
  exact HopRamsey.FZ.corollary_1' P G h rule hS hrule hΦfin hΦ
