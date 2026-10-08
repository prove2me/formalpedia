-- Prove2me | solution 1 for Helfgott.rankin_coupled_finite_prime_product_upper
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T16:48:17.753986+00:00
-- url     : https://prove2.me/submissions/03e37807-dcf5-4587-a364-3a867e3c2f4d

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Group

section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

lemma natural_power_geometric_series (σ : ℝ) (hσ : 0<σ) (p : ℕ) (hp : Nat.Prime p) :
    Summable (fun k : ℕ => ‖((p^k : ℕ) : ℝ)^(-σ)‖) ∧
      (∑' k : ℕ,((p^k : ℕ) : ℝ)^(-σ))=(1-(p : ℝ)^(-σ))⁻¹ := by
  have hpR : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ)≤p := by positivity
  have he : (fun k : ℕ => ((p^k : ℕ) : ℝ)^(-σ))=(fun k => ((p : ℝ)^(-σ))^k) := by
    funext k
    rw [Nat.cast_pow,←Real.rpow_natCast_mul hp0 k (-σ),mul_comm,Real.rpow_mul_natCast hp0]
  have hr : ‖(p : ℝ)^(-σ)‖<1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hp0 _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  constructor
  · apply (summable_geometric_of_norm_lt_one hr).congr
    intro k
    rw [←congrFun he k,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  · rw [he]
    exact tsum_geometric_of_norm_lt_one hr

theorem prime_supported_dirichlet_series (q : ℕ) (hq : 1≤q) (σ : ℝ) (hσ : 0<σ) :
    let f : ℕ→ℝ := fun n => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0
    Summable f ∧ (∑' n : ℕ,f n)=∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
  let g : ℕ→ℝ := fun n => (n : ℝ)^(-σ)
  have hg1 : g 1=1 := by simp [g]
  have hmul : ∀ {m n},Nat.Coprime m n → g (m*n)=g m*g n := by
    intro m n hmn
    dsimp [g]
    rw [Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  have h := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hg1 hmul (fun {p} hp => (natural_power_geometric_series σ hσ p hp).1) q.primeFactors
  have hfilter : q.primeFactors.filter Nat.Prime=q.primeFactors := by
    exact Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hvalue : (∏ p∈q.primeFactors with Nat.Prime p,∑' k : ℕ,g (p^k))=
      ∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
    rw [hfilter]
    exact Finset.prod_congr rfl (fun p hp => (natural_power_geometric_series σ hσ p (Nat.prime_of_mem_primeFactors hp)).2)
  have hmem (n : ℕ) : n∈Nat.factoredNumbers q.primeFactors ↔
      n≠0 ∧ (∀ p∈n.primeFactors,p∣q) := by
    rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
    constructor
    · rintro ⟨hn0,hsub⟩
      exact ⟨hn0,fun p hp => Nat.dvd_of_mem_primeFactors (hsub hp)⟩
    · rintro ⟨hn0,hall⟩
      exact ⟨hn0,fun p hp => Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,hall p hp,by omega⟩⟩
  have he : (Nat.factoredNumbers q.primeFactors).indicator g=
      (fun n : ℕ => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0) := by
    funext n
    rw [Set.indicator_apply]
    by_cases hn : n∈Nat.factoredNumbers q.primeFactors
    · rw [if_pos hn,if_pos ((hmem n).mp hn)]
    · rw [if_neg hn,if_neg (fun hh => hn ((hmem n).mpr hh))]
  constructor
  · rw [←he]
    exact summable_subtype_iff_indicator.mp h.1.of_norm
  · rw [←he,←_root_.tsum_subtype]
    exact h.2.tsum_eq.trans hvalue

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Finset Nat Real Filter
open scoped BigOperators Topology Classical
namespace Helfgott

theorem real_zeta_euler_hasProd (σ : ℝ) (hσ : 1 < σ) :
    HasProd (fun p : Nat.Primes => (1-(p : ℝ)^(-σ))⁻¹)
      (∑' n : ℕ,(n : ℝ)^(-σ)) := by
  let g : ℕ → ℝ := fun n => (n : ℝ)^(-σ)
  have hg1 : g 1=1 := by simp [g]
  have hg0 : g 0=0 := by simp [g,Real.zero_rpow (by linarith : -σ ≠ 0)]
  have hmul : ∀ {m n},Nat.Coprime m n → g (m*n)=g m*g n := by
    intro m n _
    dsimp [g]
    rw [Nat.cast_mul,Real.mul_rpow (by positivity) (by positivity)]
  have hsum : Summable (fun n : ℕ => ‖g n‖) := by
    simpa only [g,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
      (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
  have h := EulerProduct.eulerProduct_hasProd hg1 hmul hsum hg0
  have he : (fun p : Nat.Primes => ∑' k : ℕ,g (p^k))=
      (fun p : Nat.Primes => (1-(p : ℝ)^(-σ))⁻¹) := by
    funext p
    exact (natural_power_geometric_series σ (by linarith) p p.property).2
  rw [he] at h
  exact h

lemma real_zeta_sum_pos (σ : ℝ) (hσ : 1 < σ) :
    0 < ∑' n : ℕ,(n : ℝ)^(-σ) := by
  have hsum := Real.summable_nat_rpow.mpr (by linarith : -σ < -1)
  have h := hsum.sum_le_tsum {1} (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) (-σ))
  norm_num at h
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 10000
namespace Helfgott

noncomputable def rankinSparseBlock0_6 (a b : ℝ) : ℝ :=
      a*b^2*(1-b)

theorem rankinSparseBlock0_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock0_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock0_6
  positivity

noncomputable def rankinSparseBlock0_7 (a b : ℝ) : ℝ :=
      a*b*(1-b) +
      a^2*(1-a)*b +
      a*(1-a)*b

theorem rankinSparseBlock0_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock0_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock0_7
  positivity

noncomputable def rankinSparseBlock1_0 (a b : ℝ) : ℝ :=
      b

theorem rankinSparseBlock1_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_0
  positivity

noncomputable def rankinSparseBlock1_1 (a b : ℝ) : ℝ :=
      a

theorem rankinSparseBlock1_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_1
  positivity

noncomputable def rankinSparseBlock1_3 (a b : ℝ) : ℝ :=
      2*a*b +
      b^2*(1-b) +
      a^2*(1-a)

theorem rankinSparseBlock1_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_3
  positivity

noncomputable def rankinSparseBlock1_4 (a b : ℝ) : ℝ :=
      b*(1-b) +
      a*(1-a)

theorem rankinSparseBlock1_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_4
  positivity

noncomputable def rankinSparseBlock1_5 (a b : ℝ) : ℝ :=
      a^2*(1-a)*b*(1-b) +
      2*a*(1-a)*b*(1-b)

theorem rankinSparseBlock1_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_5
  positivity

noncomputable def rankinSparseBlock1_6 (a b : ℝ) : ℝ :=
      a*(1-a)*b^2*(1-b) +
      4*a*b^2*(1-b)

theorem rankinSparseBlock1_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_6
  positivity

noncomputable def rankinSparseBlock1_7 (a b : ℝ) : ℝ :=
      6*a*b*(1-b) +
      5*a^2*(1-a)*b +
      6*a*(1-a)*b

theorem rankinSparseBlock1_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock1_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock1_7
  positivity

noncomputable def rankinSparseBlock2_0 (a b : ℝ) : ℝ :=
      2*b

theorem rankinSparseBlock2_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_0
  positivity

noncomputable def rankinSparseBlock2_1 (a b : ℝ) : ℝ :=
      3*a

theorem rankinSparseBlock2_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_1
  positivity

noncomputable def rankinSparseBlock2_3 (a b : ℝ) : ℝ :=
      10*a*b +
      3*b^2*(1-b) +
      a^2*(1-a)

theorem rankinSparseBlock2_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_3
  positivity

noncomputable def rankinSparseBlock2_4 (a b : ℝ) : ℝ :=
      6*b*(1-b) +
      2*a^2*(1-a) +
      6*a*(1-a)

theorem rankinSparseBlock2_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_4
  positivity

noncomputable def rankinSparseBlock2_5 (a b : ℝ) : ℝ :=
      4*a^2*(1-a)*b*(1-b) +
      11*a*(1-a)*b*(1-b)

theorem rankinSparseBlock2_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_5
  positivity

noncomputable def rankinSparseBlock2_6 (a b : ℝ) : ℝ :=
      5*a*(1-a)*b^2*(1-b) +
      9*a*b^2*(1-b)

theorem rankinSparseBlock2_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_6
  positivity

noncomputable def rankinSparseBlock2_7 (a b : ℝ) : ℝ :=
      a^2*b^4 +
      19*a*b*(1-b) +
      14*a^2*(1-a)*b +
      19*a*(1-a)*b

theorem rankinSparseBlock2_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_7
  positivity

noncomputable def rankinSparseBlock2_8 (a b : ℝ) : ℝ :=
      a^4*b^2

theorem rankinSparseBlock2_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_8
  positivity

noncomputable def rankinSparseBlock2_9 (a b : ℝ) : ℝ :=
      a^2*(1-a)*b^2*(1-b)

theorem rankinSparseBlock2_9_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock2_9 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock2_9
  positivity

noncomputable def rankinSparseBlock3_0 (a b : ℝ) : ℝ :=
      6*b

theorem rankinSparseBlock3_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_0
  positivity

noncomputable def rankinSparseBlock3_1 (a b : ℝ) : ℝ :=
      9*a

theorem rankinSparseBlock3_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_1
  positivity

noncomputable def rankinSparseBlock3_3 (a b : ℝ) : ℝ :=
      34*a*b +
      6*b^2*(1-b)

theorem rankinSparseBlock3_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_3
  positivity

noncomputable def rankinSparseBlock3_4 (a b : ℝ) : ℝ :=
      20*b*(1-b) +
      8*a^2*(1-a) +
      20*a*(1-a)

theorem rankinSparseBlock3_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_4
  positivity

noncomputable def rankinSparseBlock3_5 (a b : ℝ) : ℝ :=
      a^2*(1-a)*b^4 +
      a^4*b^2*(1-b) +
      13*a^2*(1-a)*b*(1-b) +
      40*a*(1-a)*b*(1-b) +
      2*a^4*b

theorem rankinSparseBlock3_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_5
  positivity

noncomputable def rankinSparseBlock3_6 (a b : ℝ) : ℝ :=
      18*a*(1-a)*b^2*(1-b) +
      2*a*b^4 +
      12*a*b^2*(1-b)

theorem rankinSparseBlock3_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_6
  positivity

noncomputable def rankinSparseBlock3_7 (a b : ℝ) : ℝ :=
      22*a*b*(1-b) +
      26*a^2*(1-a)*b +
      22*a*(1-a)*b

theorem rankinSparseBlock3_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_7
  positivity

noncomputable def rankinSparseBlock3_8 (a b : ℝ) : ℝ :=
      3*a^2*b^4 +
      4*a^4*b^2 +
      13*a*b*(1-b) +
      13*a*(1-a)*b

theorem rankinSparseBlock3_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_8
  positivity

noncomputable def rankinSparseBlock3_9 (a b : ℝ) : ℝ :=
      6*a^2*(1-a)*b^2*(1-b)

theorem rankinSparseBlock3_9_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock3_9 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock3_9
  positivity

noncomputable def rankinSparseBlock4_0 (a b : ℝ) : ℝ :=
      10*b

theorem rankinSparseBlock4_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_0
  positivity

noncomputable def rankinSparseBlock4_1 (a b : ℝ) : ℝ :=
      19*a

theorem rankinSparseBlock4_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_1
  positivity

noncomputable def rankinSparseBlock4_3 (a b : ℝ) : ℝ :=
      73*a*b +
      10*b^2*(1-b)

theorem rankinSparseBlock4_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_3
  positivity

noncomputable def rankinSparseBlock4_4 (a b : ℝ) : ℝ :=
      b^4 +
      50*b*(1-b) +
      a^4 +
      18*a^2*(1-a) +
      50*a*(1-a)

theorem rankinSparseBlock4_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_4
  positivity

noncomputable def rankinSparseBlock4_5 (a b : ℝ) : ℝ :=
      a^2*(1-a)*b^4 +
      2*a^4*b^2*(1-b) +
      20*a^2*(1-a)*b*(1-b) +
      94*a*(1-a)*b*(1-b) +
      3*a^4*b

theorem rankinSparseBlock4_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_5
  positivity

noncomputable def rankinSparseBlock4_6 (a b : ℝ) : ℝ :=
      38*a*(1-a)*b^2*(1-b) +
      8*a*b^4 +
      a*b^2*(1-b) +
      3*a^4*b

theorem rankinSparseBlock4_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_6
  positivity

noncomputable def rankinSparseBlock4_7 (a b : ℝ) : ℝ :=
      9*a*b^2*(1-b) +
      36*a^2*(1-a)*b

theorem rankinSparseBlock4_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_7
  positivity

noncomputable def rankinSparseBlock4_8 (a b : ℝ) : ℝ :=
      a^4*b^3*(1-b) +
      8*a^2*b^4 +
      8*a^4*b^2 +
      43*a*b*(1-b) +
      43*a*(1-a)*b

theorem rankinSparseBlock4_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_8
  positivity

noncomputable def rankinSparseBlock4_9 (a b : ℝ) : ℝ :=
      13*a^2*(1-a)*b^2*(1-b)

theorem rankinSparseBlock4_9_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock4_9 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock4_9
  positivity

noncomputable def rankinSparseBlock5_0 (a b : ℝ) : ℝ :=
      18*b

theorem rankinSparseBlock5_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_0
  positivity

noncomputable def rankinSparseBlock5_1 (a b : ℝ) : ℝ :=
      37*a

theorem rankinSparseBlock5_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_1
  positivity

noncomputable def rankinSparseBlock5_3 (a b : ℝ) : ℝ :=
      122*a*b +
      6*b^2*(1-b)

theorem rankinSparseBlock5_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_3
  positivity

noncomputable def rankinSparseBlock5_4 (a b : ℝ) : ℝ :=
      3*b^4 +
      6*b^2*(1-b) +
      45*b*(1-b) +
      3*a^4 +
      30*a^2*(1-a) +
      45*a*(1-a)

theorem rankinSparseBlock5_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_4
  positivity

noncomputable def rankinSparseBlock5_5 (a b : ℝ) : ℝ :=
      6*a^4*b^2*(1-b) +
      18*a^2*(1-a)*b*(1-b) +
      164*a*(1-a)*b*(1-b) +
      57*b*(1-b) +
      57*a*(1-a)

theorem rankinSparseBlock5_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_5
  positivity

noncomputable def rankinSparseBlock5_6 (a b : ℝ) : ℝ :=
      4*a^2*(1-a)*b^4 +
      56*a*(1-a)*b^2*(1-b) +
      19*a*b^4 +
      14*a^4*b

theorem rankinSparseBlock5_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_6
  positivity

noncomputable def rankinSparseBlock5_7 (a b : ℝ) : ℝ :=
      9*a*b^2*(1-b) +
      36*a^2*(1-a)*b

theorem rankinSparseBlock5_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_7
  positivity

noncomputable def rankinSparseBlock5_8 (a b : ℝ) : ℝ :=
      5*a^4*b^3*(1-b) +
      11*a^2*b^4 +
      7*a^4*b^2

theorem rankinSparseBlock5_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_8
  positivity

noncomputable def rankinSparseBlock5_9 (a b : ℝ) : ℝ :=
      a^4*b^4*(1-b) +
      a^4*(1-a)*b^4 +
      8*a^2*(1-a)*b^2*(1-b)

theorem rankinSparseBlock5_9_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock5_9 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock5_9
  positivity

noncomputable def rankinSparseBlock6_0 (a b : ℝ) : ℝ :=
      22*b

theorem rankinSparseBlock6_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_0
  positivity

noncomputable def rankinSparseBlock6_1 (a b : ℝ) : ℝ :=
      59*a

theorem rankinSparseBlock6_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_1
  positivity

noncomputable def rankinSparseBlock6_3 (a b : ℝ) : ℝ :=
      159*a*b

theorem rankinSparseBlock6_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_3
  positivity

noncomputable def rankinSparseBlock6_4 (a b : ℝ) : ℝ :=
      46*a^2*(1-a)*b^3 +
      15*a^4*b*(1-b) +
      71*(1-a)*b*(1-b) +
      6*a^2*(1-a)*(1-b) +
      71*a*(1-a)*(1-b) +
      6*b^4 +
      18*b^2*(1-b) +
      a^4 +
      18*a^2*(1-a)

theorem rankinSparseBlock6_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_4
  positivity

noncomputable def rankinSparseBlock6_5 (a b : ℝ) : ℝ :=
      12*a^4*b^2*(1-b) +
      5*a^2*(1-a)*b^3 +
      224*a*(1-a)*b*(1-b) +
      168*(1-a)*b*(1-b) +
      18*a^2*(1-a)*(1-b) +
      168*a*(1-a)*(1-b) +
      5*a^4

theorem rankinSparseBlock6_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_5
  positivity

noncomputable def rankinSparseBlock6_6 (a b : ℝ) : ℝ :=
      12*a^2*(1-a)*b^4 +
      54*a*(1-a)*b^2*(1-b) +
      49*a^2*(1-a)*b*(1-b) +
      36*a*b^4 +
      16*a^4*b

theorem rankinSparseBlock6_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_6
  positivity

noncomputable def rankinSparseBlock6_7 (a b : ℝ) : ℝ :=
      2*a^4*(1-a)*b^4*(1-b) +
      4*a^3*b^4*(1-b) +
      4*a^4*(1-a)*b^3

theorem rankinSparseBlock6_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_7
  positivity

noncomputable def rankinSparseBlock6_8 (a b : ℝ) : ℝ :=
      16*a^4*b^3*(1-b)

theorem rankinSparseBlock6_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_8
  positivity

noncomputable def rankinSparseBlock6_9 (a b : ℝ) : ℝ :=
      a^4*b^4*(1-b) +
      a^4*(1-a)*b^4

theorem rankinSparseBlock6_9_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock6_9 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock6_9
  positivity

noncomputable def rankinSparseBlock7_0 (a b : ℝ) : ℝ :=
      24*b

theorem rankinSparseBlock7_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_0
  positivity

noncomputable def rankinSparseBlock7_1 (a b : ℝ) : ℝ :=
      83*a

theorem rankinSparseBlock7_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_1
  positivity

noncomputable def rankinSparseBlock7_2 (a b : ℝ) : ℝ :=
      82*b*(1-b) +
      82*a*(1-a)

theorem rankinSparseBlock7_2_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_2 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_2
  positivity

noncomputable def rankinSparseBlock7_3 (a b : ℝ) : ℝ :=
      6*(1-a)*b^4 +
      5*(1-a)*b^2*(1-b) +
      176*a*b +
      342*b*(1-b) +
      342*a*(1-a)

theorem rankinSparseBlock7_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_3
  positivity

noncomputable def rankinSparseBlock7_4 (a b : ℝ) : ℝ :=
      34*a*(1-a)*b^4 +
      17*a^4*b*(1-b) +
      4*b^4 +
      25*b^2*(1-b)

theorem rankinSparseBlock7_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_4
  positivity

noncomputable def rankinSparseBlock7_5 (a b : ℝ) : ℝ :=
      a^4*b^2*(1-b) +
      31*a*(1-a)*b^4 +
      7*a^4*b*(1-b) +
      248*a*(1-a)*b*(1-b) +
      42*(1-a)*b*(1-b) +
      72*a^2*(1-a)*(1-b) +
      42*a*(1-a)*(1-b) +
      15*a^4

theorem rankinSparseBlock7_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_5
  positivity

noncomputable def rankinSparseBlock7_6 (a b : ℝ) : ℝ :=
      7*a^3*(1-a)*b^4*(1-b) +
      7*a^4*(1-a)*b^3*(1-b) +
      38*a^2*(1-a)*b^4 +
      11*a^4*b^2*(1-b) +
      6*a^2*b^4*(1-b) +
      14*a*(1-a)*b^2*(1-b) +
      6*a^4*(1-a)*b^2 +
      55*a^2*(1-a)*b*(1-b)

theorem rankinSparseBlock7_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_6
  positivity

noncomputable def rankinSparseBlock7_7 (a b : ℝ) : ℝ :=
      a^3*b^4*(1-b) +
      a^4*(1-a)*b^3

theorem rankinSparseBlock7_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_7
  positivity

noncomputable def rankinSparseBlock7_8 (a b : ℝ) : ℝ :=
      20*a^4*b^3*(1-b)

theorem rankinSparseBlock7_8_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock7_8 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock7_8
  positivity

noncomputable def rankinSparseBlock8_0 (a b : ℝ) : ℝ :=
      24*b

theorem rankinSparseBlock8_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_0
  positivity

noncomputable def rankinSparseBlock8_1 (a b : ℝ) : ℝ :=
      107*a

theorem rankinSparseBlock8_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_1
  positivity

noncomputable def rankinSparseBlock8_3 (a b : ℝ) : ℝ :=
      108*a^2*b^2*(1-b) +
      8*(1-a)*b^4 +
      28*(1-a)*b^2*(1-b) +
      18*a^4*(1-b) +
      52*a*b +
      4*a^2*(1-a)

theorem rankinSparseBlock8_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_3
  positivity

noncomputable def rankinSparseBlock8_4 (a b : ℝ) : ℝ :=
      43*a^2*(1-a)*b^3 +
      a*(1-a)*b^4*(1-b) +
      22*a^2*b^2*(1-b) +
      a^4*(1-a)*b*(1-b) +
      9*(1-a)*b^2*(1-b) +
      12*a^4*(1-b) +
      48*a*b +
      b^4 +
      134*a^2*(1-a)

theorem rankinSparseBlock8_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_4
  positivity

noncomputable def rankinSparseBlock8_5 (a b : ℝ) : ℝ :=
      8*a^4*b^4 +
      11*a^2*(1-a)*b^4*(1-b) +
      11*a^4*(1-a)*b^2*(1-b) +
      11*a*(1-a)*b^4 +
      162*a*(1-a)*b*(1-b) +
      3*a*b^4*(1-b) +
      3*a^4*(1-a)*b +
      23*a^4*b

theorem rankinSparseBlock8_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_5
  positivity

noncomputable def rankinSparseBlock8_6 (a b : ℝ) : ℝ :=
      a^3*(1-a)*b^4*(1-b) +
      a^4*(1-a)*b^3*(1-b) +
      2*a^2*(1-a)*b^4*(1-b) +
      48*a^2*(1-a)*b^4 +
      2*a^4*(1-a)*b^2*(1-b) +
      4*a^4*b^2*(1-b)

theorem rankinSparseBlock8_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_6
  positivity

noncomputable def rankinSparseBlock8_7 (a b : ℝ) : ℝ :=
      a^3*(1-a)*b^4*(1-b) +
      a^4*(1-a)*b^3*(1-b)

theorem rankinSparseBlock8_7_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock8_7 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock8_7
  positivity

noncomputable def rankinSparseBlock9_0 (a b : ℝ) : ℝ :=
      21*b

theorem rankinSparseBlock9_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_0
  positivity

noncomputable def rankinSparseBlock9_1 (a b : ℝ) : ℝ :=
      112*b*(1-b) +
      110*a*(1-a) +
      83*a

theorem rankinSparseBlock9_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_1
  positivity

noncomputable def rankinSparseBlock9_2 (a b : ℝ) : ℝ :=
      92*a*(1-a)*b^2 +
      264*a*b*(1-b) +
      12*a^2*(1-a)*(1-b) +
      12*b^2*(1-b) +
      2*a*(1-a) +
      45*a

theorem rankinSparseBlock9_2_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_2 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_2
  positivity

noncomputable def rankinSparseBlock9_3 (a b : ℝ) : ℝ :=
      138*a^2*(1-a)*b^2 +
      24*a*(1-a)*b^2 +
      (1-a)*b^4*(1-b) +
      4*(1-a)*b^4 +
      61*a*b*(1-b) +
      a^4*(1-a)*(1-b) +
      62*a^2*(1-a)*(1-b) +
      209*a*(1-a)*b +
      9*b^2*(1-b)

theorem rankinSparseBlock9_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_3
  positivity

noncomputable def rankinSparseBlock9_4 (a b : ℝ) : ℝ :=
      11*a^2*(1-a)*b^3 +
      8*a*(1-a)*b^4*(1-b) +
      80*a^2*b^2*(1-b) +
      8*a^4*(1-a)*b*(1-b) +
      28*a^4*b*(1-b) +
      14*a*b^4 +
      2*a^4*(1-b) +
      2*b^4

theorem rankinSparseBlock9_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_4
  positivity

noncomputable def rankinSparseBlock9_5 (a b : ℝ) : ℝ :=
      24*a^4*b^4 +
      80*a^2*(1-a)*b^3 +
      3*a^2*b^4*(1-b) +
      18*a^2*b^4 +
      3*a^4*(1-a)*b^2

theorem rankinSparseBlock9_5_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_5 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_5
  positivity

noncomputable def rankinSparseBlock9_6 (a b : ℝ) : ℝ :=
      20*a^4*b^4

theorem rankinSparseBlock9_6_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock9_6 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock9_6
  positivity

noncomputable def rankinSparseBlock10_0 (a b : ℝ) : ℝ :=
      106*a*(1-b) +
      18*b

theorem rankinSparseBlock10_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock10_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock10_0
  positivity

noncomputable def rankinSparseBlock10_1 (a b : ℝ) : ℝ :=
      85*a*(1-b) +
      22*b*(1-b)

theorem rankinSparseBlock10_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock10_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock10_1
  positivity

noncomputable def rankinSparseBlock10_2 (a b : ℝ) : ℝ :=
      16*a*b^2*(1-b) +
      28*a*(1-a)*(1-b) +
      4*b*(1-b)

theorem rankinSparseBlock10_2_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock10_2 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock10_2
  positivity

noncomputable def rankinSparseBlock10_3 (a b : ℝ) : ℝ :=
      4*(1-a)^2*b^4 +
      4*a^4*(1-b)^2 +
      22*a^4*b^2 +
      8*a^2*(1-a)*b^2 +
      200*a*(1-a)*b^2 +
      (1-a)*b^4*(1-b) +
      38*a*b^2*(1-b) +
      a^4*(1-a)*(1-b) +
      107*a^2*(1-a)*b

theorem rankinSparseBlock10_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock10_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock10_3
  positivity

noncomputable def rankinSparseBlock10_4 (a b : ℝ) : ℝ :=
      a^2*(1-a)*b^4*(1-b) +
      48*a^3*b^4 +
      a^4*(1-a)*b^2*(1-b) +
      68*a^4*b^3 +
      4*a^4*b^2 +
      42*a^2*(1-a)*b^2

theorem rankinSparseBlock10_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock10_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock10_4
  positivity

noncomputable def rankinSparseBlock11_0 (a b : ℝ) : ℝ :=
      7*b +
      31*a

theorem rankinSparseBlock11_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock11_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock11_0
  positivity

noncomputable def rankinSparseBlock11_1 (a b : ℝ) : ℝ :=
      2*a^4*b*(1-b) +
      88*a*b*(1-b) +
      116*a*(1-a)*b +
      16*a*(1-b) +
      24*a*(1-a)

theorem rankinSparseBlock11_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock11_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock11_1
  positivity

noncomputable def rankinSparseBlock11_2 (a b : ℝ) : ℝ :=
      2*a^2*b^4 +
      64*a*(1-a)*b^2*(1-b) +
      10*a^4*b*(1-b) +
      92*a^2*(1-a)*b*(1-b) +
      12*a*b^4 +
      6*(1-a)*b^2*(1-b) +
      6*a^2*(1-a)*(1-b) +
      172*a*(1-a)*b

theorem rankinSparseBlock11_2_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock11_2 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock11_2
  positivity

noncomputable def rankinSparseBlock11_3 (a b : ℝ) : ℝ :=
      20*a^4*b^2*(1-b) +
      72*a^2*(1-a)*b^2*(1-b) +
      28*a^2*b^4 +
      10*a^2*b^2*(1-b)

theorem rankinSparseBlock11_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock11_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock11_3
  positivity

noncomputable def rankinSparseBlock11_4 (a b : ℝ) : ℝ :=
      a^3*b^4*(1-b) +
      a^4*(1-a)*b^3

theorem rankinSparseBlock11_4_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock11_4 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock11_4
  positivity

noncomputable def rankinSparseBlock12_0 (a b : ℝ) : ℝ :=
      20*(1-a)*b*(1-b) +
      48*a*(1-a)*(1-b) +
      28*b*(1-b) +
      4*b +
      20*a

theorem rankinSparseBlock12_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock12_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock12_0
  positivity

noncomputable def rankinSparseBlock12_1 (a b : ℝ) : ℝ :=
      2*a*(1-a)*b^4 +
      8*(1-a)^2*b^2*(1-b) +
      2*a^2*(1-a)*(1-b)^2 +
      42*a*(1-a)*b*(1-b) +
      2*(1-a)*b^4 +
      2*a^4*(1-b) +
      51*a*b

theorem rankinSparseBlock12_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock12_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock12_1
  positivity

noncomputable def rankinSparseBlock12_2 (a b : ℝ) : ℝ :=
      2*a^4*b^3 +
      2*(1-a)^2*b^2*(1-b) +
      14*a^4*b^2 +
      8*a^2*(1-a)*(1-b)^2 +
      28*a^2*(1-a)*b^2 +
      2*(1-a)*b^2*(1-b) +
      2*a^2*(1-a)*(1-b)

theorem rankinSparseBlock12_2_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock12_2 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock12_2
  positivity

noncomputable def rankinSparseBlock12_3 (a b : ℝ) : ℝ :=
      18*a^4*b^3

theorem rankinSparseBlock12_3_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock12_3 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock12_3
  positivity

noncomputable def rankinSparseBlock13_0 (a b : ℝ) : ℝ :=
      2*a*(1-a)*b^3 +
      4*a^3*b^2 +
      31*a*(1-a)*b^2 +
      4*a*b^3 +
      39*a*b*(1-b) +
      31*a*(1-a)*b +
      6*(1-a)*b +
      6*a*(1-b) +
      2*b*(1-b) +
      2*a*(1-a)

theorem rankinSparseBlock13_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock13_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock13_0
  positivity

noncomputable def rankinSparseBlock13_1 (a b : ℝ) : ℝ :=
      2*a^4*b^2*(1-b) +
      6*a^2*(1-a)*(1-b)^3 +
      6*a^3*b^2*(1-b) +
      2*a^2*b^4 +
      16*a^2*b^3 +
      10*a^3*b^2 +
      2*(1-a)^2*b^2 +
      a^2*(1-b)^2 +
      a^2*(1-b)

theorem rankinSparseBlock13_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock13_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock13_1
  positivity

noncomputable def rankinSparseBlock14_0 (a b : ℝ) : ℝ :=
      2*(1-a)^2*b^3 +
      4*a^3*b*(1-b) +
      5*a*(1-a)*b*(1-b) +
      26*a^2*b^2 +
      2*(1-a)*b^3 +
      2*(1-a)*b*(1-b) +
      5*a*b^2 +
      4*a^3*(1-b) +
      2*a*(1-a)*(1-b)

theorem rankinSparseBlock14_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock14_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock14_0
  positivity

noncomputable def rankinSparseBlock14_1 (a b : ℝ) : ℝ :=
      2*a^4*b^3

theorem rankinSparseBlock14_1_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock14_1 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock14_1
  positivity

noncomputable def rankinSparseBlock15_0 (a b : ℝ) : ℝ :=
      a*b +
      b +
      a

theorem rankinSparseBlock15_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock15_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock15_0
  positivity

noncomputable def rankinSparseBlock16_0 (a b : ℝ) : ℝ :=
      a*b

theorem rankinSparseBlock16_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock16_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock16_0
  positivity

noncomputable def rankinSparseBlock17_0 (a b : ℝ) : ℝ :=
      a*b

theorem rankinSparseBlock17_0_nonneg (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinSparseBlock17_0 a b := by
  have ha2 : 0 ≤ 1-a := by linarith
  have hb2 : 0 ≤ 1-b := by linarith
  unfold rankinSparseBlock17_0
  positivity

noncomputable def rankinCoupledSparseBlockCertificate (r a b : ℝ) : ℝ :=
      (1-r)^6*rankinSparseBlock0_6 a b +
      (1-r)^7*rankinSparseBlock0_7 a b +
      r*rankinSparseBlock1_0 a b +
      r*(1-r)*rankinSparseBlock1_1 a b +
      r*(1-r)^3*rankinSparseBlock1_3 a b +
      r*(1-r)^4*rankinSparseBlock1_4 a b +
      r*(1-r)^5*rankinSparseBlock1_5 a b +
      r*(1-r)^6*rankinSparseBlock1_6 a b +
      r*(1-r)^7*rankinSparseBlock1_7 a b +
      r^2*rankinSparseBlock2_0 a b +
      r^2*(1-r)*rankinSparseBlock2_1 a b +
      r^2*(1-r)^3*rankinSparseBlock2_3 a b +
      r^2*(1-r)^4*rankinSparseBlock2_4 a b +
      r^2*(1-r)^5*rankinSparseBlock2_5 a b +
      r^2*(1-r)^6*rankinSparseBlock2_6 a b +
      r^2*(1-r)^7*rankinSparseBlock2_7 a b +
      r^2*(1-r)^8*rankinSparseBlock2_8 a b +
      r^2*(1-r)^9*rankinSparseBlock2_9 a b +
      r^3*rankinSparseBlock3_0 a b +
      r^3*(1-r)*rankinSparseBlock3_1 a b +
      r^3*(1-r)^3*rankinSparseBlock3_3 a b +
      r^3*(1-r)^4*rankinSparseBlock3_4 a b +
      r^3*(1-r)^5*rankinSparseBlock3_5 a b +
      r^3*(1-r)^6*rankinSparseBlock3_6 a b +
      r^3*(1-r)^7*rankinSparseBlock3_7 a b +
      r^3*(1-r)^8*rankinSparseBlock3_8 a b +
      r^3*(1-r)^9*rankinSparseBlock3_9 a b +
      r^4*rankinSparseBlock4_0 a b +
      r^4*(1-r)*rankinSparseBlock4_1 a b +
      r^4*(1-r)^3*rankinSparseBlock4_3 a b +
      r^4*(1-r)^4*rankinSparseBlock4_4 a b +
      r^4*(1-r)^5*rankinSparseBlock4_5 a b +
      r^4*(1-r)^6*rankinSparseBlock4_6 a b +
      r^4*(1-r)^7*rankinSparseBlock4_7 a b +
      r^4*(1-r)^8*rankinSparseBlock4_8 a b +
      r^4*(1-r)^9*rankinSparseBlock4_9 a b +
      r^5*rankinSparseBlock5_0 a b +
      r^5*(1-r)*rankinSparseBlock5_1 a b +
      r^5*(1-r)^3*rankinSparseBlock5_3 a b +
      r^5*(1-r)^4*rankinSparseBlock5_4 a b +
      r^5*(1-r)^5*rankinSparseBlock5_5 a b +
      r^5*(1-r)^6*rankinSparseBlock5_6 a b +
      r^5*(1-r)^7*rankinSparseBlock5_7 a b +
      r^5*(1-r)^8*rankinSparseBlock5_8 a b +
      r^5*(1-r)^9*rankinSparseBlock5_9 a b +
      r^6*rankinSparseBlock6_0 a b +
      r^6*(1-r)*rankinSparseBlock6_1 a b +
      r^6*(1-r)^3*rankinSparseBlock6_3 a b +
      r^6*(1-r)^4*rankinSparseBlock6_4 a b +
      r^6*(1-r)^5*rankinSparseBlock6_5 a b +
      r^6*(1-r)^6*rankinSparseBlock6_6 a b +
      r^6*(1-r)^7*rankinSparseBlock6_7 a b +
      r^6*(1-r)^8*rankinSparseBlock6_8 a b +
      r^6*(1-r)^9*rankinSparseBlock6_9 a b +
      r^7*rankinSparseBlock7_0 a b +
      r^7*(1-r)*rankinSparseBlock7_1 a b +
      r^7*(1-r)^2*rankinSparseBlock7_2 a b +
      r^7*(1-r)^3*rankinSparseBlock7_3 a b +
      r^7*(1-r)^4*rankinSparseBlock7_4 a b +
      r^7*(1-r)^5*rankinSparseBlock7_5 a b +
      r^7*(1-r)^6*rankinSparseBlock7_6 a b +
      r^7*(1-r)^7*rankinSparseBlock7_7 a b +
      r^7*(1-r)^8*rankinSparseBlock7_8 a b +
      r^8*rankinSparseBlock8_0 a b +
      r^8*(1-r)*rankinSparseBlock8_1 a b +
      r^8*(1-r)^3*rankinSparseBlock8_3 a b +
      r^8*(1-r)^4*rankinSparseBlock8_4 a b +
      r^8*(1-r)^5*rankinSparseBlock8_5 a b +
      r^8*(1-r)^6*rankinSparseBlock8_6 a b +
      r^8*(1-r)^7*rankinSparseBlock8_7 a b +
      r^9*rankinSparseBlock9_0 a b +
      r^9*(1-r)*rankinSparseBlock9_1 a b +
      r^9*(1-r)^2*rankinSparseBlock9_2 a b +
      r^9*(1-r)^3*rankinSparseBlock9_3 a b +
      r^9*(1-r)^4*rankinSparseBlock9_4 a b +
      r^9*(1-r)^5*rankinSparseBlock9_5 a b +
      r^9*(1-r)^6*rankinSparseBlock9_6 a b +
      r^10*rankinSparseBlock10_0 a b +
      r^10*(1-r)*rankinSparseBlock10_1 a b +
      r^10*(1-r)^2*rankinSparseBlock10_2 a b +
      r^10*(1-r)^3*rankinSparseBlock10_3 a b +
      r^10*(1-r)^4*rankinSparseBlock10_4 a b +
      r^11*rankinSparseBlock11_0 a b +
      r^11*(1-r)*rankinSparseBlock11_1 a b +
      r^11*(1-r)^2*rankinSparseBlock11_2 a b +
      r^11*(1-r)^3*rankinSparseBlock11_3 a b +
      r^11*(1-r)^4*rankinSparseBlock11_4 a b +
      r^12*rankinSparseBlock12_0 a b +
      r^12*(1-r)*rankinSparseBlock12_1 a b +
      r^12*(1-r)^2*rankinSparseBlock12_2 a b +
      r^12*(1-r)^3*rankinSparseBlock12_3 a b +
      r^13*rankinSparseBlock13_0 a b +
      r^13*(1-r)*rankinSparseBlock13_1 a b +
      r^14*rankinSparseBlock14_0 a b +
      r^14*(1-r)*rankinSparseBlock14_1 a b +
      r^15*rankinSparseBlock15_0 a b +
      r^16*rankinSparseBlock16_0 a b +
      r^17*rankinSparseBlock17_0 a b

theorem rankinCoupledSparseBlockCertificate_nonneg (r a b : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : 0 ≤ rankinCoupledSparseBlockCertificate r a b := by
  have hr2 : 0 ≤ 1-r := by linarith
  have h0_6 := rankinSparseBlock0_6_nonneg a b ha ha1 hb hb1
  have h0_7 := rankinSparseBlock0_7_nonneg a b ha ha1 hb hb1
  have h1_0 := rankinSparseBlock1_0_nonneg a b ha ha1 hb hb1
  have h1_1 := rankinSparseBlock1_1_nonneg a b ha ha1 hb hb1
  have h1_3 := rankinSparseBlock1_3_nonneg a b ha ha1 hb hb1
  have h1_4 := rankinSparseBlock1_4_nonneg a b ha ha1 hb hb1
  have h1_5 := rankinSparseBlock1_5_nonneg a b ha ha1 hb hb1
  have h1_6 := rankinSparseBlock1_6_nonneg a b ha ha1 hb hb1
  have h1_7 := rankinSparseBlock1_7_nonneg a b ha ha1 hb hb1
  have h2_0 := rankinSparseBlock2_0_nonneg a b ha ha1 hb hb1
  have h2_1 := rankinSparseBlock2_1_nonneg a b ha ha1 hb hb1
  have h2_3 := rankinSparseBlock2_3_nonneg a b ha ha1 hb hb1
  have h2_4 := rankinSparseBlock2_4_nonneg a b ha ha1 hb hb1
  have h2_5 := rankinSparseBlock2_5_nonneg a b ha ha1 hb hb1
  have h2_6 := rankinSparseBlock2_6_nonneg a b ha ha1 hb hb1
  have h2_7 := rankinSparseBlock2_7_nonneg a b ha ha1 hb hb1
  have h2_8 := rankinSparseBlock2_8_nonneg a b ha ha1 hb hb1
  have h2_9 := rankinSparseBlock2_9_nonneg a b ha ha1 hb hb1
  have h3_0 := rankinSparseBlock3_0_nonneg a b ha ha1 hb hb1
  have h3_1 := rankinSparseBlock3_1_nonneg a b ha ha1 hb hb1
  have h3_3 := rankinSparseBlock3_3_nonneg a b ha ha1 hb hb1
  have h3_4 := rankinSparseBlock3_4_nonneg a b ha ha1 hb hb1
  have h3_5 := rankinSparseBlock3_5_nonneg a b ha ha1 hb hb1
  have h3_6 := rankinSparseBlock3_6_nonneg a b ha ha1 hb hb1
  have h3_7 := rankinSparseBlock3_7_nonneg a b ha ha1 hb hb1
  have h3_8 := rankinSparseBlock3_8_nonneg a b ha ha1 hb hb1
  have h3_9 := rankinSparseBlock3_9_nonneg a b ha ha1 hb hb1
  have h4_0 := rankinSparseBlock4_0_nonneg a b ha ha1 hb hb1
  have h4_1 := rankinSparseBlock4_1_nonneg a b ha ha1 hb hb1
  have h4_3 := rankinSparseBlock4_3_nonneg a b ha ha1 hb hb1
  have h4_4 := rankinSparseBlock4_4_nonneg a b ha ha1 hb hb1
  have h4_5 := rankinSparseBlock4_5_nonneg a b ha ha1 hb hb1
  have h4_6 := rankinSparseBlock4_6_nonneg a b ha ha1 hb hb1
  have h4_7 := rankinSparseBlock4_7_nonneg a b ha ha1 hb hb1
  have h4_8 := rankinSparseBlock4_8_nonneg a b ha ha1 hb hb1
  have h4_9 := rankinSparseBlock4_9_nonneg a b ha ha1 hb hb1
  have h5_0 := rankinSparseBlock5_0_nonneg a b ha ha1 hb hb1
  have h5_1 := rankinSparseBlock5_1_nonneg a b ha ha1 hb hb1
  have h5_3 := rankinSparseBlock5_3_nonneg a b ha ha1 hb hb1
  have h5_4 := rankinSparseBlock5_4_nonneg a b ha ha1 hb hb1
  have h5_5 := rankinSparseBlock5_5_nonneg a b ha ha1 hb hb1
  have h5_6 := rankinSparseBlock5_6_nonneg a b ha ha1 hb hb1
  have h5_7 := rankinSparseBlock5_7_nonneg a b ha ha1 hb hb1
  have h5_8 := rankinSparseBlock5_8_nonneg a b ha ha1 hb hb1
  have h5_9 := rankinSparseBlock5_9_nonneg a b ha ha1 hb hb1
  have h6_0 := rankinSparseBlock6_0_nonneg a b ha ha1 hb hb1
  have h6_1 := rankinSparseBlock6_1_nonneg a b ha ha1 hb hb1
  have h6_3 := rankinSparseBlock6_3_nonneg a b ha ha1 hb hb1
  have h6_4 := rankinSparseBlock6_4_nonneg a b ha ha1 hb hb1
  have h6_5 := rankinSparseBlock6_5_nonneg a b ha ha1 hb hb1
  have h6_6 := rankinSparseBlock6_6_nonneg a b ha ha1 hb hb1
  have h6_7 := rankinSparseBlock6_7_nonneg a b ha ha1 hb hb1
  have h6_8 := rankinSparseBlock6_8_nonneg a b ha ha1 hb hb1
  have h6_9 := rankinSparseBlock6_9_nonneg a b ha ha1 hb hb1
  have h7_0 := rankinSparseBlock7_0_nonneg a b ha ha1 hb hb1
  have h7_1 := rankinSparseBlock7_1_nonneg a b ha ha1 hb hb1
  have h7_2 := rankinSparseBlock7_2_nonneg a b ha ha1 hb hb1
  have h7_3 := rankinSparseBlock7_3_nonneg a b ha ha1 hb hb1
  have h7_4 := rankinSparseBlock7_4_nonneg a b ha ha1 hb hb1
  have h7_5 := rankinSparseBlock7_5_nonneg a b ha ha1 hb hb1
  have h7_6 := rankinSparseBlock7_6_nonneg a b ha ha1 hb hb1
  have h7_7 := rankinSparseBlock7_7_nonneg a b ha ha1 hb hb1
  have h7_8 := rankinSparseBlock7_8_nonneg a b ha ha1 hb hb1
  have h8_0 := rankinSparseBlock8_0_nonneg a b ha ha1 hb hb1
  have h8_1 := rankinSparseBlock8_1_nonneg a b ha ha1 hb hb1
  have h8_3 := rankinSparseBlock8_3_nonneg a b ha ha1 hb hb1
  have h8_4 := rankinSparseBlock8_4_nonneg a b ha ha1 hb hb1
  have h8_5 := rankinSparseBlock8_5_nonneg a b ha ha1 hb hb1
  have h8_6 := rankinSparseBlock8_6_nonneg a b ha ha1 hb hb1
  have h8_7 := rankinSparseBlock8_7_nonneg a b ha ha1 hb hb1
  have h9_0 := rankinSparseBlock9_0_nonneg a b ha ha1 hb hb1
  have h9_1 := rankinSparseBlock9_1_nonneg a b ha ha1 hb hb1
  have h9_2 := rankinSparseBlock9_2_nonneg a b ha ha1 hb hb1
  have h9_3 := rankinSparseBlock9_3_nonneg a b ha ha1 hb hb1
  have h9_4 := rankinSparseBlock9_4_nonneg a b ha ha1 hb hb1
  have h9_5 := rankinSparseBlock9_5_nonneg a b ha ha1 hb hb1
  have h9_6 := rankinSparseBlock9_6_nonneg a b ha ha1 hb hb1
  have h10_0 := rankinSparseBlock10_0_nonneg a b ha ha1 hb hb1
  have h10_1 := rankinSparseBlock10_1_nonneg a b ha ha1 hb hb1
  have h10_2 := rankinSparseBlock10_2_nonneg a b ha ha1 hb hb1
  have h10_3 := rankinSparseBlock10_3_nonneg a b ha ha1 hb hb1
  have h10_4 := rankinSparseBlock10_4_nonneg a b ha ha1 hb hb1
  have h11_0 := rankinSparseBlock11_0_nonneg a b ha ha1 hb hb1
  have h11_1 := rankinSparseBlock11_1_nonneg a b ha ha1 hb hb1
  have h11_2 := rankinSparseBlock11_2_nonneg a b ha ha1 hb hb1
  have h11_3 := rankinSparseBlock11_3_nonneg a b ha ha1 hb hb1
  have h11_4 := rankinSparseBlock11_4_nonneg a b ha ha1 hb hb1
  have h12_0 := rankinSparseBlock12_0_nonneg a b ha ha1 hb hb1
  have h12_1 := rankinSparseBlock12_1_nonneg a b ha ha1 hb hb1
  have h12_2 := rankinSparseBlock12_2_nonneg a b ha ha1 hb hb1
  have h12_3 := rankinSparseBlock12_3_nonneg a b ha ha1 hb hb1
  have h13_0 := rankinSparseBlock13_0_nonneg a b ha ha1 hb hb1
  have h13_1 := rankinSparseBlock13_1_nonneg a b ha ha1 hb hb1
  have h14_0 := rankinSparseBlock14_0_nonneg a b ha ha1 hb hb1
  have h14_1 := rankinSparseBlock14_1_nonneg a b ha ha1 hb hb1
  have h15_0 := rankinSparseBlock15_0_nonneg a b ha ha1 hb hb1
  have h16_0 := rankinSparseBlock16_0_nonneg a b ha ha1 hb hb1
  have h17_0 := rankinSparseBlock17_0_nonneg a b ha ha1 hb hb1
  unfold rankinCoupledSparseBlockCertificate
  positivity

theorem rankin_coupled_sparse_block_polynomial_certificate (r a b : ℝ) :
    let x := r^2
    let y := x+a*(r-x)
    let z := x+b*(r-x)
    (1-x^3)^2*(1-x^4)*((1-y+x)*(1-z+x))
      - (1-y*z)*(1-y*z^2)*(1-y^2*z)*((1-y+x)*(1-z+x)+y*z)
      = r^4*(1-r)^3*rankinCoupledSparseBlockCertificate r a b := by
  dsimp only
  unfold rankinCoupledSparseBlockCertificate rankinSparseBlock0_6 rankinSparseBlock0_7 rankinSparseBlock1_0 rankinSparseBlock1_1 rankinSparseBlock1_3 rankinSparseBlock1_4 rankinSparseBlock1_5 rankinSparseBlock1_6 rankinSparseBlock1_7 rankinSparseBlock2_0 rankinSparseBlock2_1 rankinSparseBlock2_3 rankinSparseBlock2_4 rankinSparseBlock2_5 rankinSparseBlock2_6 rankinSparseBlock2_7 rankinSparseBlock2_8 rankinSparseBlock2_9 rankinSparseBlock3_0 rankinSparseBlock3_1 rankinSparseBlock3_3 rankinSparseBlock3_4 rankinSparseBlock3_5 rankinSparseBlock3_6 rankinSparseBlock3_7 rankinSparseBlock3_8 rankinSparseBlock3_9 rankinSparseBlock4_0 rankinSparseBlock4_1 rankinSparseBlock4_3 rankinSparseBlock4_4 rankinSparseBlock4_5 rankinSparseBlock4_6 rankinSparseBlock4_7 rankinSparseBlock4_8 rankinSparseBlock4_9 rankinSparseBlock5_0 rankinSparseBlock5_1 rankinSparseBlock5_3 rankinSparseBlock5_4 rankinSparseBlock5_5 rankinSparseBlock5_6 rankinSparseBlock5_7 rankinSparseBlock5_8 rankinSparseBlock5_9 rankinSparseBlock6_0 rankinSparseBlock6_1 rankinSparseBlock6_3 rankinSparseBlock6_4 rankinSparseBlock6_5 rankinSparseBlock6_6 rankinSparseBlock6_7 rankinSparseBlock6_8 rankinSparseBlock6_9 rankinSparseBlock7_0 rankinSparseBlock7_1 rankinSparseBlock7_2 rankinSparseBlock7_3 rankinSparseBlock7_4 rankinSparseBlock7_5 rankinSparseBlock7_6 rankinSparseBlock7_7 rankinSparseBlock7_8 rankinSparseBlock8_0 rankinSparseBlock8_1 rankinSparseBlock8_3 rankinSparseBlock8_4 rankinSparseBlock8_5 rankinSparseBlock8_6 rankinSparseBlock8_7 rankinSparseBlock9_0 rankinSparseBlock9_1 rankinSparseBlock9_2 rankinSparseBlock9_3 rankinSparseBlock9_4 rankinSparseBlock9_5 rankinSparseBlock9_6 rankinSparseBlock10_0 rankinSparseBlock10_1 rankinSparseBlock10_2 rankinSparseBlock10_3 rankinSparseBlock10_4 rankinSparseBlock11_0 rankinSparseBlock11_1 rankinSparseBlock11_2 rankinSparseBlock11_3 rankinSparseBlock11_4 rankinSparseBlock12_0 rankinSparseBlock12_1 rankinSparseBlock12_2 rankinSparseBlock12_3 rankinSparseBlock13_0 rankinSparseBlock13_1 rankinSparseBlock14_0 rankinSparseBlock14_1 rankinSparseBlock15_0 rankinSparseBlock16_0 rankinSparseBlock17_0
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Helfgott

theorem rankin_coupled_euler_factor_upper_sparse_block (x y z : ℝ) (hx : 0 < x)
    (hxy : x ≤ y) (hxz : x ≤ z) (hy : y < 1) (hz : z < 1)
    (hysq : y^2 ≤ x) (hzsq : z^2 ≤ x) :
    1+y*z/((1-y+x)*(1-z+x)) ≤
      (1-x^3)^2*(1-x^4)/((1-y*z)*(1-y*z^2)*(1-y^2*z)) := by
  have hy0 : 0 ≤ y := hx.le.trans hxy
  have hz0 : 0 ≤ z := hx.le.trans hxz
  have hx1 : x < 1 := hxy.trans_lt hy
  let r := Real.sqrt x
  have hr0 : 0 < r := Real.sqrt_pos.2 hx
  have hr2 : r^2 = x := Real.sq_sqrt hx.le
  have hr1 : r < 1 := by nlinarith
  have hxr : x < r := by nlinarith
  have hyr : y ≤ r := by nlinarith
  have hzr : z ≤ r := by nlinarith
  let a := (y-x)/(r-x)
  let b := (z-x)/(r-x)
  have hden : 0 < r-x := by linarith
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hden.le
  have hb0 : 0 ≤ b := div_nonneg (by linarith) hden.le
  have ha1 : a ≤ 1 := (div_le_one hden).2 (by linarith)
  have hb1 : b ≤ 1 := (div_le_one hden).2 (by linarith)
  have hya : x+a*(r-x)=y := by dsimp [a]; field_simp; ring
  have hzb : x+b*(r-x)=z := by dsimp [b]; field_simp; ring
  have hcert := rankin_coupled_sparse_block_polynomial_certificate r a b
  dsimp only at hcert
  rw [hr2,hya,hzb] at hcert
  have hnonneg := rankinCoupledSparseBlockCertificate_nonneg r a b hr0.le hr1.le ha0 ha1 hb0 hb1
  have hP : 0 ≤ (1-x^3)^2*(1-x^4)*((1-y+x)*(1-z+x))
      -(1-y*z)*(1-y*z^2)*(1-y^2*z)*((1-y+x)*(1-z+x)+y*z) := by
    rw [hcert]
    exact mul_nonneg (mul_nonneg (pow_nonneg hr0.le 4) (pow_nonneg (by linarith) 3)) hnonneg
  have hy2 : y^2 < 1 := by nlinarith
  have hz2 : z^2 < 1 := by nlinarith
  have hyz : y*z < 1 := (show y*z ≤ z by nlinarith).trans_lt hz
  have hyzz : y*z^2 < 1 := (show y*z^2 ≤ z^2 by nlinarith [sq_nonneg z]).trans_lt hz2
  have hyyz : y^2*z < 1 := (show y^2*z ≤ y^2 by nlinarith [sq_nonneg y]).trans_lt hy2
  have hA : 0 < (1-y+x)*(1-z+x) := mul_pos (by linarith) (by linarith)
  have hD : 0 < (1-y*z)*(1-y*z^2)*(1-y^2*z) := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have he : 1+y*z/((1-y+x)*(1-z+x)) = ((1-y+x)*(1-z+x)+y*z)/((1-y+x)*(1-z+x)) := by
    rw [add_div,div_self (ne_of_gt hA)]
  rw [he]
  apply (div_le_div_iff₀ hA hD).mpr
  nlinarith only [hP]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Helfgott

theorem rankin_coupled_prime_factor_upper_sparse_block (p s t : ℝ) (hp : 1 < p)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) :
    1+p^(-s-t)/((1-p^(-s)+p^(-1:ℝ))*(1-p^(-t)+p^(-1:ℝ))) ≤
      (1-p^(-3:ℝ))^2*(1-p^(-4:ℝ))/
        ((1-p^(-s-t))*(1-p^(-s-2*t))*(1-p^(-2*s-t))) := by
  have hp0 : 0 < p := by linarith
  have hx : 0 < p^(-1:ℝ) := Real.rpow_pos_of_pos hp0 _
  have hxy : p^(-1:ℝ) ≤ p^(-s) := Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
  have hxz : p^(-1:ℝ) ≤ p^(-t) := Real.rpow_le_rpow_of_exponent_le hp.le (by linarith)
  have hy : p^(-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hz : p^(-t) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hysq : (p^(-s))^2 ≤ p^(-1:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2]
    exact Real.rpow_le_rpow_of_exponent_le hp.le (by norm_num;linarith)
  have hzsq : (p^(-t))^2 ≤ p^(-1:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-t) 2]
    exact Real.rpow_le_rpow_of_exponent_le hp.le (by norm_num;linarith)
  have h := rankin_coupled_euler_factor_upper_sparse_block (p^(-1:ℝ)) (p^(-s)) (p^(-t)) hx hxy hxz hy hz hysq hzsq
  have hst : p^(-s)*p^(-t)=p^(-s-t) := by
    rw [←Real.rpow_add hp0]
    congr 1 <;> ring
  have hstt : p^(-s)*(p^(-t))^2=p^(-s-2*t) := by
    rw [←Real.rpow_mul_natCast hp0.le (-t) 2,←Real.rpow_add hp0]
    congr 1 <;> ring
  have hsst : (p^(-s))^2*p^(-t)=p^(-2*s-t) := by
    rw [←Real.rpow_mul_natCast hp0.le (-s) 2,←Real.rpow_add hp0]
    congr 1 <;> ring
  have h3 : (p^(-1:ℝ))^3=p^(-3:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-1) 3];norm_num
  have h4 : (p^(-1:ℝ))^4=p^(-4:ℝ) := by
    rw [←Real.rpow_mul_natCast hp0.le (-1) 4];norm_num
  simpa only [hst,hstt,hsst,h3,h4] using h

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 3500000
open Finset Nat Real Filter
open scoped BigOperators Topology Classical
namespace Helfgott

lemma rankin_coupled_comparison_hasProd_sparse (s t : ℝ) (hs0 : 1/2 ≤ s) (ht0 : 1/2 ≤ t)
    (hst : 1 < s+t) :
    HasProd (fun p : Nat.Primes =>
      (1-(p : ℝ)^(-3:ℝ))^2*(1-(p : ℝ)^(-4:ℝ))/
      ((1-(p : ℝ)^(-s-t))*(1-(p : ℝ)^(-s-2*t))*(1-(p : ℝ)^(-2*s-t))))
      ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t))/
        ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ)))) := by
  have h3 := (real_zeta_euler_hasProd 3 (by norm_num)).inv₀ (ne_of_gt (real_zeta_sum_pos 3 (by norm_num)))
  have h4 := (real_zeta_euler_hasProd 4 (by norm_num)).inv₀ (ne_of_gt (real_zeta_sum_pos 4 (by norm_num)))
  have hst1 := real_zeta_euler_hasProd (s+t) hst
  have hst2 := real_zeta_euler_hasProd (s+2*t) (by linarith)
  have hst3 := real_zeta_euler_hasProd (2*s+t) (by linarith)
  have h := ((h3.pow 2).mul h4).mul ((hst1.mul hst2).mul hst3)
  have he1 : (fun n : ℕ => (n : ℝ)^(-(s+t)))=(fun n : ℕ => (n : ℝ)^(-s-t)) := by funext n;congr 1;ring
  have he2 : (fun n : ℕ => (n : ℝ)^(-(s+2*t)))=(fun n : ℕ => (n : ℝ)^(-s-2*t)) := by funext n;congr 1;ring
  have he3 : (fun n : ℕ => (n : ℝ)^(-(2*s+t)))=(fun n : ℕ => (n : ℝ)^(-2*s-t)) := by funext n;congr 1;ring
  rw [he1,he2,he3] at h
  have hv : ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))⁻¹)^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))⁻¹ *
      (((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t)))*(∑' n : ℕ,(n : ℝ)^(-2*s-t))) =
      ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
      ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))) := by
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow];ring
  rw [hv] at h
  apply h.congr_fun
  intro p
  have e1 : -(s+t)=-s-t := by ring
  have e2 : -(s+2*t)=-s-2*t := by ring
  have e3 : -(2*s+t)=-2*s-t := by ring
  simp only [inv_inv,e1,e2,e3,div_eq_mul_inv,mul_inv_rev]
  ring

theorem rankin_coupled_finite_prime_product_upper_sparse (P : Finset Nat.Primes) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    (∏ p∈P,(1+(p : ℝ)^(-s-t)/((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
        ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))) := by
  let f : Nat.Primes → ℝ := fun p => 1+(p : ℝ)^(-s-t)/
    ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)))
  let g : Nat.Primes → ℝ := fun p => (1-(p : ℝ)^(-3:ℝ))^2*(1-(p : ℝ)^(-4:ℝ))/
    ((1-(p : ℝ)^(-s-t))*(1-(p : ℝ)^(-s-2*t))*(1-(p : ℝ)^(-2*s-t)))
  have hf1 (p : Nat.Primes) : 1 ≤ f p := by
    have hp : (1:ℝ)<p := by exact_mod_cast p.property.one_lt
    have hp0 : (0:ℝ)<p := by linarith
    have hy : (p : ℝ)^(-s)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
    have hz : (p : ℝ)^(-t)<1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
    dsimp [f]
    have hd : 0<(1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ)) :=
      mul_pos (by linarith [Real.rpow_pos_of_pos hp0 (-1)]) (by linarith [Real.rpow_pos_of_pos hp0 (-1)])
    exact le_add_of_nonneg_right (div_nonneg (Real.rpow_nonneg hp0.le _) hd.le)
  have hfg (p : Nat.Primes) : f p ≤ g p :=
    rankin_coupled_prime_factor_upper_sparse_block (p : ℝ) s t (by exact_mod_cast p.property.one_lt) hs0 hs1 ht0 ht1
  have hg1 (p : Nat.Primes) : 1 ≤ g p := (hf1 p).trans (hfg p)
  have hP : (∏ p∈P,f p) ≤ ∏ p∈P,g p := Finset.prod_le_prod (fun p _ => (by norm_num : (0:ℝ)≤1).trans (hf1 p)) (fun p _ => hfg p)
  apply hP.trans
  apply ge_of_tendsto (rankin_coupled_comparison_hasProd_sparse s t hs0 ht0 hst)
  exact Filter.eventually_atTop.mpr ⟨P,fun T hPT => Finset.prod_le_prod_of_subset_of_one_le hPT
    (fun p _ => (by norm_num : (0:ℝ)≤1).trans (hg1 p)) (fun p _ _ => hg1 p)⟩

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (P : Finset Nat.Primes) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    (∏ p∈P,(1+(p : ℝ)^(-s-t)/((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))) ≤
      ((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
        ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))) := Helfgott.rankin_coupled_finite_prime_product_upper_sparse P s t hs0 hs1 ht0 ht1 hst

#print axioms solution
