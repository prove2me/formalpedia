-- Prove2me | solution 1 for Helfgott.prime_supported_dirichlet_series_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T16:19:35.541986+00:00
-- url     : https://prove2.me/submissions/9fa4f132-f5ac-4262-86de-c4390b6b09e5

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

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
set_option maxHeartbeats 1800000
open Finset Nat Real
open scoped BigOperators Classical
namespace Helfgott

theorem prime_supported_dirichlet_series_certificate_complete (q : ℕ) (hq : 1≤q) (σ : ℝ) (hσ : 0<σ) :
    let f : ℕ→ℝ := fun n => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0
    Summable f ∧ (∑' n : ℕ,f n)=∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ ∧
      ∀ Y : ℕ,(∑ n∈Finset.Icc 1 Y,f n)≤∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := by
  dsimp only
  have h := prime_supported_dirichlet_series q hq σ hσ
  dsimp only at h
  refine ⟨h.1,h.2,?_⟩
  intro Y
  rw [←h.2]
  exact h.1.sum_le_tsum _ (fun n hn => by split_ifs <;> positivity)

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction
open scoped BigOperators Classical Interval

theorem solution  (q : ℕ) (hq : 1≤q) (σ : ℝ) (hσ : 0<σ) :
    let f : ℕ→ℝ := fun n => if n≠0 ∧ (∀ p∈n.primeFactors,p∣q) then (n : ℝ)^(-σ) else 0
    Summable f ∧ (∑' n : ℕ,f n)=∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ ∧
      ∀ Y : ℕ,(∑ n∈Finset.Icc 1 Y,f n)≤∏ p∈q.primeFactors,(1-(p : ℝ)^(-σ))⁻¹ := Helfgott.prime_supported_dirichlet_series_certificate_complete q hq σ hσ

#print axioms solution
