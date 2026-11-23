-- Prove2me | solution 1 for GlobalTheory.FormalSeries.le_order_subst_sub_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:21.093809+00:00
-- url     : https://prove2.me/submissions/05ca1cdb-f898-40c1-af32-910b3233b409

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply
attribute [local simp] GlobalTheory.FormalSeries.jacobian_X
section
noncomputable section
namespace GlobalTheory
namespace FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
private theorem Close.one (k : ℕ) : Close k 0 (1 : MvPowerSeries τ S) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  simp
private theorem Close.mul {k n m : ℕ} {P Q P' Q' : MvPowerSeries τ S} (h : Close k n P Q)
    (h' : Close k m P' Q') : Close k (n + m) (P * P') (Q * Q') := by
  obtain ⟨hP, hQ, hPQ⟩ := h
  obtain ⟨hP', hQ', hPQ'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    exact (add_le_add hP hP').trans le_order_mul
  · push_cast
    exact (add_le_add hQ hQ').trans le_order_mul
  · have e : P * P' - Q * Q' = (P - Q) * P' + Q * (P' - Q') := by ring
    rw [e]
    have h1 : ((k + (n + m) : ℕ) : ℕ∞) ≤ ((P - Q) * P').order + 1 :=
      calc ((k + (n + m) : ℕ) : ℕ∞) = ((k + n : ℕ) : ℕ∞) + m := by push_cast; ring
        _ ≤ ((P - Q).order + 1) + P'.order := add_le_add hPQ hP'
        _ = ((P - Q).order + P'.order) + 1 := by ring
        _ ≤ ((P - Q) * P').order + 1 := by gcongr; exact le_order_mul
    have h2 : ((k + (n + m) : ℕ) : ℕ∞) ≤ (Q * (P' - Q')).order + 1 :=
      calc ((k + (n + m) : ℕ) : ℕ∞) = n + ((k + m : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ Q.order + ((P' - Q').order + 1) := add_le_add hQ hPQ'
        _ = (Q.order + (P' - Q').order) + 1 := by ring
        _ ≤ (Q * (P' - Q')).order + 1 := by gcongr; exact le_order_mul
    calc ((k + (n + m) : ℕ) : ℕ∞)
        ≤ min (((P - Q) * P').order + 1) ((Q * (P' - Q')).order + 1) := le_min h1 h2
      _ = min ((P - Q) * P').order (Q * (P' - Q')).order + 1 := min_add_add_right _ _ _
      _ ≤ ((P - Q) * P' + Q * (P' - Q')).order + 1 := by gcongr; exact min_order_le_add
private theorem close_pow_of_close_one {k e : ℕ} {x y : MvPowerSeries τ S} (h : Close k 1 x y) :
    Close k e (x ^ e) (y ^ e) := by
  induction e with
  | zero => simpa using Close.one (τ := τ) (S := S) k
  | succ e ih =>
    rw [pow_succ, pow_succ]
    exact Close.mul ih h
private theorem Close.prod {k : ℕ} {a b : σ → MvPowerSeries τ S}
    (h : ∀ s, Close k 1 (a s) (b s)) (d : σ →₀ ℕ) :
    Close k d.degree (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  induction d using Finsupp.induction with
  | zero => simpa using Close.one (τ := τ) (S := S) k
  | single_add i e d _ _ ih =>
    rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), map_add,
      Finsupp.degree_single]
    exact Close.mul (close_pow_of_close_one (h i)) ih
variable [Algebra R S]
private theorem natCast_lt_of_le_add_one_of_add_two_le {x : ℕ∞} {n m : ℕ} (h : (n : ℕ∞) ≤ x + 1)
    (hm : m + 2 ≤ n) : (m : ℕ∞) < x := by
  induction x using ENat.recTopCoe with
  | top => exact ENat.natCast_lt_top m
  | coe x =>
    have h' : n ≤ x + 1 := by exact_mod_cast h
    exact_mod_cast (by omega : m < x)
end FormalSeries
end GlobalTheory
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FormalSeries
open MvPowerSeries
variable {σ τ υ R S : Type*} [CommRing R] [CommRing S]
variable [Algebra R S]
namespace GlobalTheory.FormalSeries
theorem _root_.solution [Finite σ] {a b : σ → MvPowerSeries τ S}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) {k : ℕ}
    (hab : ∀ s, (k : ℕ∞) ≤ (a s - b s).order) {h : MvPowerSeries σ R} (hh : 2 ≤ h.order) :
    ((k + 1 : ℕ) : ℕ∞) ≤ (h.subst a - h.subst b).order := by
  have ha' : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hb' : HasSubst b := hasSubst_of_constantCoeff_zero hb
  have hc : ∀ s, Close k 1 (a s) (b s) := fun s =>
    ⟨by simpa using one_le_order_iff_constCoeff_eq_zero.mpr (ha s),
      by simpa using one_le_order_iff_constCoeff_eq_zero.mpr (hb s),
      by push_cast; exact add_le_add (hab s) le_rfl⟩
  refine nat_le_order fun e he => ?_
  rw [map_sub, coeff_subst ha', coeff_subst hb',
    ← finsum_sub_distrib (coeff_subst_finite ha' h e) (coeff_subst_finite hb' h e)]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  rw [← smul_sub, ← map_sub]
  by_cases hd : coeff d h = 0
  · rw [hd, zero_smul]
  · have h2 : 2 ≤ d.degree := by
      have := hh.trans (order_le hd)
      exact_mod_cast this
    obtain ⟨-, -, hcl⟩ := Close.prod hc d
    rw [coeff_of_lt_order (natCast_lt_of_le_add_one_of_add_two_le hcl (by omega)), smul_zero]
end GlobalTheory.FormalSeries
