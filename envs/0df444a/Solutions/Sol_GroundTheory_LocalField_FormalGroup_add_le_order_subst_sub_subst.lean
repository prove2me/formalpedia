-- Prove2me | solution 1 for GroundTheory.LocalField.FormalGroup.add_le_order_subst_sub_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:51.918535+00:00
-- url     : https://prove2.me/submissions/bc7b682b-ee41-4bf7-bd71-8b3f992aad19

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsUniqueFixedPoint
import Definitions.Def_GroundTheory_LocalFields_FormalGroups_Truncation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
section
namespace GroundTheory.LocalField.FormalGroup
open MvPowerSeries
section Subst
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
private lemma close_one (n : ℕ∞) : Close n 0 (1 : MvPowerSeries τ S) 1 := by
  refine ⟨by simp, by simp, ?_⟩
  simp
private lemma close_mul {n k l : ℕ∞} {u v u' v' : MvPowerSeries τ S} (h : Close n k u v)
    (h' : Close n l u' v') : Close n (k + l) (u * u') (v * v') := by
  obtain ⟨hu, hv, huv⟩ := h
  obtain ⟨hu', hv', huv'⟩ := h'
  refine ⟨(add_le_add hu hu').trans (le_order_mul), (add_le_add hv hv').trans (le_order_mul), ?_⟩
  have e : u * u' - v * v' = (u - v) * u' + v * (u' - v') := by ring
  rw [e]
  refine le_trans ?_ (add_le_add min_order_le_add le_rfl)
  rw [← min_add_add_right]
  refine le_min ?_ ?_
  · calc n + (k + l) = (n + k) + l := by rw [add_assoc]
      _ ≤ (order (u - v) + 1) + order u' := add_le_add huv hu'
      _ = (order (u - v) + order u') + 1 := by rw [add_right_comm]
      _ ≤ order ((u - v) * u') + 1 := add_le_add le_order_mul le_rfl
  · calc n + (k + l) = k + (n + l) := by rw [add_left_comm]
      _ ≤ order v + (order (u' - v') + 1) := add_le_add hv huv'
      _ = (order v + order (u' - v')) + 1 := by rw [add_assoc]
      _ ≤ order (v * (u' - v')) + 1 := add_le_add le_order_mul le_rfl
private lemma close_pow {n k : ℕ∞} {u v : MvPowerSeries τ S} (h : Close n k u v) (m : ℕ) :
    Close n (m * k) (u ^ m) (v ^ m) := by
  induction m with
  | zero => simpa using close_one (τ := τ) (S := S) n
  | succ m ih =>
    have := close_mul ih h
    rw [pow_succ, pow_succ]
    convert this using 1
    push_cast
    ring
private lemma close_prod {ι : Type*} (s : Finset ι) {n : ℕ∞} {k : ι → ℕ∞}
    {u v : ι → MvPowerSeries τ S} (h : ∀ i ∈ s, Close n (k i) (u i) (v i)) :
    Close n (∑ i ∈ s, k i) (∏ i ∈ s, u i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using close_one (τ := τ) (S := S) n
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact close_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
private lemma close_monomial {n : ℕ∞} {a b : σ → MvPowerSeries τ S}
    (h : ∀ i, Close n 1 (a i) (b i)) (d : σ →₀ ℕ) :
    Close n (d.degree : ℕ∞) (d.prod fun s e => a s ^ e) (d.prod fun s e => b s ^ e) := by
  have := close_prod d.support (k := fun i => (d i : ℕ∞) * 1) (u := fun i => a i ^ d i)
    (v := fun i => b i ^ d i) (fun i _ => close_pow (h i) (d i))
  simpa [Finsupp.prod, Finsupp.degree_apply] using this
end Subst
section FixedPoint
variable {σ R : Type*} [CommRing R]
end FixedPoint
end GroundTheory.LocalField.FormalGroup
end

set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open MvPowerSeries
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
namespace GroundTheory.LocalField.FormalGroup
theorem _root_.solution {a b : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (hb : HasSubst b) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hb0 : ∀ i, constantCoeff (b i) = 0) {n : ℕ∞} (hab : ∀ i, n ≤ order (a i - b i))
    {f : MvPowerSeries σ R} {m : ℕ∞} (hf : m ≤ order f) :
    n + m ≤ order (subst a f - subst b f) + 1 := by
  have hclose : ∀ i, Close n 1 (a i) (b i) := fun i =>
    ⟨one_le_order_iff_constCoeff_eq_zero.2 (ha0 i),
      one_le_order_iff_constCoeff_eq_zero.2 (hb0 i), add_le_add (hab i) le_rfl⟩

  have hcoeff : ∀ e : τ →₀ ℕ, (e.degree : ℕ∞) + 1 < n + m →
      coeff e (subst a f - subst b f) = 0 := by
    intro e he
    rw [map_sub, coeff_subst ha, coeff_subst hb,
      ← finsum_sub_distrib (coeff_subst_finite ha f e) (coeff_subst_finite hb f e)]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    by_cases hd : coeff d f = 0
    · simp [hd]
    rw [← smul_sub, ← map_sub]
    obtain ⟨-, -, hdc⟩ := close_monomial hclose d
    have hmd : m ≤ (d.degree : ℕ∞) := hf.trans (order_le hd)
    have : (e.degree : ℕ∞) + 1 < order ((d.prod fun s e => a s ^ e) -
        (d.prod fun s e => b s ^ e)) + 1 :=
      he.trans_le ((add_le_add le_rfl hmd).trans hdc)
    rw [coeff_of_lt_order ((ENat.add_lt_add_iff_right ENat.one_ne_top).1 this), smul_zero]
  by_contra hlt
  rw [not_le] at hlt
  have hfin : (order (subst a f - subst b f)).toNat = order (subst a f - subst b f) := by
    refine ENat.natCast_toNat fun htop => ?_
    rw [htop] at hlt
    simp at hlt
  obtain ⟨e, he, hdeg⟩ := exists_coeff_ne_zero_and_order hfin
  exact he (hcoeff e (by rw [hdeg]; exact hlt))
end GroundTheory.LocalField.FormalGroup
