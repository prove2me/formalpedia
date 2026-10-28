-- Prove2me | solution 3 for KellyLossNetworks.RevisedDual.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T02:43:07.704883+00:00
-- url     : https://prove2.me/submissions/02bf637c-3da1-4bee-b27c-24b5abf1d632

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Problem
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Theorems.Thm_KellyStochasticNetworks_erlang_fixed_point_unique

-- carved verbatim out of submission 94d28215-e977-48f5-8010-5c43a6c835b9, lines 1873-1888

section
set_option autoImplicit false
open KellyStochasticNetworks
open Finset

noncomputable def sn3S (N : ℕ) (ν : ℝ) : ℝ := ∑ k ∈ range (N + 1), ν ^ k / (k.factorial : ℝ)

lemma sn3_S_pos (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) : 1 ≤ sn3S N ν := by
  unfold sn3S
  rw [sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  have : 0 ≤ ∑ k ∈ range N, ν ^ (k + 1) / ((k + 1).factorial : ℝ) :=
    sum_nonneg (fun k _ => by positivity)
  linarith

lemma sn3_S_ge (N : ℕ) {ν : ℝ} (_hν : 0 ≤ ν) :
    ν ^ N / (N.factorial : ℝ) + ∑ k ∈ range N, ν ^ k / (k.factorial : ℝ) = sn3S N ν := by
  unfold sn3S; rw [sum_range_succ]; ring

lemma sn3_erlang_eq (ν : ℝ) (N : ℕ) : erlang ν N = (ν ^ N / (N.factorial : ℝ)) / sn3S N ν := rfl

lemma sn3_carried_eq (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    ν * (1 - erlang ν N)
      = (∑ k ∈ range (N + 1), (k : ℝ) * (ν ^ k / (k.factorial : ℝ))) / sn3S N ν := by
  have hS := sn3_S_pos N hν
  have hS0 : sn3S N ν ≠ 0 := by linarith
  rw [sn3_erlang_eq, eq_div_iff hS0]
  have e1 : ν * (1 - ν ^ N / (N.factorial : ℝ) / sn3S N ν) * sn3S N ν
      = ν * (sn3S N ν - ν ^ N / (N.factorial : ℝ)) := by field_simp
  rw [e1, ← sn3_S_ge N hν, sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

end

section
set_option autoImplicit false
open Set Finset
open KellyStochasticNetworks
open KellyLossNetworks
open KellyLossNetworks.RevisedDual

lemma carried_le_capacity (C : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    v * (1 - erlang v C) ≤ C := by
  rw [sn3_carried_eq C hv]
  apply (div_le_iff₀ (by linarith [sn3_S_pos C hv])).mpr
  rw [sn3S, mul_sum]
  apply sum_le_sum
  intro k hk
  have hkC : k ≤ C := Nat.le_of_lt_succ (mem_range.mp hk)
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkC) (by positivity)

lemma erlang_continuousOn (C : ℕ) : ContinuousOn (fun v : ℝ => erlang v C) (Ici 0) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro v hv
    have hp := sn3_S_pos C hv
    change sn3S C v ≠ 0
    linarith

lemma erlang_zero (C : ℕ) (hC : 1 ≤ C) : erlang 0 C = 0 := by
  simp [erlang, zero_pow (by omega : C ≠ 0)]

lemma exists_erlang_inverse (C : ℕ) (hC : 1 ≤ C) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) : ∃ v : ℝ, 0 ≤ v ∧ erlang v C = p := by
  let v : ℝ := (C : ℝ) / (1 - p) + 1
  have hd : 0 < 1 - p := sub_pos.mpr hp1
  have hv : 0 < v := by dsimp [v]; positivity
  have hvc : (C : ℝ) < v * (1 - p) := by
    dsimp [v]
    rw [add_mul, div_mul_cancel₀ _ hd.ne']
    linarith
  have hc := carried_le_capacity C hv.le
  have hpv : p < erlang v C := by nlinarith
  have hcont := (erlang_continuousOn C).mono (Icc_subset_Ici_self : Icc 0 v ⊆ Ici 0)
  obtain ⟨w, hw, he⟩ := intermediate_value_Icc hv.le hcont
    (show p ∈ Icc (erlang 0 C) (erlang v C) by rw [erlang_zero C hC]; exact ⟨hp0, hpv.le⟩)
  exact ⟨w, hw.1, he⟩

lemma exists_load_coordinate (C : ℕ) (hC : 1 ≤ C) {y : ℝ} (hy : 0 ≤ y) :
    ∃ v : ℝ, 0 ≤ v ∧ -Real.log (1 - erlang v C) = y := by
  have he0 := Real.exp_pos (-y)
  have he1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨v, hv, hvp⟩ := exists_erlang_inverse C hC
    (show 0 ≤ 1 - Real.exp (-y) by linarith)
    (show 1 - Real.exp (-y) < 1 by linarith)
  refine ⟨v, hv, ?_⟩
  rw [hvp, sub_sub_cancel, Real.log_exp, neg_neg]

end

section
set_option autoImplicit false
open KellyLossNetworks
open KellyLossNetworks.RevisedDual
open Finset

lemma exponential_tangent (a b : ℝ) :
    Real.exp a + Real.exp a * (b-a) ≤ Real.exp b := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b-a)) (Real.exp_pos a).le
  rw [← Real.exp_add] at h
  rw [show a+(b-a)=b by ring] at h
  nlinarith

end

section
set_option autoImplicit false
open KellyStochasticNetworks
open Finset

lemma sn3_erlang_lt_one (N : ℕ) (hN : 1 ≤ N) {ν : ℝ} (hν : 0 ≤ ν) : erlang ν N < 1 := by
  rw [sn3_erlang_eq, div_lt_one (by linarith [sn3_S_pos N hν]), ← sn3_S_ge N hν]
  have h1 : 1 ≤ ∑ k ∈ range N, ν ^ k / (k.factorial : ℝ) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    have : 0 ≤ ∑ k ∈ range M, ν ^ (k + 1) / ((k + 1).factorial : ℝ) :=
      sum_nonneg (fun k _ => by positivity)
    linarith
  linarith

end

section
set_option autoImplicit false
open KellyStochasticNetworks

lemma sn3_load_nonneg {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r)
    (E : Fin J → ℝ) (hK : ∀ j, E j ∈ Set.Icc (0 : ℝ) 1) (j : Fin J) :
    0 ≤ ∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - E i) ^ (A i r) := by
  apply Finset.sum_nonneg; intro r _
  apply mul_nonneg (mul_nonneg (by positivity) (le_of_lt (hν r)))
  apply Finset.prod_nonneg; intro i _
  exact pow_nonneg (by linarith [(hK i).2]) _

end

section
set_option autoImplicit false
open KellyStochasticNetworks
open Finset

lemma sn3_pow_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {i k : ℕ} (hki : k ≤ i) :
    a ^ i * b ^ k ≤ b ^ i * a ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hki
  have h1 : a ^ d ≤ b ^ d := pow_le_pow_left₀ ha hab d
  have h2 : 0 ≤ a ^ k := pow_nonneg ha k
  have h3 : 0 ≤ b ^ k := pow_nonneg (le_trans ha hab) k
  calc a ^ (k + d) * b ^ k = (a ^ k * b ^ k) * a ^ d := by ring
    _ ≤ (a ^ k * b ^ k) * b ^ d := mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 h3)
    _ = b ^ (k + d) * a ^ k := by ring

lemma sn3_erlang_strict (N : ℕ) (hN : 1 ≤ N) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    erlang a N < erlang b N := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha hab)
  rw [sn3_erlang_eq, sn3_erlang_eq,
    div_lt_div_iff₀ (by linarith [sn3_S_pos N ha]) (by linarith [sn3_S_pos N hb])]
  unfold sn3S
  rw [Finset.mul_sum, Finset.mul_sum, ← sub_neg, ← Finset.sum_sub_distrib]
  have key : ∀ k ∈ range (N + 1), a ^ N / (N.factorial : ℝ) * (b ^ k / (k.factorial : ℝ))
      - b ^ N / (N.factorial : ℝ) * (a ^ k / (k.factorial : ℝ))
      = (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial) := by
    intro k _; ring
  rw [Finset.sum_congr rfl key]
  have hle : ∀ k ∈ range (N + 1),
      (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial) ≤ 0 := by
    intro k hk
    have hk' : k ≤ N := by simp at hk; omega
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [sn3_pow_le ha (le_of_lt hab) hk'])
      (by positivity)
  have hlt : (a ^ N * b ^ 0 - b ^ N * a ^ 0) / ((N.factorial : ℝ) * (Nat.factorial 0 : ℕ)) < 0 := by
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have := pow_lt_pow_left₀ hab ha (by omega : N ≠ 0)
    linarith
  have h := Finset.sum_lt_sum (s := range (N + 1))
    (f := fun k => (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial))
    (g := fun _ => (0 : ℝ)) hle ⟨0, by simp, hlt⟩
  simp only [Finset.sum_const_zero] at h
  exact h

end

section
set_option autoImplicit false
open Set Finset
open KellyStochasticNetworks
open KellyLossNetworks
open KellyLossNetworks.RevisedDual

lemma load_coordinate_injective (C : ℕ) (hC : 1 ≤ C) {v w : ℝ}
    (hv : 0 ≤ v) (hw : 0 ≤ w)
    (he : -Real.log (1 - erlang v C) = -Real.log (1 - erlang w C)) : v = w := by
  have hev := sn3_erlang_lt_one C hC hv
  have hew := sn3_erlang_lt_one C hC hw
  have hl : Real.log (1 - erlang v C) = Real.log (1 - erlang w C) := by linarith
  have harg := Real.log_injOn_pos (sub_pos.mpr hev) (sub_pos.mpr hew) hl
  have heq : erlang v C = erlang w C := by linarith
  rcases lt_trichotomy v w with hlt | hequal | hgt
  · have := sn3_erlang_strict C hC hv hlt; linarith
  · exact hequal
  · have := sn3_erlang_strict C hC hw hgt; linarith

end

section
set_option autoImplicit false
open Set
open KellyStochasticNetworks
open KellyLossNetworks
open KellyLossNetworks.RevisedDual

lemma utilization_coordinate (C : ℕ) (hC : 1 ≤ C) {v : ℝ} (hv : 0 ≤ v) :
    U (-Real.log (1 - erlang v C)) C = v * (1 - erlang v C) := by
  have hex : ∃ w : ℝ, 0 ≤ w ∧ -Real.log (1 - erlang w C) =
      -Real.log (1 - erlang v C) := ⟨v, hv, rfl⟩
  rw [U, dif_pos hex]
  have heq : hex.choose = v := load_coordinate_injective C hC hex.choose_spec.1 hv
    hex.choose_spec.2
  rw [heq]

end

section
set_option autoImplicit false
open KellyLossNetworks
open KellyLossNetworks.RevisedDual
open KellyStochasticNetworks Finset

lemma fixedpoint_coordinates {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j)
    (E : Fin J → ℝ) (hK : ∀ j, E j ∈ Set.Icc (0:ℝ) 1)
    (hF : ErlangFixedPoint A ν C E) :
    (∀ j, 0 ≤ -Real.log (1-E j)) ∧
      StationarityConditions A ν C (fun j => -Real.log (1-E j)) ∧
      E = fun j => 1-Real.exp (-(-Real.log (1-E j))) := by
  let L : Fin J → ℝ := fun j => ∑ r, (A j r:ℝ)*ν r*∏ i, (1-E i)^(A i r)
  let ρ : Fin J → ℝ := fun j => (1-E j)⁻¹ * L j
  have hρ : ∀ j, 0 ≤ ρ j := fun j => mul_nonneg
    (inv_nonneg.mpr (sub_nonneg.mpr (hK j).2)) (sn3_load_nonneg A ν hν E hK j)
  have hlt : ∀ j, E j < 1 := by
    intro j
    rw [hF j]
    exact sn3_erlang_lt_one (C j) (hC j) (hρ j)
  have hexp : ∀ j, Real.exp (-(-Real.log (1-E j))) = 1-E j := by
    intro j
    rw [neg_neg,Real.exp_log (sub_pos.mpr (hlt j))]
  have hprod : ∀ r, Real.exp (-∑ i, (-Real.log (1-E i))*(A i r:ℝ)) =
      ∏ i, (1-E i)^(A i r) := by
    intro r
    rw [← Finset.sum_neg_distrib,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [show -((-Real.log (1-E i))*(A i r:ℝ)) = (A i r:ℝ)*(-(-Real.log (1-E i))) by ring,
      Real.exp_nat_mul,hexp i]
  refine ⟨?_,?_,?_⟩
  · intro j
    exact neg_nonneg.mpr (Real.log_nonpos (sub_nonneg.mpr (hlt j).le) (by linarith [(hK j).1]))
  · intro j
    have hu := utilization_coordinate (C j) (hC j) (hρ j)
    have hE : erlang (ρ j) (C j) = E j := (hF j).symm
    rw [hE] at hu
    rw [hu]
    simp_rw [hprod]
    change L j = ((1-E j)⁻¹ * L j)*(1-E j)
    have hn : 1-E j ≠ 0 := (sub_pos.mpr (hlt j)).ne'
    field_simp
  · funext j
    rw [hexp j]
    ring

end

section
set_option autoImplicit false
open Set
open KellyStochasticNetworks
open KellyLossNetworks
open KellyLossNetworks.RevisedDual

lemma load_coordinate_strictMono (C : ℕ) (hC : 1 ≤ C) :
    StrictMonoOn (fun v : ℝ => -Real.log (1 - erlang v C)) (Ici 0) := by
  intro v hv w hw hvw
  have he := sn3_erlang_strict C hC hv hvw
  have hw1 := sn3_erlang_lt_one C hC hw
  exact neg_lt_neg (Real.log_lt_log (sub_pos.mpr hw1) (by linarith))

end

section
set_option autoImplicit false
open MeasureTheory Set
open KellyLossNetworks
open KellyLossNetworks.RevisedDual

lemma primitive_intervalIntegrable (u : ℝ → ℝ)
    (hu : MonotoneOn u (Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable u volume a b := by
  apply MonotoneOn.intervalIntegrable
  apply hu.mono
  intro x hx
  exact (le_min ha hb).trans hx.1

lemma primitive_strict_tangent (u : ℝ → ℝ)
    (hu : StrictMonoOn u (Ici 0)) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hne : z ≠ y) :
    u y * (z - y) < (∫ t in (0 : ℝ)..z, u t) - ∫ t in (0 : ℝ)..y, u t := by
  have h0y := primitive_intervalIntegrable u hu.monotoneOn (le_refl 0) hy
  have hyz := primitive_intervalIntegrable u hu.monotoneOn hy hz
  have hsum := intervalIntegral.integral_add_adjacent_intervals h0y hyz
  rcases lt_or_gt_of_ne hne with hzy | hyzlt
  · have hpos : 0 < ∫ t in z..y, (u y - u t) := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on
        (intervalIntegrable_const.sub hyz.symm) _ hzy
      intro t ht
      exact sub_pos.mpr (hu (le_trans hz ht.1.le) hy ht.2)
    rw [intervalIntegral.integral_sub intervalIntegrable_const hyz.symm,
      intervalIntegral.integral_const] at hpos
    have hrev := intervalIntegral.integral_symm (f := u) (μ := volume) y z
    simp only [smul_eq_mul] at hpos
    linarith
  · have hpos : 0 < ∫ t in y..z, (u t - u y) := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on
        (hyz.sub intervalIntegrable_const) _ hyzlt
      intro t ht
      exact sub_pos.mpr (hu hy (le_trans hy ht.1.le) ht.1)
    rw [intervalIntegral.integral_sub hyz intervalIntegrable_const,
      intervalIntegral.integral_const] at hpos
    simp only [smul_eq_mul] at hpos
    linarith

lemma primitive_tangent (u : ℝ → ℝ)
    (hu : StrictMonoOn u (Ici 0)) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    u y * (z - y) ≤ (∫ t in (0 : ℝ)..z, u t) - ∫ t in (0 : ℝ)..y, u t := by
  by_cases h : z = y
  · simp [h]
  · exact (primitive_strict_tangent u hu hy hz h).le

end

section
set_option autoImplicit false
open KellyLossNetworks
open KellyLossNetworks.RevisedDual
open Finset

lemma route_tangent {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (hν : ∀ r, 0 ≤ ν r) (y z : Fin J → ℝ) :
    (∑ r, ν r * Real.exp (-∑ j, y j * (A j r : ℝ))) -
      ∑ j, (z j-y j) * (∑ r, (A j r : ℝ)*ν r*Real.exp (-∑ i, y i*(A i r : ℝ))) ≤
      ∑ r, ν r * Real.exp (-∑ j, z j * (A j r : ℝ)) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin R)))
    (fun r _ => mul_le_mul_of_nonneg_left
      (exponential_tangent (-∑ j, y j*(A j r:ℝ)) (-∑ j, z j*(A j r:ℝ))) (hν r))
  have he : (∑ r, ν r * (Real.exp (-∑ j, y j*(A j r:ℝ)) +
      Real.exp (-∑ j, y j*(A j r:ℝ)) * ((-∑ j, z j*(A j r:ℝ))-(-∑ j, y j*(A j r:ℝ))))) =
      (∑ r, ν r * Real.exp (-∑ j, y j*(A j r:ℝ))) -
      ∑ j, (z j-y j) * (∑ r, (A j r:ℝ)*ν r*Real.exp (-∑ i, y i*(A i r:ℝ))) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    have hinner : (∑ j, (z j-y j)*((A j r:ℝ)*ν r*Real.exp (-∑ i, y i*(A i r:ℝ)))) =
        (∑ j, (z j-y j)*(A j r:ℝ)) * (ν r*Real.exp (-∑ i, y i*(A i r:ℝ))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hinner]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he] at h
  exact h

lemma objective_strict_of_stationary {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 ≤ ν r)
    (hu : ∀ j, StrictMonoOn (fun z => U z (C j)) (Set.Ici 0))
    (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j) (hs : StationarityConditions A ν C y)
    (z : Fin J → ℝ) (hz : ∀ j, 0 ≤ z j) (hne : z ≠ y) :
    revisedDualObjective A ν C y < revisedDualObjective A ν C z := by
  have hp : ∀ j, U (y j) (C j)*(z j-y j) ≤
      (∫ t in (0:ℝ)..z j, U t (C j)) - ∫ t in (0:ℝ)..y j, U t (C j) :=
    fun j => primitive_tangent _ (hu j) (hy j) (hz j)
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hne
  have hstrict := Finset.sum_lt_sum (s := (univ : Finset (Fin J))) (fun j _ => hp j)
    ⟨j,mem_univ j,primitive_strict_tangent _ (hu j) (hy j) (hz j) hj⟩
  have hroute := route_tangent A ν hν y z
  have he : (∑ j, (z j-y j)*(∑ r, (A j r:ℝ)*ν r*Real.exp (-∑ i,y i*(A i r:ℝ)))) =
      ∑ j, U (y j) (C j)*(z j-y j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j,mul_comm]
  rw [he] at hroute
  rw [Finset.sum_sub_distrib] at hstrict
  unfold revisedDualObjective
  linarith

end

section
set_option autoImplicit false
open KellyStochasticNetworks
open Finset

lemma sn3_carried_strict (N : ℕ) (hN : 1 ≤ N) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a * (1 - erlang a N) < b * (1 - erlang b N) := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha hab)
  rw [sn3_carried_eq N ha, sn3_carried_eq N hb,
    div_lt_div_iff₀ (by linarith [sn3_S_pos N ha]) (by linarith [sn3_S_pos N hb])]
  unfold sn3S
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_pos]
  set w : ℕ → ℝ → ℝ := fun k ν => ν ^ k / (k.factorial : ℝ) with hw
  set X : ℕ → ℕ → ℝ := fun i k => w i b * w k a - w i a * w k b with hX
  have hD1 : (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i b * w k a)
      - (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i a * w k b)
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * X i k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    simp only [hX]; ring
  have hD2 : ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * X i k
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), -((k : ℝ) * X i k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    simp only [hX]; ring
  have hterm : ∀ i k : ℕ, 0 ≤ ((i : ℝ) - k) * X i k := by
    intro i k
    simp only [hX, hw]
    have e : b ^ i / (i.factorial : ℝ) * (a ^ k / (k.factorial : ℝ))
        - a ^ i / (i.factorial : ℝ) * (b ^ k / (k.factorial : ℝ))
        = (b ^ i * a ^ k - a ^ i * b ^ k) / ((i.factorial : ℝ) * k.factorial) := by ring
    rw [e]
    rcases le_total k i with hki | hik
    · have hc : (k : ℝ) ≤ i := by exact_mod_cast hki
      apply mul_nonneg (by linarith)
      apply div_nonneg _ (by positivity)
      linarith [sn3_pow_le ha (le_of_lt hab) hki]
    · have hc : (i : ℝ) ≤ k := by exact_mod_cast hik
      apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      linarith [sn3_pow_le ha (le_of_lt hab) hik]
  have h2D : 2 * ((∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i b * w k a)
      - (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i a * w k b))
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), ((i : ℝ) - k) * X i k := by
    rw [hD1, two_mul]
    nth_rewrite 2 [hD2]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    ring
  have hpos : 0 < ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), ((i : ℝ) - k) * X i k := by
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun k _ => hterm i k))
    refine ⟨1, by simp; omega, ?_⟩
    apply Finset.sum_pos' (fun k _ => hterm 1 k)
    refine ⟨0, by simp, ?_⟩
    simp only [hX, hw]
    norm_num
    linarith
  have hconv : ∀ ν₁ ν₂ : ℝ, (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      (i : ℝ) * (ν₁ ^ i / (i.factorial : ℝ)) * (ν₂ ^ j / (j.factorial : ℝ)))
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i ν₁ * w k ν₂ := fun _ _ => rfl
  rw [hconv b a, hconv a b]
  linarith

end

section
set_option autoImplicit false
open KellyLossNetworks
open KellyLossNetworks.RevisedDual
open Finset

lemma unique_optimum_of_stationary {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 ≤ ν r)
    (hu : ∀ j, StrictMonoOn (fun z => U z (C j)) (Set.Ici 0))
    (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j) (hs : StationarityConditions A ν C y) :
    IsRevisedDualOptimum A ν C y ∧
      ∀ z, IsRevisedDualOptimum A ν C z → z = y := by
  constructor
  · refine ⟨hy,fun z hz => ?_⟩
    by_cases he : z = y
    · rw [he]
    · exact (objective_strict_of_stationary A ν C hν hu y hy hs z hz he).le
  · intro z hz
    by_contra he
    exact (not_lt_of_ge (hz.2 y hy))
      (objective_strict_of_stationary A ν C hν hu y hy hs z hz.1 he)

end

section
set_option autoImplicit false
open Set
open KellyStochasticNetworks
open KellyLossNetworks
open KellyLossNetworks.RevisedDual

lemma utilization_strictMono (C : ℕ) (hC : 1 ≤ C) :
    StrictMonoOn (fun y : ℝ => U y C) (Ici 0) := by
  intro y hy z hz hyz
  change U y C < U z C
  obtain ⟨v, hv, hvy⟩ := exists_load_coordinate C hC hy
  obtain ⟨w, hw, hwz⟩ := exists_load_coordinate C hC hz
  have hvw : v < w := by
    by_contra h
    have hle := (load_coordinate_strictMono C hC).monotoneOn hw hv (le_of_not_gt h)
    rw [hvy, hwz] at hle
    exact (not_le_of_gt hyz) hle
  rw [← hvy, ← hwz, utilization_coordinate C hC hv, utilization_coordinate C hC hw]
  exact sn3_carried_strict C hC hv hvw

end

section
set_option autoImplicit false
open KellyLossNetworks
open KellyLossNetworks.RevisedDual

theorem theorem_3_7 {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃ y : Fin J → ℝ, IsRevisedDualOptimum A ν C y ∧
      (∀ y' : Fin J → ℝ, IsRevisedDualOptimum A ν C y' → y' = y) ∧
      ∀ E : Fin J → ℝ,
        ((∀ j, E j ∈ Set.Icc (0 : ℝ) 1) ∧ KellyStochasticNetworks.ErlangFixedPoint A ν C E) ↔
          E = fun j => 1 - Real.exp (-y j) := by
  obtain ⟨E,hE,huniq⟩ := KellyStochasticNetworks.erlang_fixed_point_unique A ν C hν hC
  obtain ⟨hy,hstat,hcoord⟩ := fixedpoint_coordinates A ν C hν hC E hE.1 hE.2
  obtain ⟨hopt,hoptuniq⟩ := unique_optimum_of_stationary A ν C (fun r => (hν r).le)
    (fun j => utilization_strictMono (C j) (hC j)) _ hy hstat
  refine ⟨(fun j => -Real.log (1-E j)),hopt,hoptuniq,?_⟩
  intro E'
  constructor
  · intro hE'
    exact (huniq E' hE').trans hcoord
  · intro he
    have heq : E' = E := he.trans hcoord.symm
    rw [heq]
    exact hE

end

section
set_option autoImplicit false
open KellyLossNetworks.RevisedDual

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃ y : Fin J → ℝ, IsRevisedDualOptimum A ν C y ∧
      (∀ y' : Fin J → ℝ, IsRevisedDualOptimum A ν C y' → y' = y) ∧
      ∀ E : Fin J → ℝ,
        ((∀ j, E j ∈ Set.Icc (0 : ℝ) 1) ∧ KellyStochasticNetworks.ErlangFixedPoint A ν C E) ↔
          E = fun j => 1 - Real.exp (-y j) := by
  exact theorem_3_7 A ν C hν hC

end
