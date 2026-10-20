-- Prove2me | solution 1 for OAI.SingleFold.PowerSystem.pinned
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:41:14.578096+00:00
-- url     : https://prove2.me/submissions/c28fd719-8e4a-435e-900f-128bf9fd8d83

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Theorems.Thm_OAI_SingleFold_PowerEstimate_input_bounds
import Theorems.Thm_OAI_SingleFold_PellPower_power_bounds
import Theorems.Thm_OAI_SingleFold_PowerEstimate_growth_nat

open OAI OAI.SingleFold OAI.SingleFold.PowerSystem
open PowerEstimate
variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg
omit hδ hell h₀ hg in
theorem h49_pin {a N k : ℕ} (ha : 1 < a) {X Y : ℕ} (hp : X^2 + Y^2 = 1 + a^2 * Y^2)
    (hm : ∀ m, Pell.yn ha m = Y → m ≤ a - 1) (hY : Y = N + (a-1)*k) (hN : N < a - 1) (hN1 : 1 ≤ N) :
    X = Pell.xn ha N ∧ Y = Pell.yn ha N := by
  have ha2 : 1 ≤ a * a := by nlinarith
  have hpe : X * X - (a*a-1) * Y * Y = 1 := by
    have : X * X = 1 + (a*a-1) * Y * Y := by
      zify [ha2]; push_cast; zify at hp; linear_combination hp
    omega
  obtain ⟨m, hx, hy⟩ := Pell.eq_pell ha hpe
  have hm' := hm m hy.symm
  have h1 : Pell.yn ha m ≡ m [MOD a - 1] := Pell.yn_modEq_a_sub_one ha m
  have h2 : Y ≡ N [MOD a - 1] := by
    rw [hY]; exact (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2 ⟨k, by omega⟩ |>.symm
  have h3 : m ≡ N [MOD a - 1] := h1.symm.trans (hy ▸ h2)
  have hm'' : m < a - 1 := by
    rcases Nat.lt_or_ge m (a-1) with h | h
    · exact h
    · have hma : m = a - 1 := le_antisymm hm' h
      rw [hma] at h3
      have h4 : (a - 1) % (a - 1) = N % (a - 1) := h3
      rw [Nat.mod_self, Nat.mod_eq_of_lt hN] at h4
      omega
  have := Nat.ModEq.eq_of_lt_of_lt h3 hm'' hN
  subst this
  exact ⟨hx, hy⟩

omit hδ hell h₀ hg in
theorem h49_seven_fourths (k : ℕ) (hk : 3 ≤ k) : (k:ℝ) + 1 ≤ (7/4:ℝ)^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : (3:ℝ) ≤ k := by exact_mod_cast hk
    rw [pow_succ]; push_cast; nlinarith

omit hδ hell h₀ hg in
theorem h49_big (u : ℕ) (hu : 4 ≤ u) : u^u ≤ (2*u-1)^(u-1) := by
  have hu' : (4:ℝ) ≤ u := by exact_mod_cast hu
  have h1 : ((u:ℝ)-1) + 1 ≤ (7/4:ℝ)^(u-1) := by
    have := h49_seven_fourths (u-1) (by omega)
    push_cast [Nat.cast_sub (by omega : 1 ≤ u)] at this; linarith
  have h2 : (7/4:ℝ) * u ≤ ((2*u-1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2*u)]; linarith
  have key : ((u^u : ℕ) : ℝ) ≤ (((2*u-1)^(u-1) : ℕ) : ℝ) := by
    push_cast
    have e : (u:ℝ)^u = u * (u:ℝ)^(u-1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]
    calc (u:ℝ) * (u:ℝ)^(u-1) ≤ (7/4:ℝ)^(u-1) * (u:ℝ)^(u-1) := by
          gcongr; linarith
      _ = ((7/4:ℝ) * u)^(u-1) := by rw [mul_pow]
      _ ≤ ((2*u-1 : ℕ) : ℝ)^(u-1) := by gcongr
  exact_mod_cast key

theorem solution {b n c : ℕ} {w : Fin 9 → ℕ} (hw : System g ell u₀ b n c w) :
    w 2=px (b*w 0) (n+1) ∧ w 3=py (b*w 0) (n+1) ∧
    w 4=px (w 0) (n+1) ∧ w 5=py (w 0) (n+1) := by
  obtain ⟨hb, h0, h1, hp1, hp2, h3pos, h3lt, h5pos, h5lt, hl1, hl2, hq, hr⟩ := hw
  obtain ⟨hu0, hu1, hu2, hu3⟩ := PowerEstimate.input_bounds (ell := ell) (u₀ := u₀) (b := b) (n := n)
    (c := c) hell h₀
  rw [← h0] at hu0 hu1 hu2 hu3
  set u := w 0 with hu
  have hu4 : 4 ≤ u := by omega
  have hgu := PowerEstimate.growth_nat hδ hu4 (hg u hu0)
  rw [← h1] at hgu
  have hbu : 1 < b * u := by nlinarith
  have hu1' : 1 < u := by omega
  -- first pair
  have hA := h49_pin hbu (N := n+1) (k := w 6) (X := w 2) (Y := w 3) hp1 ?_ hl1 (by
    have : u ≤ b * u := Nat.le_mul_of_pos_left _ (by omega); omega) (by omega)
  have hB := h49_pin hu1' (N := n+1) (k := w 7) (X := w 4) (Y := w 5) hp2 ?_ hl2 (by omega) (by omega)
  · unfold px py
    rw [dif_pos hbu, dif_pos hbu, dif_pos hu1', dif_pos hu1']
    exact ⟨hA.1, hA.2, hB.1, hB.2⟩
  · intro m hm
    by_contra hcon
    push_neg at hcon
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hpb := (PellPower.power_bounds hu1' j).1
    have hge1 : u^u ≤ (2*u-1)^(u-1) := h49_big u hu4
    have hge2 : (2*u-1)^(u-1) ≤ (2*u-1)^j := Nat.pow_le_pow_right (by omega) (by omega)
    have hlt := hgu.2
    rw [hm] at hpb
    omega
  · -- m bound for (b u)
    intro m hm
    have hub : u ≤ b * u := Nat.le_mul_of_pos_left _ (by omega)
    have hmu : m ≤ u := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have hpb := (PellPower.power_bounds hbu j).1
      have hbase : u ≤ 2*(b*u)-1 := by omega
      have hge1 : u^u ≤ (2*(b*u)-1)^u := Nat.pow_le_pow_left hbase _
      have hge2 : (2*(b*u)-1)^u ≤ (2*(b*u)-1)^j := Nat.pow_le_pow_right (by omega) (by omega)
      have hlt := hgu.2
      rw [hm] at hpb
      omega
    have : u < b * u - 1 := by
      have : 2 * u ≤ b * u := Nat.mul_le_mul_right _ hb
      omega
    omega

