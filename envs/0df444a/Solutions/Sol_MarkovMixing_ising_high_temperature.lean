-- Prove2me | solution 1 for MarkovMixing.ising_high_temperature
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T01:52:57.788521+00:00
-- url     : https://prove2.me/submissions/bb7a419d-e0d9-4214-a1d4-eed95546db02

import Definitions.Def_mm_ising
import Definitions.Def_mm_coupling
import Theorems.Thm_MarkovMixing_coupling_bound
import Theorems.Thm_MarkovMixing_glauber_stationary
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Fast mixing of the Ising Glauber dynamics at high temperature (LPW Theorem 15.1)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

section Tanh

private lemma tanh_sub_eq (x y : ℝ) :
    Real.tanh x - Real.tanh y = Real.sinh (x - y) / (Real.cosh x * Real.cosh y) := by
  have hx : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hy : Real.cosh y ≠ 0 := ne_of_gt (Real.cosh_pos y)
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub]
  field_simp
  try ring

private lemma cosh_mul_cosh (x y : ℝ) :
    Real.cosh x * Real.cosh y = (Real.cosh (x + y) + Real.cosh (x - y)) / 2 := by
  rw [Real.cosh_add, Real.cosh_sub]
  ring

private lemma tanh_mono {x y : ℝ} (h : y ≤ x) : Real.tanh y ≤ Real.tanh x := by
  have h1 : 0 ≤ Real.sinh (x - y) := by
    rw [← Real.sinh_zero]
    exact Real.sinh_le_sinh.mpr (by linarith)
  have h2 : 0 < Real.cosh x * Real.cosh y := mul_pos (Real.cosh_pos x) (Real.cosh_pos y)
  have := tanh_sub_eq x y
  have h3 : 0 ≤ Real.tanh x - Real.tanh y := by
    rw [this]
    positivity
  linarith

/-- A one-step bound on `tanh` differences from a lower bound on `cosh x · cosh y`. -/
private lemma tanh_step_of_cosh_bound {β x y M : ℝ} (hβ : 0 < β) (hxy : x - y = 2 * β)
    (hM0 : 0 < M) (hM : M ≤ Real.cosh x * Real.cosh y) :
    Real.tanh x - Real.tanh y ≤ Real.sinh (2 * β) / M := by
  have hs : 0 < Real.sinh (2 * β) := by
    rw [← Real.sinh_zero]
    exact Real.sinh_lt_sinh.mpr (by linarith)
  rw [tanh_sub_eq, hxy]
  exact div_le_div_of_nonneg_left hs.le hM0 hM

/-- The generic one-step bound: `tanh(β(c+2)) − tanh(βc) ≤ 2 tanh β`. -/
private lemma tanh_step_gen {β : ℝ} (hβ : 0 < β) (c : ℝ) :
    Real.tanh (β * (c + 2)) - Real.tanh (β * c) ≤ 2 * Real.tanh β := by
  have hM : (1 + Real.cosh (2 * β)) / 2 ≤ Real.cosh (β * (c + 2)) * Real.cosh (β * c) := by
    rw [cosh_mul_cosh]
    have h1 : (1 : ℝ) ≤ Real.cosh (β * (c + 2) + β * c) := Real.one_le_cosh _
    have h2 : β * (c + 2) - β * c = 2 * β := by ring
    rw [h2]
    linarith
  have hstep := tanh_step_of_cosh_bound (β := β) (x := β * (c + 2)) (y := β * c)
    hβ (by ring) (by positivity) hM
  refine hstep.trans (le_of_eq ?_)
  have hc : Real.cosh (2 * β) = 2 * Real.cosh β ^ 2 - 1 := by
    rw [Real.cosh_two_mul, Real.sinh_sq]; ring
  have hs : Real.sinh (2 * β) = 2 * Real.sinh β * Real.cosh β := Real.sinh_two_mul β
  rw [hc, hs, Real.tanh_eq_sinh_div_cosh]
  have hcb : Real.cosh β ≠ 0 := ne_of_gt (Real.cosh_pos β)
  field_simp
  ring

/-- The even one-step bound: for `|c + 1| ≥ 1`,
`tanh(β(c+2)) − tanh(βc) ≤ tanh(2β)`. -/
private lemma tanh_step_far {β : ℝ} (hβ : 0 < β) (c : ℝ) (hc : 1 ≤ |c + 1|) :
    Real.tanh (β * (c + 2)) - Real.tanh (β * c) ≤ Real.tanh (2 * β) := by
  have hM : Real.cosh (2 * β) ≤ Real.cosh (β * (c + 2)) * Real.cosh (β * c) := by
    rw [cosh_mul_cosh]
    have h2 : β * (c + 2) - β * c = 2 * β := by ring
    have h3 : β * (c + 2) + β * c = 2 * β * (c + 1) := by ring
    rw [h2, h3]
    have h4 : Real.cosh (2 * β) ≤ Real.cosh (2 * β * (c + 1)) := by
      refine Real.cosh_le_cosh.mpr ?_
      rw [abs_of_pos (by linarith : (0:ℝ) < 2 * β), abs_mul,
        abs_of_pos (by linarith : (0:ℝ) < 2 * β)]
      nlinarith [hc]
    linarith
  have hstep := tanh_step_of_cosh_bound (β := β) (x := β * (c + 2)) (y := β * c)
    hβ (by ring) (Real.cosh_pos _) hM
  refine hstep.trans (le_of_eq ?_)
  rw [Real.tanh_eq_sinh_div_cosh]

private lemma tanh_telescope {β : ℝ} (K : ℝ) (Q : ℤ → Prop)
    (hQ : ∀ c : ℤ, Q c → Q (c + 2))
    (hstep : ∀ c : ℤ, Q c → Real.tanh (β * ((c : ℝ) + 2)) - Real.tanh (β * (c : ℝ)) ≤ K) :
    ∀ (m : ℕ) (b : ℤ), Q b →
      Real.tanh (β * ((b : ℝ) + 2 * (m : ℝ))) - Real.tanh (β * (b : ℝ)) ≤ (m : ℝ) * K := by
  intro m
  induction m with
  | zero => intro b _; simp
  | succ m ih =>
    intro b hb
    have h1 := hstep b hb
    have h2 := ih (b + 2) (hQ b hb)
    push_cast at h1 h2 ⊢
    have hre : (b : ℝ) + 2 + 2 * (m : ℝ) = (b : ℝ) + 2 * ((m : ℝ) + 1) := by ring
    rw [hre] at h2
    linarith

private lemma tanh_abs_diff {β : ℝ} (hβ : 0 < β) (K : ℝ) (hK : 0 ≤ K) (Q : ℤ → Prop)
    (hQ : ∀ c : ℤ, Q c → Q (c + 2))
    (hstep : ∀ c : ℤ, Q c → Real.tanh (β * ((c : ℝ) + 2)) - Real.tanh (β * (c : ℝ)) ≤ K)
    (a b : ℤ) (hb : Q b) (ha : Q a) (k : ℕ) (j : ℤ) (hj : a - b = 2 * j)
    (hjk : j.natAbs ≤ k) :
    |Real.tanh (β * (a : ℝ)) - Real.tanh (β * (b : ℝ))| ≤ (k : ℝ) * K := by
  have hkK : ∀ m : ℕ, m ≤ k → (m : ℝ) * K ≤ (k : ℝ) * K := by
    intro m hm
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hK
  rcases (by omega : 0 ≤ j ∨ j < 0) with hj0 | hj0
  · have hjn : (j.natAbs : ℤ) = j := Int.natAbs_of_nonneg hj0
    have hjr : ((j.natAbs : ℕ) : ℝ) = (j : ℝ) := by
      have h' : ((j.natAbs : ℤ) : ℝ) = (j : ℝ) := by exact_mod_cast hjn
      simpa using h'
    have hae : (a : ℝ) = (b : ℝ) + 2 * (j.natAbs : ℝ) := by
      rw [hjr]
      have h2 : a = b + 2 * j := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2
    have hmain := tanh_telescope K Q hQ hstep j.natAbs b hb
    rw [← hae] at hmain
    have hrev : Real.tanh (β * (b : ℝ)) ≤ Real.tanh (β * (a : ℝ)) := by
      refine tanh_mono ?_
      have : (b : ℝ) ≤ (a : ℝ) := by
        have : b ≤ a := by omega
        exact_mod_cast this
      nlinarith
    rw [abs_le]
    constructor
    · linarith [hkK j.natAbs hjk, mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hK]
    · exact le_trans hmain (hkK j.natAbs hjk)
  · have hjn : ((-j).natAbs : ℤ) = -j := Int.natAbs_of_nonneg (by omega)
    have hjr : (((-j).natAbs : ℕ) : ℝ) = ((-j : ℤ) : ℝ) := by
      have h' : (((-j).natAbs : ℤ) : ℝ) = ((-j : ℤ) : ℝ) := by exact_mod_cast hjn
      simpa using h'
    have hbe : (b : ℝ) = (a : ℝ) + 2 * ((-j).natAbs : ℝ) := by
      rw [hjr]
      have h2 : b = a + 2 * (-j) := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h2
    have hmain := tanh_telescope K Q hQ hstep (-j).natAbs a ha
    rw [← hbe] at hmain
    have hrev : Real.tanh (β * (a : ℝ)) ≤ Real.tanh (β * (b : ℝ)) := by
      refine tanh_mono ?_
      have : (a : ℝ) ≤ (b : ℝ) := by
        have : a ≤ b := by omega
        exact_mod_cast this
      nlinarith
    have hnk : (-j).natAbs ≤ k := by
      rw [Int.natAbs_neg]; exact hjk
    rw [abs_le]
    constructor
    · linarith [hmain, hkK (-j).natAbs hnk]
    · linarith [hkK (-j).natAbs hnk, mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hK]

end Tanh

section Ising

variable {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
variable (G : SimpleGraph Vv) [DecidableRel G.Adj] (β : ℝ)

/-- The set of sites where two configurations disagree. -/
private def diffSet (σ τ : Vv → Bool) : Finset Vv :=
  univ.filter fun v => σ v ≠ τ v

private lemma mem_diffSet (σ τ : Vv → Bool) (v : Vv) : v ∈ diffSet σ τ ↔ σ v ≠ τ v := by
  simp [diffSet]

/-- The integer spin `±1`. -/
private def sgnZ (b : Bool) : ℤ := if b then 1 else -1

private lemma spin_eq (σ : Vv → Bool) (v : Vv) : spin σ v = ((sgnZ (σ v) : ℤ) : ℝ) := by
  cases h : σ v <;> simp [spin, sgnZ, h]

/-- The integer local field `∑_{w ~ v} σ(w)`. -/
private def Sz (σ : Vv → Bool) (v : Vv) : ℤ :=
  ∑ w, if G.Adj v w then sgnZ (σ w) else 0

private lemma Sz_real (σ : Vv → Bool) (v : Vv) :
    ((Sz G σ v : ℤ) : ℝ) = ∑ w, if G.Adj v w then spin σ w else 0 := by
  simp only [Sz, Int.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos h, spin_eq]
  · rw [if_neg h, if_neg h, Int.cast_zero]

private lemma Sz_sub_degree_even (σ : Vv → Bool) (v : Vv) :
    (2 : ℤ) ∣ Sz G σ v - (G.degree v : ℤ) := by
  have hdeg : ((G.degree v : ℕ) : ℤ) = ∑ w : Vv, if G.Adj v w then (1 : ℤ) else 0 := by
    rw [← Finset.sum_filter]
    have : (univ.filter fun w : Vv => G.Adj v w) = G.neighborFinset v := by
      ext w; simp [SimpleGraph.mem_neighborFinset]
    rw [this, Finset.sum_const, SimpleGraph.degree, nsmul_eq_mul, mul_one]
  rw [hdeg, Sz, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun w _ => ?_
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos h]
    cases hw : σ w <;> simp [sgnZ, hw]
  · rw [if_neg h, if_neg h]; simp

private lemma Sz_diff_dvd (σ τ : Vv → Bool) (v : Vv) : (2 : ℤ) ∣ (Sz G σ v - Sz G τ v) := by
  have h1 := Sz_sub_degree_even G σ v
  have h2 := Sz_sub_degree_even G τ v
  omega

private lemma Sz_diff_bound (σ τ : Vv → Bool) (v : Vv) :
    |Sz G σ v - Sz G τ v| ≤ 2 * ((G.neighborFinset v ∩ diffSet σ τ).card : ℤ) := by
  classical
  have hsub : Sz G σ v - Sz G τ v
      = ∑ w : Vv, (if G.Adj v w then sgnZ (σ w) - sgnZ (τ w) else 0) := by
    rw [Sz, Sz, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : G.Adj v w <;> simp [h]
  rw [hsub]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ w : Vv, |if G.Adj v w then sgnZ (σ w) - sgnZ (τ w) else 0|
      ≤ 2 * (if w ∈ G.neighborFinset v ∩ diffSet σ τ then (1 : ℤ) else 0) := by
    intro w
    by_cases h : G.Adj v w
    · rw [if_pos h]
      by_cases h2 : σ w = τ w
      · rw [h2, sub_self]
        simp only [abs_zero]
        split_ifs <;> norm_num
      · have : w ∈ G.neighborFinset v ∩ diffSet σ τ := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_diffSet]
          exact ⟨h, h2⟩
        rw [if_pos this]
        cases hs : σ w <;> cases ht : τ w <;> simp [sgnZ, hs, ht] <;> omega
    · rw [if_neg h]
      simp
      positivity
  refine le_trans (Finset.sum_le_sum fun w _ => hterm w) ?_
  rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    mul_one]

/-- The part of the energy not involving the site `v`. -/
private def offPart (σ : Vv → Bool) (v : Vv) : ℝ :=
  ∑ u ∈ univ.erase v, ∑ w ∈ univ.erase v, if G.Adj u w then spin σ u * spin σ w else 0

private lemma spin_update_ne (σ : Vv → Bool) (v : Vv) (s : Bool) {u : Vv} (h : u ≠ v) :
    spin (Function.update σ v s) u = spin σ u := by
  simp [spin, Function.update_apply, h]

private lemma spin_update_self (σ : Vv → Bool) (v : Vv) (s : Bool) :
    spin (Function.update σ v s) v = ((sgnZ s : ℤ) : ℝ) := by
  cases s <;> simp [spin, sgnZ]

private lemma offPart_update (σ : Vv → Bool) (v : Vv) (s : Bool) :
    offPart G (Function.update σ v s) v = offPart G σ v := by
  simp only [offPart]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun w hw => ?_
  rw [spin_update_ne σ v s (Finset.ne_of_mem_erase hu),
    spin_update_ne σ v s (Finset.ne_of_mem_erase hw)]

private lemma energy_update (σ : Vv → Bool) (v : Vv) (s : Bool) :
    (∑ u : Vv, ∑ w : Vv, if G.Adj u w then
        spin (Function.update σ v s) u * spin (Function.update σ v s) w else 0)
      = 2 * ((sgnZ s : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ) + offPart G σ v := by
  classical
  set σ' := Function.update σ v s with hσ'
  set c : ℝ := ((sgnZ s : ℤ) : ℝ) with hc
  have hrow : ∀ u : Vv, u ≠ v →
      (∑ w : Vv, if G.Adj u w then spin σ' u * spin σ' w else 0)
        = (if G.Adj u v then spin σ u * c else 0)
          + ∑ w ∈ univ.erase v, (if G.Adj u w then spin σ u * spin σ w else 0) := by
    intro u hu
    rw [← Finset.add_sum_erase _
      (fun w => if G.Adj u w then spin σ' u * spin σ' w else 0) (Finset.mem_univ v)]
    congr 1
    · by_cases h : G.Adj u v
      · rw [if_pos h, if_pos h, spin_update_ne σ v s hu, hσ', spin_update_self]
      · rw [if_neg h, if_neg h]
    · refine Finset.sum_congr rfl fun w hw => ?_
      rw [spin_update_ne σ v s hu, spin_update_ne σ v s (Finset.ne_of_mem_erase hw)]
  have hv : (∑ w : Vv, if G.Adj v w then spin σ' v * spin σ' w else 0)
      = c * ((Sz G σ v : ℤ) : ℝ) := by
    rw [Sz_real, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases h : G.Adj v w
    · have hwv : w ≠ v := fun hh => G.irrefl (hh ▸ h)
      rw [if_pos h, if_pos h, hσ', spin_update_self, spin_update_ne σ v s hwv]
    · rw [if_neg h, if_neg h, mul_zero]
  have hcol : (∑ u ∈ univ.erase v, if G.Adj u v then spin σ u * c else 0)
      = c * ((Sz G σ v : ℤ) : ℝ) := by
    rw [Sz_real, Finset.mul_sum]
    rw [← Finset.add_sum_erase _ (fun u => c * if G.Adj v u then spin σ u else 0)
      (Finset.mem_univ v)]
    have hvv : ¬ G.Adj v v := G.irrefl
    rw [if_neg hvv, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : G.Adj u v
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (fun hh => h hh.symm), mul_zero]
  rw [← Finset.add_sum_erase _
    (fun u => ∑ w : Vv, if G.Adj u w then spin σ' u * spin σ' w else 0) (Finset.mem_univ v)]
  rw [hv, Finset.sum_congr rfl (fun u hu => hrow u (Finset.ne_of_mem_erase hu)),
    Finset.sum_add_distrib, hcol]
  simp only [offPart]
  ring

private lemma weight_update (σ : Vv → Bool) (v : Vv) (s : Bool) :
    isingWeight G β (Function.update σ v s)
      = Real.exp (β * ((sgnZ s : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ))
        * Real.exp (β * 2⁻¹ * offPart G σ v) := by
  rw [isingWeight, energy_update, ← Real.exp_add]
  congr 1
  ring

/-- The conditional probability of the spin `+1` at `v` given the rest. -/
private def pT (σ : Vv → Bool) (v : Vv) : ℝ :=
  (1 + Real.tanh (β * ((Sz G σ v : ℤ) : ℝ))) / 2

/-- The conditional distribution of the spin at `v` given the rest. -/
private def pB (σ : Vv → Bool) (v : Vv) (s : Bool) : ℝ :=
  if s then pT G β σ v else 1 - pT G β σ v

private lemma tanh_lt_one' (x : ℝ) : |Real.tanh x| < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (Real.cosh_pos x),
    div_lt_one (Real.cosh_pos x)]
  have h := Real.cosh_sq x
  have h2 : Real.sinh x ^ 2 < Real.cosh x ^ 2 := by nlinarith [Real.cosh_pos x]
  nlinarith [abs_nonneg (Real.sinh x), sq_abs (Real.sinh x), Real.cosh_pos x]

private lemma pB_nonneg (σ : Vv → Bool) (v : Vv) (s : Bool) : 0 ≤ pB G β σ v s := by
  have h := abs_lt.mp (tanh_lt_one' (β * ((Sz G σ v : ℤ) : ℝ)))
  cases s <;> simp only [pB, pT, if_true, if_false, Bool.false_eq_true] <;> linarith [h.1, h.2]

private lemma pB_add (σ : Vv → Bool) (v : Vv) :
    pB G β σ v true + pB G β σ v false = 1 := by
  simp only [pB]
  norm_num

private lemma exp_ratio (x : ℝ) :
    Real.exp x / (Real.exp x + Real.exp (-x)) = (1 + Real.tanh x) / 2 := by
  have h : (0 : ℝ) < Real.exp x + Real.exp (-x) := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h2 : (Real.exp x + Real.exp (-x)) / 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma exp_ratio' (x : ℝ) :
    Real.exp (-x) / (Real.exp x + Real.exp (-x)) = 1 - (1 + Real.tanh x) / 2 := by
  have h : (0 : ℝ) < Real.exp x + Real.exp (-x) := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h2 : (Real.exp x + Real.exp (-x)) / 2 ≠ 0 := by positivity
  field_simp
  ring

private lemma pB_eq_exp (σ : Vv → Bool) (v : Vv) (s : Bool) :
    pB G β σ v s
      = Real.exp (β * ((sgnZ s : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ))
        / (Real.exp (β * ((Sz G σ v : ℤ) : ℝ)) + Real.exp (-(β * ((Sz G σ v : ℤ) : ℝ)))) := by
  cases s
  · rw [show β * ((sgnZ false : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ)
        = -(β * ((Sz G σ v : ℤ) : ℝ)) from by simp [sgnZ], exp_ratio']
    rfl
  · rw [show β * ((sgnZ true : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ)
        = β * ((Sz G σ v : ℤ) : ℝ) from by simp [sgnZ], exp_ratio]
    rfl

private lemma isingWeight_pos (σ : Vv → Bool) : 0 < isingWeight G β σ := Real.exp_pos _

private lemma agree_iff (σ z : Vv → Bool) (v : Vv) :
    (∀ w : Vv, w ≠ v → z w = σ w) ↔ z = Function.update σ v (z v) := by
  constructor
  · intro h
    funext w
    by_cases hw : w = v
    · subst hw; simp
    · rw [Function.update_apply, if_neg hw]
      exact h w hw
  · intro h w hw
    rw [h, Function.update_apply, if_neg hw]

private lemma update_ne (σ : Vv → Bool) (v : Vv) :
    Function.update σ v true ≠ Function.update σ v false := by
  intro h
  have := congrFun h v
  simp at this

private lemma filter_pair (σ : Vv → Bool) (v : Vv) :
    (univ.filter fun z : Vv → Bool => ∀ w : Vv, w ≠ v → z w = σ w)
      = {Function.update σ v true, Function.update σ v false} := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  rw [agree_iff]
  constructor
  · intro h
    cases hz : z v
    · right; rw [h, hz]
    · left; rw [h, hz]
  · rintro (h | h) <;> rw [h] <;> simp

private lemma cond_ratio (σ τ : Vv → Bool) (v : Vv) (h : ∀ w : Vv, w ≠ v → τ w = σ w) :
    isingWeight G β τ /
        (isingWeight G β (Function.update σ v true)
          + isingWeight G β (Function.update σ v false))
      = pB G β σ v (τ v) := by
  have hτ : τ = Function.update σ v (τ v) := (agree_iff σ τ v).mp h
  have h1 : isingWeight G β τ
      = Real.exp (β * ((sgnZ (τ v) : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ))
        * Real.exp (β * 2⁻¹ * offPart G σ v) := by
    conv_lhs => rw [hτ]
    exact weight_update G β σ v (τ v)
  have h2 : isingWeight G β (Function.update σ v true)
      = Real.exp (β * ((Sz G σ v : ℤ) : ℝ)) * Real.exp (β * 2⁻¹ * offPart G σ v) := by
    rw [weight_update, show β * ((sgnZ true : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ)
      = β * ((Sz G σ v : ℤ) : ℝ) from by simp [sgnZ]]
  have h3 : isingWeight G β (Function.update σ v false)
      = Real.exp (-(β * ((Sz G σ v : ℤ) : ℝ))) * Real.exp (β * 2⁻¹ * offPart G σ v) := by
    rw [weight_update, show β * ((sgnZ false : ℤ) : ℝ) * ((Sz G σ v : ℤ) : ℝ)
      = -(β * ((Sz G σ v : ℤ) : ℝ)) from by simp [sgnZ]]
  rw [h1, h2, h3, pB_eq_exp]
  have hE : (0 : ℝ) < Real.exp (β * 2⁻¹ * offPart G σ v) := Real.exp_pos _
  have hd : (0 : ℝ) < Real.exp (β * ((Sz G σ v : ℤ) : ℝ))
      + Real.exp (-(β * ((Sz G σ v : ℤ) : ℝ))) := by positivity
  field_simp
  try ring

private lemma glauber_apply [Nonempty Vv] (σ τ : Vv → Bool) :
    glauber (isingDist G β) σ τ
      = (Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv,
          (if ∀ w : Vv, w ≠ v → τ w = σ w then pB G β σ v (τ v) else 0) := by
  classical
  have hZ : (0 : ℝ) < ∑ η : Vv → Bool, isingWeight G β η := by
    refine Finset.sum_pos (fun η _ => Real.exp_pos _) ?_
    exact ⟨fun _ => true, Finset.mem_univ _⟩
  rw [glauber]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : ∀ w : Vv, w ≠ v → τ w = σ w
  · rw [if_pos h, if_pos h, filter_pair, Finset.sum_pair (update_ne σ v)]
    have key := cond_ratio G β σ τ v h
    have hZne : (∑ η : Vv → Bool, isingWeight G β η) ≠ 0 := ne_of_gt hZ
    have hab : isingWeight G β (Function.update σ v true)
        + isingWeight G β (Function.update σ v false) ≠ 0 :=
      ne_of_gt (add_pos (isingWeight_pos G β _) (isingWeight_pos G β _))
    simp only [isingDist]
    rw [← key]
    field_simp
  · rw [if_neg h, if_neg h]

/-! ### The optimal coupling of two Bernoulli laws -/

private def bval (p : ℝ) (s : Bool) : ℝ := if s then p else 1 - p

private lemma bval_add (p : ℝ) : bval p true + bval p false = 1 := by simp [bval]

private def Jab (p q : ℝ) (s s' : Bool) : ℝ :=
  if s = s' then min (bval p s) (bval q s) else bval p s - min (bval p s) (bval q s)

private lemma Jab_nonneg {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (s s' : Bool) : 0 ≤ Jab p q s s' := by
  have hb : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ∀ t : Bool, 0 ≤ bval r t := by
    intro r h0 h1 t
    cases t <;> simp only [bval, if_true, if_false, Bool.false_eq_true] <;> linarith
  simp only [Jab]
  split_ifs with h
  · exact le_min (hb p hp0 hp1 s) (hb q hq0 hq1 s)
  · exact sub_nonneg.mpr (min_le_left _ _)

private lemma Jab_row (p q : ℝ) (s : Bool) :
    Jab p q s true + Jab p q s false = bval p s := by
  cases s
  · show (bval p false - min (bval p false) (bval q false))
        + min (bval p false) (bval q false) = bval p false
    ring
  · show min (bval p true) (bval q true)
        + (bval p true - min (bval p true) (bval q true)) = bval p true
    ring

private lemma Jab_col (p q : ℝ) (s' : Bool) :
    Jab p q true s' + Jab p q false s' = bval q s' := by
  rcases le_total p q with h | h
  · have hm1 : min p q = p := min_eq_left h
    have hm2 : min (1 - p) (1 - q) = 1 - q := min_eq_right (by linarith)
    cases s'
    · show (bval p true - min (bval p true) (bval q true))
          + min (bval p false) (bval q false) = bval q false
      simp only [bval, if_true, if_false, Bool.false_eq_true]
      rw [hm1, hm2]
      ring
    · show min (bval p true) (bval q true)
          + (bval p false - min (bval p false) (bval q false)) = bval q true
      simp only [bval, if_true, if_false, Bool.false_eq_true]
      rw [hm1, hm2]
      ring
  · have hm1 : min p q = q := min_eq_right h
    have hm2 : min (1 - p) (1 - q) = 1 - p := min_eq_left (by linarith)
    cases s'
    · show (bval p true - min (bval p true) (bval q true))
          + min (bval p false) (bval q false) = bval q false
      simp only [bval, if_true, if_false, Bool.false_eq_true]
      rw [hm1, hm2]
      ring
    · show min (bval p true) (bval q true)
          + (bval p false - min (bval p false) (bval q false)) = bval q true
      simp only [bval, if_true, if_false, Bool.false_eq_true]
      rw [hm1, hm2]
      ring

private lemma Jab_off (p q : ℝ) :
    Jab p q true false + Jab p q false true = |p - q| := by
  rcases le_total p q with h | h
  · have hm1 : min p q = p := min_eq_left h
    have hm2 : min (1 - p) (1 - q) = 1 - q := min_eq_right (by linarith)
    show (bval p true - min (bval p true) (bval q true))
        + (bval p false - min (bval p false) (bval q false)) = |p - q|
    simp only [bval, if_true, if_false, Bool.false_eq_true]
    rw [hm1, hm2, abs_of_nonpos (by linarith)]
    ring
  · have hm1 : min p q = q := min_eq_right h
    have hm2 : min (1 - p) (1 - q) = 1 - p := min_eq_left (by linarith)
    show (bval p true - min (bval p true) (bval q true))
        + (bval p false - min (bval p false) (bval q false)) = |p - q|
    simp only [bval, if_true, if_false, Bool.false_eq_true]
    rw [hm1, hm2, abs_of_nonneg (by linarith)]
    ring

private lemma Jab_diag (p : ℝ) {s s' : Bool} (h : s ≠ s') : Jab p p s s' = 0 := by
  simp only [Jab, if_neg h, min_self, sub_self]

private lemma Jab_total (p q : ℝ) : ∑ s : Bool, ∑ s' : Bool, Jab p q s s' = 1 := by
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Jab_row, Jab_row, bval_add]

private lemma pB_eq_bval (σ : Vv → Bool) (v : Vv) (s : Bool) :
    pB G β σ v s = bval (pT G β σ v) s := rfl

private lemma pT_mem (σ : Vv → Bool) (v : Vv) : 0 ≤ pT G β σ v ∧ pT G β σ v ≤ 1 := by
  have h := abs_lt.mp (tanh_lt_one' (β * ((Sz G σ v : ℤ) : ℝ)))
  constructor <;> simp only [pT] <;> linarith [h.1, h.2]

/-! ### The coupled chain -/

private lemma ite_mul_sum {W : Type*} [Fintype W] [DecidableEq W] (z : W) (a : ℝ) (F : W → ℝ) :
    ∑ p' : W, (if p' = z then a else 0) * F p' = a * F z := by
  have h : ∀ p' ∈ (univ : Finset W), (if p' = z then a else 0) * F p'
      = if p' = z then a * F z else 0 := by
    intro p' _
    by_cases hp : p' = z <;> simp [hp]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' Finset.univ z (fun _ => a * F z)]
  simp

private lemma sum_ite_and {W : Type*} [Fintype W] [DecidableEq W] (P : Prop) [Decidable P]
    (z : W) (a : ℝ) : ∑ y : W, (if P ∧ y = z then a else 0) = if P then a else 0 := by
  by_cases h : P
  · simp only [h, true_and]
    rw [Finset.sum_ite_eq' Finset.univ z (fun _ => a)]
    simp
  · simp [h]

private lemma sum_ite_and' {W : Type*} [Fintype W] [DecidableEq W] (P : Prop) [Decidable P]
    (z : W) (a : ℝ) : ∑ y : W, (if y = z ∧ P then a else 0) = if P then a else 0 := by
  have : ∀ y : W, (if y = z ∧ P then a else 0) = if P ∧ y = z then a else 0 := by
    intro y
    by_cases h1 : P <;> by_cases h2 : y = z <;> simp [h1, h2]
  rw [Finset.sum_congr rfl fun y _ => this y]
  exact sum_ite_and P z a

private lemma sum_update_ind (σ x' : Vv → Bool) (v : Vv) (f : Bool → ℝ) :
    (∑ s : Bool, if x' = Function.update σ v s then f s else 0)
      = if ∀ w : Vv, w ≠ v → x' w = σ w then f (x' v) else 0 := by
  by_cases h : ∀ w : Vv, w ≠ v → x' w = σ w
  · rw [if_pos h]
    have hx : x' = Function.update σ v (x' v) := (agree_iff σ x' v).mp h
    have hkey : ∀ s : Bool, (if x' = Function.update σ v s then f s else 0)
        = if s = x' v then f (x' v) else 0 := by
      intro s
      by_cases hs : s = x' v
      · rw [if_pos (by rw [hs]; exact hx), if_pos hs, hs]
      · rw [if_neg hs, if_neg]
        intro hc
        exact hs (by rw [hc, Function.update_self])
    rw [Finset.sum_congr rfl fun s _ => hkey s,
      Finset.sum_ite_eq' Finset.univ (x' v) (fun _ => f (x' v))]
    simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [if_neg]
    intro hc
    exact h ((agree_iff σ x' v).mpr (by rw [hc, Function.update_self]))

/-- The coupled pair chain: update the same site, with the optimal coupling of the two
conditional laws there. -/
private def Qi : Matrix ((Vv → Bool) × (Vv → Bool)) ((Vv → Bool) × (Vv → Bool)) ℝ :=
  fun p p' => (Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv, ∑ s : Bool, ∑ s' : Bool,
    (if p' = (Function.update p.1 v s, Function.update p.2 v s') then
      Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0)

private lemma Qi_expect (p : (Vv → Bool) × (Vv → Bool)) (F : (Vv → Bool) × (Vv → Bool) → ℝ) :
    ∑ p' : (Vv → Bool) × (Vv → Bool), Qi G β p p' * F p'
      = (Fintype.card Vv : ℝ)⁻¹ * ∑ v : Vv, ∑ s : Bool, ∑ s' : Bool,
          Jab (pT G β p.1 v) (pT G β p.2 v) s s'
            * F (Function.update p.1 v s, Function.update p.2 v s') := by
  classical
  simp only [Qi, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  have h1 : ∀ p' : (Vv → Bool) × (Vv → Bool),
      (∑ v : Vv, ∑ s : Bool, ∑ s' : Bool,
        (if p' = (Function.update p.1 v s, Function.update p.2 v s') then
          Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0)) * F p'
      = ∑ v : Vv, ∑ s : Bool, ∑ s' : Bool,
          (if p' = (Function.update p.1 v s, Function.update p.2 v s') then
            Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0) * F p' := by
    intro p'
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl fun p' _ => h1 p', Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  exact ite_mul_sum _ _ _

private lemma Qi_marg1 [Nonempty Vv] (p : (Vv → Bool) × (Vv → Bool)) (x' : Vv → Bool) :
    ∑ y' : Vv → Bool, Qi G β p (x', y') = glauber (isingDist G β) p.1 x' := by
  classical
  simp only [Qi]
  rw [← Finset.mul_sum]
  rw [glauber_apply]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h1 : ∀ y' : Vv → Bool, (∑ s : Bool, ∑ s' : Bool,
      (if (x', y') = (Function.update p.1 v s, Function.update p.2 v s') then
        Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0))
      = ∑ s : Bool, ∑ s' : Bool,
        (if x' = Function.update p.1 v s ∧ y' = Function.update p.2 v s' then
          Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0) := by
    intro y'
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    simp only [Prod.mk.injEq]
  rw [Finset.sum_congr rfl fun y' _ => h1 y', Finset.sum_comm]
  refine Eq.trans ?_ (sum_update_ind p.1 x' v (fun s => pB G β p.1 v s))
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  have h2 : ∀ s' : Bool, ∑ y' : Vv → Bool,
      (if x' = Function.update p.1 v s ∧ y' = Function.update p.2 v s' then
        Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0)
      = if x' = Function.update p.1 v s then Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0 :=
    fun s' => sum_ite_and _ _ _
  rw [Finset.sum_congr rfl fun s' _ => h2 s']
  by_cases hx : x' = Function.update p.1 v s
  · simp only [if_pos hx]
    rw [Fintype.sum_bool, Jab_row, pB_eq_bval]
  · simp [hx]

private lemma Qi_marg2 [Nonempty Vv] (p : (Vv → Bool) × (Vv → Bool)) (y' : Vv → Bool) :
    ∑ x' : Vv → Bool, Qi G β p (x', y') = glauber (isingDist G β) p.2 y' := by
  classical
  simp only [Qi]
  rw [← Finset.mul_sum]
  rw [glauber_apply]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h1 : ∀ x' : Vv → Bool, (∑ s : Bool, ∑ s' : Bool,
      (if (x', y') = (Function.update p.1 v s, Function.update p.2 v s') then
        Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0))
      = ∑ s' : Bool, ∑ s : Bool,
        (if x' = Function.update p.1 v s ∧ y' = Function.update p.2 v s' then
          Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0) := by
    intro x'
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun s _ => ?_
    simp only [Prod.mk.injEq]
  rw [Finset.sum_congr rfl fun x' _ => h1 x', Finset.sum_comm]
  refine Eq.trans ?_ (sum_update_ind p.2 y' v (fun s' => pB G β p.2 v s'))
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Finset.sum_comm]
  have h2 : ∀ s : Bool, ∑ x' : Vv → Bool,
      (if x' = Function.update p.1 v s ∧ y' = Function.update p.2 v s' then
        Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0)
      = if y' = Function.update p.2 v s' then Jab (pT G β p.1 v) (pT G β p.2 v) s s' else 0 :=
    fun s => sum_ite_and' _ _ _
  rw [Finset.sum_congr rfl fun s _ => h2 s]
  by_cases hy : y' = Function.update p.2 v s'
  · simp only [if_pos hy]
    rw [Fintype.sum_bool, Jab_col, pB_eq_bval]
  · simp [hy]

private lemma Qi_stochastic [Nonempty Vv] : IsStochastic (Qi G β) := by
  have hN : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · intro p p'
    have hp := pT_mem G β p.1
    have hq := pT_mem G β p.2
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun v _ => ?_)
    refine Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun s' _ => ?_
    split_ifs
    · exact Jab_nonneg (hp v).1 (hp v).2 (hq v).1 (hq v).2 s s'
    · exact le_refl 0
  · intro p
    have h := Qi_expect G β p (fun _ => (1 : ℝ))
    simp only [mul_one] at h
    rw [h, Finset.sum_congr rfl fun v _ => Jab_total (pT G β p.1 v) (pT G β p.2 v)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    field_simp

private lemma Qi_diag [Nonempty Vv] (x : Vv → Bool) (q : (Vv → Bool) × (Vv → Bool))
    (hq : q.1 ≠ q.2) : Qi G β (x, x) q = 0 := by
  simp only [Qi]
  rw [mul_eq_zero]
  right
  refine Finset.sum_eq_zero fun v _ => ?_
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
  by_cases h : q = (Function.update x v s, Function.update x v s')
  · rw [if_pos h]
    by_cases hss : s = s'
    · exact absurd (by rw [h, hss]) hq
    · exact Jab_diag _ hss
  · rw [if_neg h]

private lemma Qi_markovian [Nonempty Vv] :
    IsMarkovianCoupling (glauber (isingDist G β)) (Qi G β) :=
  ⟨Qi_stochastic G β, Qi_marg1 G β, Qi_marg2 G β, Qi_diag G β⟩

/-! ### One-step contraction of the Hamming distance -/

private def rho (p : (Vv → Bool) × (Vv → Bool)) : ℝ := ((diffSet p.1 p.2).card : ℝ)

private lemma diffSet_update (σ τ : Vv → Bool) (v : Vv) (s s' : Bool) :
    ((diffSet (Function.update σ v s) (Function.update τ v s')).card : ℝ)
      = (((diffSet σ τ).erase v).card : ℝ) + (if s = s' then (0 : ℝ) else 1) := by
  classical
  by_cases h : s = s'
  · have hset : diffSet (Function.update σ v s) (Function.update τ v s')
        = (diffSet σ τ).erase v := by
      ext w
      simp only [mem_diffSet, Finset.mem_erase]
      by_cases hw : w = v
      · subst hw
        simp only [Function.update_self, h, ne_eq, not_true_eq_false, false_and]
      · rw [Function.update_apply, Function.update_apply, if_neg hw, if_neg hw]
        simp [hw, mem_diffSet]
    rw [hset, if_pos h, add_zero]
  · have hset : diffSet (Function.update σ v s) (Function.update τ v s')
        = insert v ((diffSet σ τ).erase v) := by
      ext w
      simp only [mem_diffSet, Finset.mem_insert, Finset.mem_erase]
      by_cases hw : w = v
      · subst hw
        simp only [Function.update_self, true_or, iff_true]
        exact h
      · rw [Function.update_apply, Function.update_apply, if_neg hw, if_neg hw]
        simp [hw, mem_diffSet]
    rw [hset, if_neg h, Finset.card_insert_of_notMem (Finset.notMem_erase v _)]
    push_cast
    ring

private lemma erase_card_eq (A : Finset Vv) (v : Vv) :
    ((A.erase v).card : ℝ) = (A.card : ℝ) - (if v ∈ A then (1 : ℝ) else 0) := by
  by_cases hv : v ∈ A
  · rw [if_pos hv]
    have h1 := Finset.card_erase_add_one hv
    have h2 : ((A.erase v).card : ℝ) + 1 = (A.card : ℝ) := by exact_mod_cast h1
    linarith
  · rw [if_neg hv, Finset.erase_eq_of_notMem hv]
    ring

private lemma sum_erase_card (D : Finset Vv) :
    ∑ v : Vv, ((D.erase v).card : ℝ)
      = (Fintype.card Vv : ℝ) * (D.card : ℝ) - (D.card : ℝ) := by
  rw [Finset.sum_congr rfl fun v _ => erase_card_eq D v, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

private lemma sum_local_diff (A : Finset Vv) :
    ∑ v : Vv, (G.neighborFinset v ∩ A).card ≤ G.maxDegree * A.card := by
  classical
  have hstep : ∀ v : Vv, (G.neighborFinset v ∩ A).card
      = ∑ w ∈ A, if w ∈ G.neighborFinset v then 1 else 0 := by
    intro v
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [Finset.sum_congr rfl fun v _ => hstep v, Finset.sum_comm]
  have hswap : ∀ w : Vv, ∑ v : Vv, (if w ∈ G.neighborFinset v then 1 else 0)
      = G.degree w := by
    intro w
    rw [← Finset.card_filter]
    have hh : (Finset.univ.filter fun v : Vv => w ∈ G.neighborFinset v)
        = G.neighborFinset w := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [hh]
    rfl
  rw [Finset.sum_congr rfl fun w _ => hswap w]
  calc ∑ w ∈ A, G.degree w ≤ ∑ _w ∈ A, G.maxDegree :=
        Finset.sum_le_sum fun w _ => G.degree_le_maxDegree w
    _ = G.maxDegree * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

private lemma pT_diff_le (hβ : 0 < β) (K : ℝ) (hK : 0 ≤ K) (Q : ℤ → Prop)
    (hQ : ∀ c : ℤ, Q c → Q (c + 2))
    (hstep : ∀ c : ℤ, Q c → Real.tanh (β * ((c : ℝ) + 2)) - Real.tanh (β * (c : ℝ)) ≤ K)
    (hQall : ∀ (σ : Vv → Bool) (v : Vv), Q (Sz G σ v))
    (σ τ : Vv → Bool) (v : Vv) :
    |pT G β σ v - pT G β τ v|
      ≤ (K / 2) * ((G.neighborFinset v ∩ diffSet σ τ).card : ℝ) := by
  obtain ⟨j, hjeq⟩ := Sz_diff_dvd G σ τ v
  have hbd := Sz_diff_bound G σ τ v
  have hjk : j.natAbs ≤ (G.neighborFinset v ∩ diffSet σ τ).card := by
    rw [abs_le] at hbd
    omega
  have hmain := tanh_abs_diff hβ K hK Q hQ hstep (Sz G σ v) (Sz G τ v)
    (hQall τ v) (hQall σ v) (G.neighborFinset v ∩ diffSet σ τ).card j hjeq hjk
  have hpt : pT G β σ v - pT G β τ v
      = (Real.tanh (β * ((Sz G σ v : ℤ) : ℝ)) - Real.tanh (β * ((Sz G τ v : ℤ) : ℝ))) / 2 := by
    simp only [pT]
    ring
  rw [hpt, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have : (K / 2) * ((G.neighborFinset v ∩ diffSet σ τ).card : ℝ) * 2
      = ((G.neighborFinset v ∩ diffSet σ τ).card : ℝ) * K := by ring
  rw [this]
  exact hmain

private lemma Qi_contract [Nonempty Vv] (K : ℝ) (hK : 0 ≤ K)
    (hdiff : ∀ (σ τ : Vv → Bool) (v : Vv),
      |pT G β σ v - pT G β τ v| ≤ (K / 2) * ((G.neighborFinset v ∩ diffSet σ τ).card : ℝ))
    (p : (Vv → Bool) × (Vv → Bool)) :
    ∑ p' : (Vv → Bool) × (Vv → Bool), Qi G β p p' * rho p'
      ≤ (1 - (1 - (K / 2) * (G.maxDegree : ℝ)) / (Fintype.card Vv : ℝ)) * rho p := by
  classical
  have hN : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [Qi_expect]
  have hper : ∀ v : Vv,
      (∑ s : Bool, ∑ s' : Bool, Jab (pT G β p.1 v) (pT G β p.2 v) s s'
          * rho (Function.update p.1 v s, Function.update p.2 v s'))
        = (((diffSet p.1 p.2).erase v).card : ℝ) + |pT G β p.1 v - pT G β p.2 v| := by
    intro v
    have hexp : ∀ s s' : Bool,
        Jab (pT G β p.1 v) (pT G β p.2 v) s s'
            * rho (Function.update p.1 v s, Function.update p.2 v s')
          = Jab (pT G β p.1 v) (pT G β p.2 v) s s' * (((diffSet p.1 p.2).erase v).card : ℝ)
            + Jab (pT G β p.1 v) (pT G β p.2 v) s s' * (if s = s' then (0:ℝ) else 1) := by
      intro s s'
      rw [show rho (Function.update p.1 v s, Function.update p.2 v s')
          = (((diffSet p.1 p.2).erase v).card : ℝ) + (if s = s' then (0:ℝ) else 1) from
        diffSet_update p.1 p.2 v s s']
      ring
    rw [Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => hexp s s']
    rw [Finset.sum_congr rfl fun s _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    · have hpull : ∀ s : Bool,
          (∑ s' : Bool, Jab (pT G β p.1 v) (pT G β p.2 v) s s'
              * (((diffSet p.1 p.2).erase v).card : ℝ))
            = (∑ s' : Bool, Jab (pT G β p.1 v) (pT G β p.2 v) s s')
              * (((diffSet p.1 p.2).erase v).card : ℝ) :=
        fun s => (Finset.sum_mul _ _ _).symm
      rw [Finset.sum_congr rfl fun s _ => hpull s, ← Finset.sum_mul, Jab_total, one_mul]
    · rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
      have h := Jab_off (pT G β p.1 v) (pT G β p.2 v)
      have e1 : (if (true : Bool) = true then (0:ℝ) else 1) = 0 := by norm_num
      have e2 : (if (true : Bool) = false then (0:ℝ) else 1) = 1 := by norm_num
      have e3 : (if (false : Bool) = true then (0:ℝ) else 1) = 1 := by norm_num
      have e4 : (if (false : Bool) = false then (0:ℝ) else 1) = 0 := by norm_num
      rw [e1, e2, e3, e4]
      linarith [h]
  rw [Finset.sum_congr rfl fun v _ => hper v, Finset.sum_add_distrib, sum_erase_card]
  have hlocal : ∑ v : Vv, |pT G β p.1 v - pT G β p.2 v|
      ≤ (K / 2) * ((G.maxDegree : ℝ) * ((diffSet p.1 p.2).card : ℝ)) := by
    refine le_trans (Finset.sum_le_sum fun v _ => hdiff p.1 p.2 v) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have h := sum_local_diff G (diffSet p.1 p.2)
    have h2 : ∑ v : Vv, ((G.neighborFinset v ∩ diffSet p.1 p.2).card : ℝ)
        = ((∑ v : Vv, (G.neighborFinset v ∩ diffSet p.1 p.2).card : ℕ) : ℝ) := by push_cast; ring
    rw [h2]
    exact_mod_cast h
  have hrho : rho p = ((diffSet p.1 p.2).card : ℝ) := rfl
  rw [hrho]
  rw [inv_mul_eq_div, div_le_iff₀ hN]
  have hfac : (1 - (1 - (K / 2) * (G.maxDegree : ℝ)) / (Fintype.card Vv : ℝ))
      * ((diffSet p.1 p.2).card : ℝ) * (Fintype.card Vv : ℝ)
      = (Fintype.card Vv : ℝ) * ((diffSet p.1 p.2).card : ℝ) - ((diffSet p.1 p.2).card : ℝ)
        + (K / 2) * ((G.maxDegree : ℝ) * ((diffSet p.1 p.2).card : ℝ)) := by
    field_simp
    ring
  rw [hfac]
  linarith

/-! ### Trajectories and iteration -/

section Paths

variable {W : Type*} [Fintype W] [DecidableEq W]

private lemma snoc_sum {t : ℕ} (f : (Fin (t + 2) → W) → ℝ) :
    ∑ ω : Fin (t + 2) → W, f ω
      = ∑ ω : Fin (t + 1) → W, ∑ y : W, f (Fin.snoc ω y) := by
  let e : ((Fin (t + 1) → W) × W) ≃ (Fin (t + 2) → W) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun ω => (Fin.init ω, ω (Fin.last _))
      left_inv := by intro p; ext <;> simp
      right_inv := by intro ω; simp }
  have := Equiv.sum_comp e f
  rw [← this, Fintype.sum_prod_type]
  rfl

private lemma pathWeight_snoc (Q : Matrix W W ℝ) {t : ℕ}
    (ω : Fin (t + 1) → W) (y : W) :
    pathWeight Q (Fin.snoc ω y : Fin (t + 2) → W)
      = pathWeight Q ω * Q (ω (Fin.last t)) y := by
  simp only [pathWeight]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [show (i.castSucc : Fin (t + 1)).castSucc = (i.castSucc : Fin (t+1)).castSucc from rfl,
      Fin.snoc_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_castSucc]
    congr 1
    rw [show (Fin.last t).succ = Fin.last (t + 1) from rfl, Fin.snoc_last]

private lemma group_by_last {t : ℕ} (F : (Fin (t + 1) → W) → ℝ) :
    ∑ ω : Fin (t + 1) → W, F ω
      = ∑ z : W, ∑ ω : Fin (t + 1) → W, (if ω (Fin.last t) = z then F ω else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp

private lemma sum_ite_last (c : ℝ) (f : W → ℝ) (h : W) :
    ∑ y : W, c * f y * (if y = h then (1 : ℝ) else 0) = c * f h := by
  have hcong : ∀ y ∈ (Finset.univ : Finset W), c * f y * (if y = h then (1 : ℝ) else 0)
      = if y = h then c * f h else 0 := by
    intro y _
    by_cases hy : y = h
    · subst hy; simp
    · simp [hy]
  rw [Finset.sum_congr rfl hcong]
  simp

private lemma path_pow (Q : Matrix W W ℝ) (t : ℕ) (z p : W) :
    ∑ ω : Fin (t + 1) → W,
        (if ω 0 = z ∧ ω (Fin.last t) = p then pathWeight Q ω else 0)
      = (Q ^ t) z p := by
  induction t generalizing p with
  | zero =>
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) W)
        (fun ω : Fin 1 → W => if ω 0 = z ∧ ω (Fin.last 0) = p then pathWeight Q ω else 0)
        (fun v : W => if v = z then (if p = z then (1 : ℝ) else 0) else 0)]
    · simp only [pow_zero, Matrix.one_apply]
      rw [Finset.sum_ite_eq' Finset.univ z]
      by_cases h : p = z
      · simp [h]
      · simp [h, Ne.symm h]
    · intro ω
      simp only [pathWeight, Finset.univ_eq_empty, Finset.prod_empty,
        Equiv.funUnique_apply]
      show (if ω 0 = z ∧ ω 0 = p then (1 : ℝ) else 0)
          = if ω 0 = z then (if p = z then (1 : ℝ) else 0) else 0
      by_cases h1 : ω 0 = z
      · rw [if_pos h1]
        by_cases h2 : p = z
        · rw [if_pos h2, if_pos ⟨h1, by rw [h1, h2]⟩]
        · rw [if_neg h2, if_neg]
          rintro ⟨-, hcon⟩
          exact h2 (by rw [← hcon, h1])
      · rw [if_neg h1, if_neg]
        rintro ⟨hcon, -⟩
        exact h1 hcon
  | succ t ih =>
    rw [snoc_sum]
    have key : ∀ (ω : Fin (t + 1) → W) (y : W),
        (if (Fin.snoc ω y : Fin (t + 2) → W) 0 = z ∧
              (Fin.snoc ω y : Fin (t + 2) → W) (Fin.last (t + 1)) = p then
            pathWeight Q (Fin.snoc ω y : Fin (t + 2) → W) else 0)
          = (if ω 0 = z then (1 : ℝ) else 0) * pathWeight Q ω *
              Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0) := by
      intro ω y
      have h0 : (Fin.snoc ω y : Fin (t + 2) → W) 0 = ω 0 := by
        have : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
        rw [this, Fin.snoc_castSucc]
      have hl : (Fin.snoc ω y : Fin (t + 2) → W) (Fin.last (t + 1)) = y := by simp
      rw [h0, hl, pathWeight_snoc]
      by_cases hx : ω 0 = z <;> by_cases hy : y = p <;> simp [hx, hy] <;> ring
    calc ∑ ω : Fin (t + 1) → W, ∑ y : W, _
        = ∑ ω : Fin (t + 1) → W, ∑ y : W,
            ((if ω 0 = z then (1 : ℝ) else 0) * pathWeight Q ω *
              Q (ω (Fin.last t)) y * (if y = p then (1 : ℝ) else 0)) :=
          Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun y _ => key ω y
      _ = ∑ ω : Fin (t + 1) → W,
            ((if ω 0 = z then (1 : ℝ) else 0) * pathWeight Q ω * Q (ω (Fin.last t)) p) :=
          Finset.sum_congr rfl fun ω _ => sum_ite_last _ _ p
      _ = ∑ z' : W, (Q ^ t) z z' * Q z' p := by
          rw [group_by_last (t := t)]
          refine Finset.sum_congr rfl fun z' _ => ?_
          rw [← ih z', Finset.sum_mul]
          refine Finset.sum_congr rfl fun ω _ => ?_
          by_cases hz : ω (Fin.last t) = z'
          · by_cases hx : ω 0 = z <;> simp [hz, hx] <;> ring
          · simp [hz]
      _ = (Q ^ (t + 1)) z p := by rw [pow_succ, Matrix.mul_apply]

private lemma pow_nonneg_of_stochastic {Q : Matrix W W ℝ} (hQ : IsStochastic Q) (t : ℕ)
    (z p : W) : 0 ≤ (Q ^ t) z p := by
  induction t generalizing p with
  | zero => rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z' _ => mul_nonneg (ih z') (hQ.1 _ _)

private lemma pow_contract (Q : Matrix W W ℝ) (hQ : IsStochastic Q) (r : W → ℝ)
    (hr : ∀ w, 0 ≤ r w) (κ : ℝ) (hκ : 0 ≤ κ)
    (hstep : ∀ z, ∑ p', Q z p' * r p' ≤ κ * r z) (t : ℕ) (z : W) :
    ∑ p' : W, (Q ^ t) z p' * r p' ≤ κ ^ t * r z := by
  induction t generalizing z with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul, pow_zero, one_mul]
    rw [Finset.sum_ite_eq Finset.univ z r]
    simp
  | succ t ih =>
    have hstep2 : ∑ p' : W, (Q ^ (t + 1)) z p' * r p'
        = ∑ z' : W, (Q ^ t) z z' * ∑ p' : W, Q z' p' * r p' := by
      have h1 : ∀ p' : W, (Q ^ (t + 1)) z p' * r p'
          = ∑ z' : W, (Q ^ t) z z' * Q z' p' * r p' := by
        intro p'; rw [pow_succ, Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun p' _ => h1 p', Finset.sum_comm]
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p' _ => by ring
    rw [hstep2]
    calc ∑ z' : W, (Q ^ t) z z' * ∑ p' : W, Q z' p' * r p'
        ≤ ∑ z' : W, (Q ^ t) z z' * (κ * r z') :=
          Finset.sum_le_sum fun z' _ =>
            mul_le_mul_of_nonneg_left (hstep z') (pow_nonneg_of_stochastic hQ t z z')
      _ = κ * ∑ z' : W, (Q ^ t) z z' * r z' := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z' _ => by ring
      _ ≤ κ * (κ ^ t * r z) := mul_le_mul_of_nonneg_left (ih z) hκ
      _ = κ ^ (t + 1) * r z := by ring

private lemma tail_le (Q : Matrix W W ℝ) (hQ : IsStochastic Q) (r : W → ℝ)
    (hr : ∀ w, 0 ≤ r w) (S : Finset W) (hS : ∀ w ∉ S, 1 ≤ r w) (z : W) (t : ℕ) :
    setAvoidTailProb Q z S t ≤ ∑ p' : W, (Q ^ t) z p' * r p' := by
  have hpw : ∀ ω : Fin (t + 1) → W, 0 ≤ pathWeight Q ω :=
    fun ω => Finset.prod_nonneg fun i _ => hQ.1 _ _
  have hle : setAvoidTailProb Q z S t
      ≤ ∑ ω : Fin (t + 1) → W,
          (if ω 0 = z then pathWeight Q ω * r (ω (Fin.last t)) else 0) := by
    simp only [setAvoidTailProb]
    refine Finset.sum_le_sum fun ω _ => ?_
    by_cases hc : ω 0 = z ∧ ∀ i : Fin (t + 1), ω i ∉ S
    · rw [if_pos hc, if_pos hc.1]
      have h1 : (1 : ℝ) ≤ r (ω (Fin.last t)) := hS _ (hc.2 _)
      nlinarith [hpw ω]
    · rw [if_neg hc]
      by_cases hz : ω 0 = z
      · rw [if_pos hz]
        exact mul_nonneg (hpw ω) (hr _)
      · rw [if_neg hz]
  refine hle.trans (le_of_eq ?_)
  rw [group_by_last (t := t)]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [← path_pow Q t z p', Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hlast : ω (Fin.last t) = p'
  · rw [if_pos hlast]
    by_cases hz : ω 0 = z
    · rw [if_pos hz, if_pos ⟨hz, hlast⟩, hlast]
    · rw [if_neg hz, if_neg (fun hc => hz hc.1), zero_mul]
  · rw [if_neg hlast, if_neg (fun hc => hlast hc.2), zero_mul]

end Paths

/-! ### Mixing -/

private lemma sum_div_const {α : Type*} (s : Finset α) (f : α → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  simp [div_eq_mul_inv, Finset.sum_mul]

private lemma isingZ_pos : (0 : ℝ) < ∑ η : Vv → Bool, isingWeight G β η :=
  Finset.sum_pos (fun η _ => Real.exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

private lemma isingDist_pos (σ : Vv → Bool) : 0 < isingDist G β σ := by
  rw [isingDist]
  exact div_pos (Real.exp_pos _) (isingZ_pos G β)

private lemma isingDist_isDist : IsDist (isingDist G β) := by
  refine ⟨fun σ => (isingDist_pos G β σ).le, ?_⟩
  simp only [isingDist]
  rw [← sum_div_const, div_self (ne_of_gt (isingZ_pos G β))]

private lemma glauber_stochastic [Nonempty Vv] : IsStochastic (glauber (isingDist G β)) := by
  have h := glauber_stationary (isingDist G β) (isingDist_isDist G β)
  exact ⟨h.1, fun x => h.2.1 x (isingDist_pos G β x)⟩

private lemma glauber_stat [Nonempty Vv] :
    IsStationary (glauber (isingDist G β)) (isingDist G β) :=
  (glauber_stationary (isingDist G β) (isingDist_isDist G β)).2.2.2

private lemma rho_nonneg (p : (Vv → Bool) × (Vv → Bool)) : 0 ≤ rho p := by
  rw [rho]; positivity

private lemma rho_le (p : (Vv → Bool) × (Vv → Bool)) : rho p ≤ (Fintype.card Vv : ℝ) := by
  rw [rho]
  have : (diffSet p.1 p.2).card ≤ Fintype.card Vv := by
    simpa using Finset.card_le_card (Finset.subset_univ (diffSet p.1 p.2))
  exact_mod_cast this

private lemma rho_off_diag (p : (Vv → Bool) × (Vv → Bool))
    (h : p ∉ pairDiagonal (Vv → Bool)) : 1 ≤ rho p := by
  simp only [pairDiagonal, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨v, hv⟩ : ∃ v : Vv, p.1 v ≠ p.2 v := by
    by_contra hcon
    exact h (funext fun v => not_not.mp fun hh => hcon ⟨v, hh⟩)
  have : (1 : ℕ) ≤ (diffSet p.1 p.2).card :=
    Finset.card_pos.mpr ⟨v, (mem_diffSet _ _ _).mpr hv⟩
  rw [rho]
  exact_mod_cast this

private lemma mixing_of_K [Nonempty Vv] (K : ℝ) (hK : 0 ≤ K)
    (hdiff : ∀ (σ τ : Vv → Bool) (v : Vv),
      |pT G β σ v - pT G β τ v| ≤ (K / 2) * ((G.neighborFinset v ∩ diffSet σ τ).card : ℝ))
    (hlt : (K / 2) * (G.maxDegree : ℝ) < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (mixingTime (glauber (isingDist G β)) (isingDist G β) ε : ℝ)
      ≤ ⌈(Fintype.card Vv : ℝ) * (Real.log (Fintype.card Vv) + Real.log (1 / ε))
          / (1 - (K / 2) * (G.maxDegree : ℝ))⌉₊ := by
  classical
  have hN : 0 < Fintype.card Vv := Fintype.card_pos
  have hNr : (0 : ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (Fintype.card Vv : ℝ) := by exact_mod_cast hN
  have hP := glauber_stochastic G β
  have hpi := glauber_stat G β
  set cst : ℝ := 1 - (K / 2) * (G.maxDegree : ℝ) with hcstdef
  have hcst0 : 0 < cst := by rw [hcstdef]; linarith
  have hcst1 : cst ≤ 1 := by
    have hnn : 0 ≤ (K / 2) * (G.maxDegree : ℝ) := by positivity
    rw [hcstdef]; linarith
  set kap : ℝ := 1 - cst / (Fintype.card Vv : ℝ) with hkapdef
  have hkap0 : 0 ≤ kap := by
    have h1 : cst / (Fintype.card Vv : ℝ) ≤ 1 := by rw [div_le_one hNr]; linarith
    rw [hkapdef]; linarith
  have hstepQ : ∀ p : (Vv → Bool) × (Vv → Bool),
      ∑ p', Qi G β p p' * rho p' ≤ kap * rho p := by
    intro p
    rw [hkapdef, hcstdef]
    exact Qi_contract G β K hK hdiff p
  have hQst : IsStochastic (Qi G β) := Qi_stochastic G β
  have htail : ∀ (t : ℕ) (p : (Vv → Bool) × (Vv → Bool)),
      setAvoidTailProb (Qi G β) p (pairDiagonal (Vv → Bool)) t
        ≤ kap ^ t * (Fintype.card Vv : ℝ) := by
    intro t p
    calc setAvoidTailProb (Qi G β) p (pairDiagonal (Vv → Bool)) t
        ≤ ∑ p' : (Vv → Bool) × (Vv → Bool), ((Qi G β) ^ t) p p' * rho p' :=
          tail_le _ hQst rho rho_nonneg (pairDiagonal (Vv → Bool))
            (fun w hw => rho_off_diag w hw) p t
      _ ≤ kap ^ t * rho p := pow_contract _ hQst rho rho_nonneg kap hkap0 hstepQ t p
      _ ≤ kap ^ t * (Fintype.card Vv : ℝ) :=
          mul_le_mul_of_nonneg_left (rho_le p) (by positivity)
  have hd : ∀ t : ℕ, distStationary (glauber (isingDist G β)) (isingDist G β) t
      ≤ kap ^ t * (Fintype.card Vv : ℝ) := by
    intro t
    have hcb := (coupling_bound (glauber (isingDist G β)) hP (isingDist G β) hpi
      (fun _ _ => Qi G β) (fun _ _ => Qi_markovian G β) t).2
    exact hcb.trans (ciSup_le fun p => htail t p)
  set L : ℝ := Real.log (Fintype.card Vv) + Real.log (1 / ε) with hLdef
  have hL0 : 0 ≤ L := by
    have h1 : 0 ≤ Real.log (Fintype.card Vv) := Real.log_nonneg hN1
    have h2 : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    rw [hLdef]; linarith
  set X : ℝ := (Fintype.card Vv : ℝ) * L / cst with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  set T : ℕ := ⌈X⌉₊ with hTdef
  have hTX : X ≤ (T : ℝ) := Nat.le_ceil X
  have hdT : distStationary (glauber (isingDist G β)) (isingDist G β) T ≤ ε := by
    refine (hd T).trans ?_
    have hkexp : kap ≤ Real.exp (-(cst / (Fintype.card Vv : ℝ))) := by
      have h := Real.add_one_le_exp (-(cst / (Fintype.card Vv : ℝ)))
      rw [hkapdef]; linarith
    have hpow : kap ^ T ≤ Real.exp (-(cst / (Fintype.card Vv : ℝ))) ^ T :=
      pow_le_pow_left₀ hkap0 hkexp T
    have hE : Real.exp (-(cst / (Fintype.card Vv : ℝ))) ^ T
        = Real.exp ((T : ℝ) * -(cst / (Fintype.card Vv : ℝ))) := by rw [Real.exp_nat_mul]
    have hle : (T : ℝ) * -(cst / (Fintype.card Vv : ℝ)) ≤ -L := by
      have h3 : X * (cst / (Fintype.card Vv : ℝ)) = L := by
        rw [hXdef]; field_simp
      have h2 : X * (cst / (Fintype.card Vv : ℝ)) ≤ (T : ℝ) * (cst / (Fintype.card Vv : ℝ)) :=
        mul_le_mul_of_nonneg_right hTX (by positivity)
      rw [h3] at h2
      linarith
    have hmono : Real.exp ((T : ℝ) * -(cst / (Fintype.card Vv : ℝ))) ≤ Real.exp (-L) :=
      Real.exp_le_exp.mpr hle
    have hexp : Real.exp (-L) * (Fintype.card Vv : ℝ) = ε := by
      rw [hLdef, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hNr,
        Real.exp_log (by positivity : (0 : ℝ) < 1 / ε)]
      field_simp
    calc kap ^ T * (Fintype.card Vv : ℝ)
        ≤ Real.exp (-L) * (Fintype.card Vv : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hNr.le
          rw [hE] at hpow
          exact hpow.trans hmono
      _ = ε := hexp
  have hmix : mixingTime (glauber (isingDist G β)) (isingDist G β) ε ≤ T := Nat.sInf_le hdT
  exact_mod_cast hmix

end Ising

end

end MarkovMixing

open MarkovMixing

open scoped BigOperators

/-- **Theorem 15.1** (LPW), the capstone of Chapter 15: fast mixing of the
Ising Glauber dynamics at high temperature. -/
theorem solution {Vv : Type*} [Fintype Vv] [DecidableEq Vv]
    [Nonempty Vv] (G : SimpleGraph Vv) [DecidableRel G.Adj]
    (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((G.maxDegree : ℝ) * Real.tanh β < 1 →
      (mixingTime (glauber (isingDist G β)) (isingDist G β) ε : ℝ) ≤
        ⌈(Fintype.card Vv : ℝ) *
            (Real.log (Fintype.card Vv) + Real.log (1 / ε)) /
          (1 - (G.maxDegree : ℝ) * Real.tanh β)⌉₊) ∧
    ((∀ v : Vv, Even (G.degree v)) →
      ((G.maxDegree : ℝ) / 2) * Real.tanh (2 * β) < 1 →
      (mixingTime (glauber (isingDist G β)) (isingDist G β) ε : ℝ) ≤
        ⌈(Fintype.card Vv : ℝ) *
            (Real.log (Fintype.card Vv) + Real.log (1 / ε)) /
          (1 - ((G.maxDegree : ℝ) / 2) * Real.tanh (2 * β))⌉₊) := by
  have htanh0 : 0 ≤ Real.tanh β := by
    rw [← Real.tanh_zero]
    exact tanh_mono hβ.le
  have htanh0' : 0 ≤ Real.tanh (2 * β) := by
    rw [← Real.tanh_zero]
    exact tanh_mono (by linarith)
  constructor
  · intro hDob
    have hK : (0 : ℝ) ≤ 2 * Real.tanh β := by linarith
    have hdiff := pT_diff_le G β hβ (2 * Real.tanh β) hK (fun _ => True)
      (fun _ _ => trivial) (fun c _ => tanh_step_gen hβ (c : ℝ)) (fun _ _ => trivial)
    have hlt : (2 * Real.tanh β) / 2 * (G.maxDegree : ℝ) < 1 := by
      rw [show (2 * Real.tanh β) / 2 * (G.maxDegree : ℝ)
        = (G.maxDegree : ℝ) * Real.tanh β from by ring]
      exact hDob
    have hmain := mixing_of_K G β (2 * Real.tanh β) hK hdiff hlt ε hε hε1
    rw [show 1 - (2 * Real.tanh β) / 2 * (G.maxDegree : ℝ)
      = 1 - (G.maxDegree : ℝ) * Real.tanh β from by ring] at hmain
    exact hmain
  · intro hEven hDob
    have hstep : ∀ c : ℤ, (2 : ℤ) ∣ c →
        Real.tanh (β * ((c : ℝ) + 2)) - Real.tanh (β * (c : ℝ)) ≤ Real.tanh (2 * β) := by
      intro c hc
      refine tanh_step_far hβ (c : ℝ) ?_
      have h1 : (1 : ℤ) ≤ |c + 1| := by
        obtain ⟨k, rfl⟩ := hc
        rcases (by omega : (0 : ℤ) ≤ 2 * k + 1 ∨ 2 * k + 1 < 0) with h | h
        · rw [abs_of_nonneg h]; omega
        · rw [abs_of_neg h]; omega
      exact_mod_cast h1
    have hQall : ∀ (σ : Vv → Bool) (v : Vv), (2 : ℤ) ∣ Sz G σ v := by
      intro σ v
      have h1 := Sz_sub_degree_even G σ v
      have h2 : (2 : ℤ) ∣ (G.degree v : ℤ) := by
        obtain ⟨k, hk⟩ := hEven v
        exact ⟨k, by rw [hk]; push_cast; ring⟩
      omega
    have hdiff := pT_diff_le G β hβ (Real.tanh (2 * β)) htanh0' (fun c => (2 : ℤ) ∣ c)
      (fun c hc => by omega) hstep hQall
    have hlt : Real.tanh (2 * β) / 2 * (G.maxDegree : ℝ) < 1 := by
      rw [show Real.tanh (2 * β) / 2 * (G.maxDegree : ℝ)
        = ((G.maxDegree : ℝ) / 2) * Real.tanh (2 * β) from by ring]
      exact hDob
    have hmain := mixing_of_K G β (Real.tanh (2 * β)) htanh0' hdiff hlt ε hε hε1
    rw [show 1 - Real.tanh (2 * β) / 2 * (G.maxDegree : ℝ)
      = 1 - ((G.maxDegree : ℝ) / 2) * Real.tanh (2 * β) from by ring] at hmain
    exact hmain
