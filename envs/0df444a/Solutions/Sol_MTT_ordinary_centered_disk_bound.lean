-- Prove2me | solution 1 for MTT.ordinary_centered_disk_bound
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T03:37:33.999785+00:00
-- url     : https://prove2.me/submissions/cbc0ed70-d656-4035-966d-af98d8975557

import Mathlib
import Definitions.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open Finset MTT

namespace MTTCentred

/-- Binomial inversion: recentring the shifted moments at `a` recovers `m ^ j * V j`. -/
theorem centered_collapse {R : Type*} [CommRing R] (V : ℕ → R) (m a : R) (j : ℕ) :
    (∑ t ∈ range (j + 1), (j.choose t : R) * (-a) ^ (j - t) *
      (∑ u ∈ range (t + 1), (t.choose u : R) * m ^ u * a ^ (t - u) * V u))
      = m ^ j * V j := by
  have step1 : ∀ t ∈ range (j + 1),
      (j.choose t : R) * (-a) ^ (j - t) *
        (∑ u ∈ range (t + 1), (t.choose u : R) * m ^ u * a ^ (t - u) * V u)
      = ∑ u ∈ range (t + 1),
          ((j.choose t : R) * (t.choose u : R)) *
            ((-a) ^ (j - t) * a ^ (t - u) * m ^ u * V u) := by
    intro t _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [Finset.sum_congr rfl step1]
  rw [Finset.sum_comm' (t' := range (j + 1)) (s' := fun u => Finset.Ico u (j + 1))
      (h := by intro x y; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have inner : ∀ u ∈ range (j + 1),
      (∑ t ∈ Finset.Ico u (j + 1),
        ((j.choose t : R) * (t.choose u : R)) *
          ((-a) ^ (j - t) * a ^ (t - u) * m ^ u * V u))
      = (j.choose u : R) * m ^ u * V u * (0 : R) ^ (j - u) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hu' : u ≤ j := Nat.lt_succ_iff.mp hu
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : j + 1 - u = (j - u) + 1 := by omega
    rw [hlen]
    have key : ∀ v ∈ range ((j - u) + 1),
        ((j.choose (u + v) : R) * ((u + v).choose u : R)) *
          ((-a) ^ (j - (u + v)) * a ^ ((u + v) - u) * m ^ u * V u)
        = ((j.choose u : R) * m ^ u * V u) *
            (a ^ v * (-a) ^ ((j - u) - v) * ((j - u).choose v : R)) := by
      intro v hv
      rw [Finset.mem_range] at hv
      have hv' : v ≤ j - u := Nat.lt_succ_iff.mp hv
      have hch : j.choose (u + v) * (u + v).choose u = j.choose u * (j - u).choose v := by
        have := Nat.choose_mul (n := j) (k := u + v) (s := u) (Nat.le_add_right u v)
        simpa using this
      have h1 : j - (u + v) = (j - u) - v := by omega
      have h2 : (u + v) - u = v := by omega
      rw [h1, h2]
      have hcast : ((j.choose (u + v) : R) * ((u + v).choose u : R))
          = ((j.choose u : R) * ((j - u).choose v : R)) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) hch
      rw [hcast]; ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    have hbin : (∑ v ∈ range ((j - u) + 1),
        a ^ v * (-a) ^ ((j - u) - v) * ((j - u).choose v : R)) = (0 : R) ^ (j - u) := by
      rw [← add_pow]; simp
    rw [hbin]
  rw [Finset.sum_congr rfl inner, Finset.sum_eq_single j]
  · simp
  · intro u hu hne
    rw [Finset.mem_range] at hu
    have : j - u ≠ 0 := by omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.self_mem_range_succ j) h

variable {p : ℕ} [Fact p.Prime]

/-- A finitely generated `ℤ`-submodule of `Qbar` has uniformly bounded image in `ℂ_[p]`. -/
theorem fg_norm_bound (ιp : Qbar →+* ℂ_[p]) (S : Set Qbar)
    (hS : (Submodule.span ℤ S).FG) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ‖ιp x‖ ≤ B := by
  obtain ⟨T, hT⟩ := hS
  refine ⟨∑ t ∈ T, ‖ιp t‖, Finset.sum_nonneg fun t _ => norm_nonneg _, ?_⟩
  have key : ∀ x ∈ Submodule.span ℤ (↑T : Set Qbar), ‖ιp x‖ ≤ ∑ t ∈ T, ‖ιp t‖ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        exact Finset.single_le_sum (f := fun t => ‖ιp t‖)
          (fun t _ => norm_nonneg _) (by simpa using hy)
    | zero => simpa using Finset.sum_nonneg fun t _ => norm_nonneg _
    | add y z _ _ hy hz =>
        refine le_trans ?_ (max_le hy hz)
        simpa using IsUltrametricDist.norm_add_le_max (ιp y) (ιp z)
    | smul c y _ hy =>
        have hc : ιp (c • y) = (c : ℂ_[p]) * ιp y := by rw [zsmul_eq_mul, map_mul, map_intCast]
        rw [hc, norm_mul]
        calc ‖(c : ℂ_[p])‖ * ‖ιp y‖ ≤ 1 * ‖ιp y‖ :=
              mul_le_mul_of_nonneg_right
                (IsUltrametricDist.norm_intCast_le_one _ c) (norm_nonneg _)
          _ = ‖ιp y‖ := one_mul _
          _ ≤ _ := hy
  intro x hx
  exact key x (hT ▸ Submodule.subset_span hx)

theorem ip_algebraicSymbol {k : ℕ} {ι : Qbar →+* ℂ} {f : UpperHalfPlane → ℂ}
    (P : Periods k ι f) (ιp : Qbar →+* ℂ_[p]) (s : Bool) (t : ℕ) (a m : ℚ) :
    ιp (algebraicSymbol P s t a m)
      = ∑ u ∈ range (t + 1), (t.choose u : ℂ_[p]) * (m : ℂ_[p]) ^ u *
          (a : ℂ_[p]) ^ (t - u) * ιp (P.value s u (-a / m)) := by
  simp only [algebraicSymbol, map_sum, map_mul, map_pow, map_natCast, map_ratCast]

end MTTCentred

open MTTCentred in
theorem solution {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Bool) (n : ℕ), 0 < n →
      ∀ (a : ℤ) (j : ℕ), j ≤ k - 2 →
        ‖∑ t ∈ Finset.range (j + 1),
          (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
            diskMoment f ιp P α s t n a‖ ≤
          C * ‖(p : ℂ_[p]) ^ (n * j)‖ := by
  classical
  obtain ⟨B, hB0, hB⟩ := fg_norm_bound ιp _ P.lattice_fg
  set E : ℝ := ‖ιp (f.epsilon (p : ZMod N))‖ with hE
  have hE0 : 0 ≤ E := norm_nonneg _
  refine ⟨B + E * B, by positivity, ?_⟩
  intro s n hn a j hj
  -- the two algebraic values that survive the recentring
  have hval1 : ‖ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ n))‖ ≤ B := hB _ ⟨s, j, _, hj, rfl⟩
  have hval2 : ‖ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖ ≤ B := hB _ ⟨s, j, _, hj, rfl⟩
  -- recentring collapses each modular-symbol sum to a single algebraic value
  have key : ∀ m : ℚ,
      (∑ t ∈ range (j + 1), (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
        ιp (algebraicSymbol P s t (a : ℚ) m))
      = (m : ℂ_[p]) ^ j * ιp (P.value s j (-(a : ℚ) / m)) := by
    intro m
    have h2 := centered_collapse (R := ℂ_[p]) (fun u => ιp (P.value s u (-(a : ℚ) / m)))
        (m : ℂ_[p]) ((a : ℤ) : ℂ_[p]) j
    rw [← h2]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ip_algebraicSymbol]
    simp only [Rat.cast_intCast]
  have hsum : (∑ t ∈ Finset.range (j + 1),
        (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) * diskMoment f ιp P α s t n a)
      = (α ^ n)⁻¹ * (((p : ℚ) ^ n : ℚ) : ℂ_[p]) ^ j *
            ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ n))
        - ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
            ((((p : ℚ) ^ (n - 1) : ℚ)) : ℂ_[p]) ^ j *
              ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1))) := by
    have expand : ∀ t ∈ range (j + 1),
        (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) * diskMoment f ιp P α s t n a
        = (α ^ n)⁻¹ * ((j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
              ιp (algebraicSymbol P s t (a : ℚ) ((p : ℚ) ^ n)))
          - ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
              ((j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
                ιp (algebraicSymbol P s t (a : ℚ) ((p : ℚ) ^ (n - 1)))) := by
      intro t _
      simp only [diskMoment]
      ring
    rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      key, key]
    ring
  rw [hsum]
  have hpn : ((((p : ℚ)) ^ n : ℚ) : ℂ_[p]) = (p : ℂ_[p]) ^ n := by push_cast; ring
  have hpn1 : ((((p : ℚ)) ^ (n - 1) : ℚ) : ℂ_[p]) = (p : ℂ_[p]) ^ (n - 1) := by push_cast; ring
  rw [hpn, hpn1, ← pow_mul, ← pow_mul]
  set q : ℝ := ‖(p : ℂ_[p])‖ with hq
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ p
  have hαn : ‖(α ^ n)⁻¹‖ = 1 := by rw [norm_inv, norm_pow, hα.1, one_pow, inv_one]
  have hαn1 : ‖α ^ (n + 1)‖ = 1 := by rw [norm_pow, hα.1, one_pow]
  have hexp : n * j ≤ (k - 2) + (n - 1) * j := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 : (n' + 1) * j = n' * j + j := by ring
    omega
  have t1 : ‖(α ^ n)⁻¹ * (p : ℂ_[p]) ^ (n * j) *
      ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ n))‖ ≤ B * q ^ (n * j) := by
    rw [norm_mul, norm_mul, hαn, one_mul, norm_pow]
    calc q ^ (n * j) * ‖ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ n))‖
        ≤ q ^ (n * j) * B := by
          exact mul_le_mul_of_nonneg_left hval1 (pow_nonneg hq0 _)
      _ = B * q ^ (n * j) := by ring
  have t2 : ‖ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
      (p : ℂ_[p]) ^ ((n - 1) * j) *
      ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖ ≤ E * B * q ^ (n * j) := by
    rw [norm_mul, norm_mul, norm_div, norm_mul, hαn1, div_one, norm_pow, norm_pow, ← hE]
    calc E * q ^ (k - 2) * q ^ ((n - 1) * j) *
            ‖ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖
        = E * ‖ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖ *
            q ^ ((k - 2) + (n - 1) * j) := by rw [pow_add]; ring
      _ ≤ E * B * q ^ (n * j) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hval2 hE0)
            (pow_le_pow_of_le_one hq0 hq1 hexp) (pow_nonneg hq0 _) (by positivity)
  have hrhs : ‖(p : ℂ_[p]) ^ (n * j)‖ = q ^ (n * j) := norm_pow _ _
  rw [hrhs]
  calc ‖(α ^ n)⁻¹ * (p : ℂ_[p]) ^ (n * j) * ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ n))
        - ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
            (p : ℂ_[p]) ^ ((n - 1) * j) * ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖
      ≤ _ + _ := norm_sub_le _ _
    _ ≤ B * q ^ (n * j) + E * B * q ^ (n * j) := add_le_add t1 t2
    _ = (B + E * B) * q ^ (n * j) := by ring
