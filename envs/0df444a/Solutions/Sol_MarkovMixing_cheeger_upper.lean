-- Prove2me | solution 1 for MarkovMixing.cheeger_upper
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T16:46:28.017916+00:00
-- url     : https://prove2.me/submissions/eff72ab6-82ba-426f-a096-60e18752c4dc

import Definitions.Def_mm_spectral
import Definitions.Def_mm_lower
import Theorems.Thm_MarkovMixing_dirichlet_gap
import Mathlib.Tactic

set_option maxHeartbeats 1000000

open scoped BigOperators
open MarkovMixing

namespace CheegerUp

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

lemma vecMul_pow {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

lemma pi_pos {P : Matrix V V ℝ} (hirr : MarkovMixing.Irreducible P) {π : V → ℝ}
    (hπ : IsStationary P π) (hP : IsStochastic P) : ∀ x, 0 < π x := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < π y := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    have := hπ.1.2
    linarith
  intro x
  obtain ⟨t, ht⟩ := hirr y x
  have hv : ∑ z, π z * (P ^ t) z x = π x := congrFun (vecMul_pow hπ t) x
  have h2 : π y * (P ^ t) y x ≤ ∑ z, π z * (P ^ t) z x := by
    refine Finset.single_le_sum (f := fun z => π z * (P ^ t) z x) ?_ (Finset.mem_univ y)
    exact fun z _ => mul_nonneg (hπ.1.1 z) (pow_entry_nonneg hP t z x)
  have := mul_pos hy ht
  linarith

end CheegerUp

open CheegerUp

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    MarkovMixing.spectralGap P ≤ 2 * MarkovMixing.bottleneckStar P π := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hsum : ∑ x, π x = 1 := hπ.1.2
  obtain ⟨hgap, -⟩ := MarkovMixing.dirichlet_gap hV P hP hirr π hπ hrev
  -- the constraint set is nonempty
  have hne : Nonempty {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹} := by
    obtain ⟨x, hx⟩ : ∃ x : V, π x ≤ 2⁻¹ := by
      by_contra hcon
      push_neg at hcon
      have hcard : 1 < Fintype.card V := by omega
      obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card hcard
      have h1 : π x + π y ≤ ∑ z, π z := by
        have : ({x, y} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
        calc π x + π y = ∑ z ∈ ({x, y} : Finset V), π z := by
              rw [Finset.sum_pair hxy]
          _ ≤ ∑ z, π z := Finset.sum_le_sum_of_subset_of_nonneg this
              (fun i _ _ => (hpos i).le)
      have := hcon x
      have := hcon y
      linarith
    exact ⟨⟨{x}, ⟨Finset.singleton_nonempty x, by simpa using hx⟩⟩⟩
  -- the key bound for a single set
  have hkey : ∀ S : {S : Finset V // S.Nonempty ∧ ∑ x ∈ S, π x ≤ 2⁻¹},
      MarkovMixing.spectralGap P / 2 ≤ MarkovMixing.bottleneckRatio P π S.1 := by
    rintro ⟨S, hSne, hShalf⟩
    set p : ℝ := ∑ x ∈ S, π x with hp_def
    set q : ℝ := ∑ x ∈ Sᶜ, π x with hq_def
    have hpq : p + q = 1 := by rw [hp_def, hq_def, Finset.sum_add_sum_compl S π, hsum]
    have hppos : 0 < p := by
      obtain ⟨x, hx⟩ := hSne
      have : 0 < π x := hpos x
      have := Finset.single_le_sum (f := π) (fun i _ => (hpos i).le) hx
      linarith
    have hqpos : (2:ℝ)⁻¹ ≤ q := by linarith
    -- the test function
    set f : V → ℝ := fun x => if x ∈ S then -q else p with hf_def
    have hexp : MarkovMixing.distExp π f = 0 := by
      show ∑ x, f x * π x = 0
      rw [← Finset.sum_add_sum_compl S (fun x => f x * π x)]
      have e1 : ∀ x ∈ S, f x * π x = -q * π x := by
        intro x hx; rw [hf_def]; simp [hx]
      have e2 : ∀ x ∈ Sᶜ, f x * π x = p * π x := by
        intro x hx
        rw [Finset.mem_compl] at hx
        rw [hf_def]; simp [hx]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum,
        ← hp_def, ← hq_def]
      ring
    have hnorm : MarkovMixing.innerPi π f f = p * q := by
      show ∑ x, f x * f x * π x = p * q
      rw [← Finset.sum_add_sum_compl S (fun x => f x * f x * π x)]
      have e1 : ∀ x ∈ S, f x * f x * π x = (q * q) * π x := by
        intro x hx; rw [hf_def]; simp [hx]
      have e2 : ∀ x ∈ Sᶜ, f x * f x * π x = (p * p) * π x := by
        intro x hx
        rw [Finset.mem_compl] at hx
        rw [hf_def]; simp [hx]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum,
        ← hp_def, ← hq_def]
      linear_combination (p * q) * hpq
    -- the Dirichlet form of the test function is the edge flow across the cut
    set Q : ℝ := ∑ x ∈ S, ∑ y ∈ Sᶜ, π x * P x y with hQ_def
    have hQnn : 0 ≤ Q := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hpos x).le (hP.1 x y)
    have hsplit : ∀ g : V → V → ℝ, ∑ x, ∑ y, g x y
        = ((∑ x ∈ S, ∑ y ∈ S, g x y) + ∑ x ∈ S, ∑ y ∈ Sᶜ, g x y)
          + ((∑ x ∈ Sᶜ, ∑ y ∈ S, g x y) + ∑ x ∈ Sᶜ, ∑ y ∈ Sᶜ, g x y) := by
      intro g
      have e : ∀ x : V, ∑ y, g x y = (∑ y ∈ S, g x y) + ∑ y ∈ Sᶜ, g x y :=
        fun x => (Finset.sum_add_sum_compl S (fun y => g x y)).symm
      rw [← Finset.sum_add_sum_compl S (fun x => ∑ y, g x y),
        Finset.sum_congr rfl (fun x (_ : x ∈ S) => e x),
        Finset.sum_congr rfl (fun x (_ : x ∈ Sᶜ) => e x),
        Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hdir : MarkovMixing.dirichletForm P π f = Q := by
      show 2⁻¹ * ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y) = Q
      rw [hsplit]
      have z1 : ∑ x ∈ S, ∑ y ∈ S, (f x - f y) ^ 2 * (π x * P x y) = 0 := by
        refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
        rw [hf_def]; simp [hx, hy]
      have z2 : ∑ x ∈ Sᶜ, ∑ y ∈ Sᶜ, (f x - f y) ^ 2 * (π x * P x y) = 0 := by
        refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_
        rw [Finset.mem_compl] at hx hy
        rw [hf_def]; simp [hx, hy]
      have z3 : ∑ x ∈ S, ∑ y ∈ Sᶜ, (f x - f y) ^ 2 * (π x * P x y) = Q := by
        refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
        rw [Finset.mem_compl] at hy
        simp only [hf_def, if_pos hx, if_neg hy]
        have h1 : (-q - p) ^ 2 = 1 := by nlinarith [hpq]
        rw [h1, one_mul]
      have z4 : ∑ x ∈ Sᶜ, ∑ y ∈ S, (f x - f y) ^ 2 * (π x * P x y) = Q := by
        have e : ∑ x ∈ Sᶜ, ∑ y ∈ S, (f x - f y) ^ 2 * (π x * P x y)
            = ∑ x ∈ Sᶜ, ∑ y ∈ S, π y * P y x := by
          refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
          rw [Finset.mem_compl] at hx
          simp only [hf_def, if_neg hx, if_pos hy]
          have h1 : (p - -q) ^ 2 = 1 := by nlinarith [hpq]
          rw [h1, one_mul, hrev x y]
        rw [e, Finset.sum_comm, hQ_def]
      rw [z1, z2, z3, z4]
      ring
    -- normalise
    have hpqpos : 0 < p * q := by nlinarith
    set c : ℝ := (Real.sqrt (p * q))⁻¹ with hc_def
    have hcsq : c ^ 2 = (p * q)⁻¹ := by
      rw [hc_def, inv_pow, Real.sq_sqrt hpqpos.le]
    set g : V → ℝ := fun x => c * f x with hg_def
    have hgexp : MarkovMixing.distExp π g = 0 := by
      show ∑ x, g x * π x = 0
      have e : ∀ x : V, g x * π x = c * (f x * π x) := fun x => by rw [hg_def]; ring
      rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum]
      show c * MarkovMixing.distExp π f = 0
      rw [hexp, mul_zero]
    have hgnorm : MarkovMixing.innerPi π g g = 1 := by
      show ∑ x, g x * g x * π x = 1
      have e : ∀ x : V, g x * g x * π x = c ^ 2 * (f x * f x * π x) := fun x => by
        rw [hg_def]; ring
      rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum]
      show c ^ 2 * MarkovMixing.innerPi π f f = 1
      rw [hnorm, hcsq]
      field_simp
    have hgdir : MarkovMixing.dirichletForm P π g = Q / (p * q) := by
      show 2⁻¹ * ∑ x, ∑ y, (g x - g y) ^ 2 * (π x * P x y) = Q / (p * q)
      have e : ∀ x y : V, (g x - g y) ^ 2 * (π x * P x y)
          = c ^ 2 * ((f x - f y) ^ 2 * (π x * P x y)) := by
        intro x y; rw [hg_def]; ring
      have e2 : ∀ x : V, ∑ y, (g x - g y) ^ 2 * (π x * P x y)
          = c ^ 2 * ∑ y, (f x - f y) ^ 2 * (π x * P x y) := by
        intro x
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => e x y
      rw [Finset.sum_congr rfl (fun x _ => e2 x), ← Finset.mul_sum]
      have : 2⁻¹ * (c ^ 2 * ∑ x, ∑ y, (f x - f y) ^ 2 * (π x * P x y))
          = c ^ 2 * MarkovMixing.dirichletForm P π f := by
        show _ = c ^ 2 * (2⁻¹ * _)
        ring
      rw [this, hdir, hcsq]
      field_simp
    -- compare with the infimum
    have hbdd : BddBelow {e : ℝ | ∃ h : V → ℝ, MarkovMixing.distExp π h = 0 ∧
        MarkovMixing.innerPi π h h = 1 ∧ e = MarkovMixing.dirichletForm P π h} := by
      refine ⟨0, ?_⟩
      rintro e ⟨h, -, -, rfl⟩
      show (0:ℝ) ≤ 2⁻¹ * ∑ x, ∑ y, (h x - h y) ^ 2 * (π x * P x y)
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (hpos x).le (hP.1 x y))
    have hle : MarkovMixing.spectralGap P ≤ Q / (p * q) := by
      rw [hgap]
      exact csInf_le hbdd ⟨g, hgexp, hgnorm, hgdir.symm⟩
    show MarkovMixing.spectralGap P / 2 ≤ Q / p
    have h1 : Q / (p * q) ≤ 2 * (Q / p) := by
      rw [div_le_iff₀ hpqpos]
      have e : 2 * (Q / p) * (p * q) = 2 * Q * q := by field_simp
      rw [e]
      nlinarith
    linarith
  have h2 : MarkovMixing.spectralGap P / 2 ≤ MarkovMixing.bottleneckStar P π := le_ciInf hkey
  linarith
