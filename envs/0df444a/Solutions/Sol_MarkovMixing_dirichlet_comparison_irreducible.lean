-- Prove2me | solution 1 for MarkovMixing.dirichlet_comparison_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T17:26:16.173403+00:00
-- url     : https://prove2.me/submissions/ec5dab43-078d-47da-810f-1beab2284ffa

import Definitions.Def_mm_spectral
import Theorems.Thm_MarkovMixing_dirichlet_gap
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open scoped BigOperators
open MarkovMixing

namespace DirichletGap

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
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

lemma innerPi_comm (π g h : V → ℝ) : innerPi π g h = innerPi π h g :=
  Finset.sum_congr rfl fun x _ => by ring

lemma dirichlet_eq_inner {P : Matrix V V ℝ} {π : V → ℝ} (hP : IsStochastic P)
    (hπ : IsStationary P π) (g : V → ℝ) :
    dirichletForm P π g = innerPi π g g - innerPi π g (P.mulVec g) := by
  have hrow : ∀ x, ∑ y, P x y = 1 := hP.2
  have hcol : ∀ y, ∑ x, π x * P x y = π y := fun y => congrFun hπ.2 y
  have A : ∑ x, ∑ y, (g x) ^ 2 * (π x * P x y) = ∑ x : V, g x * g x * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, hrow x, mul_one]
    ring
  have B : ∑ x : V, ∑ y : V, (g y) ^ 2 * (π x * P x y) = ∑ x : V, g x * g x * π x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, hcol y]
    ring
  have C : ∑ x : V, ∑ y : V, (g x * g y) * (π x * P x y)
      = ∑ x : V, g x * (P.mulVec g) x * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (P.mulVec g) x = ∑ y, P x y * g y from rfl, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hall : ∑ x : V, ∑ y : V, (g x - g y) ^ 2 * (π x * P x y)
      = (∑ x : V, ∑ y : V, (g x) ^ 2 * (π x * P x y))
        + (∑ x : V, ∑ y : V, (g y) ^ 2 * (π x * P x y))
        - 2 * ∑ x : V, ∑ y : V, (g x * g y) * (π x * P x y) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  show 2⁻¹ * ∑ x : V, ∑ y : V, (g x - g y) ^ 2 * (π x * P x y) = _
  rw [hall, A, B, C]
  show _ = (∑ x : V, g x * g x * π x) - ∑ x : V, g x * (P.mulVec g) x * π x
  ring

section Spectral

variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

lemma completeness
    (hspec : ∀ (t : ℕ) (x y : V), (P ^ t) x y / π y = ∑ j, ff j x * ff j y * lam j ^ t)
    (x y : V) : ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y := by
  have h := hspec 0 x y
  simpa [Matrix.one_apply] using h.symm

lemma expand (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) : ∑ j, innerPi π g (ff j) * ff j x = g x := by
  have e1 : ∀ j, innerPi π g (ff j) * ff j x = ∑ y : V, g y * π y * (ff j y * ff j x) := by
    intro j
    show (∑ y : V, g y * ff j y * π y) * ff j x = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_comm]
  have e2 : ∀ y : V, ∑ j, g y * π y * (ff j y * ff j x)
      = g y * π y * ((if y = x then 1 else 0) / π x) := by
    intro y
    rw [← Finset.mul_sum, hcomp y x]
  rw [Finset.sum_congr rfl (fun y _ => e2 y),
    Finset.sum_eq_single_of_mem x (Finset.mem_univ x) (fun b _ hb => by simp [hb])]
  have hx := (hpos x).ne'
  field_simp
  simp

lemma norm_eq (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) : innerPi π g g = ∑ j, (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * g x * π x
      = ∑ j, innerPi π g (ff j) * (g x * ff j x * π x) := by
    intro x
    have : ∀ j, innerPi π g (ff j) * (g x * ff j x * π x)
        = (innerPi π g (ff j) * ff j x) * (g x * π x) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, expand hpos hcomp g x]
    ring
  show ∑ x : V, g x * g x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * innerPi π g (ff j) = _
  ring

lemma mulVec_expand (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) :
    (P.mulVec g) x = ∑ j, innerPi π g (ff j) * lam j * ff j x := by
  have e1 : ∀ y : V, P x y * g y = ∑ j, innerPi π g (ff j) * (P x y * ff j y) := by
    intro y
    have : ∀ j, innerPi π g (ff j) * (P x y * ff j y)
        = (innerPi π g (ff j) * ff j y) * P x y := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, expand hpos hcomp g y]
    ring
  show ∑ y : V, P x y * g y = _
  rw [Finset.sum_congr rfl (fun y _ => e1 y), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ y : V, P x y * ff j y = lam j * ff j x := by
    have := congrFun (heig j) x
    simpa [Matrix.mulVec, dotProduct] using this
  rw [this]
  ring

lemma inner_mulVec (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) :
    innerPi π g (P.mulVec g) = ∑ j, lam j * (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * (P.mulVec g) x * π x
      = ∑ j, (innerPi π g (ff j) * lam j) * (g x * ff j x * π x) := by
    intro x
    rw [mulVec_expand heig hpos hcomp g x, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∑ x : V, g x * (P.mulVec g) x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * lam j * innerPi π g (ff j) = _
  ring

end Spectral

end DirichletGap

open DirichletGap

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P P' : Matrix V V ℝ)
    (hP : MarkovMixing.IsStochastic P) (hP' : MarkovMixing.IsStochastic P')
    (hirr : MarkovMixing.Irreducible P) (hirr' : MarkovMixing.Irreducible P')
    (π π' : V → ℝ) (hπ : MarkovMixing.IsStationary P π) (hπ' : MarkovMixing.IsStationary P' π')
    (hrev : MarkovMixing.DetailedBalance P π) (hrev' : MarkovMixing.DetailedBalance P' π')
    (hpos' : ∀ x : V, 0 < π' x)
    (B : ℝ) (hB : 0 < B)
    (hcomp : ∀ f : V → ℝ,
      MarkovMixing.dirichletForm P' π' f ≤ B * MarkovMixing.dirichletForm P π f) :
    MarkovMixing.spectralGap P' ≤ (⨆ x : V, π x / π' x) * B * MarkovMixing.spectralGap P := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hsum : ∑ x, π x = 1 := hπ.1.2
  have hsum' : ∑ x, π' x = 1 := hπ'.1.2
  have hdirnn : ∀ (Q : Matrix V V ℝ) (ρ : V → ℝ), MarkovMixing.IsStochastic Q →
      (∀ x, 0 ≤ ρ x) → ∀ g : V → ℝ, 0 ≤ MarkovMixing.dirichletForm Q ρ g := by
    intro Q ρ hQ hρ g
    show (0:ℝ) ≤ 2⁻¹ * ∑ x, ∑ y, (g x - g y) ^ 2 * (ρ x * Q x y)
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_)
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (hρ x) (hQ.1 x y))
  obtain ⟨-, f, hfexp, hfnorm, hfdir⟩ := MarkovMixing.dirichlet_gap hV P hP hirr π hπ hrev
  obtain ⟨hgap', -⟩ := MarkovMixing.dirichlet_gap hV P' hP' hirr' π' hπ' hrev'
  set m' : ℝ := MarkovMixing.distExp π' f with hm'_def
  set s2 : ℝ := MarkovMixing.distVar π' f with hs2_def
  have hs2form : s2 = ∑ x, (f x - m') ^ 2 * π' x := rfl
  have hs2nn : 0 ≤ s2 := by
    rw [hs2form]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (hπ'.1.1 x)
  have hs2pos : 0 < s2 := by
    rcases hs2nn.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 : ∀ y ∈ (Finset.univ : Finset V), (f y - m') ^ 2 * π' y = 0 := by
        refine (Finset.sum_eq_zero_iff_of_nonneg
          (fun y _ => mul_nonneg (sq_nonneg _) (hπ'.1.1 y))).mp ?_
        rw [← hs2form, ← h]
      have hz : ∀ x : V, f x = m' := by
        intro x
        rcases mul_eq_zero.mp (h1 x (Finset.mem_univ x)) with h2 | h2
        · have h3 : f x - m' = 0 := by
            have := sq_eq_zero_iff.mp h2
            exact this
          linarith
        · exact absurd h2 (hpos' x).ne'
      have hm0 : m' = 0 := by
        have h4 : MarkovMixing.distExp π f = m' := by
          show ∑ x, f x * π x = m'
          rw [Finset.sum_congr rfl (fun x _ => by rw [hz x]), ← Finset.mul_sum, hsum, mul_one]
        rw [hfexp] at h4
        exact h4.symm
      have h5 : MarkovMixing.innerPi π f f = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [hz x, hm0]
        ring
      rw [hfnorm] at h5
      norm_num at h5
  set σ' : ℝ := Real.sqrt s2 with hσ'_def
  have hσ'pos : 0 < σ' := Real.sqrt_pos.mpr hs2pos
  have hσ'sq : σ' ^ 2 = s2 := Real.sq_sqrt hs2nn
  set g : V → ℝ := fun x => (f x - m') / σ' with hg_def
  have hgexp : MarkovMixing.distExp π' g = 0 := by
    show ∑ x, (f x - m') / σ' * π' x = 0
    have e : ∀ x : V, (f x - m') / σ' * π' x = (f x * π' x - m' * π' x) / σ' :=
      fun x => by field_simp
    rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hsum', mul_one]
    have : ∑ x, f x * π' x = m' := rfl
    rw [this, sub_self, zero_div]
  have hgnorm : MarkovMixing.innerPi π' g g = 1 := by
    show ∑ x, (f x - m') / σ' * ((f x - m') / σ') * π' x = 1
    have e : ∀ x : V, (f x - m') / σ' * ((f x - m') / σ') * π' x
        = ((f x - m') ^ 2 * π' x) / σ' ^ 2 := fun x => by field_simp
    rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.sum_div, ← hs2form, hσ'sq,
      div_self hs2pos.ne']
  have hgdir : MarkovMixing.dirichletForm P' π' g
      = MarkovMixing.dirichletForm P' π' f / s2 := by
    show 2⁻¹ * ∑ x, ∑ y, ((f x - m') / σ' - (f y - m') / σ') ^ 2 * (π' x * P' x y)
      = (2⁻¹ * ∑ x, ∑ y, (f x - f y) ^ 2 * (π' x * P' x y)) / s2
    have e : ∀ x y : V, ((f x - m') / σ' - (f y - m') / σ') ^ 2 * (π' x * P' x y)
        = ((f x - f y) ^ 2 * (π' x * P' x y)) / s2 := by
      intro x y
      rw [← hσ'sq]
      have hσ0 : σ' ≠ 0 := hσ'pos.ne'
      field_simp
      ring
    have e2 : ∀ x : V, ∑ y, ((f x - m') / σ' - (f y - m') / σ') ^ 2 * (π' x * P' x y)
        = (∑ y, (f x - f y) ^ 2 * (π' x * P' x y)) / s2 := by
      intro x
      rw [Finset.sum_congr rfl (fun y _ => e x y), ← Finset.sum_div]
    rw [Finset.sum_congr rfl (fun x _ => e2 x), ← Finset.sum_div]
    ring
  have hbdd' : BddBelow {e : ℝ | ∃ h : V → ℝ, MarkovMixing.distExp π' h = 0 ∧
      MarkovMixing.innerPi π' h h = 1 ∧ e = MarkovMixing.dirichletForm P' π' h} := by
    refine ⟨0, ?_⟩
    rintro e ⟨h, -, -, rfl⟩
    exact hdirnn P' π' hP' (fun x => (hpos' x).le) h
  have hgapP' : MarkovMixing.spectralGap P' ≤ MarkovMixing.dirichletForm P' π' f / s2 := by
    rw [hgap']
    exact csInf_le hbdd' ⟨g, hgexp, hgnorm, hgdir.symm⟩
  have hγnn : 0 ≤ MarkovMixing.spectralGap P := by
    rw [hfdir]
    exact hdirnn P π hP (fun x => (hpos x).le) f
  have hcompf : MarkovMixing.dirichletForm P' π' f ≤ B * MarkovMixing.spectralGap P := by
    rw [hfdir]
    exact hcomp f
  set c : ℝ := ⨆ x : V, π x / π' x with hc_def
  have hcb : BddAbove (Set.range fun z : V => π z / π' z) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hcle : ∀ x : V, π x / π' x ≤ c := fun x => le_ciSup hcb x
  have hkey : 1 ≤ c * s2 := by
    have h1 : ∑ x, (f x - m') ^ 2 * π x = 1 + m' ^ 2 := by
      have e : ∀ x : V, (f x - m') ^ 2 * π x
          = f x * f x * π x - 2 * m' * (f x * π x) + m' ^ 2 * π x := fun x => by ring
      rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_one]
      have h2 : ∑ x, f x * f x * π x = 1 := hfnorm
      have h3 : ∑ x, f x * π x = 0 := hfexp
      rw [h2, h3]
      ring
    have h2 : ∑ x, (f x - m') ^ 2 * π x ≤ c * ∑ x, (f x - m') ^ 2 * π' x := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      have h3 : π x ≤ c * π' x := by
        have h4 := hcle x
        rw [div_le_iff₀ (hpos' x)] at h4
        exact h4
      nlinarith [sq_nonneg (f x - m')]
    rw [h1, ← hs2form] at h2
    nlinarith [sq_nonneg m']
  calc MarkovMixing.spectralGap P' ≤ MarkovMixing.dirichletForm P' π' f / s2 := hgapP'
    _ ≤ (B * MarkovMixing.spectralGap P) / s2 := by gcongr
    _ ≤ c * B * MarkovMixing.spectralGap P := by
        rw [div_le_iff₀ hs2pos]
        nlinarith [mul_nonneg (mul_nonneg hB.le hγnn) (sub_nonneg.mpr hkey)]
