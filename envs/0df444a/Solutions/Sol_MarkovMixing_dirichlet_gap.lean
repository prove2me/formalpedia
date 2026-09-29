-- Prove2me | solution 1 for MarkovMixing.dirichlet_gap
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T16:08:20.807413+00:00
-- url     : https://prove2.me/submissions/616189f1-3392-44b3-8844-8247c63bd122

import Definitions.Def_mm_spectral
import Theorems.Thm_MarkovMixing_spectral_representation
import Theorems.Thm_MarkovMixing_eigenvalue_basic
import Mathlib.Tactic

set_option maxHeartbeats 1000000

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
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    MarkovMixing.spectralGap P =
      sInf {e : ℝ | ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧
        MarkovMixing.innerPi π f f = 1 ∧ e = MarkovMixing.dirichletForm P π f} ∧
    ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧ MarkovMixing.innerPi π f f = 1 ∧
      MarkovMixing.spectralGap P = MarkovMixing.dirichletForm P π f := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hsum : ∑ x : V, π x = 1 := hπ.1.2
  obtain ⟨lam, ff, heig, horth, hspec⟩ :=
    MarkovMixing.spectral_representation P hP π hπ.1 hpos hrev
  have hcomp := completeness hspec
  have hdir : ∀ g : V → ℝ, dirichletForm P π g
      = ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam j) := by
    intro g
    rw [dirichlet_eq_inner hP hπ g, norm_eq hpos hcomp g, inner_mulVec heig hpos hcomp g,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcoef : ∀ (a : Fin (Fintype.card V) → ℝ) (k : Fin (Fintype.card V)),
      innerPi π (fun x => ∑ j, a j * ff j x) (ff k) = a k := by
    intro a k
    have e : ∀ x : V, (∑ j, a j * ff j x) * ff k x * π x
        = ∑ j, a j * (ff j x * ff k x * π x) := by
      intro x
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    show ∑ x : V, (∑ j, a j * ff j x) * ff k x * π x = a k
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_comm]
    have e2 : ∀ j, ∑ x : V, a j * (ff j x * ff k x * π x)
        = a j * (if j = k then 1 else 0) := by
      intro j
      rw [← Finset.mul_sum]
      exact congrArg _ (horth j k)
    rw [Finset.sum_congr rfl (fun j _ => e2 j),
      Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (fun b _ hb => by simp [hb])]
    simp
  -- the constant function
  set one : V → ℝ := fun _ => 1 with hone_def
  have hPone : P.mulVec one = one := by
    funext x
    show ∑ y, P x y * 1 = 1
    simpa using hP.2 x
  have hone_eig : ∀ j, innerPi π one (ff j) * (lam j - 1) = 0 := by
    intro j
    have hA : P.mulVec one = fun x => ∑ k, (innerPi π one (ff k) * lam k) * ff k x := by
      funext x
      rw [mulVec_expand heig hpos hcomp one x]
    have hL : innerPi π (P.mulVec one) (ff j) = innerPi π one (ff j) * lam j := by
      rw [hA]; exact hcoef _ j
    rw [hPone] at hL
    linear_combination -hL
  have hc1 : ∃ j, innerPi π one (ff j) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ j, innerPi π one (ff j) * ff j (Classical.arbitrary V) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
    rw [expand hpos hcomp one (Classical.arbitrary V)] at h0
    exact one_ne_zero h0
  obtain ⟨j0, hj0⟩ := hc1
  have hlam0 : lam j0 = 1 := by
    rcases mul_eq_zero.mp (hone_eig j0) with h | h
    · exact absurd h hj0
    · linarith
  set x0 : V := Classical.arbitrary V with hx0_def
  have const_inner : ∀ u v : V → ℝ, (∀ x y : V, u x = u y) → (∀ x y : V, v x = v y) →
      innerPi π u v = u x0 * v x0 := by
    intro u v hu hv
    have e : ∀ x : V, u x * v x * π x = (u x0 * v x0) * π x := by
      intro x; rw [hu x x0, hv x x0]
    show ∑ x : V, u x * v x * π x = _
    rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum, hsum, mul_one]
  have hffconst : ∀ x y : V, ff j0 x = ff j0 y := by
    have h1 : P.mulVec (ff j0) = ff j0 := by
      rw [heig j0, hlam0, one_smul]
    exact (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j0) h1
  have ha : ff j0 x0 * ff j0 x0 = 1 := by
    have := horth j0 j0
    rw [const_inner _ _ hffconst hffconst] at this
    simpa using this
  have ha0 : ff j0 x0 ≠ 0 := by
    intro h; rw [h] at ha; norm_num at ha
  have hlamne : ∀ j, j ≠ j0 → lam j ≠ 1 := by
    intro j hj hlam1
    have h1 : P.mulVec (ff j) = ff j := by rw [heig j, hlam1, one_smul]
    have hcj : ∀ x y : V, ff j x = ff j y := (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j) h1
    have hb : ff j x0 * ff j0 x0 = 0 := by
      have := horth j j0
      rw [const_inner _ _ hcj hffconst] at this
      simpa [hj] using this
    have hbb : ff j x0 * ff j x0 = 1 := by
      have := horth j j
      rw [const_inner _ _ hcj hcj] at this
      simpa using this
    have : ff j x0 = 0 := by
      rcases mul_eq_zero.mp hb with h | h
      · exact h
      · exact absurd h ha0
    rw [this] at hbb
    norm_num at hbb
  -- the second-largest eigenvalue
  have hne : (Finset.univ.erase j0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨jstar, hjs_mem, hjs⟩ := Finset.exists_max_image (Finset.univ.erase j0) lam hne
  have hjs_ne : jstar ≠ j0 := (Finset.mem_erase.mp hjs_mem).1
  have hffne : ∀ j, ff j ≠ 0 := by
    intro j h
    have := horth j j
    rw [h] at this
    simp [innerPi] at this
  have hgap : MarkovMixing.spectralGap P = 1 - lam jstar := by
    have hmem : lam jstar ∈ {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1} :=
      ⟨⟨ff jstar, hffne jstar, heig jstar⟩, hlamne jstar hjs_ne⟩
    have hbdd : ∀ r ∈ {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1}, r ≤ lam jstar := by
      rintro r ⟨⟨g, hg0, hg⟩, hr1⟩
      have hex : ∃ k, innerPi π g (ff k) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hg0
        funext x
        rw [← expand hpos hcomp g x]
        exact Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
      obtain ⟨k, hk⟩ := hex
      have hA : P.mulVec g = fun x => ∑ j, (innerPi π g (ff j) * lam j) * ff j x := by
        funext x
        rw [mulVec_expand heig hpos hcomp g x]
      have hL : innerPi π (P.mulVec g) (ff k) = innerPi π g (ff k) * lam k := by
        rw [hA]; exact hcoef _ k
      have hR : innerPi π (P.mulVec g) (ff k) = r * innerPi π g (ff k) := by
        rw [hg]
        show ∑ x : V, (r • g) x * ff k x * π x = r * ∑ x : V, g x * ff k x * π x
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply]; ring
      have hlamk : lam k = r := by
        have : innerPi π g (ff k) * lam k = innerPi π g (ff k) * r := by rw [← hL, hR]; ring
        exact mul_left_cancel₀ hk this
      have hkne : k ≠ j0 := by
        intro h; rw [h, hlam0] at hlamk; exact hr1 hlamk.symm
      rw [← hlamk]
      exact hjs k (Finset.mem_erase.mpr ⟨hkne, Finset.mem_univ k⟩)
    show 1 - MarkovMixing.lambdaTwo P = 1 - lam jstar
    rw [show MarkovMixing.lambdaTwo P = lam jstar from
      le_antisymm (csSup_le ⟨_, hmem⟩ hbdd) (le_csSup ⟨lam jstar, hbdd⟩ hmem)]
  -- the minimiser
  have hfs_exp : MarkovMixing.distExp π (ff jstar) = 0 := by
    have h1 : innerPi π (ff jstar) (ff j0) = ff j0 x0 * MarkovMixing.distExp π (ff jstar) := by
      have e : ∀ x : V, ff jstar x * ff j0 x * π x = ff j0 x0 * (ff jstar x * π x) := by
        intro x; rw [hffconst x x0]; ring
      show ∑ x : V, ff jstar x * ff j0 x * π x = _
      rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum]
      rfl
    rw [horth jstar j0] at h1
    simp [hjs_ne] at h1
    rcases h1 with h | h
    · exact absurd h ha0
    · exact h
  have hfs_norm : innerPi π (ff jstar) (ff jstar) = 1 := by simpa using horth jstar jstar
  have hfs_dir : MarkovMixing.dirichletForm P π (ff jstar) = 1 - lam jstar := by
    rw [hdir]
    rw [Finset.sum_eq_single_of_mem jstar (Finset.mem_univ jstar)
      (fun b _ hb => by rw [horth jstar b]; simp [Ne.symm hb])]
    rw [horth jstar jstar]
    simp
  have hmemS : (1 - lam jstar) ∈ {e : ℝ | ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧
      MarkovMixing.innerPi π f f = 1 ∧ e = MarkovMixing.dirichletForm P π f} :=
    ⟨ff jstar, hfs_exp, hfs_norm, hfs_dir.symm⟩
  have hlb : ∀ e ∈ {e : ℝ | ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧
      MarkovMixing.innerPi π f f = 1 ∧ e = MarkovMixing.dirichletForm P π f},
      1 - lam jstar ≤ e := by
    rintro e ⟨g, hgexp, hgnorm, rfl⟩
    have hc0 : innerPi π g (ff j0) = 0 := by
      have e1 : ∀ x : V, g x * ff j0 x * π x = ff j0 x0 * (g x * π x) := by
        intro x; rw [hffconst x x0]; ring
      have : innerPi π g (ff j0) = ff j0 x0 * MarkovMixing.distExp π g := by
        show ∑ x : V, g x * ff j0 x * π x = _
        rw [Finset.sum_congr rfl (fun x _ => e1 x), ← Finset.mul_sum]
        rfl
      rw [this, hgexp, mul_zero]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (Fintype.card V))),
        (innerPi π g (ff j)) ^ 2 * (1 - lam jstar) ≤ (innerPi π g (ff j)) ^ 2 * (1 - lam j) := by
      intro j _
      by_cases hj : j = j0
      · subst hj; rw [hc0]; simp
      · refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have := hjs j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
        linarith
    calc 1 - lam jstar = (∑ j, (innerPi π g (ff j)) ^ 2) * (1 - lam jstar) := by
          rw [← norm_eq hpos hcomp g, hgnorm, one_mul]
      _ = ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam jstar) := Finset.sum_mul _ _ _
      _ ≤ ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam j) := Finset.sum_le_sum hterm
      _ = MarkovMixing.dirichletForm P π g := (hdir g).symm
  refine ⟨?_, ff jstar, hfs_exp, hfs_norm, ?_⟩
  · rw [hgap]
    exact le_antisymm (le_csInf ⟨_, hmemS⟩ hlb) (csInf_le ⟨1 - lam jstar, hlb⟩ hmemS)
  · rw [hgap, hfs_dir]
