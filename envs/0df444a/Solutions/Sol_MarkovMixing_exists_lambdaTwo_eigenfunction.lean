-- Prove2me | solution 1 for MarkovMixing.exists_lambdaTwo_eigenfunction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:28.778927+00:00
-- url     : https://prove2.me/submissions/1c3f4fd2-d117-482d-9a70-a9ec0b728542

import Mathlib
import Definitions.Def_mm_spectral
import Theorems.Thm_MarkovMixing_spectral_completeness
import Theorems.Thm_MarkovMixing_dirichletForm_eq_innerPi_sub
import Theorems.Thm_MarkovMixing_eigenvalue_basic
import Theorems.Thm_MarkovMixing_eigenbasis_expand
import Theorems.Thm_MarkovMixing_innerPi_mulVec_eq_sum
import Theorems.Thm_MarkovMixing_mulVec_eq_sum_eigen
import Theorems.Thm_MarkovMixing_innerPi_self_eq_sum_sq
import Theorems.Thm_MarkovMixing_stationary_pos_of_irreducible
import Theorems.Thm_MarkovMixing_spectral_representation

-- carved verbatim out of submission cbb05a5c-f0c1-49a4-815e-fb54ebb129bc, lines 1837-2012

section
set_option autoImplicit false
open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    ∃ g : V → ℝ, MarkovMixing.innerPi π g g = 1 ∧ MarkovMixing.distExp π g = 0 ∧
      P.mulVec g = (MarkovMixing.lambdaTwo P) • g := by
  classical
  have hpos := MarkovMixing.stationary_pos_of_irreducible hirr hπ hP
  have hsum : ∑ x : V, π x = 1 := hπ.1.2
  obtain ⟨lam, ff, heig, horth, hspec⟩ :=
    MarkovMixing.spectral_representation P hP π hπ.1 hpos hrev
  have hcomp := MarkovMixing.spectral_completeness hspec
  have hdir : ∀ g : V → ℝ, dirichletForm P π g
      = ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam j) := by
    intro g
    rw [MarkovMixing.dirichletForm_eq_innerPi_sub hP hπ g, MarkovMixing.innerPi_self_eq_sum_sq hpos hcomp g, MarkovMixing.innerPi_mulVec_eq_sum heig hpos hcomp g,
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
      rw [MarkovMixing.mulVec_eq_sum_eigen heig hpos hcomp one x]
    have hL : innerPi π (P.mulVec one) (ff j) = innerPi π one (ff j) * lam j := by
      rw [hA]; exact hcoef _ j
    rw [hPone] at hL
    linear_combination -hL
  have hc1 : ∃ j, innerPi π one (ff j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∑ j, innerPi π one (ff j) * ff j (Classical.arbitrary V) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
    rw [MarkovMixing.eigenbasis_expand hpos hcomp one (Classical.arbitrary V)] at h0
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
        push Not at hcon
        apply hg0
        funext x
        rw [← MarkovMixing.eigenbasis_expand hpos hcomp g x]
        exact Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
      obtain ⟨k, hk⟩ := hex
      have hA : P.mulVec g = fun x => ∑ j, (innerPi π g (ff j) * lam j) * ff j x := by
        funext x
        rw [MarkovMixing.mulVec_eq_sum_eigen heig hpos hcomp g x]
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
  refine ⟨ff jstar, hfs_norm, hfs_exp, ?_⟩
  have : MarkovMixing.lambdaTwo P = lam jstar := by
    have h1 : MarkovMixing.spectralGap P = 1 - MarkovMixing.lambdaTwo P := rfl
    rw [h1] at hgap
    linarith
  rw [this]
  exact heig jstar

end
