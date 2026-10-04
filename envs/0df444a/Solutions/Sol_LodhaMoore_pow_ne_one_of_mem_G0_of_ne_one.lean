-- Prove2me | solution 1 for LodhaMoore.pow_ne_one_of_mem_G0_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:29:31.813533+00:00
-- url     : https://prove2.me/submissions/226ad5b4-7413-4894-8d49-477acd3cfee2

import Mathlib
import Definitions.Def_LodhaMoore

set_option autoImplicit false

namespace LodhaMooreAux96133d2e
open LodhaMoore

/-- Elements fixing `∞` and acting on `ℝ` as a strictly increasing map. -/
def P (e : OnePoint ℝ ≃ₜ OnePoint ℝ) : Prop :=
  e OnePoint.infty = OnePoint.infty ∧
  ∀ x y : ℝ, x < y → ∃ u v : ℝ, e (x : OnePoint ℝ) = u ∧ e (y : OnePoint ℝ) = v ∧ u < v

lemma P_real {e : OnePoint ℝ ≃ₜ OnePoint ℝ} (he : P e) (x : ℝ) :
    ∃ u : ℝ, e (x : OnePoint ℝ) = u := by
  obtain ⟨u, v, h1, -, -⟩ := he.2 x (x + 1) (by linarith)
  exact ⟨u, h1⟩

def H : Subgroup (OnePoint ℝ ≃ₜ OnePoint ℝ) where
  carrier := {e | P e}
  one_mem' := ⟨rfl, fun x y hxy => ⟨x, y, rfl, rfl, hxy⟩⟩
  mul_mem' := by
    intro e f he hf
    refine ⟨?_, ?_⟩
    · show e (f _) = _
      rw [hf.1, he.1]
    · intro x y hxy
      obtain ⟨u, v, hu, hv, huv⟩ := hf.2 x y hxy
      obtain ⟨u', v', hu', hv', huv'⟩ := he.2 u v huv
      refine ⟨u', v', ?_, ?_, huv'⟩
      · show e (f _) = _
        rw [hu, hu']
      · show e (f _) = _
        rw [hv, hv']
  inv_mem' := by
    intro e he
    have hinf : e.symm OnePoint.infty = OnePoint.infty := by
      rw [Homeomorph.symm_apply_eq]; exact he.1.symm
    have hreal : ∀ x : ℝ, ∃ u : ℝ, e.symm (x : OnePoint ℝ) = u := by
      intro x
      have hne : e.symm (x : OnePoint ℝ) ≠ OnePoint.infty := by
        intro h
        rw [Homeomorph.symm_apply_eq, he.1] at h
        exact OnePoint.coe_ne_infty x h
      obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.mp hne
      exact ⟨u, hu.symm⟩
    refine ⟨?_, ?_⟩
    · show e.symm _ = _
      exact hinf
    · intro x y hxy
      obtain ⟨u, hu⟩ := hreal x
      obtain ⟨v, hv⟩ := hreal y
      refine ⟨u, v, hu, hv, ?_⟩
      have hxu : e (u : OnePoint ℝ) = x := by rw [← hu]; simp
      have hyv : e (v : OnePoint ℝ) = y := by rw [← hv]; simp
      rcases lt_trichotomy u v with h | h | h
      · exact h
      · subst h
        rw [hxu] at hyv
        exact absurd (OnePoint.coe_injective hyv) (ne_of_lt hxy)
      · obtain ⟨v', u', hv', hu', hlt⟩ := he.2 v u h
        rw [hyv] at hv'
        rw [hxu] at hu'
        have e1 := OnePoint.coe_injective hv'
        have e2 := OnePoint.coe_injective hu'
        subst e1; subst e2
        exact absurd hlt (not_lt.mpr hxy.le)

lemma ofReal_mem (f : ℝ → ℝ) (hs : Function.Surjective f) (hm : StrictMono f) :
    ofReal f ∈ H := by
  unfold ofReal
  split_ifs with h
  · have spec := h.choose_spec
    refine ⟨?_, ?_⟩
    · by_contra hne
      obtain ⟨r, hr⟩ := OnePoint.ne_infty_iff_exists.mp hne
      obtain ⟨t, ht⟩ := hs r
      have : h.choose (t : OnePoint ℝ) = h.choose OnePoint.infty := by
        rw [spec, ht, hr]
      exact OnePoint.coe_ne_infty t (h.choose.injective this)
    · intro x y hxy
      exact ⟨f x, f y, spec x, spec y, hm hxy⟩
  · exact H.one_mem

lemma aFun_mem : a ∈ H := by
  apply ofReal_mem
  · intro r; exact ⟨r - 1, by simp [aFun]⟩
  · intro x y hxy; simp only [aFun]; linarith

lemma L2 (t : ℝ) (h0 : 0 < t) (h1 : t ≤ 1 / 2) : 0 < t / (1 - t) ∧ t / (1 - t) ≤ 1 := by
  constructor
  · apply div_pos h0; linarith
  · rw [div_le_one (by linarith)]; linarith

lemma L3 (t : ℝ) (h0 : 1 / 2 < t) (h1 : t ≤ 1) : 1 < 3 - 1 / t ∧ 3 - 1 / t ≤ 2 := by
  have ht : 0 < t := by linarith
  constructor
  · have : 1 / t < 2 := by rw [div_lt_iff₀ ht]; linarith
    linarith
  · have : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
    linarith

lemma M2 (x y : ℝ) (h0 : 0 < x) (hxy : x < y) (h1 : y ≤ 1 / 2) :
    x / (1 - x) < y / (1 - y) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith

lemma M3 (x y : ℝ) (h0 : 1 / 2 < x) (hxy : x < y) :
    3 - 1 / x < 3 - 1 / y := by
  have : 1 / y < 1 / x := one_div_lt_one_div_of_lt (by linarith) hxy
  linarith

lemma bFun_mono : StrictMono bFun := by
  intro x y hxy
  unfold bFun
  split_ifs <;> (try push Not at *) <;>
  first
  | linarith
  | exact M2 x y (by linarith) hxy (by linarith)
  | exact M3 x y (by linarith) hxy
  | (have := L2 y (by linarith) (by linarith); linarith)
  | (have := L3 y (by linarith) (by linarith); linarith)
  | (have := L2 x (by linarith) (by linarith); have := L3 y (by linarith) (by linarith); linarith)
  | (have := L2 x (by linarith) (by linarith); linarith)
  | (have := L3 x (by linarith) (by linarith); linarith)

lemma bFun_surj : Function.Surjective bFun := by
  intro r
  rcases le_or_gt r 0 with h0 | h0
  · exact ⟨r, by simp [bFun, h0]⟩
  rcases le_or_gt r 1 with h1 | h1
  · refine ⟨r / (1 + r), ?_⟩
    have hp : 0 < r / (1 + r) := div_pos h0 (by linarith)
    have hq : r / (1 + r) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    unfold bFun
    rw [if_neg (by linarith), if_pos hq]
    have : (1 : ℝ) + r ≠ 0 := by linarith
    field_simp
    ring
  rcases le_or_gt r 2 with h2 | h2
  · refine ⟨1 / (3 - r), ?_⟩
    have hp : 1 / 2 < 1 / (3 - r) := by
      apply one_div_lt_one_div_of_lt (by linarith); linarith
    have hq : 1 / (3 - r) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    unfold bFun
    rw [if_neg (by linarith), if_neg (by linarith), if_pos hq]
    have : (3 : ℝ) - r ≠ 0 := by linarith
    field_simp
    ring
  · refine ⟨r - 1, ?_⟩
    unfold bFun
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    ring

lemma bFun_mem : b ∈ H := ofReal_mem _ bFun_surj bFun_mono

lemma C1 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ 2 * t / (1 + t) ∧ 2 * t / (1 + t) ≤ 1 := by
  constructor
  · positivity
  · rw [div_le_one (by linarith)]; linarith

lemma cFun_mono : StrictMono cFun := by
  intro x y hxy
  unfold cFun
  split_ifs with hx hy hy
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · have := C1 x hx.1 hx.2
    have : 1 < y := by
      by_contra hc; push Not at hc; exact hy ⟨by linarith, hc⟩
    linarith
  · have := C1 y hy.1 hy.2
    have : x < 0 := by
      by_contra hc; push Not at hc; exact hx ⟨hc, by linarith⟩
    linarith
  · exact hxy

lemma cFun_surj : Function.Surjective cFun := by
  intro r
  by_cases hr : 0 ≤ r ∧ r ≤ 1
  · refine ⟨r / (2 - r), ?_⟩
    have hp : 0 ≤ r / (2 - r) := div_nonneg hr.1 (by linarith)
    have hq : r / (2 - r) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    unfold cFun
    rw [if_pos ⟨hp, hq⟩]
    have : (2 : ℝ) - r ≠ 0 := by linarith
    field_simp
    ring
  · exact ⟨r, by simp only [cFun]; rw [if_neg hr]⟩

lemma cFun_mem : c ∈ H := ofReal_mem _ cFun_surj cFun_mono

lemma G0_le_H : G0 ≤ H := by
  unfold G0
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact aFun_mem
  · exact bFun_mem
  · exact cFun_mem

lemma key (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (hg : g ∈ H) (x u : ℝ)
    (hgx : g (x : OnePoint ℝ) = u) (hxu : x < u) :
    ∀ k : ℕ, ∃ w : ℝ, (g ^ (k + 1)) (x : OnePoint ℝ) = w ∧ x < w := by
  intro k
  induction k with
  | zero => exact ⟨u, by rw [zero_add, pow_one]; exact hgx, hxu⟩
  | succ k ih =>
    obtain ⟨w, hw, hxw⟩ := ih
    have hk : g ^ (k + 1) ∈ H := H.pow_mem hg _
    obtain ⟨w1, w2, h1, h2, h12⟩ := hk.2 x u hxu
    rw [hw] at h1
    have := OnePoint.coe_injective h1
    subst this
    refine ⟨w2, ?_, by linarith⟩
    rw [pow_succ, Homeomorph.mul_apply, hgx, h2]

lemma no_torsion (g : OnePoint ℝ ≃ₜ OnePoint ℝ) (hg : g ∈ H) (x u : ℝ)
    (hgx : g (x : OnePoint ℝ) = u) (hxu : x < u) (n : ℕ) (hn : 0 < n) : g ^ n ≠ 1 := by
  intro h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨w, hw, hxw⟩ := key g hg x u hgx hxu k
  rw [h, Homeomorph.one_apply] at hw
  have := OnePoint.coe_injective hw
  linarith

end LodhaMooreAux96133d2e

open LodhaMoore in
theorem solution : ∀ g ∈ G0, g ≠ 1 → ∀ n : ℕ, 0 < n → g ^ n ≠ 1 := by
  intro g hg hne n hn
  have hH : g ∈ LodhaMooreAux96133d2e.H := LodhaMooreAux96133d2e.G0_le_H hg
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ z := by
    by_contra hc
    push Not at hc
    exact hne (Homeomorph.ext hc)
  have hzi : z ≠ OnePoint.infty := by
    rintro rfl; exact hz hH.1
  obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hzi
  obtain ⟨u, hu⟩ := LodhaMooreAux96133d2e.P_real hH x
  have hux : u ≠ x := by
    rintro rfl; exact hz hu
  rcases lt_or_gt_of_ne hux with h | h
  · have hinv : g⁻¹ ∈ LodhaMooreAux96133d2e.H := LodhaMooreAux96133d2e.H.inv_mem hH
    have hgi : g⁻¹ (u : OnePoint ℝ) = x := by
      rw [Homeomorph.inv_apply, Homeomorph.symm_apply_eq, hu]
    intro hpow
    apply LodhaMooreAux96133d2e.no_torsion g⁻¹ hinv u x hgi h n hn
    rw [inv_pow, hpow, inv_one]
  · exact LodhaMooreAux96133d2e.no_torsion g hH x u hu h n hn
