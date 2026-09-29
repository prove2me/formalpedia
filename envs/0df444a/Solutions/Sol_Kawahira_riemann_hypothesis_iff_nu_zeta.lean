-- Prove2me | solution 1 for Kawahira.riemann_hypothesis_iff_nu_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T11:43:49.212028+00:00
-- url     : https://prove2.me/submissions/edae8e76-a9e0-4b5d-8f17-14482d032ee7

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nu_at_zero_of_order
import Theorems.Thm_Kawahira_norm_one_sub_inv
import Theorems.Thm_Kawahira_nontrivial_zero_mem_strip
import Theorems.Thm_Kawahira_riemannZeta_analyticOrderAt_ne_top
import Theorems.Thm_Kawahira_indifferent_in_strip_implies_rh_and_simplicity
import Theorems.Thm_Kawahira_fixed_point_off_strip_repelling

open Complex Topology

namespace Kawahira

/-! ### Elementary facts about `ζ` and the fixed points of `ν_ζ` -/

/-- `ζ` is analytic away from its pole at `1`. -/
theorem zeta_analyticAt {a : ℂ} (ha : a ≠ 1) : AnalyticAt ℂ riemannZeta a :=
  DifferentiableOn.analyticAt
    (fun _ hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds ha)

/-- A point of the right half plane is not `0`. -/
theorem ne_zero_of_re_pos {a : ℂ} (ha : 0 < a.re) : a ≠ 0 := by
  rintro rfl; simp at ha

/-- A point with real part `< 1` is not `1`. -/
theorem ne_one_of_re_lt_one {a : ℂ} (ha : a.re < 1) : a ≠ 1 := by
  rintro rfl; simp at ha

/-- Points of the right half plane are not trivial zeros. -/
theorem not_trivial_of_re_pos {a : ℂ} (ha : 0 < a.re) (n : ℕ) : a ≠ -2 * (n + 1) := by
  intro h
  rw [h] at ha
  simp at ha
  nlinarith [ha, Nat.cast_nonneg (α := ℝ) n]

/-- At a zero of finite order, the order is a positive natural number. -/
theorem exists_order {a : ℂ} (ha1 : a ≠ 1) (hz : riemannZeta a = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ analyticOrderAt riemannZeta a = (m : ℕ∞) := by
  have hg : AnalyticAt ℂ riemannZeta a := zeta_analyticAt ha1
  have hne : analyticOrderAt riemannZeta a ≠ ⊤ := riemannZeta_analyticOrderAt_ne_top a ha1
  have hnz : analyticOrderAt riemannZeta a ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hg, hz⟩
  refine ⟨(analyticOrderAt riemannZeta a).toNat, ?_, (ENat.natCast_toNat hne).symm⟩
  rcases Nat.eq_zero_or_pos (analyticOrderAt riemannZeta a).toNat with h | h
  · exact absurd (by rw [← ENat.natCast_toNat hne, h]; rfl) hnz
  · exact h

/-- A zero of order exactly one is a simple zero, and conversely. -/
theorem analyticOrderAt_eq_one_iff {g : ℂ → ℂ} {a : ℂ} (hg : AnalyticAt ℂ g a) (h0 : g a = 0) :
    analyticOrderAt g a = 1 ↔ deriv g a ≠ 0 := by
  have hsub : (fun z => g z - g a) = g := by funext z; rw [h0, sub_zero]
  constructor
  · intro h1
    have hkey := hg.analyticOrderAt_deriv_add_one
    rw [show (fun z => g z - g a) = g from hsub, h1] at hkey
    have hd : analyticOrderAt (deriv g) a = 0 := by
      cases hd : analyticOrderAt (deriv g) a with
      | top =>
        rw [hd] at hkey
        exact absurd hkey (by simp)
      | coe n =>
        rw [hd] at hkey
        have h2 : n + 1 = 1 := by exact_mod_cast hkey
        have hn : n = 0 := by omega
        rw [hn]
        rfl
    rcases analyticOrderAt_eq_zero.mp hd with h | h
    · exact absurd hg.deriv h
    · exact h
  · intro hd
    have := hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd
    rwa [show (fun z => g z - g a) = g from hsub] at this

/-! ### Comparing the orders of `ζ` and of the completed zeta function -/

/-- `Λ` is analytic away from its two poles. -/
theorem completed_analyticAt {a : ℂ} (h0 : a ≠ 0) (h1 : a ≠ 1) :
    AnalyticAt ℂ completedRiemannZeta a := by
  refine DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 0 ∧ z ≠ 1})
    (fun z hz => (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt) ?_
  have hopen : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1} :=
    (isOpen_ne).inter (isOpen_ne)
  exact hopen.mem_nhds ⟨h0, h1⟩

/-- On the right half plane, `ζ` and `Λ` have the same vanishing order. -/
theorem analyticOrderAt_zeta_eq_completed {a : ℂ} (ha : 0 < a.re) (ha1 : a ≠ 1) :
    analyticOrderAt riemannZeta a = analyticOrderAt completedRiemannZeta a := by
  have ha0 : a ≠ 0 := ne_zero_of_re_pos ha
  have hu : AnalyticAt ℂ (fun z : ℂ => (Gammaℝ z)⁻¹) a :=
    DifferentiableOn.analyticAt (s := Set.univ)
      (fun z _ => (differentiable_Gammaℝ_inv z).differentiableWithinAt) Filter.univ_mem
  have hua : (Gammaℝ a)⁻¹ ≠ 0 := inv_ne_zero (Gammaℝ_ne_zero_of_re_pos ha)
  have heq : riemannZeta =ᶠ[𝓝 a] completedRiemannZeta * (fun z : ℂ => (Gammaℝ z)⁻¹) := by
    filter_upwards [(isOpen_ne).mem_nhds ha0] with z hz
    simpa [div_eq_mul_inv] using riemannZeta_def_of_ne_zero hz
  have hzero : analyticOrderAt (fun z : ℂ => (Gammaℝ z)⁻¹) a = 0 :=
    (analyticOrderAt_eq_zero (f := fun z : ℂ => (Gammaℝ z)⁻¹) (z₀ := a)).mpr (Or.inr hua)
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul (completed_analyticAt ha0 ha1) hu,
    hzero, add_zero]

/-- The functional equation gives the symmetry of the order of `Λ` under `z ↦ 1 - z`. -/
theorem analyticOrderAt_completed_one_sub (a : ℂ) :
    analyticOrderAt completedRiemannZeta (1 - a) = analyticOrderAt completedRiemannZeta a := by
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) a := by fun_prop
  have hg' : deriv (fun z : ℂ => 1 - z) a ≠ 0 := by
    simp
  have hcomp : (completedRiemannZeta ∘ fun z : ℂ => 1 - z) = completedRiemannZeta := by
    funext z; exact completedRiemannZeta_one_sub z
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := completedRiemannZeta)
    (g := fun z : ℂ => 1 - z) (z₀ := a) hg hg'
  rw [hcomp] at this
  exact this.symm

/-- Inside the critical strip the order of `ζ` is symmetric under `s ↦ 1 - s`. -/
theorem analyticOrderAt_zeta_one_sub {a : ℂ} (h0 : 0 < a.re) (h1 : a.re < 1) :
    analyticOrderAt riemannZeta (1 - a) = analyticOrderAt riemannZeta a := by
  have h0' : 0 < (1 - a).re := by simp; linarith
  have h1' : (1 - a).re < 1 := by simp; linarith
  rw [analyticOrderAt_zeta_eq_completed h0' (ne_one_of_re_lt_one h1'),
    analyticOrderAt_completed_one_sub a, ← analyticOrderAt_zeta_eq_completed h0
      (ne_one_of_re_lt_one h1)]

/-! ### The multiplier of `ν_ζ` at a zero -/

/-- The fixed-point data of `ν_ζ` at a zero of `ζ` of order `m`. -/
theorem nu_data {a : ℂ} {m : ℕ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) (hm : 1 ≤ m)
    (hmord : analyticOrderAt riemannZeta a = (m : ℕ∞)) :
    nuZeta a = a ∧ deriv nuZeta a = 1 - 1 / ((m : ℂ) * a) :=
  nu_at_zero_of_order riemannZeta a m ha0 hm (zeta_analyticAt ha1) hmord

/-- The classification of the multiplier `1 - 1/(m a)` by the real part of `m a`. -/
theorem norm_multiplier {a : ℂ} {m : ℕ} (hw : (m : ℂ) * a ≠ 0) :
    (‖1 - 1 / ((m : ℂ) * a)‖ = 1 ↔ (m : ℝ) * a.re = 1 / 2) ∧
      (‖1 - 1 / ((m : ℂ) * a)‖ < 1 ↔ 1 / 2 < (m : ℝ) * a.re) := by
  have h := norm_one_sub_inv ((m : ℂ) * a) hw
  have hre : ((m : ℂ) * a).re = (m : ℝ) * a.re := by simp
  rw [hre] at h
  simpa [one_div] using h

/-! ### The three conditions -/

/-- A fixed point of `ν_ζ` which is not a pole of `ν_ζ` is a zero of `ζ`. -/
theorem zero_of_fixed {a : ℂ} (ha0 : a ≠ 0)
    (hreg : riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0) (hfix : nuZeta a = a) :
    riemannZeta a = 0 := by
  rcases hreg with h | h
  · exact h
  · have : riemannZeta a / (a * deriv riemannZeta a) = 0 := by
      have := hfix
      simp only [nuZeta, nu] at this
      linear_combination -this
    rcases div_eq_zero_iff.mp this with h' | h'
    · exact h'
    · exact absurd h' (mul_ne_zero ha0 h)

/-- (a) ⟹ (b). -/
theorem rh_to_indifferent
    (hA : ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 ∧ deriv riemannZeta s ≠ 0) :
    ∀ s : ℂ, IsNontrivialZero s → IsIndifferentFixedPoint nuZeta s := by
  intro s hs
  obtain ⟨hre, hderiv⟩ := hA s hs
  obtain ⟨h0, h1⟩ := nontrivial_zero_mem_strip s hs.1 hs.2
  have hs0 : s ≠ 0 := ne_zero_of_re_pos h0
  have hs1 : s ≠ 1 := ne_one_of_re_lt_one h1
  have hord : analyticOrderAt riemannZeta s = ((1 : ℕ) : ℕ∞) := by
    have := (analyticOrderAt_eq_one_iff (zeta_analyticAt hs1) hs.1).mpr hderiv
    simpa using this
  obtain ⟨hfix, hder⟩ := nu_data hs0 hs1 (le_refl 1) hord
  refine ⟨hfix, ?_⟩
  rw [hder]
  have hw : ((1 : ℕ) : ℂ) * s ≠ 0 := by simpa using hs0
  exact (norm_multiplier hw).1.mpr (by simpa using hre)

/-- (b) ⟹ (a). -/
theorem indifferent_to_rh
    (hB : ∀ s : ℂ, IsNontrivialZero s → IsIndifferentFixedPoint nuZeta s) :
    ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 ∧ deriv riemannZeta s ≠ 0 := by
  refine indifferent_in_strip_implies_rh_and_simplicity ?_
  intro a h0 _ hreg hfix
  have ha0 : a ≠ 0 := ne_zero_of_re_pos h0
  exact hB a ⟨zero_of_fixed ha0 hreg hfix, not_trivial_of_re_pos h0⟩

/-- (b) ⟹ (c). -/
theorem indifferent_to_no_attracting
    (hB : ∀ s : ℂ, IsNontrivialZero s → IsIndifferentFixedPoint nuZeta s) :
    ∀ a : ℂ, a ≠ 0 → a ≠ 1 → (riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0) →
      ¬ IsAttractingFixedPoint nuZeta a := by
  intro a ha0 ha1 hreg hattr
  obtain ⟨hfix, hlt⟩ := hattr
  by_cases hstrip : 0 < a.re ∧ a.re < 1
  · have hzero : IsNontrivialZero a :=
      ⟨zero_of_fixed ha0 hreg hfix, not_trivial_of_re_pos hstrip.1⟩
    have := (hB a hzero).2
    rw [this] at hlt
    exact lt_irrefl 1 hlt
  · have := (fixed_point_off_strip_repelling a ha0 ha1 hreg hstrip hfix).2
    linarith

/-- If `ν_ζ` has no attracting fixed point, then at a zero `a` of `ζ` in the strip, of order `m`,
one has `m · Re a ≤ 1/2`. -/
theorem order_re_le_half
    (hC : ∀ a : ℂ, a ≠ 0 → a ≠ 1 → (riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0) →
      ¬ IsAttractingFixedPoint nuZeta a)
    {a : ℂ} {m : ℕ} (h0 : 0 < a.re) (h1 : a.re < 1) (hz : riemannZeta a = 0) (hm : 1 ≤ m)
    (hmord : analyticOrderAt riemannZeta a = (m : ℕ∞)) :
    (m : ℝ) * a.re ≤ 1 / 2 := by
  have ha0 : a ≠ 0 := ne_zero_of_re_pos h0
  have ha1 : a ≠ 1 := ne_one_of_re_lt_one h1
  obtain ⟨hfix, hder⟩ := nu_data ha0 ha1 hm hmord
  have hw : (m : ℂ) * a ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) ha0
  refine not_lt.mp fun hcon => hC a ha0 ha1 (Or.inl hz) ⟨hfix, ?_⟩
  rw [hder]
  exact (norm_multiplier hw).2.mpr hcon

/-- (c) ⟹ (a). -/
theorem no_attracting_to_rh
    (hC : ∀ a : ℂ, a ≠ 0 → a ≠ 1 → (riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0) →
      ¬ IsAttractingFixedPoint nuZeta a) :
    ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 ∧ deriv riemannZeta s ≠ 0 := by
  intro s hs
  obtain ⟨h0, h1⟩ := nontrivial_zero_mem_strip s hs.1 hs.2
  have hs1 : s ≠ 1 := ne_one_of_re_lt_one h1
  obtain ⟨m, hm, hmord⟩ := exists_order hs1 hs.1
  -- the reflected point
  have h0' : 0 < (1 - s).re := by simp; linarith
  have h1' : (1 - s).re < 1 := by simp; linarith
  have hmord' : analyticOrderAt riemannZeta (1 - s) = (m : ℕ∞) := by
    rw [analyticOrderAt_zeta_one_sub h0 h1]; exact hmord
  have hz' : riemannZeta (1 - s) = 0 := by
    refine apply_eq_zero_of_analyticOrderAt_ne_zero ?_
    rw [hmord']
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hm
  have e1 : (m : ℝ) * s.re ≤ 1 / 2 := order_re_le_half hC h0 h1 hs.1 hm hmord
  have e2 : (m : ℝ) * (1 - s).re ≤ 1 / 2 := order_re_le_half hC h0' h1' hz' hm hmord'
  have hre' : (1 - s).re = 1 - s.re := by simp
  rw [hre'] at e2
  have hmle : (m : ℝ) ≤ 1 := by nlinarith
  have hm1 : m = 1 := by
    have : (m : ℝ) ≤ (1 : ℕ) := by simpa using hmle
    have : m ≤ 1 := by exact_mod_cast this
    omega
  subst hm1
  have hre : s.re = 1 / 2 := by
    simp only [Nat.cast_one, one_mul] at e1 e2
    linarith
  refine ⟨hre, ?_⟩
  refine (analyticOrderAt_eq_one_iff (zeta_analyticAt hs1) hs.1).mp ?_
  simpa using hmord

end Kawahira

open Kawahira in
theorem solution :
    ((∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2 ∧ deriv riemannZeta s ≠ 0) ↔
        (∀ s : ℂ, IsNontrivialZero s → IsIndifferentFixedPoint nuZeta s)) ∧
      ((∀ s : ℂ, IsNontrivialZero s → IsIndifferentFixedPoint nuZeta s) ↔
        (∀ a : ℂ, a ≠ 0 → a ≠ 1 → (riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0) →
          ¬ IsAttractingFixedPoint nuZeta a)) :=
  ⟨⟨rh_to_indifferent, indifferent_to_rh⟩,
    ⟨indifferent_to_no_attracting, fun hC => rh_to_indifferent (no_attracting_to_rh hC)⟩⟩
