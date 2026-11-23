-- Prove2me | solution 1 for GlobalTheory.appellHumbert_trivial_of_nowhere_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:19.106332+00:00
-- url     : https://prove2.me/submissions/804dffe9-6599-4d4b-8dee-60872ddd1161

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_eq_zero_of_gaussian_decay
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_exists_bound_of_periodic
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_left
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_right
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_continuous_hermForm_self
import Theorems.Thm_GlobalTheory_AppellHumbertTrivial_re_hermForm_add_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {g : ℕ}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ], Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  ∀ (B : Matrix (Fin g) (Fin g) ℂ) (c : Λ → ℂ) (r : (Fin g → ℂ) → ℂ), B.IsHermitian → (∀ l, ‖c l‖ = 1) →
  Differentiable ℂ r → (∀ z, r z ≠ 0) →
  (∀ (l : Λ) z, r (z + l) = c l * Complex.exp (Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z l + Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B l l) * r z) →
  B = 0 ∧ (∀ l, c l = 1) ∧ ∀ z, r z = r 0 := by
  intro g Λ _ hΛ B c r hB hc hr hr0 hper
  have hnorm : ∀ (l : Λ) z, ‖r (z + l)‖ = Real.exp (Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z l).re +
      Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B l l).re) * ‖r z‖ := by
    intro l z
    rw [hper l z, norm_mul, norm_mul, hc, one_mul, Complex.norm_exp]
    congr 2
    simp
  have hφper : ∀ (l : Λ) z, ‖r (z + l)‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (z + l) (z + l)).re)
      = ‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
    intro l z
    rw [hnorm, _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self hB, mul_comm (Real.exp _) ‖r z‖, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hφcont : Continuous fun z => ‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) :=
    hr.continuous.norm.mul (Real.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_re.comp (_root_.GlobalTheory.AppellHumbertTrivial.continuous_hermForm_self B))))
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1
    (_root_.GlobalTheory.AppellHumbertTrivial.exists_bound_of_periodic Λ hΛ _ hφcont hφper)
  have hup : ∀ z, ‖r z‖ ≤ M * Real.exp (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
    intro z
    have h := hM _ ⟨z, rfl⟩
    rw [Real.norm_of_nonneg (by positivity)] at h
    calc ‖r z‖ = (‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re)) *
          Real.exp (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ M * Real.exp (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hψcont : Continuous fun z => (‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re))⁻¹ :=
    hφcont.inv₀ fun z => (mul_pos (norm_pos_iff.2 (hr0 z)) (Real.exp_pos _)).ne'
  obtain ⟨M', hM'⟩ := isBounded_iff_forall_norm_le.1
    (_root_.GlobalTheory.AppellHumbertTrivial.exists_bound_of_periodic Λ hΛ _ hψcont
      fun l z => congrArg (·⁻¹) (hφper l z))
  have hlow : ∀ z, ‖r z‖⁻¹ ≤ M' * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
    intro z
    have h := hM' _ ⟨z, rfl⟩
    rw [Real.norm_of_nonneg (by positivity)] at h
    calc ‖r z‖⁻¹ = (‖r z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re))⁻¹ *
          Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) := by
          rw [mul_inv, mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', mul_one]
      _ ≤ M' * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B z z).re) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  have hscale : ∀ (t : ℂ) v, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (t • v) (t • v)).re = ‖t‖ ^ 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re := by
    intro t v
    rw [_root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_left, _root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_right, ← mul_assoc]
    have ht : t * star t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [ht, Complex.re_ofReal_mul]

  have hq0 : ∀ v, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re = 0 := by
    intro v
    have hd : Differentiable ℂ fun t : ℂ => r (t • v) := hr.comp (differentiable_id.smul_const v)
    rcases lt_trichotomy (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re 0 with hneg | hzero | hpos
    · exfalso
      have h := _root_.GlobalTheory.AppellHumbertTrivial.eq_zero_of_gaussian_decay (fun t => r (t • v)) hd M
        (Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re) (mul_neg_of_pos_of_neg (by positivity) hneg)
        (fun t => by
          refine (hup (t • v)).trans_eq ?_
          rw [hscale]
          congr 2
          ring)
      exact hr0 0 (by simpa using h)
    · exact hzero
    · exfalso
      have h := _root_.GlobalTheory.AppellHumbertTrivial.eq_zero_of_gaussian_decay (fun t => (r (t • v))⁻¹)
        (hd.inv fun t => hr0 _) M' (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B v v).re)
        (by nlinarith [Real.pi_pos])
        (fun t => by
          rw [norm_inv]
          refine (hlow (t • v)).trans_eq ?_
          rw [hscale]
          congr 2
          ring)
      exact hr0 0 (by simpa using h)
  have hH : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x y = 0 := by
    intro x y
    have h1 := _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self hB x y
    have h2 := _root_.GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self hB x (Complex.I • y)
    simp only [hq0] at h1
    rw [hq0, hq0, hq0, _root_.GlobalTheory.AppellHumbertTrivial.hermForm_smul_right] at h2
    refine Complex.ext ?_ ?_
    · simp only [Complex.zero_re]
      linarith
    · simp [Complex.star_def] at h2
      simpa using h2
  have hB0 : B = 0 := by
    ext i j
    have h := hH (Pi.single i 1) (Pi.single j 1)
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm at h
    simpa using h
  have hbdd : Bornology.IsBounded (Set.range r) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa [hq0] using hup z
  have hconst : ∀ z, r z = r 0 := fun z => hr.apply_eq_apply_of_bounded hbdd z 0
  refine ⟨hB0, fun l => ?_, hconst⟩
  have h := hper l 0
  simp only [hH, hconst (0 + (l : Fin g → ℂ)), mul_zero, add_zero, Complex.exp_zero, mul_one] at h
  exact mul_right_cancel₀ (hr0 0) (h.symm.trans (one_mul _).symm)
end _root_.GlobalTheory
end GlobalTheory
