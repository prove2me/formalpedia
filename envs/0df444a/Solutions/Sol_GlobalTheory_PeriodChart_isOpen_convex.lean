-- Prove2me | solution 1 for GlobalTheory.PeriodChart.isOpen_convex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:17.628258+00:00
-- url     : https://prove2.me/submissions/8c01be4e-7324-4604-97bb-16cb9aeb547f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PeriodChart
section Abstract
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Abstract
section Mat
variable {g : ℕ}
variable {M : Type} [AddCommGroup M]
private lemma re_sesq_real_smul (G : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (x : Fin g → ℂ) :
    (sesq G ((r : ℂ) • x) ((r : ℂ) • x)).re = r ^ 2 * (sesq G x x).re := by
  simp only [map_smul, LinearMap.smul_apply, map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul,
    Complex.re_ofReal_mul]
  ring
private lemma anti_real_smul (W : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (x : Fin g → ℂ) :
    anti W ((r : ℂ) • x) = (r : ℂ) • anti W x := by
  rw [map_smulₛₗ, Complex.conj_ofReal]
private lemma re_sesq_convex_of_pos_def (G : Matrix (Fin g) (Fin g) ℂ) (hp : ∀ z, z ≠ 0 → 0 < (sesq G z z).re)
    (x y : Fin g → ℂ) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1) :
    (sesq G ((a : ℂ) • x + (c : ℂ) • y) ((a : ℂ) • x + (c : ℂ) • y)).re ≤
      a * (sesq G x x).re + c * (sesq G y y).re := by
  have hxy : 0 ≤ (sesq G (x - y) (x - y)).re := by
    by_cases h : x - y = 0
    · simp [h]
    · exact (hp _ h).le
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul, Complex.add_re, Complex.sub_re,
    Complex.re_ofReal_mul] at hxy ⊢
  have hc' : c = 1 - a := by linarith
  subst hc'
  nlinarith [mul_nonneg ha hc, mul_nonneg (mul_nonneg ha hc) hxy]
private lemma continuous_hermForm (G : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun p : (Fin g → ℂ) × (Fin g → ℂ) => hermForm G p.1 p.2 := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Pi.star_apply]
  refine continuous_finsetSum _ fun i _ => ?_
  refine ((continuous_apply i).comp continuous_fst).mul ?_
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_star.comp ((continuous_apply j).comp continuous_snd))
end Mat
section Period
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}
end Period
end GlobalTheory.PeriodChart
end

set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.PeriodChart
theorem _root_.solution {m : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (hp : ∀ z, z ≠ 0 → 0 < (sesq G z z).re)
    (Z : (Fin m → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ) :
    IsOpen {b | ∀ z, z ≠ 0 → (sesq G (anti (Z b) z) (anti (Z b) z)).re < (sesq G z z).re} ∧
    Convex ℝ {b | ∀ z, z ≠ 0 → (sesq G (anti (Z b) z) (anti (Z b) z)).re < (sesq G z z).re} := by
  have hA : ∀ (W : Matrix (Fin g) (Fin g) ℂ) z, anti W z = W *ᵥ star z := fun _ _ => rfl
  have hS : ∀ (G' : Matrix (Fin g) (Fin g) ℂ) z w, sesq G' z w = hermForm G' z w := fun _ _ _ => rfl
  constructor
  · rw [isOpen_iff_mem_nhds]
    intro b0 hb0
    have hZ : Continuous Z := LinearMap.continuous_of_finiteDimensional Z
    have hcont : Continuous fun p : (Fin m → ℂ) × (Fin g → ℂ) =>
        (sesq G p.2 p.2).re - (sesq G (anti (Z p.1) p.2) (anti (Z p.1) p.2)).re := by
      have hv : Continuous fun p : (Fin m → ℂ) × (Fin g → ℂ) => Z p.1 *ᵥ star p.2 :=
        (hZ.comp continuous_fst).matrix_mulVec continuous_snd.star
      exact (Complex.continuous_re.comp ((continuous_hermForm G).comp (continuous_snd.prodMk continuous_snd))).sub
        (Complex.continuous_re.comp ((continuous_hermForm G).comp (hv.prodMk hv)))
    have hev : ∀ᶠ b in nhds b0, ∀ z ∈ Metric.sphere (0 : Fin g → ℂ) 1,
        0 < (sesq G z z).re - (sesq G (anti (Z b) z) (anti (Z b) z)).re := by
      refine (isCompact_sphere (0 : Fin g → ℂ) 1).eventually_forall_of_forall_eventually ?_
      intro z hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hz
      exact hcont.continuousAt.eventually (eventually_gt_nhds (sub_pos.mpr (hb0 z hz0)))
    filter_upwards [hev] with b hb
    intro z hz
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hu : ((‖z‖⁻¹ : ℝ) : ℂ) • z ∈ Metric.sphere (0 : Fin g → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul]
      simp [hr.ne']
    have h1 := hb _ hu
    rw [anti_real_smul, re_sesq_real_smul, re_sesq_real_smul, ← mul_sub] at h1
    have hpos : 0 < (‖z‖⁻¹) ^ 2 := by positivity
    exact sub_pos.mp (pos_of_mul_pos_right h1 hpos.le)
  · intro b1 hb1 b2 hb2 a c ha hc hac z hz
    have hW : anti (Z (a • b1 + c • b2)) z = (a : ℂ) • anti (Z b1) z + (c : ℂ) • anti (Z b2) z := by
      rw [map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hA, hA, hA, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.smul_mulVec, Complex.coe_smul, Complex.coe_smul]
    have e1 := hb1 z hz
    have e2 := hb2 z hz
    show (sesq G (anti (Z (a • b1 + c • b2)) z) (anti (Z (a • b1 + c • b2)) z)).re < (sesq G z z).re
    rw [hW]
    refine lt_of_le_of_lt (re_sesq_convex_of_pos_def G hp _ _ a c ha hc hac) ?_
    rcases ha.eq_or_lt with h0 | h0
    · subst h0
      have : c = 1 := by linarith
      subst this
      linarith
    · have hQ : a * (sesq G z z).re + c * (sesq G z z).re = (sesq G z z).re := by
        rw [← add_mul, hac, one_mul]
      linarith [mul_lt_mul_of_pos_left e1 h0, mul_le_mul_of_nonneg_left e2.le hc]
end GlobalTheory.PeriodChart
