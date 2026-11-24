-- Prove2me | solution 1 for GlobalTheory.pureType_vector_spans_quadratic_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:39.464842+00:00
-- url     : https://prove2.me/submissions/6ff466f3-d1b4-4cb1-9c76-136c53afe17d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_PureTypeVectorSpansQuadraticLattice
import Theorems.Thm_GlobalTheory_PureTypeVector_hermForm_smul_smul
import Theorems.Thm_GlobalTheory_PureTypeVector_hermForm_self_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open scoped CategoryTheory.Obj
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty Pe → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) →
  (∀ x y, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe x) (Pe y)).im = D.EF x y) →
  ∀ (ρ : ℂ) (a : D.La), ρ ^ 2 = -(H.d : ℂ) → (∀ i, ty i (H.rt : E) ≠ ρ → Pe a i = 0) →
  (∀ m n : ℤ, ((m : ℂ) + n * ((1 + Complex.I * Real.sqrt H.d) / 2)) • Pe a ∈ Pe.range) ∧
  ∀ z w : ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z • Pe a) (w • Pe a) = ((D.EF (H.w0 • a) a).natAbs : ℂ) * (2 * z * starRingEnd ℂ w / Real.sqrt H.d) := by
  intro E _ _ _ H D g ty Pe Hm hP hH hpos hE ρ a hρ hsupp
  have hw0 : ∀ i, Pe (H.w0 • a) i = (1 + ρ) / 2 * Pe a i := by
    intro i
    rw [hP.1 H.w0 a i]
    by_cases hi : ty i (H.rt : E) = ρ
    · have h2 : (2 : ℂ) * ty i (H.w0 : E) = 1 + ty i (H.rt : E) := by
        have := congrArg (fun x : 𝓞 E => ty i (x : E)) H.two_weight_eq_one_add_root
        simp only [map_mul, map_add, map_one, RingOfIntegers.coe_eq_algebraMap, map_ofNat] at this
        linear_combination this
      rw [hi] at h2
      have h3 : ty i (H.w0 : E) = (1 + ρ) / 2 := by linear_combination h2 / 2
      rw [h3]
    · rw [hsupp i hi]
      simp
  have hw0' : Pe (H.w0 • a) = ((1 + ρ) / 2) • Pe a := funext fun i => by simp [hw0 i]
  have hsqd : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = H.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hsq : ρ = Complex.I * Real.sqrt H.d ∨ ρ = -(Complex.I * Real.sqrt H.d) := by
    have hprod : (ρ - Complex.I * Real.sqrt H.d) * (ρ + Complex.I * Real.sqrt H.d) = 0 := by
      linear_combination hρ + hsqd - ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 * Complex.I_sq
    rcases mul_eq_zero.1 hprod with h | h
    · left
      linear_combination h
    · right
      linear_combination h
  constructor
  · intro m n
    rcases hsq with h | h
    · refine ⟨m • a + n • (H.w0 • a), ?_⟩
      rw [map_add, map_zsmul, map_zsmul]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply]
      simp only [smul_eq_mul, zsmul_eq_mul, hw0 i, h]
      ring
    · refine ⟨(m + n) • a - n • (H.w0 • a), ?_⟩
      rw [map_sub, map_zsmul, map_zsmul]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply]
      simp only [smul_eq_mul, zsmul_eq_mul, hw0 i, h]
      push_cast
      ring
  · intro z w
    rw [_root_.GlobalTheory.PureTypeVector.hermForm_smul_smul]
    have him : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).im = 0 := _root_.GlobalTheory.PureTypeVector.hermForm_self_im hH _
    have hre : 0 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re := by
      by_cases h0 : Pe a = 0
      · simp [h0, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm]
      · exact (hpos _ h0).le
    have hc : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (((1 + ρ) / 2) • Pe a) (Pe a) = (1 + ρ) / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a) := by
      simpa using _root_.GlobalTheory.PureTypeVector.hermForm_smul_smul Hm ((1 + ρ) / 2) 1 (Pe a) (Pe a)
    have hEF := hE (H.w0 • a) a
    rw [hw0', hc] at hEF
    have hh : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a) = ((_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re : ℂ) :=
      Complex.ext rfl (by simp [him])
    have hs : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (Nat.cast_pos.2 H.d_prime.pos)
    have habs : |((D.EF (H.w0 • a) a : ℤ) : ℝ)| = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 := by
      rw [hh] at hEF
      have hnn : 0 ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 :=
        div_nonneg (mul_nonneg hre hs.le) zero_le_two
      rcases hsq with h | h
      · rw [h] at hEF
        simp [Complex.mul_im, Complex.div_re, Complex.div_im] at hEF
        have he : ((D.EF (H.w0 • a) a : ℤ) : ℝ) = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2 := by
          linarith
        rw [he, abs_of_nonneg hnn]
      · rw [h] at hEF
        simp [Complex.mul_im, Complex.div_re, Complex.div_im] at hEF
        have he : ((D.EF (H.w0 • a) a : ℤ) : ℝ) = -((_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pe a) (Pe a)).re * Real.sqrt H.d / 2) := by
          linarith
        rw [he, abs_neg, abs_of_nonneg hnn]
    have hcast : (((D.EF (H.w0 • a) a).natAbs : ℕ) : ℂ) = ((|((D.EF (H.w0 • a) a : ℤ) : ℝ)| : ℝ) : ℂ) := by
      rw [Nat.cast_natAbs, ← Int.cast_abs, Complex.ofReal_intCast]
    have hs' : ((Real.sqrt H.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
    rw [hcast, habs]
    conv_lhs => rw [hh]
    push_cast
    field_simp
end _root_.GlobalTheory
end GlobalTheory
