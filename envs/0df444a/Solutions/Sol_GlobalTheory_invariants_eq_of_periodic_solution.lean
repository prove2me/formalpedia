-- Prove2me | solution 1 for GlobalTheory.invariants_eq_of_periodic_solution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:39:59.811439+00:00
-- url     : https://prove2.me/submissions/2cc3fc46-485d-4a36-b09c-08806deabb89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsConstOfSqMulTendstoZero
import Theorems.Thm_GlobalTheory_PeriodicWeierstrass_exists_eq_of_sq_mul_tendsto
import Theorems.Thm_GlobalTheory_PeriodicWeierstrass_exists_eq_of_cube_mul_tendsto
import Theorems.Thm_GlobalTheory_PeriodicWeierstrass_tendsto_leading
import Theorems.Thm_GlobalTheory_eventually_ne_notMem_periodLattice
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_exists_weierstrassP_eq_and_derivWeierstrassP_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology
noncomputable section
open GlobalTheory
open Filter PeriodPair
open scoped Topology
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (L : PeriodPair) (W : WeierstrassCurve ℂ) (x y t : ℂ → ℂ) (c : ℂ), c ≠ 0 →
  DifferentiableOn ℂ x (L.lattice : Set ℂ)ᶜ → DifferentiableOn ℂ y (L.lattice : Set ℂ)ᶜ →
  (∀ l ∈ L.lattice, ∀ z, x (z + l) = x z ∧ y (z + l) = y z) →
  (∀ z, z ∉ L.lattice → W.toAffine.Equation (x z) (y z)) →
  AnalyticAt ℂ t 0 → t 0 = 0 → deriv t 0 = c →
  (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) →
  Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop →
  c ^ 4 * W.c₄ = 12 * L.g₂ ∧ c ^ 6 * W.c₆ = 216 * L.g₃ ∧
    c ^ 12 * W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  intro L W x y t c hc hxd hyd hper hEq ht ht0 ht1 hty hy
  have hxd' : ∀ z ∉ L.lattice, DifferentiableAt ℂ x z := fun z hz =>
    hxd.differentiableAt (_root_.GlobalTheory.eventually_notMem_periodLattice L hz)
  have hyd' : ∀ z ∉ L.lattice, DifferentiableAt ℂ y z := fun z hz =>
    hyd.differentiableAt (_root_.GlobalTheory.eventually_notMem_periodLattice L hz)
  have hE : ∀ᶠ z in 𝓝[≠] 0, W.toAffine.Equation (x z) (y z) :=
    (_root_.GlobalTheory.eventually_ne_notMem_periodLattice L 0).mono fun z hz => hEq z hz
  obtain ⟨h2, h3⟩ := _root_.GlobalTheory.PeriodicWeierstrass.tendsto_leading W hc hE ht ht0 ht1 hty hy
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.PeriodicWeierstrass.exists_eq_of_sq_mul_tendsto L (g := fun z => c ^ 2 * x z) (a := 1)
    (fun z hz => (hxd' z hz).const_mul _) (fun z l hl => by rw [(hper l hl z).1]) h2
  have h3' : Tendsto (fun z => z ^ 3 * (2 * (c ^ 3 * y z))) (𝓝[≠] 0) (𝓝 (-2)) := by
    have := h3.const_mul 2
    rw [show (2 : ℂ) * -1 = -2 by norm_num] at this
    exact this.congr' (Eventually.of_forall fun z => by ring)
  obtain ⟨b, k', hb⟩ := _root_.GlobalTheory.PeriodicWeierstrass.exists_eq_of_cube_mul_tendsto L
    (g := fun z => 2 * (c ^ 3 * y z))
    (fun z hz => ((hyd' z hz).const_mul _).const_mul _) (fun z l hl => by rw [(hper l hl z).2]) h3'
  have hcurve : ∀ X Y : ℂ, Y ^ 2 = 4 * X ^ 3 - L.g₂ * X - L.g₃ →
      (Y + b * X + k') ^ 2 + 2 * W.a₁ * c * (X + k) * (Y + b * X + k')
        + 2 * W.a₃ * c ^ 3 * (Y + b * X + k') - 4 * (X + k) ^ 3 - 4 * W.a₂ * c ^ 2 * (X + k) ^ 2
        - 4 * W.a₄ * c ^ 4 * (X + k) - 4 * W.a₆ * c ^ 6 = 0 := by
    intro X Y hXY
    obtain ⟨z, hz, hP, hQ⟩ := _root_.GlobalTheory.exists_weierstrassP_eq_and_derivWeierstrassP_eq L hXY
    have he := hEq z hz
    rw [WeierstrassCurve.Affine.equation_iff] at he
    have hx := hk z hz
    have hy' := hb z hz
    rw [hP] at hx
    rw [hP, hQ] at hy'
    have e1 : X + k = c ^ 2 * x z := by linear_combination -hx
    have e2 : Y + b * X + k' = 2 * (c ^ 3 * y z) := by linear_combination -hy'
    rw [e1, e2]
    linear_combination 4 * c ^ 6 * he
  have hAB : ∀ X : ℂ,
      (b ^ 2 + 2 * W.a₁ * c * b - 12 * k - 4 * W.a₂ * c ^ 2) * X ^ 2
        + (-L.g₂ + 2 * b * k' + 2 * W.a₁ * c * (k' + b * k) + 2 * W.a₃ * c ^ 3 * b - 12 * k ^ 2
          - 8 * W.a₂ * c ^ 2 * k - 4 * W.a₄ * c ^ 4) * X
        + (-L.g₃ + k' ^ 2 + 2 * W.a₁ * c * k * k' + 2 * W.a₃ * c ^ 3 * k' - 4 * k ^ 3
          - 4 * W.a₂ * c ^ 2 * k ^ 2 - 4 * W.a₄ * c ^ 4 * k - 4 * W.a₆ * c ^ 6) = 0 ∧
      ((2 * b + 2 * W.a₁ * c) * X + (2 * k' + 2 * W.a₁ * c * k + 2 * W.a₃ * c ^ 3)) ^ 2
        * (4 * X ^ 3 - L.g₂ * X - L.g₃) = 0 := by
    intro X
    obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq (4 * X ^ 3 - L.g₂ * X - L.g₃) two_pos
    have e1 := hcurve X Y hY
    have e2 := hcurve X (-Y) (by rw [neg_sq]; exact hY)
    constructor
    · linear_combination (e1 + e2) / 2 - hY
    · linear_combination
        (-((2 * b + 2 * W.a₁ * c) * X + (2 * k' + 2 * W.a₁ * c * k + 2 * W.a₃ * c ^ 3)) ^ 2) * hY
        + (Y * ((2 * b + 2 * W.a₁ * c) * X + (2 * k' + 2 * W.a₁ * c * k + 2 * W.a₃ * c ^ 3)) / 2)
          * (e1 - e2)
  have hA0 := (hAB 0).1
  have hA1 := (hAB 1).1
  have hAm := (hAB (-1)).1
  have hα₀ : -L.g₃ + k' ^ 2 + 2 * W.a₁ * c * k * k' + 2 * W.a₃ * c ^ 3 * k' - 4 * k ^ 3
      - 4 * W.a₂ * c ^ 2 * k ^ 2 - 4 * W.a₄ * c ^ 4 * k - 4 * W.a₆ * c ^ 6 = 0 := by
    linear_combination hA0
  have hα₁ : -L.g₂ + 2 * b * k' + 2 * W.a₁ * c * (k' + b * k) + 2 * W.a₃ * c ^ 3 * b - 12 * k ^ 2
      - 8 * W.a₂ * c ^ 2 * k - 4 * W.a₄ * c ^ 4 = 0 := by
    linear_combination (hA1 - hAm) / 2
  have hα₂ : b ^ 2 + 2 * W.a₁ * c * b - 12 * k - 4 * W.a₂ * c ^ 2 = 0 := by
    linear_combination (hA1 + hAm) / 2 - hA0
  open Polynomial in
  have hp : (C (2 * b + 2 * W.a₁ * c) * X + C (2 * k' + 2 * W.a₁ * c * k + 2 * W.a₃ * c ^ 3)) ^ 2
      * (C 4 * X ^ 3 - C L.g₂ * X - C L.g₃) = 0 := by
    refine Polynomial.funext fun X => ?_
    simp only [eval_mul, eval_pow, eval_add, eval_sub, eval_C, eval_X, eval_zero]
    exact (hAB X).2
  open Polynomial in
  have hcub : (C 4 * X ^ 3 - C L.g₂ * X - C L.g₃ : ℂ[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.coeff · 3) h
    norm_num [Polynomial.coeff_X, Polynomial.coeff_C] at this
  have hlin := pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp hp).resolve_right hcub)
  have hβ₁ : 2 * b + 2 * W.a₁ * c = 0 := by
    have := congrArg (Polynomial.coeff · 1) hlin
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      Polynomial.coeff_zero, one_ne_zero, zero_ne_one, ↓reduceIte, add_zero, zero_add] at this
    exact this
  have hβ₀ : 2 * k' + 2 * W.a₁ * c * k + 2 * W.a₃ * c ^ 3 = 0 := by
    have := congrArg (Polynomial.coeff · 0) hlin
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C,
      Polynomial.coeff_zero, one_ne_zero, zero_ne_one, ↓reduceIte, add_zero, zero_add] at this
    exact this
  have hb' : b = -(W.a₁ * c) := by linear_combination hβ₁ / 2
  have hk' : k' = -(W.a₁ * c * k) - W.a₃ * c ^ 3 := by linear_combination hβ₀ / 2
  rw [hb'] at hα₂
  have hk₀ : k = -(c ^ 2 * (W.a₁ ^ 2 + 4 * W.a₂)) / 12 := by linear_combination (-1 / 12) * hα₂
  have hg₂ : L.g₂ = 2 * b * k' + 2 * W.a₁ * c * (k' + b * k) + 2 * W.a₃ * c ^ 3 * b - 12 * k ^ 2
      - 8 * W.a₂ * c ^ 2 * k - 4 * W.a₄ * c ^ 4 := by linear_combination -hα₁
  have hg₃ : L.g₃ = k' ^ 2 + 2 * W.a₁ * c * k * k' + 2 * W.a₃ * c ^ 3 * k' - 4 * k ^ 3
      - 4 * W.a₂ * c ^ 2 * k ^ 2 - 4 * W.a₄ * c ^ 4 * k - 4 * W.a₆ * c ^ 6 := by
    linear_combination -hα₀
  rw [hg₂, hg₃, hb', hk', hk₀]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  refine ⟨by ring, by ring, by ring⟩
end _root_.GlobalTheory
end GlobalTheory
