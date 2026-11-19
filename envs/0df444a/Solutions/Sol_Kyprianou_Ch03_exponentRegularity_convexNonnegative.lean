-- Prove2me | solution 1 for Kyprianou.Ch03.exponentRegularity_convexNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T15:06:06.115451+00:00
-- url     : https://prove2.me/submissions/f18d2a10-99e3-4f06-89fb-4e910c28b07f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace CvxAux

lemma holder_exp {Omega : Type} [MeasurableSpace Omega] {P : Measure Omega}
    (Z : Omega → ℝ) (hZ : Measurable Z) (x y a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1)
    (hx : Integrable (fun ω => Real.exp (x * Z ω)) P)
    (hy : Integrable (fun ω => Real.exp (y * Z ω)) P) :
    ∫ ω, Real.exp ((a * x + b * y) * Z ω) ∂P ≤
      (∫ ω, Real.exp (x * Z ω) ∂P) ^ a * (∫ ω, Real.exp (y * Z ω) ∂P) ^ b := by
  have hpq : (a⁻¹).HolderConjugate (b⁻¹) := Real.HolderConjugate.inv_inv ha hb hab
  have hpow : ∀ (c u : ℝ), 0 < c → ∀ ω, (Real.exp (c * u * Z ω)) ^ c⁻¹ = Real.exp (u * Z ω) := by
    intro c u hc ω
    rw [← Real.exp_mul]; congr 1; field_simp
  have hmem : ∀ (c u : ℝ), 0 < c → Integrable (fun ω => Real.exp (u * Z ω)) P →
      MemLp (fun ω => Real.exp (c * u * Z ω)) (ENNReal.ofReal c⁻¹) P := by
    intro c u hc hu
    have hm : AEStronglyMeasurable (fun ω => Real.exp (c * u * Z ω)) P :=
      (Real.measurable_exp.comp (measurable_const.mul hZ)).aestronglyMeasurable
    rw [← integrable_norm_rpow_iff hm (by simp [hc]) (by simp)]
    rw [ENNReal.toReal_ofReal (inv_nonneg.2 hc.le)]
    refine hu.congr (Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (hpow c u hc ω).symm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun ω => (Real.exp_pos (a * x * Z ω)).le)
    (Eventually.of_forall fun ω => (Real.exp_pos (b * y * Z ω)).le)
    (hmem a x ha hx) (hmem b y hb hy)
  simp only [hpow a x ha, hpow b y hb, one_div, inv_inv] at h
  calc ∫ ω, Real.exp ((a * x + b * y) * Z ω) ∂P
      = ∫ ω, Real.exp (a * x * Z ω) * Real.exp (b * y * Z ω) ∂P := by
        congr 1; ext ω; rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := h

lemma psi_eq {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∫ ω, Real.exp (θ * L.X 1 ω) ∂P = Real.exp (L.ψ θ) := by
  have h := (L.laplace 1 θ hθ).2
  simp only [NNReal.coe_one, one_mul] at h
  exact h

end CvxAux

theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    ConvexOn ℝ (Set.Ici 0) L.ψ := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_Ici] at hx hy
  simp only [smul_eq_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    subst this; simp
  rcases hb.eq_or_lt with rfl | hb'
  · have : a = 1 := by linarith
    subst this; simp
  have hZ : Measurable (L.X 1) :=
    (L.adapted 1).mono (F.le 1) le_rfl
  have h := CvxAux.holder_exp (P := P) (L.X 1) hZ x y a b ha' hb' hab
    (L.laplace 1 x hx).1 (L.laplace 1 y hy).1
  have hxy : 0 ≤ a * x + b * y := by positivity
  rw [CvxAux.psi_eq L _ hxy, CvxAux.psi_eq L _ hx, CvxAux.psi_eq L _ hy,
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add] at h
  have := Real.exp_le_exp.1 h
  linarith
