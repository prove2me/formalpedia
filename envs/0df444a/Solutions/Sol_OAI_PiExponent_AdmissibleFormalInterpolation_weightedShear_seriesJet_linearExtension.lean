-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_seriesJet_linearExtension
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:15:07.266544+00:00
-- url     : https://prove2.me/submissions/c4f942d5-e1d7-4cdd-8906-89afec0604d4

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

/-- The shear identity for the weighted series jet, verified on monomials, extends to all
polynomials because both sides are linear in the polynomial argument. -/
theorem solution {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D F : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (hH : 0 < H)
    (c : Fin m → ℂ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hmono : ∀ e : Fin (m + 1) →₀ ℕ,
      (weightedShear (m := m) v0 u H D).toFun
          (weightedSeriesJet (m := m) v0 u H c F
            (MvPolynomial.monomial e 1)) =
        weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i)
          (MvPolynomial.monomial e 1)) :
    (weightedShear (m := m) v0 u H D).toFun
        (weightedSeriesJet (m := m) v0 u H c F P) =
      weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i) P := by
  classical
  -- Linearity of the weighted series jet in its polynomial argument.
  have hSJ_add : ∀ (G : Fin m → PowerSeries ℂ) (Q R : MvPolynomial (Fin (m + 1)) ℂ),
      weightedSeriesJet (m := m) v0 u H c G (Q + R) =
        weightedSeriesJet (m := m) v0 u H c G Q +
          weightedSeriesJet (m := m) v0 u H c G R := by
    intro G Q R
    funext b
    simp only [weightedSeriesJet, Pi.add_apply]
    rw [map_add (seriesJet c G), map_add]
  have hSJ_smul : ∀ (G : Fin m → PowerSeries ℂ) (r : ℂ)
      (Q : MvPolynomial (Fin (m + 1)) ℂ),
      weightedSeriesJet (m := m) v0 u H c G (r • Q) =
        r • weightedSeriesJet (m := m) v0 u H c G Q := by
    intro G r Q
    funext b
    simp only [weightedSeriesJet, Pi.smul_apply, smul_eq_mul]
    rw [map_smul (seriesJet c G), map_smul]
    exact smul_eq_mul r _
  -- The two sides as linear maps of the polynomial argument.
  let L1 : MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ]
      (↥(strictWeightedSimplex (Fin.cases v0 u) H) → ℂ) :=
    { toFun := fun Q => (weightedShear (m := m) v0 u H D).toFun
        (weightedSeriesJet (m := m) v0 u H c F Q)
      map_add' := fun Q R => by
        rw [hSJ_add]
        exact (weightedShear (m := m) v0 u H D).map_add _ _
      map_smul' := fun r Q => by
        rw [hSJ_smul]
        exact (weightedShear (m := m) v0 u H D).map_smul r _ }
  let L2 : MvPolynomial (Fin (m + 1)) ℂ →ₗ[ℂ]
      (↥(strictWeightedSimplex (Fin.cases v0 u) H) → ℂ) :=
    { toFun := fun Q =>
        weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i) Q
      map_add' := fun Q R => hSJ_add (fun i => F i + D i) Q R
      map_smul' := fun r Q => hSJ_smul (fun i => F i + D i) r Q }
  -- Linear maps out of the polynomial ring are determined by their values on monomials.
  have hL : L1 = L2 := by
    refine (MvPolynomial.basisMonomials (Fin (m + 1)) ℂ).ext (fun e => ?_)
    simp only [MvPolynomial.coe_basisMonomials]
    change (weightedShear (m := m) v0 u H D).toFun
        (weightedSeriesJet (m := m) v0 u H c F (MvPolynomial.monomial e 1)) =
      weightedSeriesJet (m := m) v0 u H c (fun i => F i + D i)
        (MvPolynomial.monomial e 1)
    exact hmono e
  exact LinearMap.congr_fun hL P
