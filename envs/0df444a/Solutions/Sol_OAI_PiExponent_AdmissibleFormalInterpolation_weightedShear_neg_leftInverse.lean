-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_neg_leftInverse
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:28:09.322408+00:00
-- url     : https://prove2.me/submissions/43268d08-9d03-493c-a45f-3fbed23da8df

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weight_mem_strictWeightedSimplex
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_coordinate_roundtrip
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_roundtrip_coeff
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_inverse_preserves_filtered_vanishing

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

set_option maxHeartbeats 1200000

/-- The weighted shear of `-D` is a left inverse of the weighted shear of `D` on the
strict weighted simplex. -/
theorem solution
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hD : ∀ i n, n < N i → PowerSeries.coeff n (D i) = 0)
    (hH : 0 < H) :
    (weightedShear (m := m) v0 u H (fun i : Fin m => -D i)) ∘ₗ
        (weightedShear (m := m) v0 u H D) =
      (LinearMap.id :
        ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ) →ₗ[ℂ]
          ((↥(strictWeightedSimplex (Fin.cases v0 u) H)) → ℂ)) := by
  classical
  -- The weights in the `q`-indexed shape used by the roundtrip lemmas.
  let w : Fin (m + 1) → ℝ := fun i => Fin.cases v0 u i
  let S : Finset (Fin (m + 1) → ℕ) := strictWeightedSimplex w H
  let q : Fin (m + 1) → ℝ := w
  -- The forward and inverse shear families.
  let P : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    fun i => Fin.cases (MvPowerSeries.X 0)
      (fun j => MvPowerSeries.X j.succ + liftLogSeries m (D j)) i
  let M : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ :=
    fun i => Fin.cases (MvPowerSeries.X 0)
      (fun j => MvPowerSeries.X j.succ - liftLogSeries m (D j)) i
  have hP : seriesShear (m := m) D = MvPolynomial.aeval P := rfl
  have hMinus : seriesShear (m := m) (fun i : Fin m => -D i) = MvPolynomial.aeval M := by
    simp only [seriesShear]
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp [M]
    · intro i
      simp [M, map_neg, sub_eq_add_neg]
  -- the matrix entries are computed by the shear of the corresponding monomials
  have happ : ∀ (E : Fin m → PowerSeries ℂ) (z : ↥S → ℂ) (c : ↥S),
      weightedShear (m := m) v0 u H E z c =
        ∑ a : ↥S, z a * MvPowerSeries.coeff
          (InterpolationMatrix.exponentVector c.val)
          (seriesShear (m := m) E
            (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ))) := by
    intro E z c
    rfl
  -- positivity and the `q`-shaped vanishing hypothesis for `D`
  have hq : ∀ j, 0 < q j := by
    intro j
    refine Fin.cases ?_ ?_ j
    · simpa [q, w] using hv0
    · intro i; simpa [q, w] using hu i
  have hDq : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0 := by
    intro i n hn
    have hq0 : q 0 = v0 := rfl
    have hqi : q i.succ = u i := rfl
    rw [hq0, hqi] at hn
    refine hD i n ?_
    by_contra hlt
    push Not at hlt
    have hle : (N i : ℝ) * v0 ≤ (n : ℝ) * v0 := by
      have hNle : (N i : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlt
      exact mul_le_mul_of_nonneg_right hNle hv0.le
    linarith [hN i]
  -- the inverse family is substitutable
  have hMsub : MvPowerSeries.HasSubst M :=
    (OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_coordinate_roundtrip
      (q := q) hq D hDq).2.1
  -- a strictly sub-cutoff exponent lies in the simplex
  have hmem_of_weight : ∀ a : Fin (m + 1) → ℕ,
      (∑ j, q j * (a j : ℝ)) < H → a ∈ S := by
    intro a ha
    have := OAI.PiExponent.AdmissibleFormalInterpolation.weight_mem_strictWeightedSimplex
      (m := m) v0 u H hv0 hu hH a (by simpa [q, w] using ha)
    simpa [S, w] using this
  -- coefficient of a sum of scaled monomials
  have hinj : Function.Injective
      (fun a : Fin (m + 1) → ℕ => InterpolationMatrix.exponentVector a) := by
    intro a b h
    simpa [InterpolationMatrix.exponentVector] using congrArg Finsupp.equivFunOnFinite h
  have hcoeff_sum_monomial : ∀ (z : ↥S → ℂ) (c : ↥S),
      MvPolynomial.coeff (InterpolationMatrix.exponentVector c.val)
        (∑ a : ↥S, z a •
          MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) 1) = z c := by
    intro z c
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single c]
    · simp
    · intro a _ hne
      have hvec : InterpolationMatrix.exponentVector a.val ≠
          InterpolationMatrix.exponentVector c.val := by
        intro h
        exact hne (Subtype.ext (hinj h))
      simp [hvec]
    · intro hc
      exact absurd (Finset.mem_univ c) hc
  apply LinearMap.ext
  intro x
  -- the two intermediate objects: the coefficients of the forward shear of `Px`
  let Px : MvPolynomial (Fin (m + 1)) ℂ :=
    ∑ a : ↥S, x a • MvPolynomial.monomial
      (InterpolationMatrix.exponentVector a.val) 1
  let F : MvPowerSeries (Fin (m + 1)) ℂ := MvPolynomial.aeval P Px
  let y : ↥S → ℂ := fun a =>
    ∑ a' : ↥S, x a' * MvPowerSeries.coeff
      (InterpolationMatrix.exponentVector a.val)
      (MvPolynomial.aeval P
        (MvPolynomial.monomial (InterpolationMatrix.exponentVector a'.val) (1 : ℂ)))
  let Qy : MvPolynomial (Fin (m + 1)) ℂ :=
    ∑ a : ↥S, y a • MvPolynomial.monomial
      (InterpolationMatrix.exponentVector a.val) 1
  have hPx_coeff : ∀ c : ↥S,
      MvPolynomial.coeff (InterpolationMatrix.exponentVector c.val) Px = x c := by
    intro c
    simpa [Px] using hcoeff_sum_monomial x c
  have hF_coeff : ∀ c : ↥S,
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector c.val) F = y c := by
    intro c
    simp only [F, Px, y]
    rw [map_sum]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have hQy_coeff : ∀ c : ↥S,
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector c.val)
        (Qy : MvPowerSeries (Fin (m + 1)) ℂ) = y c := by
    intro c
    rw [MvPolynomial.coeff_coe]
    simpa [Qy] using hcoeff_sum_monomial y c
  -- the error between the forward sheared series and the inverse-sheared polynomial
  have hE : ∀ a : Fin (m + 1) → ℕ, (∑ j, q j * (a j : ℝ)) < H →
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (F - (Qy : MvPowerSeries (Fin (m + 1)) ℂ)) = 0 := by
    intro a ha
    have hmem : a ∈ S := hmem_of_weight a ha
    have h1 : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a) F =
        y ⟨a, hmem⟩ := by simpa using hF_coeff ⟨a, hmem⟩
    have h2 : MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (Qy : MvPowerSeries (Fin (m + 1)) ℂ) = y ⟨a, hmem⟩ := by
      simpa using hQy_coeff ⟨a, hmem⟩
    rw [map_sub, h1, h2, sub_self]
  funext b
  -- weight of the target exponent is below the cutoff
  have hbH : (∑ j, q j * (b.val j : ℝ)) < H := by
    have h := (Finset.mem_filter.mp b.property).2
    simpa [S, w] using h
  have hEzero : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
      (MvPowerSeries.subst M (F - (Qy : MvPowerSeries (Fin (m + 1)) ℂ))) = 0 := by
    have hpres :=
      OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_inverse_preserves_filtered_vanishing
        (q := q) hq D hDq H (F - (Qy : MvPowerSeries (Fin (m + 1)) ℂ)) hE
    simpa [M] using hpres b.val (by simpa [q] using hbH)
  have hsplit : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
        (MvPowerSeries.subst M F) =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
        (MvPowerSeries.subst M (Qy : MvPowerSeries (Fin (m + 1)) ℂ)) := by
    have hsub := MvPowerSeries.subst_sub hMsub F
      (Qy : MvPowerSeries (Fin (m + 1)) ℂ)
    have hc := congrArg
      (MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)) hsub
    simp only [map_sub] at hc
    rw [hEzero] at hc
    exact sub_eq_zero.mp hc.symm
  have hroundtrip : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
        (MvPowerSeries.subst M F) =
      MvPolynomial.coeff (InterpolationMatrix.exponentVector b.val) Px := by
    have hrt := OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_roundtrip_coeff
      (q := q) hq D hDq Px b.val
    simpa [F, P, M] using hrt
  have hLHS : (∑ a : ↥S, y a * MvPowerSeries.coeff
        (InterpolationMatrix.exponentVector b.val)
        (MvPolynomial.aeval M
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ)))) =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
        (MvPolynomial.aeval M Qy) := by
    simp only [Qy]
    rw [map_sum]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  have hsubstCoe : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
        (MvPolynomial.aeval M Qy) =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
        (MvPowerSeries.subst M (Qy : MvPowerSeries (Fin (m + 1)) ℂ)) := by
    rw [MvPowerSeries.subst_coe]
  -- reduce the goal to the matrix identity
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  simp only [happ]
  rw [hP, hMinus]
  change (∑ a : ↥S, y a * MvPowerSeries.coeff
        (InterpolationMatrix.exponentVector b.val)
        (MvPolynomial.aeval M
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ)))) = x b
  calc (∑ a : ↥S, y a * MvPowerSeries.coeff
        (InterpolationMatrix.exponentVector b.val)
        (MvPolynomial.aeval M
          (MvPolynomial.monomial (InterpolationMatrix.exponentVector a.val) (1 : ℂ))))
      = MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (MvPolynomial.aeval M Qy) := hLHS
    _ = MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (MvPowerSeries.subst M (Qy : MvPowerSeries (Fin (m + 1)) ℂ)) := hsubstCoe
    _ = MvPowerSeries.coeff (InterpolationMatrix.exponentVector b.val)
          (MvPowerSeries.subst M F) := hsplit.symm
    _ = MvPolynomial.coeff (InterpolationMatrix.exponentVector b.val) Px := hroundtrip
    _ = x b := hPx_coeff b
