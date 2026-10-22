-- Prove2me | solution 1 for InfoGen.Expected.empRisk_subgaussian
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:21:12.964472+00:00
-- url     : https://prove2.me/submissions/5be94333-15a3-48f6-be66-3d50ff0930e3

import Mathlib
import Definitions.Def_InfoGen_Expected_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

open InfoGen.Expected LearnStability.Characterization

theorem solution {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ) :
    ∀ w, HasSubgaussianMGF (fun s => empRisk ℓ s w - risk ℓ μ w) (σ ^ 2 / n)
      (sampleLaw μ n) := by
  intro w
  classical
  set r := risk ℓ μ w with hr
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let g : Z → ℝ := fun z => (1 / (n : ℝ)) * (ℓ w z - r)
  let c : ℝ≥0 := ((n : ℝ≥0)⁻¹) ^ 2 * σ ^ 2
  have hceq : (⟨(1 / (n : ℝ)) ^ 2, sq_nonneg _⟩ : ℝ≥0) = ((n : ℝ≥0)⁻¹) ^ 2 := by
    apply NNReal.eq
    show (1 / (n : ℝ)) ^ 2 = (((n : ℝ≥0)⁻¹ ^ 2 : ℝ≥0) : ℝ)
    push_cast
    simp
  have hg : HasSubgaussianMGF g c μ := by
    have := (hσ w).const_mul (1 / (n : ℝ))
    rw [hceq] at this
    exact this
  have hgm : Measurable g :=
    measurable_const.mul ((hℓ.comp (measurable_const.prodMk measurable_id)).sub_const r)
  have hmap : ∀ i : Fin n, (sampleLaw μ n).map (fun s : Fin n → Z => s i) = μ := by
    intro i
    unfold sampleLaw
    rw [Measure.pi_map_eval]
    simp
  have hi : ∀ i : Fin n, HasSubgaussianMGF (fun s : Fin n → Z => g (s i)) c (sampleLaw μ n) := by
    intro i
    have h1 : HasSubgaussianMGF g c ((sampleLaw μ n).map (fun s : Fin n → Z => s i)) := by
      rw [hmap i]; exact hg
    exact HasSubgaussianMGF.of_map (X := g) (Y := fun s : Fin n → Z => s i)
      (measurable_pi_apply i).aemeasurable h1
  have hind : iIndepFun (fun (i : Fin n) (s : Fin n → Z) => g (s i)) (sampleLaw μ n) :=
    iIndepFun_pi (μ := fun _ : Fin n => μ) (X := fun _ => g) (fun _ => hgm.aemeasurable)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ) (c := fun _ => c)
    (fun i _ => hi i)
  have hfun : (fun s : Fin n → Z => empRisk ℓ s w - r) = fun s => ∑ i : Fin n, g (s i) := by
    funext s
    simp only [empRisk, g]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp
    field_simp
  have hc : (σ ^ 2 / (n : ℝ≥0) : ℝ≥0) = ∑ _i : Fin n, c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hnN : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [c, nsmul_eq_mul]
    field_simp
  rw [hc, hfun]
  exact hsum
