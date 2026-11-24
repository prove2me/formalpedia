-- Prove2me | solution 1 for GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:37.883469+00:00
-- url     : https://prove2.me/submissions/6722c9ea-8792-4e6d-b9b5-ee8ac2a42c2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPolarGaussianProbabilityComplex
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_finrank_euclidean_complex
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sphereProb_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
noncomputable section
open GlobalTheory GlobalTheory.SphereMeanDrop
namespace GlobalTheory.SphereMeanDrop
theorem _root_.solution (n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)))
      ((sphereProb n).prod (radProb n)) (gaussProb n) := by
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  set f : UnitSphereC n × Ioi (0:ℝ) → EuclideanSpace ℂ (Fin n) :=
    fun p => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)) with hf_def
  set S := (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere with hS
  set R0 := Measure.volumeIoiPow (2 * n - 1) with hR0
  set h : Ioi (0:ℝ) → ENNReal := fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2)) with hh_def
  set g : EuclideanSpace ℂ (Fin n) → ENNReal := fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hg_def
  have hfm : Measurable f := by
    apply Continuous.measurable
    exact (continuous_subtype_val.comp continuous_snd).smul (continuous_subtype_val.comp continuous_fst)
  have hhm : Measurable h := Measurable.ennreal_ofReal (by fun_prop)
  have hgm : Measurable g := Measurable.ennreal_ofReal (by fun_prop)

  have hA : MeasurePreserving f (S.prod R0) volume := by
    have h1 := Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))
    rw [finrank_euclidean_complex] at h1
    have h2 : MeasurePreserving (homeomorphUnitSphereProd (EuclideanSpace ℂ (Fin n))).toMeasurableEquiv
      _ _ := h1
    have h3 := h2.symm
    have h4 : MeasurePreserving (Subtype.val : ({(0 : EuclideanSpace ℂ (Fin n))}ᶜ : Set _) → _)
        ((volume : Measure (EuclideanSpace ℂ (Fin n))).comap Subtype.val) volume := by
      refine ⟨measurable_subtype_coe, ?_⟩
      rw [map_comap_subtype_coe (measurableSet_singleton _).compl, restrict_compl_singleton]
    have h5 := h4.comp h3
    convert h5 using 1
    funext p
    simp [hf_def]

  have hB : MeasurePreserving f (S.prod (R0.withDensity h))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) := by
    refine ⟨hfm, ?_⟩
    rw [prod_withDensity_right hhm]
    ext s hs
    rw [Measure.map_apply hfm hs, withDensity_apply _ (hfm hs), withDensity_apply _ hs]
    have hpt : ∀ z : UnitSphereC n × Ioi (0:ℝ), h z.2 = g (f z) := by
      intro z
      simp only [hh_def, hg_def, hf_def, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < z.2 from z.2.2)]
      have : ‖(z.1 : EuclideanSpace ℂ (Fin n))‖ = 1 := by simp
      rw [this, mul_one]
    simp_rw [hpt]
    exact hA.setLIntegral_comp_preimage hs hgm

  have ha0 : S univ ≠ 0 := by
    rw [hS, Measure.toSphere_apply_univ, finrank_euclidean_complex]
    exact mul_ne_zero (by simp; omega) (Metric.measure_ball_pos _ _ one_pos).ne'
  have haT : S univ ≠ ⊤ := measure_ne_top _ _
  have hsph : sphereProb n = (S univ)⁻¹ • S := sphereProb_eq n
  have hrad : radProb n = ((R0.withDensity h) univ)⁻¹ • R0.withDensity h := by
    simp only [radProb, ProbabilityTheory.cond, Measure.restrict_univ]; rfl
  have hgau : gaussProb n = (((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ)⁻¹ •
      (volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g := by
    simp only [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ]; rfl
  have hmass : ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity g) univ
      = S univ * (R0.withDensity h) univ := by
    rw [← hB.map_eq, Measure.map_apply hfm MeasurableSet.univ, preimage_univ, ← univ_prod_univ,
      Measure.prod_prod]
  refine ⟨hfm, ?_⟩
  rw [hsph, hrad, hgau, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul, hB.map_eq, hmass, ENNReal.mul_inv (Or.inl ha0) (Or.inl haT)]
end GlobalTheory.SphereMeanDrop
