-- Prove2me | solution 1 for JHolomorphic.HasWeakPartialsOn.of_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T21:12:41.82599+00:00
-- url     : https://prove2.me/submissions/57b1e189-6f71-434d-b034-052c76e550b6

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts



namespace JHolomorphic

open MeasureTheory
open scoped ContDiff

theorem HasWeakPartialsOn.of_contDiffOn_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} (hU : IsOpen U) {u : ℂ → E} (hu : ContDiffOn ℝ 1 u U) :
    HasWeakPartialsOn U u (fun z => fderiv ℝ u z 1) (fun z => fderiv ℝ u z Complex.I) := by
  intro φ hφ hφc hφU
  have hcont : ContinuousOn u U := hu.continuousOn
  have hdcont : ∀ v : ℂ, ContinuousOn (fun z => fderiv ℝ u z v) U := fun v =>
    ((hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)
  have huK : ∀ K ⊆ U, IsCompact K → IntegrableOn u K := fun K hK hKc =>
    (hcont.mono hK).integrableOn_compact hKc
  have hdK : ∀ v : ℂ, ∀ K ⊆ U, IsCompact K → IntegrableOn (fun z => fderiv ℝ u z v) K :=
    fun v K hK hKc => ((hdcont v).mono hK).integrableOn_compact hKc
  have key : ∀ v : ℂ, ∫ z, fderiv ℝ φ z v • u z = -∫ z, φ z • fderiv ℝ u z v := by
    intro v
    obtain ⟨hφv, hφvc, hφvU⟩ := fderiv_apply_isTestFunction hφ hφc hφU v
    have i1 : Integrable (fun z => fderiv ℝ φ z v • u z) :=
      integrable_smul_of_integrableOn_compact huK hφv.continuous.continuousOn hφvc hφvU
    have i2 : Integrable (fun z => φ z • fderiv ℝ u z v) :=
      integrable_smul_of_integrableOn_compact (hdK v) hφ.continuous.continuousOn hφc hφU
    have i3 : Integrable (fun z => φ z • u z) :=
      integrable_smul_of_integrableOn_compact huK hφ.continuous.continuousOn hφc hφU
    have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume) (v := v)
      i1 i2 i3 (fun x _ => (hφ.differentiable (by simp)) x)
      (fun x hx => (hu.differentiableOn one_ne_zero x (hφU hx)).differentiableAt
        (hU.mem_nhds (hφU hx)))
    rw [h, neg_neg]
  exact ⟨key 1, key Complex.I⟩

end JHolomorphic

open JHolomorphic JHolomorphic.HasWeakPartialsOn

open MeasureTheory
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} (hU : IsOpen U) {u : ℂ → E} (hu : ContDiffOn ℝ 1 u U) :
    HasWeakPartialsOn U u (fun z => fderiv ℝ u z 1) (fun z => fderiv ℝ u z Complex.I) :=
  HasWeakPartialsOn.of_contDiffOn_aux hU hu
