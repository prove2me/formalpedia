-- Prove2me | solution 1 for GlobalTheory.HCXi.lintegral_cone_polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:22.818107+00:00
-- url     : https://prove2.me/submissions/b43b1e42-d608-47be-866c-99dd4d1d9f32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibration
import Theorems.Thm_GlobalTheory_HCXi_ConePolar_plane
import Theorems.Thm_GlobalTheory_HCXi_ConePolar_measurable_snoc
import Theorems.Thm_GlobalTheory_HCXi_ConePolar_measurable_sqLen
import Theorems.Thm_GlobalTheory_HCXi_ConePolar_lintegral_snoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.HCXi
open ConePolar
namespace GlobalTheory.HCXi
theorem _root_.solution : ∀ (k : ℕ) (ψ : (Fin (k + 1) → ℂ) → ℝ≥0∞) (F : ℝ → ℝ≥0∞), Measurable ψ → Measurable F → (∫⁻ v : Fin (k + 1) → ℂ in {v | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}, F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ : ℝ in Set.Ioi 0, F τ * ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))) := by
  intro k ψ F hψ hF
  have hinit : Measurable fun v : Fin (k + 1) → ℂ => sqLen (Fin.init v : Fin k → ℂ) :=
    (measurable_sqLen k).comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)
  have hlast : Measurable fun v : Fin (k + 1) → ℂ => Complex.normSq (v (Fin.last k)) :=
    Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)
  have hS := measurableSet_lt hinit hlast
  rw [← lintegral_indicator hS, lintegral_snoc k _
    (by exact Measurable.indicator ((hF.comp (hlast.sub hinit)).mul hψ) hS)]
  have h1 : ∀ w : Fin k → ℂ, (∫⁻ z : ℂ, Set.indicator
      {v : Fin (k + 1) → ℂ | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}
      (fun v => F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v)
      (Fin.snoc (α := fun _ => ℂ) w z)) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ in Set.Ioi (0 : ℝ),
        F τ * ∫⁻ θ in Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) w
          (((Real.sqrt (sqLen w + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℝ)))) := by
    intro w
    rw [← plane (sqLen w) (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _) F
      (fun z => ψ (Fin.snoc (α := fun _ => ℂ) w z)) hF
      (hψ.comp ((measurable_snoc k).comp measurable_prodMk_left))]
    refine lintegral_congr fun z => ?_
    simp [Set.indicator]
  simp only [h1]
  have hG : Measurable fun q : ((Fin k → ℂ) × ℝ) × ℝ => ψ (Fin.snoc (α := fun _ => ℂ) q.1.1
      (((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by
    have := measurable_sqLen k
    exact hψ.comp ((measurable_snoc k).comp (f := fun q : ((Fin k → ℂ) × ℝ) × ℝ =>
      (q.1.1, ((Real.sqrt (sqLen q.1.1 + q.1.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ))))
      (by fun_prop))
  have hH := hG.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  rw [lintegral_const_mul' _ _ (by simp), lintegral_lintegral_swap
    (by exact ((hF.comp measurable_snd).mul hH).aemeasurable)]
  congr 1
  refine lintegral_congr fun τ => ?_
  have hG' : Measurable fun q : (Fin k → ℂ) × ℝ => ψ (Fin.snoc (α := fun _ => ℂ) q.1
      (((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ)))) := by
    have := measurable_sqLen k
    exact hψ.comp ((measurable_snoc k).comp (f := fun q : (Fin k → ℂ) × ℝ =>
      (q.1, ((Real.sqrt (sqLen q.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * (q.2 : ℝ))))
      (by fun_prop))
  have hH' := hG'.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  simp only at hH'
  rw [lintegral_const_mul _ hH', Measure.volume_eq_prod, ← Measure.prod_restrict,
    Measure.restrict_univ, lintegral_prod _ hG'.aemeasurable]
end GlobalTheory.HCXi
