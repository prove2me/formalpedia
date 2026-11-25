-- Prove2me | solution 1 for GlobalTheory.T.lintegral_hyperboloid_fibration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:03:10.160058+00:00
-- url     : https://prove2.me/submissions/112f87fb-4d7b-4516-a29b-07e5de765144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibrationStatement
import Theorems.Thm_GlobalTheory_HCXi_lintegral_cone_polar


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : ℕ) (ψ : (Fin (k + 1) → ℂ) → ℝ≥0∞) (F : ℝ → ℝ≥0∞), Measurable ψ → Measurable F → (∫⁻ v : Fin (k + 1) → ℂ in {v | sqLen (Fin.init v : Fin k → ℂ) < Complex.normSq (v (Fin.last k))}, F (Complex.normSq (v (Fin.last k)) - sqLen (Fin.init v : Fin k → ℂ)) * ψ v) = (1 / 2 : ℝ≥0∞) * ∫⁻ τ : ℝ in Set.Ioi 0, F τ * ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi), ψ (Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))) := by
  first | exact @GlobalTheory.HCXi.lintegral_cone_polar | exact GlobalTheory.HCXi.lintegral_cone_polar | (intros; apply GlobalTheory.HCXi.lintegral_cone_polar <;> assumption)
end _root_.GlobalTheory.T
