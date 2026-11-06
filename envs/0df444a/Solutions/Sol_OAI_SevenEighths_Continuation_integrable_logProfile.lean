-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.integrable_logProfile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:51:52.654644+00:00
-- url     : https://prove2.me/submissions/94089308-964a-49b1-bc68-21b7a08c0a89

import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Mathlib.Analysis.MellinInversion
import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationInversion

set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology FourierTransform
open OAI.SevenEighths OAI.SevenEighths.Continuation
namespace OAI.SevenEighths.Continuation
theorem _root_.solution {f : ℝ → ℂ} {σ : ℝ}
    (hf : MellinConvergent f (σ : ℂ)) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  have hder : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
    fun x _ => mul_neg_one (Real.exp (-x)) ▸
      ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt
  have himage : Real.exp ∘ Neg.neg '' (univ : Set ℝ) = Ioi 0 := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
      Set.image_univ, Real.range_exp]
  have hinj : univ.InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [MellinConvergent, ← himage,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder hinj] at hf
  have heq (u : ℝ) :
      |-(Real.exp (-u))| • ((Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1) • f (Real.exp (-u))) =
        Real.exp (-σ * u) • f (Real.exp (-u)) := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _)]
    change (Real.exp (-u) : ℂ) *
      ((Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1) * f (Real.exp (-u))) =
        (Real.exp (-σ * u) : ℂ) * f (Real.exp (-u))
    rw [← mul_assoc]
    congr 1
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (Real.exp_pos (-u)).le]
    norm_cast
    rw [Real.rpow_def_of_pos (Real.exp_pos (-u)), Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  simpa only [Function.comp_apply, integrableOn_univ, heq] using hf
end OAI.SevenEighths.Continuation
