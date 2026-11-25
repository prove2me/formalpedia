-- Prove2me | solution 1 for GroundTheory.Global.existsUnique_cpow_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:56.327795+00:00
-- url     : https://prove2.me/submissions/63f482b1-cbd7-4012-94a2-8ad7173d4f95

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits
import Theorems.Thm_GroundTheory_Global_ofReal_cpow_eq_exp
import Theorems.Thm_GroundTheory_Global_eq_of_forall_exp_mul_eq
import Theorems.Thm_GroundTheory_Global_existsUnique_exp_of_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex
namespace GroundTheory.Global
theorem _root_.solution (χ : {x : ℝ // 0 < x} →ₜ* ℂˣ) :
    ∃! s : ℂ, ∀ x : {x : ℝ // 0 < x}, (χ x : ℂ) = ((x : ℝ) : ℂ) ^ s := by
  let e : ℝ → {x : ℝ // 0 < x} := fun t => ⟨Real.exp t, Real.exp_pos t⟩
  have econt : Continuous e := Real.continuous_exp.subtype_mk _
  have hlog : ∀ x : {x : ℝ // 0 < x}, e (Real.log x) = x :=
    fun x => Subtype.ext (Real.exp_log x.2)
  obtain ⟨s, hs, -⟩ := existsUnique_exp_of_continuous (fun t => χ (e t))
    (χ.continuous.comp econt)
    (fun a b => by rw [← map_mul]; congr 1; exact Subtype.ext (Real.exp_add a b))
  have hs' : ∀ t : ℝ, (χ (e t) : ℂ) = Complex.exp (s * t) := hs
  refine ⟨s, fun x => ?_, fun s' h' => eq_of_forall_exp_mul_eq fun t => ?_⟩
  · rw [ofReal_cpow_eq_exp x.2, ← hs', hlog]
  · have h1 := h' (e t)
    rw [ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp] at h1
    rw [← h1, hs']
end GroundTheory.Global
