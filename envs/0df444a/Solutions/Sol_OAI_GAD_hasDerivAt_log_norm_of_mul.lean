-- Prove2me | solution 1 for OAI.GAD.hasDerivAt_log_norm_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:17:14.15633+00:00
-- url     : https://prove2.me/submissions/6c2e0323-38eb-476b-b1d9-4e4d8eb1a366

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean:L108-L127
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.hasDerivAt_log_norm_of_mul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

-- ---- from OAI.InformationTheory.AmplitudeDamping.MatrixDifferentiation ----
namespace OAI

universe u_1 u_2

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Logarithmic norm differentiation, without choosing a complex logarithm branch. -/
theorem hasDerivAt_log_norm_of_mul {z : ℝ → ℂ} {w : ℂ} {t : ℝ}
    (hz : HasDerivAt z (z t * w) t) (h0 : z t ≠ 0) :
    HasDerivAt (fun s ↦ Real.log ‖z s‖) w.re t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
  change HasDerivAt (fun s ↦ (z s).re) (z t * w).re t at hr
  change HasDerivAt (fun s ↦ (z s).im) (z t * w).im t at hi
  have hq : HasDerivAt (fun s ↦ Complex.normSq (z s))
      (2 * Complex.normSq (z t) * w.re) t := by
    convert! (hr.mul hr).add (hi.mul hi) using 1
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hn : Complex.normSq (z t) ≠ 0 := ne_of_gt (Complex.normSq_pos.2 h0)
  have h := (hq.log hn).div_const 2
  convert! h using 1
  · ext s
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    simp
  · field_simp

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.hasDerivAt_log_norm_of_mul := @_root_.OAI.GAD.hasDerivAt_log_norm_of_mul
