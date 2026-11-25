-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.fderiv_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:17:36.8559+00:00
-- url     : https://prove2.me/submissions/7f95d6be-e458-4149-81c5-56d7ddf5b317

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_ThetaGauss_hasDerivAt_line
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {f p : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (hp : Differentiable ℂ p) (a v : Fin g → ℂ) (j : (Fin g → ℂ) → ℂ) (l : ℂ)
    (hj : ∀ z (t : ℂ), j (z + t • v) = j z * Complex.exp (t * l))
    (h : ∀ z, f (z + a) = j z * p z) (z : Fin g → ℂ) :
    fderiv ℂ f (z + a) v = j z * (fderiv ℂ p z v + l * p z) := by
  have h1 := hasDerivAt_line hf (z + a) v 0
  have h2 := ((((hasDerivAt_id (0 : ℂ)).mul_const l).cexp).const_mul (j z)).mul
    (hasDerivAt_line hp z v 0)
  have e : (fun t : ℂ => f (z + a + t • v)) =
      (fun t : ℂ => j z * Complex.exp (id t * l)) * fun t : ℂ => p (z + t • v) := by
    ext t
    rw [add_right_comm, h, hj]; rfl
  rw [e] at h1
  have := h1.unique h2
  simp only [zero_smul, add_zero, id, zero_mul, Complex.exp_zero] at this
  rw [this]; ring
end GlobalTheory.ThetaGauss
