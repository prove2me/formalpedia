-- Prove2me | solution 1 for Malliavin.integral_sq_norm_eq_factorial_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:07.275373+00:00
-- url     : https://prove2.me/submissions/42d411a7-f1a0-4390-8a2b-00fd5bbe472a

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_IsSymmetric_comp_left
import Theorems.Thm_Malliavin_integral_eq_factorial_smul_setIntegral_simplex

set_option autoImplicit false
open MeasureTheory Finset Set
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
variable {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedSpace ℝ E]
namespace Malliavin
theorem _root_.solution [NullSingletonClass μ] {n : ℕ} {g : (Fin n → T) → E}
    (hg : IsSymmetric n g) (hg2 : MemLp g 2 (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, ‖g t‖ ^ 2 ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, ‖g t‖ ^ 2 ∂(Measure.pi fun _ : Fin n => μ) :=
  integral_eq_factorial_smul_setIntegral_simplex (E := ℝ) (hg.comp_left fun x => ‖x‖ ^ 2)
    ((memLp_two_iff_integrable_sq_norm hg2.1).1 hg2)
end Malliavin
