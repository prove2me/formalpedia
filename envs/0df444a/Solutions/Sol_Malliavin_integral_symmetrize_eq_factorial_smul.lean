-- Prove2me | solution 1 for Malliavin.integral_symmetrize_eq_factorial_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:11.292827+00:00
-- url     : https://prove2.me/submissions/34b562f4-09f2-4300-8e7c-41927b26d3c9

import Definitions.Def_Malliavin_Symmetrization
import Definitions.Def_Malliavin_Simplex
import Theorems.Thm_Malliavin_integral_eq_factorial_smul_setIntegral_simplex
import Theorems.Thm_Malliavin_isSymmetric_symmetrize


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
namespace Malliavin
theorem _root_.solution [NullSingletonClass μ] {n : ℕ} {f : (Fin n → T) → E}
    (hint : Integrable (symmetrize n f) (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, symmetrize n f t ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, symmetrize n f t ∂(Measure.pi fun _ : Fin n => μ) :=
  integral_eq_factorial_smul_setIntegral_simplex (isSymmetric_symmetrize n f) hint
end Malliavin
