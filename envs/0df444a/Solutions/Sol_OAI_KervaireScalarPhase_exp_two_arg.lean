-- Prove2me | solution 1 for OAI.KervaireScalarPhase.exp_two_arg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:17:02.093484+00:00
-- url     : https://prove2.me/submissions/98675e22-983f-4378-b745-f892a02fc477

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase

open OAI OAI.KervaireScalarPhase
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
theorem solution (x : ℂ) (hx : x ≠ 0) :
    Complex.exp ((2 * x.arg : ℝ) * Complex.I) = x / star x := by
  have hr : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have h1 : x = (‖x‖ : ℂ) * Complex.exp ((x.arg : ℂ) * Complex.I) := (Complex.norm_mul_exp_arg_mul_I x).symm
  have h2 : star x = (‖x‖ : ℂ) * Complex.exp (-((x.arg : ℂ) * Complex.I)) := by
    conv_lhs => rw [h1]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    ring_nf
  rw [h2, eq_div_iff (mul_ne_zero hr (Complex.exp_ne_zero _))]
  conv_rhs => rw [h1]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast; ring
