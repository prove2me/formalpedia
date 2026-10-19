-- Prove2me | solution 2 for OAI.KervaireScalarPhase.exp_two_arg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:43:55.055689+00:00
-- url     : https://prove2.me/submissions/28a1a16d-d5a9-4599-8da9-933f66d6b435

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/ScalarPhase.lean:L56-L70
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireScalarPhase.exp_two_arg. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.GroupTheory.Kervaire.ScalarPhase ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireScalarPhase

/-- The polar angle encoded by a doubled exponential. -/
theorem exp_two_arg (x : ℂ) (hx : x ≠ 0) :
    Complex.exp ((2 * x.arg : ℝ) * Complex.I) = x / star x := by
  have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have he : Complex.exp ((x.arg : ℂ) * Complex.I) = x / ‖x‖ := by
    exact (eq_div_iff hn).mpr (by simpa [mul_comm] using Complex.norm_mul_exp_arg_mul_I x)
  rw [show ((2 * x.arg : ℝ) : ℂ) * Complex.I =
    (x.arg : ℂ) * Complex.I + (x.arg : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, he]
  have hsq : (‖x‖ : ℂ) ^ 2 = star x * x := by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq]
    exact Complex.normSq_eq_conj_mul_self
  have hstar : star x ≠ 0 := star_ne_zero.mpr hx
  rw [div_mul_div_comm, ← pow_two, ← pow_two, hsq]
  field_simp

end KervaireScalarPhase

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireScalarPhase
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.KervaireScalarPhase.exp_two_arg := @_root_.OAI.KervaireScalarPhase.exp_two_arg
