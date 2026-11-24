-- Prove2me | solution 1 for GlobalTheory.CMVal.entire_eq_of_halfPlane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:47:21.849802+00:00
-- url     : https://prove2.me/submissions/79e55a03-6b60-4b8d-a6b2-4dde428d58ab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_Formalism_L2_Host_unif_spec
import Theorems.Thm_GlobalTheory_EntireFunctionHalfPlane_entire_eq_of_eqOn_halfPlane


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal
open Neutral.B1 (finiteSingle)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)
open Formalism.L2.Host (atFin atInf unif unif_spec IsUnitAt IsUnifAt upF aboveInf)
variable (E : Type) [Field E] [NumberField E]
variable {E}
variable (E)
variable {E}
variable {I : Type} [Fintype I]
namespace GlobalTheory.CMVal
theorem _root_.solution {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (a : ℝ)
    (h : ∀ s : ℂ, a < s.re → f s = g s) : f = g := by
  first
  | exact @_root_.GlobalTheory.EntireFunctionHalfPlane.entire_eq_of_eqOn_halfPlane
  | exact _root_.GlobalTheory.EntireFunctionHalfPlane.entire_eq_of_eqOn_halfPlane
  | (apply _root_.GlobalTheory.EntireFunctionHalfPlane.entire_eq_of_eqOn_halfPlane <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntireFunctionHalfPlane.entire_eq_of_eqOn_halfPlane <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntireFunctionHalfPlane.entire_eq_of_eqOn_halfPlane <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntireFunctionHalfPlane.entire_eq_of_eqOn_halfPlane ..)
end GlobalTheory.CMVal
