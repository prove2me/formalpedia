-- Prove2me | solution 1 for GlobalTheory.CMVal.cmValueConst_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:01:28.252295+00:00
-- url     : https://prove2.me/submissions/f6ab6031-4800-41e8-bb2d-1bc478accedc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_cmValueConst_eq
import Theorems.Thm_Formalism_L2_Host_unif_spec


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
theorem _root_.solution (E : Type) [Field E] [NumberField E] {d k : ℕ} (hd : 0 < d) (hk : 1 ≤ k) (κ : I → ℕ) : 0 < C0 E d k κ := by
  rw [cmValueConst_eq]
  have h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
  have h2 : (0 : ℝ) < k := by exact_mod_cast hk
  have h3 : (0 : ℝ) < d := by exact_mod_cast hd
  refine mul_pos (mul_pos (Real.rpow_pos_of_pos h1 _) (Finset.prod_pos fun i _ => Real.Gamma_pos_of_pos (by positivity))) ?_
  have := Real.pi_pos
  positivity
end GlobalTheory.CMVal
