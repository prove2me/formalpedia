-- Prove2me | solution 1 for GlobalTheory.CMVal.cmValueConst_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:17.919691+00:00
-- url     : https://prove2.me/submissions/0bba364c-dc83-4f5d-837f-e1cb4875c66a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
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
theorem _root_.solution (E : Type) [Field E] [NumberField E] (d k : ℕ) (κ : I → ℕ) :
    C0 E d k κ = (|(discr (maximalRealSubfield E) : ℝ)|) ^ (((k : ℝ) - 1) / 2) * (∏ i, Real.Gamma ((k : ℝ) + κ i)) *
      (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := rfl
end GlobalTheory.CMVal
