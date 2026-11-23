-- Prove2me | solution 1 for GlobalTheory.CMVal.finPart_mul_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:19.575634+00:00
-- url     : https://prove2.me/submissions/3e734524-d284-4fc1-912e-bbe8b8ece6d1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_infDiag_eq
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
theorem _root_.solution (χ : HChar E) (k : Eˣ) :
    finPart χ (Units.map (algebraMap E (Af E)).toMonoidHom k) * χ.inf k = 1 := by
  rw [← χ.2.2 k]
  show χ.1 _ * χ.1 (infDiag k) = _
  rw [← map_mul, infDiag_eq]
  congr 1
  ext : 1
  apply Prod.ext
  · show 1 * _ = _
    rw [one_mul]; rfl
  · show _ * 1 = _
    rw [mul_one]; rfl
end GlobalTheory.CMVal
