-- Prove2me | solution 1 for GlobalTheory.CMVal.SuppAt.eq_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:08:17.07554+00:00
-- url     : https://prove2.me/submissions/9b3789fa-9eba-4073-82af-8283a03957eb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_suppAt_single
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
namespace SuppAt
theorem _root_.solution {v : HeightOneSpectrum (𝓞 E)} {y : (Af E)ˣ} (h : SuppAt v y) : y = single v (coord v y) := by
  ext : 1
  apply Subtype.ext
  funext w
  show (y : Af E) w = (single v _ : Af E) w
  by_cases hw : w = v
  · subst hw; rw [single_self, coe_coord]
  · rw [h w hw, suppAt_single v _ w hw]
end SuppAt
end GlobalTheory.CMVal
