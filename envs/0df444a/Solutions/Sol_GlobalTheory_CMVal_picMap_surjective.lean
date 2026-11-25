-- Prove2me | solution 1 for GlobalTheory.CMVal.picMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:51.710844+00:00
-- url     : https://prove2.me/submissions/1e069070-d568-4e6e-b59d-1bdb5014e1fd

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
theorem _root_.solution {c c' : Ideal (OF E)} (h : c' ≤ c) : Function.Surjective (picMap h) := fun q => by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨QuotientGroup.mk y, rfl⟩
end GlobalTheory.CMVal
