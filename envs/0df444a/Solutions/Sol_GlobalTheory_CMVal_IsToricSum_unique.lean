-- Prove2me | solution 1 for GlobalTheory.CMVal.IsToricSum.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:54:02.902379+00:00
-- url     : https://prove2.me/submissions/e9ff226a-8344-4c64-8135-9cb76f5b0c7c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_ExpAt_unique
import Theorems.Thm_GlobalTheory_CMVal_IsHeckeL_unique
import Theorems.Thm_GlobalTheory_CMVal_IsLatSum_unique
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
namespace IsToricSum
theorem _root_.solution {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ : HChar E}
    {T T' : ℂ} (h : IsToricSum φ s κ c χ T) (h' : IsToricSum φ s κ c χ T') : T = T' := by
  obtain ⟨_, S, hS, rfl⟩ := h
  obtain ⟨_, S', hS', rfl⟩ := h'
  have : S = S' := funext fun q => (hS q).unique (hS' q)
  rw [this]
end IsToricSum
end GlobalTheory.CMVal
