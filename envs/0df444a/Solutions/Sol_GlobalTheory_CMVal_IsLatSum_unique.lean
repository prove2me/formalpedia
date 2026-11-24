-- Prove2me | solution 1 for GlobalTheory.CMVal.IsLatSum.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:28:01.849068+00:00
-- url     : https://prove2.me/submissions/d43ba1bf-e29d-4cd9-9f45-582cfd3da9db

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_ExpAt_unique
import Theorems.Thm_GlobalTheory_CMVal_entire_eq_of_halfPlane
import Theorems.Thm_GlobalTheory_CMVal_IsHeckeL_unique
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
namespace IsLatSum
theorem _root_.solution {φ : I → E →+* ℂ} {k : ℕ} {κ : I → ℕ} {L : Set E} {f g : ℂ → ℂ}
    (hf : IsLatSum φ k κ L f) (hg : IsLatSum φ k κ L g) : f = g :=
  entire_eq_of_halfPlane hf.1 hg.1 (1 - (k : ℝ) / 2) fun s hs =>
    (hf.2 s (by linarith)).unique (hg.2 s (by linarith))
end IsLatSum
end GlobalTheory.CMVal
