-- Prove2me | solution 1 for GlobalTheory.CMVal.modF_unifAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:18.43207+00:00
-- url     : https://prove2.me/submissions/e65c36ca-ef04-45cc-a2c3-10639059e922

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_unifAt_spec
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_Formalism_L2_Host_unif_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 E)) : modF (unifAt v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  obtain ⟨h1, h2⟩ := unifAt_spec v
  unfold modF
  rw [finprod_eq_single _ v]
  · rw [h2, WithZero.log_exp]; simp
  · intro w hw
    rw [h1 w hw]; simp
end GlobalTheory.CMVal
