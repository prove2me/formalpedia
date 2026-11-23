-- Prove2me | solution 1 for GlobalTheory.CMVal.lattice_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:37.83516+00:00
-- url     : https://prove2.me/submissions/a7fd829b-13ef-44b5-880f-f9fe87b95e92

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_mem_hatOUnits
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
theorem _root_.solution {c : Ideal (OF E)} (y : (Af E)ˣ) {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) :
    lattice c (y * u) = lattice c y := by
  ext x
  rw [mem_lattice, mem_lattice, mul_inv, Units.val_mul, ← mul_assoc]
  refine ⟨fun h => ?_, fun h => mul_mem h hu.2⟩
  have := mul_mem h (mem_hatOUnits.1 hu).1
  rwa [mul_assoc, Units.inv_mul, mul_one] at this
end GlobalTheory.CMVal
