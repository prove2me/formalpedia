-- Prove2me | solution 1 for GlobalTheory.CMVal.mul_mem_lattice_princ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:24.990505+00:00
-- url     : https://prove2.me/submissions/a8e893ea-7fd0-4f3b-a6ee-2767621069ae

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
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
theorem _root_.solution (c : Ideal (OF E)) (y : (Af E)ˣ) (a : Eˣ) (x : E) :
    (a : E) * x ∈ lattice c (Units.map (algebraMap E (Af E)).toMonoidHom a * y) ↔ x ∈ lattice c y := by
  rw [mem_lattice, mem_lattice]
  have : algebraMap E (Af E) ((a : E) * x) * (↑(Units.map (algebraMap E (Af E)).toMonoidHom a * y)⁻¹ : Af E)
      = algebraMap E (Af E) x * (↑y⁻¹ : Af E) := by
    rw [mul_inv, ← map_inv, Units.val_mul, map_mul]
    have h1 : algebraMap E (Af E) (a : E) * (↑(Units.map (algebraMap E (Af E)).toMonoidHom a⁻¹) : Af E) = 1 := by
      show algebraMap E (Af E) (a : E) * algebraMap E (Af E) ((a⁻¹ : Eˣ) : E) = 1
      rw [← map_mul]; simp
    linear_combination (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) * h1
  rw [this]
end GlobalTheory.CMVal
