-- Prove2me | solution 1 for GlobalTheory.CMVal.out_mem_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:50.499989+00:00
-- url     : https://prove2.me/submissions/3e12e2d0-bd22-4237-b028-fd135e8c1089

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_algebraMap_mem_orderC
import Theorems.Thm_GlobalTheory_CMVal_mul_mem_lattice
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
theorem _root_.solution {c : Ideal (OF E)} {y : (Af E)ˣ} (q : modUnits (lattice c y)) :
    q.1.out ∈ lattice c y ∧ q.1.out ≠ 0 := by
  obtain ⟨x, hx, h0, hq⟩ := q.2
  obtain ⟨u, hu⟩ : (unitRel (E := E)).r x q.1.out := Quotient.exact (hq.trans (Quotient.out_eq _).symm)
  rw [hu]
  refine ⟨mul_mem_lattice (algebraMap_mem_orderC c _) hx, mul_ne_zero ?_ h0⟩
  exact (u.isUnit.map (algebraMap (OF E) E)).ne_zero
end GlobalTheory.CMVal
