-- Prove2me | solution 1 for GlobalTheory.CMVal.hasInfRatio_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:00.924286+00:00
-- url     : https://prove2.me/submissions/c2f8e2ae-7be5-4324-9a33-5c8c6c9b2298

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
theorem _root_.solution (χ : HChar E) (φ : I → E →+* ℂ) (m : I → ℤ) :
    HasInfRatio χ φ m ↔
      ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i (k : E) / starRingEnd ℂ (φ i (k : E))) ^ m i := by
  refine forall_congr' fun k => ?_
  have : ∀ i, (φ i (k : E) / starRingEnd ℂ (φ i (k : E))) ^ m i =
      (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ (2 * m i) := fun i => by
    have h1 : φ i k ≠ 0 := by simp
    rw [zpow_mul]
    congr 1
    rw [zpow_two, div_mul_div_comm, ← sq ((‖φ i (k : E)‖ : ℝ) : ℂ), ← Complex.mul_conj', mul_div_mul_left _ _ h1]
  simp only [this]
end GlobalTheory.CMVal
