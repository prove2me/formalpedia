-- Prove2me | solution 1 for GlobalTheory.CMVal.term_mul_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:19.784515+00:00
-- url     : https://prove2.me/submissions/c8b83c93-19d6-4c1b-9667-86de5700e04c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_GlobalTheory_CMVal_hasInfRatio_iff
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
theorem _root_.solution {χ : HChar E} {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    (h : HasInfRatio χ φ fun i => (κ i : ℤ) + s) (a : Eˣ) :
    term φ (2 * s) κ 0 a * (((χ.inf a : ℂˣ) : ℂ) * ∏ i, (φ i a * starRingEnd ℂ (φ i a)) ^ s) = 1 := by
  rw [(hasInfRatio_iff χ φ _).1 h a]
  unfold term
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  have h1 : φ i a ≠ 0 := by simp
  have h2 : starRingEnd ℂ (φ i a) ≠ 0 := by simp
  rw [← Nat.cast_add]
  simp only [mul_zero, Complex.cpow_zero, mul_one, zpow_natCast, inv_pow, div_pow]
  field_simp
  ring
end GlobalTheory.CMVal
