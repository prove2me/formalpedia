-- Prove2me | solution 1 for GlobalTheory.CMVal.LatBij.toIdele_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:41.272051+00:00
-- url     : https://prove2.me/submissions/1fb3a273-654e-43ba-856e-e398ff64e22b

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdelicRingClassLatticeOneEqOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLatticePointsIntegralIdelesEquiv
import Theorems.Thm_GlobalTheory_CMVal_LatBij_coe_diag
import Theorems.Thm_GlobalTheory_CMVal_LatBij_diag_unit_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.LatBij
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.LatBij
theorem _root_.solution (c : Ideal (OF E)) : Function.Surjective (toIdele c) := by
  rintro ⟨_, y, rfl, hy⟩
  let q : PicO c := QuotientGroup.mk y⁻¹
  have hq : (q.out)⁻¹ * y⁻¹ ∈ princ ⊔ hatOUnits c := QuotientGroup.eq.1 (Quotient.out_eq q)
  obtain ⟨_, ⟨α, rfl⟩, u, hu, h⟩ := Subgroup.mem_sup.1 hq
  change diag α * u = _ at h
  have h1 : diag α⁻¹ * q.out⁻¹ = y * u := by
    rw [map_inv, eq_mul_inv_iff_mul_eq.1 h |>.symm, mul_assoc, inv_mul_cancel_left, mul_comm]
  have hx : ((α⁻¹ : Eˣ) : E) ∈ lattice c q.out := by
    rw [mem_lattice, ← coe_diag, ← Units.val_mul, h1, Units.val_mul]
    exact mul_mem hy hu.1
  let a : modUnits (lattice c q.out) := ⟨Quotient.mk _ ((α⁻¹ : Eˣ) : E), _, hx, Units.ne_zero _, rfl⟩
  obtain ⟨w, hw⟩ : (unitRel (E := E)).r ((α⁻¹ : Eˣ) : E) a.1.out := Quotient.exact (Quotient.out_eq a.1).symm
  have hr : rep a = Units.map (algebraMap (OF E) E).toMonoidHom w * α⁻¹ := Units.ext hw
  refine ⟨⟨q, a⟩, Subtype.ext ?_⟩
  refine (QuotientGroup.eq.2 ?_ : (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits c) = _).symm
  change y⁻¹ * (diag (rep a) * q.out⁻¹) ∈ _
  rw [hr, map_mul, mul_assoc, h1, mul_left_comm, inv_mul_cancel_left]
  exact mul_mem (diag_unit_mem c w) hu
end GlobalTheory.CMVal.LatBij
