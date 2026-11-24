-- Prove2me | solution 1 for GlobalTheory.LatPair.resChar_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:46.476123+00:00
-- url     : https://prove2.me/submissions/6288284e-28c9-44b1-87a5-949d4657fb1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Theorems.Thm_GlobalTheory_LatPair_resChar_residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
open SplitWeil
namespace GlobalTheory.LatPair
theorem _root_.solution {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) : resChar ψ hψ q ≠ 1 := by
  intro h
  have h0 : valuation k (q.1 : k) ≠ 0 := (Valuation.ne_zero_iff _).2 q.ne_zero
  have h1 : valuation k q.inv ≤ valuation k ((1 : kˣ) : k) := (hψ q.inv).1 fun y hy => by
    have hy' : (q.1 : k) * y ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_mul]
      rw [Unif.inv, map_inv₀] at hy
      exact (mul_le_mul_right hy _).trans_eq (mul_inv_cancel₀ h0)
    have := resChar_residue hψ q ⟨_, hy'⟩
    rw [h, AddChar.one_apply, Unif.inv, inv_mul_cancel_left₀ q.ne_zero] at this
    exact Circle.ext this.symm
  have h2 : q.inv ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by simpa using h1)
  exact q.2.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h2⟩ (Subtype.ext (mul_inv_cancel₀ q.ne_zero)))
end GlobalTheory.LatPair
