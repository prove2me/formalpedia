-- Prove2me | solution 1 for GlobalTheory.PairOp.Gs_mul_GsStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:07.86002+00:00
-- url     : https://prove2.me/submissions/eb8f7ff4-2099-4d67-98a4-78d960510436

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_sum_units_char
import Theorems.Thm_GlobalTheory_LatPair_GsStar_apply
import Theorems.Thm_GlobalTheory_LatPair_Gs_apply
import Theorems.Thm_GlobalTheory_LatPair_Nm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
namespace GlobalTheory.PairOp
theorem _root_.solution (hχ : χ ≠ 1) :
    (Gs χ * GsStar χ : Module.End ℂ (Form k n M)) = (resCard k : ℂ) • 1 - Nm := by
  classical
  letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _
  refine LinearMap.ext fun φ => funext fun P => ?_
  rw [Module.End.mul_apply, Gs_apply, LinearMap.sub_apply, Pi.sub_apply, Nm_apply, LinearMap.smul_apply,
    Pi.smul_apply, Module.End.one_apply]
  simp only [GsStar_apply, Finset.smul_sum, smul_smul]
  have hre : ∀ c : 𝓀[k]ˣ, ∑ d : 𝓀[k]ˣ, (χ c * χ (-(d : 𝓀[k]))) • φ ((d⁻¹ * c) • P) =
      ∑ u : 𝓀[k]ˣ, χ (c * (1 - ((u⁻¹ : 𝓀[k]ˣ) : 𝓀[k]))) • φ (u • P) := by
    intro c
    refine Fintype.sum_equiv ⟨fun d => d⁻¹ * c, fun u => c * u⁻¹, fun d => by simp, fun u => by simp⟩ _ _
      fun d => ?_
    simp only [Equiv.coe_fn_mk, ← AddChar.map_add_eq_mul]
    congr 2
    simp [_root_.mul_inv_rev, sub_eq_add_neg]
    rw [mul_add, mul_one, mul_neg, ← mul_assoc, mul_inv_cancel₀ c.ne_zero, one_mul]
  simp only [hre]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, sum_units_char hχ, sub_smul, Finset.sum_sub_distrib, one_smul, sub_eq_zero,
    ite_smul, zero_smul]
  rw [Finset.sum_eq_single (1 : 𝓀[k]ˣ)]
  · simp
  · intro u _ hu
    rw [if_neg]
    intro h0
    apply hu
    ext
    have : ((u⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) = 1 := by
      exact h0.symm
    simpa using this
  · simp
end GlobalTheory.PairOp
