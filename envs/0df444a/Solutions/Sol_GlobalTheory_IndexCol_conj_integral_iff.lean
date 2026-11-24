-- Prove2me | solution 1 for GlobalTheory.IndexCol.conj_integral_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:26.926841+00:00
-- url     : https://prove2.me/submissions/0d3330a7-c877-45fe-a0ac-7f7555b4b5ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence
import Theorems.Thm_GlobalTheory_IndexCol_conj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndexCol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.IndexCol
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) (z : Matrix ι ι k) (hz : ∀ r s, z r s ∈ 𝒪[k]) :
    (∀ r s, ((diagGL (Pi.mulSingle t ϖ : ι → kˣ)).val * z * ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val) r s ∈ 𝒪[k]) ↔
      ∀ r, r ≠ t → valuation k (z r t) < 1 := by
  have hv : valuation k (ϖ : k) ≠ 0 := by simp
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  simp only [conj_apply]
  constructor
  · intro h r hr
    have h1 := h r t
    simp only [Pi.mulSingle_apply, hr, if_false, if_true, Units.val_one, one_mul] at h1
    have h2 : valuation k (z r t * ((ϖ⁻¹ : kˣ) : k)) ≤ 1 := h1
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h2
    have h3 : valuation k (z r t) ≤ valuation k (ϖ : k) := by
      have := mul_le_mul_of_nonneg_right h2 (zero_le' (a := valuation k (ϖ : k)))
      rwa [mul_assoc, inv_mul_cancel₀ hv, mul_one, one_mul] at this
    exact h3.trans_lt hlt
  · intro h r s
    by_cases hr : r = t <;> by_cases hs : s = t
    · subst hr; subst hs
      simp only [Pi.mulSingle_eq_same]
      rw [mul_comm (ϖ : k), mul_assoc, Units.mul_inv, mul_one]; exact hz _ _
    · subst hr
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_apply, hs, if_false, inv_one, Units.val_one, mul_one]
      exact mul_mem hϖ.mem (hz _ _)
    · subst hs
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_apply, hr, if_false, Units.val_one, one_mul]
      show valuation k _ ≤ 1
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      have h3 : valuation k (z r s) ≤ valuation k (ϖ : k) := by
        rw [hϖ, le_uniformizer_iff]; exact h r hr
      calc valuation k (z r s) * (valuation k (ϖ : k))⁻¹ ≤ valuation k (ϖ : k) * (valuation k (ϖ : k))⁻¹ :=
            mul_le_mul_of_nonneg_right h3 zero_le'
        _ = 1 := mul_inv_cancel₀ hv
    · simp only [Pi.mulSingle_apply, hr, hs, if_false, inv_one, Units.val_one, one_mul, mul_one]
      exact hz _ _
end GlobalTheory.IndexCol
