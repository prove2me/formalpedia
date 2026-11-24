-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.SelfDual.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:37:54.915801+00:00
-- url     : https://prove2.me/submissions/bc0757a0-9ea4-4b82-a3d3-c91cb3b3ab11

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_inv_one_sub_mem
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_add
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_smul
import Theorems.Thm_GlobalTheory_UnitarySwap_SelfDual_pair
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {V : Type} [AddCommGroup V] [Module L V] {σ : L →+* L}
variable {B : V →ₛₗ[σ] V →ₗ[L] L} {W : Submodule L V} {Λ : Set V}
namespace GlobalTheory.UnitarySwap
namespace SelfDual
theorem _root_.solution (h : SelfDual B W Λ) (hσ : ∀ x ∈ intL L, σ x ∈ intL L)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) (hxy : B x y = 1) (hyx : B y x = 1)
    (hs : Valued.v (B x x * B y y) < 1) {v : V} (hv : v ∈ Λ) :
    ∃ c ∈ intL L, ∃ d ∈ intL L, ∃ v₀ ∈ Λ, B x v₀ = 0 ∧ B y v₀ = 0 ∧ v = c • x + d • y + v₀ := by
  obtain ⟨h0, hi⟩ := inv_one_sub_mem hs
  have hc : (B y v - B y y * B x v) * (1 - B x x * B y y)⁻¹ ∈ intL L :=
    mul_mem (sub_mem (h.pair hy hv) (mul_mem (h.pair hy hy) (h.pair hx hv))) hi
  have hd : (B x v - B x x * B y v) * (1 - B x x * B y y)⁻¹ ∈ intL L :=
    mul_mem (sub_mem (h.pair hx hv) (mul_mem (h.pair hx hx) (h.pair hy hv))) hi
  refine ⟨_, hc, _, hd, v + ((-((B y v - B y y * B x v) * (1 - B x x * B y y)⁻¹)) • x +
    (-((B x v - B x x * B y v) * (1 - B x x * B y y)⁻¹)) • y),
    h.add hv (h.add (h.smul hσ (neg_mem hc) hx) (h.smul hσ (neg_mem hd) hy)), ?_, ?_, ?_⟩
  · simp only [map_add, map_smul, smul_eq_mul, hxy]
    linear_combination (-(B x v)) * mul_inv_cancel₀ h0
  · simp only [map_add, map_smul, smul_eq_mul, hyx]
    linear_combination (-(B y v)) * mul_inv_cancel₀ h0
  · module
end SelfDual
end GlobalTheory.UnitarySwap
