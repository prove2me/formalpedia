-- Prove2me | solution 1 for GlobalTheory.PrinTwo.coord_eq_of_far
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:22:00.992352+00:00
-- url     : https://prove2.me/submissions/a1888385-4627-41ed-add8-8a17a207fd15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrincipalSeriesCoordinateNearInfinity
import Theorems.Thm_GlobalTheory_PrinTwo_exists_ev_nL_eq
import Theorems.Thm_GlobalTheory_PrinTwo_bchar_one
import Theorems.Thm_GlobalTheory_PrinTwo_coordL_apply
import Theorems.Thm_GlobalTheory_PrinTwo_evL_apply
import Theorems.Thm_GlobalTheory_PrinTwo_ev_bor
import Theorems.Thm_GlobalTheory_PrinTwo_val_bor
import Theorems.Thm_GlobalTheory_PrinTwo_val_nL
import Theorems.Thm_GlobalTheory_PrinTwo_val_nU
import Theorems.Thm_GlobalTheory_PrinTwo_val_tD
import Theorems.Thm_GlobalTheory_PrinTwo_val_wE
import Theorems.Thm_GlobalTheory_PrinTwo_wE_mul_nU_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.PrinTwo.bchar_one
attribute [local simp] GlobalTheory.PrinTwo.coordL_apply
attribute [local simp] GlobalTheory.PrinTwo.evL_apply
attribute [local simp] GlobalTheory.PrinTwo.val_bor
attribute [local simp] GlobalTheory.PrinTwo.val_nL
attribute [local simp] GlobalTheory.PrinTwo.val_nU
attribute [local simp] GlobalTheory.PrinTwo.val_tD
attribute [local simp] GlobalTheory.PrinTwo.val_wE



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped Topology
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.PrinTwo
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (μ₁ μ₂ : kˣ →* ℂˣ) (f : GlobalTheory.PrinTwo.PSp μ₁ μ₂), ∃ R : kˣ, ∀ x : kˣ,
    ValuativeRel.valuation k (R : k) < ValuativeRel.valuation k (x : k) →
      GlobalTheory.PrinTwo.coord f x = GlobalTheory.PrinTwo.bchar μ₁ μ₂ (-x⁻¹) x * GlobalTheory.PrinTwo.ev f 1 := by
  intro k _ _ _ _ μ₁ μ₂ f
  obtain ⟨r, hr⟩ := exists_ev_nL_eq f
  refine ⟨r⁻¹, fun x hx => ?_⟩
  rw [coord, wE_mul_nU_eq, ev_bor, hr]
  have hx0 : (0 : ValueGroupWithZero k) < valuation k (x : k) := by simp [zero_lt_iff]
  have hr0 : (0 : ValueGroupWithZero k) < valuation k (r : k) := by simp [zero_lt_iff]
  simp only [Units.val_inv_eq_inv_val, map_inv₀] at hx ⊢
  exact (inv_lt_comm₀ hr0 hx0).mp hx
end GlobalTheory.PrinTwo
