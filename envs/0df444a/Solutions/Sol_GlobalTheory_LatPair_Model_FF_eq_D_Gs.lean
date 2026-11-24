-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.FF_eq_D_Gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:12:02.622672+00:00
-- url     : https://prove2.me/submissions/6c671b16-4abc-41d9-84af-d24e43de1cac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_Model_sum_stable_eq_zero
import Theorems.Thm_GlobalTheory_LatPair_D_apply
import Theorems.Thm_GlobalTheory_LatPair_FF_apply
import Theorems.Thm_GlobalTheory_LatPair_Gs_apply
import Theorems.Thm_GlobalTheory_LatPair_cross_dia_right


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
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.LatPair.Model
theorem _root_.solution (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    FF q χ φ = D q (Gs χ φ) := by
  classical
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ext P₁
  rw [FF_apply, D_apply, ← Finset.sum_filter_add_sum_filter_not _ (fun P => cross q P₁ P = 0)]
  have h0 : ∑ P ∈ withLat P₁.ker with cross q P₁ P = 0, χ (cross q P₁ P) • φ P = 0 := by
    rw [Finset.sum_congr rfl (g := φ) fun P hP => by simp [(Finset.mem_filter.1 hP).2]]
    refine sum_stable_eq_zero h _ fun c P => ?_
    simp only [Finset.mem_filter, mem_withLat, Pair.dia_lat]
    exact and_congr_right fun hP => by simp [cross_dia_right q hP]
  rw [h0, zero_add]
  simp only [Gs_apply]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun z _ => z.2 • z.1) ?_ ?_ ?_ ?_
  · rintro ⟨P, c⟩ hz
    simp only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz
    simp [hz.1, cross_dia_right q hz.1, hz.2]
  · rintro ⟨P, c⟩ hz ⟨P', c'⟩ hz' e
    simp only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz hz' e
    have := congrArg (cross q P₁) e
    rw [cross_dia_right q hz.1, cross_dia_right q hz'.1, hz.2, hz'.2, mul_one, mul_one, Units.val_inj] at this
    subst this
    rw [MulAction.injective c e]
  · intro P hP
    simp only [Finset.mem_filter, mem_withLat] at hP
    refine ⟨((Units.mk0 _ hP.2)⁻¹ • P, Units.mk0 _ hP.2), ?_, smul_inv_smul _ _⟩
    simp [hP.1, cross_dia_right q hP.1, hP.2]
  · rintro ⟨P, c⟩ hz
    simp only [Finset.mem_product, Finset.mem_filter, mem_withLat, Finset.mem_univ, and_true] at hz
    simp [cross_dia_right q hz.1, hz.2]
end GlobalTheory.LatPair.Model
