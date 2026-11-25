-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.exists_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:33.176726+00:00
-- url     : https://prove2.me/submissions/45d18222-f599-4757-968d-1aa78c72c143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open Module NumberField
open GlobalTheory.CompanionTheory.Ar.HT.LatBasic
variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
namespace GlobalTheory.CompanionTheory.Ar.HT.LatBasic
theorem _root_.solution (hv : v.Integers O) {L : Submodule O V} {x : V}
    (hx : x ∈ Submodule.span C (L : Set V)) : ∃ a : C, a ≠ 0 ∧ a • x ∈ L := by
  have key : ∀ {a a' : C} {y : V}, a' ≠ 0 → v a ≤ v a' → a' • y ∈ L → a • y ∈ L := by
    intro a a' y ha' hle hy
    obtain ⟨o, ho⟩ := hv.exists_of_le_one (r := a / a') (by
      rw [map_div₀]; exact div_le_one_of_le₀ hle zero_le)
    have := L.smul_mem o hy
    rwa [← algebraMap_smul C o, ho, smul_smul, div_mul_cancel₀ _ ha'] at this
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨a', ha', hy⟩ := hy
    rcases le_total (v a) (v a') with h | h
    · exact ⟨a, ha, by rw [smul_add]; exact L.add_mem hx (key ha' h hy)⟩
    · exact ⟨a', ha', by rw [smul_add]; exact L.add_mem (key ha h hx) hy⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    by_cases hc : c = 0
    · exact ⟨1, one_ne_zero, by simp [hc]⟩
    · exact ⟨a / c, div_ne_zero ha hc, by rwa [smul_smul, div_mul_cancel₀ _ hc]⟩
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
