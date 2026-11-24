-- Prove2me | solution 1 for GlobalTheory.isLattice_fractionalIdeal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:47.592705+00:00
-- url     : https://prove2.me/submissions/62158dd5-d3cf-4162-8e21-9bcec5eda654

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [IsCMField E]
namespace GlobalTheory
theorem _root_.solution {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0)
    {Λ : Submodule (𝓞 E) (Fin r → E)} (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice ((a : Submodule (𝓞 E) E) • Λ) := by
  constructor
  · obtain ⟨s, hs⟩ := FractionalIdeal.fg_of_isUnit a ha.isUnit
    obtain ⟨t, ht⟩ := hΛ.1
    classical
    refine ⟨Finset.image₂ (· • ·) s t, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨α, hα, y, hy, rfl⟩ := Finset.mem_image₂.1 hx
      exact Submodule.smul_mem_smul (hs ▸ Submodule.subset_span hα)
        (ht ▸ Submodule.subset_span hy)
    · rw [Submodule.smul_le, ← hs, ← ht]
      intro α hα y hy
      induction hα using Submodule.span_induction with
      | mem α hα =>
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image₂_of_mem hα hy))
        | zero => simp
        | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
        | smul c y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ c hy
      | zero => simp
      | add α β _ _ hα hβ => rw [add_smul]; exact add_mem hα hβ
      | smul c α _ hα => rw [smul_assoc]; exact Submodule.smul_mem _ c hα
  · obtain ⟨α, hα0, hα⟩ : ∃ α : E, α ≠ 0 ∧ α ∈ a := by
      by_contra h
      push Not at h
      exact ha (FractionalIdeal.eq_zero_iff.2 fun x hx => by_contra fun h0 => h x h0 hx)
    rw [eq_top_iff, ← hΛ.2, Submodule.span_le]
    intro y hy
    have : y = α⁻¹ • α • y := by rw [smul_smul, inv_mul_cancel₀ hα0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.smul_mem_smul hα hy))
end GlobalTheory
