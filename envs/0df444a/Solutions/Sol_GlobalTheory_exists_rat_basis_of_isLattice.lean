-- Prove2me | solution 1 for GlobalTheory.exists_rat_basis_of_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:00.438206+00:00
-- url     : https://prove2.me/submissions/d3f49b00-70a8-4af5-ab3a-dd0893c37528

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_exists_smul_mem
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
variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}
omit [IsCMField E]
namespace GlobalTheory
theorem _root_.solution (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ (Fin r → E)),
      Submodule.span ℤ (Set.range b) = Λ.restrictScalars ℤ := by
  have : (Λ.restrictScalars ℤ).IsLattice ℚ := by
    constructor
    · have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hΛ.1
      have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
      exact Module.Finite.iff_fg.1 this
    · rw [eq_top_iff]
      intro x _
      obtain ⟨d, hd, hdx⟩ := exists_smul_mem (F := E) Λ (x := x) (hΛ.2 ▸ Submodule.mem_top)
      obtain ⟨e, he⟩ : ∃ e : 𝓞 E, e * d = (Algebra.norm ℤ d : 𝓞 E) := by
        have := Ideal.absNorm_mem (Ideal.span {d})
        rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton'] at this
        obtain ⟨e, he⟩ := this
        rcases Int.natAbs_eq (Algebra.norm ℤ d) with h | h
        · exact ⟨e, by rw [he, h]; simp⟩
        · exact ⟨-e, by rw [neg_mul, he, h]; simp⟩
      have hn : (Algebra.norm ℤ d : ℚ) ≠ 0 := by
        exact_mod_cast Algebra.norm_ne_zero_iff.2 hd
      have h1 : (Algebra.norm ℤ d : ℚ) • x ∈ Λ := by
        have := Λ.smul_mem e hdx
        rwa [smul_smul, he, Int.cast_smul_eq_zsmul, ← Int.cast_smul_eq_zsmul ℚ] at this
      rw [← inv_smul_smul₀ hn x]
      exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  let b := Module.finBasis ℤ (Λ.restrictScalars ℤ)
  refine ⟨_, b.extendOfIsLattice ℚ, ?_⟩
  have h1 : Set.range (b.extendOfIsLattice ℚ) = (Λ.restrictScalars ℤ).subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    exact funext fun i => b.extendOfIsLattice_apply ℚ i
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
end GlobalTheory
