-- Prove2me | solution 1 for GlobalTheory.FlagMahler.finite_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:10:45.311863+00:00
-- url     : https://prove2.me/submissions/a5fefb9e-b211-43cb-a0fe-55a13256ba2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TraceIntegralBasis_conj_conj
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
open GlobalTheory GlobalTheory.FlagMahler
open ReciprocityTheory.ChartRestriction.G.FD NumberField Module
open Matrix hiding col gram
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace GlobalTheory.FlagMahler
theorem _root_.solution (B : X.Ψ → ℝ) :
    {α : E | IsIntegral ℤ ((X.den : E) * α) ∧ ∀ τ : X.Ψ, ‖τ.1 α‖ ≤ B τ}.Finite := by
  have hd : (X.den : E) ≠ 0 := by exact_mod_cast X.den_ne
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ
    (∑ τ : X.Ψ, ‖τ.1 (X.den : E)‖ * |B τ|)
  refine (hfin.preimage (f := fun α => (X.den : E) * α)
    (fun a _ b _ h => mul_left_cancel₀ hd h)).subset ?_
  rintro α ⟨h1, h2⟩
  have key : ∀ τ : X.Ψ, ‖τ.1 ((X.den : E) * α)‖ ≤ ∑ τ : X.Ψ, ‖τ.1 (X.den : E)‖ * |B τ| := by
    intro τ
    rw [map_mul, norm_mul]
    refine (mul_le_mul_of_nonneg_left ((h2 τ).trans (le_abs_self _)) (norm_nonneg _)).trans ?_
    exact Finset.single_le_sum (f := fun τ : X.Ψ => ‖τ.1 (X.den : E)‖ * |B τ|)
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  refine ⟨h1, fun φ => ?_⟩
  by_cases hφ : φ ∈ X.Ψ
  · exact key ⟨φ, hφ⟩
  · have h3 : ComplexEmbedding.conjugate φ ∈ X.Ψ :=
      (X.cmType _).mpr (by rw [TraceIntegralBasis.conj_conj]; exact hφ)
    have h4 := key ⟨_, h3⟩
    simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h4
    exact h4
end GlobalTheory.FlagMahler
