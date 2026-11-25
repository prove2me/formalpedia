-- Prove2me | solution 1 for GlobalTheory.TupleSumPos.exists_generators_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:13:03.4052+00:00
-- url     : https://prove2.me/submissions/b93fc8d6-fbb6-4815-9330-626a23049a3c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorsLattice
import Theorems.Thm_GlobalTheory_TupleSumPos_exists_generators_mod
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
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
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open scoped TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.TupleSumPos
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.TupleSumPos
theorem _root_.solution {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (h : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ e : Fin n → Λ, ∀ x : Λ, ∃ (c : Fin n → 𝓞 E) (y : Λ), x = ∑ k, c k • e k + (5 : 𝓞 E) • y := by
  have : IsLocalizedModule (𝓞 E)⁰ Λ.subtype :=
    { map_units := fun s => by
        have := isLocalizedModule_id (𝓞 E)⁰ (Fin n → E) E
        exact IsLocalizedModule.map_units (S := (𝓞 E)⁰) (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] _) s
      surj := fun y => by
        have hy : y ∈ Submodule.span E (Λ : Set (Fin n → E)) := h ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
      exists_of_eq := fun h => ⟨1, by simpa using h⟩ }
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  have : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ Ideal.span {(5 : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simp)
  refine exists_generators_mod (𝓞 E) Λ 5 n ?_
  rw [← IsLocalizedModule.finrank_eq (𝓞 E)⁰ Λ.subtype le_rfl,
    ← IsLocalization.finrank_eq E (𝓞 E)⁰ le_rfl]
  simp
end GlobalTheory.TupleSumPos
