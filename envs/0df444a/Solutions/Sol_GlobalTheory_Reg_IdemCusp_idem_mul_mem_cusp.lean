-- Prove2me | solution 1 for GlobalTheory.Reg.IdemCusp.idem_mul_mem_cusp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:18:32.2789+00:00
-- url     : https://prove2.me/submissions/91e0ce36-d12d-4722-8716-1cf4ffc0cbbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspCoefficientFlow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_EmbeddingHermitianPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IdemMulMemCusp
import Theorems.Thm_GlobalTheory_Reg_IdemCusp_mul_mem_holSub
import Theorems.Thm_GlobalTheory_Reg_IdemCusp_isIdemFn_of_isSec
import Theorems.Thm_GlobalTheory_Reg_IdemCusp_rdU_mul
import Theorems.Thm_GlobalTheory_Reg_IdemCusp_laU_zero
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
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.IdemCusp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
namespace GlobalTheory.Reg.IdemCusp
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ χ ∈ sec Xo c 0 0, χ * χ = χ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, χ * g ∈ Formalism.L2.PjFree.cusp Xo c U a n := by
  intro E _ _ _ H Dw l Xo c r U hU χ hχ hi a n g hg
  have hχ' := hχ
  unfold sec secW at hχ'
  obtain ⟨hχn, hχw⟩ := hχ'
  unfold Formalism.L2.PjFree.cusp at hg ⊢
  obtain ⟨hgs, hgc⟩ := Submodule.mem_inf.mp hg
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  ·
    have hgs' := hgs
    unfold sec secW at hgs' ⊢
    obtain ⟨hgn, hgw⟩ := hgs'
    refine ⟨fun p q φ y z hyz => ?_, fun p t y y' hyy => ?_⟩
    · show χ q z * g q z = φ (χ p y * g p y)
      rw [hχn p q φ y z hyz, hgn p q φ y z hyz, map_mul]
    · show χ p y' * g p y' = _ * (χ p y * g p y)
      rw [hχw p t y y' hyy, hgw p t y y' hyy]
      have h1 : wchar (ex Dw 0 0) t = 1 := by simp [wchar, ex]
      rw [h1]
      ring
  ·
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hgc ⊢
    intro σ hσ
    have hsec := (hU σ hσ).2.2.2.2.1 0 0 (by unfold Formalism.L2.Pj.Dom; simp [antitone_const]) χ hχ
    rw [rdU_mul]
    refine mul_mem_holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (Formalism.L2.PjFree.rdU (U σ) χ)
      (fun k => ?_) (hgc σ hσ)
    apply isIdemFn_of_isSec
    · have hk := hsec k
      rwa [laU_zero] at hk
    · have hk := congrFun (rdU_mul (U σ) χ χ) k
      rw [hi] at hk
      exact hk.symm
end GlobalTheory.Reg.IdemCusp
