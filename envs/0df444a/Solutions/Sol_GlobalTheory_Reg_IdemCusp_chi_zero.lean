-- Prove2me | solution 1 for GlobalTheory.Reg.IdemCusp.chi_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:02.080263+00:00
-- url     : https://prove2.me/submissions/b13a2fae-316e-450b-83db-45e766d497c6

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

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.IdemCusp
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Reg.IdemCusp
theorem _root_.solution (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ 0 γ = 1 := by
  have hsq : X.χ 0 γ * X.χ 0 γ = X.χ 0 γ := by
    have h := X.χ_add 0 0 γ hγ
    rw [add_zero] at h
    exact h.symm
  obtain ⟨n, hn, hpow⟩ := X.χ_fin 0
  have hne : X.χ 0 γ ≠ 0 := by
    intro h0
    have h := hpow γ hγ
    rw [h0, zero_pow hn.ne'] at h
    exact zero_ne_one h
  exact mul_left_cancel₀ hne (by rw [hsq, mul_one])
end GlobalTheory.Reg.IdemCusp
