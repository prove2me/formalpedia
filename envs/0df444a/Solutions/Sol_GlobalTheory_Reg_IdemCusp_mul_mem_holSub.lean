-- Prove2me | solution 1 for GlobalTheory.Reg.IdemCusp.mul_mem_holSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:02:56.525408+00:00
-- url     : https://prove2.me/submissions/f9af2a70-ae1d-4777-84b2-8d8386afd62c

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
import Theorems.Thm_GlobalTheory_Reg_IdemCusp_mul_mem_SS

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
theorem _root_.solution {ι : Type} (X : ι → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    (χ : Formalism.L2.PjFree.FDSec X) (hχ : ∀ k, IsIdemFn (X k) (χ k)) {P : Formalism.L2.PjFree.FDSec X}
    (hP : P ∈ Formalism.L2.PjFree.holSub X la) : (fun k => χ k * P k) ∈ Formalism.L2.PjFree.holSub X la := by
  have hle : (Formalism.L2.PjFree.holSub X la).map (mulL X χ) ≤ Formalism.L2.PjFree.holSub X la := by
    unfold Formalism.L2.PjFree.holSub
    rw [Submodule.map_span_le]
    intro Q hQ
    exact Submodule.subset_span fun k => mul_mem_SS (X k) (hχ k) (la k) (hQ k)
  exact hle (Submodule.mem_map_of_mem hP)
end GlobalTheory.Reg.IdemCusp
