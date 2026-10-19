-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.tendsto_cyclicKernelOutput_of_cubic_dom
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:08:38.250169+00:00
-- url     : https://prove2.me/submissions/a1303885-0535-4630-a1ff-2961df7f0b54

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/CyclicSlice.lean:L49-L76
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.tendsto_cyclicKernelOutput_of_cubic_dom. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SortedWindows
import Definitions.Def_OAI_Analysis_TriangularHilbert_MaskedActual
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedCenter
import Definitions.Def_OAI_Analysis_TriangularHilbert_SelectedScale
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscretePairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_SmoothFormula
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorEnvelope
import Definitions.Def_OAI_Analysis_TriangularHilbert_ErrorPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_HardPairing
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridCell
import Definitions.Def_OAI_Analysis_TriangularHilbert_Quantization
import Definitions.Def_OAI_Analysis_TriangularHilbert_GridLine
import Definitions.Def_OAI_Analysis_TriangularHilbert_BoundedBox
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledOutput
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicSlice
import Theorems.Thm_OAI_TriangularHilbert_tendsto_integral_product_bounded_kernel

-- ---- from OAI.Analysis.TriangularHilbert.HardScalar ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma abs_hardKernel_le {r R : ℝ} (hr : 0 < r) (hb : r ≤ R) (t : ℝ) : |hardKernel r R t| ≤ 1/r := by
  unfold hardKernel
  by_cases hrt : r < |t|
  · by_cases hRt : R < |t|
    · simp [hrt,hRt,hr.le]
    · simp only [hrt,hRt,ite_true,ite_false,sub_zero,abs_div,abs_one]
      exact one_div_le_one_div_of_le hr hrt.le
  · have hRt : ¬R < |t| := fun h => hrt (hb.trans_lt h)
    simp [hrt,hRt,hr.le]

lemma measurable_hardKernel (r R : ℝ) : Measurable (hardKernel r R) := by
  unfold hardKernel
  exact ((measurable_const.ite (measurableSet_lt measurable_const measurable_abs) measurable_const).sub
    (measurable_const.ite (measurableSet_lt measurable_const measurable_abs) measurable_const)).div measurable_id

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicSlice ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology
noncomputable section

lemma hardKernel_shift_support {r R : ℝ} (hr : r ≤ R) (a c : ℝ)
    (hc : c ∉ Set.Icc (-(R+|a|)) (R+|a|)) : hardKernel r R (a+c) = 0 := by
  have hR : R < |a+c| := by
    by_contra hR
    apply hc
    apply abs_le.mp
    have hh : |c| ≤ |a+c|+|a| := by
      calc
        |c| = |(a+c)-a| := by congr 1; ring
        _ ≤ |a+c|+|a| := abs_sub _ _
    linarith [le_of_not_gt hR]
  simp only [hardKernel,hr.trans_lt hR,hR,ite_true,sub_self,zero_div]

lemma tendsto_cyclicKernelOutput_of_cubic_dom (B C : ℝ×ℝ → ℂ) (F G : ℕ → ℝ×ℝ → ℂ)
    (hF : ∀ n, Continuous (F n)) (hG : ∀ n, Continuous (G n))
    {D E : ℝ×ℝ → ℝ} (hD : Integrable D) (hE : Integrable E)
    (hb : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖F n z‖^3 ≤ D z) ∧ Tendsto (fun n => F n z) atTop (𝓝 (B z)))
    (hc : ∀ᵐ z : ℝ×ℝ, (∀ n, ‖G n z‖^3 ≤ E z) ∧ Tendsto (fun n => G n z) atTop (𝓝 (C z))) :
    ∀ᵐ z : ℝ×ℝ, ∀ r R : ℝ, 0 < r → r ≤ R →
      Tendsto (fun n => cyclicKernelOutput (F n) (G n) (hardKernel r R) z) atTop
        (𝓝 (cyclicKernelOutput B C (hardKernel r R) z)) := by
  have hb' := ae_ae_of_ae_prod hb
  have hc' := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae hc)
  filter_upwards [quasiMeasurePreserving_snd.ae hb',quasiMeasurePreserving_fst.ae hc',
    quasiMeasurePreserving_snd.ae hD.prod_right_ae,quasiMeasurePreserving_fst.ae hE.prod_left_ae]
    with z hzb hzc hzD hzE
  intro r R hr hR
  apply tendsto_integral_product_bounded_kernel _ _ _ _ _
    (s := Set.Icc (-(R+|z.1+z.2|)) (R+|z.1+z.2|)) (L := 1/r)
    (fun n => ((hF n).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun n => ((hG n).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    ((measurable_hardKernel _ _).comp (measurable_const.add measurable_id)) hzD hzE
  · filter_upwards [hzb,hzc] with c hb hc
    exact fun n => ⟨hb.1 n,hc.1 n⟩
  · filter_upwards [hzb,hzc] with c hb hc
    exact ⟨hb.2,hc.2⟩
  · exact measurableSet_Icc
  · exact isCompact_Icc.measure_ne_top
  · exact show 0 ≤ 1/r by positivity
  · exact fun c => abs_hardKernel_le hr hR _
  · exact hardKernel_shift_support hR (z.1+z.2)
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.tendsto_cyclicKernelOutput_of_cubic_dom := @_root_.OAI.TriangularHilbert.Heat.tendsto_cyclicKernelOutput_of_cubic_dom
