-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_continuous_axial_sections
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:39:24.961404+00:00
-- url     : https://prove2.me/submissions/37f68020-7814-4270-a657-1dd881c8f14a

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_axial_boundary_null

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVRadial
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus

lemma isClosed_volumeSupport (E : Set Torus) : IsClosed (volumeSupport E) :=
  Measure.isClosed_support

lemma isOpen_openRepresentative (E : Set Torus) : IsOpen (openRepresentative E) :=
  (isClosed_volumeSupport Eᶜ).isOpen_compl

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVSharpUpperBound
attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace CubicTorus.UpperComparison

lemma continuous_tubeSplit_symm : Continuous tubeSplit.symm := by
  apply (PiLp.homeomorph 2 (fun _ : Fin 3 ↦ ℝ)).continuous_symm.comp
  apply continuous_pi
  intro i
  change Continuous (fun p : ℝ × Plane ↦ tubeSplit.symm p i)
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [tubeSplit_symm_zero] using (continuous_fst : Continuous (fun p : ℝ × Plane ↦ p.1))
  · simp_rw [tubeSplit_symm_succ]
    fun_prop

end CubicTorus.UpperComparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_AxialSectionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_axialSplit_symm (i : Fin 3) : Continuous (axialSplit i).symm :=
  (coverCoordinatePermute (Equiv.swap 0 i)).symm.continuous.comp UpperComparison.continuous_tubeSplit_symm

lemma transverseSquare_subset_ball : transverseSquare⊆Metric.closedBall (0 : Plane) 2 := by
  intro y hy
  rw [Metric.mem_closedBall,dist_zero_right]
  have hh : ‖y‖^2≤2 := by
    rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two]
    have h0 := hy 0
    have h1 := hy 1
    simp only [Real.norm_eq_abs,sq_abs]
    nlinarith [sq_nonneg (y 0),sq_nonneg (y 1)]
  nlinarith [norm_nonneg y]

lemma volume_transverseSquare_lt_top : volume transverseSquare<⊤ :=
  (measure_mono transverseSquare_subset_ball).trans_lt measure_closedBall_lt_top

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Function
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axial_section_inner {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) (t c : ℝ) :
    (∫ y in transverseSquare,characteristic E (quotientMap ((axialSplit i).symm (t,y)))*c)=
      axialSectionArea E i t*c := by
  let B : Set Plane := (fun y => quotientMap ((axialSplit i).symm (t,y))) ⁻¹' E
  have hB : MeasurableSet B := hE.preimage
    (measurable_quotientMap.comp ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have he : (fun y => characteristic E (quotientMap ((axialSplit i).symm (t,y)))*c)=
      B.indicator (fun _ => c) := by
    funext y
    by_cases hy : y∈B
    · simp only [indicator_of_mem hy]
      change quotientMap ((axialSplit i).symm (t,y))∈E at hy
      simp only [characteristic,indicator_of_mem hy,one_mul]
    · simp only [indicator_of_notMem hy]
      change quotientMap ((axialSplit i).symm (t,y))∉E at hy
      simp only [characteristic,indicator_of_notMem hy,zero_mul]
  rw [he,setIntegral_indicator hB,integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_axialSectionArea_of_boundary_null {F : Set Torus}
    (hF : MeasurableSet F) (i : Fin 3)
    (hz : ∀ t : ℝ,volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier F}=0) :
    Continuous (axialSectionArea F i) := by
  have hid : axialSectionArea F i=(fun t => ∫ y in transverseSquare,
      characteristic F (quotientMap ((axialSplit i).symm (t,y)))) := by
    funext t
    simpa only [mul_one] using (axial_section_inner hF i t 1).symm
  rw [hid,continuous_iff_continuousAt]
  intro t
  apply continuousAt_of_dominated (bound := fun _ : Plane => (1 : ℝ))
  · apply Eventually.of_forall
    intro u
    exact ((measurable_characteristic hF).comp (measurable_quotientMap.comp
      ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
  · exact Eventually.of_forall fun _ => Eventually.of_forall fun y =>
      characteristic_bound F _
  · exact integrableOn_const volume_transverseSquare_lt_top.ne
  · have hnull : ∀ᵐ y : Plane,quotientMap ((axialSplit i).symm (t,y))∉frontier F := by
      rw [ae_iff]
      simpa only [not_not] using hz t
    filter_upwards [ae_restrict_of_ae hnull] with y hy
    have hc : ContinuousAt (characteristic F) (quotientMap ((axialSplit i).symm (t,y))) :=
      (continuousOn_const : ContinuousOn (fun _ : Torus => (1 : ℝ)) (interior F)).continuousAt_indicator hy
    have hg : ContinuousAt (fun u : ℝ => quotientMap ((axialSplit i).symm (u,y))) t :=
      (continuous_quotientMap.comp ((continuous_axialSplit_symm i).comp
        (continuous_id.prodMk continuous_const))).continuousAt
    exact ContinuousAt.comp (f := fun u : ℝ => quotientMap ((axialSplit i).symm (u,y))) hc hg

theorem isMinimizerAt_continuous_axial_sections_oai {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) : Continuous (axialSectionArea (openRepresentative E) i) :=
  continuous_axialSectionArea_of_boundary_null (isOpen_openRepresentative E).measurableSet i
    (isMinimizerAt_axial_boundary_null hV hE hm hμ hN hp ha hs hsg i)

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_continuous_axial_sections_oai := @OAI.CubicTorus.isMinimizerAt_continuous_axial_sections_oai
