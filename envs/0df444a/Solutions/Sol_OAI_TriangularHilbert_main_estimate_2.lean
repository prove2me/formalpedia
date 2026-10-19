-- Prove2me | solution 2 for OAI.TriangularHilbert.main_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:36:47.55838+00:00
-- url     : https://prove2.me/submissions/4a0e6ceb-4429-4376-818f-a731542047dd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Main.lean:L41-L45
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.TriangularHilbert.main_estimate.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_TriangularHilbert_main_estimate) verbatim and is proved by it.
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_RationalSup
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_SampledMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteDual
import Definitions.Def_OAI_Analysis_TriangularHilbert_DiscreteMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicMaxMoment
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicHomogeneity
import Definitions.Def_OAI_Analysis_TriangularHilbert_CyclicNorm
import Definitions.Def_OAI_Analysis_TriangularHilbert_Coordinates
import Theorems.Thm_OAI_TriangularHilbert_Heat_continuousAt_cyclicHard
import Theorems.Thm_OAI_TriangularHilbert_Heat_tendsto_cyclicKernelOutput_of_cubic_dom
import Theorems.Thm_OAI_TriangularHilbert_exists_cubic_approximation
import Theorems.Thm_OAI_TriangularHilbert_hardKernel_eq_indicator_ae
import Theorems.Thm_OAI_TriangularHilbert_lintegral_cyclicMax_moment_le

-- ---- from OAI.Analysis.TriangularHilbert.CubicProduct ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma sq_le_cube_add_one {x : ℝ} (hx : 0 ≤ x) : x^2 ≤ x^3+1 := by
  by_cases h : x ≤ 1
  · have hs := pow_le_pow_left₀ hx h 2
    nlinarith [pow_nonneg hx 3]
  · have hm := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith

lemma mul_le_cube_add_cube_add_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x*y ≤ x^3+y^3+2 := by
  nlinarith [sq_nonneg (x-y),sq_le_cube_add_one hx,sq_le_cube_add_one hy,
    pow_nonneg hx 3,pow_nonneg hy 3]

lemma norm_product_kernel_le (f g : ℝ → ℂ) (K : ℝ → ℝ) {D E : ℝ → ℝ} {L : ℝ}
    (_hL : 0 ≤ L) {c : ℝ} (hf : ‖f c‖^3 ≤ D c) (hg : ‖g c‖^3 ≤ E c)
    (hk : |K c| ≤ L) : ‖f c*g c*(K c:ℂ)‖ ≤ (D c+E c+2)*L := by
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have hp := mul_le_cube_add_cube_add_two (norm_nonneg (f c)) (norm_nonneg (g c))
  have hD : 0 ≤ D c := (pow_nonneg (norm_nonneg _) 3).trans hf
  have hE : 0 ≤ E c := (pow_nonneg (norm_nonneg _) 3).trans hg
  exact mul_le_mul (by linarith : ‖f c‖*‖g c‖ ≤ D c+E c+2) hk (abs_nonneg _) (by positivity)

lemma integrable_product_bounded_kernel (f g : ℝ → ℂ) (K : ℝ → ℝ)
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) (hK : Measurable K)
    {D E : ℝ → ℝ} (hD : Integrable D) (hE : Integrable E)
    (hbound : ∀ᵐ c : ℝ, ‖f c‖^3 ≤ D c ∧ ‖g c‖^3 ≤ E c)
    {s : Set ℝ} (hs : MeasurableSet s) (hμ : volume s ≠ ⊤) {L : ℝ} (hL : 0 ≤ L)
    (hk : ∀ c, |K c| ≤ L) (hzero : ∀ c ∉ s, K c = 0) :
    Integrable (fun c => f c*g c*(K c:ℂ)) := by
  have hb : Integrable (s.indicator (fun c => (D c+E c+2)*L)) :=
    IntegrableOn.integrable_indicator
      (((hD.integrableOn.add hE.integrableOn).add (integrableOn_const (C := (2:ℝ)) hμ)).mul_const L) hs
  apply hb.mono' ((hf.mul hg).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hK.aestronglyMeasurable))
  filter_upwards [hbound] with c hc
  by_cases hc' : c ∈ s
  · rw [Set.indicator_of_mem hc']
    exact norm_product_kernel_le f g K hL hc.1 hc.2 (hk c)
  · simp only [Pi.mul_apply,hzero c hc',Complex.ofReal_zero,mul_zero,norm_zero,Set.indicator_of_notMem hc',le_refl]

end
end TriangularHilbert
end

end OAI

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

lemma ae_cubicSliceGood (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    ∀ᵐ z : ℝ×ℝ, CubicSliceGood B C z := by
  have hb := hB.aestronglyMeasurable.prodMk_left
  have hc := hC.aestronglyMeasurable.prodMk_right
  have hbi := (hB.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0)).prod_right_ae
  have hci := (hC.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0)).prod_left_ae
  filter_upwards [quasiMeasurePreserving_snd.ae hb,quasiMeasurePreserving_fst.ae hc,
    quasiMeasurePreserving_snd.ae hbi,quasiMeasurePreserving_fst.ae hci] with z hzB hzC hiB hiC
  exact ⟨hzB,hzC,hiB,hiC⟩

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

lemma CubicSliceGood.integrable_hard {B C : ℝ×ℝ → ℂ} {z : ℝ×ℝ} (hz : CubicSliceGood B C z)
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    Integrable (fun c : ℝ => B (z.2,c)*C (c,z.1)*(hardKernel r R (z.1+z.2+c):ℂ)) := by
  apply integrable_product_bounded_kernel _ _ _ hz.1 hz.2.1
    ((measurable_hardKernel _ _).comp (measurable_const.add measurable_id)) hz.2.2.1 hz.2.2.2
    (Eventually.of_forall (fun _ => ⟨le_rfl,le_rfl⟩)) measurableSet_Icc isCompact_Icc.measure_ne_top
    (show 0 ≤ 1/r by positivity) (fun c => abs_hardKernel_le hr hR _)
  exact hardKernel_shift_support hR (z.1+z.2)

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.RationalSup ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter Heat
open scoped Topology ENNReal
noncomputable section

lemma cyclicHard_le_cyclicMax {B C : Plane → ℂ} {z : Plane} (hz : CubicSliceGood B C z)
    {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel r R) z‖ ≤ cyclicMax B C z := by
  obtain ⟨u,_,hu,htu⟩ := Real.exists_seq_rat_strictMono_tendsto r
  obtain ⟨v,_,hv,htv⟩ := Real.exists_seq_rat_strictAnti_tendsto R
  have ht := (continuousAt_cyclicHard hz hr hR).tendsto.comp (htu.prodMk_nhds htv)
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht.norm)
  filter_upwards [htu (eventually_gt_nhds hr)] with n hn
  have hq : 0 < u n ∧ u n < v n := by
    constructor
    · exact_mod_cast (show (0:ℝ) < (u n:ℝ) from hn)
    · exact_mod_cast ((hu n).trans (hR.trans (hv n)))
  exact le_iSup (fun q : RatEndpoints => ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel (q.1.1:ℝ) (q.1.2:ℝ)) z‖)
    ⟨(u n,v n),hq⟩

lemma cyclicMax_eq_iSup {B C : Plane → ℂ} {z : Plane} (hz : CubicSliceGood B C z) :
    cyclicMax B C z = ⨆ E : Endpoints, ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel E.lower E.upper) z‖ := by
  apply le_antisymm
  · apply iSup_le
    intro q
    exact le_iSup (fun E : Endpoints => ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel E.lower E.upper) z‖) q.toEndpoints
  · apply iSup_le
    intro E
    exact cyclicHard_le_cyclicMax hz E.lower_pos E.lower_lt_upper

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicMeasurable ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma measurable_cyclicKernelOutput (B C : ℝ×ℝ → ℂ) (hB : Measurable B) (hC : Measurable C)
    (K : ℝ → ℝ) (hK : Measurable K) : Measurable (cyclicKernelOutput B C K) := by
  have hm : Measurable (fun q : (ℝ×ℝ)×ℝ => B (q.1.2,q.2)*C (q.2,q.1.1)*(K (q.1.1+q.1.2+q.2):ℂ)) := by
    apply Measurable.mul
    · exact (hB.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul
        (hC.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
    · exact Complex.measurable_ofReal.comp (hK.comp
        (((measurable_fst.comp measurable_fst).add (measurable_snd.comp measurable_fst)).add measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CubicApprox ----
namespace OAI

universe uα

section
namespace TriangularHilbert
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
noncomputable section

lemma lintegral_enorm_cube {α : Type uα} [MeasurableSpace α] (f : α → ℂ) (μ : Measure α)
    (hf : AEStronglyMeasurable f μ) :
    (∫⁻ x, ‖f x‖ₑ^3 ∂μ) = eLpNorm f 3 μ ^ (3:ℕ) := by
  simpa only [ENNReal.rpow_ofNat,NNReal.coe_ofNat,ENNReal.coe_ofNat] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := (3:ℝ≥0)) (by norm_num)).symm

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicDensity ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

universe uκ

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

lemma aemeasurable_cyclic_hard (B C : ℝ×ℝ → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) : AEMeasurable (cyclicKernelOutput B C (hardKernel r R)) volume := by
  obtain ⟨F,hF,D,hD,_,hb⟩ := exists_cubic_approximation B hB
  obtain ⟨G,hG,E,hE,_,hc⟩ := exists_cubic_approximation C hC
  have ht := tendsto_cyclicKernelOutput_of_cubic_dom B C F G (fun n => (hF n).1) (fun n => (hG n).1) hD hE hb hc
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (measurable_cyclicKernelOutput (F n) (G n) (hF n).1.measurable (hG n).1.measurable _
      (measurable_hardKernel r R)).aemeasurable)
  filter_upwards [ht] with z hz
  exact hz r R hr hR

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicMaxMoment ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter Heat
open scoped Topology ENNReal
noncomputable section

lemma aemeasurable_cyclicMax (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    AEMeasurable (cyclicMax B C) volume := by
  apply AEMeasurable.iSup
  intro q
  exact (aemeasurable_cyclic_hard B C hB hC q.toEndpoints.lower_pos q.toEndpoints.lower_lt_upper.le).norm.ennreal_ofReal

end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicHomogeneity ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat Filter
open scoped ENNReal
noncomputable section

lemma cyclicKernelOutput_congr_ae {B C B' C' : Plane → ℂ}
    (hb : B =ᵐ[volume] B') (hc : C =ᵐ[volume] C') :
    ∀ᵐ z : Plane, ∀ K : ℝ → ℝ, cyclicKernelOutput B C K z = cyclicKernelOutput B' C' K z := by
  filter_upwards [quasiMeasurePreserving_snd.ae (ae_ae_of_ae_prod hb),
    quasiMeasurePreserving_fst.ae (ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae hc))]
    with z hzB hzC
  intro K
  apply integral_congr_ae
  filter_upwards [hzB,hzC] with c hB hC
  change C (c,z.1) = C' (c,z.1) at hC
  simp only [hB,hC]

lemma cyclicMax_congr_ae {B C B' C' : Plane → ℂ}
    (hb : B =ᵐ[volume] B') (hc : C =ᵐ[volume] C') :
    cyclicMax B C =ᵐ[volume] cyclicMax B' C' := by
  filter_upwards [cyclicKernelOutput_congr_ae hb hc] with z hz
  simp only [cyclicMax,hz]

lemma cyclicNorm_congr_ae {B C B' C' : Plane → ℂ}
    (hb : B =ᵐ[volume] B') (hc : C =ᵐ[volume] C') :
    cyclicNorm B C = cyclicNorm B' C' := by
  unfold cyclicNorm
  congr 1
  apply lintegral_congr_ae
  filter_upwards [cyclicMax_congr_ae hb hc] with z hz
  rw [hz]

lemma cyclicKernelOutput_smul (B C : Plane → ℂ) (u v : ℂ) (K : ℝ → ℝ) (z : Plane) :
    cyclicKernelOutput (u • B) (v • C) K z = (u*v)*cyclicKernelOutput B C K z := by
  rw [cyclicKernelOutput,cyclicKernelOutput,← integral_const_mul]
  congr 1
  funext c
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

lemma cyclicMax_smul (B C : Plane → ℂ) (u v : ℂ) (z : Plane) :
    cyclicMax (u • B) (v • C) z = (‖u‖ₑ*‖v‖ₑ)*cyclicMax B C z := by
  simp only [cyclicMax,cyclicKernelOutput_smul,ofReal_norm,enorm_mul]
  rw [ENNReal.mul_iSup]

lemma cyclicNorm_smul (B C : Plane → ℂ) (u v : ℂ) :
    cyclicNorm (u • B) (v • C) = (‖u‖ₑ*‖v‖ₑ)*cyclicNorm B C := by
  have he : (fun z : Plane => cyclicMax (u • B) (v • C) z ^ ((3:ℝ)/2)) =
      (fun z : Plane => (‖u‖ₑ*‖v‖ₑ)^((3:ℝ)/2)*cyclicMax B C z^((3:ℝ)/2)) := by
    funext z
    rw [cyclicMax_smul,ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  rw [cyclicNorm,cyclicNorm,he,
    lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top)),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3),← ENNReal.rpow_mul]
  norm_num
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.CyclicNorm ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Heat Filter
open scoped ENNReal NNReal
noncomputable section

lemma coe_mainConstant : (mainConstant : ℝ≥0∞) = ENNReal.ofReal (2*momentConstant)^((2:ℝ)/3) := by
  rw [ENNReal.coe_nnreal_eq]
  exact (ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by norm_num) momentConstant_pos.le) (by norm_num)).symm

lemma ofReal_integral_cube (B : Plane → ℂ) (hB : MemLp B 3 volume) :
    ENNReal.ofReal (∫ z : Plane, ‖B z‖^3) = eLpNorm B 3 volume ^ (3:ℕ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (hB.integrable_norm_pow (by norm_num : (3:ℕ) ≠ 0))
    (Eventually.of_forall (fun z => pow_nonneg (norm_nonneg (B z)) 3))]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
  exact lintegral_enorm_cube B volume hB.aestronglyMeasurable

lemma integral_cube_eq_one (B : Plane → ℂ) (hB : MemLp B 3 volume) (hn : eLpNorm B 3 volume = 1) :
    (∫ z : Plane, ‖B z‖^3) = 1 := by
  have h := congrArg ENNReal.toReal (ofReal_integral_cube B hB)
  simpa only [hn,one_pow,ENNReal.toReal_one,
    ENNReal.toReal_ofReal (integral_nonneg (fun z => pow_nonneg (norm_nonneg (B z)) 3))] using h

lemma cyclicNorm_le_unit (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume)
    (hnB : eLpNorm B 3 volume = 1) (hnC : eLpNorm C 3 volume = 1) :
    cyclicNorm B C ≤ (mainConstant : ℝ≥0∞) := by
  rw [cyclicNorm,coe_mainConstant]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  have h := lintegral_cyclicMax_moment_le B C hB hC
  rw [integral_cube_eq_one B hB hnB,integral_cube_eq_one C hC hnC] at h
  simpa only [show momentConstant*((1:ℝ)+1) = 2*momentConstant by ring] using h

lemma cyclicNorm_le (B C : Plane → ℂ) (hB : MemLp B 3 volume) (hC : MemLp C 3 volume) :
    cyclicNorm B C ≤ (mainConstant : ℝ≥0∞)*eLpNorm B 3 volume*eLpNorm C 3 volume := by
  by_cases hb0 : eLpNorm B 3 volume = 0
  · have hb := (eLpNorm_eq_zero_iff hB.aestronglyMeasurable (by norm_num)).mp hb0
    rw [cyclicNorm_congr_ae hb (EventuallyEq.refl _ _),cyclicNorm_zero_left]
    exact bot_le
  by_cases hc0 : eLpNorm C 3 volume = 0
  · have hc := (eLpNorm_eq_zero_iff hC.aestronglyMeasurable (by norm_num)).mp hc0
    rw [cyclicNorm_congr_ae (EventuallyEq.refl _ _) hc,cyclicNorm_zero_right]
    exact bot_le
  let u : ℂ := (eLpNorm B 3 volume).toReal
  let v : ℂ := (eLpNorm C 3 volume).toReal
  have hu : ‖u‖ₑ = eLpNorm B 3 volume := by
    rw [← ofReal_norm]
    simp only [u,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hB.eLpNorm_ne_top]
  have hv : ‖v‖ₑ = eLpNorm C 3 volume := by
    rw [← ofReal_norm]
    simp only [v,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hC.eLpNorm_ne_top]
  have hu0 : u ≠ 0 := by
    intro he
    exact hb0 (by simpa only [he,enorm_zero] using hu.symm)
  have hv0 : v ≠ 0 := by
    intro he
    exact hc0 (by simpa only [he,enorm_zero] using hv.symm)
  have hiB : MemLp (u⁻¹ • B) 3 volume := hB.const_smul _
  have hiC : MemLp (v⁻¹ • C) 3 volume := hC.const_smul _
  have hnB : eLpNorm (u⁻¹ • B) 3 volume = 1 := by
    rw [eLpNorm_const_smul,enorm_inv hu0,hu,ENNReal.inv_mul_cancel hb0 hB.eLpNorm_ne_top]
  have hnC : eLpNorm (v⁻¹ • C) 3 volume = 1 := by
    rw [eLpNorm_const_smul,enorm_inv hv0,hv,ENNReal.inv_mul_cancel hc0 hC.eLpNorm_ne_top]
  calc
    cyclicNorm B C = cyclicNorm (u • (u⁻¹ • B)) (v • (v⁻¹ • C)) := by
      rw [smul_smul,smul_smul,mul_inv_cancel₀ hu0,mul_inv_cancel₀ hv0,one_smul,one_smul]
    _ = (‖u‖ₑ*‖v‖ₑ)*cyclicNorm (u⁻¹ • B) (v⁻¹ • C) := cyclicNorm_smul _ _ _ _
    _ ≤ (‖u‖ₑ*‖v‖ₑ)*(mainConstant : ℝ≥0∞) := by
      gcongr
      exact cyclicNorm_le_unit _ _ hiB hiC hnB hnC
    _ = (mainConstant : ℝ≥0∞)*eLpNorm B 3 volume*eLpNorm C 3 volume := by
      rw [hu,hv]
      ac_rfl
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.Coordinates ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory MeasureTheory.Measure Heat
open scoped ENNReal
noncomputable section

lemma measurePreserving_chartB : MeasurePreserving chartB volume volume := by
  exact measurePreserving_add_prod_neg_right (volume : Measure ℝ) volume

lemma measurePreserving_chartC : MeasurePreserving chartC volume volume := by
  have hs : MeasurePreserving (Prod.swap : Plane → Plane) volume volume := measurePreserving_swap
  have h := (hs.comp measurePreserving_chartB).comp hs
  convert h using 1
  funext z
  simp only [Function.comp_apply,chartC,chartB,Prod.swap,add_comm]

lemma measurePreserving_reflect : MeasurePreserving (fun z : Plane => -z) volume volume :=
  volume.measurePreserving_neg

lemma memLp_cyclicB {F : Plane → ℂ} (hF : MemLp F 3 volume) : MemLp (cyclicB F) 3 volume :=
  hF.comp_measurePreserving measurePreserving_chartB
lemma memLp_cyclicC {G : Plane → ℂ} (hG : MemLp G 3 volume) : MemLp (cyclicC G) 3 volume :=
  hG.comp_measurePreserving measurePreserving_chartC

lemma eLpNorm_cyclicB {F : Plane → ℂ} (hF : MemLp F 3 volume) :
    eLpNorm (cyclicB F) 3 volume = eLpNorm F 3 volume :=
  eLpNorm_comp_measurePreserving hF.aestronglyMeasurable measurePreserving_chartB
lemma eLpNorm_cyclicC {G : Plane → ℂ} (hG : MemLp G 3 volume) :
    eLpNorm (cyclicC G) 3 volume = eLpNorm G 3 volume :=
  eLpNorm_comp_measurePreserving hG.aestronglyMeasurable measurePreserving_chartC

lemma measurableSet_annulus (r R : ℝ) : MeasurableSet (annulus r R) :=
  (isOpen_lt continuous_const continuous_abs).measurableSet.inter
    (isOpen_lt continuous_abs continuous_const).measurableSet

lemma cyclicHard_coordinate_integrand (F G : Plane → ℂ) (z : Plane) (r R t : ℝ) :
    cyclicB F ((-z).2,t+z.1+z.2) * cyclicC G (t+z.1+z.2,(-z).1) *
      (hardKernel r R ((-z).1+(-z).2+(t+z.1+z.2)):ℂ) =
    F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ) := by
  change F (-z.2+(t+z.1+z.2),-(-z.2))*G (-(-z.1),(t+z.1+z.2)+(-z.1))*
    (hardKernel r R (-z.1 + -z.2+(t+z.1+z.2)):ℂ) = _
  rw [show -z.2+(t+z.1+z.2) = z.1+t by ring,
    show (t+z.1+z.2)+(-z.1) = z.2+t by ring,
    show -z.1 + -z.2+(t+z.1+z.2) = t by ring]
  simp only [neg_neg]
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.TruncationCoordinates ----
namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Heat Filter
noncomputable section

lemma cyclicHard_coordinate_output (F G : Plane → ℂ) (z : Plane) (r R : ℝ) :
    cyclicKernelOutput (cyclicB F) (cyclicC G) (hardKernel r R) (-z) =
      ∫ t : ℝ, F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ) := by
  rw [cyclicKernelOutput,← integral_add_right_eq_self _ (z.1+z.2)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by simpa only [add_assoc] using cyclicHard_coordinate_integrand F G z r R t)

lemma hardIntegrand_eq_indicator_ae (F G : Plane → ℂ) (z : Plane) {r R : ℝ} (hR : r ≤ R) :
    (fun t : ℝ => F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ)) =ᵐ[volume]
      (annulus r R).indicator (integrand F G z) := by
  filter_upwards [hardKernel_eq_indicator_ae hR] with t ht
  classical
  by_cases hm : t ∈ annulus r R
  · rw [Set.indicator_of_mem hm] at ht
    rw [ht,Set.indicator_of_mem hm]
    simp only [integrand,div_eq_mul_inv,one_mul,Complex.ofReal_inv]
  · rw [Set.indicator_of_notMem hm] at ht
    simp only [ht,Complex.ofReal_zero,mul_zero,Set.indicator_of_notMem hm]

lemma truncation_eq_cyclicHard (F G : Plane → ℂ) (z : Plane) (E : Endpoints) :
    truncation F G E z = cyclicKernelOutput (cyclicB F) (cyclicC G) (hardKernel E.lower E.upper) (-z) := by
  rw [cyclicHard_coordinate_output,integral_congr_ae (hardIntegrand_eq_indicator_ae F G z E.lower_lt_upper.le),
    integral_indicator (measurableSet_annulus E.lower E.upper)]
  rfl

lemma Heat.CubicSliceGood.integrableOn_annulus {F G : Plane → ℂ} {z : Plane}
    (hz : CubicSliceGood (cyclicB F) (cyclicC G) (-z))
    {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) : IntegrableOn (integrand F G z) (annulus r R) := by
  have hi := hz.integrable_hard hr hR
  have ht := ((measurePreserving_add_right (volume : Measure ℝ) (z.1+z.2)).integrable_comp hi.aestronglyMeasurable).mpr hi
  have hi' : Integrable (fun t : ℝ => F (z.1+t,z.2)*G (z.1,z.2+t)*(hardKernel r R t:ℂ)) := by
    convert ht using 1
    funext t
    simpa only [Function.comp_apply,add_assoc] using (cyclicHard_coordinate_integrand F G z r R t).symm
  exact (integrable_indicator_iff (measurableSet_annulus r R)).mp
    (hi'.congr (hardIntegrand_eq_indicator_ae F G z hR))

lemma Heat.CubicSliceGood.goodPoint {F G : Plane → ℂ} {z : Plane}
    (hz : CubicSliceGood (cyclicB F) (cyclicC G) (-z)) : GoodPoint F G z := by
  intro n
  apply hz.integrableOn_annulus
  · positivity
  · apply (div_le_iff₀ (show (0:ℝ) < n+2 by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma ae_goodPoint (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    ∀ᵐ z : Plane, GoodPoint F G z := by
  filter_upwards [measurePreserving_reflect.quasiMeasurePreserving.ae
    (ae_cubicSliceGood (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG))] with z hz
  exact hz.goodPoint
end
end TriangularHilbert
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.Main ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Heat Filter
open scoped ENNReal
noncomputable section

lemma maximal_eq_cyclicMax_ae (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    maximal F G =ᵐ[volume] (fun z => cyclicMax (cyclicB F) (cyclicC G) (-z)) := by
  filter_upwards [measurePreserving_reflect.quasiMeasurePreserving.ae
    (ae_cubicSliceGood (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG))] with z hz
  rw [maximal,ite_eq_left hz.goodPoint]
  simp_rw [truncation_eq_cyclicHard]
  exact (cyclicMax_eq_iSup hz).symm

lemma aemeasurable_maximal (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    AEMeasurable (maximal F G) volume := by
  have h := (aemeasurable_cyclicMax (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG)).comp_quasiMeasurePreserving
    measurePreserving_reflect.quasiMeasurePreserving
  exact h.congr (maximal_eq_cyclicMax_ae F G hF hG).symm

lemma maximalNorm_eq_cyclicNorm (F G : Plane → ℂ) (hF : MemLp F 3 volume) (hG : MemLp G 3 volume) :
    maximalNorm F G = cyclicNorm (cyclicB F) (cyclicC G) := by
  unfold maximalNorm cyclicNorm
  congr 1
  calc
    (∫⁻ z : Plane, maximal F G z ^ ((3:ℝ)/2)) =
        ∫⁻ z : Plane, cyclicMax (cyclicB F) (cyclicC G) (-z)^((3:ℝ)/2) := by
      apply lintegral_congr_ae
      filter_upwards [maximal_eq_cyclicMax_ae F G hF hG] with z hz
      rw [hz]
    _ = _ := measurePreserving_reflect.lintegral_comp_emb (Homeomorph.neg Plane).measurableEmbedding
      (fun z => cyclicMax (cyclicB F) (cyclicC G) z^((3:ℝ)/2))

theorem main_estimate : MainEstimate := by
  refine ⟨mainConstant,fun F G hF hG => ⟨ae_goodPoint F G hF hG,aemeasurable_maximal F G hF hG,?_⟩⟩
  rw [maximalNorm_eq_cyclicNorm F G hF hG]
  simpa only [eLpNorm_cyclicB hF,eLpNorm_cyclicC hG] using
    cyclicNorm_le (cyclicB F) (cyclicC G) (memLp_cyclicB hF) (memLp_cyclicC hG)
end
end TriangularHilbert
end

end OAI

-- ---- mission target ----
open OAI OAI.TriangularHilbert
open MeasureTheory
open scoped ENNReal NNReal
open MeasureTheory Filter
open scoped ENNReal
open MeasureTheory Heat Filter

namespace OAI
namespace TriangularHilbert
theorem _root_.solution : MainEstimate := by
  first
    | exact OAI.TriangularHilbert.main_estimate
    | (apply OAI.TriangularHilbert.main_estimate <;> assumption)
    | (intros; apply OAI.TriangularHilbert.main_estimate <;> assumption)
end TriangularHilbert
end OAI
