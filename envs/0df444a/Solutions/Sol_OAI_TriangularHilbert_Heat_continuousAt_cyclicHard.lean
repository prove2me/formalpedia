-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.continuousAt_cyclicHard
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:10:52.248538+00:00
-- url     : https://prove2.me/submissions/10612383-cc94-461f-904e-75be9bd6da63

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/EndpointContinuity.lean:L45-L87
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.Heat.continuousAt_cyclicHard. The node keeps its source
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

end
end TriangularHilbert.Heat
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.EndpointContinuity ----
namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma continuousAt_threshold (u v : ℝ) (hu : u ≠ v) :
    ContinuousAt (fun r : ℝ => if r < v then (1:ℝ) else 0) u := by
  rcases lt_or_gt_of_ne hu with h|h
  · have he : ∀ᶠ r in 𝓝 u, r < v := eventually_lt_nhds h
    apply (show ContinuousAt (fun _ : ℝ => (1:ℝ)) u from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with r hr
    simp only [hr,ite_true]
  · have he : ∀ᶠ r in 𝓝 u, v < r := eventually_gt_nhds h
    apply (show ContinuousAt (fun _ : ℝ => (0:ℝ)) u from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with r hr
    simp only [not_lt.mpr hr.le,ite_false]

lemma continuousAt_hardKernel_endpoints (r R t : ℝ) (hr : r ≠ |t|) (hR : R ≠ |t|) :
    ContinuousAt (fun p : ℝ×ℝ => hardKernel p.1 p.2 t) (r,R) := by
  have h1 : ContinuousAt (fun p : ℝ×ℝ => if p.1 < |t| then (1:ℝ) else 0) (r,R) := by
    simpa only [Function.comp_def] using (continuousAt_threshold r |t| hr).comp (continuousAt_fst (p := (r,R)))
  have h2 : ContinuousAt (fun p : ℝ×ℝ => if p.2 < |t| then (1:ℝ) else 0) (r,R) := by
    simpa only [Function.comp_def] using (continuousAt_threshold R |t| hR).comp (continuousAt_snd (p := (r,R)))
  exact (h1.sub h2).div_const t

lemma ae_continuousAt_hardKernel_endpoints (r R a : ℝ) :
    ∀ᵐ c : ℝ, ContinuousAt (fun p : ℝ×ℝ => hardKernel p.1 p.2 (a+c)) (r,R) := by
  have hne (x : ℝ) : ∀ᵐ c : ℝ, c ≠ x := by simp [ae_iff]
  filter_upwards [hne (r-a),hne (-r-a),hne (R-a),hne (-R-a)] with c h1 h2 h3 h4
  apply continuousAt_hardKernel_endpoints
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he.symm with he|he
    · apply h1; linarith
    · apply h2; linarith
  · intro he
    rcases eq_or_eq_neg_of_abs_eq he.symm with he|he
    · apply h3; linarith
    · apply h4; linarith

lemma continuousAt_cyclicHard {B C : ℝ×ℝ → ℂ} {z : ℝ×ℝ} (hz : CubicSliceGood B C z)
    {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    ContinuousAt (fun p : ℝ×ℝ => cyclicKernelOutput B C (hardKernel p.1 p.2) z) (r,R) := by
  let s := Set.Icc (-(R+1+|z.1+z.2|)) (R+1+|z.1+z.2|)
  let L := 1/(r/2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let D (c : ℝ) := ‖B (z.2,c)‖^3
  let E (c : ℝ) := ‖C (c,z.1)‖^3
  have hdom : Integrable (s.indicator (fun c => (D c+E c+2)*L)) :=
    IntegrableOn.integrable_indicator
      (((hz.2.2.1.integrableOn.add hz.2.2.2.integrableOn).add
        (integrableOn_const (C := (2:ℝ)) isCompact_Icc.measure_ne_top)).mul_const L) measurableSet_Icc
  have hnear : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), r/2 < p.1 ∧ p.1 < p.2 ∧ p.2 < R+1 := by
    have h1 : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), r/2 < p.1 :=
      (continuous_fst.tendsto (r,R)) (eventually_gt_nhds (show r/2 < r by linarith))
    have h2 : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), 0 < p.2-p.1 :=
      ((continuous_snd.sub continuous_fst).tendsto (r,R)) (eventually_gt_nhds (show 0 < R-r by linarith))
    have h3 : ∀ᶠ p : ℝ×ℝ in 𝓝 (r,R), p.2 < R+1 :=
      (continuous_snd.tendsto (r,R)) (eventually_lt_nhds (show R < R+1 by linarith))
    filter_upwards [h1,h2,h3] with p hp1 hp2 hp3
    exact ⟨hp1,by linarith,hp3⟩

  apply tendsto_integral_filter_of_dominated_convergence (s.indicator (fun c => (D c+E c+2)*L))
  · exact Eventually.of_forall (fun p => (hz.1.mul hz.2.1).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (((measurable_hardKernel _ _).comp (measurable_const.add measurable_id)).aestronglyMeasurable)))
  · filter_upwards [hnear] with p hp
    filter_upwards [] with c
    by_cases hc : c ∈ s
    · rw [Set.indicator_of_mem hc]
      exact norm_product_kernel_le (fun c => B (z.2,c)) (fun c => C (c,z.1))
        (fun c => hardKernel p.1 p.2 (z.1+z.2+c)) (D := D) (E := E) hL (c := c) le_rfl le_rfl
        ((abs_hardKernel_le (by linarith [hp.1]) hp.2.1.le _).trans
          (one_div_le_one_div_of_le (by positivity) hp.1.le))
    · have he : hardKernel p.1 p.2 (z.1+z.2+c) = 0 := by
        apply hardKernel_shift_support hp.2.1.le
        intro hh
        apply hc
        exact ⟨by linarith [hh.1,hp.2.2],by linarith [hh.2,hp.2.2]⟩
      simp only [he,Complex.ofReal_zero,mul_zero,norm_zero,Set.indicator_of_notMem hc,le_refl]
  · exact hdom
  · filter_upwards [ae_continuousAt_hardKernel_endpoints r R (z.1+z.2)] with c hc
    exact tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hc.tendsto)
end
end TriangularHilbert.Heat
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.TriangularHilbert.Heat.continuousAt_cyclicHard := @_root_.OAI.TriangularHilbert.Heat.continuousAt_cyclicHard
