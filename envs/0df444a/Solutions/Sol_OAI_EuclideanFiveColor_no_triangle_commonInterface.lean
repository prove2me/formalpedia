-- Prove2me | solution 1 for OAI.EuclideanFiveColor.no_triangle_commonInterface
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:08:14.690444+00:00
-- url     : https://prove2.me/submissions/268db335-2ca9-42db-aa71-0511eb7a7fa4

import Mathlib
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_EuclideanFiveColor_triangleState_flip
import Theorems.Thm_OAI_EuclideanFiveColor_triangleState_palette
import Theorems.Thm_OAI_EuclideanFiveColor_triangle_boundary_one_orbit

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Expansion
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y] [NormalSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} {ν : Measure Y}
omit [TopologicalSpace Y] [NormalSpace Y] [BorelSpace Y] in
lemma integrable_comp_of_map_le {T : X → Y} (hT : Measurable T) {C : ℝ≥0}
    (hmap : μ.map T ≤ (C : ENNReal) • ν) {f : Y → ℝ} (hf : Integrable f ν) :
    Integrable (fun x => f (T x)) μ := by
  have hh := (hf.smul_measure (by simp : (C : ENNReal) ≠ ⊤)).mono_measure hmap
  exact (integrable_map_measure hh.aestronglyMeasurable hT.aemeasurable).mp hh
omit [TopologicalSpace Y] [NormalSpace Y] [BorelSpace Y] in
lemma integral_norm_comp_le {T : X → Y} (hT : Measurable T) {C : ℝ≥0}
    (hmap : μ.map T ≤ (C : ENNReal) • ν) {f : Y → ℝ} (hf : Integrable f ν) :
    (∫ x, ‖f (T x)‖ ∂μ) ≤ (C : ℝ)*(∫ y, ‖f y‖ ∂ν) := by
  have hh := (hf.smul_measure (by simp : (C : ENNReal) ≠ ⊤)).mono_measure hmap
  rw [← integral_map hT.aemeasurable hh.norm.aestronglyMeasurable]
  calc
    _ ≤ ∫ y, ‖f y‖ ∂((C : ENNReal) • ν) :=
      integral_mono_measure hmap (Eventually.of_forall fun y => norm_nonneg _) (hf.norm.smul_measure (by simp))
    _ = _ := by rw [integral_smul_measure]; simp
/-- L¹ continuity under measurable perturbations with a common bounded pushforward density. -/
lemma tendsto_integral_norm_comp_sub [IsFiniteMeasure μ] [ν.WeaklyRegular]
    {T : ℕ → X → Y} {S : X → Y} {C : ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (hS : Measurable S)
    (hmT : ∀ n, μ.map (T n) ≤ (C : ENNReal) • ν) (hmS : μ.map S ≤ (C : ENNReal) • ν)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => T n x) atTop (𝓝 (S x)))
    {f : Y → ℝ} (hf : Integrable f ν) :
    Tendsto (fun n => ∫ x, ‖f (T n x)-f (S x)‖ ∂μ) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε/(3*((C : ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨g,hg,hgi⟩ := hf.exists_boundedContinuous_integral_sub_le hδ
  have hgT (n : ℕ) : Integrable (fun x => g (T n x)) μ :=
    integrable_comp_of_map_le (hT n) (hmT n) hgi
  have hgS : Integrable (fun x => g (S x)) μ := integrable_comp_of_map_le hS hmS hgi
  have hfT (n : ℕ) := integrable_comp_of_map_le (hT n) (hmT n) hf
  have hfS := integrable_comp_of_map_le hS hmS hf
  have hmid : Tendsto (fun n => ∫ x, ‖g (T n x)-g (S x)‖ ∂μ) atTop (𝓝 0) := by
    have hp := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => 2*‖g‖)
      (fun n => ((hgT n).sub hgS).norm.aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [norm_norm]
        exact (norm_sub_le _ _).trans (by linarith [g.norm_coe_le_norm (T n x),g.norm_coe_le_norm (S x)]))
      (ht.mono fun x hx => by
        have hh := (g.continuous.tendsto (S x)).comp hx
        simpa using (hh.sub tendsto_const_nhds).norm)
    simpa using hp
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hmid (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h1 : (∫ x, ‖f (T n x)-g (T n x)‖ ∂μ) ≤ (C : ℝ)*δ :=
    (integral_norm_comp_le (hT n) (hmT n) (hf.sub hgi)).trans (mul_le_mul_of_nonneg_left hg C.2)
  have h2 : (∫ x, ‖f (S x)-g (S x)‖ ∂μ) ≤ (C : ℝ)*δ :=
    (integral_norm_comp_le hS hmS (hf.sub hgi)).trans (mul_le_mul_of_nonneg_left hg C.2)
  have htri : (∫ x, ‖f (T n x)-f (S x)‖ ∂μ) ≤
      (∫ x, ‖f (T n x)-g (T n x)‖ ∂μ) + (∫ x, ‖g (T n x)-g (S x)‖ ∂μ) +
      (∫ x, ‖f (S x)-g (S x)‖ ∂μ) := by
    have ha : Integrable (fun x => ‖f (T n x)-g (T n x)‖) μ := ((hfT n).sub (hgT n)).norm
    have hb : Integrable (fun x => ‖g (T n x)-g (S x)‖) μ := ((hgT n).sub hgS).norm
    have hc : Integrable (fun x => ‖f (S x)-g (S x)‖) μ := (hfS.sub hgS).norm
    have hi := integral_mono ((hfT n).sub hfS).norm ((ha.add hb).add hc) (fun x => by
      simpa only [Pi.add_apply,Pi.sub_apply,← dist_eq_norm,dist_comm (g (S x))] using
        dist_triangle4 (f (T n x)) (g (T n x)) (g (S x)) (f (S x)))
    apply hi.trans_eq
    exact (integral_add (ha.add hb) hc).trans (congrArg (fun t => t + ∫ x, ‖f (S x)-g (S x)‖ ∂μ) (integral_add ha hb))
  have hδv : (C : ℝ)*δ ≤ ε/3 := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<3*((C : ℝ)+1))).mpr
    nlinarith [C.2]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
  have hm := hN n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at hm
  linarith
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
lemma tendsto_integral_norm_comp_sub_eventual {X Y : Type*} [MeasurableSpace X]
    [TopologicalSpace Y] [NormalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [ν.WeaklyRegular]
    {T : ℕ → X → Y} {S : X → Y} {C : ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (hS : Measurable S)
    (hmT : ∀ᶠ n in atTop, μ.map (T n) ≤ (C : ENNReal) • ν) (hmS : μ.map S ≤ (C : ENNReal) • ν)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => T n x) atTop (𝓝 (S x)))
    {f : Y → ℝ} (hf : Integrable f ν) :
    Tendsto (fun n => ∫ x, ‖f (T n x)-f (S x)‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hmT
  apply (tendsto_add_atTop_iff_nat N).mp
  apply tendsto_integral_norm_comp_sub (T := fun n => T (n+N)) (C := C)
    (fun n => hT (n+N)) hS (fun n => hN _ (Nat.le_add_left N n)) hmS
  · exact ht.mono fun x hx => (tendsto_add_atTop_iff_nat N).mpr hx
  · exact hf
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CircleMaps
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma circleSum_continuous (r : ℝ) : Continuous (circleSum r) :=
  continuous_iff_continuousAt.mpr fun p => (circleSum_strict r p).continuousAt
lemma circleSum_local_antilipschitz {r : ℝ} {p : RealPlane} (h : r*Real.sin (p.2-p.1) ≠ 0) :
    ∃ s : Set RealPlane, IsOpen s ∧ p ∈ s ∧ ∃ K : ℝ≥0, AntilipschitzWith K (s.domRestrict (circleSum r)) := by
  let L := circleSumDerivEquiv h
  have hd : HasStrictFDerivAt (circleSum r) (L : RealPlane →L[ℝ] RealPlane) p := circleSum_strict r p
  obtain ⟨s,hp,hs,ha⟩ := hd.approximates_deriv_on_open_nhds
  refine ⟨s,hs,hp,_,ha.antilipschitz ?_⟩
  right
  have hpos := L.subsingleton_or_nnnorm_symm_pos.resolve_left (not_subsingleton RealPlane)
  exact half_lt_self (inv_pos.mpr hpos)
lemma realDirection_lipschitz : LipschitzWith 1 (fun t : ℝ => (Real.cos t,Real.sin t)) := by
  simpa using Real.lipschitzWith_cos.prodMk Real.lipschitzWith_sin
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma angleChartMeas_le : angleChartMeasure ≤ volume := Measure.restrict_le_self
lemma angleChart_preserving : MeasurePreserving angleChart angleChartMeasure
    ((volume : Measure Angles).prod volume) := by
  have h := (AddCircle.measurePreserving_mk (2*Real.pi) 0).prod
    (AddCircle.measurePreserving_mk (2*Real.pi) 0)
  convert h using 1
  · rfl
  · simp only [angleChartMeasure,zero_add,Measure.prod_restrict,← Measure.volume_eq_prod]
lemma angleChart_measure : (angleChartMeasure.map angleChart) =
    (ENNReal.ofReal (2*Real.pi))^2 • angularMeasure.prod angularMeasure := by
  rw [angleChart_preserving.map_eq,AddCircle.volume_eq_smul_haarAddCircle,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,pow_two]
  rfl
lemma integral_angular_eq_chart {f : Angles × Angles → ℝ} (hf : Measurable f) :
    (∫ p, f p ∂angularMeasure.prod angularMeasure) =
      ((2*Real.pi)^2)⁻¹ * ∫ q, f (angleChart q) ∂angleChartMeasure := by
  have h := integral_map (μ := angleChartMeasure) angleChart_preserving.measurable.aemeasurable hf.aestronglyMeasurable
  rw [angleChart_measure,integral_smul_measure,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*Real.pi),smul_eq_mul] at h
  rw [← h]
  field_simp
lemma direction_realPlane (t : ℝ) : Complex.equivRealProdCLM (direction (t : Angles)) =
    (Real.cos t,Real.sin t) := by
  rw [direction_real,Circle.coe_exp,Complex.exp_mul_I]
  ext <;> simp [Complex.cos_ofReal_re,Complex.sin_ofReal_re]
lemma circleSum_chart (x : ℂ) (r : ℝ) (q : RealPlane) :
    Complex.equivRealProdCLM (x+(r : ℂ)*direction (angleChart q).1+direction (angleChart q).2) =
      Complex.equivRealProdCLM x+circleSum r q := by
  change Complex.equivRealProdCLM (x+(r : ℂ)*direction (q.1 : Angles)+direction (q.2 : Angles)) = _
  rw [map_add,map_add]
  have h : (r : ℂ)*direction (q.1 : Angles) = r • direction (q.1 : Angles) := by simp
  rw [h,map_smul,direction_realPlane,direction_realPlane]
  ext <;> simp [circleSum,add_assoc]
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
namespace EuclideanFiveColor
lemma volume_preimage_bound {F : ℝ × ℝ → ℝ × ℝ} {s : Set (ℝ × ℝ)} {K : ℝ≥0}
    (hF : AntilipschitzWith K (s.domRestrict F)) (A : Set (ℝ × ℝ)) :
    volume (F ⁻¹' A ∩ s) ≤ (K : ENNReal)^2 * volume A := by
  have he : Subtype.val '' ((s.domRestrict F) ⁻¹' A) = F ⁻¹' A ∩ s := by
    ext p
    constructor
    · rintro ⟨q,hq,rfl⟩; exact ⟨hq,q.2⟩
    · rintro ⟨hp,hs⟩; exact ⟨⟨p,hs⟩,hp,rfl⟩
  have hi := (isometry_subtype_coe : Isometry (Subtype.val : s → ℝ × ℝ)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ)≤2)) ((s.domRestrict F) ⁻¹' A)
  have ha := hF.hausdorffMeasure_preimage_le (by norm_num : (0 : ℝ)≤2) A
  rw [he,hausdorffMeasure_prod_real] at hi
  rw [← hi,hausdorffMeasure_prod_real,ENNReal.rpow_two] at ha
  exact ha
lemma map_restrict_volume_le {F : ℝ × ℝ → ℝ × ℝ} (hm : Measurable F)
    {s B : Set (ℝ × ℝ)} (_hB : MeasurableSet B) {K : ℝ≥0}
    (hF : AntilipschitzWith K (s.domRestrict F)) (himage : MapsTo F s B) :
    (volume.restrict s).map F ≤ ((K^2 : ℝ≥0) : ENNReal) • volume.restrict B := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.map_apply hm hA,Measure.restrict_apply (hm hA),Measure.smul_apply,
    Measure.restrict_apply hA,smul_eq_mul,ENNReal.coe_pow]
  have he : F ⁻¹' A ∩ s = F ⁻¹' (A ∩ B) ∩ s := by
    ext x
    exact ⟨fun hx => ⟨⟨hx.1,himage hx.2⟩,hx.2⟩,fun hx => ⟨hx.1.1,hx.2⟩⟩
  rw [he]
  exact volume_preimage_bound hF (A ∩ B)
lemma antilipschitz_small_perturbation {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace X] {F G : X → E} {K L : ℝ≥0} (hf : AntilipschitzWith K F)
    (hg : LipschitzWith L G) {a : ℝ} (ha : (K : ℝ)*‖a‖*(L : ℝ) ≤ 1/2) :
    AntilipschitzWith (2*K) (fun x => F x+a • G x) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h1 := hf.le_mul_dist x y
  have h2 := hg.dist_le_mul x y
  have h3 : dist (F x) (F y) ≤ dist (F x+a • G x) (F y+a • G y) + ‖a‖*dist (G x) (G y) := by
    simpa only [add_sub_cancel_right,dist_smul₀] using
      dist_sub_sub_le (F x+a • G x) (a • G x) (F y+a • G y) (a • G y)
  have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg a)
  have h5 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add_right h4 _)) K.2
  have h6 := mul_le_mul_of_nonneg_right ha (dist_nonneg (x := x) (y := y))
  simp only [NNReal.coe_mul,NNReal.coe_ofNat]
  nlinarith
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma realDirection_norm_le (t : ℝ) : ‖(Real.cos t,Real.sin t)‖ ≤ (1 : ℝ) := by
  rw [Prod.norm_def,max_le_iff]
  exact ⟨by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one t,
    by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one t⟩
lemma circleSum_decompose (r : ℝ) (q : RealPlane) :
    circleSum r q = r • (Real.cos q.1,Real.sin q.1) + (Real.cos q.2,Real.sin q.2) := rfl
lemma circleSum_norm_le (r : ℝ) (q : RealPlane) : ‖circleSum r q‖ ≤ |r|+1 := by
  rw [circleSum_decompose]
  calc
    _ ≤ ‖r • (Real.cos q.1,Real.sin q.1)‖+‖(Real.cos q.2,Real.sin q.2)‖ := norm_add_le _ _
    _ ≤ |r| * 1+1 := by rw [norm_smul]; exact add_le_add (mul_le_mul_of_nonneg_left (realDirection_norm_le _) (norm_nonneg r)) (realDirection_norm_le _)
    _ = _ := by ring
lemma circleSum_perturb_identity (r : ℝ) (q : RealPlane) :
    circleSum r q = circleSum 1 q + (r-1) • (Real.cos q.1,Real.sin q.1) := by
  apply Prod.ext
  · change r*Real.cos q.1+Real.cos q.2 = 1*Real.cos q.1+Real.cos q.2+(r-1)*Real.cos q.1
    ring
  · change r*Real.sin q.1+Real.sin q.2 = 1*Real.sin q.1+Real.sin q.2+(r-1)*Real.sin q.1
    ring
lemma circleSum_parameter_tendsto {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (q : RealPlane) :
    Tendsto (fun n => circleSum (r n) q) atTop (𝓝 (circleSum 1 q)) := by
  exact (hr.mul_const (Real.cos q.1) |>.add_const (Real.cos q.2)).prodMk_nhds
    (hr.mul_const (Real.sin q.1) |>.add_const (Real.sin q.2))
lemma circleSum_eventual_image {r : ℕ → ℝ} {y : ℕ → RealPlane} {x : RealPlane}
    (hr : Tendsto r atTop (𝓝 1)) (hy : Tendsto y atTop (𝓝 x)) :
    ∀ᶠ n in atTop, ∀ q, y n+circleSum (r n) q ∈ Metric.closedBall x 4 := by
  filter_upwards [hr.eventually (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ)<1)),
    hy.eventually (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ)<1))] with n hn hyn
  intro q
  have hh := circleSum_norm_le (r n) q
  have hb : |r n| ≤ 2 := by
    have ht := norm_le_norm_sub_add (r n) (1 : ℝ)
    rw [Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,abs_one] at ht
    rw [Real.dist_eq] at hn
    linarith
  rw [Metric.mem_closedBall]
  calc
    _ ≤ dist (y n+circleSum (r n) q) (y n)+dist (y n) x := dist_triangle _ _ _
    _ = ‖circleSum (r n) q‖+dist (y n) x := by rw [dist_eq_norm,add_sub_cancel_left]
    _ ≤ 4 := by linarith
lemma circleSum_limit_image (x q : RealPlane) : x+circleSum 1 q ∈ Metric.closedBall x 4 := by
  rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left]
  have hh := circleSum_norm_le 1 q
  norm_num at hh
  linarith
lemma circleSum_eventual_antilipschitz {V : Set RealPlane} {K : ℝ≥0}
    (hK : AntilipschitzWith K (V.domRestrict (circleSum 1)))
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (y : ℕ → RealPlane) :
    ∀ᶠ n in atTop, AntilipschitzWith (2*K) (V.domRestrict (fun q => y n+circleSum (r n) q)) := by
  have hD : LipschitzWith 1 (fun q : V => (Real.cos q.1.1,Real.sin q.1.1)) := by
    have hf : LipschitzWith 1 (fun q : V => q.1.1) := LipschitzWith.of_dist_le_mul (fun q p => by
      simp only [NNReal.coe_one,one_mul]
      exact le_max_left _ _)
    simpa only [Function.comp_def,one_mul] using realDirection_lipschitz.comp hf
  have ht : Tendsto (fun n => (K : ℝ)*‖r n-1‖) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => r n-1) atTop (𝓝 0) := by simpa using hr.sub_const 1
    simpa using hh.norm.const_mul (K : ℝ)
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with n hn
  have ha := antilipschitz_small_perturbation hK hD (a := r n-1) (by simpa using le_of_lt hn)
  apply AntilipschitzWith.of_le_mul_dist
  intro q p
  have hh := ha.le_mul_dist q p
  simpa only [Set.domRestrict_apply,dist_add_left,← circleSum_perturb_identity] using hh
lemma circleSum_limit_antilipschitz {V : Set RealPlane} {K : ℝ≥0}
    (hK : AntilipschitzWith K (V.domRestrict (circleSum 1))) (x : RealPlane) :
    AntilipschitzWith (2*K) (V.domRestrict (fun q => x+circleSum 1 q)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro q p
  have hh := hK.le_mul_dist q p
  simpa only [Set.domRestrict_apply,dist_add_left] using hh.trans
    (mul_le_mul_of_nonneg_right (by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; linarith [K.2] : (K : ℝ)≤ ((2*K : ℝ≥0) : ℝ)) dist_nonneg)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma measure_null_of_locally_null_on_conull {X : Type*} [TopologicalSpace X]
    [HereditarilyLindelofSpace X] [MeasurableSpace X] {μ : Measure X} {R A : Set X}
    (hR : μ Rᶜ = 0) (h : ∀ x ∈ R, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ μ (A ∩ V) = 0) :
    μ A = 0 := by
  classical
  choose V hVo hxV hV0 using (fun x : R => h x.1 x.2)
  obtain ⟨t,ht,hcov⟩ := (HereditarilyLindelofSpace.isLindelof R).elim_countable_subcover V hVo
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩)
  have hu : μ (⋃ i ∈ t, A ∩ V i) = 0 := (measure_biUnion_null_iff ht).mpr (fun i _ => hV0 i)
  apply measure_mono_null (t := Rᶜ ∪ ⋃ i ∈ t, A ∩ V i) _ (measure_union_null hR hu)
  intro x hx
  by_cases hr : x ∈ R
  · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcov hr)
    exact Or.inr (mem_iUnion₂.mpr ⟨i,hi,hx,hxi⟩)
  · exact Or.inl hr
lemma circleSum_regular_ae : ∀ᵐ p : RealPlane ∂volume, Real.sin (p.2-p.1) ≠ 0 := by
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · exact Eventually.of_forall fun t => by
      have hs : {s : ℝ | Real.sin (s-t)=0} ⊆ Set.range (fun n : ℤ => t+n*Real.pi) := by
        intro s h
        obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp h
        exact ⟨n,by linarith⟩
      change volume {s : ℝ | ¬ Real.sin (s-t) ≠ 0} = 0
      simpa only [not_not] using measure_mono_null hs ((countable_range _).measure_zero volume)
  · exact (measurableSet_eq_fun (Real.measurable_sin.comp (measurable_snd.sub measurable_fst)) measurable_const).compl
lemma circleSum_preimage_null {r : ℝ} (hr : r ≠ 0) {A : Set RealPlane} (hA : volume A=0) :
    volume (circleSum r ⁻¹' A)=0 := by
  apply measure_null_of_locally_null_on_conull (μ := (volume : Measure RealPlane))
    (R := {p : RealPlane | Real.sin (p.2-p.1) ≠ 0}) (A := circleSum r ⁻¹' A) circleSum_regular_ae
  intro p hp
  obtain ⟨s,hso,hps,K,hK⟩ := circleSum_local_antilipschitz (mul_ne_zero hr hp)
  refine ⟨s,hso,hps,?_⟩
  have hh := volume_preimage_bound hK A
  rw [hA,mul_zero] at hh
  exact nonpos_iff_eq_zero.mp hh
lemma circleSum_quasiMeasurePreserving {r : ℝ} (hr : r ≠ 0) :
    Measure.QuasiMeasurePreserving (circleSum r) volume volume := by
  refine ⟨(circleSum_continuous r).measurable,Measure.AbsolutelyContinuous.mk (fun A hA hz => ?_)⟩
  rw [Measure.map_apply (circleSum_continuous r).measurable hA]
  exact circleSum_preimage_null hr hz
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_CircleTransport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter Topology
namespace EuclideanFiveColor
/-- A uniformly bounded nonnegative sequence converging locally in L¹ on a conull open
cover converges globally in L¹ for a finite inner-regular measure. -/
lemma tendsto_integral_of_local_cover {X I : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [Measure.InnerRegularCompactLTTop μ] {F : ℕ → X → ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hb : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (V : I → Set X) (hVo : ∀ i, IsOpen (V i)) (hfull : ∀ᵐ x ∂μ, x ∈ ⋃ i, V i)
    (hlocal : ∀ i, Tendsto (fun n => ∫ x in V i, F n x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hKU,hK,hμK⟩ := (isOpen_iUnion hVo).measurableSet.exists_isCompact_sdiff_lt
    (measure_ne_top μ _) (by exact ne_of_gt (ENNReal.ofReal_pos.mpr (half_pos hε)))
  have hδ : μ Kᶜ < ENNReal.ofReal (ε/2) := by
    have he : (Kᶜ : Set X) =ᵐ[μ] ((⋃ i, V i) \ K : Set X) := by
      filter_upwards [hfull] with x hx
      exact propext ⟨fun h => ⟨hx,h⟩,fun h => h.2⟩
    exact (measure_congr he).trans_lt hμK
  have hδr : μ.real Kᶜ < ε/2 := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (ENNReal.ofReal_ne_top)).mpr hδ
    simpa only [Measure.real,ENNReal.toReal_ofReal (le_of_lt (half_pos hε))] using hh
  obtain ⟨J,hJ⟩ := hK.elim_finite_subcover V hVo hKU
  have hlim : Tendsto (fun n => ∑ i ∈ J, ∫ x in V i, F n x ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum J (fun i _ => hlocal i)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hlim (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hmaj : (∫ x, F n x ∂μ) ≤ (∑ i ∈ J, ∫ x in V i, F n x ∂μ) + μ.real Kᶜ := by
    have hJJ : Integrable (fun x => ∑ i ∈ J, (V i).indicator (F n) x) μ :=
      integrable_finsetSum J (fun i _ => (hF n).indicator (hVo i).measurableSet)
    have hCC : Integrable (Kᶜ.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const _).indicator hK.measurableSet.compl
    have hi := integral_mono (hF n) (hJJ.add hCC) (fun x => by
      have hs (i : I) : 0 ≤ (V i).indicator (F n) x := indicator_nonneg (fun y _ => (hb n y).1) x
      by_cases hx : x ∈ K
      · obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hJ hx)
        have hsum := Finset.single_le_sum (fun j _ => hs j) hi
        simp only [Pi.add_apply,indicator_of_notMem (show x ∉ Kᶜ from not_not.mpr hx),add_zero]
        exact (by simpa only [indicator_of_mem hxi] using hsum)
      · change F n x ≤ (∑ i ∈ J, (V i).indicator (F n) x) + Kᶜ.indicator (fun _ => (1 : ℝ)) x
        rw [indicator_of_mem hx]
        linarith [Finset.sum_nonneg (fun i (_ : i ∈ J) => hs i), (hb n x).2])
    apply hi.trans_eq
    refine (integral_add hJJ hCC).trans ?_
    apply congrArg₂ (·+·)
    · exact (integral_finsetSum J (fun i _ => (hF n).indicator (hVo i).measurableSet)).trans
        (Finset.sum_congr rfl (fun i _ => integral_indicator (hVo i).measurableSet))
    · rw [integral_indicator hK.measurableSet.compl]
      simp only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ]
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => (hb n x).1)]
  have hh := hN n hn
  have hs0 : 0 ≤ ∑ i ∈ J, ∫ x in V i, F n x ∂μ :=
    Finset.sum_nonneg fun i _ => integral_nonneg (fun x => (hb n x).1)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hs0] at hh
  linarith
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma bounded_difference_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hgb : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    Integrable (fun x => ‖f x-g x‖) μ := by
  apply Integrable.of_bound ((hf.sub hg).norm.aestronglyMeasurable) 1
  exact Eventually.of_forall fun x => by
    rw [norm_norm,Real.norm_eq_abs,abs_le]
    change -1 ≤ f x-g x ∧ f x-g x ≤ 1
    constructor <;> linarith [(hfb x).1,(hfb x).2,(hgb x).1,(hgb x).2]
lemma circleSum_tendsto_L1 {μ : Measure RealPlane} [IsFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] (hμ : μ ≤ volume)
    {r : ℕ → ℝ} {y : ℕ → RealPlane} {x : RealPlane}
    (hr : Tendsto r atTop (𝓝 1)) (hy : Tendsto y atTop (𝓝 x))
    {f : RealPlane → ℝ} (hf : Measurable f) (hfb : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    Tendsto (fun n => ∫ q, ‖f (y n+circleSum (r n) q)-f (x+circleSum 1 q)‖ ∂μ) atTop (𝓝 0) := by
  classical
  let T : ℕ → RealPlane → RealPlane := fun n q => y n+circleSum (r n) q
  let S : RealPlane → RealPlane := fun q => x+circleSum 1 q
  have hT (n : ℕ) : Measurable (T n) := (continuous_const.add (circleSum_continuous _)).measurable
  have hS : Measurable S := (continuous_const.add (circleSum_continuous _)).measurable
  let R : Set RealPlane := {p | Real.sin (p.2-p.1) ≠ 0}
  have hex : ∀ p : R, ∃ V : Set RealPlane, IsOpen V ∧ p.1 ∈ V ∧
      ∃ K : ℝ≥0, AntilipschitzWith K (V.domRestrict (circleSum 1)) := by
    intro p
    exact circleSum_local_antilipschitz (by simpa only [one_mul] using (show Real.sin (p.1.2-p.1.1) ≠ 0 from p.2))
  choose V hVo hpV K hK using hex
  have hfull : ∀ᵐ q ∂μ, q ∈ ⋃ p : R, V p := by
    filter_upwards [circleSum_regular_ae.filter_mono (ae_mono hμ)] with q hq
    exact mem_iUnion.mpr ⟨⟨q,hq⟩,hpV ⟨q,hq⟩⟩
  apply tendsto_integral_of_local_cover (μ := μ)
    (fun n => bounded_difference_integrable (hf.comp (hT n)) (hf.comp hS)
      (fun q => hfb (T n q)) (fun q => hfb (S q)))
    (fun n q => ⟨norm_nonneg _,by
      rw [Real.norm_eq_abs,abs_le]
      change -1 ≤ f (T n q)-f (S q) ∧ f (T n q)-f (S q) ≤ 1
      constructor <;> linarith [(hfb (T n q)).1,(hfb (T n q)).2,(hfb (S q)).1,(hfb (S q)).2]⟩)
    V hVo hfull
  intro p
  let B := Metric.closedBall x (4 : ℝ)
  let ν : Measure RealPlane := volume.restrict B
  have hB : MeasurableSet B := measurableSet_closedBall
  let : IsFiniteMeasure ν := ⟨by simpa [ν] using (isCompact_closedBall x 4).measure_lt_top⟩
  have hfi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable 1
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hfb z).1]; exact (hfb z).2)
  have hmapT : ∀ᶠ n in atTop, ((μ.restrict (V p)).map (T n)) ≤
      (((2*K p)^2 : ℝ≥0) : ENNReal) • ν := by
    filter_upwards [circleSum_eventual_image hr hy,circleSum_eventual_antilipschitz (hK p) hr y] with n hn ha
    apply (Measure.map_mono (Measure.restrict_mono_measure hμ (V p)) (hT n)).trans
    exact map_restrict_volume_le (hT n) hB ha (fun q _ => hn q)
  have hmapS : ((μ.restrict (V p)).map S) ≤ (((2*K p)^2 : ℝ≥0) : ENNReal) • ν := by
    apply (Measure.map_mono (Measure.restrict_mono_measure hμ (V p)) hS).trans
    exact map_restrict_volume_le hS hB (circleSum_limit_antilipschitz (hK p) x)
      (fun q _ => circleSum_limit_image x q)
  apply tendsto_integral_norm_comp_sub_eventual hT hS hmapT hmapS _ hfi
  exact Eventually.of_forall fun q => hy.add (circleSum_parameter_tendsto hr q)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma angularSum_measurable (x : ℂ) (r : ℝ) : Measurable (angularSum x r) :=
  (measurable_const.add (measurable_const.mul (direction_continuous.measurable.comp measurable_fst))).add
    (direction_continuous.measurable.comp measurable_snd)
lemma angularSum_chart (x : ℂ) (r : ℝ) (q : RealPlane) :
    angularSum x r (angleChart q) = Complex.equivRealProdCLM.symm
      (Complex.equivRealProdCLM x+circleSum r q) := by
  apply Complex.equivRealProdCLM.injective
  simpa only [angularSum,ContinuousLinearEquiv.apply_symm_apply] using circleSum_chart x r q
lemma angularSum_quasiMeasurePreserving (x : ℂ) {r : ℝ} (hr : r ≠ 0) :
    Measure.QuasiMeasurePreserving (angularSum x r) (angularMeasure.prod angularMeasure) volume := by
  have hreal : Measure.QuasiMeasurePreserving
      (fun q => Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM x+circleSum r q)) volume volume :=
    (Complex.volume_preserving_equiv_real_prod.symm).quasiMeasurePreserving.comp
      ((measurePreserving_add_left volume (Complex.equivRealProdCLM x)).quasiMeasurePreserving.comp
        (circleSum_quasiMeasurePreserving hr))
  refine ⟨angularSum_measurable x r,Measure.AbsolutelyContinuous.mk (fun A hA hz => ?_)⟩
  rw [Measure.map_apply (angularSum_measurable x r) hA]
  have hpre : angleChartMeasure (angleChart ⁻¹' (angularSum x r ⁻¹' A))=0 := by
    apply le_antisymm _ bot_le
    apply (angleChartMeas_le _).trans
    have hz' := hreal.preimage_null hz
    simpa [preimage_preimage,Function.comp_def,angularSum_chart] using le_of_eq hz'
  have hz' : (ENNReal.ofReal (2*Real.pi))^2 *
      (angularMeasure.prod angularMeasure) (angularSum x r ⁻¹' A)=0 := by
    rw [← smul_eq_mul,← Measure.smul_apply,← angleChart_measure,
      Measure.map_apply angleChart_preserving.measurable ((angularSum_measurable x r) hA)]
    exact hpre
  exact (mul_eq_zero.mp hz').resolve_left (by positivity)
lemma angularSum_tendsto_L1 {r : ℕ → ℝ} {y : ℕ → ℂ} {x : ℂ}
    (hr : Tendsto r atTop (𝓝 1)) (hy : Tendsto y atTop (𝓝 x))
    {f : ℂ → ℝ} (hf : Measurable f) (hfb : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    Tendsto (fun n => ∫ p, ‖f (angularSum (y n) (r n) p)-f (angularSum x 1 p)‖
      ∂angularMeasure.prod angularMeasure) atTop (𝓝 0) := by
  have h := circleSum_tendsto_L1 (μ := angleChartMeasure) angleChartMeas_le hr
    (Complex.equivRealProdCLM.continuous.tendsto x |>.comp hy)
    (hf.comp Complex.equivRealProdCLM.symm.continuous.measurable)
    (fun z => hfb (Complex.equivRealProdCLM.symm z))
  have he := h.const_mul (((2*Real.pi)^2)⁻¹)
  simp only [mul_zero] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  simpa only [Function.comp_def,Pi.sub_apply,angularSum_chart] using
    (integral_angular_eq_chart (f := fun p => ‖f (angularSum (y n) (r n) p)-f (angularSum x 1 p)‖)
      (((hf.comp (angularSum_measurable _ _)).sub (hf.comp (angularSum_measurable _ _))).norm))
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_WeakColoring
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma shiftL2_ae (z : ℂ) (f : PlaneL2) : shiftL2 z f =ᵐ[volume] fun x => f (x+z) :=
  Lp.coeFn_compMeasurePreserving f _
lemma shiftL2_continuous (f : PlaneL2) : Continuous (fun z => shiftL2 z f) := by
  let g : C(ℂ,C(ℂ,ℂ)) := (ContinuousMap.mk (fun p : ℂ × ℂ => p.2+p.1) (by fun_prop)).curry
  exact continuous_const.compMeasurePreservingLp g.continuous (fun z => measurePreserving_add_right volume z) (by simp)
lemma product_zero_of_inner_zero (f g : PlaneL2) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hg : ∀ᵐ x ∂volume, 0 ≤ g x) (h : ⟪f,g⟫ = 0) :
    ∀ᵐ x ∂volume, f x*g x=0 := by
  have hi : Integrable (fun x : ℂ => f x*g x) volume := by
    simpa [RCLike.inner_apply,mul_comm] using (L2.integrable_inner (𝕜 := ℝ) f g)
  have hn : ∀ᵐ x ∂volume, 0 ≤ f x*g x := by
    filter_upwards [hf,hg] with x hx hy
    exact mul_nonneg hx hy
  rw [L2.inner_def] at h
  apply (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
  simpa [RCLike.inner_apply,mul_comm] using h
/-- AE exclusions over any full-support parameter measure upgrade to every parameter. -/
lemma all_parameters_product_zero {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    (μ : Measure T) [μ.IsOpenPosMeasure] (d : T → ℂ) (hd : Continuous d)
    (f : PlaneL2) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (ho : ∀ᵐ t ∂μ, ∀ᵐ x ∂(volume : Measure ℂ), f x*f (x+d t)=0) :
    ∀ t : T, ∀ᵐ x ∂(volume : Measure ℂ), f x*f (x+d t)=0 := by
  have hc : Continuous (fun t : T => ⟪f,shiftL2 (d t) f⟫) :=
    continuous_const.inner ((shiftL2_continuous f).comp hd)
  have hz : (fun t : T => ⟪f,shiftL2 (d t) f⟫) =ᵐ[μ] fun _ => 0 := by
    filter_upwards [ho] with t ht
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [shiftL2_ae (d t) f,ht] with x hx hh
    simpa [RCLike.inner_apply,mul_comm,hx] using hh
  have he := (hc.ae_eq_iff_eq μ continuous_const).mp hz
  intro t
  have hg : ∀ᵐ x ∂volume, 0 ≤ shiftL2 (d t) f x := by
    filter_upwards [shiftL2_ae (d t) f,
      (measurePreserving_add_right volume (d t)).quasiMeasurePreserving.ae hf] with x hx hh
    simpa only [hx] using hh
  have h0 := product_zero_of_inner_zero f (shiftL2 (d t) f) hf hg (congrFun he t)
  filter_upwards [h0,shiftL2_ae (d t) f] with x hx hh
  simpa only [hh] using hx
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
include hc
lemma truncatedVector_ae (i : Fin k) (n : ℕ) :
    truncatedVector c hc i n =ᵐ[volume] (truncatedClass c i n).indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _
lemma weak_all_directions (hweak : WeakColoring k c) :
    ∀ t : Angles, ∀ᵐ z ∂(volume : Measure ℂ), c z ≠ c (z+direction t) := by
  have ho : ∀ᵐ t ∂angularMeasure, ∀ᵐ z ∂(volume : Measure ℂ), c z ≠ c (z+direction t) := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod hweak.2)
    exact (measurableSet_eq_fun (hc.comp measurable_fst)
      (hc.comp (measurable_fst.add (direction_continuous.measurable.comp measurable_snd)))).compl
  have hz (i : Fin k) (n : ℕ) : ∀ t : Angles, ∀ᵐ z ∂(volume : Measure ℂ),
      truncatedVector c hc i n z*truncatedVector c hc i n (z+direction t)=0 := by
    apply all_parameters_product_zero angularMeasure direction direction_continuous
    · filter_upwards [truncatedVector_ae c hc i n] with z hz
      rw [hz]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · filter_upwards [ho] with t ht
      filter_upwards [ht,truncatedVector_ae c hc i n,
        (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving.ae (truncatedVector_ae c hc i n)] with z hne h1 h2
      rw [h1,h2]
      by_cases h : z ∈ truncatedClass c i n
      · have hh : z+direction t ∉ truncatedClass c i n := fun hh => hne (h.1.trans hh.1.symm)
        simp [Set.indicator_of_notMem hh]
      · simp [Set.indicator_of_notMem h]
  intro t
  have hi : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin k, ∀ n : ℕ,
      ((truncatedClass c i n).indicator (fun _ => (1 : ℝ)) z)*
      ((truncatedClass c i n).indicator (fun _ => (1 : ℝ)) (z+direction t))=0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    filter_upwards [hz i n t,truncatedVector_ae c hc i n,
      (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving.ae (truncatedVector_ae c hc i n)] with z h0 h1 h2
    simpa only [h1,h2] using h0
  filter_upwards [hi] with z hz
  intro he
  obtain ⟨n,hn⟩ := exists_nat_gt (max ‖z‖ ‖z+direction t‖)
  have h1 : z ∈ truncatedClass c (c z) n := ⟨rfl,by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (lt_of_le_of_lt (le_max_left _ _) hn).le⟩
  have h2 : z+direction t ∈ truncatedClass c (c z) n := ⟨he.symm,by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (lt_of_le_of_lt (le_max_right _ _) hn).le⟩
  have h0 := hz (c z) n
  simp [Set.indicator_of_mem h1,Set.indicator_of_mem h2] at h0
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma densityOne_disjoint {A B : Set ℂ} (hB : MeasurableSet B)
    (hd : AEDisjoint volume A B) {x : ℂ} (hA : DensityOne A x) : ¬ DensityOne B x := by
  intro hb
  have hh := hA.add hb
  have hle : (1 : ENNReal)+1 ≤ 1 := le_of_tendsto hh (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [← ENNReal.add_div,← measure_union₀ (hB.inter measurableSet_closedBall).nullMeasurableSet
      (hd.mono inter_subset_left inter_subset_left)]
    apply (ENNReal.div_le_iff (Metric.measure_closedBall_pos volume x hr).ne'
      ((isCompact_closedBall x r).measure_ne_top)).mpr
    simpa only [one_mul] using measure_mono (union_subset inter_subset_right inter_subset_right))
  norm_num at hle
lemma densityOne_translate {A : Set ℂ} {x u : ℂ} :
    DensityOne ((fun z : ℂ => z+u) ⁻¹' A) x ↔ DensityOne A (x+u) := by
  have he (r : ℝ) : (fun z : ℂ => z+u) ⁻¹' (Metric.closedBall (x+u) r) = Metric.closedBall x r := by
    ext z
    simp only [Set.mem_preimage,Metric.mem_closedBall,dist_eq_norm,add_sub_add_right_eq_sub]
  have h1 (r : ℝ) : volume (((fun z : ℂ => z+u) ⁻¹' A) ∩ Metric.closedBall x r) =
      volume (A ∩ Metric.closedBall (x+u) r) := by
    rw [← he,← Set.preimage_inter,measure_preimage_add_right]
  have h2 (r : ℝ) : volume (Metric.closedBall x r) = volume (Metric.closedBall (x+u) r) := by
    rw [← he,measure_preimage_add_right]
  simp only [DensityOne,h1,h2]
lemma direction_exists {u : ℂ} (hu : ‖u‖=1) : ∃ t, direction t=u := by
  let v : Circle := ⟨u,mem_sphere_zero_iff_norm.mpr hu⟩
  obtain ⟨t,ht⟩ := Circle.exp_surjective v
  exact ⟨(t : Angles),by simpa only [direction_real] using congrArg Subtype.val ht⟩
lemma weak_density_proper {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    (i : Fin k) {x y : ℂ} (hxy : ‖x-y‖=1) (hx : DensityOne {z | c z=i} x) :
    ¬ DensityOne {z | c z=i} y := by
  let u := y-x
  obtain ⟨t,ht⟩ := direction_exists (u := u) (by simpa only [u,norm_sub_rev] using hxy)
  have hd : AEDisjoint volume {z | c z=i} ((fun z : ℂ => z+u) ⁻¹' {z | c z=i}) := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [weak_all_directions c hc hw t] with z hz
    rintro ⟨h1,h2⟩
    exact hz (by simpa only [ht] using h1.trans h2.symm)
  have hh := densityOne_disjoint ((measurableSet_eq_fun hc measurable_const).preimage
    (measurable_id.add_const u)) hd hx
  simp only [id_eq] at hh
  rw [densityOne_translate] at hh
  simpa only [u,add_sub_cancel] using hh
lemma ae_density_actual {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) :
    ∀ᵐ x ∂(volume : Measure ℂ), DensityOne {z | c z=c x} x := by
  have hh : ∀ᵐ x ∂(volume : Measure ℂ), ∀ i : Fin k,
      Tendsto (fun r : ℝ => volume ({z | c z=i} ∩ Metric.closedBall x r) / volume (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 (({z | c z=i} : Set ℂ).indicator (1 : ℂ → ENNReal) x)) :=
    ae_all_iff.mpr fun i => Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume
      (measurableSet_eq_fun hc measurable_const)
  filter_upwards [hh] with x hx
  simpa only [DensityOne,Set.indicator_of_mem (show x ∈ {z | c z=c x} from rfl),Pi.one_apply] using hx (c x)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Compactness
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
lemma oneL2_ae : oneL2 μ =ᵐ[μ] (fun _ => (1 : ℝ)) := by
  simpa only [oneL2,Set.indicator_univ] using (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
    (hμs := measure_ne_top μ Set.univ) (c := (1 : ℝ)))
lemma weak_limit_nonneg {f : ℕ → RealL2 μ} {b : RealL2 μ}
    (ht : ∀ v, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hf : ∀ n, 0 ≤ᵐ[μ] f n) : 0 ≤ᵐ[μ] b := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (MemLp.integrable (by norm_num) (Lp.memLp b))
  intro s hs hμs
  have h := ht (indicatorConstLp 2 hs hμs.ne 1)
  have he (v : RealL2 μ) : ⟪v,indicatorConstLp 2 hs hμs.ne 1⟫ = ∫ x in s, v x ∂μ := by
    rw [real_inner_comm,L2.inner_indicatorConstLp_one]
  simp_rw [he] at h
  exact ge_of_tendsto h (Eventually.of_forall fun n => integral_nonneg_of_ae (ae_restrict_of_ae (hf n)))
lemma weak_limit_le_one {f : ℕ → RealL2 μ} {b : RealL2 μ}
    (ht : ∀ v, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hf : ∀ n, f n ≤ᵐ[μ] (fun _ => (1 : ℝ))) : b ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
  have hh : 0 ≤ᵐ[μ] (oneL2 μ-b) := weak_limit_nonneg μ
    (f := fun n => oneL2 μ-f n) (fun v => by simpa only [inner_sub_left] using tendsto_const_nhds.sub (ht v)) (fun n => by
      filter_upwards [Lp.coeFn_sub (oneL2 μ) (f n),oneL2_ae μ,hf n] with x hx h1 hn
      simpa only [hx,Pi.sub_apply,Pi.zero_apply,h1,sub_nonneg] using hn)
  filter_upwards [hh,Lp.coeFn_sub (oneL2 μ) b,oneL2_ae μ] with x hx he h1
  simpa only [he,Pi.sub_apply,Pi.zero_apply,h1,sub_nonneg] using hx
lemma weak_limit_sum {ι : Type*} [Fintype ι] {f : ℕ → ι → RealL2 μ} {b : ι → RealL2 μ}
    (ht : ∀ i v, Tendsto (fun n => ⟪f n i,v⟫) atTop (𝓝 ⟪b i,v⟫))
    (hf : ∀ n, ∑ i, f n i = oneL2 μ) : ∑ i, b i = oneL2 μ := by
  apply ext_inner_right ℝ
  intro v
  have hh := tendsto_finsetSum Finset.univ (fun i _ => ht i v)
  simp_rw [← sum_inner,hf] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma ae_typicalSampling (hc : Measurable c) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂(volume : Measure ℂ), TypicalSampling c y r := by
  have hq : QuasiMeasurePreserving (fun p : ℂ × Angles => p.1+(r : ℂ)*direction p.2)
      ((volume : Measure ℂ).prod angularMeasure) volume :=
    QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (measurable_const.mul (direction_continuous.measurable.comp measurable_snd)))
      (Eventually.of_forall fun t => (measurePreserving_add_right (volume : Measure ℂ)
        ((r : ℂ)*direction t)).quasiMeasurePreserving)
  have hh : ∀ᵐ p ∂((volume : Measure ℂ).prod angularMeasure), Typical c (p.1+(r : ℂ)*direction p.2) :=
    hq.ae (ae_density_actual c hc)
  exact (Measure.ae_ae_of_ae_prod hh).mono fun y hy => ⟨hr,hy⟩
lemma sample_sum (hc : Measurable c) (y : ℂ) (r : ℝ) :
    ∑ i, sample c hc y r i = oneL2 angularMeasure := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => sample c hc y r i),
    ae_all_iff.mpr (sample_ae c hc y r),oneL2_ae angularMeasure] with t ht ha h1
  rw [ht,h1]
  simp only [ha,sampleFn]
  simp
end EuclideanFiveColor
end

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor.WeakBall
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
omit [TopologicalSpace.SeparableSpace E] in
lemma value_eval (a : Space E) (v : E) : ⟪value E a,v⟫ = a.1 v := by
  simp only [value,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply]
omit [TopologicalSpace.SeparableSpace E] in
lemma tendsto_iff {I : Type*} {l : Filter I} {f : I → Space E} {b : Space E} :
    Tendsto f l (𝓝 b) ↔ ∀ v : E, Tendsto (fun n => ⟪value E (f n),v⟫) l (𝓝 ⟪value E b,v⟫) := by
  simp only [value_eval]
  rw [tendsto_subtype_rng, tendsto_iff_forall_eval_tendsto_topDualPairing]
  rfl
end EuclideanFiveColor.WeakBall
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
lemma bounded_test_error {f v g : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfb : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1) (hv : Integrable v μ) (hg : Integrable g μ) :
    dist (∫ x, f x*v x ∂μ) (∫ x, f x*g x ∂μ) ≤ ∫ x, ‖v x-g x‖ ∂μ := by
  have hft : MemLp f ⊤ μ := MemLp.of_bound hf 1 hfb
  have hiv : Integrable (fun x => f x*v x) μ := hv.mul_of_top_right hft
  have hig : Integrable (fun x => f x*g x) μ := hg.mul_of_top_right hft
  rw [dist_eq_norm,← integral_sub hiv hig]
  calc
    _ ≤ ∫ x, ‖f x*v x-f x*g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖v x-g x‖ ∂μ := by
      apply integral_mono_ae ((hv.mul_of_top_right hft).sub (hg.mul_of_top_right hft)).norm (hv.sub hg).norm
      filter_upwards [hfb] with x hx
      change ‖f x * v x - f x * g x‖ ≤ ‖v x - g x‖
      rw [← mul_sub,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
lemma weak_L2_to_weakStar {f : ℕ → Lp ℝ 2 μ} {b : Lp ℝ 2 μ}
    (hf : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ 1) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ 1)
    (ht : ∀ v : Lp ℝ 2 μ, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    {v : X → ℝ} (hv : Integrable v μ) :
    Tendsto (fun n => ∫ x, f n x*v x ∂μ) atTop (𝓝 (∫ x, b x*v x ∂μ)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g,hg,hgm⟩ := (memLp_one_iff_integrable.mpr hv).exists_simpleFunc_eLpNorm_sub_lt (by simp : (1 : ENNReal) ≠ ⊤)
    (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < ε/3))
  obtain ⟨C,hC⟩ := g.exists_forall_norm_le
  have hg2 : MemLp g 2 μ := MemLp.of_bound g.measurable.aestronglyMeasurable C (Eventually.of_forall hC)
  have hgi : Integrable (fun x => g x) μ := memLp_one_iff_integrable.mp hgm
  have herr : (∫ x, ‖v x-g x‖ ∂μ) < ε/3 := by
    change (∫ x, ‖(v - (fun x => g x)) x‖ ∂μ) < ε/3
    rw [integral_norm_eq_lintegral_enorm (hv.sub hgi).aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm]
    exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hg) ENNReal.ofReal_ne_top).mpr hg |>.trans_eq (ENNReal.toReal_ofReal (by positivity))
  have he (w : Lp ℝ 2 μ) : ⟪w,hg2.toLp g⟫ = ∫ x, w x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with x hx
    simp [hx, mul_comm]
  have htt := ht (hg2.toLp g)
  simp_rw [he] at htt
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp htt (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h1 := bounded_test_error (Lp.aestronglyMeasurable (f n)) (hf n) hv hgi
  have h2 := bounded_test_error (Lp.aestronglyMeasurable b) hb hv hgi
  calc
    _ ≤ dist (∫ x, f n x*v x ∂μ) (∫ x, f n x*g x ∂μ) +
        dist (∫ x, f n x*g x ∂μ) (∫ x, b x*g x ∂μ) +
        dist (∫ x, b x*g x ∂μ) (∫ x, b x*v x ∂μ) := by
      exact dist_triangle4 _ _ _ _
    _ < ε := by rw [dist_comm (∫ x, b x*g x ∂μ)]; linarith [hN n hn]
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma trace_realization {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    ∃ y : ℕ → ℂ, ∃ r : ℕ → ℝ, (∀ n, TypicalSampling c (y n) (r n)) ∧
      Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 1) ∧
      Tendsto (fun n => sampleCode c hc (y n) (r n)) atTop (𝓝 b) := by
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp hb
  simp only [nhds_prod_eq] at ht
  refine ⟨fun n => (p n).1,fun n => (p n).2.1,fun n => (hp n).1,ht.fst,ht.snd.fst,?_⟩
  simpa only [show (fun n => (p n).2.2) = (fun n => sampleCode c hc (p n).1 (p n).2.1) from
    funext fun n => (hp n).2] using ht.snd.snd
lemma trace_of_realization {x : ℂ} {b : TraceVector k} {y : ℕ → ℂ} {r : ℕ → ℝ}
    (htr : ∀ n, TypicalSampling c (y n) (r n)) (hy : Tendsto y atTop (𝓝 x))
    (hr : Tendsto r atTop (𝓝 1))
    (hb : Tendsto (fun n => sampleCode c hc (y n) (r n)) atTop (𝓝 b)) : IsTrace c hc x b := by
  exact mem_closure_of_tendsto (hy.prodMk_nhds (hr.prodMk_nhds hb))
    (Eventually.of_forall fun n => show (y n,r n,sampleCode c hc (y n) (r n)) ∈ sampleSet c hc from ⟨htr n,rfl⟩)
lemma traceCode_tendsto_iff {I : Type*} {l : Filter I} {f : I → TraceVector k} {b : TraceVector k} :
    Tendsto f l (𝓝 b) ↔ ∀ i v, Tendsto (fun n => ⟪traceValue (f n) i,v⟫) l (𝓝 ⟪traceValue b i,v⟫) := by
  rw [tendsto_pi_nhds]
  exact forall_congr' fun i => WeakBall.tendsto_iff _
lemma trace_bounds {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    (∀ i, 0 ≤ᵐ[angularMeasure] traceValue b i) ∧
    (∀ i, traceValue b i ≤ᵐ[angularMeasure] (fun _ => (1 : ℝ))) ∧
    ∑ i, traceValue b i = oneL2 angularMeasure := by
  obtain ⟨y,r,_,_,_,ht⟩ := trace_realization c hc hb
  have hw := traceCode_tendsto_iff.mp ht
  simp only [traceValue_sampleCode] at hw
  refine ⟨?_,?_,?_⟩
  · intro i
    apply weak_limit_nonneg angularMeasure (hw i)
    intro n
    filter_upwards [sample_ae c hc (y n) (r n) i] with t he
    simpa only [he,Pi.zero_apply] using sampleFn_nonneg c (y n) (r n) i t
  · intro i
    apply weak_limit_le_one angularMeasure (hw i)
    intro n
    filter_upwards [sample_ae c hc (y n) (r n) i] with t he
    simpa only [he] using sampleFn_le_one c (y n) (r n) i t
  · exact weak_limit_sum angularMeasure hw (fun n => sample_sum c hc (y n) (r n))
lemma trace_realization_weakStar {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    ∃ y : ℕ → ℂ, ∃ r : ℕ → ℝ, (∀ n, TypicalSampling c (y n) (r n)) ∧
      Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 1) ∧
      ∀ i (v : Angles → ℝ), Integrable v angularMeasure →
        Tendsto (fun n => ∫ t, sampleFn c (y n) (r n) i t*v t ∂angularMeasure) atTop
          (𝓝 (∫ t, traceValue b i t*v t ∂angularMeasure)) := by
  obtain ⟨y,r,hy,hyt,hrt,hbt⟩ := trace_realization c hc hb
  refine ⟨y,r,hy,hyt,hrt,fun i v hv => ?_⟩
  have hbounds := trace_bounds c hc hb
  have hbn : ∀ᵐ t ∂angularMeasure, ‖traceValue b i t‖ ≤ 1 := by
    filter_upwards [hbounds.1 i,hbounds.2.1 i] with t ht1 ht2
    rwa [Real.norm_eq_abs,abs_of_nonneg ht1]
  have hsn (n : ℕ) : ∀ᵐ t ∂angularMeasure, ‖sample c hc (y n) (r n) i t‖ ≤ 1 := by
    filter_upwards [sample_ae c hc (y n) (r n) i] with t ht
    rw [ht,Real.norm_eq_abs,abs_of_nonneg (sampleFn_nonneg c _ _ _ t)]
    exact sampleFn_le_one c _ _ _ t
  have hw := weak_L2_to_weakStar hsn hbn
    (by simpa only [traceValue_sampleCode] using (traceCode_tendsto_iff.mp hbt) i) hv
  convert hw using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  exact (integral_congr_ae ((sample_ae c hc (y n) (r n) i).mono fun t ht => congrArg (fun a => a*v t) ht)).symm
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Palettes
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma tracePositive_le_palette (x : ℂ) (i : Fin k) (b : Traces c hc x) :
    tracePositive c hc x i b ≤ᵐ[angularMeasure] paletteSet c hc x i :=
  (exists_countable_essential_union angularMeasure (tracePositive c hc x i) (tracePositive_measurable c hc x i)).choose_spec.2 b
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PaletteDensity
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
lemma weak_strong_disjoint {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : ℕ → X → ℝ} {b : X → ℝ} {G : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hF : ∀ n, Measurable (F n)) (hb : Measurable b)
    (hG : ∀ n, Measurable (G n)) (hg : Measurable g)
    (hFb : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (hbb : ∀ᵐ x ∂μ, 0 ≤ b x ∧ b x ≤ 1)
    (hGb : ∀ n p, 0 ≤ G n p ∧ G n p ≤ 1)
    (hgb : ∀ p, 0 ≤ g p ∧ g p ≤ 1)
    (hw : ∀ v : X → ℝ, Integrable v μ →
      Tendsto (fun n => ∫ x, F n x*v x ∂μ) atTop (𝓝 (∫ x, b x*v x ∂μ)))
    (hs : Tendsto (fun n => ∫ p, ‖G n p-g p‖ ∂μ.prod ν) atTop (𝓝 0))
    (hz : ∀ n, ∀ᵐ p ∂μ.prod ν, F n p.1*G n p=0) :
    ∀ᵐ p ∂μ.prod ν, b p.1*g p=0 := by
  have hgi : Integrable g (μ.prod ν) := Integrable.of_bound hg.aestronglyMeasurable 1
    (Eventually.of_forall fun p => by rw [Real.norm_eq_abs,abs_of_nonneg (hgb p).1]; exact (hgb p).2)
  have hFi (n : ℕ) : Integrable (fun p : X × Y => F n p.1*g p) (μ.prod ν) := by
    apply Integrable.of_bound (((hF n).comp measurable_fst).mul hg).aestronglyMeasurable 1
    exact Eventually.of_forall fun p => by
      change ‖F n p.1*g p‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hFb n p.1).1 (hgb p).1)]
      exact (mul_le_of_le_one_left (hgb p).1 (hFb n p.1).2).trans (hgb p).2
  have hbi : Integrable (fun p : X × Y => b p.1*g p) (μ.prod ν) := by
    apply Integrable.of_bound ((hb.comp measurable_fst).mul hg).aestronglyMeasurable 1
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbb] with p hp
    change ‖b p.1*g p‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp.1 (hgb p).1)]
    exact (mul_le_of_le_one_left (hgb p).1 hp.2).trans (hgb p).2
  have herr (n : ℕ) : Integrable (fun p => ‖G n p-g p‖) (μ.prod ν) := by
    apply Integrable.of_bound ((hG n).sub hg).norm.aestronglyMeasurable 1
    exact Eventually.of_forall fun p => by
      rw [norm_norm,Real.norm_eq_abs,abs_le]
      change -1 ≤ G n p-g p ∧ G n p-g p ≤ 1
      constructor <;> linarith [(hGb n p).1,(hGb n p).2,(hgb p).1,(hgb p).2]
  have hi0 : Tendsto (fun n => ∫ p, F n p.1*g p ∂μ.prod ν) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun p => mul_nonneg (hFb n p.1).1 (hgb p).1) _ hs
    intro n
    apply integral_mono_ae (hFi n) (herr n)
    filter_upwards [hz n] with p hp
    rw [Real.norm_eq_abs]
    calc
      F n p.1*g p = F n p.1*(g p-G n p) := by rw [mul_sub,hp,sub_zero]
      _ ≤ |g p-G n p| := by
        calc
          _ ≤ F n p.1*|g p-G n p| := mul_le_mul_of_nonneg_left (le_abs_self _) (hFb n p.1).1
          _ ≤ 1*|g p-G n p| := mul_le_mul_of_nonneg_right (hFb n p.1).2 (abs_nonneg _)
          _ = _ := one_mul _
      _ = |G n p-g p| := abs_sub_comm _ _
  let v : X → ℝ := fun x => ∫ y, g (x,y) ∂ν
  have hvi : Integrable v μ := hgi.integral_prod_left
  have hlim := hw v hvi
  have hconvert (f : X → ℝ) (hi : Integrable (fun p : X × Y => f p.1*g p) (μ.prod ν)) :
      (∫ p, f p.1*g p ∂μ.prod ν) = ∫ x, f x*v x ∂μ := by
    rw [integral_prod _ hi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      exact integral_const_mul (f x) (fun y => g (x,y))
  have he0 : (∫ p, b p.1*g p ∂μ.prod ν)=0 := by
    have ht : Tendsto (fun n => ∫ p, F n p.1*g p ∂μ.prod ν) atTop
        (𝓝 (∫ p, b p.1*g p ∂μ.prod ν)) := by
      simpa only [hconvert b hbi,hconvert (F _) (hFi _)] using hlim
    exact tendsto_nhds_unique ht hi0
  exact (integral_eq_zero_iff_of_nonneg_ae
    ((Measure.quasiMeasurePreserving_fst.ae hbb).mono fun p hp => mul_nonneg hp.1 (hgb p).1) hbi).mp he0
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
include hc in
lemma colorIndicator_measurable (i : Fin k) : Measurable (colorIndicator c i) :=
  measurable_one.piecewise (measurableSet_eq_fun hc measurable_const) measurable_zero
lemma colorIndicator_bounds (i : Fin k) (z : ℂ) : 0 ≤ colorIndicator c i z ∧ colorIndicator c i z ≤ 1 := by
  simp only [colorIndicator]; split_ifs <;> norm_num
include hc in
lemma sample_pair_disjoint (hw : WeakColoring k c) {y : ℂ} {r : ℝ}
    (hy : TypicalSampling c y r) (i : Fin k) :
    ∀ᵐ p ∂angularMeasure.prod angularMeasure,
      sampleFn c y r i p.1*colorIndicator c i (angularSum y r p)=0 := by
  have h1 : ∀ᵐ p ∂angularMeasure.prod angularMeasure, Typical c (y+(r : ℂ)*direction p.1) :=
    Measure.quasiMeasurePreserving_fst.ae hy.2
  have h2 := (angularSum_quasiMeasurePreserving y hy.1.ne').ae (ae_density_actual c hc)
  filter_upwards [h1,h2] with p hp1 hp2
  by_cases ha : c (y+(r : ℂ)*direction p.1)=i
  · have hb : c (angularSum y r p) ≠ i := by
      intro hb
      have hdist : ‖(y+(r : ℂ)*direction p.1)-angularSum y r p‖=1 := by
        simp [angularSum]
      apply weak_density_proper c hc hw i hdist
      · simpa only [Typical,ha] using hp1
      · simpa only [hb] using hp2
    simp [sampleFn,colorIndicator,ha,hb]
  · simp [sampleFn,ha]
lemma trace_pair_disjoint (hw : WeakColoring k c) {x : ℂ} {b : TraceVector k}
    (hb : IsTrace c hc x b) (i : Fin k) :
    ∀ᵐ p ∂angularMeasure.prod angularMeasure,
      traceValue b i p.1*colorIndicator c i (angularSum x 1 p)=0 := by
  obtain ⟨y,r,ht,hy,hr,hweak⟩ := trace_realization_weakStar c hc hb
  have hbnd := trace_bounds c hc hb
  apply weak_strong_disjoint (F := fun n => sampleFn c (y n) (r n) i)
    (G := fun n p => colorIndicator c i (angularSum (y n) (r n) p))
    (fun n => sampleFn_measurable c hc (y n) (r n) i) (Lp.stronglyMeasurable _).measurable
    (fun n => (colorIndicator_measurable c hc i).comp (angularSum_measurable _ _))
    ((colorIndicator_measurable c hc i).comp (angularSum_measurable _ _))
    (fun n t => ⟨sampleFn_nonneg c _ _ _ t,sampleFn_le_one c _ _ _ t⟩)
    (Eventually.and (hbnd.1 i) (hbnd.2.1 i))
    (fun n p => colorIndicator_bounds c i _) (fun p => colorIndicator_bounds c i _)
    (hweak i) (angularSum_tendsto_L1 hr hy (colorIndicator_measurable c hc i) (colorIndicator_bounds c i))
    (fun n => sample_pair_disjoint c hc hw (ht n) i)
lemma palette_first_exclusion (hw : WeakColoring k c) (x : ℂ) (i : Fin k) :
    ∀ᵐ p ∂angularMeasure.prod angularMeasure,
      p.1 ∈ paletteSet c hc x i → c (angularSum x 1 p) ≠ i := by
  have hall : ∀ᵐ p ∂angularMeasure.prod angularMeasure, ∀ b ∈ paletteGenerators c hc x i,
      traceValue b.1 i p.1*colorIndicator c i (angularSum x 1 p)=0 :=
    (ae_ball_iff (paletteGenerators_countable c hc x i)).mpr
      (fun b _ => trace_pair_disjoint c hc hw b.2 i)
  filter_upwards [hall] with p hp
  intro hm he
  obtain ⟨b,hb,hpos⟩ := Set.mem_iUnion₂.mp hm
  have hzero := hp b hb
  have hval : colorIndicator c i (angularSum x 1 p)=1 := by simp [colorIndicator,he]
  rw [hval,mul_one] at hzero
  exact (show 0 < traceValue b.1 i p.1 from hpos).ne' hzero
end EuclideanFiveColor

end

noncomputable section
open MeasureTheory Set
namespace EuclideanFiveColor
lemma angleMk_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving ((↑) : ℝ → Angles) volume angularMeasure := by
  have hm : Measurable ((↑) : ℝ → Angles) := (AddCircle.measurePreserving_mk (2*Real.pi) 0).measurable
  refine ⟨hm,Measure.AbsolutelyContinuous.mk (fun A hA hz => ?_)⟩
  rw [Measure.map_apply hm hA]
  have hzv : (volume : Measure Angles) A=0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,Measure.smul_apply]
    change ENNReal.ofReal (2*Real.pi) * angularMeasure A=0
    rw [hz,mul_zero]
  have hh (n : ℤ) : volume (((↑) : ℝ → Angles) ⁻¹' A ∩
      Ioc (n • (2*Real.pi)) ((n+1) • (2*Real.pi)))=0 := by
    have h := (AddCircle.measurePreserving_mk (2*Real.pi) (n • (2*Real.pi))).quasiMeasurePreserving.preimage_null hzv
    rw [Measure.restrict_apply' measurableSet_Ioc] at h
    simpa only [add_zsmul,one_zsmul] using h
  have hcov := iUnion_Ioc_zsmul (by positivity : 0 < 2*Real.pi)
  have he : ((↑) : ℝ → Angles) ⁻¹' A = ⋃ n : ℤ,
      ((↑) : ℝ → Angles) ⁻¹' A ∩ Ioc (n • (2*Real.pi)) ((n+1) • (2*Real.pi)) := by
    rw [← inter_iUnion,hcov,inter_univ]
  rw [he]
  exact measure_iUnion_null hh
lemma anglePair_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ => ((p.1 : Angles),(p.2 : Angles)))
      volume (angularMeasure.prod angularMeasure) := by
  exact QuasiMeasurePreserving.prodMap angleMk_quasiMeasurePreserving
    angleMk_quasiMeasurePreserving
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma volume_image_bound {F : ℝ × ℝ → ℝ × ℝ} {s : Set (ℝ × ℝ)} {K : ℝ≥0}
    (hF : LipschitzWith K (s.domRestrict F)) (A : Set (ℝ × ℝ)) (hA : A ⊆ s) :
    volume (F '' A) ≤ (K : ENNReal)^2 * volume A := by
  let B : Set s := Subtype.val ⁻¹' A
  have he1 : (s.domRestrict F) '' B = F '' A := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩; exact ⟨z.1,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩; exact ⟨⟨z,hA hz⟩,hz,rfl⟩
  have he2 : Subtype.val '' B = A := by
    ext z
    exact ⟨fun ⟨q,hq,he⟩ => he ▸ hq,fun hz => ⟨⟨z,hA hz⟩,hz,rfl⟩⟩
  have hi := (isometry_subtype_coe : Isometry (Subtype.val : s → ℝ × ℝ)).hausdorffMeasure_image
    (Or.inl (by norm_num : (0 : ℝ)≤2)) B
  have ha := hF.hausdorffMeasure_image_le (by norm_num : (0 : ℝ)≤2) B
  rw [he1,hausdorffMeasure_prod_real,ENNReal.rpow_two] at ha
  rw [he2,hausdorffMeasure_prod_real] at hi
  rwa [← hi] at ha
lemma flatDensityZero_prod {D : Set ℝ} {t u : ℝ} (hD : LineDensityZero D t) :
    FlatDensityZero (D ×ˢ univ) (t,u) := by
  have h := hD.const_mul 2
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp : 0 < r := hr
  rw [← closedBall_prod_same,prod_inter_prod,univ_inter,Measure.volume_eq_prod]
  simp only [Measure.real,Measure.prod_prod,ENNReal.toReal_mul,Real.volume_closedBall,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*r)]
  change 2*(volume.real (D ∩ Metric.closedBall t r)/r) =
    volume.real (D ∩ Metric.closedBall t r)*(2*r)/r^2
  field_simp [hp.ne']
lemma tendsto_pos_mul_nhdsWithin {a : ℝ} (ha : 0<a) :
    Tendsto (fun r : ℝ => a*r) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0)))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos ha hr
lemma FlatDensityZero.image {D s : Set (ℝ × ℝ)} {p : ℝ × ℝ} {F : ℝ × ℝ → ℝ × ℝ}
    {K L : ℝ≥0} (hD : FlatDensityZero D p) (hps : p ∈ s)
    (hF : LipschitzWith K (s.domRestrict F)) (hA : AntilipschitzWith L (s.domRestrict F))
    (hL : 0 < L) : FlatDensityZero (F '' (D ∩ s)) (F p) := by
  have h := (hD.comp (tendsto_pos_mul_nhdsWithin (show 0 < (L : ℝ) from hL))).const_mul
    ((K : ℝ)^2*(L : ℝ)^2)
  simp only [mul_zero] at h
  apply squeeze_zero' (Eventually.of_forall fun r => div_nonneg measureReal_nonneg (sq_nonneg r)) _ h
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp : 0 < r := hr
  let E : Set (ℝ × ℝ) := D ∩ s ∩ Metric.closedBall p ((L : ℝ)*r)
  have he : F '' (D ∩ s) ∩ Metric.closedBall (F p) r ⊆ F '' E := by
    rintro z ⟨⟨q,hq,rfl⟩,hz⟩
    refine ⟨q,⟨hq,?_⟩,rfl⟩
    exact (hA.le_mul_dist ⟨q,hq.2⟩ ⟨p,hps⟩).trans
      (mul_le_mul_of_nonneg_left hz L.2)
  have hm := (measure_mono he).trans (volume_image_bound hF E (fun q hq => hq.1.2))
  have hsub : E ⊆ D ∩ Metric.closedBall p ((L : ℝ)*r) := fun q hq => ⟨hq.1.1,hq.2⟩
  have hfin : volume (D ∩ Metric.closedBall p ((L : ℝ)*r)) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall _ _).measure_ne_top (measure_mono inter_subset_right)
  have hm' := hm.trans (mul_le_mul (le_refl _) (measure_mono hsub) bot_le bot_le)
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by finiteness) hfin) hm'
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.coe_toReal] at hreal
  calc
    _ ≤ (K : ℝ)^2*volume.real (D ∩ Metric.closedBall p ((L : ℝ)*r))/r^2 :=
      div_le_div_of_nonneg_right hreal (sq_nonneg r)
    _ = _ := by
      change _ = ((K : ℝ)^2*(L : ℝ)^2)*
        (volume.real (D ∩ Metric.closedBall p ((L : ℝ)*r))/((L : ℝ)*r)^2)
      have hLr : (L : ℝ) ≠ 0 := ne_of_gt hL
      field_simp [hp.ne',hLr]
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma FlatDensityZero.of_locally_le {A B s : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    (hb : FlatDensityZero B p) (hs : s ∈ 𝓝 p) (hAB : (A ∩ s : Set (ℝ × ℝ)) ≤ᵐ[volume] B) :
    FlatDensityZero A p := by
  obtain ⟨δ,hδ,hsδ⟩ := Metric.mem_nhds_iff.mp hs
  apply squeeze_zero' (Eventually.of_forall fun r => div_nonneg measureReal_nonneg (sq_nonneg r)) _ hb
  filter_upwards [(eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hr
  apply div_le_div_of_nonneg_right _ (sq_nonneg r)
  apply ENNReal.toReal_mono
  · exact ne_top_of_le_ne_top (isCompact_closedBall p r).measure_ne_top (measure_mono inter_subset_right)
  · apply measure_mono_ae
    filter_upwards [hAB] with q hq
    intro hqa
    exact ⟨hq ⟨hqa.1,hsδ (Metric.closedBall_subset_ball hr hqa.2)⟩,hqa.2⟩
lemma FlatDensityZero.transport {A D s : Set (ℝ × ℝ)} {p : ℝ × ℝ}
    {F : ℝ × ℝ → ℝ × ℝ} {K L : ℝ≥0} (hD : FlatDensityZero D p)
    (hps : p ∈ s) (hs : F '' s ∈ 𝓝 (F p))
    (hF : LipschitzWith K (s.domRestrict F)) (hA : AntilipschitzWith L (s.domRestrict F))
    (hL : 0 < L) (hAD : (F ⁻¹' A ∩ s : Set (ℝ × ℝ)) ≤ᵐ[volume] D) : FlatDensityZero A (F p) := by
  let N := (F ⁻¹' A ∩ s) \ D
  have hN : volume N=0 := measure_eq_zero_iff_ae_notMem.mpr (hAD.mono fun q hq h => h.2 (hq h.1))
  have himg : volume (F '' N)=0 := by
    apply le_antisymm _ (zero_le : (0 : ENNReal) ≤ volume (F '' N))
    simpa only [hN,mul_zero] using volume_image_bound hF N (fun q hq => hq.1.2)
  apply (hD.image hps hF hA hL).of_locally_le hs
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp himg] with q hq
  rintro ⟨hqa,⟨t,ht,rfl⟩⟩
  by_cases hd : t ∈ D
  · exact ⟨t,⟨hd,ht⟩,rfl⟩
  · exact (hq ⟨t,⟨⟨hqa,ht⟩,hd⟩,rfl⟩).elim
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma circleSum_one_lipschitz : LipschitzWith 2 (circleSum 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have h₁ := realDirection_lipschitz.dist_le_mul a.1 b.1
  have h₂ := realDirection_lipschitz.dist_le_mul a.2 b.2
  have h := dist_add_add_le (Real.cos a.1,Real.sin a.1) (Real.cos a.2,Real.sin a.2)
    (Real.cos b.1,Real.sin b.1) (Real.cos b.2,Real.sin b.2)
  have he (p : RealPlane) : circleSum 1 p =
      (Real.cos p.1,Real.sin p.1)+(Real.cos p.2,Real.sin p.2) := by simp [circleSum]
  rw [he a,he b]
  norm_num only [NNReal.coe_ofNat,NNReal.coe_one,one_mul] at *
  have ha : dist a.1 b.1 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hb : dist a.2 b.2 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_right _ _
  linarith
lemma circleSum_densityZero {D : Set ℝ} {A : Set RealPlane} {t u : ℝ} (x : RealPlane)
    (hD : LineDensityZero D t) (hu : Real.sin (u-t) ≠ 0)
    (hAD : ∀ᵐ q : RealPlane ∂volume, x+circleSum 1 q ∈ A → q.1 ∈ D) :
    FlatDensityZero A (x+circleSum 1 (t,u)) := by
  let F : RealPlane → RealPlane := fun q => x+circleSum 1 q
  have hreg : (1 : ℝ)*Real.sin (u-t) ≠ 0 := by simpa only [one_mul] using hu
  obtain ⟨s,hso,hps,K,hK⟩ := circleSum_local_antilipschitz (r := 1) (p := (t,u)) hreg
  have ha : AntilipschitzWith (K+1) (s.domRestrict F) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro a b
    have h := hK.le_mul_dist a b
    simp only [domRestrict] at h
    simp only [domRestrict,F,dist_add_left,NNReal.coe_add,NNReal.coe_one]
    nlinarith [dist_nonneg (x := circleSum 1 a.1) (y := circleSum 1 b.1)]
  let L := circleSumDerivEquiv (r := 1) (p := (t,u)) hreg
  have hd : HasStrictFDerivAt F (L : RealPlane →L[ℝ] RealPlane) (t,u) :=
    (circleSum_strict 1 (t,u)).const_add x
  have him : F '' s ∈ 𝓝 (F (t,u)) := by
    rw [← hd.map_nhds_eq_of_equiv]
    exact image_mem_map (hso.mem_nhds hps)
  have hl : LipschitzWith 2 F := LipschitzWith.of_dist_le_mul fun a b => by
    simpa only [F,dist_add_left] using circleSum_one_lipschitz.dist_le_mul a b
  apply (flatDensityZero_prod hD).transport hps him
    (show LipschitzWith 2 (s.domRestrict F) from fun a b => hl a.1 b.1) ha (by positivity)
  filter_upwards [hAD] with q hq
  rintro ⟨hm,_⟩
  exact ⟨hq hm,mem_univ _⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma complex_ball_flat_ball {z w : ℂ} {r : ℝ} (h : w ∈ Metric.closedBall z r) :
    Complex.equivRealProdCLM w ∈ Metric.closedBall (Complex.equivRealProdCLM z) r := by
  rw [Metric.mem_closedBall,dist_eq_norm] at h ⊢
  change max ‖w.re-z.re‖ ‖w.im-z.im‖ ≤ r
  simpa only [Real.norm_eq_abs,Complex.sub_re,Complex.sub_im] using
    max_le ((Complex.abs_re_le_norm (w-z)).trans h) ((Complex.abs_im_le_norm (w-z)).trans h)
lemma flat_to_complex_densityZero {A : Set ℂ} {z : ℂ}
    (h : FlatDensityZero (Complex.equivRealProdCLM.symm ⁻¹' A) (Complex.equivRealProdCLM z)) :
    Tendsto (fun r : ℝ => volume (A ∩ Metric.closedBall z r)/volume (Metric.closedBall z r))
      (𝓝[>] 0) (𝓝 (0 : ENNReal)) := by
  have ht := h.const_mul (Real.pi)⁻¹
  simp only [mul_zero] at ht
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  simp only [ENNReal.ofReal_zero] at he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp : 0 < r := hr
  let B := Complex.equivRealProdCLM.symm ⁻¹' A ∩ Metric.closedBall (Complex.equivRealProdCLM z) r
  have hm : volume (A ∩ Metric.closedBall z r) ≤ (volume : Measure (ℝ × ℝ)) B := by
    apply (measure_mono (t := Complex.equivRealProdCLM ⁻¹' B) ?_).trans
      (Complex.volume_preserving_equiv_real_prod.measure_preimage_le B)
    intro w hw
    exact ⟨by simpa only [Set.mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using hw.1,complex_ball_flat_ball hw.2⟩
  have hfin : (volume : Measure (ℝ × ℝ)) B ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall _ _).measure_ne_top (measure_mono inter_subset_right)
  have hfinA : volume (A ∩ Metric.closedBall z r) ≠ ⊤ := ne_top_of_le_ne_top (isCompact_closedBall z r).measure_ne_top
    (measure_mono (s := A ∩ Metric.closedBall z r) inter_subset_right)
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top hfinA
    (Metric.measure_closedBall_pos volume z hp).ne') ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_div,Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hp.le,ENNReal.coe_toReal,NNReal.coe_real_pi,
    ENNReal.toReal_ofReal (by positivity)]
  calc
    _ ≤ volume.real B/(r^2*Real.pi) := div_le_div_of_nonneg_right (ENNReal.toReal_mono hfin hm) (by positivity)
    _ = _ := by dsimp [B]; ring
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_spatial_densityZero (hw : WeakColoring k c) {x : ℂ} {i : Fin k} {t u : ℝ}
    (ht : LineDensityZero (liftPalette c hc x i)ᶜ t) (hu : Real.sin (u-t) ≠ 0) :
    Tendsto (fun r : ℝ => volume ({z | c z=i} ∩ Metric.closedBall (angularSum x 1 (angleChart (t,u))) r)/
      volume (Metric.closedBall (angularSum x 1 (angleChart (t,u))) r))
        (𝓝[>] 0) (𝓝 (0 : ENNReal)) := by
  apply flat_to_complex_densityZero
  have he := anglePair_quasiMeasurePreserving.ae (palette_first_exclusion c hc hw x i)
  have hAD : ∀ᵐ q : RealPlane ∂volume, Complex.equivRealProdCLM x+circleSum 1 q ∈
      Complex.equivRealProdCLM.symm ⁻¹' {z | c z=i} → q.1 ∈ (liftPalette c hc x i)ᶜ := by
    filter_upwards [he] with q hq hm hd
    apply hq hd
    change c (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM x+circleSum 1 q))=i at hm
    change c (angularSum x 1 (angleChart q))=i
    rwa [angularSum_chart]
  have hb := circleSum_densityZero (Complex.equivRealProdCLM x) ht hu hAD
  rwa [← circleSum_chart x 1 (t,u)] at hb
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PaletteTransport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma ae_of_locally_ae {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) {S : Set X} {P : X → Prop}
    (h : ∀x∈S,∃U : Set X,IsOpen U ∧ x∈U ∧ ∀ᵐy∂μ,y∈U → P y) :
    ∀ᵐx∂μ,x∈S → P x := by
  choose U ho hm ha using fun x : S => h x x.2
  obtain ⟨T,hT,hcov⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover U ho
    (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩,hm ⟨x,hx⟩⟩)
  have hh : ∀ᵐy∂μ,∀x∈T,y∈U x → P y := (ae_ball_iff hT).mpr (fun x _ => ha x)
  filter_upwards [hh] with y hy hs
  obtain ⟨x,hx,hyU⟩ := mem_iUnion₂.mp (hcov hs)
  exact hy x hx hyU
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_States
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma LineDensityZero.mono_ae {A B : Set ℝ} {t : ℝ}
    (hB : LineDensityZero B t) (hAB : A≤ᵐ[volume] B) : LineDensityZero A t := by
  apply squeeze_zero' ?_ ?_ hB
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonneg measureReal_nonneg (le_of_lt hr)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    apply div_le_div_of_nonneg_right _ (le_of_lt hr)
    apply ENNReal.toReal_mono
    · exact ne_top_of_le_ne_top (isCompact_closedBall t r).measure_ne_top (measure_mono inter_subset_right)
    · exact measure_mono_ae (hAB.mono fun _ hz h => ⟨hz h.1,h.2⟩)
lemma DensityZero.union {A B : Set ℂ} {x : ℂ} (hA : DensityZero A x) (hB : DensityZero B x) :
    DensityZero (A∪B) x := by
  have hh := hA.add hB
  rw [add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => zero_le)
  intro r
  dsimp only
  rw [← ENNReal.add_div,union_inter_distrib_right]
  exact ENNReal.div_le_div_right (measure_union_le _ _) _
lemma densityZero_empty (x : ℂ) : DensityZero ∅ x := by
  simp only [DensityZero,empty_inter,measure_empty,ENNReal.zero_div]
  exact tendsto_const_nhds
lemma DensityZero.biUnion_finset {ι : Type*} (J : Finset ι) {A : ι → Set ℂ} {x : ℂ}
    (hA : ∀ i∈J,DensityZero (A i) x) : DensityZero (⋃ i∈J,A i) x := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa using densityZero_empty x
  | @insert i J hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (hA i (Finset.mem_insert_self _ _)).union
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))
lemma DensityZero.compl {A : Set ℂ} {x : ℂ} (hA : MeasurableSet A) (hz : DensityZero A x) :
    DensityOne Aᶜ x := by
  have ht := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1:ENNReal))) hz (Or.inl (by finiteness))
  rw [tsub_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hfin : volume (A∩Metric.closedBall x r)≠⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall x r).measure_ne_top (measure_mono inter_subset_right)
  have hp := (Metric.measure_closedBall_pos volume x hr).ne'
  have he : Aᶜ∩Metric.closedBall x r=Metric.closedBall x r\(A∩Metric.closedBall x r) := by
    ext z; simp; tauto
  rw [he,measure_sdiff inter_subset_right (hA.inter measurableSet_closedBall).nullMeasurableSet hfin,
    ENNReal.sub_div (fun _ _ => hp),ENNReal.div_self hp (isCompact_closedBall x r).measure_ne_top]
variable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
lemma state_densityZero (hw : WeakColoring k c) {x : ℂ} {A : Set ℝ} {J : Finset (Fin k)}
    (hA : RealState hc x A J) {t u : ℝ} (ht : LineDensityZero Aᶜ t)
    (hu : Real.sin (u-t)≠0) {i : Fin k} (hi : i∈J) :
    DensityZero {z | c z=i} (angularSum x 1 (angleChart (t,u))) := by
  apply palette_spatial_densityZero c hc hw _ hu
  apply ht.mono_ae
  filter_upwards [hA.2 i hi] with v hv
  exact mt hv
lemma angularSum_swap (x : ℂ) (t u : ℝ) :
    angularSum x 1 (angleChart (u,t))=angularSum x 1 (angleChart (t,u)) := by
  simp only [angularSum,angleChart,Complex.ofReal_one,one_mul]
  ring
lemma states_densityOne (hw : WeakColoring k c) {x : ℂ} {A B : Set ℝ} {J K : Finset (Fin k)}
    (hA : RealState hc x A J) (hB : RealState hc x B K) {t u : ℝ}
    (ht : LineDensityZero Aᶜ t) (hu : LineDensityZero Bᶜ u) (hne : Real.sin (u-t)≠0) :
    DensityOne {z | c z∉J∪K} (angularSum x 1 (angleChart (t,u))) := by
  have hz : DensityZero (⋃ i∈J∪K, {z | c z=i}) (angularSum x 1 (angleChart (t,u))) := by
    apply DensityZero.biUnion_finset
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact state_densityZero hc hw hA ht hne hi
    · rw [← angularSum_swap x t u]
      apply state_densityZero hc hw hB hu _ hi
      rwa [← neg_sub u t,Real.sin_neg,neg_ne_zero]
  have hm : MeasurableSet (⋃ i∈J∪K, {z | c z=i}) :=
    (J∪K).measurableSet_biUnion fun _ _ => measurableSet_eq_fun hc measurable_const
  convert hz.compl hm using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_compl_iff,mem_iUnion,mem_ofPred_eq]
  aesop
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma DensityOne.compl {A : Set ℂ} {x : ℂ} (hA : MeasurableSet A) (h : DensityOne A x) :
    DensityZero Aᶜ x := by
  have ht := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1:ENNReal))) h (Or.inl (by finiteness))
  rw [tsub_self] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hfin : volume (A∩Metric.closedBall x r)≠⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall x r).measure_ne_top (measure_mono inter_subset_right)
  have hp := (Metric.measure_closedBall_pos volume x hr).ne'
  have he : Aᶜ∩Metric.closedBall x r=Metric.closedBall x r\(A∩Metric.closedBall x r) := by
    ext z; simp; tauto
  rw [he,measure_sdiff inter_subset_right (hA.inter measurableSet_closedBall).nullMeasurableSet hfin,
    ENNReal.sub_div (fun _ _ => hp),ENNReal.div_self hp (isCompact_closedBall x r).measure_ne_top]
lemma DensityOne.inter {A B : Set ℂ} {x : ℂ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (ha : DensityOne A x) (hb : DensityOne B x) : DensityOne (A∩B) x := by
  have hh := ((ha.compl hA).union (hb.compl hB)).compl (hA.compl.union hB.compl)
  simpa using hh
lemma DensityOne.measure_ne_zero {A : Set ℂ} {x : ℂ} (h : DensityOne A x) : volume A≠0 := by
  intro hz
  have hzero : (fun r => volume (A∩Metric.closedBall x r)/volume (Metric.closedBall x r))=fun _ : ℝ => (0:ENNReal) := by
    funext r
    rw [measure_mono_null inter_subset_left hz,ENNReal.zero_div]
  change Tendsto _ _ _ at h
  rw [hzero] at h
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h)
lemma densityOne_univ (x : ℂ) : DensityOne univ x := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [univ_inter]
  exact (ENNReal.div_self (Metric.measure_closedBall_pos volume x hr).ne'
    (isCompact_closedBall x r).measure_ne_top).symm
lemma DensityOne.iInter {ι : Type*} [Finite ι] {A : ι → Set ℂ} {x : ℂ}
    (hm : ∀i,MeasurableSet (A i)) (h : ∀i,DensityOne (A i) x) : DensityOne (⋂i,A i) x := by
  classical
  let := Fintype.ofFinite ι
  have hh (J : Finset ι) : DensityOne (⋂i∈J,A i) x := by
    induction J using Finset.induction_on with
    | empty => simpa using densityOne_univ x
    | @insert i J hi ih =>
      simp only [Finset.set_biInter_insert]
      exact (h i).inter (hm i) (J.measurableSet_biInter fun j _ => hm j) ih
  simpa using hh Finset.univ
variable {k : ℕ} {c : ℂ → Fin k}
lemma finite_density_realization (hc : Measurable c) (hw : WeakColoring k c)
    {ι : Type*} [Finite ι] (z : ι → ℂ) (J : ι → Finset (Fin k))
    (hz : ∀v,DensityOne {q | c q∈J v} (z v)) :
    ∃q : ℂ, (∀v,c (q+z v)∈J v) ∧
      ∀v w, ‖z v-z w‖=1 → c (q+z v)≠c (q+z w) := by
  have hmem : DensityOne (⋂v,{q | c (q+z v)∈J v}) 0 := by
    apply DensityOne.iInter
    · intro v
      exact (J v).finite_toSet.measurableSet.preimage (hc.comp (measurable_id.add_const _))
    · intro v
      simpa only [zero_add,preimage_ofPred_eq] using (densityOne_translate (A := {q | c q∈J v}) (x := 0) (u := z v)).mpr (by simpa using hz v)
  have hproper : ∀ᵐ q : ℂ ∂volume, ∀v w, ‖z v-z w‖=1 → c (q+z v)≠c (q+z w) := by
    apply ae_all_iff.mpr
    intro v
    apply ae_all_iff.mpr
    intro w
    by_cases hh : ‖z v-z w‖=1
    · obtain ⟨t,ht⟩ := direction_exists (u := z w-z v) (by simpa only [norm_sub_rev] using hh)
      have hd := (measurePreserving_add_right volume (z v)).quasiMeasurePreserving.ae
        (weak_all_directions c hc hw t)
      filter_upwards [hd] with q hq _
      simpa only [ht,show q+z v+(z w-z v)=q+z w by ring] using hq
    · exact Eventually.of_forall fun _ => fun h => (hh h).elim
  obtain ⟨q,hq,hqp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmem.measure_ne_zero (ae_restrict_of_ae hproper)
  exact ⟨q,fun v => mem_iInter.mp hq v,hqp⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma complex_unit_orthogonal {e v : ℂ} (he : ‖e‖=1) (hv : ‖v‖=1) (h : ⟪e,v⟫=0) :
    e=Complex.I*v ∨ e= -Complex.I*v := by
  have hr : (e*star v).re=0 := by
    rw [real_inner_comm,Complex.inner] at h
    exact h
  have hn : ‖e*star v‖=1 := by rw [norm_mul,norm_star,he,hv,one_mul]
  have hs : (e*star v).im^2=1 := by
    have hh := Complex.normSq_eq_norm_sq (e*star v)
    rw [hn] at hh
    simp only [Complex.normSq_apply,hr,zero_mul,zero_add,one_pow] at hh
    nlinarith
  have him : (e*star v).im=1 ∨ (e*star v).im= -1 := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hs)
  have hmul : star v*v=1 := by
    change (starRingEnd ℂ) v*v=1
    rw [Complex.conj_mul']
    simp only [hv,one_pow,Complex.ofReal_one]
  rcases him with him|him
  · left
    have hz : e*star v=Complex.I := Complex.ext (by simpa using hr) (by simpa using him)
    calc e = (e*star v)*v := by rw [mul_assoc,hmul,mul_one]
         _ = Complex.I*v := congrArg (·*v) hz
  · right
    have hz : e*star v= -Complex.I := Complex.ext (by simpa using hr) (by simpa using him)
    calc e = (e*star v)*v := by rw [mul_assoc,hmul,mul_one]
         _ = -Complex.I*v := congrArg (·*v) hz
lemma ae_direction_nonorthogonal {v : ℂ} (hv : ‖v‖=1) :
    ∀ᵐt∂angularMeasure,⟪direction t,v⟫≠0 := by
  have hd : Function.Injective direction := fun _ _ h =>
    AddCircle.injective_toCircle (by positivity : (2*Real.pi:ℝ)≠0) (Subtype.ext h)
  have hf : {t | ⟪direction t,v⟫=0}.Finite := by
    apply ((Set.toFinite {Complex.I*v,-Complex.I*v}).preimage (f := direction) hd.injOn).subset
    intro t ht
    rcases complex_unit_orthogonal (direction_norm t) hv ht with ht|ht <;> simp [ht]
  exact measure_eq_zero_iff_ae_notMem.mp (hf.measure_zero angularMeasure)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BoundaryTrace
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma sample_region_ae (r : ℝ) {W : Set ℂ} {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J) :
    ∀ᵐy : ℂ∂volume,∀ᵐt∂angularMeasure,y+(r : ℂ)*direction t∈W →
      c (y+(r : ℂ)*direction t)∈J := by
  have hq : QuasiMeasurePreserving (fun p : ℂ × Angles => p.1+(r : ℂ)*direction p.2)
      ((volume : Measure ℂ).prod angularMeasure) volume :=
    QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (measurable_const.mul (direction_continuous.measurable.comp measurable_snd)))
      (Eventually.of_forall fun t => (measurePreserving_add_right (volume : Measure ℂ)
        ((r : ℂ)*direction t)).quasiMeasurePreserving)
  exact Measure.ae_ae_of_ae_prod (hq.ae hW)
include hc in
lemma sampling_near_region {x : ℂ} {r : ℝ} (hr : 0 < r) {K : Set Angles} (hK : IsCompact K)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J)
    (hmem : ∀t∈K,x+(r : ℂ)*direction t∈W) {δ : ℝ} (hδ : 0<δ) :
    ∃y : ℂ,dist y x<δ ∧ TypicalSampling c y r ∧
      ∀ᵐt∂angularMeasure,t∈K → c (y+(r : ℂ)*direction t)∈J := by
  let U : Set (ℂ × Angles) := {p | p.1+(r : ℂ)*direction p.2∈W}
  have hU : IsOpen U := ho.preimage (continuous_fst.add (continuous_const.mul (direction_continuous.comp continuous_snd)))
  obtain ⟨V,T,hV,_,hxV,hKT,hVT⟩ := generalized_tube_lemma (isCompact_singleton (x := x)) hK hU
    (by rintro ⟨y,t⟩ ⟨hy,ht⟩; change y=x at hy; subst y; exact hmem t ht)
  have hv : x∈V := hxV (mem_singleton x)
  have hpos : 0<volume (V∩Metric.ball x δ) := (hV.inter Metric.isOpen_ball).measure_pos volume
    ⟨x,hv,Metric.mem_ball_self hδ⟩
  obtain ⟨y,hy,hyp,hyW⟩ := ((frequently_ae_mem_iff.mpr hpos.ne').and_eventually
    ((ae_typicalSampling c hc hr).and (sample_region_ae c r hW))).exists
  refine ⟨y,hy.2,hyp,hyW.mono fun t ht htK => ht ?_⟩
  exact hVT (show (y,t)∈V×ˢT from ⟨hy.1,hKT htK⟩)
lemma weak_limit_zero_on {f : ℕ → RealL2 angularMeasure} {b : RealL2 angularMeasure}
    {K : Set Angles} (hK : MeasurableSet K)
    (ht : ∀v,Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hb : 0≤ᵐ[angularMeasure] b)
    (hf : ∀n,∀ᵐt∂angularMeasure,t∈K → f n t=0) :
    ∀ᵐt∂angularMeasure,t∈K → b t=0 := by
  have ht' := ht (indicatorConstLp 2 hK (measure_ne_top angularMeasure K) 1)
  have he (v : RealL2 angularMeasure) :
      ⟪v,indicatorConstLp 2 hK (measure_ne_top angularMeasure K) 1⟫=∫t in K,v t∂angularMeasure := by
    rw [real_inner_comm,L2.inner_indicatorConstLp_one]
  simp only [he] at ht'
  have hf0 (n) : ∫t in K,f n t∂angularMeasure=0 := by
    apply integral_eq_zero_of_ae
    exact (ae_restrict_iff' hK).mpr (hf n)
  simp only [hf0] at ht'
  have hzero : ∫t in K,b t∂angularMeasure=0 := (tendsto_nhds_unique tendsto_const_nhds ht').symm
  have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae hb)
    ((Lp.memLp b).integrable (by norm_num)).integrableOn).mp hzero
  exact (ae_restrict_iff' hK).mp hz
lemma trace_region_palette {x : ℂ} {K : Set Angles} (hK : IsCompact K)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J) {r : ℕ → ℝ}
    (hr : ∀n,0 < r n) (hrt : Tendsto r atTop (𝓝 1))
    (hmem : ∀n,∀t∈K,x+(r n : ℂ)*direction t∈W) :
    ∀ᵐt∂angularMeasure,t∈K → (palette c hc x t∩J).Nonempty := by
  have hex (n : ℕ) := sampling_near_region c hc (hr n) hK ho hW (hmem n)
    (δ := 1/((n:ℝ)+1)) (by positivity)
  choose y hy hyt hyJ using hex
  have hyl : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hy n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (TraceVector k))).isSeqCompact.subseq_of_frequently_in
    (Eventually.frequently (Eventually.of_forall fun n => Set.mem_univ (sampleCode c hc (y n) (r n))))
  have htrace := trace_of_realization c hc (fun n => hyt (φ n)) (hyl.comp hφ.tendsto_atTop)
    (hrt.comp hφ.tendsto_atTop) hb
  have hz (i : Fin k) (hi : i∉J) : ∀ᵐt∂angularMeasure,t∈K → traceValue b i t=0 := by
    apply weak_limit_zero_on hK.measurableSet
      (by simpa only [traceValue_sampleCode] using traceCode_tendsto_iff.mp hb i)
      ((trace_bounds c hc htrace).1 i)
    intro n
    filter_upwards [hyJ (φ n),sample_ae c hc (y (φ n)) (r (φ n)) i] with t ht he htK
    simp only [Function.comp_apply,traceValue_sampleCode]
    rw [he]
    unfold sampleFn
    split_ifs with htcol
    · exact (hi (htcol ▸ ht htK)).elim
    · rfl
  have hs : (fun t => ∑i,traceValue b i t)=ᵐ[angularMeasure](fun _ => (1:ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (traceValue b)
    rw [(trace_bounds c hc htrace).2.2] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  filter_upwards [hs,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hz i)),
    ae_all_iff.mpr (fun i => tracePositive_le_palette c hc x i ⟨b,htrace⟩)] with t hs hz hp htK
  by_contra! hn
  have hn' : ∀i,traceValue b i t≤0 := by
    intro i
    by_contra! hpos
    have hi : i∈palette c hc x t := (mem_palette c hc x t i).mpr (hp i hpos)
    by_cases hiJ : i∈J
    · have hh := Finset.mem_inter.mpr ⟨hi,hiJ⟩
      rw [hn] at hh
      exact Finset.notMem_empty i hh
    · linarith [hz i hiJ htK]
  have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hn' i)
  linarith
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma outer_strip_trace {x : ℂ} {t : Angles} {δ : ℝ} (hδ : 0<δ)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J)
    (hstrip : ∀u : Angles,dist (direction u) (direction t)<δ → ∀r : ℝ,
      1 < r → r<1+δ → x+(r : ℂ)*direction u∈W) :
    ∃U : Set Angles,IsOpen U ∧ t∈U ∧
      ∀ᵐu∂angularMeasure,u∈U → (palette c hc x u∩J).Nonempty := by
  let K : Set Angles := {u | dist (direction u) (direction t)≤δ/2}
  let U : Set Angles := {u | dist (direction u) (direction t)<δ/2}
  have hK : IsCompact K := (isClosed_le (direction_continuous.dist continuous_const) continuous_const).isCompact
  let r : ℕ → ℝ := fun n => 1+(δ/2)/(n+1)
  have hr (n) : 0 < r n := by dsimp [r]; positivity
  have hrt : Tendsto r atTop (𝓝 1) := by
    simpa only [r,div_eq_mul_inv,one_mul,mul_zero,add_zero] using (tendsto_const_nhds (x := (1:ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ/2))
  have hh := trace_region_palette c hc hK ho hW hr hrt (fun n u hu => by
    apply hstrip u (by dsimp [K] at hu; linarith)
    · dsimp [r]
      have : 0<(δ/2)/((n:ℝ)+1) := by positivity
      linarith
    · have hn : (1:ℝ)≤(n:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hb := div_le_self (by positivity : (0:ℝ)≤δ/2) hn
      dsimp [r]
      linarith)
  refine ⟨U,isOpen_lt (direction_continuous.dist continuous_const) continuous_const,?_,?_⟩
  · change dist (direction t) (direction t)<δ/2
    simp only [dist_self]; positivity
  · exact hh.mono fun u hu hU => hu (show u∈K from (show dist (direction u) (direction t)<δ/2 from hU).le)
lemma inner_strip_trace {x : ℂ} {t : Angles} {δ : ℝ} (hδ : 0<δ)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J)
    (hstrip : ∀u : Angles,dist (direction u) (direction t)<δ → ∀r : ℝ,
      0 < r → 1-δ < r → r<1 → x+(r : ℂ)*direction u∈W) :
    ∃U : Set Angles,IsOpen U ∧ t∈U ∧
      ∀ᵐu∂angularMeasure,u∈U → (palette c hc x u∩J).Nonempty := by
  let K : Set Angles := {u | dist (direction u) (direction t)≤δ/2}
  let U : Set Angles := {u | dist (direction u) (direction t)<δ/2}
  have hK : IsCompact K := (isClosed_le (direction_continuous.dist continuous_const) continuous_const).isCompact
  let ε := min δ (1/2)
  have he : 0<ε := lt_min hδ (by norm_num)
  have heδ : ε≤δ := min_le_left _ _
  have he1 : ε≤1/2 := min_le_right _ _
  let r : ℕ → ℝ := fun n => 1-(ε/2)/(n+1)
  have hb (n : ℕ) : (ε/2)/(n+1)≤ε/2 := div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr (n) : 0 < r n := by dsimp [r]; linarith [hb n]
  have hrt : Tendsto r atTop (𝓝 1) := by
    simpa only [r,div_eq_mul_inv,one_mul,mul_zero,sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ε/2))
  have hh := trace_region_palette c hc hK ho hW hr hrt (fun n u hu => by
    apply hstrip u (by dsimp [K] at hu; linarith) (r n) (hr n)
    · dsimp [r]; linarith [hb n]
    · dsimp [r]
      have : 0<(ε/2)/((n:ℝ)+1) := by positivity
      linarith)
  refine ⟨U,isOpen_lt (direction_continuous.dist continuous_const) continuous_const,?_,?_⟩
  · change dist (direction t) (direction t)<δ/2
    simp only [dist_self]; positivity
  · exact hh.mono fun u hu hU => hu (show u∈K from (show dist (direction u) (direction t)<δ/2 from hU).le)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_AngularBoundary
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma straddle_isOpen (K : Set ℂ) : IsOpen (Straddle K) := by
  have he : Straddle K=⋃p∈K,⋃q∈K,{z | dist z p<1 ∧ 1<dist z q} := by
    ext z
    simp only [Straddle,mem_iUnion,mem_ofPred_eq,exists_prop]
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
      (isOpen_lt continuous_const (continuous_id.dist continuous_const))
lemma approaching_direction_inside {r : ℕ → ℝ} {w : ℕ → ℂ} {v e : ℂ}
    (hr : ∀n,0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) (hw : ∀n,‖w n‖=1)
    (hwv : Tendsto w atTop (𝓝 v)) (he : ‖e‖=1) (hv : 0<⟪e,v⟫) :
    ∀ᶠn in atTop,‖e-(r n : ℂ)*w n‖<1 := by
  have ht : Tendsto (fun n => 2*⟪e,w n⟫-r n) atTop (𝓝 (2*⟪e,v⟫)) := by
    simpa only [sub_zero] using ((tendsto_const_nhds.inner hwv).const_mul 2).sub hr0
  filter_upwards [ht.eventually (lt_mem_nhds (by positivity : (0:ℝ)<2*⟪e,v⟫))] with n hn
  have heq : ‖e-(r n : ℂ)*w n‖^2=1-2*r n*⟪e,w n⟫+(r n)^2 := by
    change ‖e-r n • w n‖^2= _
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos (hr n),he,hw]
    ring
  have hpos := mul_pos (hr n) hn
  nlinarith [norm_nonneg (e-(r n : ℂ)*w n)]
lemma approaching_direction_outside {r : ℕ → ℝ} {w : ℕ → ℂ} {v e : ℂ}
    (hr : ∀n,0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) (hw : ∀n,‖w n‖=1)
    (hwv : Tendsto w atTop (𝓝 v)) (he : ‖e‖=1) (hv : ⟪e,v⟫<0) :
    ∀ᶠn in atTop,1<‖e-(r n : ℂ)*w n‖ := by
  have ht : Tendsto (fun n => 2*⟪e,w n⟫-r n) atTop (𝓝 (2*⟪e,v⟫)) := by
    simpa only [sub_zero] using ((tendsto_const_nhds.inner hwv).const_mul 2).sub hr0
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : 2*⟪e,v⟫<(0:ℝ)))] with n hn
  have heq : ‖e-(r n : ℂ)*w n‖^2=1-2*r n*⟪e,w n⟫+(r n)^2 := by
    change ‖e-r n • w n‖^2= _
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos (hr n),he,hw]
    ring
  have hneg := mul_neg_of_pos_of_neg (hr n) hn
  nlinarith [norm_nonneg (e-(r n : ℂ)*w n)]
lemma outer_straddle_strip {K : Set ℂ} {x e q : ℂ} (hx : x∈K) (hq : q∈K)
    (_he : ‖e‖=1) (hed : dist (x+e) q<1) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,1 < r → r<1+δ →
      x+(r : ℂ)*e'∈Straddle K := by
  have hn : ∀ᶠp : ℝ × ℂ in 𝓝 (1,e),dist (x+(p.1 : ℂ)*p.2) q<1 :=
    (show Continuous (fun p : ℝ × ℂ => dist (x+(p.1 : ℂ)*p.2) q) by fun_prop).continuousAt.eventually
      (gt_mem_nhds (by simpa only [Complex.ofReal_one,one_mul] using hed))
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,hδ,fun e' he' heδ r hr hrδ => ⟨q,hq,x,hx,?_,?_⟩⟩
  · apply hsub (a := (r,e'))
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by rw [Real.dist_eq,abs_of_pos (by linarith : 0 < r-1)]; linarith,heδ⟩
  · rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < r),he',mul_one]
    exact hr
lemma inner_straddle_strip {K : Set ℂ} {x e q : ℂ} (hx : x∈K) (hq : q∈K)
    (_he : ‖e‖=1) (hed : 1<dist (x+e) q) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,0 < r → 1-δ < r → r<1 →
      x+(r : ℂ)*e'∈Straddle K := by
  have hn : ∀ᶠp : ℝ × ℂ in 𝓝 (1,e),1<dist (x+(p.1 : ℂ)*p.2) q :=
    (show Continuous (fun p : ℝ × ℂ => dist (x+(p.1 : ℂ)*p.2) q) by fun_prop).continuousAt.eventually
      (lt_mem_nhds (by simpa only [Complex.ofReal_one,one_mul] using hed))
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,hδ,fun e' he' heδ r hr hrδ hr1 => ⟨x,hx,q,hq,?_,?_⟩⟩
  · rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,he',mul_one]
    exact hr1
  · apply hsub (a := (r,e'))
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by rw [Real.dist_eq,abs_of_neg (by linarith : r-1<0)]; linarith,heδ⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma finite_positive_lower_bound {ι : Type*} (E : Finset ι) (d : ι → ℝ)
    (hd : ∀i∈E,0<d i) : ∃δ>0,δ≤1 ∧ ∀i∈E,δ≤d i := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,le_rfl,by simp⟩
  | @insert a E ha ih =>
    obtain ⟨δ,hδ,hδ1,hδd⟩ := ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    refine ⟨min δ (d a),lt_min hδ (hd a (Finset.mem_insert_self _ _)),(min_le_left _ _).trans hδ1,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hδd i hi)
lemma ApproachingContinuum.outer_strip {x : ℂ} {K : Set ℂ} {v e : ℂ}
    (h : ApproachingContinuum x K v) (he : ‖e‖=1) (hv : 0<⟪e,v⟫) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,1 < r → r<1+δ →
      x+(r : ℂ)*e'∈Straddle K := by
  obtain ⟨n,hn⟩ := (approaching_direction_inside h.r_pos h.r_tendsto h.w_unit h.w_tendsto he hv).exists
  apply outer_straddle_strip h.center_mem (h.point_mem n) he
  simpa only [dist_eq_norm,add_sub_add_left_eq_sub] using hn
lemma ApproachingContinuum.inner_strip {x : ℂ} {K : Set ℂ} {v e : ℂ}
    (h : ApproachingContinuum x K v) (he : ‖e‖=1) (hv : ⟪e,v⟫<0) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,0 < r → 1-δ < r → r<1 →
      x+(r : ℂ)*e'∈Straddle K := by
  obtain ⟨n,hn⟩ := (approaching_direction_outside h.r_pos h.r_tendsto h.w_unit h.w_tendsto he hv).exists
  apply inner_straddle_strip h.center_mem (h.point_mem n) he
  simpa only [dist_eq_norm,add_sub_add_left_eq_sub] using hn
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma mem_spatialSupport_ae (hc : Measurable c) (i : Fin k) :
    ∀ᵐz : ℂ∂volume,c z=i → z∈spatialSupport c i :=
  (ae_restrict_iff' (measurableSet_eq_fun hc measurable_const)).mp
    (volume.restrict {z | c z=i}).support_mem_ae
lemma support_exclusion_ae (hc : Measurable c) {i : Fin k} {W : Set ℂ}
    (h : Disjoint (spatialSupport c i) W) : ∀ᵐz : ℂ∂volume,z∈W → c z≠i := by
  filter_upwards [mem_spatialSupport_ae c hc i] with z hz hzW hzcol
  exact Set.disjoint_left.mp h (hz hzcol) hzW
lemma finite_support_exclusion_ae (hc : Measurable c) {ι : Type*} [Fintype ι]
    (K : ι → Set ℂ) (F : ι → Finset (Fin k))
    (h : ∀i,∀j∈F i,Disjoint (spatialSupport c j) (Straddle (K i))) :
    ∀ᵐz : ℂ∂volume,∀i,z∈Straddle (K i) → c z∉F i := by
  have hh : ∀i,∀j,∀ᵐz : ℂ∂volume,j∈F i → z∈Straddle (K i) → c z≠j := by
    intro i j
    by_cases hj : j∈F i
    · exact (support_exclusion_ae c hc (h i j hj)).mono fun z hz _ => hz
    · exact Eventually.of_forall fun _ h => (hj h).elim
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hh i))] with z hz i hi hj
  exact hz i (c z) hj hi rfl
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma angleEssential_open (s : Angles → Bool) (b : Bool) : IsOpen (angleEssential s b) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro t ⟨U,hU,ht,ha⟩
  exact ⟨U,fun u hu => ⟨U,hU,hu,ha⟩,hU,ht⟩
lemma angleEssential_ae (s : Angles → Bool) (b : Bool) :
    ∀ᵐt∂angularMeasure,t∈angleEssential s b → s t=b := ae_of_locally_ae angularMeasure (fun _ h => h)
lemma angleEssential_disjoint (s : Angles → Bool) {a b : Bool} (hab : a≠b) :
    Disjoint (angleEssential s a) (angleEssential s b) := by
  apply disjoint_left.mpr
  rintro t ⟨U,hU,ht,ha⟩ ⟨V,hV,ht',hb⟩
  have hpos := (hU.inter hV).measure_pos angularMeasure ⟨t,ht,ht'⟩
  obtain ⟨u,hu,huab⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' (ae_restrict_of_ae (ha.and hb))
  exact hab ((huab.1 hu.1).symm.trans (huab.2 hu.2))
lemma angleEssential_shift {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) (t : Angles) (b : Bool) :
    t+(sixty : Angles)∈angleEssential s (!b) ↔ t∈angleEssential s b := by
  constructor
  · rintro ⟨U,hU,ht,ha⟩
    refine ⟨(fun q : Angles => q+(sixty : Angles)) ⁻¹' U,hU.preimage (continuous_id.add continuous_const),ht,?_⟩
    filter_upwards [(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae ha,hf] with q hq hqf hqU
    have hh := hq hqU
    rw [hqf] at hh
    exact Bool.not_injective hh
  · rintro ⟨U,hU,ht,ha⟩
    refine ⟨(fun q : Angles => q-(sixty : Angles)) ⁻¹' U,hU.preimage (continuous_id.sub continuous_const),by simpa,?_⟩
    have hh := (measurePreserving_add_right angularMeasure (-(sixty : Angles))).quasiMeasurePreserving.ae (ha.and hf)
    filter_upwards [hh] with q hq hqU
    have hcol := hq.1 hqU
    have hflip := hq.2
    change s (q-(sixty : Angles))=b at hcol
    simpa only [←sub_eq_add_neg,sub_add_cancel,hcol] using hflip
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Moser
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace EuclideanFiveColor
lemma square_coordinate_bounds {x c h : ℝ} (_hh : 0≤h) (hc : h≤|c|) (hx : |x-c|≤h) :
    (|c|-h)^2≤x^2 ∧ x^2≤(|c|+h)^2 := by
  have hu : |x|≤|c|+h := by
    calc |x|=|c+(x-c)| := by congr 1; ring
         _≤|c|+|x-c| := abs_add_le _ _
         _≤|c|+h := by linarith
  have hl : |c|-h≤|x| := by
    have ht : |c|≤|x|+|x-c| := by
      calc |c|=|x-(x-c)| := by congr 1; ring
           _≤|x|+|x-c| := abs_sub _ _
    linarith
  constructor
  · simpa only [sq_abs] using pow_le_pow_left₀ (sub_nonneg.mpr hc) hl 2
  · simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hu 2
lemma region_of_rational_bounds {x y a b Y H d : ℝ}
    (ha : 0<a) (hb : b<4) (hY : 0≤Y) (_hH : 0≤H) (hd : 0≤d)
    (hl : a≤x^2+y^2) (hu : x^2+y^2≤b)
    (hy : y^2≤Y) (habs : |3*x^2-y^2|≤H) (hg : d≤|x^2+y^2-1|)
    (hnum : Y*H^2<a^3*(1-b/4)*d^2) : ThreeLabelRegion x y := by
  refine ⟨lt_of_lt_of_le ha hl,lt_of_le_of_lt hu hb,?_⟩
  calc y^2*(3*x^2-y^2)^2 ≤ Y*H^2 := by
         have hpow : (3*x^2-y^2)^2≤H^2 := by
           simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
         exact mul_le_mul hy hpow (sq_nonneg _) hY
       _ < a^3*(1-b/4)*d^2 := hnum
       _ ≤ (x^2+y^2)^3*(1-(x^2+y^2)/4)*(x^2+y^2-1)^2 := by
         have hnonneg : 0≤1-b/4 := by linarith
         have hgap : d^2≤(x^2+y^2-1)^2 := by
           simpa only [sq_abs] using pow_le_pow_left₀ hd hg 2
         have hpos : 0≤(x^2+y^2)^3*(1-(x^2+y^2)/4) :=
           mul_nonneg (pow_nonneg (le_trans ha.le hl) _) (by linarith)
         gcongr
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
lemma sin_sub_add_product (a b : ℝ) :
    Real.sin (a-b)*Real.sin (a+b)=Real.sin a^2-Real.sin b^2 := by
  rw [Real.sin_sub,Real.sin_add]
  have ha : Real.cos a^2=1-Real.sin a^2 := by linarith [Real.sin_sq_add_cos_sq a]
  have hb : Real.cos b^2=1-Real.sin b^2 := by linarith [Real.sin_sq_add_cos_sq b]
  calc _ = Real.sin a^2*Real.cos b^2-Real.cos a^2*Real.sin b^2 := by ring
       _ = _ := by rw [ha,hb]; ring
lemma sin_three_using_cos (a : ℝ) :
    Real.sin (3*a)=Real.sin a*(4*Real.cos a^2-1) := by
  rw [Real.sin_three_mul]
  nlinarith [congrArg (fun x : ℝ => Real.sin a*x) (Real.sin_sq_add_cos_sq a)]
/-- Exact strict angular form of the manuscript's polynomial region. -/
lemma polynomial_region_angles {z : ℂ} (hz : ThreeLabelRegion z.re z.im) :
    ∃ t u : ℝ, (Circle.exp t : ℂ)+(Circle.exp u : ℂ)=z ∧
      Real.sin (u-t)≠0 ∧ Real.sin (3*t)*Real.sin (3*u)<0 := by
  let r : ℝ := ‖z‖
  let p : ℝ := z.arg
  let d : ℝ := Real.arccos (r/2)
  have hr2 : r^2=z.re^2+z.im^2 := by
    change ‖z‖^2=_
    rw [Complex.sq_norm,Complex.normSq_apply]
    ring
  have hr0 : 0 < r := by
    have hn : 0 ≤ r := norm_nonneg z
    nlinarith [hz.1]
  have hrlt : r<2 := by nlinarith [hz.2.1]
  have hdcos : Real.cos d=r/2 := Real.cos_arccos (by linarith) (by linarith)
  have hd0 : 0<d := Real.arccos_pos.mpr (by linarith)
  have hdlt : d<Real.pi/2 := Real.arccos_lt_pi_div_two.mpr (by positivity)
  have hdsin : 0<Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd0 (by linarith [Real.pi_pos])
  have hdsq : Real.sin d^2=1-r^2/4 := by
    have hh := Real.sin_sq_add_cos_sq d
    rw [hdcos] at hh
    nlinarith
  have hdp : Real.sin (3*d)=Real.sin d*(r^2-1) := by
    rw [sin_three_using_cos,hdcos]; ring
  have hpysin : r*Real.sin p=z.im := Complex.norm_mul_sin_arg z
  have hpxcos : r*Real.cos p=z.re := Complex.norm_mul_cos_arg z
  have hpy : r^3*Real.sin (3*p)=z.im*(3*z.re^2-z.im^2) := by
    rw [Real.sin_three_mul]
    calc _ = 3*r^2*(r*Real.sin p)-4*(r*Real.sin p)^3 := by ring
         _ = _ := by rw [hr2,hpysin]; ring
  have hP : z.im^2*(3*z.re^2-z.im^2)^2=r^6*Real.sin (3*p)^2 := by
    calc _ = (z.im*(3*z.re^2-z.im^2))^2 := by ring
         _ = (r^3*Real.sin (3*p))^2 := by rw [hpy]
         _ = _ := by ring
  have hP' : (z.re^2+z.im^2)^3*(1-(z.re^2+z.im^2)/4)*(z.re^2+z.im^2-1)^2=
      r^6*Real.sin (3*d)^2 := by
    rw [←hr2,hdp]
    rw [show 1-r^2/4=Real.sin d^2 from hdsq.symm]
    ring
  have hlt : Real.sin (3*p)^2<Real.sin (3*d)^2 := by
    have hh := hz.2.2
    rw [hP,hP'] at hh
    exact (mul_lt_mul_iff_right₀ (pow_pos hr0 6)).mp hh
  refine ⟨p-d,p+d,?_,?_,?_⟩
  · apply Complex.ext
    · simp only [Complex.add_re,Circle.coe_exp,Complex.exp_mul_I,
        ←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.add_re,Complex.mul_re,
        Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,mul_zero,
        sub_zero,zero_mul,add_zero]
      rw [Real.cos_sub,Real.cos_add,hdcos]
      nlinarith
    · simp only [Complex.add_im,Circle.coe_exp,Complex.exp_mul_I,
        ←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.add_im,Complex.mul_im,
        Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,Complex.I_im,mul_zero,
        mul_one,add_zero,zero_add]
      rw [Real.sin_sub,Real.sin_add,hdcos]
      nlinarith
  · rw [show p+d-(p-d)=2*d by ring,Real.sin_two_mul,hdcos]
    exact ne_of_gt (by positivity)
  · rw [mul_sub,mul_add,sin_sub_add_product]
    linarith
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
lemma complex_norm_one_of_sq {z : ℂ} (h : z.re^2+z.im^2=1) : ‖z‖=1 := by
  have he : ‖z‖^2=1 := by rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]; nlinarith
  nlinarith [norm_nonneg z]
lemma moser_edge_unit {i j : Fin 7} (h : (i,j)∈moserEdges) : ‖moserPoint i-moserPoint j‖=1 := by
  have h3 := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have h11 := Real.sq_sqrt (show (0:ℝ)≤11 by norm_num)
  simp only [moserEdges,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl⟩
  all_goals
    apply complex_norm_one_of_sq
    norm_num [moserA,moserB,moserT,moserU,Complex.mul_re,Complex.mul_im,
      Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.sub_re,Complex.sub_im,
      Complex.add_re,Complex.add_im] <;>
      (ring_nf; norm_num [h3,h11])
lemma three_color_diamond {a b p q : Fin 3} (hab : a≠b)
    (hpa : p≠a) (hpb : p≠b) (hqa : q≠a) (hqb : q≠b) : p=q := by
  fin_cases a <;> fin_cases b <;> fin_cases p <;> fin_cases q <;> simp_all
lemma moser_not_three_colorable (f : Fin 7 → Fin 3)
    (hf : ∀i j,(i,j)∈moserEdges → f i≠f j) : False := by
  have h03 : f 0=f 3 := three_color_diamond
    (hf 1 2 (by decide)) (hf 0 1 (by decide)) (hf 0 2 (by decide))
    (hf 3 1 (by decide)) (hf 3 2 (by decide))
  have h06 : f 0=f 6 := three_color_diamond
    (hf 4 5 (by decide)) (hf 0 4 (by decide)) (hf 0 5 (by decide))
    (hf 6 4 (by decide)) (hf 6 5 (by decide))
  exact hf 3 6 (by decide) (h03.symm.trans h06)
lemma moserRotation_unit : ‖moserRotation‖=1 := by
  apply complex_norm_one_of_sq
  norm_num [moserRotation,Complex.div_ofReal_re,Complex.div_ofReal_im]
lemma placedMoser_edge_unit {i j : Fin 7} (h : (i,j)∈moserEdges) : ‖placedMoser i-placedMoser j‖=1 := by
  have he : placedMoser i-placedMoser j=moserRotation*(moserPoint i-moserPoint j) := by
    unfold placedMoser; ring
  rw [he,norm_mul,moserRotation_unit,moser_edge_unit h,one_mul]
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
lemma radical_bounds : 1.73205<Real.sqrt 3 ∧ Real.sqrt 3<1.73206 ∧
    3.31662<Real.sqrt 11 ∧ Real.sqrt 11<3.31663 := by
  have h3 := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have h11 := Real.sq_sqrt (show (0:ℝ)≤11 by norm_num)
  have hn3 := Real.sqrt_nonneg (3:ℝ)
  have hn11 := Real.sqrt_nonneg (11:ℝ)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith
lemma radical_product_bounds : (1.73205*3.31662 : ℝ)≤Real.sqrt 3*Real.sqrt 11 ∧
    Real.sqrt 3*Real.sqrt 11≤1.73206*3.31663 := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  constructor <;> gcongr
lemma seven_point_box_0 :
    |(placedMoser 0).re-certificateX 0|≤(0.00011 : ℝ) ∧
    |(placedMoser 0).im-certificateY 0|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 0).re-(-1.2906)|≤0.00011 ∧ |(placedMoser 0).im-(0.1876)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
lemma seven_point_box_1 :
    |(placedMoser 1).re-certificateX 1|≤(0.00011 : ℝ) ∧
    |(placedMoser 1).im-certificateY 1|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 1).re-(-0.6335)|≤0.00011 ∧ |(placedMoser 1).im-(0.9414)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_box_2 :
    |(placedMoser 2).re-certificateX 2|≤(0.00011 : ℝ) ∧
    |(placedMoser 2).im-certificateY 2|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 2).re-(-0.3092)|≤0.00011 ∧ |(placedMoser 2).im-(-0.0045)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_box_3 :
    |(placedMoser 3).re-certificateX 3|≤(0.00011 : ℝ) ∧
    |(placedMoser 3).im-certificateY 3|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 3).re-(0.3478)|≤0.00011 ∧ |(placedMoser 3).im-(0.7493)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_box_4 :
    |(placedMoser 4).re-certificateX 4|≤(0.00011 : ℝ) ∧
    |(placedMoser 4).im-certificateY 4|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 4).re-(-1.1598)|≤0.00011 ∧ |(placedMoser 4).im-(1.1790)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_box_5 :
    |(placedMoser 5).re-certificateX 5|≤(0.00011 : ℝ) ∧
    |(placedMoser 5).im-certificateY 5|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 5).re-(-0.3666)|≤0.00011 ∧ |(placedMoser 5).im-(0.5700)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_box_6 :
    |(placedMoser 6).re-certificateX 6|≤(0.00011 : ℝ) ∧
    |(placedMoser 6).im-certificateY 6|≤(0.00011 : ℝ) := by
  obtain ⟨ha,hb,hc,hd⟩ := radical_bounds
  obtain ⟨hp,hq⟩ := radical_product_bounds
  change |(placedMoser 6).re-(-0.2358)|≤0.00011 ∧ |(placedMoser 6).im-(1.5614)|≤0.00011
  norm_num [placedMoser,moserRotation,moserA,moserB,moserT,moserU,
    Complex.mul_re,Complex.mul_im,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith
lemma seven_point_boxes (i : Fin 7) :
    |(placedMoser i).re-certificateX i|≤(0.00011 : ℝ) ∧
    |(placedMoser i).im-certificateY i|≤(0.00011 : ℝ) := by
  fin_cases i
  · exact seven_point_box_0
  · exact seven_point_box_1
  · exact seven_point_box_2
  · exact seven_point_box_3
  · exact seven_point_box_4
  · exact seven_point_box_5
  · exact seven_point_box_6
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor
/-- Exact rational interval certificate for the manuscript's seven placed vertices. -/
lemma seven_point_certificate (i : Fin 7) :
    ThreeLabelRegion (placedMoser i).re (placedMoser i).im := by
  obtain ⟨hx,hy⟩ := seven_point_boxes i
  fin_cases i
  · change ThreeLabelRegion (placedMoser 0).re (placedMoser 0).im
    change |(placedMoser 0).re-(-1.2906)|≤0.00011 at hx
    change |(placedMoser 0).im-(0.1876)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-1.2906:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(0.1876:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 1.70) (b := 1.71) (Y := 0.0353) (H := 4.963) (d := 0.70)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := le_abs_self ((placedMoser 0).re^2+(placedMoser 0).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 1).re (placedMoser 1).im
    change |(placedMoser 1).re-(-0.6335)|≤0.00011 at hx
    change |(placedMoser 1).im-(0.9414)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-0.6335:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(0.9414:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 1.28) (b := 1.29) (Y := 0.887) (H := 0.319) (d := 0.28)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := le_abs_self ((placedMoser 1).re^2+(placedMoser 1).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 2).re (placedMoser 2).im
    change |(placedMoser 2).re-(-0.3092)|≤0.00011 at hx
    change |(placedMoser 2).im-(-0.0045)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-0.3092:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-0.0045:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 0.095) (b := 0.096) (Y := 0.000022) (H := 0.287) (d := 0.904)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := neg_le_abs ((placedMoser 2).re^2+(placedMoser 2).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 3).re (placedMoser 3).im
    change |(placedMoser 3).re-(0.3478)|≤0.00011 at hx
    change |(placedMoser 3).im-(0.7493)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(0.3478:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(0.7493:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 0.682) (b := 0.683) (Y := 0.562) (H := 0.199) (d := 0.317)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := neg_le_abs ((placedMoser 3).re^2+(placedMoser 3).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 4).re (placedMoser 4).im
    change |(placedMoser 4).re-(-1.1598)|≤0.00011 at hx
    change |(placedMoser 4).im-(1.1790)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-1.1598:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(1.1790:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 2.73) (b := 2.74) (Y := 1.391) (H := 2.647) (d := 1.73)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := le_abs_self ((placedMoser 4).re^2+(placedMoser 4).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 5).re (placedMoser 5).im
    change |(placedMoser 5).re-(-0.3666)|≤0.00011 at hx
    change |(placedMoser 5).im-(0.5700)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-0.3666:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(0.5700:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 0.459) (b := 0.46) (Y := 0.326) (H := 0.079) (d := 0.54)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := neg_le_abs ((placedMoser 5).re^2+(placedMoser 5).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
  · change ThreeLabelRegion (placedMoser 6).re (placedMoser 6).im
    change |(placedMoser 6).re-(-0.2358)|≤0.00011 at hx
    change |(placedMoser 6).im-(1.5614)|≤0.00011 at hy
    have hxx := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(-0.2358:ℝ)|) hx
    have hyy := square_coordinate_bounds (by norm_num : (0:ℝ)≤0.00011)
      (by norm_num : (0.00011:ℝ)≤|(1.5614:ℝ)|) hy
    norm_num at hxx hyy
    apply region_of_rational_bounds (a := 2.493) (b := 2.495) (Y := 2.44) (H := 2.273) (d := 1.493)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · nlinarith [hxx.1,hyy.1]
    · nlinarith [hxx.2,hyy.2]
    · nlinarith [hyy.2]
    · rw [abs_le]; constructor <;> nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · have hh := le_abs_self ((placedMoser 6).re^2+(placedMoser 6).im^2-1)
      nlinarith [hxx.1,hxx.2,hyy.1,hyy.2]
    · norm_num
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Sectors
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma triangle_majority_cover : ∀s : Fin 3 → Bool,∃b : Bool,
    ∀j∈({0,1,2} : Finset (Fin 5)),∃i : Fin 3,s i=b ∧ j∈triangleEdge i := by decide
lemma triangle_outsider : ∀s : Fin 3 → Bool,∀b : Bool,
    (∀j∈({0,1,2} : Finset (Fin 5)),∃i : Fin 3,s i=b ∧ j∈triangleEdge i) →
    ∀j : Fin 5,(∀i : Fin 3,s i=b → j∉triangleEdge i) → j=3 ∨ j=4 := by decide
lemma ApproachingContinuum.side_strip {x : ℂ} {K : Set ℂ} {v e : ℂ}
    (h : ApproachingContinuum x K v) (he : ‖e‖=1) (hn : ⟪e,v⟫≠0) (b : Bool)
    (hs : decide (0<⟪e,v⟫)=b) : ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,
      0 < r → |r-1|<δ → (if b then 1 < r else r<1) → x+(r:ℂ)*e'∈Straddle K := by
  cases b
  · have hneg : ⟪e,v⟫<0 := lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false hs)) hn
    obtain ⟨δ,hδ,hh⟩ := h.inner_strip he hneg
    refine ⟨δ,hδ,fun e' he' hd r hr hab hr1 => hh e' he' hd r hr ?_ hr1⟩
    have := (abs_lt.mp hab).1
    linarith
  · obtain ⟨δ,hδ,hh⟩ := h.outer_strip he (of_decide_eq_true hs)
    refine ⟨δ,hδ,fun e' he' hd r _ hab hr1 => hh e' he' hd r hr1 ?_⟩
    have := (abs_lt.mp hab).2
    linarith
/-- Three interface edges supply an actual outsider-only open strip in every
nonexceptional direction, with the radial side chosen by the majority sign. -/
lemma triangle_outsider_strip {c : ℂ → Fin 5} (hc : Measurable c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ}
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i)))
    {e : ℂ} (he : ‖e‖=1) (hn : ∀i,⟪e,v i⟫≠0) :
    ∃b : Bool,∃δ>0,∃W : Set ℂ,IsOpen W ∧
      (∀ᵐz : ℂ∂volume,z∈W → c z=3 ∨ c z=4) ∧
      ∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,
        0 < r → |r-1|<δ → (if b then 1 < r else r<1) → x+(r:ℂ)*e'∈W := by
  classical
  let s : Fin 3 → Bool := fun i => decide (0<⟪e,v i⟫)
  obtain ⟨b,hb⟩ := triangle_majority_cover s
  let E : Finset (Fin 3) := Finset.univ.filter fun i => s i=b
  have hex (i : E) := (hK i).side_strip he (hn i) b ((Finset.mem_filter.mp i.2).2)
  choose d hd hs using hex
  obtain ⟨δ,hδ,_,hδd⟩ := finite_positive_lower_bound Finset.univ d (fun i _ => hd i)
  let W : Set ℂ := ⋂i : E,Straddle (K i)
  refine ⟨b,δ,hδ,W,isOpen_iInter_of_finite (fun i => straddle_isOpen (K i)),?_,?_⟩
  · filter_upwards [finite_support_exclusion_ae c hc K triangleEdge hH] with z hz hzW
    apply triangle_outsider s b hb (c z)
    intro i hi
    exact hz i (mem_iInter.mp hzW ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩)
  · intro e' he' heδ r hr hrδ hside
    apply mem_iInter.mpr
    intro i
    exact hs i e' he' (heδ.trans_le (hδd i (Finset.mem_univ _))) r hr
      (hrδ.trans_le (hδd i (Finset.mem_univ _))) hside
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma triangle_binary_from_continua {c : ℂ → Fin 5} (hc : Measurable c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i))) :
    BinaryCenter c hc x 3 4 := by
  have hh : ∀ᵐt∂angularMeasure,(∀i,⟪direction t,v i⟫≠0) →
      t∈paletteSet c hc x 3 ∨ t∈paletteSet c hc x 4 := by
    apply ae_of_locally_ae angularMeasure
    intro t ht
    obtain ⟨b,δ,hδ,W,hW,hWc,hs⟩ := triangle_outsider_strip hc hK hH (direction_norm t) ht
    have hcols : ∀ᵐz : ℂ∂volume,z∈W → c z∈({3,4} : Finset (Fin 5)) :=
      hWc.mono fun z hz hzw => by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz hzw
    have hex : ∃A : Set Angles,IsOpen A ∧ t∈A ∧
        ∀ᵐu∂angularMeasure,u∈A → (palette c hc x u∩{3,4}).Nonempty := by
      cases b
      · apply inner_strip_trace c hc hδ hW hcols
        intro u hu r hr hrδ hr1
        apply hs (direction u) (direction_norm u) hu r hr _ hr1
        rw [abs_lt]; constructor <;> linarith
      · apply outer_strip_trace c hc hδ hW hcols
        intro u hu r hr1 hrδ
        apply hs (direction u) (direction_norm u) hu r (by linarith) _ hr1
        rw [abs_lt]; constructor <;> linarith
    obtain ⟨A,hA,htA,hae⟩ := hex
    refine ⟨A,hA,htA,hae.mono fun u hu hAu => ?_⟩
    obtain ⟨i,hi⟩ := hu hAu
    rcases Finset.mem_inter.mp hi with ⟨hip,hi⟩
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact Or.inl ((mem_palette c hc x u 3).mp hip)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Or.inr ((mem_palette c hc x u 4).mp hip)
  filter_upwards [hh,ae_all_iff.mpr (fun i => ae_direction_nonorthogonal (hv i))] with t ht hn
  exact ht hn
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma angleEssential_connected {s : Angles → Bool} {U : Set Angles}
    (hU : IsPreconnected U) (hne : U.Nonempty) (hbound : Disjoint U (angleBoundary s)) :
    ∃b,U⊆angleEssential s b := by
  have hcov : U⊆angleEssential s false∪angleEssential s true := by
    intro t ht
    have hn := disjoint_left.mp hbound ht
    simp only [angleBoundary,mem_compl_iff,not_not,mem_iUnion] at hn
    obtain ⟨b,hb⟩ := hn
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  obtain ⟨t,ht⟩ := hne
  rcases hcov ht with hb|hb
  · exact ⟨false,hU.subset_left_of_subset_union (angleEssential_open s false) (angleEssential_open s true)
      (angleEssential_disjoint s (by decide)) hcov ⟨t,ht,hb⟩⟩
  · exact ⟨true,hU.subset_left_of_subset_union (angleEssential_open s true) (angleEssential_open s false)
      (angleEssential_disjoint s (by decide)) (by simpa only [union_comm] using hcov) ⟨t,ht,hb⟩⟩
lemma one_orbit_first_arc {s : Angles → Bool} {φ : ℝ}
    (hboundary : angleBoundary s={u | ∃j : Fin 6,u=(φ : Angles)+sixAngle j}) :
    ∃b,∀t∈Ioo φ (φ+Real.pi/3),(t : Angles)∈angleEssential s b := by
  let U : Set Angles := ((↑) : ℝ → Angles) '' Ioo φ (φ+Real.pi/3)
  have hU : IsPreconnected U := isPreconnected_Ioo.image _ continuous_quotient_mk'.continuousOn
  have hne : U.Nonempty := (nonempty_Ioo.mpr (by linarith [Real.pi_pos] : φ<φ+Real.pi/3)).image _
  have hd : Disjoint U (angleBoundary s) := by
    apply disjoint_left.mpr
    rintro q ⟨t,ht,rfl⟩ hq
    rw [hboundary] at hq
    obtain ⟨j,hj⟩ := hq
    have he : (t : Angles)=((φ+(j.val:ℝ)*(Real.pi/3) : ℝ) : Angles) := by
      have hx : sixAngle j=((j.val:ℝ)*(Real.pi/3) : ℝ) := by
        rw [sixAngle,←AddCircle.coe_nsmul]
        simp only [nsmul_eq_mul,sixty]
      simpa only [hx,AddCircle.coe_add] using hj
    have htI : t∈Ico φ (φ+2*Real.pi) := ⟨ht.1.le,by linarith [Real.pi_pos,ht.2]⟩
    have hjI : φ+(j.val:ℝ)*(Real.pi/3)∈Ico φ (φ+2*Real.pi) := by
      have hj0 : 0≤(j.val:ℝ) := Nat.cast_nonneg _
      have hj6 : (j.val:ℝ)<6 := by exact_mod_cast j.isLt
      constructor
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    have hv := (AddCircle.coe_eq_coe_iff_of_mem_Ico htI hjI).mp he
    by_cases hz : j.val=0
    · simp only [hz,Nat.cast_zero,zero_mul,add_zero] at hv
      linarith [ht.1]
    · have hj1 : (1:ℝ)≤j.val := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      nlinarith [ht.2,Real.pi_pos]
  obtain ⟨b,hb⟩ := angleEssential_connected hU hne hd
  exact ⟨b,fun t ht => hb ⟨t,ht,rfl⟩⟩
lemma angleEssential_real_periodic {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) (b : Bool) :
    Function.Periodic (fun t : ℝ => (t : Angles)∈angleEssential s b) (2*(Real.pi/3)) := by
  intro t
  apply propext
  have hh := angleEssential_shift hf ((t : Angles)+(sixty : Angles)) (!b)
  rw [Bool.not_not] at hh
  have hh' := angleEssential_shift hf (t : Angles) b
  have he : ((t+2*(Real.pi/3) : ℝ) : Angles) = (t : Angles)+(sixty : Angles)+(sixty : Angles) := by
    calc ((t+2*(Real.pi/3) : ℝ) : Angles) = ((t+sixty+sixty : ℝ) : Angles) := by
           congr 1
           dsimp [sixty]
           ring
         _ = _ := by rw [AddCircle.coe_add,AddCircle.coe_add]
  dsimp only
  rw [he]
  exact hh.trans hh'
lemma one_orbit_sectors {s : Angles → Bool} {φ : ℝ}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t))
    (hboundary : angleBoundary s={u | ∃j : Fin 6,u=(φ : Angles)+sixAngle j}) :
    ∃b,(∀t,0<Real.sin (3*(t-φ)) → (t : Angles)∈angleEssential s b) ∧
      (∀t,Real.sin (3*(t-φ))<0 → (t : Angles)∈angleEssential s (!b)) := by
  obtain ⟨b,hb⟩ := one_orbit_first_arc hboundary
  have hb' (t : ℝ) (ht : t∈Ioo (φ+Real.pi/3) (φ+2*(Real.pi/3))) :
      (t : Angles)∈angleEssential s (!b) := by
    have hh := (angleEssential_shift hf ((t-Real.pi/3 : ℝ) : Angles) b).mpr
      (hb (t-Real.pi/3) ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    simpa only [sixty,←AddCircle.coe_add,sub_add_cancel] using hh
  have hreduce (t : ℝ) : ∃r : ℝ,∃n : ℤ,0 ≤ r ∧ r<2*(Real.pi/3) ∧
      t=φ+r+n*(2*(Real.pi/3)) ∧ Real.sin (3*(t-φ))=Real.sin (3*r) := by
    let n : ℤ := ⌊(t-φ)/(2*(Real.pi/3))⌋
    let r : ℝ := (t-φ)-n*(2*(Real.pi/3))
    have he : t=φ+r+n*(2*(Real.pi/3)) := by dsimp [r]; ring
    refine ⟨r,n,Int.sub_floor_div_mul_nonneg _ (by positivity),Int.sub_floor_div_mul_lt _ (by positivity),he,?_⟩
    have he' : 3*(t-φ)=3*r+(n:ℝ)*(2*Real.pi) := by rw [he]; ring
    rw [he',Real.sin_add_int_mul_two_pi]
  refine ⟨b,?_,?_⟩
  · intro t ht
    obtain ⟨r,n,hr0,hrP,he,hsin⟩ := hreduce t
    rw [hsin] at ht
    have hrpos : 0 < r := by
      by_contra hn
      have hr : r=0 := le_antisymm (le_of_not_gt hn) hr0
      simp only [hr,mul_zero,Real.sin_zero,lt_self_iff_false] at ht
    have hra : r<Real.pi/3 := by
      by_contra hn
      have hh := Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by linarith : 3*r-2*Real.pi≤0) (by linarith : -Real.pi≤3*r-2*Real.pi)
      rw [Real.sin_sub_two_pi] at hh
      exact (not_lt_of_ge hh) ht
    have hy := hb (φ+r) ⟨by linarith,by linarith⟩
    rw [he]
    exact (angleEssential_real_periodic hf b).int_mul n (φ+r) ▸ hy
  · intro t ht
    obtain ⟨r,n,hr0,hrP,he,hsin⟩ := hreduce t
    rw [hsin] at ht
    have hra : Real.pi/3 < r := by
      by_contra hn
      have hh := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0≤3*r) (by linarith : 3*r≤Real.pi)
      exact (not_lt_of_ge hh) ht
    have hy := hb' (φ+r) ⟨by linarith,by linarith⟩
    rw [he]
    exact (angleEssential_real_periodic hf (!b)).int_mul n (φ+r) ▸ hy
end EuclideanFiveColor
end

noncomputable section
open Set MeasureTheory
namespace EuclideanFiveColor
lemma moser_density_impossible {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c) (x v : ℂ) (hv : ‖v‖=1)
    (J : Finset (Fin k)) (hJ : J.card≤3) :
    ¬(∀ i, DensityOne {q | c q∈J} (x+v*placedMoser i)) := by
  intro hD
  obtain ⟨q,hq,hp⟩ := finite_density_realization hc hw (fun i => x+v*placedMoser i)
    (fun _ => J) hD
  have hh : Fintype.card J≤Fintype.card (Fin 3) := by simpa using hJ
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hh
  apply moser_not_three_colorable (fun i => f ⟨c (q+(x+v*placedMoser i)),hq i⟩)
  intro i j hij he
  have hd : ‖(x+v*placedMoser i)-(x+v*placedMoser j)‖=1 := by
    rw [show (x+v*placedMoser i)-(x+v*placedMoser j)=v*(placedMoser i-placedMoser j) by ring,
      norm_mul,hv,placedMoser_edge_unit hij,one_mul]
  exact hp i j hd (congrArg Subtype.val (f.injective he))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma lineDensityZero_compl_of_mem_nhds {A : Set ℝ} {t : ℝ} (hA : A∈𝓝 t) :
    LineDensityZero Aᶜ t := by
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hA
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with r hr
  have hempty : Aᶜ∩Metric.closedBall t r=∅ := by
    ext q
    simp only [mem_empty_iff_false,iff_false]
    rintro ⟨hq,hqr⟩
    exact hq (hsub (lt_of_le_of_lt hqr hr))
  simp [hempty]
lemma positiveSector_open (φ : ℝ) : IsOpen (positiveSector φ) := by
  apply isOpen_lt <;> fun_prop
lemma negativeSector_open (φ : ℝ) : IsOpen (negativeSector φ) := by
  apply isOpen_lt <;> fun_prop
variable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
lemma polynomial_region_density (hw : WeakColoring k c) {x : ℂ} {a b : Fin k} {φ : ℝ}
    (hpos : RealState hc x (positiveSector φ) {a})
    (hneg : RealState hc x (negativeSector φ) {b})
    {z : ℂ} (hz : ThreeLabelRegion z.re z.im) :
    DensityOne {q | c q∉({a,b} : Finset (Fin k))} (x+(Circle.exp φ:ℂ)*z) := by
  obtain ⟨t,u,hs,hn,ht⟩ := polynomial_region_angles hz
  have hpoint : angularSum x 1 (angleChart (φ+t,φ+u))=x+(Circle.exp φ:ℂ)*z := by
    simp only [angularSum,angleChart,Complex.ofReal_one,one_mul,direction_real,Circle.exp_add,Circle.coe_mul]
    rw [add_assoc,←mul_add,hs]
  have hnon : Real.sin ((φ+u)-(φ+t))≠0 := by
    simpa only [show φ+u-(φ+t)=u-t by ring] using hn
  rcases mul_neg_iff.mp ht with ⟨ht,hu⟩|⟨ht,hu⟩
  · have htm : φ+t∈positiveSector φ := by simpa [positiveSector] using ht
    have hum : φ+u∈negativeSector φ := by simpa [negativeSector] using hu
    have hd := states_densityOne hc hw hpos hneg
      (lineDensityZero_compl_of_mem_nhds ((positiveSector_open φ).mem_nhds htm))
      (lineDensityZero_compl_of_mem_nhds ((negativeSector_open φ).mem_nhds hum)) hnon
    rw [hpoint] at hd
    simpa only [Finset.singleton_union] using hd
  · have htm : φ+t∈negativeSector φ := by simpa [negativeSector] using ht
    have hum : φ+u∈positiveSector φ := by simpa [positiveSector] using hu
    have hd := states_densityOne hc hw hneg hpos
      (lineDensityZero_compl_of_mem_nhds ((negativeSector_open φ).mem_nhds htm))
      (lineDensityZero_compl_of_mem_nhds ((positiveSector_open φ).mem_nhds hum)) hnon
    rw [hpoint] at hd
    simpa only [Finset.singleton_union,Finset.pair_comm b a] using hd
/-- The exact six-sector outcome of triangle rigidity is impossible, for every center and phase. -/
lemma no_alternating_sectors {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} {a b : Fin 5} (hab : a≠b) (φ : ℝ)
    (hpos : RealState hc x (positiveSector φ) {a})
    (hneg : RealState hc x (negativeSector φ) {b}) : False := by
  let J : Finset (Fin 5) := {a,b}ᶜ
  have hJ : J.card≤3 := by
    change ({a,b}ᶜ : Finset (Fin 5)).card≤3
    rw [Finset.card_compl,Finset.card_pair hab]
    decide
  apply moser_density_impossible hc hw x (Circle.exp φ) (Circle.norm_coe _) J hJ
  intro i
  simpa only [J,Finset.mem_compl] using polynomial_region_density hc hw hpos hneg
    (seven_point_certificate i)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Complete actual triangle-interface endgame, including boundary rigidity,
sector extraction and the exact seven-point unit-distance certificate. -/
lemma no_triangle_interfaces {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i))) : False := by
  have hbinary := triangle_binary_from_continua hc hv hK hH
  obtain ⟨q,hq⟩ := triangle_boundary_one_orbit hc hw hv hK hH
  obtain ⟨φ,rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨b,hpos,hneg⟩ := one_orbit_sectors (triangleState_flip hc hw hbinary) hq
  have hstate (d : Bool) (A : Set ℝ) (hA : MeasurableSet A)
      (hAd : ∀t∈A,(t : Angles)∈angleEssential (triangleState c hc x) d) :
      RealState hc x A {if d then 4 else 3} := by
    refine ⟨hA,?_⟩
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst i
    have hh := angleMk_quasiMeasurePreserving.ae
      ((angleEssential_ae (triangleState c hc x) d).and (triangleState_palette hc hw hbinary d))
    filter_upwards [hh] with t ht hAt
    exact ht.2 (ht.1 (hAd t hAt))
  have hp := hstate b (positiveSector φ) (positiveSector_open φ).measurableSet hpos
  have hn := hstate (!b) (negativeSector φ) (negativeSector_open φ).measurableSet hneg
  exact no_alternating_sectors hc hw (by cases b <;> decide) φ hp hn
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_ContinuumLimits
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma no_triangle_commonInterface_oai {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) {x : ℂ} (h01 : CommonInterface c x 0 1)
    (h12 : CommonInterface c x 1 2) (h20 : CommonInterface c x 2 0) : False := by
  let a : Fin 3 → Fin 5 := ![0,1,2]
  let b : Fin 3 → Fin 5 := ![1,2,0]
  have h (i : Fin 3) : CommonInterface c x (a i) (b i) := by
    fin_cases i
    · exact h01
    · exact h12
    · exact h20
  choose K v hv hK hA hB using h
  apply no_triangle_interfaces hc hw hv (fun i => Classical.choice (hK i))
  intro i j hj
  have he : triangleEdge i={a i,b i} := by fin_cases i <;> decide
  rw [he] at hj
  rcases Finset.mem_insert.mp hj with rfl|hj
  · exact hA i
  · rw [Finset.mem_singleton] at hj; subst j; exact hB i
end EuclideanFiveColor
end

end OAI
end

theorem solution : type_of% @OAI.EuclideanFiveColor.no_triangle_commonInterface_oai := @OAI.EuclideanFiveColor.no_triangle_commonInterface_oai
