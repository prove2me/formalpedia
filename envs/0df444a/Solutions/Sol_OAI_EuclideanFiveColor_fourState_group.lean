-- Prove2me | solution 1 for OAI.EuclideanFiveColor.fourState_group
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:01:24.207425+00:00
-- url     : https://prove2.me/submissions/c95be45a-9b2e-4861-8af9-fdbc5aeffae7

import Mathlib
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_EuclideanFiveColor_ae_not_binary_circle

section
-- module Solutions.OAIQ5_T4.Compat
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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
lemma exists_trace (x : ℂ) : ∃ b : TraceVector k, IsTrace c hc x b := by
  have hd : Dense {y : ℂ | TypicalSampling c y 1} := Measure.dense_of_ae
    (ae_typicalSampling c hc (by norm_num : (0 : ℝ)<1))
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp (hd x)
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (TraceVector k))).isSeqCompact.subseq_of_frequently_in
    (Eventually.frequently (Eventually.of_forall fun n => Set.mem_univ (sampleCode c hc (y n) 1)))
  exact ⟨b,trace_of_realization c hc (fun n => hy (φ n)) (hyt.comp hφ.tendsto_atTop) tendsto_const_nhds hb⟩
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
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Fourier
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
namespace Multiplier
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma clm_ae (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C)
    (g : Lp ℂ 2 μ) : clm μ f hf hbound g =ᵐ[μ] fun x => f x*g x := apply_ae μ f hf hbound g
end Multiplier
lemma planeTranslate_ae (h : ℂ) (g : ComplexPlaneL2) :
    planeTranslate h g =ᵐ[volume] fun x => g (x+h) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_add_right volume h)
lemma phaseMultiplier_ae (h : ℂ) (g : ComplexPlaneL2) :
    phaseMultiplier h g =ᵐ[volume] fun ξ => planePhase h ξ*g ξ := Multiplier.clm_ae _ _ _ _ _
lemma schwartzTranslate_apply (h : ℂ) (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    schwartzTranslate h f x = f (x+h) := rfl
lemma schwartzTranslate_toLp (h : ℂ) (f : SchwartzMap ℂ ℂ) :
    (schwartzTranslate h f).toLp 2 = planeTranslate h (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(schwartzTranslate h f).coeFn_toLp 2,planeTranslate_ae h (f.toLp 2),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (f.coeFn_toLp 2 volume)] with x hx hy hz
  exact hx.trans ((schwartzTranslate_apply h f x).trans (hz.symm.trans hy.symm))
lemma fourier_schwartzTranslate (h : ℂ) (f : SchwartzMap ℂ ℂ) (ξ : ℂ) :
    𝓕 (schwartzTranslate h f) ξ = planePhase h ξ * 𝓕 f ξ := by
  have hh := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ ℂ) (f : ℂ → ℂ) h) ξ
  simpa only [SchwartzMap.fourier_coe,Real.fourier_eq,schwartzTranslate_apply,
    planePhase,Circle.smul_def,smul_eq_mul,VectorFourier.fourierIntegral,Function.comp_def,innerₗ_apply_apply] using hh
lemma fourier_planeTranslate (h : ℂ) (g : ComplexPlaneL2) :
    𝓕 (planeTranslate h g) = phaseMultiplier h (𝓕 g) := by
  apply DenseRange.induction_on (p := fun g : ComplexPlaneL2 => 𝓕 (planeTranslate h g) = phaseMultiplier h (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (E := ℂ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) g
  · exact isClosed_eq ((Lp.fourierTransformₗᵢ ℂ ℂ).continuous.comp (planeTranslate h).continuous)
      ((phaseMultiplier h).continuous.comp (Lp.fourierTransformₗᵢ ℂ ℂ).continuous)
  intro f
  change 𝓕 (planeTranslate h (f.toLp 2)) = phaseMultiplier h (𝓕 (f.toLp 2))
  rw [← schwartzTranslate_toLp,SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (schwartzTranslate h f)).coeFn_toLp 2,phaseMultiplier_ae h ((𝓕 f).toLp 2),
    (𝓕 f).coeFn_toLp 2] with ξ hξ hmul hf
  rw [hξ,hmul,hf]
  exact fourier_schwartzTranslate h f ξ
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter
namespace EuclideanFiveColor.ProbabilityL2
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

variable (μ : Measure X) [SFinite μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
lemma average_toLp_integral {F : X × Ω → ℂ} (hF : StronglyMeasurable F)
    (hF2 : Integrable (fun z => ‖F z‖^2) (μ.prod ν)) (G : Ω → Lp ℂ 2 μ)
    (hG : Integrable G ν) (hrep : ∀ᵐ ω ∂ν, G ω =ᵐ[μ] fun x => F (x,ω)) :
    (average_memLp μ ν hF hF2).toLp (average ν F) = ∫ ω, G ω ∂ν := by
  apply ext_inner_left ℂ
  intro g
  have hg2 : Integrable (fun z : X × Ω => ‖g z.1‖^2) (μ.prod ν) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)).comp_fst ν
  have hpair : Integrable (fun z : X × Ω => inner ℂ (g z.1) (F z)) (μ.prod ν) := by
    apply (hg2.add hF2).mono'
      (((Lp.stronglyMeasurable g).comp_measurable measurable_fst).inner hF).aestronglyMeasurable
    exact Eventually.of_forall fun z => (norm_inner_le_norm _ _).trans
      (by dsimp only [Pi.add_apply]; nlinarith [sq_nonneg (‖g z.1‖-‖F z‖)])
  rw [L2.inner_def,← integral_inner hG g]
  calc
    _ = ∫ x, inner ℂ (g x) (average ν F x) ∂μ := integral_congr_ae (by
      filter_upwards [MemLp.coeFn_toLp (average_memLp μ ν hF hF2)] with x hx
      rw [hx])
    _ = ∫ x, ∫ ω, inner ℂ (g x) (F (x,ω)) ∂ν ∂μ := integral_congr_ae (by
      filter_upwards [fiber_memLp μ ν hF hF2] with x hx
      exact (integral_inner (hx.integrable (by norm_num)) (g x)).symm)
    _ = ∫ ω, ∫ x, inner ℂ (g x) (F (x,ω)) ∂μ ∂ν := integral_integral_swap hpair
    _ = _ := integral_congr_ae (by
      filter_upwards [hrep] with ω hω
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hω] with x hx
      rw [hx])
end EuclideanFiveColor.ProbabilityL2
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_CircleDecay
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma oscillatory_integral_bound {a b : ℝ} (hab : a ≤ b)
    {g g' : ℝ → ℂ} {w w' : ℝ → ℝ}
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (w' t) t)
    (hgi : IntervalIntegrable g' volume a b) (hwi : IntervalIntegrable w' volume a b)
    (hn : ∀ t ∈ Icc a b, ‖g t‖=1) (hwpos : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hwneg : ∀ t ∈ Icc a b, w' t ≤ 0)
    (he : ∀ t ∈ Icc a b, ((w t : ℂ)*Complex.I)*g' t=g t) :
    ‖∫ t in a..b, g t‖ ≤ 2*w a := by
  have hwu : ∀ t ∈ uIcc a b, HasDerivAt (fun t => (w t : ℂ)*Complex.I) ((w' t : ℂ)*Complex.I) t := by
    intro t ht
    exact ((hw t (by simpa [uIcc_of_le hab] using ht)).ofReal_comp).mul_const _
  have hs := intervalIntegral.integral_mul_deriv_eq_deriv_mul hwu
    (fun t ht => hg t (by simpa [uIcc_of_le hab] using ht)) ((show IntervalIntegrable (fun t => (w' t : ℂ)) volume a b from
      ⟨Complex.ofRealCLM.integrable_comp hwi.1,Complex.ofRealCLM.integrable_comp hwi.2⟩).mul_const _) hgi
  have hleft : (∫ t in a..b, ((w t : ℂ)*Complex.I)*g' t) = ∫ t in a..b, g t :=
    intervalIntegral.integral_congr (fun t ht => he t (by simpa [uIcc_of_le hab] using ht))
  rw [hleft] at hs
  have hint : ‖∫ t in a..b, (w' t : ℂ)*Complex.I*g t‖ ≤ ∫ t in a..b, -w' t := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ hwi.neg
    filter_upwards with t ht
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,hn t ⟨ht.1.le,ht.2⟩,mul_one,mul_one,
      abs_of_nonpos (hwneg t ⟨ht.1.le,ht.2⟩)]
    rfl
  have hiw : (∫ t in a..b, -w' t)=w a-w b := by
    rw [intervalIntegral.integral_neg,intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hw t (by simpa [uIcc_of_le hab] using ht)) hwi]
    ring
  have hna : ‖(w a : ℂ)*Complex.I*g a‖=w a := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hwpos a ⟨le_rfl,hab⟩),
      Complex.norm_I,hn a ⟨le_rfl,hab⟩,mul_one,mul_one]
  have hnb : ‖(w b : ℂ)*Complex.I*g b‖=w b := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hwpos b ⟨hab,le_rfl⟩),
      Complex.norm_I,hn b ⟨hab,le_rfl⟩,mul_one,mul_one]
  rw [hs]
  have hh := norm_sub_le ((w b : ℂ)*Complex.I*g b-(w a : ℂ)*Complex.I*g a)
    (∫ t in a..b, (w' t : ℂ)*Complex.I*g t)
  have hh' := norm_sub_le ((w b : ℂ)*Complex.I*g b) ((w a : ℂ)*Complex.I*g a)
  rw [hna,hnb] at hh'
  rw [hiw] at hint
  linarith
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma circleOscillation_norm (r t : ℝ) : ‖circleOscillation r t‖=1 := Complex.norm_exp_ofReal_mul_I _
lemma circleOscillation_continuous (r : ℝ) : Continuous (circleOscillation r) := by unfold circleOscillation; fun_prop
lemma circleOscillation_hasDeriv (r t : ℝ) :
    HasDerivAt (circleOscillation r) ((-r*Real.sin t : ℝ)*Complex.I*circleOscillation r t) t := by
  unfold circleOscillation
  convert (((Real.hasDerivAt_cos t).const_mul r).ofReal_comp.mul_const Complex.I).cexp using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Complex.ofReal_mul,Complex.ofReal_neg]
  ring
lemma circleOscillation_tail {r a : ℝ} (hr : 0 < r) (ha : 0<a) (hab : a≤Real.pi/2) :
    ‖∫ t in a..Real.pi/2, circleOscillation r t‖ ≤ 2/(r*Real.sin a) := by
  have hsin (t : ℝ) (ht : t ∈ Icc a (Real.pi/2)) : 0<Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi (ha.trans_le ht.1) (by linarith [ht.2,Real.pi_pos])
  have hcos (t : ℝ) (ht : t ∈ Icc a (Real.pi/2)) : 0≤Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
  let w := fun t => 1/(r*Real.sin t)
  let w' := fun t => -Real.cos t/(r*(Real.sin t)^2)
  have hw : ∀ t ∈ Icc a (Real.pi/2), HasDerivAt w (w' t) t := by
    intro t ht
    convert ((Real.hasDerivAt_sin t).const_mul r).inv (mul_ne_zero hr.ne' (hsin t ht).ne') using 1 <;> first
    | rfl
    | (change w = (fun y => r * Real.sin y)⁻¹; funext s; simp only [w,Pi.inv_apply,one_div])
    | (change -Real.cos t/(r*(Real.sin t)^2) = -(r*Real.cos t)/(r*Real.sin t)^2; field_simp)
  have hwi : IntervalIntegrable w' volume a (Real.pi/2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (Real.continuous_cos.neg.continuousOn) (continuous_const.mul (Real.continuous_sin.pow 2)).continuousOn
    intro t ht
    have ht' : t ∈ Icc a (Real.pi/2) := by simpa [uIcc_of_le hab] using ht
    exact mul_ne_zero hr.ne' (pow_ne_zero _ (hsin t ht').ne')
  have hi : IntervalIntegrable (fun t => (-r*Real.sin t : ℝ)*Complex.I*circleOscillation r t) volume a (Real.pi/2) := by
    apply Continuous.intervalIntegrable
    unfold circleOscillation
    fun_prop
  have h := oscillatory_integral_bound hab (fun t _ => circleOscillation_hasDeriv r t) hw hi hwi
    (fun t _ => circleOscillation_norm r t) (fun t ht => (one_div_pos.mpr (mul_pos hr (hsin t ht))).le)
    (fun t ht => by dsimp [w']; exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hcos t ht)) (by positivity))
    (fun t ht => by
      dsimp [w]
      have hrC : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have hsC : (Real.sin t : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hsin t ht).ne'
      simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_neg]
      field_simp
      simp only [Complex.I_sq]
      ring)
  simpa only [w,mul_one_div] using h
lemma circleOscillation_quarter {r : ℝ} (hr : 1 ≤ r) :
    ‖∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t‖ ≤ (1+Real.pi)/Real.sqrt r := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hs : 0<Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs1 : 1≤Real.sqrt r := by simpa using Real.sqrt_le_sqrt hr
  let a := 1/Real.sqrt r
  have ha : 0<a := one_div_pos.mpr hs
  have ha1 : a≤1 := (div_le_one hs).mpr hs1
  have hab : a≤Real.pi/2 := by linarith [Real.pi_gt_three]
  have hi := circleOscillation_continuous r
  have hhead : ‖∫ t in (0:ℝ)..a, circleOscillation r t‖ ≤ a := by
    simpa [abs_of_nonneg ha.le] using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := a) (C := (1:ℝ)) (fun t _ => (circleOscillation_norm r t).le)
  have htail := circleOscillation_tail hr0 ha hab
  have hsin := Real.mul_le_sin ha.le hab
  have hden : 0 < r*(2/Real.pi*a) := by positivity
  have hh : 2/(r*Real.sin a) ≤ Real.pi/Real.sqrt r := by
    calc
      _ ≤ 2/(r*(2/Real.pi*a)) := div_le_div_of_nonneg_left (by norm_num) hden
        (mul_le_mul_of_nonneg_left hsin hr0.le)
      _ = Real.pi/Real.sqrt r := by
        dsimp [a]
        field_simp
        nlinarith [Real.sq_sqrt hr0.le]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := a))
    (hi.intervalIntegrable (a := a) (b := Real.pi/2))]
  have hn := norm_add_le (∫ t in (0:ℝ)..a, circleOscillation r t)
    (∫ t in a..Real.pi/2, circleOscillation r t)
  have hea : a + Real.pi/Real.sqrt r = (1+Real.pi)/Real.sqrt r := by dsimp [a]; ring
  linarith
lemma circleOscillation_pi_sub (r t : ℝ) :
    circleOscillation r (Real.pi-t) = (starRingEnd ℂ) (circleOscillation r t) := by
  simp only [circleOscillation,Real.cos_pi_sub,← Complex.exp_conj,map_mul,
    Complex.conj_ofReal,Complex.conj_I]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_neg]
  ring
lemma circleOscillation_two_pi_sub (r t : ℝ) :
    circleOscillation r (2*Real.pi-t) = circleOscillation r t := by
  simp only [circleOscillation,Real.cos_two_pi_sub]
lemma circleOscillation_full {r : ℝ} (hr : 1 ≤ r) :
    ‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation r t‖ ≤ 4*(1+Real.pi)/Real.sqrt r := by
  have hi := circleOscillation_continuous r
  have hq : (∫ t in Real.pi/2..Real.pi, circleOscillation r t) =
      (starRingEnd ℂ) (∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t) := by
    calc
      _ = ∫ t in (0:ℝ)..Real.pi/2, circleOscillation r (Real.pi-t) := by
        rw [intervalIntegral.integral_comp_sub_left]; congr 2 <;> ring
      _ = _ := by simp only [circleOscillation_pi_sub,intervalIntegral.intervalIntegral_conj]
  have hhalf : ‖∫ t in (0:ℝ)..Real.pi, circleOscillation r t‖ ≤
      2*((1+Real.pi)/Real.sqrt r) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := Real.pi/2))
      (hi.intervalIntegrable (a := Real.pi/2) (b := Real.pi)),hq]
    have hn := norm_add_le (∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t)
      ((starRingEnd ℂ) (∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t))
    rw [Complex.norm_conj] at hn
    linarith [circleOscillation_quarter hr]
  have hs : (∫ t in Real.pi..2*Real.pi, circleOscillation r t) =
      ∫ t in (0:ℝ)..Real.pi, circleOscillation r t := by
    calc
      _ = ∫ t in (0:ℝ)..Real.pi, circleOscillation r (2*Real.pi-t) := by
        rw [intervalIntegral.integral_comp_sub_left]; congr 2 <;> ring
      _ = _ := by simp only [circleOscillation_two_pi_sub]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := Real.pi))
    (hi.intervalIntegrable (a := Real.pi) (b := 2*Real.pi)),hs]
  have hn := norm_add_le (∫ t in (0:ℝ)..Real.pi, circleOscillation r t)
    (∫ t in (0:ℝ)..Real.pi, circleOscillation r t)
  rw [mul_div_assoc]
  linarith
end EuclideanFiveColor

end

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
lemma circlePhase_real (ξ : ℂ) (t : ℝ) :
    planePhase (direction (t:Angles)) ξ = circleOscillation (2*Real.pi*‖ξ‖) (t-Complex.arg ξ) := by
  have hinner : inner ℝ (direction (t:Angles)) ξ = ‖ξ‖*Real.cos (t-Complex.arg ξ) := by
    rw [Complex.inner,direction_real,Circle.coe_exp,Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im]
    rw [Real.cos_sub]
    have hr := Complex.norm_mul_cos_arg ξ
    have hi := Complex.norm_mul_sin_arg ξ
    rw [← hr,← hi]
    ring
  rw [planePhase,hinner,Real.fourierChar_apply]
  simp only [circleOscillation]
  congr 1
  push_cast
  ring
lemma circleSymbol_integral (ξ : ℂ) :
    circleSymbol ξ = (2*Real.pi)⁻¹ • ∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t := by
  have hp : Function.Periodic (circleOscillation (2*Real.pi*‖ξ‖)) (2*Real.pi) := by
    intro t
    simp only [circleOscillation,Real.cos_add_two_pi]
  rw [circleSymbol,angularMeasure,AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2*Real.pi) 0]
  congr 1
  simp_rw [circlePhase_real]
  rw [intervalIntegral.integral_comp_sub_right]
  simpa [sub_eq_add_neg,add_comm] using hp.intervalIntegral_add_eq (-(Complex.arg ξ)) 0
lemma circleSymbol_sq_bound (ξ : ℂ) : ‖circleSymbol ξ‖^2 ≤ 400/(1+‖ξ‖) := by
  have hn : 0≤‖ξ‖ := norm_nonneg _
  by_cases hs : ‖ξ‖≤1
  · have hb := circleSymbol_norm_le_one ξ
    apply (le_div_iff₀ (by positivity : 0<1+‖ξ‖)).mpr
    nlinarith [norm_nonneg (circleSymbol ξ)]
  have hr : 1≤2*Real.pi*‖ξ‖ := by nlinarith [Real.pi_gt_three]
  have hb := circleOscillation_full hr
  rw [circleSymbol_integral,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by positivity))]
  have hsqr := Real.sq_sqrt (by positivity : 0≤2*Real.pi*‖ξ‖)
  have hsqrt : 0<Real.sqrt (2*Real.pi*‖ξ‖) := Real.sqrt_pos.mpr (by positivity)
  have hlow : 0<2*Real.pi := by positivity
  have hq := (le_div_iff₀ hsqrt).mp hb
  have hpos := norm_nonneg (∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t)
  have hq2 : (‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖ * Real.sqrt (2*Real.pi*‖ξ‖))^2 ≤ (4*(1+Real.pi))^2 :=
    pow_le_pow_left₀ (mul_nonneg hpos hsqrt.le) hq 2
  apply (le_div_iff₀ (by positivity : 0<1+‖ξ‖)).mpr
  rw [mul_pow,hsqr] at hq2
  have hpi : Real.pi<4 := Real.pi_lt_four
  have hN : ‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖^2 * ‖ξ‖ ≤ 100 := by
    have hmul := mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le)
      (mul_nonneg (sq_nonneg (‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖)) hn)
    nlinarith [Real.pi_gt_three]
  rw [mul_pow,inv_pow]
  have hN' : ‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖^2 ≤ 100 := by
    nlinarith [sq_nonneg (‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖)]
  rw [← div_eq_inv_mul,div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hlow)]
  nlinarith [Real.pi_gt_three]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_CircleOperator
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
lemma planeTranslate_continuous (g : ComplexPlaneL2) : Continuous (fun h => planeTranslate h g) := by
  let f : C(ℂ,C(ℂ,ℂ)) := (ContinuousMap.mk (fun p : ℂ × ℂ => p.2+p.1) (by fun_prop)).curry
  exact continuous_const.compMeasurePreservingLp f.continuous (fun h => measurePreserving_add_right volume h) (by simp)
lemma circleTranslate_integrable (g : ComplexPlaneL2) : Integrable (fun t => planeTranslate (direction t) g) angularMeasure :=
  Integrable.of_bound ((planeTranslate_continuous g).comp direction_continuous).aestronglyMeasurable ‖g‖
    (Eventually.of_forall fun t => (planeTranslate (direction t)).norm_map g |>.le)
lemma circleOperator_ae (g : ComplexPlaneL2) :
    circleOperator g =ᵐ[volume] fun x => ∫ t, g (x+direction t) ∂angularMeasure := by
  let F : ℂ × Angles → ℂ := fun p => g (p.1+direction p.2)
  have hF : StronglyMeasurable F := (Lp.stronglyMeasurable g).comp_measurable
    (measurable_fst.add (direction_continuous.measurable.comp measurable_snd))
  have hg2 : Integrable (fun x => ‖g x‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hi : Integrable (fun p => ‖F p‖^2) (volume.prod angularMeasure) := by
    apply (integrable_prod_iff' (hF.norm.pow 2).aestronglyMeasurable).mpr
    constructor
    · exact Eventually.of_forall fun t => (measurePreserving_add_right volume (direction t)).integrable_comp_of_integrable hg2
    · have he : (fun t => ∫ x, ‖‖F (x,t)‖^2‖ ∂volume) = fun _ => ∫ x, ‖g x‖^2 ∂volume := by
        funext t
        simp only [Real.norm_eq_abs,abs_sq,F]
        change (∫ x : ℂ, (fun y => ‖g y‖^2) (x+direction t)) = _
        exact (measurePreserving_add_right volume (direction t)).integral_comp
          (Homeomorph.addRight (direction t)).measurableEmbedding (fun y : ℂ => ‖g y‖^2)
      simp only [Pi.pow_apply]
      rw [he]
      exact integrable_const _
  have h := ProbabilityL2.average_toLp_integral volume angularMeasure hF hi
    (fun t => planeTranslate (direction t) g) (circleTranslate_integrable g)
    (Eventually.of_forall fun t => planeTranslate_ae (direction t) g)
  have ha : circleOperator g = (ProbabilityL2.average_memLp volume angularMeasure hF hi).toLp (ProbabilityL2.average angularMeasure F) := h.symm
  rw [ha]
  exact MemLp.coeFn_toLp (ProbabilityL2.average_memLp volume angularMeasure hF hi)
lemma circleMultiplier_ae (g : ComplexPlaneL2) :
    circleMultiplier g =ᵐ[volume] fun x => circleSymbol x*g x := Multiplier.clm_ae _ _ _ _ _
lemma fourier_circleOperator (g : ComplexPlaneL2) : 𝓕 (circleOperator g) = circleMultiplier (𝓕 g) := by
  let F : ℂ × Angles → ℂ := fun p => planePhase (direction p.2) p.1 * 𝓕 g p.1
  have hF : StronglyMeasurable F := by
    have h : Continuous (fun p : ℂ × Angles => planePhase (direction p.2) p.1) := by
      unfold planePhase
      exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        ((direction_continuous.comp continuous_snd).inner continuous_fst)
    exact h.stronglyMeasurable.mul ((Lp.stronglyMeasurable (𝓕 g)).comp_measurable measurable_fst)
  have hi : Integrable (fun p => ‖F p‖^2) (volume.prod angularMeasure) := by
    have he : (fun p => ‖F p‖^2) = fun p => ‖𝓕 g p.1‖^2 := by
      funext p
      simp only [F,norm_mul,planePhase_norm,one_mul]
    rw [he]
    exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (𝓕 g))).mp
      (Lp.memLp (𝓕 g))).comp_fst angularMeasure
  have hG : Integrable (fun t => 𝓕 (planeTranslate (direction t) g)) angularMeasure :=
    (Lp.fourierTransformₗᵢ ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (circleTranslate_integrable g)
  have h := ProbabilityL2.average_toLp_integral volume angularMeasure hF hi
    (fun t => 𝓕 (planeTranslate (direction t) g)) hG (Eventually.of_forall fun t => by
      rw [fourier_planeTranslate]
      exact phaseMultiplier_ae (direction t) (𝓕 g))
  have hc := (Lp.fourierTransformₗᵢ ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (circleTranslate_integrable g)
  change (∫ t, 𝓕 (planeTranslate (direction t) g) ∂angularMeasure) = 𝓕 (circleOperator g) at hc
  rw [← hc,← h]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (ProbabilityL2.average_memLp volume angularMeasure hF hi),
    circleMultiplier_ae (𝓕 g)] with x hx hy
  rw [hx,hy]
  exact integral_mul_const (𝓕 g x) (fun t => planePhase (direction t) x)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
lemma planePhase_sub_bound (h ξ : ℂ) : ‖1-planePhase h ξ‖ ≤ 8*‖h‖*‖ξ‖ := by
  have he : planePhase h ξ = Complex.exp (Complex.I * (2*Real.pi*inner ℝ h ξ : ℝ)) := by
    rw [planePhase,Real.fourierChar_apply,mul_comm Complex.I]
  rw [he,norm_sub_rev]
  apply (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*inner ℝ h ξ)).trans
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)]
  have hi := abs_real_inner_le_norm h ξ
  have hp := mul_nonneg (norm_nonneg h) (norm_nonneg ξ)
  calc
    _ ≤ 2*Real.pi*(‖h‖*‖ξ‖) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ 8*‖h‖*‖ξ‖ := by nlinarith [Real.pi_lt_four]
lemma planePhase_sub_bound_two (h ξ : ℂ) : ‖1-planePhase h ξ‖≤2 := by
  have hi := norm_sub_le (1:ℂ) (planePhase h ξ)
  simpa only [norm_one,planePhase_norm,one_add_one_eq_two] using hi

lemma circleDifferenceRatio_nonneg (h ξ : ℂ) : 0 ≤ circleDifferenceRatio h ξ := by
  unfold circleDifferenceRatio
  positivity
lemma circleDifferenceRatio_small (h ξ : ℂ) :
    circleDifferenceRatio h ξ ≤ 64*‖h‖*‖ξ‖^2 := by
  by_cases hh : h=0
  · simp [hh,circleDifferenceRatio]
  have hh0 : 0<‖h‖ := norm_pos_iff.mpr hh
  have hb := planePhase_sub_bound h ξ
  have hc := circleSymbol_norm_le_one ξ
  have hc2 : ‖circleSymbol ξ‖^2 ≤ 1 := by nlinarith [norm_nonneg (circleSymbol ξ)]
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  unfold circleDifferenceRatio
  apply (div_le_iff₀ hh0).mpr
  calc
    _ ≤ ‖1-planePhase h ξ‖^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg ‖1-planePhase h ξ‖)]
    _ ≤ (8*‖h‖*‖ξ‖)^2 := hb2
    _ = _ := by ring
lemma circleDifferenceRatio_bound (h ξ : ℂ) : circleDifferenceRatio h ξ ≤ 25600 := by
  by_cases hh : h=0
  · simp [hh,circleDifferenceRatio]
  have hh0 : 0<‖h‖ := norm_pos_iff.mpr hh
  have hn : 0<1+‖ξ‖ := by positivity
  have hc := (le_div_iff₀ hn).mp (circleSymbol_sq_bound ξ)
  by_cases hs : ‖h‖*‖ξ‖≤1
  · have hb2 := pow_le_pow_left₀ (norm_nonneg _) (planePhase_sub_bound h ξ) 2
    have hmul := mul_le_mul_of_nonneg_left hb2 (sq_nonneg ‖circleSymbol ξ‖)
    have hs' : ‖h‖ * ‖ξ‖^2 ≤ ‖ξ‖ := by nlinarith [mul_nonneg (sub_nonneg.mpr hs) (norm_nonneg ξ)]
    have hc' : ‖circleSymbol ξ‖^2 * ‖ξ‖ ≤ 400 := by nlinarith [sq_nonneg ‖circleSymbol ξ‖]
    have hb : ‖circleSymbol ξ‖^2 * (‖h‖ * ‖ξ‖^2) ≤ 400 :=
      (mul_le_mul_of_nonneg_left hs' (sq_nonneg _)).trans hc'
    unfold circleDifferenceRatio
    apply (div_le_iff₀ hh0).mpr
    have hb' := mul_le_mul_of_nonneg_left hb (by positivity : 0≤64*‖h‖)
    nlinarith
  · have hb2 := pow_le_pow_left₀ (norm_nonneg _) (planePhase_sub_bound_two h ξ) 2
    have hc' : ‖circleSymbol ξ‖^2 ≤ 400*‖h‖ := by
      have hmul := mul_le_mul_of_nonneg_left hc (norm_nonneg h)
      have hi := mul_nonneg (sq_nonneg ‖circleSymbol ξ‖)
        (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hs)))
      nlinarith
    unfold circleDifferenceRatio
    apply (div_le_iff₀ hh0).mpr
    have hmul := mul_le_mul_of_nonneg_left hb2 (sq_nonneg ‖circleSymbol ξ‖)
    nlinarith
lemma circleDifferenceRatio_tendsto (ξ : ℂ) :
    Tendsto (fun h => circleDifferenceRatio h ξ) (𝓝 0) (𝓝 0) := by
  apply squeeze_zero (fun h => circleDifferenceRatio_nonneg h ξ)
    (fun h => circleDifferenceRatio_small h ξ)
  simpa using ((continuous_norm.tendsto (0:ℂ)).const_mul 64).mul_const (‖ξ‖^2)
lemma circleDifferenceRatio_measurable (h : ℂ) : StronglyMeasurable (circleDifferenceRatio h) := by
  unfold circleDifferenceRatio
  have hc : StronglyMeasurable circleSymbol := by
    have h' : Continuous (fun p : ℂ × Angles => planePhase (direction p.2) p.1) := by
      unfold planePhase
      exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        ((direction_continuous.comp continuous_snd).inner continuous_fst)
    exact h'.stronglyMeasurable.integral_prod_right'
  exact ((hc.norm.pow 2).mul ((continuous_const.sub (planePhase_continuous h)).stronglyMeasurable.norm.pow 2)).div stronglyMeasurable_const
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
lemma planeL2_norm_sq (g : ComplexPlaneL2) : ‖g‖^2 = ∫ x, ‖g x‖^2 ∂volume := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
lemma circleDifference_norm_sq (g : ComplexPlaneL2) (h : ℂ) :
    ‖circleOperator (g-planeTranslate h g)‖^2 / ‖h‖ =
      ∫ ξ, circleDifferenceRatio h ξ * ‖𝓕 g ξ‖^2 ∂volume := by
  have hn := (Lp.fourierTransformₗᵢ ℂ ℂ).norm_map (circleOperator (g-planeTranslate h g))
  change ‖𝓕 (circleOperator (g-planeTranslate h g))‖ = _ at hn
  rw [← hn, fourier_circleOperator]
  have hs : 𝓕 (g-planeTranslate h g) = 𝓕 g - phaseMultiplier h (𝓕 g) := by
    change (Lp.fourierTransformₗᵢ ℂ ℂ) (g-planeTranslate h g) = _
    rw [map_sub]
    exact congrArg (fun f => 𝓕 g-f) (fourier_planeTranslate h g)
  rw [hs,planeL2_norm_sq,← integral_div]
  apply integral_congr_ae
  filter_upwards [circleMultiplier_ae (𝓕 g-phaseMultiplier h (𝓕 g)),
    Lp.coeFn_sub (𝓕 g) (phaseMultiplier h (𝓕 g)), phaseMultiplier_ae h (𝓕 g)] with ξ hc hs hp
  rw [hc,hs,Pi.sub_apply,hp]
  have he : 𝓕 g ξ-planePhase h ξ*𝓕 g ξ = (1-planePhase h ξ)*𝓕 g ξ := by ring
  rw [he,norm_mul,norm_mul]
  unfold circleDifferenceRatio
  ring
lemma circle_smoothing_L2 (g : ComplexPlaneL2) :
    Tendsto (fun h : ℂ => ‖circleOperator (g-planeTranslate h g)‖^2 / ‖h‖)
      (𝓝 0) (𝓝 0) := by
  simp_rw [circleDifference_norm_sq]
  have hg : Integrable (fun ξ => ‖𝓕 g ξ‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (𝓕 g))).mp (Lp.memLp (𝓕 g))
  have hd := tendsto_integral_filter_of_dominated_convergence
    (fun ξ : ℂ => 25600*‖𝓕 g ξ‖^2)
    (F := fun h ξ => circleDifferenceRatio h ξ * ‖𝓕 g ξ‖^2)
    (f := fun _ => (0:ℝ)) (l := 𝓝 (0:ℂ))
    (Eventually.of_forall fun h =>
      ((circleDifferenceRatio_measurable h).mul ((Lp.stronglyMeasurable (𝓕 g)).norm.pow 2)).aestronglyMeasurable)
    (Eventually.of_forall fun h => Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (circleDifferenceRatio_nonneg h ξ) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (circleDifferenceRatio_bound h ξ) (sq_nonneg _))
    (hg.const_mul 25600)
    (Eventually.of_forall fun ξ => by simpa using (circleDifferenceRatio_tendsto ξ).mul_const (‖𝓕 g ξ‖^2))
  simpa using hd
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
lemma ae_circle_pullback {p : ℂ → Prop} (hp : ∀ᵐ x ∂(volume : Measure ℂ), p x) :
    ∀ᵐ q ∂(volume : Measure ℂ), ∀ᵐ t ∂angularMeasure, p (q+direction t) := by
  have hq : QuasiMeasurePreserving (fun z : ℂ × Angles => z.1+direction z.2)
      (volume.prod angularMeasure) volume :=
    QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (direction_continuous.measurable.comp measurable_snd))
      (Eventually.of_forall fun t => (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving)
  exact Measure.ae_ae_of_ae_prod (hq.ae hp)
lemma circleOperator_toLp_ae {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    circleOperator (hf.toLp f) =ᵐ[volume] circleAverage f := by
  filter_upwards [circleOperator_ae (hf.toLp f),ae_circle_pullback (MemLp.coeFn_toLp hf)] with q hq he
  exact hq.trans (integral_congr_ae he)
lemma circleOperator_difference_ae {f : ℂ → ℂ} (hf : MemLp f 2 volume) (h : ℂ) :
    circleOperator (hf.toLp f-planeTranslate h (hf.toLp f)) =ᵐ[volume]
      circleAverage (fun q => f q-f (q+h)) := by
  have hfh : MemLp (fun q => f (q+h)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume h)
  have he : (hf.sub hfh).toLp (fun q => f q-f (q+h)) = hf.toLp f-planeTranslate h (hf.toLp f) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hf.sub hfh),Lp.coeFn_sub (hf.toLp f) (planeTranslate h (hf.toLp f)),
      MemLp.coeFn_toLp hf,planeTranslate_ae h (hf.toLp f),
      (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (MemLp.coeFn_toLp hf)] with q h1 h2 h3 h4 h5
    change ((hf.sub hfh).toLp (fun q => f q-f (q+h))) q = _ at h1
    simp only [h1,h2,Pi.sub_apply,h3,h4,h5]
  rw [← he]
  exact circleOperator_toLp_ae (hf.sub hfh)
lemma colorMass_nonneg {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (q : ℂ) : 0 ≤ colorMass c i q :=
  integral_nonneg (sampleFn_nonneg c q 1 i)
lemma colorCutoff_sample {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (x q h : ℂ) (R : ℝ)
    (hq : q ∈ Metric.ball x R) (hh : ‖h‖<1) (t : Angles) :
    colorCutoff c i x R (q+direction t+h) = if c (q+direction t+h)=i then 1 else 0 := by
  apply Set.indicator_of_mem
  rw [Metric.mem_closedBall,dist_eq_norm]
  have hn := norm_add_le (q-x) (direction t+h)
  have hn' := norm_add_le (direction t) h
  have hd : ‖direction t‖=1 := Circle.norm_coe _
  have hqr : ‖q-x‖<R := by simpa only [Metric.mem_ball,dist_eq_norm] using hq
  rw [show q+direction t+h-x=(q-x)+(direction t+h) by ring]
  linarith
lemma colorCutoff_circleDifference {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (i : Fin k)
    (x q h : ℂ) (R : ℝ) (hq : q ∈ Metric.ball x R) (hh : ‖h‖<1) :
    circleAverage (fun y => colorCutoff c i x R y-colorCutoff c i x R (y+h)) q =
      ((colorMass c i q-colorMass c i (q+h) : ℝ) : ℂ) := by
  have he (t : Angles) : colorCutoff c i x R (q+direction t)-colorCutoff c i x R (q+direction t+h) =
      ((sampleFn c q 1 i t-sampleFn c (q+h) 1 i t : ℝ) : ℂ) := by
    have h0 := colorCutoff_sample c i x q 0 R hq (by simp) t
    simp only [add_zero] at h0
    rw [h0,colorCutoff_sample c i x q h R hq hh t]
    simp only [sampleFn,Complex.ofReal_one,one_mul,show q+direction t+h=q+h+direction t by ring,
      Complex.ofReal_sub]
    split_ifs <;> simp
  unfold circleAverage
  simp_rw [he,integral_complex_ofReal]
  rw [integral_sub ((sampleFn_memLp c hc q 1 i).integrable (by norm_num))
    ((sampleFn_memLp c hc (q+h) 1 i).integrable (by norm_num))]
  rfl
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Transitions
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma transitionSet_measurable (hc : Measurable c) (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) :
    MeasurableSet (transitionSet c i j x R h) := by
  exact measurableSet_ball.inter (((measurableSet_eq_fun hc measurable_const).inter
    (measurableSet_eq_fun (hc.comp (measurable_id.add_const h)) measurable_const)).union
    ((measurableSet_eq_fun hc measurable_const).inter
    (measurableSet_eq_fun (hc.comp (measurable_id.add_const h)) measurable_const)))
lemma transitionSet_finite (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) :
    volume (transitionSet c i j x R h) < ⊤ :=
  (measure_mono (fun _ hq => Metric.ball_subset_closedBall hq.1)).trans_lt
    (isCompact_closedBall x R).measure_lt_top
lemma transition_abundance {i j : Fin k} {x : ℂ} (he : TransitionEdge c i j x)
    {R : ℝ} (hR : 0<R) : ∃ a : ℝ, 0<a ∧
      ∃ᶠ h in 𝓝[≠] (0:ℂ), a*‖h‖ < volume.real (transitionSet c i j x R h) := by
  obtain ⟨a,_,ha,hal⟩ := ENNReal.lt_iff_exists_real_btwn.mp (he.2 R hR)
  have ha0 : 0<a := ENNReal.ofReal_pos.mp ha
  refine ⟨a,ha0,?_⟩
  have hf := frequently_lt_of_lt_limsup (h := hal)
  refine (hf.and_eventually self_mem_nhdsWithin).mono ?_
  intro h hh
  have hne : h≠0 := hh.2
  have hn : ENNReal.ofReal ‖h‖≠0 := (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hne)).ne'
  have hm : ENNReal.ofReal a*ENNReal.ofReal ‖h‖ < volume (transitionSet c i j x R h) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hn) (Or.inl ENNReal.ofReal_ne_top)).mp hh.1
  rw [← ENNReal.ofReal_mul ha0.le] at hm
  exact (ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg ha0.le (norm_nonneg h)) (transitionSet_finite c i j x R h).ne).mp hm
lemma colorMass_own_zero (hc : Measurable c) (hw : WeakColoring k c) {q : ℂ}
    (hq : Typical c q) (hs : TypicalSampling c q 1) : colorMass c (c q) q=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hs.2] with t ht
  simp only [Complex.ofReal_one,one_mul] at ht
  have hn : c (q+direction t)≠c q := by
    intro he
    have hd : ‖q-(q+direction t)‖=1 := by
      simp only [sub_add_cancel_left,norm_neg]
      exact Circle.norm_coe _
    exact weak_density_proper c hc hw (c q) hd hq (by simpa only [Typical,he] using ht)
  simp only [sampleFn,Complex.ofReal_one,one_mul,ite_eq_right hn,Pi.zero_apply]
lemma exists_energy_small {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {T : Set X} (hT : MeasurableSet T) (hfin : μ T < ⊤) {E : X → ℝ}
    (hE : Integrable E μ) (hn : ∀ᵐ q ∂μ, 0≤E q) {P : X → Prop} (hP : ∀ᵐ q ∂μ, P q)
    {d : ℝ} (hi : (∫ q, E q ∂μ) < d*μ.real T) : ∃ q ∈ T, P q ∧ E q<d := by
  by_contra! h
  have : IsFiniteMeasure (μ.restrict T) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  have hge : ∀ᵐ q ∂μ.restrict T, d≤E q := by
    filter_upwards [ae_restrict_mem hT,ae_restrict_of_ae hP] with q hq hp
    exact h q hq hp
  have hl := integral_mono_ae (integrable_const d) hE.restrict hge
  have hr := integral_mono_measure (μ.restrict_le_self (s := T)) hn hE
  have he : (∫ _q in T, d ∂μ)=d*μ.real T := by simp [mul_comm]
  rw [he] at hl
  exact (not_lt_of_ge (hl.trans hr)) hi
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma colorError_ae (i : Fin k) (x : ℂ) (R : ℝ) {h : ℂ} (hh : ‖h‖<1) :
    ∀ᵐ q ∂(volume : Measure ℂ), q ∈ Metric.ball x R →
      colorError c hc i x R h q = ((colorMass c i q-colorMass c i (q+h) : ℝ) : ℂ) := by
  filter_upwards [circleOperator_difference_ae (colorCutoff_memLp c hc i x R) h] with q hq hB
  exact hq.trans (colorCutoff_circleDifference c hc i x q h R hB hh)
lemma colorError_smoothing (i : Fin k) (x : ℂ) (R : ℝ) :
    Tendsto (fun h : ℂ => ‖colorError c hc i x R h‖^2 / ‖h‖) (𝓝 0) (𝓝 0) :=
  circle_smoothing_L2 _
lemma transition_mass_energy (hw : WeakColoring k c) (i j : Fin k) (x : ℂ) (R : ℝ)
    {h : ℂ} (hh : ‖h‖<1) : ∀ᵐ q ∂(volume : Measure ℂ), q ∈ transitionSet c i j x R h →
      (colorMass c i q+colorMass c j q)^2 ≤
        ‖colorError c hc i x R h q‖^2+‖colorError c hc j x R h q‖^2 := by
  filter_upwards [colorError_ae c hc i x R hh,colorError_ae c hc j x R hh,
    ae_density_actual c hc,ae_typicalSampling c hc (by norm_num : (0:ℝ)<1),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (ae_density_actual c hc),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae
      (ae_typicalSampling c hc (by norm_num : (0:ℝ)<1))] with q hi hj hq hqs hqh hqhs hT
  have he_i : ‖colorError c hc i x R h q‖^2=(colorMass c i q-colorMass c i (q+h))^2 := by
    rw [hi hT.1,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have he_j : ‖colorError c hc j x R h q‖^2=(colorMass c j q-colorMass c j (q+h))^2 := by
    rw [hj hT.1,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [he_i,he_j]
  have h0 := colorMass_own_zero c hc hw hq hqs
  have h1 := colorMass_own_zero c hc hw hqh hqhs
  rcases hT.2 with ⟨hqi,hqj⟩ | ⟨hqj,hqi⟩
  · rw [hqi] at h0
    rw [hqj] at h1
    rw [h0,h1]
    nlinarith [sq_nonneg (colorMass c i (q+h))]
  · rw [hqj] at h0
    rw [hqi] at h1
    rw [h0,h1]
    nlinarith [sq_nonneg (colorMass c j (q+h))]
include hc in
lemma transition_small_mass (hw : WeakColoring k c) {i j : Fin k} {x : ℂ}
    (he : TransitionEdge c i j x) {R ε : ℝ} (hR : 0<R) (hε : 0<ε) :
    ∃ q ∈ Metric.ball x R, TypicalSampling c q 1 ∧ colorMass c i q+colorMass c j q<ε := by
  obtain ⟨a,ha,hfreq⟩ := transition_abundance c he hR
  have hlim : Tendsto (fun h : ℂ =>
      (‖colorError c hc i x R h‖^2+‖colorError c hc j x R h‖^2)/‖h‖) (𝓝 0) (𝓝 0) := by
    simp only [add_div]
    simpa only [add_zero] using (colorError_smoothing c hc i x R).add (colorError_smoothing c hc j x R)
  have hsmall : ∀ᶠ h in 𝓝[≠] (0:ℂ),
      (‖colorError c hc i x R h‖^2+‖colorError c hc j x R h‖^2)/‖h‖<ε^2*a :=
    (hlim.eventually (gt_mem_nhds (by positivity))).filter_mono nhdsWithin_le_nhds
  have hnorm : ∀ᶠ h in 𝓝[≠] (0:ℂ), ‖h‖<1 :=
    (continuous_norm.tendsto (0:ℂ)).eventually (by simpa using (gt_mem_nhds (by norm_num : (0:ℝ)<1)))
      |>.filter_mono nhdsWithin_le_nhds
  obtain ⟨h,hab,hsm,hhn,hne⟩ := (hfreq.and_eventually (hsmall.and (hnorm.and self_mem_nhdsWithin))).exists
  have hnpos : 0<‖h‖ := norm_pos_iff.mpr hne
  let E : ℂ → ℝ := fun q => ‖colorError c hc i x R h q‖^2+‖colorError c hc j x R h q‖^2
  have hEi : Integrable (fun q => ‖colorError c hc i x R h q‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hEj : Integrable (fun q => ‖colorError c hc j x R h q‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hInt : (∫ q, E q ∂volume) < ε^2*volume.real (transitionSet c i j x R h) := by
    rw [show (∫ q, E q ∂volume) = ‖colorError c hc i x R h‖^2+‖colorError c hc j x R h‖^2 by
      dsimp only [E]
      rw [integral_add hEi hEj,← planeL2_norm_sq,← planeL2_norm_sq]]
    have hs := (div_lt_iff₀ hnpos).mp hsm
    have hab' := mul_lt_mul_of_pos_left hab (sq_pos_of_pos hε)
    nlinarith
  obtain ⟨q,hq,hqs,henergy⟩ := exists_energy_small volume (transitionSet_measurable c hc i j x R h)
    (transitionSet_finite c i j x R h) (hEi.add hEj)
    (Eventually.of_forall fun q => add_nonneg (sq_nonneg _) (sq_nonneg _))
    ((ae_typicalSampling c hc (by norm_num : (0:ℝ)<1)).and (transition_mass_energy c hc hw i j x R hhn)) hInt
  refine ⟨q,hq.1,hqs.1,?_⟩
  have hm := hqs.2 hq
  change E q<ε^2 at henergy
  change (colorMass c i q+colorMass c j q)^2≤E q at hm
  nlinarith
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
lemma palette_nonempty (x : ℂ) : ∀ᵐ t ∂angularMeasure, (palette c hc x t).Nonempty := by
  obtain ⟨b,hb⟩ := exists_trace c hc x
  let B : Traces c hc x := ⟨b,hb⟩
  have hsum := (trace_bounds c hc hb).2.2
  have hs : (fun t => ∑ i, traceValue b i t) =ᵐ[angularMeasure] (fun _ => (1 : ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (traceValue b)
    rw [hsum] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  filter_upwards [hs,ae_all_iff.mpr (fun i => tracePositive_le_palette c hc x i B)] with t ht hP
  have he : ∃ i : Fin k, 0 < traceValue b i t := by
    by_contra! hh
    have hz : (∑ i, traceValue b i t) ≤ 0 := Finset.sum_nonpos (fun i _ => hh i)
    linarith
  obtain ⟨i,hi⟩ := he
  exact ⟨i,(mem_palette c hc x t i).mpr ((hP i) hi)⟩
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma inner_oneL2_integral (f : RealL2 angularMeasure) :
    ⟪f,oneL2 angularMeasure⟫ = ∫ t, f t ∂angularMeasure := by
  rw [real_inner_comm]
  exact (L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top angularMeasure Set.univ) f).trans
    (by simp)
lemma sample_inner_one (i : Fin k) (q : ℂ) :
    ⟪sample c hc q 1 i,oneL2 angularMeasure⟫ = colorMass c i q := by
  rw [inner_oneL2_integral]
  exact integral_congr_ae (sample_ae c hc q 1 i)
lemma transition_avoiding_trace (hw : WeakColoring k c) {i j : Fin k} {x : ℂ}
    (he : TransitionEdge c i j x) :
    ∃ b : TraceVector k, IsTrace c hc x b ∧ traceValue b i=0 ∧ traceValue b j=0 := by
  obtain ⟨q,hq⟩ := Classical.axiomOfChoice (fun n : ℕ => transition_small_mass c hc hw he
    (R := 1/((n:ℝ)+1)) (ε := 1/((n:ℝ)+1)) (by positivity) (by positivity))
  have hqt : Tendsto q atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun n => dist_nonneg)
      (fun n => (hq n).1.le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (TraceVector k))).isSeqCompact.subseq_of_frequently_in
    (Eventually.frequently (Eventually.of_forall fun n => Set.mem_univ (sampleCode c hc (q n) 1)))
  have htrace : IsTrace c hc x b := trace_of_realization c hc
    (fun n => (hq (φ n)).2.1) (hqt.comp hφ.tendsto_atTop) tendsto_const_nhds hb
  have hmass (a : Fin k) (ha : a=i ∨ a=j) : ∫ t, traceValue b a t ∂angularMeasure = 0 := by
    have ht := (traceCode_tendsto_iff.mp hb) a (oneL2 angularMeasure)
    simp only [Function.comp_apply,traceValue_sampleCode,sample_inner_one] at ht
    rw [inner_oneL2_integral] at ht
    have ht' : Tendsto (fun n => colorMass c a (q n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => colorMass_nonneg c a (q n)) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rcases ha with rfl | rfl
      · exact (le_add_of_nonneg_right (colorMass_nonneg c j (q n))).trans (hq n).2.2.le
      · exact (le_add_of_nonneg_left (colorMass_nonneg c i (q n))).trans (hq n).2.2.le
    exact tendsto_nhds_unique ht (ht'.comp hφ.tendsto_atTop)
  have hzero (a : Fin k) (ha : a=i ∨ a=j) : traceValue b a=0 := by
    apply Lp.ext
    have hi : Integrable (traceValue b a) angularMeasure := (Lp.memLp _).integrable (by norm_num)
    have hz := (integral_eq_zero_iff_of_nonneg_ae ((trace_bounds c hc htrace).1 a) hi).mp (hmass a ha)
    exact hz.trans (Lp.coeFn_zero ℝ 2 angularMeasure).symm
  exact ⟨b,htrace,hzero i (Or.inl rfl),hzero j (Or.inr rfl)⟩
lemma edge_palette_not_pair (hw : WeakColoring k c) {i j : Fin k} {x : ℂ}
    (he : TransitionEdge c i j x) : ∀ᵐ t ∂angularMeasure, ¬ palette c hc x t ⊆ {i,j} := by
  obtain ⟨b,hb,hi,hj⟩ := transition_avoiding_trace c hc hw he
  have hs : (fun t => ∑ a, traceValue b a t) =ᵐ[angularMeasure] (fun _ => (1 : ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (traceValue b)
    rw [(trace_bounds c hc hb).2.2] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  have hzi : traceValue b i =ᵐ[angularMeasure] (fun _ => (0:ℝ)) := by rw [hi]; exact Lp.coeFn_zero _ _ _
  have hzj : traceValue b j =ᵐ[angularMeasure] (fun _ => (0:ℝ)) := by rw [hj]; exact Lp.coeFn_zero _ _ _
  filter_upwards [hs,hzi,hzj,ae_all_iff.mpr (fun a => tracePositive_le_palette c hc x a ⟨b,hb⟩)] with t ht hi0 hj0 hp hsub
  have hnon : ∀ a : Fin k, traceValue b a t ≤ 0 := by
    intro a
    by_contra! ha
    have ham := hsub ((mem_palette c hc x t a).mpr (hp a ha))
    simp only [Finset.mem_insert,Finset.mem_singleton] at ham
    rcases ham with rfl | rfl <;> linarith
  have hh := Finset.sum_nonpos (s := Finset.univ) (fun a _ => hnon a)
  linarith
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

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BinaryPalettes
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma exact_sample_isTrace {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) {y : ℂ}
    (hy : TypicalSampling c y 1) : IsTrace c hc y (sampleCode c hc y 1) :=
  subset_closure ⟨hy,rfl⟩
lemma trace_positive_le_palette {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) {y : ℂ}
    {b : TraceVector k} (hb : IsTrace c hc y b) (i : Fin k) :
    ∀ᵐ t ∂angularMeasure, 0 < traceValue b i t → t ∈ paletteSet c hc y i :=
  tracePositive_le_palette c hc y i ⟨b,hb⟩
lemma trace_sample_ae {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (y : ℂ) (i : Fin k) :
    traceValue (sampleCode c hc y 1) i =ᵐ[angularMeasure] sampleFn c y 1 i := by
  rw [traceValue_sampleCode]
  exact sample_ae c hc y 1 i
lemma exact_sample_palette_fixed {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) {y : ℂ}
    (hy : TypicalSampling c y 1) (i : Fin k) :
    ∀ᵐ t ∂angularMeasure, c (y+direction t)=i → t ∈ paletteSet c hc y i := by
  have hp := trace_positive_le_palette c hc (exact_sample_isTrace c hc hy) i
  have hs := trace_sample_ae c hc y i
  apply (hp.and hs).mono
  intro t ht hcolor
  apply ht.1
  rw [ht.2]
  change 0 < if c (y+(1:ℂ)*direction t)=i then (1:ℝ) else 0
  rw [one_mul,ite_eq_left hcolor]
  exact zero_lt_one
lemma typical_sample_palette {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) {y : ℂ}
    (hy : TypicalSampling c y 1) :
    ∀ᵐ t ∂angularMeasure, t ∈ paletteSet c hc y (c (y+direction t)) := by
  exact (ae_all_iff.mpr (exact_sample_palette_fixed c hc hy)).mono
    (fun t ht => ht (c (y+direction t)) rfl)
lemma ae_circle_palette_exclusion {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
    (hw : WeakColoring k c) (x : ℂ) :
    ∀ᵐ t ∂angularMeasure, ∀ᵐ v ∂angularMeasure,
      c (x+direction t+direction v) ∉ palette c hc x t := by
  have hh := Measure.ae_ae_of_ae_prod (ae_all_iff.mpr (fun i => palette_first_exclusion c hc hw x i))
  apply hh.mono
  intro t ht
  apply ht.mono
  intro v hv hmem
  apply hv (c (x+direction t+direction v)) ((mem_palette c hc x t _).mp hmem)
  simp only [angularSum,Complex.ofReal_one,one_mul]
lemma ae_circle_typicalSampling {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (x : ℂ) :
    ∀ᵐ t ∂angularMeasure, TypicalSampling c (x+direction t) 1 := by
  have htyp := Measure.ae_ae_of_ae_prod ((angularSum_quasiMeasurePreserving x (by norm_num : (1:ℝ)≠0)).ae (ae_density_actual c hc))
  apply htyp.mono
  intro t ht
  refine ⟨by norm_num,?_⟩
  simpa only [Typical,angularSum,Complex.ofReal_one,one_mul] using ht
lemma two_complement_pred {α : Type*} [Fintype α] [DecidableEq α] {S : Finset α} {i j a : α}
    (hcomp : Finset.univ\S={i,j}) (hnot : a∉S) (P : α → Prop) (hp : P a) : P i ∨ P j := by
  have ha : a∈({i,j} : Finset α) := by rw [← hcomp]; simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]; exact hnot
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with h|h
  · exact Or.inl (h ▸ hp)
  · exact Or.inr (h ▸ hp)
lemma circle_complement_binary {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
    {x : ℂ} {t : Angles} {S : Finset (Fin k)} {i j : Fin k}
    (hcomp : Finset.univ\S={i,j}) (hsub : S ⊆ palette c hc x t)
    (ht : ∀ᵐ v ∂angularMeasure, c (x+direction t+direction v) ∉ palette c hc x t)
    (hy : TypicalSampling c (x+direction t) 1) : BinaryCenter c hc (x+direction t) i j := by
  apply (ht.and (typical_sample_palette c hc hy)).mono
  intro v hv
  exact two_complement_pred hcomp (fun hq => hv.1 (hsub hq))
    (fun a => v ∈ paletteSet c hc (x+direction t) a) hv.2
lemma palette_triple_null (c : ℂ → Fin 5) (hc : Measurable c) (hw : WeakColoring 5 c)
    (x : ℂ) (S : Finset (Fin 5)) (hS : S.card=3) :
    ∀ᵐ t ∂angularMeasure, ¬ S ⊆ palette c hc x t := by
  have hSc : (Finset.univ\S).card=2 := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]; simp [hS]
  obtain ⟨i,j,_,hcomp⟩ := Finset.card_eq_two.mp hSc
  filter_upwards [ae_circle_palette_exclusion c hc hw x,ae_circle_typicalSampling c hc x,
    ae_not_binary_circle c hc hw x i j] with t ht hy hn
  exact fun hsub => hn (circle_complement_binary c hc hcomp hsub ht hy)
lemma palette_cardinality (c : ℂ → Fin 5) (hc : Measurable c) (hw : WeakColoring 5 c) (x : ℂ) :
    ∀ᵐ t ∂angularMeasure, 1 ≤ (palette c hc x t).card ∧ (palette c hc x t).card ≤ 2 := by
  filter_upwards [palette_nonempty c hc x,ae_all_iff.mpr (fun S : Finset (Fin 5) =>
    ae_all_iff.mpr (fun hS : S.card=3 => palette_triple_null c hc hw x S hS))] with t ht htriple
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ht),?_⟩
  by_contra! hcard
  obtain ⟨S,hsub,hS⟩ := Finset.exists_subset_card_eq (by omega : 3 ≤ (palette c hc x t).card)
  exact htriple S hS hsub
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
open Set
namespace EuclideanFiveColor
lemma four_admissible_group : ∀ p : Finset (Fin 5), FourAdmissible p → fourGroup (fourCanonical p)⊆p := by
  unfold FourAdmissible
  decide
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma four_palette_admissible (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x) :
    ∀ᵐ t∂angularMeasure, FourAdmissible (palette c hc x t) := by
  filter_upwards [palette_nonempty c hc x,palette_cardinality c hc hw x,
    edge_palette_not_pair c hc hw hx.1,edge_palette_not_pair c hc hw hx.2.1,
    edge_palette_not_pair c hc hw hx.2.2.1,edge_palette_not_pair c hc hw hx.2.2.2] with t ht hcard h01 h12 h23 h30
  refine ⟨ht,hcard.2,?_⟩
  intro e
  fin_cases e <;> simp only [fourEdge] <;> assumption
lemma fourState_group_oai (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x) :
    ∀ᵐ t∂angularMeasure, fourGroup (fourState c hc x t)⊆palette c hc x t :=
  (four_palette_admissible c hc hw hx).mono fun _ ht => four_admissible_group _ ht
end EuclideanFiveColor
end

end OAI
end

theorem solution : type_of% @OAI.EuclideanFiveColor.fourState_group_oai := @OAI.EuclideanFiveColor.fourState_group_oai
