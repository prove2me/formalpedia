-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:21:58.56921+00:00
-- url     : https://prove2.me/submissions/47245ec4-f21c-4cb9-8a00-8d3001ecfe6b

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc033
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_current_quantitative
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_exists_closed_lift_hodge_bound
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_hodgeCorrected_energy_identity
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_hodge_regularized_positive_current_cross
import Theorems.Thm_OAI_TamingCompatibility_separating_probability_local_quadratic

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ScalarChartLift
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X]

omit [IsManifold Model ∞ X] [T2Space X] in
lemma vectorLiftSupport_subset (p : X) {f : Space → Space}
    (hf : tsupport f ⊆ (extChartAt Model p).target) :
    vectorLiftSupport p f ⊆ (extChartAt Model p).source := by
  rintro _ ⟨z,hz,rfl⟩
  exact (extChartAt Model p).map_target (hf hz)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma vectorLiftSupport_compact (p : X) {f : Space → Space}
    (hc : HasCompactSupport f) (hf : tsupport f ⊆ (extChartAt Model p).target) :
    IsCompact (vectorLiftSupport p f) :=
  hc.image_of_continuousOn ((continuousOn_extChartAt_symm p).mono hf)

omit [IsManifold Model ∞ X] [T2Space X] in
lemma vectorChartLift_zero_off (p : X) (f : Space → Space)
    {x : X} (hx : x ∉ vectorLiftSupport p f) : vectorChartLift p f x = 0 := by
  unfold vectorChartLift
  split_ifs with hs
  · exact image_eq_zero_of_notMem_tsupport (fun hz => hx ⟨_,hz,(extChartAt Model p).left_inv hs⟩)
  · rfl

lemma vectorChartLift_smooth (p : X) {f : Space → Space}
    (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hf : tsupport f ⊆ (extChartAt Model p).target) :
    ContMDiff Model Model ∞ (vectorChartLift p f) := by
  intro x
  by_cases hk : x ∈ vectorLiftSupport p f
  · have hsrc := vectorLiftSupport_subset p hf hk
    have he : vectorChartLift p f =ᶠ[𝓝 x] fun y => f (extChartAt Model p y) := by
      filter_upwards [(isOpen_extChartAt_source p).mem_nhds hsrc] with y hy
      simp only [vectorChartLift,ite_eq_left hy]
    have hchart := contMDiffAt_extChartAt' (I := Model) (n := ∞)
      (by simpa only [extChartAt_source] using hsrc)
    exact ((contMDiff_iff_contDiff.mpr hs).contMDiffAt.comp x hchart).congr_of_eventuallyEq he
  · have he : vectorChartLift p f =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(vectorLiftSupport_compact p hc hf).isClosed.isOpen_compl.mem_nhds hk] with y hy
      exact vectorChartLift_zero_off p f hy
    exact contMDiffAt_const.congr_of_eventuallyEq he

end TamingCompatibility.ManifoldForms

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RiemannianSmoothLipschitz
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Bundle Manifold Set _root_.MeasureTheory Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

lemma smooth_mfderiv_uniform_bound {f : X → Space} (hf : ContMDiff Model Model ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : X) (v : TangentSpace Model x),
      ‖mfderiv Model Model f x v‖ ≤ C*‖v‖ := by
  have hc : Continuous (fun p : TangentBundle Model X =>
      ‖mfderiv Model Model f p.proj p.2‖) :=
    (((contMDiff_snd_tangentBundle_modelSpace (n := ∞) Space Model).continuous.comp
      (hf.continuous_tangentMap (by simp))).norm)
  obtain ⟨C,hC⟩ := (isCompact_bundle_unitSphere (E := TangentSpace Model)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x v
  by_cases hv : v = 0
  · simp [hv]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by simp [norm_smul,hnv.ne']
  have hb := hC ⟨x,(‖v‖⁻¹ : ℝ) • v⟩ hu
  simp only [ContinuousLinearMap.map_smul,norm_smul,Real.norm_eq_abs,
    abs_inv,abs_of_pos hnv] at hb
  have hb' := (le_abs_self _).trans hb
  have h : ‖mfderiv Model Model f x v‖ ≤ C*‖v‖ := by
    apply (div_le_iff₀ hnv).mp
    simpa only [div_eq_mul_inv,mul_comm] using hb'
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))

omit [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)] in

lemma smooth_edist_le_length {f : X → Space} (hf : ContMDiff Model Model ∞ f)
    {C : ℝ≥0} (hC : ∀ (x : X) (v : TangentSpace Model x),
      ‖mfderiv Model Model f x v‖ ≤ C*‖v‖)
    {γ : ℝ → X} (hγ : ContMDiff 𝓘(ℝ,ℝ) Model 1 γ) :
    edist (f (γ 1)) (f (γ 0)) ≤ C * pathELength Model γ 0 1 := by
  let η := f ∘ γ
  have hη : ContDiff ℝ 1 η := contMDiff_iff_contDiff.mp ((hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp hγ)
  calc
    _ = ‖η 1 - η 0‖ₑ := edist_eq_enorm_sub _ _
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη.contDiffOn zero_le_one
    _ = ∫⁻ t in Icc (0:ℝ) 1, ‖mfderiv 𝓘(ℝ,ℝ) Model η t 1‖ₑ := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      simp only
      rw [← fderivWithin_derivWithin,
        (hη.differentiable (by simp) t).fderivWithin (uniqueDiffOn_Icc zero_lt_one t ht),
        mfderiv_eq_fderiv]
      rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, (C:ℝ≥0∞)*‖mfderiv 𝓘(ℝ,ℝ) Model γ t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t _ht
      have he := mfderiv_comp t (hf.mdifferentiable (by simp) (γ t))
        (hγ.mdifferentiable (by simp) t)
      change ‖mfderiv 𝓘(ℝ,ℝ) Model (f ∘ γ) t 1‖ₑ ≤ _
      rw [he,ContinuousLinearMap.comp_apply]
      have h := ENNReal.ofReal_le_ofReal (hC (γ t) (mfderiv 𝓘(ℝ,ℝ) Model γ t 1))
      simpa only [← ofReal_norm,ENNReal.ofReal_mul C.coe_nonneg,ENNReal.ofReal_coe_nnreal] using h
    _ = C * pathELength Model γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,pathELength]

theorem smooth_lipschitz_riemannian {f : X → Space} (hf : ContMDiff Model Model ∞ f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x y : X,
      edist (f x) (f y) ≤ C * riemannianEDist Model x y := by
  obtain ⟨C,hCp,hC⟩ := smooth_mfderiv_uniform_bound hf
  lift C to ℝ≥0 using hCp.le
  refine ⟨C,hCp,?_⟩
  intro x y
  have hCnp : (C:ℝ≥0∞) ≠ 0 := by exact_mod_cast hCp.ne'
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hεfin
  by_cases hd : riemannianEDist Model x y = ⊤
  · simp [hd,hCnp]
  have hd' : riemannianEDist Model x y < riemannianEDist Model x y + ε/(C:ℝ≥0∞) := by
    exact ENNReal.lt_add_right hd (ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast hε.ne', ENNReal.coe_ne_top⟩)
  obtain ⟨γ,hγx,hγy,hγ,hγlen,_⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hd' zero_lt_one
  have hh := smooth_edist_le_length hf hC hγ
  rw [hγx,hγy,edist_comm] at hh
  calc
    _ ≤ C * pathELength Model γ 0 1 := hh
    _ ≤ C * (riemannianEDist Model x y + ε/(C:ℝ≥0∞)) := by gcongr
    _ = C*riemannianEDist Model x y + ε := by
      rw [mul_add,ENNReal.mul_div_cancel (by exact_mod_cast hCp.ne') ENNReal.coe_ne_top]
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_RiemannianChartControl
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms Set Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]

theorem compact_chart_distance_control (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ L : ℝ≥0, 0 < L ∧ ∀ x y : X,
      x ∈ (extChartAt Model p).source → y ∈ (extChartAt Model p).source →
      extChartAt Model p x ∈ K → extChartAt Model p y ∈ K →
      edist (extChartAt Model p x) (extChartAt Model p y) ≤
        L * Manifold.riemannianEDist Model x y := by
  obtain ⟨φ,hφ,hφT,hφone⟩ := SchwartzCutoff.exists_one_on_compact hK
    (isOpen_extChartAt_target p) hKT
  let f : Space → Space := fun z => φ z • z
  have hfs : ContDiff ℝ ∞ f := (φ.smooth ⊤).smul contDiff_id
  have hfc : HasCompactSupport f := hφ.smul_right
  have hfT : tsupport f ⊆ (extChartAt Model p).target :=
    (tsupport_smul_subset_left φ id).trans hφT
  obtain ⟨L,hL,hbound⟩ := smooth_lipschitz_riemannian
    (vectorChartLift_smooth p hfs hfc hfT)
  refine ⟨L,hL,?_⟩
  intro x y hxs hys hxK hyK
  have he (z : X) (hzs : z ∈ (extChartAt Model p).source)
      (hzK : extChartAt Model p z ∈ K) :
      vectorChartLift p f z = extChartAt Model p z := by
    simp only [vectorChartLift,ite_eq_left hzs,f,hφone _ hzK,one_smul]
  simpa only [he x hxs hxK,he y hys hyK] using hbound x y
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactUniformBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter Topology

theorem IsCompact.exists_uniform_monotone_bound {Y : Type*} [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) (P : Y → ℝ → Prop)
    (hmono : ∀ y a b, a ≤ b → P y a → P y b)
    (hlocal : ∀ q ∈ K, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 q, P y C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, P y C := by
  classical
  have hloc : ∀ q : K, ∃ C : ℝ, ∃ U : Set Y,
      0 ≤ C ∧ IsOpen U ∧ q.val ∈ U ∧ ∀ y ∈ U, P y C := by
    intro q
    obtain ⟨C,hC,hq⟩ := hlocal q.val q.property
    obtain ⟨U,hUP,hU,hqU⟩ := mem_nhds_iff.mp hq
    exact ⟨C,U,hC,hU,hqU,hUP⟩
  choose C U hC hU hqU hUP using hloc
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hqU ⟨y,hy⟩⟩)
  refine ⟨∑ q ∈ s, C q, Finset.sum_nonneg (fun q _ => hC q), ?_⟩
  intro y hy
  obtain ⟨q,hq,hyq⟩ := mem_iUnion₂.mp (hs hy)
  exact hmono y (C q) _ (Finset.single_le_sum (fun r _ => hC r) hq) (hUP q y hyq)

end


end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_GeometricLocalMass
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeInclusion_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth _root_.OAI.TamingCompatibility.GeometricHilbert.l2Star_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility
open Bundle Manifold Set _root_.MeasureTheory Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]

theorem local_chart_mass_to_riemannian {Y : Type*} [MeasurableSpace Y]
    (proj : Y → X) (μ : Measure Y) [IsProbabilityMeasure μ]
    (hloc : ∀ x : X, ∃ p : X, ∃ R C r : ℝ,
      x ∈ (extChartAt Model p).source ∧ 0 < R ∧ 0 ≤ C ∧ 0 < r ∧
      Metric.closedBall (extChartAt Model p x) (4*R) ⊆ (extChartAt Model p).target ∧
      ∀ s ∈ Ioc (0:ℝ) r, ∀ b ∈ Metric.closedBall (extChartAt Model p x) R,
        μ.real {u : Y | proj u ∈ (extChartAt Model p).symm '' Metric.closedBall b s} ≤ C*s^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {u : Y | riemannianEDist Model x (proj u) < ENNReal.ofReal s} ≤ C*s^2 := by
  let : EMetricSpace X := .ofRiemannianMetric Model X
  let P := fun (x : X) (C : ℝ) => ∀ s : ℝ, 0 < s →
    μ.real {u : Y | riemannianEDist Model x (proj u) < ENNReal.ofReal s} ≤ C*s^2
  suffices hlocal : ∀ x ∈ (univ : Set X), ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, P y C by
    obtain ⟨C,hC,hbound⟩ := _root_.OAI.IsCompact.exists_uniform_monotone_bound (isCompact_univ : IsCompact (univ : Set X))
      P (fun _ a b hab ha s hs => (ha s hs).trans
        (mul_le_mul_of_nonneg_right hab (sq_nonneg s))) hlocal
    exact ⟨C,hC,fun x => hbound x (mem_univ x)⟩
  intro x _hx
  obtain ⟨p,R,C,r,hxs,hR,hC,hr,h4,hmass⟩ := hloc x
  let e := extChartAt Model p
  have h2 : Metric.closedBall (e x) (2*R) ⊆ e.target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans h4
  have h1 : Metric.closedBall (e x) R ⊆ e.target :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans h4
  let K := e.symm '' Metric.closedBall (e x) R
  let W := e.source ∩ e ⁻¹' Metric.ball (e x) (2*R)
  let V := e.source ∩ e ⁻¹' Metric.ball (e x) R
  have hK : IsCompact K := inverse_chart_compact_image p (isCompact_closedBall _ _) h1
  have hW : IsOpen W := isOpen_extChartAt_preimage' p Metric.isOpen_ball
  have hV : IsOpen V := isOpen_extChartAt_preimage' p Metric.isOpen_ball
  have hxV : x ∈ V := ⟨hxs,by simpa using hR⟩
  have hKW : K ⊆ W := by
    rintro y ⟨z,hz,rfl⟩
    have hzt := h1 hz
    refine ⟨e.map_target hzt,?_⟩
    change dist (e (e.symm z)) (e x) < 2*R
    rw [e.right_inv hzt]
    exact lt_of_le_of_lt hz (by linarith)
  obtain ⟨δ,hδ,hδW⟩ := hK.exists_thickening_subset_open hW hKW
  obtain ⟨L,hL,hbound⟩ := compact_chart_distance_control p (isCompact_closedBall (e x) (2*R)) h2
  let q : ℝ := min δ (r/L)
  have hLp : (0:ℝ) < L := hL
  have hq : 0 < q := lt_min hδ (div_pos hr hLp)
  have hCL : 0 ≤ C*(L:ℝ)^2 := mul_nonneg hC (sq_nonneg _)
  let D : ℝ := C*(L:ℝ)^2 + 1/q^2
  have hD : 0 ≤ D := add_nonneg hCL (by positivity)
  refine ⟨D,hD,?_⟩
  filter_upwards [hV.mem_nhds hxV] with y hy
  intro s hs
  by_cases hsq : s ≤ q
  · have hsδ : s ≤ δ := hsq.trans (min_le_left _ _)
    have hsLr : (L:ℝ)*s ≤ r := by
      have ht := (le_div_iff₀ hLp).mp (hsq.trans (min_le_right _ _))
      simpa only [mul_comm] using ht
    have hyK : y ∈ K := ⟨e y,Metric.ball_subset_closedBall hy.2,e.left_inv hy.1⟩
    have hy2 : e y ∈ Metric.closedBall (e x) (2*R) :=
      (Metric.closedBall_subset_closedBall (by linarith)) (Metric.ball_subset_closedBall hy.2)
    have hsub : {u : Y | riemannianEDist Model y (proj u) < ENNReal.ofReal s} ⊆
        {u : Y | proj u ∈ e.symm '' Metric.closedBall (e y) ((L:ℝ)*s)} := by
      intro u hu
      have huδ : edist (proj u) y < ENNReal.ofReal δ := by
        rw [edist_comm]
        exact hu.trans_le (ENNReal.ofReal_le_ofReal hsδ)
      have huW : proj u ∈ W := hδW ((Metric.mem_thickening_iff_exists_edist_lt K (proj u)).mpr ⟨y,hyK,huδ⟩)
      have hc := hbound y (proj u) hy.1 huW.1 hy2 (Metric.ball_subset_closedBall huW.2)
      have hcoord : dist (e (proj u)) (e y) ≤ (L:ℝ)*s := by
        apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg L.coe_nonneg hs.le)).mp
        rw [ENNReal.ofReal_mul L.coe_nonneg,ENNReal.ofReal_coe_nnreal,← edist_dist,edist_comm]
        exact hc.trans (by gcongr; exact hu.le)
      exact ⟨e (proj u),hcoord,e.left_inv huW.1⟩
    calc
      _ ≤ μ.real {u : Y | proj u ∈ e.symm '' Metric.closedBall (e y) ((L:ℝ)*s)} := measureReal_mono hsub
      _ ≤ C*((L:ℝ)*s)^2 := hmass _ ⟨mul_pos hLp hs,hsLr⟩ _ (Metric.ball_subset_closedBall hy.2)
      _ = (C*(L:ℝ)^2)*s^2 := by ring
      _ ≤ D*s^2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (sq_nonneg s)
  · have hqs : q ≤ s := le_of_lt (lt_of_not_ge hsq)
    have hpow : q^2 ≤ s^2 := pow_le_pow_left₀ hq.le hqs 2
    have hlarge : 1 ≤ (1/q^2)*s^2 := by
      rw [one_div,inv_mul_eq_div]
      exact (le_div_iff₀ (sq_pos_of_pos hq)).mpr (by simpa using hpow)
    exact measureReal_le_one.trans (hlarge.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCL) (sq_nonneg s)))
end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SmoothingKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertKernel
open _root_.MeasureTheory
open scoped RealInnerProductSpace
variable {H F G A B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

lemma kernel_inner (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G)
    (x : A) (y : B) (a : F) (b : G) :
    ⟪a,kernel E D x y b⟫ = ⟪(E x).adjoint a,(D y).adjoint b⟫ := by
  exact (ContinuousLinearMap.adjoint_inner_left (E x) ((D y).adjoint b) a).symm

lemma regularize_pair [MeasurableSpace A] (μ : Measure A)
    (E : A → H →L[ℝ] F) (v : A → F)
    (hv : Integrable (fun x => (E x).adjoint (v x)) μ) (f : H) :
    ⟪regularize μ E v,f⟫ = ∫ x, ⟪v x,E x f⟫ ∂μ := by
  have h := (innerSL ℝ f).integral_comp_comm hv
  simp only [innerSL_apply_apply] at h
  rw [regularize,real_inner_comm,← h]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [real_inner_comm,ContinuousLinearMap.adjoint_inner_left]

lemma regularize_kernel_pair [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G)
    (v : A → F) (w : B → G)
    (hv : Integrable (fun x => (E x).adjoint (v x)) μ)
    (hw : Integrable (fun y => (D y).adjoint (w y)) ν) :
    ⟪regularize μ E v,regularize ν D w⟫ =
      ∫ x, ∫ y, ⟪v x,kernel E D x y (w y)⟫ ∂ν ∂μ := by
  rw [regularize_pair μ E v hv]
  apply integral_congr_ae
  filter_upwards [] with x
  have h := ((innerSL ℝ (v x)).comp (E x)).integral_comp_comm hw
  simpa only [regularize,ContinuousLinearMap.comp_apply,innerSL_apply_apply,kernel] using h.symm

end TamingCompatibility.HilbertKernel

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_GeometricQuadraticMass
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Bundle Manifold ManifoldForms ManifoldVolume GeometricHilbert Set _root_.MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel

theorem separating_probability_quadratic_growth
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {u : MetricUnit (hermitianMetric J α hs ht) |
        hermitianEDist J α hs ht x u.val.proj < ENNReal.ofReal s} ≤ C*s^2 := by
  let g := hermitianMetric J α hs ht
  let : RiemannianBundle (TangentSpace Model : X → Type) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type) :=
    ⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩
  apply local_chart_mass_to_riemannian (fun u : MetricUnit g => u.val.proj) μ
  intro x
  obtain ⟨p,R,C,r,hx,hR,hC,hr,_hrR,h4,hm⟩ := separating_probability_local_quadratic J α hs ht μ hann x
  exact ⟨p,R,C,r,hx,hR,hC,hr,h4,hm⟩
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_QuadraticShell
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace QuadraticShell

lemma exists_dyadic_majorant {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    ∃ n : ℕ, d < 2^(n+1)*r ∧ (1+d/r)⁻¹^6 ≤ (1/64:ℝ)^n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near (le_max_left 1 (d/r)) (by norm_num : (1:ℝ)<2)
  have hbase : (2:ℝ)^n ≤ 1+d/r := hn.trans (max_le (le_add_of_nonneg_right (div_nonneg hd hr.le)) (by linarith))
  refine ⟨n,(div_lt_iff₀ hr).mp ((le_max_right 1 (d/r)).trans_lt hn'),?_⟩
  calc
    (1+d/r)⁻¹^6 ≤ ((2:ℝ)^n)⁻¹^6 := by
      gcongr
    _ = (1/64:ℝ)^n := by
      rw [← inv_pow,← pow_mul,Nat.mul_comm,pow_mul,inv_pow]
      norm_num

lemma profile_ofReal {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d) :
    profile r (ENNReal.ofReal d) = ENNReal.ofReal ((1+d/r)⁻¹^6) := by
  simp only [profile, ← ENNReal.ofReal_div_of_pos hr, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (div_nonneg hd hr.le)]
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_pow (by positivity)]

lemma profile_top {r : ℝ} : profile r ⊤ = 0 := by
  simp [profile, ENNReal.top_div]

lemma profile_majorant {r : ℝ} (hr : 0 < r) (d : ℝ≥0∞) :
    profile r d ≤ ∑' n : ℕ,
      {e : ℝ≥0∞ | e < ENNReal.ofReal (2^(n+1)*r)}.indicator
        (fun _ => ENNReal.ofReal ((1/64:ℝ)^n)) d := by
  by_cases hd : d = ⊤
  · rw [hd,profile_top]; exact bot_le
  obtain ⟨n,hn,hbound⟩ := exists_dyadic_majorant hr d.toReal_nonneg
  have hdreal : ENNReal.ofReal d.toReal = d := ENNReal.ofReal_toReal hd
  have hn' : d < ENNReal.ofReal (2^(n+1)*r) := by
    rw [←hdreal]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hn
  calc
    _ = ENNReal.ofReal ((1+d.toReal/r)⁻¹^6) := by rw [←hdreal,profile_ofReal hr d.toReal_nonneg]; simp [hdreal]
    _ ≤ ENNReal.ofReal ((1/64:ℝ)^n) := ENNReal.ofReal_le_ofReal hbound
    _ = _ := by simp only [indicator, mem_ofPred_eq, hn', ↓reduceIte]
    _ ≤ _ := ENNReal.le_tsum n

lemma dyadic_term_identity (C r : ℝ) (n : ℕ) :
    (1/64:ℝ)^n*(C*(2^(n+1)*r)^2) = 4*C*r^2*(1/16:ℝ)^n := by
  have hpow : ((2:ℝ)^n)^2 = ((2:ℝ)^2)^n := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  calc
    _ = 4*C*r^2*((1/64:ℝ)^n*((2:ℝ)^2)^n) := by rw [pow_succ,←hpow]; ring
    _ = _ := by rw [←mul_pow]; norm_num

theorem lintegral_profile_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ y, profile r (δ y) ∂μ ≤ ENNReal.ofReal (8*C*r^2) := by
  let f : ℕ → Y → ℝ≥0∞ := fun n =>
    {y | δ y < ENNReal.ofReal (2^(n+1)*r)}.indicator
      (fun _ => ENNReal.ofReal ((1/64:ℝ)^n))
  have hf : ∀ n, Measurable (f n) := fun n =>
    measurable_const.indicator (measurableSet_lt hδ measurable_const)
  have hi (n : ℕ) : ∫⁻ y, f n y ∂μ ≤ ENNReal.ofReal (4*C*r^2*(1/16:ℝ)^n) := by
    rw [lintegral_indicator_const (measurableSet_lt hδ measurable_const)]
    have hm : μ {y | δ y < ENNReal.ofReal (2^(n+1)*r)} ≤
        ENNReal.ofReal (C*(2^(n+1)*r)^2) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal (hgrowth _ (by positivity))
    calc
      _ ≤ ENNReal.ofReal ((1/64:ℝ)^n) * ENNReal.ofReal (C*(2^(n+1)*r)^2) :=
        by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), dyadic_term_identity]
  calc
    _ ≤ ∫⁻ y, ∑' n, f n y ∂μ := lintegral_mono fun y => profile_majorant hr (δ y)
    _ = ∑' n, ∫⁻ y, f n y ∂μ := lintegral_tsum fun n => (hf n).aemeasurable
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (4*C*r^2*(1/16:ℝ)^n) := ENNReal.tsum_le_tsum hi
    _ = ENNReal.ofReal (4*C*r^2) * (1-ENNReal.ofReal (1/16))⁻¹ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4*C*r^2), ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/16)]
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (8*C*r^2) := by
      have hratio : (1-ENNReal.ofReal (1/16))⁻¹ ≤ ENNReal.ofReal 2 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/16)]
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 1-1/16)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      calc
        _ ≤ ENNReal.ofReal (4*C*r^2)*ENNReal.ofReal 2 := by gcongr
        _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end QuadraticShell

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_QuadraticShellLimit
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace QuadraticShell

lemma profile_le_one (r : ℝ) (d : ℝ≥0∞) : profile r d ≤ 1 := by
  apply pow_le_one₀ bot_le
  exact ENNReal.inv_le_one.mpr le_self_add

lemma measurable_profile {Y : Type*} [MeasurableSpace Y]
    (δ : Y → ℝ≥0∞) (hδ : Measurable δ) (r : ℝ) :
    Measurable (fun y => profile r (δ y)) := by
  unfold profile
  fun_prop

lemma integral_profile_toReal {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (δ : Y → ℝ≥0∞) (hδ : Measurable δ) (r : ℝ) :
    (∫ y, (profile r (δ y)).toReal ∂μ) = (∫⁻ y, profile r (δ y) ∂μ).toReal := by
  exact integral_toReal (measurable_profile δ hδ r).aemeasurable
    (Eventually.of_forall fun y => (profile_le_one r (δ y)).trans_lt (by simp))

lemma integral_profile_normalized_bound {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (δ : Y → ℝ≥0∞) (hδ : Measurable δ)
    (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℝ, 0 < s → μ.real {y | δ y < ENNReal.ofReal s} ≤ C*s^2)
    {r : ℝ} (hr : 0 < r) : (∫ y, (profile r (δ y)).toReal ∂μ)/r^2 ≤ 8*C := by
  rw [integral_profile_toReal μ δ hδ r]
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (lintegral_profile_le μ δ hδ C hC hgrowth hr)
  rw [ENNReal.toReal_ofReal (by positivity)] at hle
  exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr hle

end QuadraticShell

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization
open Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma evaluationVector_continuous : Continuous (C.evaluationVector g) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.evaluation_continuous g)).clm_apply continuous_const

lemma evaluationVector_integrable (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] :
    Integrable (C.evaluationVector g) μ :=
  (C.evaluationVector_continuous g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma regularize_inner (μ ν : Measure (MetricUnit g)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⟪C.regularize g μ,C.regularize g ν⟫ =
      ∫ u, ∫ v, C.innerKernel g u v ∂ν ∂μ := by
  have h := HilbertKernel.regularize_kernel_pair μ ν (C.evaluation g) (C.evaluation g)
    (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
    (C.evaluationVector_integrable g μ) (C.evaluationVector_integrable g ν)
  simpa only [regularize,HilbertKernel.regularize,innerKernel,evaluationVector,
    HilbertKernel.kernel_inner] using h

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization _root_.MeasureTheory Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

variable [T2Space X]
variable {A J α hs ht D hD}
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)
variable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma heatEvaluation_continuous : Continuous (C.heatEvaluation g) :=
  (C.evaluation_continuous g).clm_comp continuous_const

lemma heatEvaluationVector_continuous : Continuous (C.heatEvaluationVector g) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := L2 A J α hs ht true) (F := ℝ)).continuous.comp
    (C.heatEvaluation_continuous g)).clm_apply continuous_const

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_ResolventTaylor
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace ResolventTaylor
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
open scoped BigOperators

lemma cube_second (L : E →ₗ[ℝ] E) (t : ℝ) (a : E) :
    (((LinearMap.id : E →ₗ[ℝ] E)+t • L)^3) (second L t a) =
      a+(10*t^3) • ((L^3) a)+(15*t^4) • ((L^4) a)+(6*t^5) • ((L^5) a) := by
  simp only [second,pow_succ,Module.End.mul_apply,LinearMap.add_apply,
    LinearMap.id_apply,LinearMap.smul_apply,map_add,map_sub,map_smul,pow_zero,
    Module.End.one_apply]
  module
end ResolventTaylor

end
end

section
noncomputable section
namespace ResolventTaylor
open Filter Set
open scoped Topology RealInnerProductSpace
variable {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma scaled_inner_tendsto (U : ℝ → H) (K : ℝ)
    (hb : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖U r‖ ≤ K*(r⁻¹)^3)
    (b : H) (n : ℕ) :
    Tendsto (fun r : ℝ => r^(n+4)*⟪U r,b⟫) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ => K*‖b‖*r^(n+1)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0)).pow (n+1)).const_mul (K*‖b‖)
  apply squeeze_zero_norm' _ ht
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with r hr hr1
  have hp : 0 < r := hr
  calc
    ‖r^(n+4)*⟪U r,b⟫‖ = r^(n+4)*|⟪U r,b⟫| := by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (pow_pos hp _)]
    _ ≤ r^(n+4)*(‖U r‖*‖b‖) := mul_le_mul_of_nonneg_left
      (abs_real_inner_le_norm _ _) (pow_nonneg hp.le _)
    _ ≤ r^(n+4)*((K*(r⁻¹)^3)*‖b‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hb r hp hr1.le) (norm_nonneg _)) (pow_nonneg hp.le _)
    _ = K*‖b‖*r^(n+1) := by
      simp only [pow_add]
      field_simp

lemma cube_distribution_tendsto (L : E →ₗ[ℝ] E) (i : E →ₗ[ℝ] H)
    (F : E →ₗ[ℝ] ℝ) (U : ℝ → H) (K : ℝ)
    (hb : ∀ r : ℝ, 0 < r → r ≤ 1 → ‖U r‖ ≤ K*(r⁻¹)^3)
    (he : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ a : E,
      ⟪U r,i ((((LinearMap.id : E →ₗ[ℝ] E)+r^2 • L)^3) a)⟫ = F a)
    (a : E) : Tendsto (fun r : ℝ => ⟪U r,i a⟫) (𝓝[>] 0) (𝓝 (F a)) := by
  have h3 := (scaled_inner_tendsto U K hb (i ((L^3) a)) 2).const_mul 10
  have h4 := (scaled_inner_tendsto U K hb (i ((L^4) a)) 4).const_mul 15
  have h5 := (scaled_inner_tendsto U K hb (i ((L^5) a)) 6).const_mul 6
  have ht : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 := (ht.pow 2).const_mul (3*F (L a))
  have h2 := (ht.pow 4).const_mul (6*F ((L^2) a))
  have hlim := ((((tendsto_const_nhds (x:=F a)).sub h1).add h2).sub h3).sub h4 |>.sub h5
  simp only [zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 4 ≠ 0),
    mul_zero,sub_zero,add_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with r hr hr1
  have hx := he r hr hr1.le (second L (r^2) a)
  rw [cube_second] at hx
  simp only [second,map_add,map_sub,map_smul,inner_add_right,real_inner_smul_right] at hx
  norm_num only [← pow_mul,smul_eq_mul] at hx
  norm_num only
  nlinarith [hx]
end ResolventTaylor

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSmoothInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeSmoothInverse_left (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    hodgeSmoothInverse A J α hs ht D hD r hr ((hodgeSmoothShift A J α hs ht r ^ 3) a) = a :=
  (LinearEquiv.ofBijective _ (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr)).symm_apply_apply a
lemma hodgeSmoothInverse_right (r : ℝ) (hr : 0 < r) (a : PreL2 A J α hs ht true) :
    (hodgeSmoothShift A J α hs ht r ^ 3) (hodgeSmoothInverse A J α hs ht D hD r hr a) = a :=
  (LinearEquiv.ofBijective _ (hodgeSmoothShift_cube_bijective A J α hs ht D hD r hr)).apply_symm_apply a

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeDistributionInverse_bound (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ a, ‖F a‖ ≤ K*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖) :
    ‖hodgeDistributionInverse A J α hs ht D hD r hr F‖ ≤ K := by
  rw [hodgeDistributionInverse,(InnerProductSpace.toDual ℝ (L2 A J α hs ht true)).symm.norm_map]
  apply LinearMap.opNorm_extendOfNorm_le (smoothL2_dense A J α hs ht true) hK
  intro b
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,hodgeSmoothInverse_right,
    LinearIsometry.coe_toLinearMap] using hF (hodgeSmoothInverse A J α hs ht D hD r hr b)

lemma hodgeDistributionInverse_represents (r : ℝ) (hr : 0 < r)
    (F : PreL2 A J α hs ht true →ₗ[ℝ] ℝ) (K : ℝ)
    (hF : ∀ a, ‖F a‖ ≤ K*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖) :
    hodgeCubeRepresents A J α hs ht r F
      (hodgeDistributionInverse A J α hs ht D hD r hr F) := by
  intro a
  rw [hodgeDistributionInverse,InnerProductSpace.toDual_symm_apply]
  have hb : ∃ K : ℝ, ∀ b : PreL2 A J α hs ht true,
      ‖(F.comp (hodgeSmoothInverse A J α hs ht D hD r hr).toLinearMap) b‖ ≤
        K*‖smoothL2 A J α hs ht true b‖ := by
    exact ⟨K,fun b => by simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,
      hodgeSmoothInverse_right] using hF (hodgeSmoothInverse A J α hs ht D hD r hr b)⟩
  have he := LinearMap.extendOfNorm_eq (smoothL2_dense A J α hs ht true) hb
    ((hodgeSmoothShift A J α hs ht r^3) a)
  simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,hodgeSmoothInverse_left,
    LinearIsometry.coe_toLinearMap] using he

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricHilbert
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel 

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitMeasureCurrent_finite_bound
    (J : AlmostComplexStructure X)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (β : smoothForms X 2) :
    ‖unitMeasureCurrent J g μ β‖ ≤ μ.real univ * ‖smoothUnitEvaluation J g β‖ := by
  change ‖∫ p, smoothUnitEvaluation J g β p ∂μ‖ ≤ _
  exact (norm_integral_le_of_norm_le_const (μ := μ) (f := smoothUnitEvaluation J g β)
    (C := ‖smoothUnitEvaluation J g β‖)
    (Filter.Eventually.of_forall (fun p => (smoothUnitEvaluation J g β).norm_coe_le_norm p))).trans_eq
      (mul_comm _ _)

namespace GeometricHilbert
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeCorrectionSource_anti
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ] (a : PreL2 A J α hs ht true) :
    hodgeCorrectionSource A J α hs ht B g μ (preAntiProjection A J α hs ht a) =
      hodgeCorrectionSource A J α hs ht B g μ a := by
  have he : smoothAntiProjection A J α hs ht (preAntiProjection A J α hs ht a) =
      smoothAntiProjection A J α hs ht a := by
    apply Subtype.ext
    apply Subtype.ext
    exact antiInvariantPart_idempotent J a.val
  change -(unitMeasureCurrent J g μ (B _)) = -(unitMeasureCurrent J g μ (B _))
  rw [he]

lemma hodgeCorrectionSource_bound
    (B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2)
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
    (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ]
    (r C : ℝ)
    (hB : ∀ a : PreL2 A J α hs ht true,
      ‖smoothUnitEvaluation J g (B (smoothAntiProjection A J α hs ht a))‖ ≤
        C*(r⁻¹)^3*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖)
    (a : PreL2 A J α hs ht true) :
    ‖hodgeCorrectionSource A J α hs ht B g μ a‖ ≤
      (μ.real univ*C*(r⁻¹)^3)*‖smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r^3) a)‖ := by
  change ‖-(unitMeasureCurrent J g μ (B (smoothAntiProjection A J α hs ht a)))‖ ≤ _
  rw [norm_neg]
  exact ((unitMeasureCurrent_finite_bound J g μ _).trans
    (mul_le_mul_of_nonneg_left (hB a) (measureReal_nonneg))).trans_eq (by ring)
end GeometricHilbert
end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCorrectionRegularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel

theorem exists_regularizable_closed_lift
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    ∃ B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2,
      (∀ f, IsClosed (B f).val) ∧
      (∀ f, antiInvariantPart J (B f).val = f.val.val) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ],
        ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
          hodgeCubeRepresents A J α hs ht r (hodgeCorrectionSource A J α hs ht B g μ)
            (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr) ∧
          ‖hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr‖ ≤ μ.real univ*C*(r⁻¹)^3 := by
  obtain ⟨B,hBc,hBR,C,hC,hB⟩ := exists_closed_lift_hodge_bound A J α hs ht D hD g
  refine ⟨B,hBc,hBR,C,hC,fun μ _ r hr hr1 => ?_⟩
  have hb := hodgeCorrectionSource_bound A J α hs ht B g μ r C (hB r hr hr1)
  exact ⟨hodgeDistributionInverse_represents A J α hs ht D hD r hr _ _ hb,
    hodgeDistributionInverse_bound A J α hs ht D hD r hr _ _ (by positivity) hb⟩

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCorrectionLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Filter
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel

theorem exists_convergent_closed_lift
    (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    ∃ B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2,
      (∀ f, IsClosed (B f).val) ∧
      (∀ f, antiInvariantPart J (B f).val = f.val.val) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Measure (MetricUnit g)) [IsFiniteMeasure μ],
        (∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
          hodgeCubeRepresents A J α hs ht r (hodgeCorrectionSource A J α hs ht B g μ)
            (hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr) ∧
          ‖hodgeCorrectionRegularize A J α hs ht D hD B g μ r hr‖ ≤ μ.real univ*C*(r⁻¹)^3) ∧
        ∀ a : PreL2 A J α hs ht true,
          Tendsto (fun r : ℝ => ⟪hodgeCorrectionFamily A J α hs ht D hD B g μ r,
            smoothL2 A J α hs ht true a⟫) (𝓝[>] 0) (𝓝 (hodgeCorrectionSource A J α hs ht B g μ a)) := by
  obtain ⟨B,hBc,hBR,C,hC,hB⟩ := exists_regularizable_closed_lift A J α hs ht D hD g
  refine ⟨B,hBc,hBR,C,hC,fun μ _ => ⟨hB μ,fun a => ?_⟩⟩
  apply ResolventTaylor.cube_distribution_tendsto (hodgeLaplacian A J α hs ht)
    (smoothL2 A J α hs ht true).toLinearMap
    (hodgeCorrectionSource A J α hs ht B g μ)
    (hodgeCorrectionFamily A J α hs ht D hD B g μ) (μ.real univ*C)
  · intro r hr hr1
    simpa only [hodgeCorrectionFamily,dite_eq_left hr] using (hB μ r hr hr1).2
  · intro r hr hr1 b
    simpa only [hodgeCorrectionFamily,dite_eq_left hr,hodgeSmoothShift,LinearIsometry.coe_toLinearMap] using
      (hB μ r hr hr1).1 b
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeKernelGammaBounds
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.HodgeKernelBounds
open _root_.MeasureTheory Set

lemma moment_integrable (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => s^n * Real.exp (-(b*s))) (Ioi 0) := by
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hb)

lemma moment_integral (n : ℕ) {b : ℝ} (hb : 0 < b) :
    (∫ s : ℝ in Ioi 0, s^n * Real.exp (-(b*s))) = moment n b := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1)
    (by positivity) hb
  simp_rw [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  have he : (n:ℝ)+1 = ((n+1:ℕ):ℝ) := by push_cast; rfl
  rw [he, Real.rpow_natCast] at h
  exact h

lemma moment_pos (n : ℕ) {b : ℝ} (hb : 0 < b) : 0 < moment n b := by
  unfold moment
  positivity

lemma gammaTail_le {T : ℝ} (hT : 0 ≤ T) :
    gammaTail T ≤ moment 5 (1/2) * Real.exp (-(T/2)) := by
  have hi := (moment_integrable 5 (by norm_num : (0:ℝ)<1)).mono_set
    (show Ioi T ⊆ Ioi (0:ℝ) from fun _ hs => hT.trans_lt hs)
  have hj := (moment_integrable 5 (by norm_num : (0:ℝ)<1/2)).mono_set
    (show Ioi T ⊆ Ioi (0:ℝ) from fun _ hs => hT.trans_lt hs)
  calc
    gammaTail T ≤ ∫ s : ℝ in Ioi T, (s^5 * Real.exp (-((1/2)*s))) * Real.exp (-(T/2)) := by
      apply integral_mono_ae (by simpa only [IntegrableOn, mul_comm, one_mul, mul_one] using hi)
        (hj.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have he : Real.exp (-s) ≤ Real.exp (-((1/2)*s)) * Real.exp (-(T/2)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [show T < s from hs])
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right he (pow_nonneg (hT.trans hs.le) 5)
    _ ≤ ∫ s : ℝ in Ioi 0, (s^5 * Real.exp (-((1/2)*s))) * Real.exp (-(T/2)) := by
      apply setIntegral_mono_set ((moment_integrable 5 (by norm_num : (0:ℝ)<1/2)).mul_const _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        positivity
      · exact Filter.Eventually.of_forall (fun _ hs => hT.trans_lt hs)
    _ = moment 5 (1/2) * Real.exp (-(T/2)) := by
      rw [integral_mul_const, moment_integral 5 (by norm_num : (0:ℝ)<1/2)]

lemma exp_neg_le_power {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Real.exp (-a) ≤ (n.factorial : ℝ) / a^n := by
  apply (le_div_iff₀ (pow_pos ha n)).mpr
  have h := (div_le_iff₀ (show 0 < (n.factorial : ℝ) by positivity)).mp
    (Real.pow_div_factorial_le_exp a ha.le n)
  calc
    Real.exp (-a) * a^n ≤ Real.exp (-a) * ((n.factorial : ℝ)*Real.exp a) :=
      mul_le_mul_of_nonneg_left (by simpa only [mul_comm] using h) (Real.exp_pos _).le
    _ = (n.factorial : ℝ) := by rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

lemma gammaTail_small_scale (M : ℕ) {t₀ r : ℝ} (ht₀ : 0 < t₀) (hr : 0 < r) :
    gammaTail (t₀/r^2) ≤
      (moment 5 (1/2) * (M.factorial : ℝ) * (2/t₀)^M) * r^(2*M) := by
  have h := (gammaTail_le (div_nonneg ht₀.le (sq_nonneg r))).trans
    (mul_le_mul_of_nonneg_left
      (exp_neg_le_power (show 0 < t₀/r^2/2 by positivity) M)
      (moment_pos 5 (by norm_num : (0:ℝ)<1/2)).le)
  calc
    _ ≤ moment 5 (1/2) * ((M.factorial : ℝ) / (t₀/r^2/2)^M) := h
    _ = _ := by
      rw [div_pow, div_pow, pow_mul, div_pow]
      field_simp

end TamingCompatibility.GeometricHilbert.HodgeKernelBounds

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGeometricDistance
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle Manifold ManifoldForms Set _root_.MeasureTheory
open scoped Bundle Manifold ContDiff ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X]

lemma geometric_edist_eq (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) (x y : X) :
    let := geometricMetricSpace J α hs ht
    edist x y = hermitianEDist J α hs ht x y := rfl

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairingIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

variable [T2Space X]
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {ρ : ℝ} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma gammaTailKernel_bound (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (u v : MetricUnit g) :
    |C.gammaTailKernel g T hT r u v| ≤
      (1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2)*
        ‖C.heatEvaluationVector g u‖*‖C.heatEvaluationVector g v‖ := by
  apply (abs_real_inner_le_norm _ _).trans
  have hh := mul_le_mul_of_nonneg_left
    (hodgeGammaShiftLinear_bound A J α hs ht D hD T hT r (2*ρ^2) (C.heatEvaluationVector g v))
    (norm_nonneg (C.heatEvaluationVector g u))
  exact hh.trans_eq (by ring)

lemma gammaTailKernel_uniform (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, ∀ u v : MetricUnit g,
      |C.gammaTailKernel g T hT r u v| ≤ (1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2)*B^2 := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (C.heatEvaluationVector_continuous g).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hb (u : MetricUnit g) : ‖C.heatEvaluationVector g u‖ ≤ M := (hB u (mem_univ _)).trans (le_max_left _ _)
  refine ⟨M,hM,fun r u v => (C.gammaTailKernel_bound g T hT r u v).trans ?_⟩
  have htail : 0 ≤ HodgeKernelBounds.gammaTail (T/r^2) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg ((div_nonneg hT (sq_nonneg r)).trans_lt hsp).le _)
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul (hb u) (hb v) (norm_nonneg _) hM)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/120) htail)
  simpa only [sq,mul_assoc] using hh

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaTailPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

variable [T2Space X]
attribute [local instance] unitMeasurable unitBorel 
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {ρ : ℝ} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma gammaTailKernel_rapid {T : ℝ} (hT : 0 < T) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
      |C.gammaTailKernel g T hT.le r u v| ≤ B*r^(2*N) := by
  obtain ⟨M,hM,hb⟩ := C.gammaTailKernel_uniform g T hT.le
  let B := ((1/120 : ℝ)*HodgeKernelBounds.moment 5 (1/2)*(N.factorial : ℝ)*(2/T)^N)*M^2
  have hB : 0 ≤ B := by
    have hm := (HodgeKernelBounds.moment_pos 5 (by norm_num : (0:ℝ)<1/2)).le
    dsimp [B]
    positivity
  refine ⟨B,hB,fun r hr u v => (hb r u v).trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (HodgeKernelBounds.gammaTail_small_scale N hT hr)
      (by norm_num : (0:ℝ)≤1/120)) (sq_nonneg M)
  exact hh.trans_eq (by dsimp [B] <;> ring)

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

include hE D hD in
lemma same_resolvent_current_point_bound :
    let := geometricMetricSpace J α hs ht
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (r : ℝ) (hr : 0 < r) (S : HodgeSmoothingCover A J α hs ht D hD r hr),
        ∀ u v : MetricUnit g,
        |S.innerKernel g u v| ≤
          (C/r^4+C/r^2)*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 + B := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,C,hT,hC,_,hbound,hker⟩ :=
    same_resolvent_current_quantitative A J α hs ht E hE D hD g 6
  let ρ := Real.sqrt T/2
  have hρ : 0 < ρ := div_pos (Real.sqrt_pos.mpr hT) (by norm_num)
  have hρT : 2*ρ^2 ≤ T := by
    have hsqrt := Real.sq_sqrt hT.le
    dsimp [ρ]
    nlinarith
  let R := hodgeSmoothingCover A J α hs ht D hD ρ hρ
  obtain ⟨B,hB,hBR⟩ := R.gammaTailKernel_rapid g hT 0
  refine ⟨C,B,hC,hB,fun r hr S u v => ?_⟩
  have hb := hbound r hr u v
  have ha : 0 < 1+dist u.val.proj v.val.proj/r := by positivity
  have hw : VolterraBounds.weight 6 (r^2) u.val.proj v.val.proj =
      (1+dist u.val.proj v.val.proj/r)^6 := by
    simp only [VolterraBounds.weight,Real.sqrt_sq_eq_abs,abs_of_pos hr]
  rw [hw] at hb
  have hdiv (x c : ℝ) (h : (1+dist u.val.proj v.val.proj/r)^6 * |x| ≤ c) :
      |x| ≤ c*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 := by
    rw [inv_pow,← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos ha _)).mpr (by simpa only [mul_comm] using h)
  have htbound : |R.gammaTailKernel g T hT.le r u v| ≤ B := by
    simpa using hBR r hr u v
  rw [hker r hr S ρ hρ R hρT u v]
  calc
    _ ≤ |unitCurrentKernel A J α ht E g
          (HodgeKernelBounds.gammaKernel (globalLeading J α ht A E) T r) u v| +
        |unitCurrentKernel A J α ht E g
          (HodgeKernelBounds.gammaKernel (globalError J α ht A E T) T r) u v| +
        |R.gammaTailKernel g T hT.le r u v| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ C/r^4*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 +
        C/r^2*((1+dist u.val.proj v.val.proj/r)⁻¹)^6 + B :=
      add_le_add (add_le_add (hdiv _ _ hb.1) (hdiv _ _ hb.2)) htbound
    _ = _ := by ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeMassBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local instance] unitMeasurable unitBorel 

include hE D hD in
lemma same_resolvent_current_mass_bound :
    let := geometricMetricSpace J α hs ht
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
      ∀ (μ : Measure (MetricUnit g)) [IsProbabilityMeasure μ], ∀ M : ℝ, 0 ≤ M →
      (∀ x : X, ∀ s : ℝ, 0 < s →
        μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2) →
      ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
        ‖S.regularize g μ‖^2 ≤ (C*M+B)/r^2 := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_current_point_bound A J α hs ht E hE D hD g
  refine ⟨16*C,B,mul_nonneg (by norm_num) hC,hB,?_⟩
  intro μ _ M hM hgrowth r hr hr1 S
  have hb : Continuous (fun v : MetricUnit g => v.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  let P : X → MetricUnit g → ℝ := fun x v => ((1+dist x v.val.proj/r)⁻¹)^6
  have hm (x : X) : Measurable (fun v : MetricUnit g => ENNReal.ofReal (dist x v.val.proj)) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.dist hb)).measurable
  have hp (x : X) : Continuous (P x) := by
    apply Continuous.pow
    apply Continuous.inv₀
    · exact continuous_const.add ((continuous_const.dist hb).div_const r)
    · intro v
      have h : 0 < 1+dist x v.val.proj/r := by positivity
      exact h.ne'
  have hi (x : X) : Integrable (P x) μ :=
    (hp x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint (x : X) : (∫ v, P x v ∂μ) ≤ 8*M*r^2 := by
    have hh := QuadraticShell.integral_profile_normalized_bound μ
      (fun v : MetricUnit g => ENNReal.ofReal (dist x v.val.proj)) (hm x) M hM (hgrowth x) hr
    have he (v : MetricUnit g) :
        (QuadraticShell.profile r (ENNReal.ofReal (dist x v.val.proj))).toReal = P x v := by
      rw [QuadraticShell.profile_ofReal hr dist_nonneg,ENNReal.toReal_ofReal (by positivity)]
    simp_rw [he] at hh
    exact (div_le_iff₀ (sq_pos_of_pos hr)).mp hh
  have hcoef : 0 ≤ C/r^4+C/r^2 := by positivity
  have hinner (u : MetricUnit g) : ‖∫ v, S.innerKernel g u v ∂μ‖ ≤ (16*C*M+B)/r^2 := by
    calc
      _ ≤ ∫ v, |S.innerKernel g u v| ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ v, (C/r^4+C/r^2)*P u.val.proj v+B ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall (fun _ => abs_nonneg _))
          (((hi u.val.proj).const_mul _).add (integrable_const _))
          (Eventually.of_forall (hbound r hr S u))
      _ = (C/r^4+C/r^2)*(∫ v, P u.val.proj v ∂μ)+B := by
        rw [integral_add ((hi u.val.proj).const_mul _) (integrable_const _),
          integral_const_mul,integral_const,probReal_univ,one_smul]
      _ ≤ (C/r^4+C/r^2)*(8*M*r^2)+B :=
        add_le_add (mul_le_mul_of_nonneg_left (hint u.val.proj) hcoef) le_rfl
      _ = (8*C*M+8*C*M*r^2+B*r^2)/r^2 := by
        field_simp
      _ ≤ (16*C*M+B)/r^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg r)
        have hr2 : r^2 ≤ 1 := pow_le_one₀ hr.le hr1
        have h1 := mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ 8*C*M)
        have h2 := mul_le_mul_of_nonneg_left hr2 hB
        nlinarith
  have hout := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hinner)
  rw [probReal_univ,mul_one,← S.regularize_inner g μ μ,real_inner_self_eq_norm_sq,
    Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at hout
  exact hout

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))
attribute [local instance] unitMeasurable unitBorel 

include hE D hD in
lemma same_resolvent_current_mass_cross :
    let := geometricMetricSpace J α hs ht
    ∀ (μ : Measure (MetricUnit g)) [IsProbabilityMeasure μ], ∀ M : ℝ, 0 ≤ M →
      (∀ x : X, ∀ s : ℝ, 0 < s →
        μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
      ∀ V : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪V,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
            (a-preAntiProjection A J α hs ht a))⟫ = 0) →
        |⟪S.regularize g μ,V⟫| ≤ K*‖V‖ := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  intro μ _ M hM hgrowth
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_current_mass_bound A J α hs ht E hE D hD g
  obtain ⟨L,hL,hcross⟩ := hodge_regularized_positive_current_cross A J α hs ht D hD
  have hCB : 0 ≤ C*M+B := add_nonneg (mul_nonneg hC hM) hB
  refine ⟨L*Real.sqrt (C*M+B),mul_nonneg hL (Real.sqrt_nonneg _),?_⟩
  intro r hr hr1 S V hV
  have hm := hbound μ M hM hgrowth r hr hr1 S
  have hm' : (r*‖S.regularize g μ‖)^2 ≤ C*M+B := by
    have hh := (le_div_iff₀ (sq_pos_of_pos hr)).mp hm
    nlinarith
  have hsqrt : r*‖S.regularize g μ‖ ≤ Real.sqrt (C*M+B) := by
    have hh := Real.sq_sqrt hCB
    have hp := Real.sqrt_nonneg (C*M+B)
    nlinarith [norm_nonneg (S.regularize g μ)]
  calc
    _ ≤ L*r*‖S.regularize g μ‖*‖V‖ := hcross r hr hr1 S g μ V hV
    _ = L*(r*‖S.regularize g μ‖)*‖V‖ := by ring
    _ ≤ (L*Real.sqrt (C*M+B))*‖V‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hL) (norm_nonneg V)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeSeparatingMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

include hE D hD in
lemma separating_current_mass_and_cross
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
      ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
        ‖S.regularize (hermitianMetric J α hs ht) μ‖^2 ≤ C/r^2 ∧
        ∀ V : L2 A J α hs ht true,
          (∀ a : PreL2 A J α hs ht true,
            ⟪V,smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3)
              (a-preAntiProjection A J α hs ht a))⟫ = 0) →
          |⟪S.regularize (hermitianMetric J α hs ht) μ,V⟫| ≤ K*‖V‖ := by
  let := geometricMetricSpace J α hs ht
  obtain ⟨M,hM,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  have hg : ∀ x : X, ∀ s : ℝ, 0 < s →
      μ.real {v | ENNReal.ofReal (dist x v.val.proj) < ENNReal.ofReal s} ≤ M*s^2 := by
    intro x s hs'
    simpa only [← edist_dist,geometric_edist_eq J α hs ht] using hgrowth x s hs'
  obtain ⟨C,B,hC,hB,hm⟩ :=
    same_resolvent_current_mass_bound A J α hs ht E hE D hD (hermitianMetric J α hs ht)
  obtain ⟨K,hK,hk⟩ :=
    same_resolvent_current_mass_cross A J α hs ht E hE D hD (hermitianMetric J α hs ht)
      μ M hM hg
  exact ⟨C*M+B,K,add_nonneg (mul_nonneg hC hM) hB,hK,
    fun r hr hr1 S => ⟨hm μ M hM hg r hr hr1 S,hk r hr hr1 S⟩⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWedgeMassUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricNormalCharts
open Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] unitMeasurable unitBorel 

include hE in
lemma separating_current_wedge_upper_oai
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
      ⟪S.regularize (hermitianMetric J α hs ht) μ,
          l2Star A J α hs ht (S.regularize (hermitianMetric J α hs ht) μ)⟫ ≤ K := by
  obtain ⟨B,hBc,hBR,L,hL,hB⟩ := exists_convergent_closed_lift A J α hs ht D hD (hermitianMetric J α hs ht)
  obtain ⟨C,K,hC,hK,hcross⟩ := separating_current_mass_and_cross A J α hs ht E hE D hD μ hann
  refine ⟨K^2,sq_nonneg _,fun r hr hr1 S => ?_⟩
  have hrep := ((hB μ).1 r hr hr1).1
  have hcr := (hcross r hr hr1 S).2
    (hodgeCorrectionRegularize A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr) (by
      intro a
      rw [hrep,map_sub,hodgeCorrectionSource_anti,sub_self])
  have he := hodgeCorrected_energy_identity A J α hs ht D hD B hBc hBR
    (hermitianMetric J α hs ht) μ hann r hr S hrep
  have hh := (neg_le_abs ⟪S.regularize (hermitianMetric J α hs ht) μ,
    hodgeCorrectionRegularize A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr⟫).trans hcr
  nlinarith [sq_nonneg (‖hodgeCorrectionRegularize A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr‖-K)]

end TamingCompatibility.GeometricHilbert

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.separating_current_wedge_upper_oai.{u_1}
