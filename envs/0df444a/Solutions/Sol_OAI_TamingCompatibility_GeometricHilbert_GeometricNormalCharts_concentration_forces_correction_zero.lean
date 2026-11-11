-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_forces_correction_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:20:35.571204+00:00
-- url     : https://prove2.me/submissions/70c16a53-435f-4675-95ee-1e0780a6ed12

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc032
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_concentration_double_physical_tail
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_same_resolvent_positive_cross_lower
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_subprob_anti_cross_tendsto
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_hodge_residual_energy_zero
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ManifoldScalarCalculus
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.antiMultiply_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

omit [IsManifold Model ∞ X] in
lemma scalarDifferential_sum {ι : Type*} (s : Finset ι) (f : ι → X → ℝ)
    (hf : ∀ i ∈ s, MDifferentiable Model 𝓘(ℝ,ℝ) (f i)) :
    scalarDifferential (∑ i ∈ s, f i) = ∑ i ∈ s, scalarDifferential (f i) := by
  funext x
  have hh : HasMFDerivAt Model 𝓘(ℝ,ℝ) (∑ i ∈ s, f i) x
      (∑ i ∈ s, (show Space →L[ℝ] ℝ from mfderiv Model 𝓘(ℝ,ℝ) (f i) x)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using! (hasMFDerivAt_const (I := Model) (I' := 𝓘(ℝ,ℝ)) (0 : ℝ) x)
    | insert i s hi IH =>
      erw [Finset.sum_insert hi,Finset.sum_insert hi]
      exact ((hf i (Finset.mem_insert_self i s) x).hasMFDerivAt).add
        (IH (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
  unfold scalarDifferential
  rw [hh.mfderiv]
  change (ofSubsingletonLIE (𝕜 := ℝ) (E := Space) (F := ℝ) (0 : Fin 1))
    (∑ i ∈ s, mfderiv Model 𝓘(ℝ,ℝ) (f i) x) = _
  erw [_root_.map_sum]
  change ∑ i ∈ s, scalarDifferential (f i) x = (∑ i ∈ s, scalarDifferential (f i)) x
  exact (Finset.sum_apply x s (fun i => scalarDifferential (f i))).symm

omit [IsManifold Model ∞ X] in
lemma scalarDifferential_comp {f : X → ℝ} (hf : MDifferentiable Model 𝓘(ℝ,ℝ) f)
    {g : ℝ → ℝ} {g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' (f x)) (f x)) :
    scalarDifferential (g ∘ f) = fun x => g' (f x) • scalarDifferential f x := by
  funext x
  unfold scalarDifferential
  rw [mfderiv_comp x ((hg x).differentiableAt.mdifferentiableAt) (hf x),mfderiv_eq_fderiv,
    (hg x).hasFDerivAt.fderiv]
  erw [←map_smul]
  congr 1
  ext v
  let L : Space →L[ℝ] ℝ := mfderiv Model 𝓘(ℝ,ℝ) f x
  change L v * g' (f x) = g' (f x) * L v
  ring

omit [IsManifold Model ∞ X] in
lemma wedgeOne_sum_left {ι : Type*} (s : Finset ι) (a : ι → Form X 1) (b : Form X 1) :
    wedgeOne (∑ i ∈ s, a i) b = ∑ i ∈ s, wedgeOne (a i) b := by
  funext x
  simp only [wedgeOne,Finset.sum_apply, ExteriorForms.oneLinear]
  erw [_root_.map_sum]
  exact _root_.map_sum (ExteriorForms.wedgeOneRight (E := Space) (b x)) _ _

omit [IsManifold Model ∞ X] in
lemma wedgeOne_fun_smul_left (f : X → ℝ) (a b : Form X 1) :
    wedgeOne (fun x => f x • a x) b = fun x => f x • wedgeOne a b x := by
  funext x
  change ExteriorForms.wedgeOne (E := Space) (ExteriorForms.oneLinear (E := Space) (f x • a x)) (b x) = _
  dsimp only [ExteriorForms.oneLinear]
  erw [_root_.map_smul]
  exact _root_.map_smul (ExteriorForms.wedgeOneRight (E := Space) (b x)) _ _
end TamingCompatibility.ManifoldForms

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_SummableCutoff
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter _root_.MeasureTheory Finset
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff
variable {X : Type*}

lemma saturation_nonneg (c : ℕ → X → ℝ) (hc : ∀ n x, 0 ≤ c n x)
    (n N : ℕ) (x : X) : 0 ≤ saturation c n N x := by
  rw [saturation, sub_nonneg, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun k _ => hc (k+n) x))

lemma saturation_le_one (c : ℕ → X → ℝ) (n N : ℕ) (x : X) :
    saturation c n N x ≤ 1 := by
  have := Real.exp_pos (-(∑ k ∈ Finset.range N, c (k+n) x))
  unfold saturation
  linarith

lemma saturation_tendsto_tail (c : ℕ → X → ℝ) (hc : ∀ n x, 0 ≤ c n x)
    (n : ℕ) (x : X) :
    Tendsto (fun N => saturation c n N x) atTop (𝓝 (tailLimit c n x)) := by
  classical
  by_cases hx : Summable (fun k => c k x)
  · simp only [tailLimit,ite_eq_left hx]
    exact tendsto_const_nhds.sub
      (Real.continuous_exp.tendsto _ |>.comp (((summable_nat_add_iff n).2 hx).hasSum.tendsto_sum_nat.neg))
  · simp only [tailLimit,ite_eq_right hx]
    have hns : ¬ Summable (fun k => c (k+n) x) := by
      exact fun h => hx ((summable_nat_add_iff n).1 h)
    have htop := (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun k => hc (k+n) x)).1 hns
    simpa only [sub_zero,saturation,Function.comp_def] using tendsto_const_nhds.sub (Real.tendsto_exp_neg_atTop_nhds_zero.comp htop)

lemma tail_nonneg (c : ℕ → X → ℝ) (hc : ∀ n x, 0 ≤ c n x)
    (n : ℕ) (x : X) : 0 ≤ tailLimit c n x :=
  ge_of_tendsto (saturation_tendsto_tail c hc n x)
    (Eventually.of_forall (fun N => saturation_nonneg c hc n N x))

lemma tail_le_one (c : ℕ → X → ℝ) (hc : ∀ n x, 0 ≤ c n x)
    (n : ℕ) (x : X) : tailLimit c n x ≤ 1 :=
  le_of_tendsto (saturation_tendsto_tail c hc n x)
    (Eventually.of_forall (fun N => saturation_le_one c n N x))

lemma tail_tendsto_indicator (c : ℕ → X → ℝ) (x : X) :
    Tendsto (fun n => tailLimit c n x) atTop
      (𝓝 ((exceptional c).indicator (fun _ => (1:ℝ)) x)) := by
  classical
  by_cases hx : Summable (fun k => c k x)
  · have hxe : x ∉ exceptional c := not_not.mpr hx
    simp only [tailLimit,ite_eq_left hx,Set.indicator_of_notMem hxe]
    simpa only [neg_zero,Real.exp_zero,sub_self,Function.comp_def] using (tendsto_const_nhds (x := (1:ℝ)) (f := atTop)).sub
      (Real.continuous_exp.tendsto _ |>.comp (tendsto_sum_nat_add (fun k => c k x)).neg)
  · have hxe : x ∈ exceptional c := hx
    simp only [tailLimit,ite_eq_right hx,Set.indicator_of_mem hxe]
    exact tendsto_const_nhds

lemma measurable_exceptional [MeasurableSpace X] (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n)) :
    MeasurableSet (exceptional c) := by
  have he : exceptional c = {x | (∑' n, ‖c n x‖ₑ) = ∞} := by
    ext x
    change (¬ Summable (fun n => c n x)) ↔ (∑' n, ‖c n x‖ₑ) = ∞
    have h := (tsum_enorm_ne_top_iff_summable_norm (f := fun n => c n x))
    have hn : (fun n => ‖c n x‖) = (fun n => c n x) := by
      funext n
      exact abs_of_nonneg (hc n x)
    rw [hn] at h
    exact (not_congr h).symm.trans not_not
  rw [he]
  exact measurableSet_eq_fun (Measurable.tsum (fun n => (hm n).enorm)) measurable_const

lemma measurable_saturation [MeasurableSpace X] (c : ℕ → X → ℝ)
    (hm : ∀ n, Measurable (c n)) (n N : ℕ) : Measurable (saturation c n N) := by
  exact measurable_const.sub (Real.continuous_exp.measurable.comp
    ((Finset.measurable_sum _ (fun k _ => hm (k+n))).neg))

lemma measurable_tail [MeasurableSpace X] (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n)) (n : ℕ) :
    Measurable (tailLimit c n) :=
  measurable_of_tendsto_metrizable (fun N => measurable_saturation c hm n N)
    (tendsto_pi_nhds.mpr (fun x => saturation_tendsto_tail c hc n x))
end TamingCompatibility.SummableCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ActivationScales
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff

lemma stepSize_pos (n : ℕ) : 0 < stepSize n := pow_pos (by norm_num) _
lemma summable_stepSize : Summable stepSize := summable_geometric_of_abs_lt_one (by norm_num)
end TamingCompatibility.SummableCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ActivationMeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Bundle ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]

lemma contMDiff_saturation {c : ℕ → X → ℝ}
    (hc : ∀ k, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (c k)) (n N : ℕ) :
    ContMDiff Model 𝓘(ℝ,ℝ) ∞ (SummableCutoff.saturation c n N) := by
  apply contMDiff_const.sub
  apply Real.contDiff_exp.comp_contMDiff
  exact (contMDiff_finsetSum (fun k _ => hc (k+n))).neg

lemma scalarDifferential_saturation {c : ℕ → X → ℝ}
    (hc : ∀ k, MDifferentiable Model 𝓘(ℝ,ℝ) (c k)) (n N : ℕ) :
    scalarDifferential (SummableCutoff.saturation c n N) =
      fun x => Real.exp (-(∑ k ∈ Finset.range N, c (k+n) x)) •
        (∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) x) := by
  let f : X → ℝ := ∑ k ∈ Finset.range N, c (k+n)
  have hf : MDifferentiable Model 𝓘(ℝ,ℝ) f := MDifferentiable.sum (fun k _ => hc (k+n))
  have h := scalarDifferential_comp hf (g := fun t : ℝ => 1-Real.exp (-t))
    (g' := fun t => Real.exp (-t)) (fun x => by
      convert! ((Real.hasDerivAt_exp (-f x)).comp (f x) (hasDerivAt_neg (f x))).const_sub 1 using 1; ring)
  rw [scalarDifferential_sum _ _ (fun k _ => hc (k+n))] at h
  convert! h using 1
  · congr 1
    funext x
    simp only [SummableCutoff.saturation,f,Function.comp_def,Finset.sum_apply]
  · funext x
    simp only [f,Finset.sum_apply]
end TamingCompatibility.ManifoldForms

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeNormalDistribution
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.harmonicAnti_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeInclusion_dense : DenseRange (hodgeInclusion A J α hs ht) :=
  (smoothL2_dense A J α hs ht true).mono (by rintro _ ⟨a,rfl⟩; exact ⟨hodgeSmooth A J α hs ht a,rfl⟩)
end TamingCompatibility.GeometricHilbert

end
end

end
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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeL2Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.MeasureTheory
open scoped RealInnerProductSpace
namespace TamingCompatibility.GeometricHilbert
variable {V E X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace X]
  {μ : Measure X}

variable [CompleteSpace E]

lemma isometryFromCompletion_coe (f : V →ₗᵢ[ℝ] E) (v : V) :
    isometryFromCompletion f (v : UniformSpace.Completion V) = f v :=
  f.toContinuousLinearMap.fromCompletion_apply_coe v

end TamingCompatibility.GeometricHilbert

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldVolume ManifoldLocalization HodgeFrame _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

lemma l2Coefficients_smooth (a : PreL2 A J α hs ht true) :
    ∀ᵐ x ∂geometricVolume A J α,
      l2Coefficients A J α hs ht E hE (smoothL2 A J α hs ht true a) x =
        normalizedFrameEncode A J α ht E x (a.val x) := by
  change ∀ᵐ x ∂geometricVolume A J α,
    isometryFromCompletion (lpEncodeIsometry (smoothFrameEncode A J α hs ht E)
      (smoothFrameEncode_memLp A J α hs ht E hE)
      (smoothFrameEncode_inner_integral A J α hs ht E hE))
        (a : UniformSpace.Completion (PreL2 A J α hs ht true)) x = _
  rw [isometryFromCompletion_coe]
  exact (smoothFrameEncode_memLp A J α hs ht E hE a).coeFn_toLp

lemma l2Coefficients_pairing (Q : L2 A J α hs ht true) (a : PreL2 A J α hs ht true) :
    ⟪Q,smoothL2 A J α hs ht true a⟫ =
      ∫ x, ⟪l2Coefficients A J α hs ht E hE Q x,
        normalizedFrameEncode A J α ht E x (a.val x)⟫ ∂geometricVolume A J α := by
  rw [← (l2Coefficients A J α hs ht E hE).inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Coefficients_smooth A J α hs ht E hE a] with x hx
  rw [hx]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_ManifoldBoundaryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma saturation_boundary_eval (J : AlmostComplexStructure X) (c : ℕ → X → ℝ)
    (hc : ∀ k, MDifferentiable Model 𝓘(ℝ,ℝ) (c k)) (hpos : ∀ k x, 0 ≤ c k x)
    (θ : Form X 1) (n N : ℕ) (x : X) (v : TangentSpace Model x) :
    |eval (ManifoldForms.wedgeOne (scalarDifferential (SummableCutoff.saturation c n N)) θ) x v (J.endomorphism x v)| ≤
      ∑ k ∈ Finset.range N, |eval (ManifoldForms.wedgeOne (scalarDifferential (c (k+n))) θ) x v (J.endomorphism x v)| := by
  rw [scalarDifferential_saturation hc,wedgeOne_fun_smul_left]
  have he : eval (fun x => Real.exp (-(∑ k ∈ Finset.range N, c (k+n) x)) •
      ManifoldForms.wedgeOne (fun x => ∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) x) θ x) x v (J.endomorphism x v) =
      Real.exp (-(∑ k ∈ Finset.range N, c (k+n) x)) *
        (∑ k ∈ Finset.range N, eval (ManifoldForms.wedgeOne (scalarDifferential (c (k+n))) θ) x v (J.endomorphism x v)) := by
    have hh : (fun x => ∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) x) =
        ∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) := by funext x; simp only [Finset.sum_apply]
    rw [hh,wedgeOne_sum_left]
    simp only [eval,Finset.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
    erw [ContinuousAlternatingMap.sum_apply]
  rw [he,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_of_le_one_left (abs_nonneg _) ?_).trans (Finset.abs_sum_le_sum_abs _ _)
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun k _ => hpos (k+n) x))

variable [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (ht : Tames α J) (E : ∀ p : A.centers, ParametrixData J α ht p.val)

omit [T2Space X] [CompactSpace X] in
lemma saturation_boundary_norm (c : ℕ → X → ℝ)
    (hc : ∀ k, MDifferentiable Model 𝓘(ℝ,ℝ) (c k)) (hpos : ∀ k x, 0 ≤ c k x)
    (θ : Form X 1) (n N : ℕ) (x : X) :
    ‖normalizedFrameEncode A J α ht E x
      (ManifoldForms.wedgeOne (scalarDifferential (SummableCutoff.saturation c n N)) θ x)‖ ≤
      ∑ k ∈ Finset.range N, ‖normalizedFrameEncode A J α ht E x
        (ManifoldForms.wedgeOne (scalarDifferential (c (k+n))) θ x)‖ := by
  rw [scalarDifferential_saturation hc,wedgeOne_fun_smul_left]
  have hh : (fun x => ∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) x) =
      ∑ k ∈ Finset.range N, scalarDifferential (c (k+n)) := by funext x; simp only [Finset.sum_apply]
  rw [hh,wedgeOne_sum_left]
  simp only [Finset.sum_apply]
  erw [_root_.map_smul,_root_.map_sum]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
    (norm_sum_le (Finset.range N) (fun k => normalizedFrameEncode A J α ht E x
      (ManifoldForms.wedgeOne (scalarDifferential (c (k+n))) θ x)))
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun k _ => hpos (k+n) x))
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScalarBoundaryIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel

omit [MeasurableSpace X] [BorelSpace X] in
lemma unit_boundary_integrable
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (θ : smoothForms X 1) :
    Integrable (fun u : MetricUnit (hermitianMetric J α hs ht) =>
      |eval (ManifoldForms.wedgeOne (scalarDifferential f) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)|) μ :=
  (smoothUnitEvaluation J (hermitianMetric J α hs ht)
    ⟨_,smooth_boundary f hf θ⟩).continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

include hE in
lemma coefficient_boundary_integrable
    (Q : L2 A J α hs ht true) (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f)
    (θ : smoothForms X 1) :
    Integrable (fun x => ‖l2Coefficients A J α hs ht E hE Q x‖ *
      ‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne (scalarDifferential f) θ.val x)‖)
      (geometricVolume A J α) := by
  let q := l2Coefficients A J α hs ht E hE Q
  have hb := smoothFrameEncode_memLp A J α hs ht E hE ⟨_,smooth_boundary f hf θ⟩
  exact (Lp.memLp q).norm.integrable_mul hb.norm

include hE in
lemma coefficient_pairing_integrable (Q : L2 A J α hs ht true) (a : smoothForms X 2) :
    Integrable (fun x => ⟪l2Coefficients A J α hs ht E hE Q x,
      normalizedFrameEncode A J α ht E x (a.val x)⟫) (geometricVolume A J α) := by
  apply (MeasureTheory.L2.integrable_inner
    (l2Coefficients A J α hs ht E hE Q)
    (l2Coefficients A J α hs ht E hE (smoothL2 A J α hs ht true a))).congr
  filter_upwards [l2Coefficients_smooth A J α hs ht E hE a] with x hx
  rw [hx]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ActivationSaturationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory Filter SummableCutoff
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel 
variable (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
  (Q : L2 A J α hs ht true) (S : ConcentrationActivationData A J α hs ht E hE μ Q)

lemma saturation_unit_boundary (θ : smoothForms X 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n N,
    (∫ u : MetricUnit (hermitianMetric J α hs ht),
      |eval (ManifoldForms.wedgeOne (scalarDifferential (saturation S.cutoff n N)) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ∂μ) ≤
      ∑ k ∈ Finset.range N, C*stepSize (k+n) := by
  obtain ⟨C,hC,hbound⟩ := S.unit_boundary θ
  refine ⟨C,hC,fun n N => ?_⟩
  calc
    _ ≤ ∫ u : MetricUnit (hermitianMetric J α hs ht), ∑ k ∈ Finset.range N,
        |eval (ManifoldForms.wedgeOne (scalarDifferential (S.cutoff (k+n))) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ∂μ :=
      integral_mono (unit_boundary_integrable J α hs ht μ _ (contMDiff_saturation S.smooth n N) θ)
        (integrable_finsetSum _ (fun k _ => unit_boundary_integrable J α hs ht μ _ (S.smooth (k+n)) θ))
        (fun u => saturation_boundary_eval J S.cutoff
          (fun k => (S.smooth k).mdifferentiable (by simp)) S.nonneg θ.val n N u.val.proj u.val.2)
    _ = ∑ k ∈ Finset.range N, ∫ u : MetricUnit (hermitianMetric J α hs ht),
        |eval (ManifoldForms.wedgeOne (scalarDifferential (S.cutoff (k+n))) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ∂μ :=
      integral_finsetSum _ (fun k _ => unit_boundary_integrable J α hs ht μ _ (S.smooth (k+n)) θ)
    _ ≤ _ := Finset.sum_le_sum (fun k _ => hbound (k+n))

omit [IsFiniteMeasure μ] in
lemma saturation_Q_boundary (θ : smoothForms X 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n N,
    (∫ x, ‖l2Coefficients A J α hs ht E hE Q x‖ *
      ‖normalizedFrameEncode A J α ht E x
        (ManifoldForms.wedgeOne (scalarDifferential (saturation S.cutoff n N)) θ.val x)‖ ∂geometricVolume A J α) ≤
      ∑ k ∈ Finset.range N, C*stepSize (k+n) := by
  obtain ⟨C,hC,hbound⟩ := S.Q_boundary θ
  refine ⟨C,hC,fun n N => ?_⟩
  calc
    _ ≤ ∫ x, ∑ k ∈ Finset.range N, ‖l2Coefficients A J α hs ht E hE Q x‖ *
        ‖normalizedFrameEncode A J α ht E x
          (ManifoldForms.wedgeOne (scalarDifferential (S.cutoff (k+n))) θ.val x)‖ ∂geometricVolume A J α :=
      integral_mono (coefficient_boundary_integrable A J α hs ht E hE Q _ (contMDiff_saturation S.smooth n N) θ)
        (integrable_finsetSum _ (fun k _ => coefficient_boundary_integrable A J α hs ht E hE Q _ (S.smooth (k+n)) θ))
        (fun x => by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            (saturation_boundary_norm A J α ht E S.cutoff
              (fun k => (S.smooth k).mdifferentiable (by simp)) S.nonneg θ.val n N x) (norm_nonneg _))
    _ = ∑ k ∈ Finset.range N, ∫ x, ‖l2Coefficients A J α hs ht E hE Q x‖ *
        ‖normalizedFrameEncode A J α ht E x
          (ManifoldForms.wedgeOne (scalarDifferential (S.cutoff (k+n))) θ.val x)‖ ∂geometricVolume A J α :=
      integral_finsetSum _ (fun k _ => coefficient_boundary_integrable A J α hs ht E hE Q _ (S.smooth (k+n)) θ)
    _ ≤ _ := Finset.sum_le_sum (fun k _ => hbound (k+n))
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_CutoffEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel 

lemma current_cutoff_equation
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (θ : smoothForms X 1) :
    (∫ u : MetricUnit (hermitianMetric J α hs ht), f u.val.proj *
      eval (exteriorDerivative θ.val) u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) ∂μ) +
      (∫ x, f x * ⟪l2Coefficients A J α hs ht E hE Q x,
        normalizedFrameEncode A J α ht E x (exteriorDerivative θ.val x)⟫ ∂geometricVolume A J α) =
      -(unitMeasureCurrent J (hermitianMetric J α hs ht) μ ⟨_,smooth_boundary f hf θ⟩ +
        ⟪Q,smoothL2 A J α hs ht true ⟨_,smooth_boundary f hf θ⟩⟫) := by
  let a : smoothForms X 2 := ⟨fun x => f x • exteriorDerivative θ.val x, θ.property.exteriorDerivative.fun_smul hf⟩
  let b : smoothForms X 2 := ⟨_,smooth_boundary f hf θ⟩
  have hb : a+b = ⟨exteriorDerivative (fun x => f x • θ.val x),
      (θ.property.fun_smul hf).exteriorDerivative⟩ := by
    apply Subtype.ext
    exact (exteriorDerivative_fun_smul hf θ.property).symm
  have h := hT (a+b) (by rw [hb]; exact (θ.property.fun_smul hf).closed_exteriorDerivative)
  erw [_root_.map_add,_root_.map_add,inner_add_right] at h
  have haP : unitMeasureCurrent J (hermitianMetric J α hs ht) μ a =
      ∫ u : MetricUnit (hermitianMetric J α hs ht), f u.val.proj *
        eval (exteriorDerivative θ.val) u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) ∂μ := by
    rfl
  have haQ : ⟪Q,smoothL2 A J α hs ht true a⟫ =
      ∫ x, f x * ⟪l2Coefficients A J α hs ht E hE Q x,
        normalizedFrameEncode A J α ht E x (exteriorDerivative θ.val x)⟫ ∂geometricVolume A J α := by
    rw [l2Coefficients_pairing A J α hs ht E hE Q a]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    change ⟪_,normalizedFrameEncode A J α ht E x (f x • exteriorDerivative θ.val x)⟫ = _
    erw [_root_.map_smul]
    rw [real_inner_smul_right]
  rw [haP,haQ] at h
  change _ = -(unitMeasureCurrent J (hermitianMetric J α hs ht) μ b + ⟪Q,smoothL2 A J α hs ht true b⟫)
  linarith

lemma current_cutoff_bound
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (f : X → ℝ) (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (θ : smoothForms X 1) :
    |(∫ u : MetricUnit (hermitianMetric J α hs ht), f u.val.proj *
      eval (exteriorDerivative θ.val) u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) ∂μ) +
      (∫ x, f x * ⟪l2Coefficients A J α hs ht E hE Q x,
        normalizedFrameEncode A J α ht E x (exteriorDerivative θ.val x)⟫ ∂geometricVolume A J α)| ≤
      (∫ u : MetricUnit (hermitianMetric J α hs ht),
        |eval (ManifoldForms.wedgeOne (scalarDifferential f) θ.val)
          u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ∂μ) +
      (∫ x, ‖l2Coefficients A J α hs ht E hE Q x‖ *
        ‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne (scalarDifferential f) θ.val x)‖ ∂geometricVolume A J α) := by
  rw [current_cutoff_equation A J α hs ht E hE μ Q hT f hf θ,abs_neg]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact abs_integral_le_integral_abs
  · rw [l2Coefficients_pairing A J α hs ht E hE Q ⟨_,smooth_boundary f hf θ⟩]
    apply (abs_integral_le_integral_abs).trans
    apply integral_mono (coefficient_pairing_integrable A J α hs ht E hE Q ⟨_,smooth_boundary f hf θ⟩).abs
      (coefficient_boundary_integrable A J α hs ht E hE Q f hf θ)
    exact fun x => abs_real_inner_le_norm _ _
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SummableRestriction
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter _root_.MeasureTheory Finset
open scoped Topology ENNReal
namespace TamingCompatibility.SummableCutoff
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma weighted_saturation_tendsto (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n))
    (μ : Measure X) (a : X → ℝ) (ha : Integrable a μ) (n : ℕ) :
    Tendsto (fun N => ∫ x, saturation c n N x * a x ∂μ) atTop
      (𝓝 (∫ x, tailLimit c n x * a x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖a x‖)
    (fun N => (measurable_saturation c hm n N).aestronglyMeasurable.mul ha.aestronglyMeasurable) ha.norm
  · intro N
    apply Eventually.of_forall
    intro x
    change ‖saturation c n N x * a x‖ ≤ ‖a x‖
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (saturation_nonneg c hc n N x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (saturation_le_one c n N x)
  · exact Eventually.of_forall (fun x => (saturation_tendsto_tail c hc n x).mul tendsto_const_nhds)

lemma weighted_tail_tendsto (c : ℕ → X → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hm : ∀ n, Measurable (c n))
    (μ : Measure X) (a : X → ℝ) (ha : Integrable a μ) :
    Tendsto (fun n => ∫ x, tailLimit c n x * a x ∂μ) atTop
      (𝓝 (∫ x in exceptional c, a x ∂μ)) := by
  have hlim : ∀ x, Tendsto (fun n => tailLimit c n x * a x) atTop
      (𝓝 ((exceptional c).indicator a x)) := by
    intro x
    convert (tail_tendsto_indicator c x).mul (tendsto_const_nhds (x := a x)) using 1
    all_goals try with_reducible_and_instances rfl
    by_cases hx : x ∈ exceptional c <;> simp [hx]
  have hD := tendsto_integral_of_dominated_convergence (fun x => ‖a x‖)
    (fun n => (measurable_tail c hc hm n).aestronglyMeasurable.mul ha.aestronglyMeasurable) ha.norm
    (fun n => Eventually.of_forall (fun x => show ‖tailLimit c n x * a x‖ ≤ ‖a x‖ from by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (tail_nonneg c hc n x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (tail_le_one c hc n x)))
    (Eventually.of_forall hlim)
  rwa [integral_indicator (measurable_exceptional c hc hm)] at hD

lemma restriction_zero_of_tail_bounds
    (c : ℕ → X → ℝ) (d : ℕ → Y → ℝ)
    (hc : ∀ n x, 0 ≤ c n x) (hd : ∀ n y, 0 ≤ d n y)
    (hcm : ∀ n, Measurable (c n)) (hdm : ∀ n, Measurable (d n))
    (μ : Measure X) (ν : Measure Y) (a : X → ℝ) (b : Y → ℝ)
    (ha : Integrable a μ) (hb : Integrable b ν)
    (hnull : ν (exceptional d) = 0)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n) (hes : Summable e)
    (hbound : ∀ n N, |(∫ x, saturation c n N x * a x ∂μ) +
      (∫ y, saturation d n N y * b y ∂ν)| ≤ ∑ k ∈ Finset.range N, e (k+n)) :
    ∫ x in exceptional c, a x ∂μ = 0 := by
  have htail (n : ℕ) : |(∫ x, tailLimit c n x * a x ∂μ)+
      (∫ y, tailLimit d n y * b y ∂ν)| ≤ ∑' k, e (k+n) := by
    apply le_of_tendsto (((weighted_saturation_tendsto c hc hcm μ a ha n).add
      (weighted_saturation_tendsto d hd hdm ν b hb n)).abs)
    apply Eventually.of_forall
    intro N
    exact (hbound n N).trans (((summable_nat_add_iff n).2 hes).sum_le_tsum
      (Finset.range N) (fun k _ => he (k+n)))
  have hlim := ((weighted_tail_tendsto c hc hcm μ a ha).add
    (weighted_tail_tendsto d hd hdm ν b hb)).abs
  have hbzero : ∫ y in exceptional d, b y ∂ν = 0 := by
    rw [Measure.restrict_eq_zero.mpr hnull,integral_zero_measure]
  rw [hbzero,add_zero] at hlim
  have hh := le_of_tendsto_of_tendsto hlim (tendsto_sum_nat_add e)
    (Eventually.of_forall htail)
  exact abs_nonpos_iff.mp hh
end TamingCompatibility.SummableCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory Filter SummableCutoff
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel 
variable (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
  (Q : L2 A J α hs ht true) (S : ConcentrationActivationData A J α hs ht E hE μ Q)

lemma concentration_restriction_closed
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (θ : smoothForms X 1) :
    unitMeasureCurrent J (hermitianMetric J α hs ht)
      (μ.restrict ((fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) ⁻¹' exceptional S.cutoff))
      ⟨exteriorDerivative θ.val,θ.property.exteriorDerivative⟩ = 0 := by
  let c := fun n (u : MetricUnit (hermitianMetric J α hs ht)) => S.cutoff n u.val.proj
  let a := fun u : MetricUnit (hermitianMetric J α hs ht) =>
    eval (exteriorDerivative θ.val) u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)
  let b := fun x => ⟪l2Coefficients A J α hs ht E hE Q x,
    normalizedFrameEncode A J α ht E x (exteriorDerivative θ.val x)⟫
  have ha : Integrable a μ :=
    (smoothUnitEvaluation J (hermitianMetric J α hs ht)
      ⟨_,θ.property.exteriorDerivative⟩).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb : Integrable b (geometricVolume A J α) :=
    coefficient_pairing_integrable A J α hs ht E hE Q ⟨_,θ.property.exteriorDerivative⟩
  have hπ : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  obtain ⟨CP,hCP,hP⟩ := saturation_unit_boundary A J α hs ht E hE μ Q S θ
  obtain ⟨CQ,hCQ,hQ⟩ := saturation_Q_boundary A J α hs ht E hE μ Q S θ
  have hh := restriction_zero_of_tail_bounds c S.cutoff
    (fun n u => S.nonneg n u.val.proj) S.nonneg
    (fun n => ((S.smooth n).continuous.comp hπ).measurable)
    (fun n => (S.smooth n).continuous.measurable)
    μ (geometricVolume A J α) a b ha hb S.null
    (fun n => (CP+CQ)*stepSize n) (fun n => mul_nonneg (add_nonneg hCP hCQ) (stepSize_pos n).le)
    (summable_stepSize.mul_left _) (fun n N => ?_)
  · exact hh
  · apply (current_cutoff_bound A J α hs ht E hE μ Q hT
      (saturation S.cutoff n N) (contMDiff_saturation S.smooth n N) θ).trans
    apply (add_le_add (hP n N) (hQ n N)).trans_eq
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory Filter SummableCutoff
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel 

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitMeasureCurrent_restrict_add
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Z : Set (MetricUnit (hermitianMetric J α hs ht))) (hZ : MeasurableSet Z)
    (a : smoothForms X 2) :
    unitMeasureCurrent J (hermitianMetric J α hs ht) (μ.restrict Z) a+
      unitMeasureCurrent J (hermitianMetric J α hs ht) (μ.restrict Zᶜ) a =
        unitMeasureCurrent J (hermitianMetric J α hs ht) μ a := by
  have hi := (smoothUnitEvaluation J (hermitianMetric J α hs ht) a).continuous.integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  change (∫ u, smoothUnitEvaluation J (hermitianMetric J α hs ht) a u ∂μ.restrict Z)+
      (∫ u, smoothUnitEvaluation J (hermitianMetric J α hs ht) a u ∂μ.restrict Zᶜ) = _
  rw [← integral_add_measure hi.restrict hi.restrict,Measure.restrict_add_restrict_compl hZ]
  rfl

lemma concentration_residual_source_closed
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    (Q : L2 A J α hs ht true) (S : ConcentrationActivationData A J α hs ht E hE μ Q)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) :
    let ν := μ.restrict ((fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) ⁻¹' (exceptional S.cutoff)ᶜ)
    ∀ ξ : PreL2 A J α hs ht false,
      (positiveL2Source A J α hs ht ν + l2CurrentSource A J α hs ht Q)
        (hodgePreD A J α hs ht ξ) = 0 := by
  dsimp only
  let Z := (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) ⁻¹' exceptional S.cutoff
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hZ : MeasurableSet Z :=
    (measurable_exceptional S.cutoff S.nonneg (fun n => (S.smooth n).continuous.measurable)).preimage hp.measurable
  intro ξ
  have hclosed := concentration_restriction_closed A J α hs ht E hE μ Q S hT ξ
  have hsplit := unitMeasureCurrent_restrict_add J α hs ht μ Z hZ (hodgePreD A J α hs ht ξ)
  have ht' := hT (hodgePreD A J α hs ht ξ) ξ.property.closed_exteriorDerivative
  change unitMeasureCurrent J (hermitianMetric J α hs ht) (μ.restrict Z) (hodgePreD A J α hs ht ξ) = 0 at hclosed
  rw [hclosed,zero_add] at hsplit
  change unitMeasureCurrent J (hermitianMetric J α hs ht) (μ.restrict Zᶜ) (hodgePreD A J α hs ht ξ)+
    ⟪Q,smoothL2 A J α hs ht true (hodgePreD A J α hs ht ξ)⟫ = 0
  rw [hsplit]
  exact ht'
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeConvergence
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Filter Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeResolvent_domain_error (r : ℝ) (hr : 0 < r) (a : hodgeEnergy A J α hs ht) :
    ‖hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht a) -
      hodgeInclusion A J α hs ht a‖ ≤ r * ‖hodgeWeakDerivative A J α hs ht a‖ := by
  let i := hodgeInclusion A J α hs ht
  let D := hodgeWeakDerivative A J α hs ht
  let u := hodgeWeakSolution A J α hs ht r hr (i a)
  have he := hodgeWeakSolution_identity A J α hs ht r hr (i a) (u-a)
  have hi : hodgeResolvent A J α hs ht r (i a) = i u := by
    rw [hodgeResolvent_eq A J α hs ht r hr]; rfl
  change ⟪hodgeResolvent A J α hs ht r (i a),i (u-a)⟫ + r^2*⟪D u,D (u-a)⟫ = ⟪i a,i (u-a)⟫ at he
  rw [hi,map_sub,map_sub,inner_sub_right,inner_sub_right,inner_sub_right] at he
  have hn : ‖i u-i a‖^2 + r^2*‖D u‖^2 = r^2*⟪D u,D a⟫ := by
    rw [← real_inner_self_eq_norm_sq (i u-i a)]
    simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq]
    rw [real_inner_comm (i a) (i u)] at he ⊢
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at he
    linarith
  have hc := mul_le_mul_of_nonneg_left (real_inner_le_norm (D u) (D a)) (sq_nonneg r)
  rw [hi]
  have hpos : 0 ≤ r * ‖D a‖ := mul_nonneg hr.le (norm_nonneg _)
  have hsquare := sq_nonneg (r*‖D u‖-r*‖D a‖)
  nlinarith [norm_nonneg (i u-i a)]

lemma hodgeResolvent_tendsto (f : L2 A J α hs ht true) :
    Tendsto (fun r : ℝ => hodgeResolvent A J α hs ht r f) (𝓝[>] 0) (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a,ha⟩ := (hodgeInclusion_dense A J α hs ht).exists_dist_lt f (by positivity : 0 < ε/4)
  let D := hodgeWeakDerivative A J α hs ht a
  have hδ : 0 < ε/(2*(‖D‖+1)) := div_pos hε (by positivity)
  filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Iio_mem_nhds hδ))] with r hr hsmall
  have hr' : 0 < r := hr
  have hsmallD : r * ‖D‖ < ε/2 := by
    have hb : r*(2*(‖D‖+1)) < ε := (lt_div_iff₀ (by positivity)).mp hsmall
    nlinarith [norm_nonneg D]
  rw [dist_eq_norm]
  have hx := hodgeResolvent_domain_error A J α hs ht r hr' a
  have hf := hodgeResolvent_norm_le A J α hs ht r (f-hodgeInclusion A J α hs ht a)
  rw [map_sub] at hf
  have htri := norm_add_le (hodgeResolvent A J α hs ht r f-
    hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht a))
    (hodgeResolvent A J α hs ht r (hodgeInclusion A J α hs ht a)-hodgeInclusion A J α hs ht a)
  have htri2 := norm_add_le (hodgeResolvent A J α hs ht r f-hodgeInclusion A J α hs ht a)
    (hodgeInclusion A J α hs ht a-f)
  rw [sub_add_sub_cancel] at htri htri2
  rw [dist_eq_norm,norm_sub_rev] at ha
  have hn := norm_sub_rev (hodgeInclusion A J α hs ht a) f
  change r*‖hodgeWeakDerivative A J α hs ht a‖ < ε/2 at hsmallD
  linarith

lemma hodgeRegularization_error (r : ℝ) (f : L2 A J α hs ht true) :
    ‖hodgeRegularization A J α hs ht r f-f‖ ≤
      3*‖hodgeResolvent A J α hs ht r f-f‖ := by
  let R := hodgeResolvent A J α hs ht r
  have h1 : ‖R (R f)-R f‖ ≤ ‖R f-f‖ := by
    rw [← map_sub]; exact hodgeResolvent_norm_le A J α hs ht r _
  have h2 : ‖R (R (R f))-R (R f)‖ ≤ ‖R (R f)-R f‖ := by
    rw [← map_sub]; exact hodgeResolvent_norm_le A J α hs ht r _
  have ht1 := norm_add_le (R (R (R f))-R (R f)) (R (R f)-R f)
  have ht2 := norm_add_le (R (R (R f))-R f) (R f-f)
  rw [sub_add_sub_cancel] at ht1 ht2
  change ‖R (R (R f))-f‖ ≤ 3*‖R f-f‖
  linarith

lemma hodgeRegularization_tendsto (f : L2 A J α hs ht true) :
    Tendsto (fun r : ℝ => hodgeRegularization A J α hs ht r f) (𝓝[>] 0) (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := (hodgeResolvent_tendsto A J α hs ht f).sub (tendsto_const_nhds (x := f))
  have hn := h.norm.const_mul 3
  simp only [sub_self,norm_zero,mul_zero] at hn
  exact squeeze_zero (fun r => norm_nonneg _)
    (fun r => hodgeRegularization_error A J α hs ht r f) hn
end TamingCompatibility.GeometricHilbert

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeResidualEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace TamingCompatibility
lemma zero_of_residual_energy_limit
    {V : Type*} [NormedAddCommGroup V]
    (q : ℕ → V) (Q : V) (w e a b : ℕ → ℝ)
    (hq : Tendsto q atTop (𝓝 Q)) (he : Tendsto e atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hlower : ∀ n, -e n ≤ w n)
    (henergy : ∀ n, w n+a n+b n+‖q n‖^2 = 0) : Q = 0 := by
  have hh : ∀ n, ‖q n‖^2 ≤ e n-a n-b n := by
    intro n
    have h₁ := hlower n
    have h₂ := henergy n
    linarith
  have hlim : ‖Q‖^2 ≤ (0:ℝ) := by
    have hl := le_of_tendsto_of_tendsto (hq.norm.pow 2) ((he.sub ha).sub hb) (Eventually.of_forall hh)
    simpa only [sub_zero] using hl
  apply norm_eq_zero.mp
  have hn := norm_nonneg Q
  nlinarith
end TamingCompatibility

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume Set _root_.MeasureTheory Filter SummableCutoff
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

include D hD in
lemma concentration_forces_correction_zero_oai
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true) (haQ : l2AntiProjection A J α hs ht Q = Q)
    (hQ : l2Star A J α hs ht Q = Q)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a+⟪Q,smoothL2 A J α hs ht true a⟫ = 0)
    (S : ConcentrationActivationData A J α hs ht E hE μ Q) : Q = 0 := by
  let Z := (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) ⁻¹' (exceptional S.cutoff)ᶜ
  let ν := μ.restrict Z
  have hre (U : Set (MetricUnit (hermitianMetric J α hs ht))) : ν.real U ≤ μ.real U :=
    ENNReal.toReal_mono (measure_ne_top μ U) (Measure.restrict_apply_le Z U)
  have hν1 : ν.real univ ≤ 1 := by simpa only [probReal_univ] using hre univ
  obtain ⟨M,hM,hgrowth⟩ := separating_probability_quadratic_growth J α hs ht μ hann
  have hνgrowth : ∀ x : X, ∀ s : ℝ, 0 < s →
      ν.real {u | hermitianEDist J α hs ht x u.val.proj < ENNReal.ofReal s} ≤ M*s^2 := by
    intro x s hs'
    exact (hre _).trans (hgrowth x s hs')
  have hr : Tendsto S.radius atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨S.radius_limit,Eventually.of_forall S.radius_pos⟩
  let P := fun n => hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) μ (S.radius n)
  let P' := fun n => hodgePositiveCurrentFamily A J α hs ht D hD (hermitianMetric J α hs ht) ν (S.radius n)
  let V := fun n => hodgeRegularization A J α hs ht (S.radius n) Q
  have hV : Tendsto V atTop (𝓝 Q) := (hodgeRegularization_tendsto A J α hs ht Q).comp hr
  have hp : Tendsto (fun n => ⟪P n,V n⟫) atTop (𝓝 0) :=
    (subprob_anti_cross_tendsto A J α hs ht E hE D hD μ (by simp) M hM hgrowth Q haQ).comp hr
  have hp' : Tendsto (fun n => ⟪P' n,V n⟫) atTop (𝓝 0) :=
    (subprob_anti_cross_tendsto A J α hs ht E hE D hD ν hν1 M hM hνgrowth Q haQ).comp hr
  obtain ⟨C,B,hC,hB,hbound⟩ := same_resolvent_positive_cross_lower A J α hs ht E hE D hD
  let e := fun n => C*(∫ v, physicalProfileMass J α hs ht μ (S.radius n) v.val.proj/(S.radius n)^2 ∂ν)+
    B*(S.radius n)^2*ν.real univ
  have he : Tendsto e atTop (𝓝 0) := by
    have hl := concentration_double_physical_tail A J α hs ht E hE μ Q S hann
    have hh := (hl.const_mul C).add (((S.radius_limit.pow 2).const_mul B).mul_const (ν.real univ))
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,add_zero] using hh
  have hlower (n : ℕ) : -e n ≤ ⟪P n,l2Star A J α hs ht (P' n)⟫ := by
    have hh := hbound μ ν (S.radius n) (S.radius_pos n)
      (hodgeSmoothingCover A J α hs ht D hD (S.radius n) (S.radius_pos n))
    simp only [P,P',hodgePositiveCurrentFamily,dite_eq_left (S.radius_pos n)]
    dsimp only [e]
    convert hh using 1 <;> first | rfl | ring
  have hν := concentration_residual_source_closed A J α hs ht E hE μ Q S hT
  have henergy (n : ℕ) : ⟪P n,l2Star A J α hs ht (P' n)⟫+⟪P n,V n⟫+⟪P' n,V n⟫+‖V n‖^2 = 0 :=
    hodge_residual_energy_zero A J α hs ht D hD μ ν Q hQ hT hν (S.radius n) (S.radius_pos n)
  exact zero_of_residual_energy_limit V Q (fun n => ⟪P n,l2Star A J α hs ht (P' n)⟫) e
    (fun n => ⟪P n,V n⟫) (fun n => ⟪P' n,V n⟫) hV he hp hp' hlower henergy
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_forces_correction_zero_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.concentration_forces_correction_zero_oai.{u_1}
