-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_second_variation_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:29:31.191244+00:00
-- url     : https://prove2.me/submissions/85c4ce8a-b203-449d-aa8e-245ba5e1fa35

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc025
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_separating_current_euclidean_angular_profile
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_separating_probability_transverse_product_limit

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
lemma rationalKernel_nonneg (r : ℝ) (z : V) : 0 ≤ rationalKernel r z := by
  unfold rationalKernel
  positivity

lemma rationalKernel_deriv {r : ℝ} (hr : 0 < r) (z v : V) :
    fderiv ℝ (rationalKernel r) z v =
      -(6*r^4/(r^2+‖z‖^2)^4)*⟪z,v⟫ := by
  have hd : r^2+‖z‖^2 ≠ 0 := ne_of_gt (by positivity)
  have hh₀ := (hasDerivAt_const (‖z‖^2) (r^4)).div
    (((hasDerivAt_id (‖z‖^2)).const_add (r^2)).pow 3) (pow_ne_zero _ hd)
  have hh := hh₀.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  change HasFDerivAt (rationalKernel r) _ z at hh
  rw [hh.fderiv]
  simp only [smul_apply, smul_eq_mul, Pi.pow_apply, id_eq, innerSL_apply_apply]
  field_simp
  ring

omit [InnerProductSpace ℝ V] in
lemma compact_continuous_bound {W : Type*} [NormedAddCommGroup W]
    (f : V → W) (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C := by
  obtain ⟨C,hC⟩ := hs.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0,le_max_right _ _,fun z => ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact (hC z hz).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz,norm_zero]
    exact le_max_right _ _

lemma cutKernel_deriv {r : ℝ} (hr : 0 < r) (η : V → ℝ) (hη : ContDiff ℝ ∞ η) (z v : V) :
    fderiv ℝ (cutKernel η r) z v =
      (fderiv ℝ η z v)*rationalKernel r z -
        η z*(6*r^4/(r^2+‖z‖^2)^4)*⟪z,v⟫ := by
  have h₁ := ((hη.differentiable (by simp)).differentiableAt (x := z)).hasFDerivAt
  have h₂ := (((rationalKernel_smooth hr).differentiable (by simp)).differentiableAt (x := z)).hasFDerivAt
  change fderiv ℝ (η * rationalKernel r) z v = _
  rw [(h₁.mul h₂).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,
    rationalKernel_deriv hr]
  ring
end TamingCompatibility.Concentration

end
end

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology
namespace TamingCompatibility.Concentration

lemma radialCoefficient_nonneg (r t : ℝ) : 0 ≤ radialCoefficient r t := by
  unfold radialCoefficient
  positivity

end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationCutoff
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
lemma cutKernel_tsupport (η : V → ℝ) (r : ℝ) : tsupport (cutKernel η r) ⊆ tsupport η :=
  tsupport_mul_subset_left

omit [InnerProductSpace ℝ V] in
lemma rationalKernel_away {r a : ℝ} (ha : 0 < a) {z : V} (hz : a ≤ ‖z‖) :
    rationalKernel r z ≤ r^4/a^6 := by
  unfold rationalKernel
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hh : a^2 ≤ r^2+‖z‖^2 := by nlinarith [sq_nonneg r,norm_nonneg z]
  have hp := pow_le_pow_left₀ (sq_nonneg a) hh 3
  simpa only [←pow_mul] using hp

lemma bump_derivative_away_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) {a : ℝ} (ha : 0 < a)
    (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, ∀ z w : V,
      |fderiv ℝ η z w*rationalKernel r z| ≤ C*r^4*‖w‖ := by
  obtain ⟨B,hB,hbound⟩ := compact_continuous_bound (fderiv ℝ η)
    (hη.continuous_fderiv (by simp)) (hηc.fderiv ℝ)
  refine ⟨B/a^6,by positivity,fun r z w => ?_⟩
  by_cases hz : ‖z‖ < a
  · have he : η =ᶠ[𝓝 z] (fun _ => 1) := by
      filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds (gt_mem_nhds hz)] with y hy
      exact hηone y hy
    rw [he.fderiv_eq]
    simp only [fderiv_fun_const]
    change |(0 : ℝ)*rationalKernel r z| ≤ _
    rw [zero_mul,abs_zero]
    positivity
  · have hder : |fderiv ℝ η z w| ≤ B*‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ w).trans (mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg _))
    rw [abs_mul,abs_of_nonneg (rationalKernel_nonneg r z)]
    calc
      _ ≤ (B*‖w‖)*(r^4/a^6) := mul_le_mul hder (rationalKernel_away ha (le_of_not_gt hz))
        (rationalKernel_nonneg r z) (by positivity)
      _ = _ := by ring

lemma cutKernel_deriv_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    {a : ℝ} (ha : 0 < a) (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ z w : V,
      |fderiv ℝ (cutKernel η r) z w| ≤
        6*radialCoefficient r ‖z‖*|inner ℝ z w| + C*r^4*‖w‖ := by
  obtain ⟨C,hC,hbound⟩ := bump_derivative_away_bound η hη hηc ha hηone
  refine ⟨C,hC,fun r hr z w => ?_⟩
  rw [cutKernel_deriv hr η hη]
  have he : 6*r^4/(r^2+‖z‖^2)^4 = 6*radialCoefficient r ‖z‖ := by unfold radialCoefficient; ring
  rw [he]
  have hp : 0 ≤ 6*radialCoefficient r ‖z‖ := mul_nonneg (by norm_num) (radialCoefficient_nonneg _ _)
  have hm : |η z*(6*radialCoefficient r ‖z‖)*inner ℝ z w| ≤
      6*radialCoefficient r ‖z‖*|inner ℝ z w| := by
    rw [abs_mul,abs_mul,abs_of_nonneg (hη0 z),abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hp (hη1 z)) (abs_nonneg _)
  exact (abs_sub _ _).trans (by linarith [hbound r z w])
end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryFrame
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame

lemma wedge_inner (u v a b : V) :
    ⟪wedge u v, wedge a b⟫ = ⟪u, a⟫ * ⟪v, b⟫ - ⟪u, b⟫ * ⟪v, a⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, wedge]
  ring

end TamingCompatibility.UnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_PlaneNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma second_continuousAt {a b : V} (ha : a ≠ 0) (hab : normalPart a b ≠ 0) :
    ContinuousAt (fun p : V × V => second p.1 p.2) (a,b) := by
  change ContinuousAt (first ∘ fun p : V × V => normalPart p.1 p.2) (a,b)
  exact ContinuousAt.comp (x := (a,b))
    (g := first) (f := fun p : V × V => normalPart p.1 p.2)
    (first_continuousAt hab) (normalPart_continuousAt (b := b) ha)

end TamingCompatibility.PlaneVariation

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FourthMomentKernel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.antiEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Bundle Set TopologicalSpace
lemma bundle_totalSpace_secondCountable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [SecondCountableTopology B] [SecondCountableTopology F] (E : B → Type*)
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E] :
    SecondCountableTopology (TotalSpace F E) := by
  let e : B → Trivialization F (π F E) := fun b => trivializationAt F E b
  obtain ⟨s,hsc,hs⟩ := isOpen_iUnion_countable (fun b => (e b).baseSet) (fun b => (e b).open_baseSet)
  have hcover : (⋃ b : B, (e b).baseSet) = univ := by
    apply eq_univ_iff_forall.mpr
    intro b
    exact mem_iUnion.mpr ⟨b,mem_baseSet_trivializationAt F E b⟩
  rw [hcover] at hs
  let := hsc.to_subtype
  let U : s → Set (TotalSpace F E) := fun b => (e b.val).source
  have (b : s) : SecondCountableTopology (U b) :=
    (e b.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply secondCountableTopology_of_countable_cover (U := U) (fun b => (e b.val).open_source)
  apply eq_univ_iff_forall.mpr
  intro v
  have hv : v.proj ∈ ⋃ b ∈ s, (e b).baseSet := hs.symm ▸ mem_univ _
  obtain ⟨b,hb,hv⟩ := mem_iUnion₂.mp hv
  exact mem_iUnion.mpr ⟨⟨b,hb⟩,(e b).mem_source.mpr hv⟩
namespace TamingCompatibility
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [SecondCountableTopology X]
lemma unitSecondCountable (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type)) :
    SecondCountableTopology (MetricUnit g) := by
  have : SecondCountableTopology (TangentBundle Model X) :=
    bundle_totalSpace_secondCountable (TangentSpace Model : X → Type)
  exact TopologicalSpace.Subtype.secondCountableTopology {p : TangentBundle Model X | g.inner p.proj p.2 p.2 = 1}
end TamingCompatibility

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_RationalKernelCompare
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma norm_skew_sq (a b w : V) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    ‖skew a b w‖^2 = ⟪a,w⟫^2+⟪b,w⟫^2 := by
  have hba : ⟪b,a⟫ = 0 := (real_inner_comm _ _).trans hab
  rw [← real_inner_self_eq_norm_sq]
  simp only [skew,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,ha,hb,hab,hba,one_pow]
  ring

lemma norm_transverse_sq (u v z : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    ‖transverse u v z‖^2 = ‖z‖^2-⟪u,z⟫^2-⟪v,z⟫^2 := by
  have hvu : ⟪v,u⟫ = 0 := (real_inner_comm _ _).trans huv
  rw [← real_inner_self_eq_norm_sq]
  simp only [transverse,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hu,hv,huv,hvu,
    real_inner_comm z u,real_inner_comm z v,one_pow]
  ring

lemma norm_skew_le (a b w : V) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    ‖skew a b w‖ ≤ ‖w‖ := by
  have hh := norm_skew_sq a b w ha hb hab
  have ht := norm_transverse_sq a b w ha hb hab
  nlinarith [sq_nonneg ‖transverse a b w‖,norm_nonneg w,norm_nonneg (skew a b w)]

lemma skew_orthogonal (a b w : V) : ⟪w,skew a b w⟫ = 0 := by
  simp only [skew,inner_sub_right,real_inner_smul_right,real_inner_comm w a,real_inner_comm w b]
  ring

lemma inner_skew (u v a b : V) : ⟪u,skew a b v⟫ = detInner u v a b := by
  simp only [skew,inner_sub_right,real_inner_smul_right,detInner,real_inner_comm b v,real_inner_comm a v]
  ring

lemma first_variation_bound (u v a b z : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    |⟪z,u-skew a b v⟫| ≤
      (1-detInner u v a b)*‖z‖ +
        Real.sqrt (2*(1-detInner u v a b))*‖transverse u v z‖ := by
  let e := u-skew a b v
  have hesq : ‖e‖^2 ≤ 2*(1-detInner u v a b) := by
    have hh := norm_skew_le a b v ha hb hab
    rw [hv] at hh
    have heq : ‖e‖^2 = 1+‖skew a b v‖^2-2*detInner u v a b := by
      dsimp [e]
      rw [norm_sub_sq_real,hu,inner_skew]
      ring
    nlinarith [norm_nonneg (skew a b v)]
  have hd : 0 ≤ 1-detInner u v a b := by nlinarith [sq_nonneg ‖e‖]
  have hen : ‖e‖ ≤ Real.sqrt (2*(1-detInner u v a b)) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hesq
  have heu : ⟪u,e⟫ = 1-detInner u v a b := by
    simp only [e,inner_sub_right,real_inner_self_eq_norm_sq,hu,one_pow,inner_skew]
  have hev : ⟪v,e⟫ = 0 := by
    rw [show e = u-skew a b v from rfl,inner_sub_right,skew_orthogonal,sub_zero,real_inner_comm,huv]
  have heq : ⟪z,e⟫ = ⟪u,z⟫*(1-detInner u v a b)+⟪transverse u v z,e⟫ := by
    simp only [transverse,inner_sub_left,real_inner_smul_left,heu,hev,mul_zero,sub_zero]
    ring
  calc
    |⟪z,e⟫| ≤ |⟪u,z⟫*(1-detInner u v a b)|+|⟪transverse u v z,e⟫| := by
      rw [heq]; exact abs_add_le _ _
    _ ≤ ‖z‖*(1-detInner u v a b)+‖transverse u v z‖*‖e‖ := by
      apply add_le_add
      · rw [abs_mul,abs_of_nonneg hd]
        have hh := abs_real_inner_le_norm u z
        rw [hu,one_mul] at hh
        exact mul_le_mul_of_nonneg_right hh hd
      · exact abs_real_inner_le_norm _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hen (norm_nonneg (transverse u v z))
      nlinarith
end TamingCompatibility.PlaneVariation

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PlaneTransverseGraph
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
open RadialPotential
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma transverse_sub (u v z w : V) :
    transverse u v (z-w) = transverse u v z - transverse u v w := by
  simp only [transverse,inner_sub_right,sub_smul]
  abel

lemma transverse_smul (u v z : V) (c : ℝ) :
    transverse u v (c • z) = c • transverse u v z := by
  simp only [transverse,real_inner_smul_right,smul_sub,smul_smul]

lemma norm_transverse_le (u v z : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    ‖transverse u v z‖ ≤ ‖z‖ := by
  have hh := norm_transverse_sq u v z hu hv huv
  nlinarith [sq_nonneg ⟪u,z⟫,sq_nonneg ⟪v,z⟫,norm_nonneg (transverse u v z),norm_nonneg z]

end TamingCompatibility.PlaneVariation

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

omit [CompactSpace X] [T2Space X] in
lemma unitChartFirst_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartFirst J α hs ht p) (unitChartDomain J α hs ht p K) := by
  intro u hu
  exact (first_continuousAt (unitChartVector_ne_zero J α hs ht p u
    (unitChart_mem J α hs ht p hKT hu).1)).comp_continuousWithinAt
      ((unitChartVector_continuousOn J α hs ht p hKT) u hu)

omit [CompactSpace X] [T2Space X] in
lemma unitChartSecond_continuousOn (p : X) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p).target) :
    ContinuousOn (unitChartSecond J α hs ht p) (unitChartDomain J α hs ht p K) := by
  intro u hu
  have ha := unitChartVector_ne_zero J α hs ht p u (unitChart_mem J α hs ht p hKT hu).1
  have hab := normalPart_complex_ne_zero _ (coordinateJ_square J p
    (hKT (unitChart_mem J α hs ht p hKT hu).2)) ha
  apply ContinuousAt.comp_continuousWithinAt
    (f := fun v => (unitChartVector J α hs ht p v,unitChartJVector J α hs ht p v))
    (second_continuousAt ha hab)
  exact     (((unitChartVector_continuousOn J α hs ht p hKT) u hu).prodMk
      ((unitChartJVector_continuousOn J α hs ht p hKT) u hu))

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.ManifoldLocalization.globalL2_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedSpace
lemma source_subset : D.source ⊆ (extChartAt Model p).source := Set.inter_subset_left

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_ConcentrationChart
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian NormalMetricCalculus CoordinateOperator
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}

namespace ParametrixData

omit [T2Space X] [CompactSpace X] in
lemma concentrationCompact_center (D : ParametrixData J α ht p) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) : q ∈ D.concentrationCompact := by
  have hx : (q,0) ∈ D.normalCompact := ⟨hq,Metric.mem_closedBall_self D.radius_pos.le⟩
  have he : D.normalChart (q,0) = (q,q) := by
    change (q,normalMap D.metricExtension D.frameExtension q 0) = (q,q)
    rw [normalMap_zero]
  exact Or.inl ⟨(q,q),⟨(q,0),hx,he⟩,rfl⟩

end ParametrixData

attribute [local instance] unitMeasurable unitBorel unitSecondCountable

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_BoundedMassLimit
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open _root_.MeasureTheory Filter
open scoped Topology ENNReal
namespace TamingCompatibility
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma sqrt_memLp_two (f : Ω → ℝ) (hi : Integrable f μ) (hp : ∀ x, 0 ≤ f x) :
    MemLp (fun x => Real.sqrt (f x)) 2 μ := by
  rw [memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable)]
  simpa only [Real.sq_sqrt (hp _)] using hi

lemma integral_sqrt_mul_sqrt_le (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfp : ∀ x, 0 ≤ f x) (hgp : ∀ x, 0 ≤ g x) :
    (∫ x, Real.sqrt (f x)*Real.sqrt (g x) ∂μ) ≤
      Real.sqrt (∫ x, f x ∂μ)*Real.sqrt (∫ x, g x ∂μ) := by
  have hf' := sqrt_memLp_two f hf hfp
  have hg' := sqrt_memLp_two g hg hgp
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ fun x => Real.sqrt_nonneg (f x)) (ae_of_all μ fun x => Real.sqrt_nonneg (g x))
    (show MemLp (fun x => Real.sqrt (f x)) (ENNReal.ofReal (2:ℝ)) μ by simpa using hf')
    (show MemLp (fun x => Real.sqrt (g x)) (ENNReal.ofReal (2:ℝ)) μ by simpa using hg')
  simp only [Real.rpow_two,Real.sq_sqrt (hfp _),Real.sq_sqrt (hgp _)] at hh
  simpa only [Real.sqrt_eq_rpow,one_div] using hh

end TamingCompatibility

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_WedgeTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.UnitaryFrame
open FormMetric

lemma norm_wedge_orthonormal (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    ‖wedge u v‖ = 1 := by
  have h := wedge_inner u v u v
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    hu,hv,huv,zero_mul,sub_zero,one_pow,mul_one] at h
  nlinarith [norm_nonneg (wedge u v)]

end TamingCompatibility.UnitaryFrame

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeManifoldKernelExtension
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldKernelExtension
open Set Filter
open scoped Manifold Topology
variable {E X G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X]
  [NormedAddCommGroup G]
attribute [local instance] Classical.propDecidable
local notation "I" => 𝓘(ℝ,E)

lemma liftSet_source (p : X) (K : Set (E × E))
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    liftSet p K ⊆ (extChartAt I p).source ×ˢ (extChartAt I p).source := by
  rintro x ⟨z,hz,rfl⟩
  exact ⟨(extChartAt I p).map_target (hK hz).1,(extChartAt I p).map_target (hK hz).2⟩

lemma liftSet_compact (p : X) (K : Set (E × E)) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    IsCompact (liftSet p K) := by
  apply hc.image_of_continuousOn
  exact ((continuousOn_extChartAt_symm p).comp continuousOn_fst (fun z hz => (hK hz).1)).prodMk
    ((continuousOn_extChartAt_symm p).comp continuousOn_snd (fun z hz => (hK hz).2))

end TamingCompatibility.ManifoldKernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalParametrix
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] Classical.propDecidable

omit [T2Space X] [CompactSpace X] in
lemma physicalCompact_target (p : A.centers) :
    (D p).physicalCompact ⊆ (extChartAt Model p.val).target ×ˢ (extChartAt Model p.val).target :=
  fun _ hz => ⟨(D p).chart.domain_subset ((D p).physicalCompact_domain hz).1,
    (D p).chart.domain_subset ((D p).physicalCompact_domain hz).2⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] in
lemma angularBase_continuous : Continuous (angularBase J α hs ht) := by
  have hb : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  exact (hb.comp continuous_snd).prodMk (hb.comp continuous_fst)

omit [CompactSpace X] in
lemma angularDomain_closed (p : A.centers) : _root_.IsClosed (angularDomain A J α hs ht E p) :=
  ((ManifoldKernelExtension.liftSet_compact p.val _ (E p).physicalCompact_compact
    (physicalCompact_target J α ht A E p)).isClosed).preimage (angularBase_continuous J α hs ht)

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_mem (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    angularChartCoordinates A J α hs ht p uv ∈ (E p).physicalCompact := by
  obtain ⟨w,hw,he⟩ := huv
  have he' := congrArg (fun xy : X × X => (extChartAt Model p.val xy.1,extChartAt Model p.val xy.2)) he
  have ht' := physicalCompact_target J α ht A E p hw
  simp only [(extChartAt Model p.val).right_inv ht'.1,(extChartAt Model p.val).right_inv ht'.2] at he'
  change w = angularChartCoordinates A J α hs ht p uv at he'
  rw [← he']
  exact hw

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_source (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    uv.2.val.proj ∈ (extChartAt Model p.val).source ∧ uv.1.val.proj ∈ (extChartAt Model p.val).source :=
  ManifoldKernelExtension.liftSet_source p.val _ (physicalCompact_target J α ht A E p) huv

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_continuousOn (p : A.centers) :
    ContinuousOn (angularChartCoordinates A J α hs ht p) (angularDomain A J α hs ht E p) := by
  have hb := angularBase_continuous J α hs ht
  exact ((continuousOn_extChartAt p.val).comp hb.fst.continuousOn
      (fun _ h => (angularChartCoordinates_source A J α hs ht E p h).1)).prodMk
    ((continuousOn_extChartAt p.val).comp hb.snd.continuousOn
      (fun _ h => (angularChartCoordinates_source A J α hs ht E p h).2))

attribute [local instance] unitMeasurable unitBorel unitSecondCountable

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanAngularDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)

omit [CompactSpace X] [T2Space X] in
lemma euclideanLine_continuousOn (p : A.centers) :
    ContinuousOn (fun uv : UnitPair J α hs ht =>
      euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2)
      (angularDomain A J α hs ht E p) := by
  let K := Prod.fst '' (E p).physicalCompact ∪ Prod.snd '' (E p).physicalCompact
  have hKt : K ⊆ (extChartAt Model p.val).target := by
    rintro y (⟨xy,hxy,rfl⟩ | ⟨xy,hxy,rfl⟩)
    · exact ((E p).chart.domain_subset ((E p).physicalCompact_domain hxy).1)
    · exact ((E p).chart.domain_subset ((E p).physicalCompact_domain hxy).2)
  have hb : ContinuousOn (fun u : MetricUnit (hermitianMetric J α hs ht) =>
      euclideanLine A J α hs ht p u) (unitChartDomain J α hs ht p.val K) := by
    intro u hu
    have hsrc := (unitChart_mem J α hs ht p.val hKt hu).1
    have hn := unitChartVector_ne_zero J α hs ht p.val u hsrc
    have hn' := normalPart_complex_ne_zero _
      (coordinateJ_square J p.val ((extChartAt Model p.val).map_source hsrc)) hn
    have h1 := (unitChartVector_continuousOn J α hs ht p.val hKt u hu)
    have h2 := (unitChartJVector_continuousOn J α hs ht p.val hKt u hu)
    have hf := (first_continuousAt hn).comp_continuousWithinAt h1
    have hsc : ContinuousAt (fun v : Space × Space => second v.1 v.2)
        (unitChartVector J α hs ht p.val u,unitChartJVector J α hs ht p.val u) := second_continuousAt hn hn'
    have hg := ContinuousAt.comp_continuousWithinAt (x := u)
      (g := fun v : Space × Space => second v.1 v.2)
      (f := fun u => (unitChartVector J α hs ht p.val u,unitChartJVector J α hs ht p.val u)) hsc (h1.prodMk h2)
    have hw : Continuous (fun ab : Space × Space => wedge ab.1 ab.2) := by
      unfold wedge
      fun_prop
    exact ContinuousAt.comp_continuousWithinAt (x := u)
      (g := fun ab : Space × Space => wedge ab.1 ab.2)
      (f := fun v => (unitChartFirst J α hs ht p.val v,unitChartSecond J α hs ht p.val v))
      hw.continuousAt (hf.prodMk hg)
  have hf : MapsTo Prod.fst (angularDomain A J α hs ht E p) (unitChartDomain J α hs ht p.val K) := by
    intro uv huv
    have hxy := angularChartCoordinates_mem A J α hs ht E p huv
    have hsrc := (angularChartCoordinates_source A J α hs ht E p huv).2
    exact ⟨unitChartBase J α hs ht p.val uv.1,Or.inr ⟨_,hxy,rfl⟩,(extChartAt Model p.val).left_inv hsrc⟩
  have hg : MapsTo Prod.snd (angularDomain A J α hs ht E p) (unitChartDomain J α hs ht p.val K) := by
    intro uv huv
    have hxy := angularChartCoordinates_mem A J α hs ht E p huv
    have hsrc := (angularChartCoordinates_source A J α hs ht E p huv).1
    exact ⟨unitChartBase J α hs ht p.val uv.2,Or.inl ⟨_,hxy,rfl⟩,(extChartAt Model p.val).left_inv hsrc⟩
  exact (hb.comp continuous_fst.continuousOn hf).sub (hb.comp continuous_snd.continuousOn hg)

omit [CompactSpace X] [T2Space X] in
lemma euclideanAngularWeight_nonneg (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ euclideanAngularWeight A J α hs ht p uv :=
  mul_nonneg (A.partition.nonneg _ _) (sq_nonneg _)

omit [CompactSpace X] [T2Space X] in
lemma euclideanAngularWeight_continuousOn (p : A.centers) :
    ContinuousOn (euclideanAngularWeight A J α hs ht p) (angularDomain A J α hs ht E p) :=
  (((A.partition p).property.continuous.comp (angularBase_continuous J α hs ht).fst).continuousOn).mul
    ((euclideanLine_continuousOn A J α hs ht E p).norm.pow 2)

attribute [local instance] unitMeasurable unitBorel unitSecondCountable

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanAngularNearPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
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
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma euclideanLine_norm (p : A.centers) (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source) : ‖euclideanLine A J α hs ht p u‖ = 1 := by
  obtain ⟨h1,h2,h3,_⟩ := unitChartPlane J α hs ht p.val u hu
  exact norm_wedge_orthonormal _ _ h1 h2 h3

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
lemma euclideanAngularWeight_le (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) : euclideanAngularWeight A J α hs ht p uv ≤ 4 := by
  have hsrc := angularChartCoordinates_source A J α hs ht E p huv
  have hh := norm_sub_le (euclideanLine A J α hs ht p uv.1) (euclideanLine A J α hs ht p uv.2)
  rw [euclideanLine_norm A J α hs ht p uv.1 hsrc.2,euclideanLine_norm A J α hs ht p uv.2 hsrc.1] at hh
  have hsq : ‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2 ≤ 4 := by
    nlinarith [norm_nonneg (euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2)]
  exact (mul_le_mul_of_nonneg_left hsq (A.partition.nonneg p uv.2.val.proj)).trans
    (by have h := A.partition.le_one p uv.2.val.proj; nlinarith)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactProfilePoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.Concentration
lemma sum_six_le (r t : ℝ) : (r+t)^6 ≤ 8*(r^2+t^2)^3 := by
  have h₁ : (r+t)^2 ≤ 2*(r^2+t^2) := by nlinarith [sq_nonneg (r-t)]
  have hh := pow_le_pow_left₀ (sq_nonneg (r+t)) h₁ 3
  calc
    (r+t)^6 = ((r+t)^2)^3 := by ring
    _ ≤ (2*(r^2+t^2))^3 := hh
    _ = _ := by ring

lemma radialCoefficient_profile {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    radialCoefficient r t ≤ (8/r^4)*((1+t/r)⁻¹)^6 := by
  have hs : 0 < r^2+t^2 := by positivity
  have hrt : 0 < r+t := by positivity
  have he : ((1+t/r)⁻¹)^6 = r^6/(r+t)^6 := by
    field_simp
  rw [he,radialCoefficient]
  have he' : (8/r^4)*(r^6/(r+t)^6) = 8*r^2/(r+t)^6 := by field_simp
  rw [he']
  apply (div_le_div_iff₀ (pow_pos hs 4) (pow_pos hrt 6)).mpr
  have hsmall : r^2 ≤ r^2+t^2 := by nlinarith [sq_nonneg t]
  have hmult := mul_le_mul_of_nonneg_left (sum_six_le r t) (by positivity : 0 ≤ r^2)
  have hbig := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 8*(r^2+t^2)^3)
  have h := mul_le_mul_of_nonneg_left (hmult.trans hbig) (by positivity : 0 ≤ r^2)
  nlinarith

lemma radialCoefficient_linear_profile {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    radialCoefficient r t*t ≤ (8/r^3)*((1+t/r)⁻¹)^6 := by
  have hs : 0 < r^2+t^2 := by positivity
  have hrt : 0 < r+t := by positivity
  have he : ((1+t/r)⁻¹)^6 = r^6/(r+t)^6 := by
    field_simp
  rw [he,radialCoefficient]
  have he' : (8/r^3)*(r^6/(r+t)^6) = 8*r^3/(r+t)^6 := by field_simp
  rw [he',div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (pow_pos hs 4) (pow_pos hrt 6)).mpr
  have hsmall : r*t ≤ r^2+t^2 := by nlinarith [sq_nonneg (r-t)]
  have hmult := mul_le_mul_of_nonneg_left (sum_six_le r t) (by positivity : 0 ≤ r*t)
  have hbig := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 8*(r^2+t^2)^3)
  have h := mul_le_mul_of_nonneg_left (hmult.trans hbig) (by positivity : 0 ≤ r^3)
  nlinarith
lemma radialCoefficient_quadratic_profile {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    radialCoefficient r t*t^2 ≤ (8/r^2)*((1+t/r)⁻¹)^6 := by
  have hs : 0 < r^2+t^2 := by positivity
  have hrt : 0 < r+t := by positivity
  have he : ((1+t/r)⁻¹)^6 = r^6/(r+t)^6 := by field_simp
  rw [he,radialCoefficient]
  have he' : (8/r^2)*(r^6/(r+t)^6) = 8*r^4/(r+t)^6 := by field_simp
  rw [he',div_mul_eq_mul_div]
  apply (div_le_div_iff₀ (pow_pos hs 4) (pow_pos hrt 6)).mpr
  have hsmall : t^2 ≤ r^2+t^2 := by nlinarith [sq_nonneg r]
  have hmult := mul_le_mul_of_nonneg_left (sum_six_le r t) (by positivity : 0 ≤ t^2)
  have hbig := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 8*(r^2+t^2)^3)
  have h := mul_le_mul_of_nonneg_left (hmult.trans hbig) (by positivity : 0 ≤ r^4)
  nlinarith
end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FourthWeightedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
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
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] [CompactSpace X] in
lemma euclideanAngularGlobal_measurable (p : A.centers) : Measurable (euclideanAngularGlobal A J α hs ht E p) := by
  classical
  exact (euclideanAngularWeight_continuousOn A J α hs ht E p).measurable_piecewise continuousOn_const
    (angularDomain_closed A J α hs ht E p).measurableSet

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] [CompactSpace X] in
lemma euclideanDistanceGlobal_measurable (p : A.centers) : Measurable (euclideanDistanceGlobal A J α hs ht E p) := by
  classical
  exact ((angularChartCoordinates_continuousOn A J α hs ht E p).snd.sub
    (angularChartCoordinates_continuousOn A J α hs ht E p).fst).norm.measurable_piecewise continuousOn_const
    (angularDomain_closed A J α hs ht E p).measurableSet

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology
namespace TamingCompatibility.Concentration
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma profile_six_le_one {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) :
    ((1+t/r)⁻¹)^6 ≤ 1 := by
  apply pow_le_one₀ (by positivity)
  apply inv_le_one_of_one_le₀
  have hh := div_nonneg ht hr.le
  linarith

lemma weighted_profile_integrable (w d : Ω → ℝ) (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ x, 0 ≤ w x) (hd0 : ∀ x, 0 ≤ d x) (hi : Integrable w μ)
    {r : ℝ} (hr : 0 < r) : Integrable (fun x => w x*((1+d x/r)⁻¹)^6) μ := by
  apply hi.mono' ((hw.mul ((measurable_const.add (hd.div_const r)).inv.pow_const 6)).aestronglyMeasurable)
  apply ae_of_all
  intro x
  change ‖w x*((1+d x/r)⁻¹)^6‖ ≤ w x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw0 x) (by positivity))]
  exact mul_le_of_le_one_right (hw0 x) (profile_six_le_one hr (hd0 x))

lemma weighted_radial_integrable (w d : Ω → ℝ) (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ x, 0 ≤ w x) (hd0 : ∀ x, 0 ≤ d x) (hi : Integrable w μ)
    {r : ℝ} (hr : 0 < r) : Integrable (fun x => w x*radialCoefficient r (d x)) μ := by
  have hm : Measurable (fun x => w x*radialCoefficient r (d x)) :=
    hw.mul (measurable_const.div ((measurable_const.add (hd.pow_const 2)).pow_const 4))
  apply ((weighted_profile_integrable w d hw hd hw0 hd0 hi hr).const_mul (8/r^4)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hw0 x) (radialCoefficient_nonneg _ _))]
  calc
    _ ≤ w x*((8/r^4)*((1+d x/r)⁻¹)^6) := mul_le_mul_of_nonneg_left
      (radialCoefficient_profile hr (hd0 x)) (hw0 x)
    _ = _ := by ring

lemma weighted_radial_linear_integrable (w d : Ω → ℝ) (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ x, 0 ≤ w x) (hd0 : ∀ x, 0 ≤ d x) (hi : Integrable w μ)
    {r : ℝ} (hr : 0 < r) : Integrable (fun x => w x*radialCoefficient r (d x)*d x) μ := by
  have hm : Measurable (fun x => w x*radialCoefficient r (d x)*d x) :=
    (hw.mul (measurable_const.div ((measurable_const.add (hd.pow_const 2)).pow_const 4))).mul hd
  apply ((weighted_profile_integrable w d hw hd hw0 hd0 hi hr).const_mul (8/r^3)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (mul_nonneg (hw0 x) (radialCoefficient_nonneg _ _)) (hd0 x))]
  calc
    _ = w x*(radialCoefficient r (d x)*d x) := by ring
    _ ≤ w x*((8/r^3)*((1+d x/r)⁻¹)^6) := mul_le_mul_of_nonneg_left
      (radialCoefficient_linear_profile hr (hd0 x)) (hw0 x)
    _ = _ := by ring

lemma weighted_radial_estimates (w d : Ω → ℝ) (hw : Measurable w) (hd : Measurable d)
    (hw0 : ∀ x, 0 ≤ w x) (hd0 : ∀ x, 0 ≤ d x) (hi : Integrable w μ)
    {C r : ℝ} (hr : 0 < r)
    (hbound : (∫ x, w x*((1+d x/r)⁻¹)^6 ∂μ) ≤ C*r^4) :
    (∫ x, w x*radialCoefficient r (d x) ∂μ) ≤ 8*C ∧
    (∫ x, w x*radialCoefficient r (d x)*d x ∂μ) ≤ 8*C*r := by
  have hp := weighted_profile_integrable w d hw hd hw0 hd0 hi hr
  constructor
  · calc
      _ ≤ ∫ x, (8/r^4)*(w x*((1+d x/r)⁻¹)^6) ∂μ := integral_mono
        (weighted_radial_integrable w d hw hd hw0 hd0 hi hr) (hp.const_mul _) (fun x => by
          have hh := mul_le_mul_of_nonneg_left (radialCoefficient_profile hr (hd0 x)) (hw0 x)
          nlinarith)
      _ = (8/r^4)*(∫ x, w x*((1+d x/r)⁻¹)^6 ∂μ) := integral_const_mul _ _
      _ ≤ (8/r^4)*(C*r^4) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 8*C := by field_simp
  · calc
      _ ≤ ∫ x, (8/r^3)*(w x*((1+d x/r)⁻¹)^6) ∂μ := integral_mono
        (weighted_radial_linear_integrable w d hw hd hw0 hd0 hi hr) (hp.const_mul _) (fun x => by
          have hh := mul_le_mul_of_nonneg_left (radialCoefficient_linear_profile hr (hd0 x)) (hw0 x)
          nlinarith)
      _ = (8/r^3)*(∫ x, w x*((1+d x/r)⁻¹)^6 ∂μ) := integral_const_mul _ _
      _ ≤ (8/r^3)*(C*r^4) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 8*C*r := by field_simp
end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanAngularRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory Filter
open Hermitian UnitaryFrame PlaneVariation Concentration
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
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
lemma euclideanAngularGlobal_nonneg (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ euclideanAngularGlobal A J α hs ht E p uv :=
  indicator_nonneg (fun v _ => euclideanAngularWeight_nonneg A J α hs ht p v) uv

omit [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
lemma euclideanDistanceGlobal_nonneg (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ euclideanDistanceGlobal A J α hs ht E p uv := indicator_nonneg (fun _ _ => norm_nonneg _) uv

omit [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma euclideanAngularGlobal_integrable (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    [IsFiniteMeasure μ] (p : A.centers) : Integrable (euclideanAngularGlobal A J α hs ht E p) (μ.prod μ) := by
  apply (integrable_const (4:ℝ)).mono'
    (euclideanAngularGlobal_measurable A J α hs ht E p).aestronglyMeasurable
  apply ae_of_all
  intro uv
  rw [Real.norm_eq_abs,abs_of_nonneg (euclideanAngularGlobal_nonneg A J α hs ht E p uv)]
  by_cases huv : uv ∈ angularDomain A J α hs ht E p
  · exact (indicator_of_mem huv _).le.trans (euclideanAngularWeight_le A J α hs ht E p huv)
  · simp only [euclideanAngularGlobal,indicator_of_notMem huv] <;> norm_num

include hE hD in
lemma separating_current_euclidean_radial_angular
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      (∫ uv, euclideanAngularGlobal A J α hs ht E p uv *
        radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv) ∂μ.prod μ) ≤ C ∧
      (∫ uv, euclideanAngularGlobal A J α hs ht E p uv *
        radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv)*
          euclideanDistanceGlobal A J α hs ht E p uv ∂μ.prod μ) ≤ C*r := by
  obtain ⟨C,hC,hbound⟩ := separating_current_euclidean_angular_profile A J α hs ht E hE D hD μ hann p
  refine ⟨8*C,by positivity,fun r hr => ?_⟩
  exact weighted_radial_estimates _ _
    (euclideanAngularGlobal_measurable A J α hs ht E p)
    (euclideanDistanceGlobal_measurable A J α hs ht E p)
    (euclideanAngularGlobal_nonneg A J α hs ht E p)
    (euclideanDistanceGlobal_nonneg A J α hs ht E p)
    (euclideanAngularGlobal_integrable A J α hs ht E μ p) hr (hbound r hr)

include hE hD in
lemma separating_current_euclidean_radial_linear_limit
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    Tendsto (fun r : ℝ => ∫ uv, euclideanAngularGlobal A J α hs ht E p uv *
        radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv)*
          euclideanDistanceGlobal A J α hs ht E p uv ∂μ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,_,hbound⟩ := separating_current_euclidean_radial_angular A J α hs ht E hE D hD μ hann p
  apply squeeze_zero' (Eventually.of_forall fun r => integral_nonneg fun uv => mul_nonneg
    (mul_nonneg (euclideanAngularGlobal_nonneg A J α hs ht E p uv) (radialCoefficient_nonneg _ _))
    (euclideanDistanceGlobal_nonneg A J α hs ht E p uv))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hbound r hr).2
  · simpa only [mul_zero] using tendsto_const_nhds.mul
      (show Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) from nhdsWithin_le_nhds)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PlaneFirstVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma detInner_comm (u v a b : V) : detInner u v a b = detInner a b u v := by
  simp only [detInner,real_inner_comm u a,real_inner_comm v b,real_inner_comm u b,real_inner_comm v a]
  ring

lemma detInner_le_one (u v a b : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    detInner u v a b ≤ 1 := by
  rw [← inner_skew]
  have hh := real_inner_le_norm u (skew a b v)
  have hh' := norm_skew_le a b v ha hb hab
  rw [hu,one_mul] at hh
  rw [hv] at hh'
  exact hh.trans hh'

lemma skew_error_norm (u v a b : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    ‖u-skew a b v‖ ≤ Real.sqrt (2*(1-detInner u v a b)) := by
  have hh := norm_skew_le a b v ha hb hab
  rw [hv] at hh
  apply (Real.le_sqrt (norm_nonneg _) (by linarith [detInner_le_one u v a b hu hv ha hb hab])).mpr
  rw [norm_sub_sq_real,hu,inner_skew]
  nlinarith [norm_nonneg (skew a b v)]

lemma transverse_skew (u v w : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    transverse u v (skew u v w) = 0 := by
  have hvu : ⟪v,u⟫ = 0 := (real_inner_comm _ _).trans huv
  simp only [transverse,skew,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
    hu,hv,huv,hvu,one_pow,mul_one,mul_zero,sub_zero,zero_sub,neg_smul]
  abel

lemma norm_transverse_comparison (u v a b z : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖transverse u v z‖ ≤ ‖transverse a b z‖ +
      2*Real.sqrt (2*(1-detInner u v a b))*‖z‖ := by
  let δ := Real.sqrt (2*(1-detInner u v a b))
  have hpa : ‖transverse u v a‖ ≤ δ := by
    have he : transverse u v a = transverse u v (a-skew u v b) := by
      rw [transverse_sub,transverse_skew u v b hu hv huv,sub_zero]
    rw [he]
    exact (norm_transverse_le u v _ hu hv huv).trans
      ((skew_error_norm a b u v ha hb hu hv huv).trans_eq (by rw [detInner_comm]))
  have hpb : ‖transverse u v b‖ ≤ δ := by
    have he : transverse u v b = transverse u v (b-skew v u a) := by
      have he' : skew v u a = -skew u v a := by simp only [skew]; abel
      rw [transverse_sub,he',show -skew u v a = (-1:ℝ) • skew u v a by simp,
        transverse_smul,transverse_skew u v a hu hv huv,smul_zero,sub_zero]
    rw [he]
    apply (norm_transverse_le u v _ hu hv huv).trans
    have hh := skew_error_norm b a v u hb ha hv hu ((real_inner_comm _ _).trans huv)
    simpa only [δ,detInner,real_inner_comm b v,real_inner_comm a u,real_inner_comm b u,real_inner_comm a v,
      mul_comm] using hh
  have he : transverse u v z = transverse u v (transverse a b z) +
      ⟪a,z⟫ • transverse u v a + ⟪b,z⟫ • transverse u v b := by
    simp only [transverse,inner_sub_right,inner_smul_right,
      sub_smul,smul_sub,smul_smul]
    module
  have hac : |⟪a,z⟫| ≤ ‖z‖ := by simpa only [ha,one_mul] using abs_real_inner_le_norm a z
  have hbc : |⟪b,z⟫| ≤ ‖z‖ := by simpa only [hb,one_mul] using abs_real_inner_le_norm b z
  calc
    _ ≤ ‖transverse u v (transverse a b z)‖ + ‖⟪a,z⟫ • transverse u v a‖ +
        ‖⟪b,z⟫ • transverse u v b‖ := by rw [he]; exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖transverse a b z‖ + ‖z‖*δ + ‖z‖*δ := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (add_le_add (norm_transverse_le u v _ hu hv huv)
        (mul_le_mul hac hpa (norm_nonneg _) (norm_nonneg _)))
        (mul_le_mul hbc hpb (norm_nonneg _) (norm_nonneg _))
    _ = _ := by dsimp [δ] <;> ring

lemma first_variation_source_bound (u v a b z : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    |⟪z,u-skew a b v⟫| ≤
      5*(1-detInner u v a b)*‖z‖ +
        Real.sqrt (2*(1-detInner u v a b))*‖transverse a b z‖ := by
  have h₁ := first_variation_bound u v a b z hu hv huv ha hb hab
  have h₂ := mul_le_mul_of_nonneg_left (norm_transverse_comparison u v a b z hu hv huv ha hb)
    (Real.sqrt_nonneg (2*(1-detInner u v a b)))
  have hsq := Real.sq_sqrt (show 0 ≤ 2*(1-detInner u v a b) by linarith [detInner_le_one u v a b hu hv ha hb hab])
  have hmul := congrArg (fun t : ℝ => t*‖z‖) hsq
  nlinarith
end TamingCompatibility.PlaneVariation

namespace TamingCompatibility.UnitaryFrame
open PlaneVariation
lemma first_variation_wedge_bound (u v a b z : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    |⟪z,u-skew a b v⟫| ≤
      (5/2:ℝ)*‖wedge u v-wedge a b‖^2*‖z‖ +
        ‖wedge u v-wedge a b‖*‖transverse a b z‖ := by
  have he : ‖wedge u v-wedge a b‖^2 = 2*(1-detInner u v a b) := by
    rw [norm_sub_sq_real,norm_wedge_orthonormal u v hu hv huv,
      norm_wedge_orthonormal a b ha hb hab,wedge_inner]
    unfold detInner
    ring
  have hroot : Real.sqrt (2*(1-detInner u v a b)) = ‖wedge u v-wedge a b‖ := by
    rw [← he,Real.sqrt_sq (norm_nonneg _)]
  have hh := first_variation_source_bound u v a b z hu hv huv ha hb hab
  rw [hroot] at hh
  have hmul := congrArg (fun t : ℝ => t*‖z‖) he
  nlinarith
end TamingCompatibility.UnitaryFrame

end
end

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.Concentration
open PlaneVariation UnitaryFrame
lemma cutKernel_plane_variation_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    {a : ℝ} (ha : 0 < a) (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ u v b c z : V,
      ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      ‖b‖ = 1 → ‖c‖ = 1 → inner ℝ b c = 0 →
      |fderiv ℝ (cutKernel η r) z (u-skew b c v)| ≤
        15*radialCoefficient r ‖z‖*‖wedge u v-wedge b c‖^2*‖z‖ +
        6*radialCoefficient r ‖z‖*‖wedge u v-wedge b c‖*‖transverse b c z‖ + C*r^4 := by
  obtain ⟨C,hC,hbound⟩ := cutKernel_deriv_bound η hη hηc hη0 hη1 ha hηone
  refine ⟨2*C,by positivity,fun r hr u v b c z hu hv huv hb hc hbc => ?_⟩
  have hw : ‖u-skew b c v‖ ≤ 2 := by
    have hh := norm_skew_le b c v hb hc hbc
    exact (norm_sub_le _ _).trans (by rw [hu,hv] at *; linarith)
  have hvar := first_variation_wedge_bound u v b c z hu hv huv hb hc hbc
  have hh := mul_le_mul_of_nonneg_left hvar (show 0 ≤ (6:ℝ)*radialCoefficient r ‖z‖ from mul_nonneg (by norm_num) (radialCoefficient_nonneg r ‖z‖))
  have hrem := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ C*r^4)
  have hder := hbound r hr z (u-skew b c v)
  nlinarith

lemma sqrt_angular_transverse {χ k δ t : ℝ} (hχ : 0 ≤ χ) (hk : 0 ≤ k)
    (hδ : 0 ≤ δ) (ht : 0 ≤ t) :
    Real.sqrt (χ*δ^2*k)*Real.sqrt (χ*k*t^2) = χ*k*δ*t := by
  rw [←Real.sqrt_mul (by positivity)]
  have he : χ*δ^2*k*(χ*k*t^2) = (χ*k*δ*t)^2 := by ring
  rw [he,Real.sqrt_sq (by positivity)]
end TamingCompatibility.Concentration

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransversePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma transversePairKernel_measurable (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target) {r : ℝ} (hr : 0 < r) :
    Measurable (transversePairKernel A J α hs ht p K r) := by
  classical
  let S := unitChartDomain J α hs ht p.val K
  let f := fun uv : UnitPair J α hs ht => unitChartFirst J α hs ht p.val uv.2
  let g := fun uv : UnitPair J α hs ht => unitChartSecond J α hs ht p.val uv.2
  let z := fun uv : UnitPair J α hs ht => unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1
  have hf : ContinuousOn f (S ×ˢ S) := (unitChartFirst_continuousOn J α hs ht p.val hKT).comp continuous_snd.continuousOn (fun _ h => h.2)
  have hg : ContinuousOn g (S ×ˢ S) := (unitChartSecond_continuousOn J α hs ht p.val hKT).comp continuous_snd.continuousOn (fun _ h => h.2)
  have hb := unitChartBase_continuousOn J α hs ht p.val hKT
  have hz : ContinuousOn z (S ×ˢ S) := (hb.comp continuous_snd.continuousOn (fun _ h => h.2)).sub
    (hb.comp continuous_fst.continuousOn (fun _ h => h.1))
  have hi : ContinuousOn (fun uv => inner ℝ (f uv) (z uv)) (S ×ˢ S) := hf.inner hz
  have hj : ContinuousOn (fun uv => inner ℝ (g uv) (z uv)) (S ×ˢ S) := hg.inner hz
  have hiv : ContinuousOn (fun uv => (inner ℝ (f uv) (z uv)) • f uv) (S ×ˢ S) := hi.smul hf
  have hjv : ContinuousOn (fun uv => (inner ℝ (g uv) (z uv)) • g uv) (S ×ˢ S) := hj.smul hg
  have hv : ContinuousOn (fun uv => unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2) (S ×ˢ S) := (hz.sub hiv).sub hjv
  have ha : ContinuousOn (fun uv : UnitPair J α hs ht => A.partition p uv.1.val.proj) (S ×ˢ S) :=
    ((A.partition p).property.continuous.comp (angularBase_continuous J α hs ht).snd).continuousOn
  have hk : ContinuousOn (fun uv => radialCoefficient r ‖z uv‖) (S ×ˢ S) :=
    continuousOn_const.div ((continuousOn_const.add (hz.norm.pow 2)).pow 4) (fun uv _ => by positivity)
  have hm := ((ha.mul hk).mul (hv.norm.pow 2)).measurable_piecewise
      (continuousOn_const : ContinuousOn (fun _ : UnitPair J α hs ht => (0 : ℝ)) (S ×ˢ S)ᶜ)
      ((unitChartDomain_closed J α hs ht p.val hK hKT).prod
        (unitChartDomain_closed J α hs ht p.val hK hKT)).measurableSet
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext uv
  by_cases hu : uv ∈ S ×ˢ S <;>
    simp [transversePairKernel, Set.indicator, Set.piecewise, S, z] at hu ⊢

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SecondPlaneVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.Concentration
open PlaneVariation UnitaryFrame
lemma wedge_second_neg_first (u v : V) : wedge v (-u) = wedge u v := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

lemma cutKernel_plane_second_variation_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    {a : ℝ} (ha : 0 < a) (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ u v b c z : V,
      ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      ‖b‖ = 1 → ‖c‖ = 1 → inner ℝ b c = 0 →
      |fderiv ℝ (cutKernel η r) z (v-skew b c (-u))| ≤
        15*radialCoefficient r ‖z‖*‖wedge u v-wedge b c‖^2*‖z‖ +
        6*radialCoefficient r ‖z‖*‖wedge u v-wedge b c‖*‖transverse b c z‖ + C*r^4 := by
  obtain ⟨C,hC,hbound⟩ := cutKernel_plane_variation_bound η hη hηc hη0 hη1 ha hηone
  refine ⟨C,hC,fun r hr u v b c z hu hv huv hb hc hbc => ?_⟩
  have h := hbound r hr v (-u) b c z hv (by simpa only [norm_neg] using hu)
    (by rw [inner_neg_right,real_inner_comm,huv,neg_zero]) hb hc hbc
  rwa [wedge_second_neg_first] at h
end TamingCompatibility.Concentration

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

omit [T2Space X] [CompactSpace X] in
lemma secondVariationDensity_nonneg (p : A.centers) (r : ℝ) (uv : UnitPair J α hs ht) :
    0 ≤ secondVariationDensity A J α hs ht E p r uv := by
  apply mul_nonneg (A.partition.nonneg _ _)
  apply indicator_nonneg _ uv.1
  intro u _
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)

include hE in
lemma secondVariationDensity_bound (p : A.centers) :
    ∃ P C : ℝ, 0 ≤ P ∧ 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ uv : UnitPair J α hs ht,
      secondVariationDensity A J α hs ht E p r uv ≤
        15*P*(euclideanAngularGlobal A J α hs ht E p uv *
          radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv)*
            euclideanDistanceGlobal A J α hs ht E p uv) +
        6*P*(Real.sqrt (euclideanAngularGlobal A J α hs ht E p uv *
          radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv))*
          Real.sqrt (transversePairKernel A J α hs ht p (E p).concentrationCompact r uv.swap)) + C*r^4 := by
  obtain ⟨_,P,_,hP,harea⟩ := unitChartArea_bounds J α hs ht p.val
    (E p).concentrationCompact_compact (E p).concentrationCompact_target
  have hone : ∀ z : Space, ‖z‖ < (E p).concentrationCutoff.radius/2 → (E p).concentrationCutoff.bump z = 1 := by
    intro z hz
    apply ContDiffBump.one_of_mem_closedBall
    change dist z 0 ≤ (E p).concentrationCutoff.radius/2
    simpa only [dist_zero_right] using hz.le
  obtain ⟨C,hC,hder⟩ := cutKernel_plane_second_variation_bound
    (E p).concentrationCutoff.bump (E p).concentrationCutoff.bump.contDiff
    (E p).concentrationCutoff.bump.hasCompactSupport
    (fun z => (E p).concentrationCutoff.bump.nonneg (x := z))
    (fun z => (E p).concentrationCutoff.bump.le_one (x := z))
    (by linarith [(E p).concentrationCutoff.positive] : 0 < (E p).concentrationCutoff.radius/2) hone
  refine ⟨P,P*C,hP.le,by positivity,fun r hr uv => ?_⟩
  have hright : 0 ≤ 15*P*(euclideanAngularGlobal A J α hs ht E p uv *
          radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv)*
            euclideanDistanceGlobal A J α hs ht E p uv) +
        6*P*(Real.sqrt (euclideanAngularGlobal A J α hs ht E p uv *
          radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv))*
          Real.sqrt (transversePairKernel A J α hs ht p (E p).concentrationCompact r uv.swap)) + (P*C)*r^4 := by
    have := euclideanAngularGlobal_nonneg A J α hs ht E p uv
    have := euclideanDistanceGlobal_nonneg A J α hs ht E p uv
    have := radialCoefficient_nonneg r (euclideanDistanceGlobal A J α hs ht E p uv)
    positivity
  by_cases hc : A.partition p uv.2.val.proj = 0
  · rw [secondVariationDensity,hc,zero_mul]
    exact hright
  have hx : uv.2.val.proj ∈ tsupport (A.partition p) := subset_tsupport _ (Function.mem_support.mpr hc)
  have hcenter := partition_center_ball A J α ht E hE p hx
  have hcentersrc := A.subordinate p hx
  have hvK : uv.2 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact :=
    ⟨unitChartBase J α hs ht p.val uv.2,(E p).concentrationCompact_center hcenter,
      (extChartAt Model p.val).left_inv hcentersrc⟩
  by_cases hu : uv.1 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  swap
  · rw [secondVariationDensity,indicator_of_notMem hu,mul_zero]
    exact hright
  let z := unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1
  by_cases hz : z ∈ tsupport ((E p).concentrationCutoff.bump : Space → ℝ)
  swap
  · have hzero : fderiv ℝ (cutKernel (E p).concentrationCutoff.bump r) z = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun hz' => hz (cutKernel_tsupport _ _ hz'))
    rw [secondVariationDensity,indicator_of_mem hu]
    change A.partition p uv.2.val.proj*(unitChartArea J α hs ht p.val uv.1*|fderiv ℝ _ z _|) ≤ _
    rw [hzero,zero_apply,abs_zero,mul_zero,mul_zero]
    exact hright
  have husrc := (unitChart_mem J α hs ht p.val (E p).concentrationCompact_target hu).1
  have hn : ‖unitChartBase J α hs ht p.val uv.1-unitChartBase J α hs ht p.val uv.2‖ ≤
      (E p).concentrationCutoff.radius := by
    rw [(E p).concentrationCutoff.bump.tsupport_eq] at hz
    change dist z 0 ≤ _ at hz
    simpa only [dist_zero_right,z,norm_sub_rev,ParametrixData.ConcentrationCutoff.bump] using hz
  have hphys := (E p).concentrationCutoff.near _ hcenter _ hn
  have hang : uv ∈ angularDomain A J α hs ht E p := by
    refine ⟨(unitChartBase J α hs ht p.val uv.2,unitChartBase J α hs ht p.val uv.1),hphys,?_⟩
    exact Prod.ext ((extChartAt Model p.val).left_inv hcentersrc) ((extChartAt Model p.val).left_inv husrc)
  obtain ⟨hu1,hu2,hu3,_⟩ := unitChartPlane J α hs ht p.val uv.1 husrc
  obtain ⟨hv1,hv2,hv3,_⟩ := unitChartPlane J α hs ht p.val uv.2 hcentersrc
  have hd := hder r hr _ _ _ _ z hv1 hv2 hv3 hu1 hu2 hu3
  have hpbound : secondVariationDensity A J α hs ht E p r uv ≤
      A.partition p uv.2.val.proj * P *
        (15*radialCoefficient r ‖z‖*‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2*‖z‖+
          6*radialCoefficient r ‖z‖*‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖*
            ‖transverse (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1) z‖+C*r^4) := by
    rw [secondVariationDensity,indicator_of_mem hu,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (A.partition.nonneg _ _)
    apply mul_le_mul (harea uv.1 hu).2 _ (abs_nonneg _) hP.le
    simpa only [euclideanLine,norm_sub_rev] using hd
  have htnorm : ‖unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.2) uv.1‖ =
      ‖transverse (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1) z‖ := by
    unfold unitTransverse
    rw [show unitChartBase J α hs ht p.val uv.1-unitChartBase J α hs ht p.val uv.2 = (-1:ℝ) • z by simp [z],
      transverse_smul,norm_smul,Real.norm_eq_abs,abs_neg,abs_one,one_mul]
  have hrad : euclideanDistanceGlobal A J α hs ht E p uv = ‖z‖ := by
    simp only [euclideanDistanceGlobal,indicator_of_mem hang,angularChartCoordinates,z,unitChartBase,norm_sub_rev]
  have hweight : euclideanAngularGlobal A J α hs ht E p uv =
      A.partition p uv.2.val.proj*‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2 :=
    indicator_of_mem hang _
  have htrans : transversePairKernel A J α hs ht p (E p).concentrationCompact r uv.swap =
      A.partition p uv.2.val.proj*radialCoefficient r ‖z‖*
        ‖transverse (unitChartFirst J α hs ht p.val uv.1) (unitChartSecond J α hs ht p.val uv.1) z‖^2 := by
    rw [transversePairKernel,indicator_of_mem (show uv.swap ∈ _ ×ˢ _ from ⟨hvK,hu⟩)]
    simp only [Prod.swap,htnorm,z,norm_sub_rev]
  rw [hweight,hrad,htrans,sqrt_angular_transverse (A.partition.nonneg _ _) (radialCoefficient_nonneg _ _) (norm_nonneg _) (norm_nonneg _)]
  have hrem := mul_le_mul_of_nonneg_right (A.partition.le_one p uv.2.val.proj)
    (by positivity : 0 ≤ P*C*r^4)
  nlinarith [hpbound]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SecondVariationIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.PlaneVariation
open Set
open scoped RealInnerProductSpace
lemma continuousOn_secondVariation {Y V : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f g : Y → V} {S : Set Y} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
    ContinuousOn (fun uv : Y × Y => g uv.2-skew (f uv.1) (g uv.1) (-f uv.2)) (S ×ˢ S) := by
  have hf1 : ContinuousOn (fun uv : Y × Y => f uv.1) (S ×ˢ S) := hf.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hf2 : ContinuousOn (fun uv : Y × Y => f uv.2) (S ×ˢ S) := hf.comp continuous_snd.continuousOn (fun _ h => h.2)
  have hg1 : ContinuousOn (fun uv : Y × Y => g uv.1) (S ×ˢ S) := hg.comp continuous_fst.continuousOn (fun _ h => h.1)
  have hg2 : ContinuousOn (fun uv : Y × Y => g uv.2) (S ×ˢ S) := hg.comp continuous_snd.continuousOn (fun _ h => h.2)
  exact hg2.sub (((hg1.inner hf2.neg).smul hf1).sub ((hf1.inner hf2.neg).smul hg1))
end TamingCompatibility.PlaneVariation
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

include hE in
omit [T2Space X] [CompactSpace X] [SecondCountableTopology X] in
lemma secondVariationDensity_eq_indicator (p : A.centers) (r : ℝ) :
    secondVariationDensity A J α hs ht E p r =
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)).indicator
        (secondVariationRaw A J α hs ht E p r) := by
  funext uv
  by_cases hu : uv.1 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
  · by_cases hv : uv.2 ∈ unitChartDomain J α hs ht p.val (E p).concentrationCompact
    · simp only [secondVariationDensity,indicator_of_mem hu,indicator_of_mem (show uv ∈ _ ×ˢ _ from ⟨hu,hv⟩),secondVariationRaw]
    · have hz : A.partition p uv.2.val.proj = 0 := by
        by_contra hn
        have hc := partition_center_ball A J α ht E hE p (subset_tsupport _ hn)
        have hsrc := (E p).source_subset (hE p (subset_tsupport _ hn))
        exact hv ⟨_,(E p).concentrationCompact_center hc,(extChartAt Model p.val).left_inv hsrc⟩
      simp only [secondVariationDensity,indicator_of_mem hu,hz,zero_mul,
        indicator_of_notMem (show uv ∉ _ ×ˢ _ from fun h => hv h.2)]
  · simp only [secondVariationDensity,indicator_of_notMem hu,mul_zero,
      indicator_of_notMem (show uv ∉ _ ×ˢ _ from fun h => hu h.1)]

omit [CompactSpace X] [SecondCountableTopology X] [T2Space X] in
lemma secondVariationVector_continuousOn (p : A.centers) :
    ContinuousOn (secondVariationVector A J α hs ht p)
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)) := by
  exact PlaneVariation.continuousOn_secondVariation
    (unitChartFirst_continuousOn J α hs ht p.val (E p).concentrationCompact_target)
    (unitChartSecond_continuousOn J α hs ht p.val (E p).concentrationCompact_target)

omit [CompactSpace X] [SecondCountableTopology X] [T2Space X] in
lemma secondVariationRaw_continuousOn (p : A.centers) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (secondVariationRaw A J α hs ht E p r)
      ((unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)) := by
  let S := unitChartDomain J α hs ht p.val (E p).concentrationCompact
  have hb := unitChartBase_continuousOn J α hs ht p.val (E p).concentrationCompact_target
  have hz : ContinuousOn (fun uv : UnitPair J α hs ht =>
      unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1) (S ×ˢ S) :=
    (hb.comp continuous_snd.continuousOn (fun _ h => h.2)).sub (hb.comp continuous_fst.continuousOn (fun _ h => h.1))
  have hd := ((cutKernel_smooth hr _ (E p).concentrationCutoff.bump.contDiff).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp_continuousOn hz
  have ha : ContinuousOn (fun uv : UnitPair J α hs ht => unitChartArea J α hs ht p.val uv.1) (S ×ˢ S) := (unitChartArea_continuousOn J α hs ht p.val (E p).concentrationCompact_target).comp continuous_fst.continuousOn (fun _ h => h.1)
  have hp : ContinuousOn (fun uv : UnitPair J α hs ht => A.partition p uv.2.val.proj) (S ×ˢ S) :=
    ((A.partition p).property.continuous.comp (angularBase_continuous J α hs ht).fst).continuousOn
  exact hp.mul (ha.mul (hd.clm_apply (secondVariationVector_continuousOn A J α hs ht E p)).abs)

include hE in
lemma secondVariationDensity_integrable (μ : Measure (MetricUnit (hermitianMetric J α hs ht)))
    [IsFiniteMeasure μ] (p : A.centers) {r : ℝ} (hr : 0 < r) :
    Integrable (secondVariationDensity A J α hs ht E p r) (μ.prod μ) := by
  classical
  let S := (unitChartDomain J α hs ht p.val (E p).concentrationCompact) ×ˢ
       (unitChartDomain J α hs ht p.val (E p).concentrationCompact)
  have hc := unitChartDomain_closed J α hs ht p.val (E p).concentrationCompact_compact (E p).concentrationCompact_target
  have hS : _root_.IsClosed S := hc.prod hc
  have hf := secondVariationRaw_continuousOn A J α hs ht E p hr
  have hm := hf.measurable_piecewise
    (continuousOn_const : ContinuousOn (fun _ : UnitPair J α hs ht => (0 : ℝ)) Sᶜ) hS.measurableSet
  have hm' : Measurable (secondVariationDensity A J α hs ht E p r) := by
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    funext uv
    rw [secondVariationDensity_eq_indicator A J α hs ht E hE p r]
    by_cases huv : uv ∈ S <;> simp [Set.indicator, Set.piecewise, S] at huv ⊢
  obtain ⟨C,hC⟩ := hS.isCompact.exists_bound_of_continuousOn hf
  apply (integrable_const (max C 0 : ℝ)).mono' hm'.aestronglyMeasurable
  apply ae_of_all
  intro uv
  rw [secondVariationDensity_eq_indicator A J α hs ht E hE p r]
  by_cases huv : uv ∈ S
  · rw [indicator_of_mem huv]
    exact (hC uv huv).trans (le_max_left _ _)
  · rw [indicator_of_notMem huv,norm_zero]
    exact le_max_right _ _
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitTransversePairProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory RadialPotential PlaneVariation Concentration GeometricNormalCharts
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X] [CompactSpace X] in
lemma transversePairKernel_nonneg (p : A.centers) (K : Set Space) (r : ℝ) (uv : UnitPair J α hs ht) :
    0 ≤ transversePairKernel A J α hs ht p K r uv := by
  apply indicator_nonneg _ uv
  intro v _
  exact mul_nonneg (mul_nonneg (A.partition.nonneg _ _) (radialCoefficient_nonneg _ _)) (sq_nonneg _)

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [T2Space X] [CompactSpace X] in
lemma transversePairKernel_bound (p : A.centers) {K : Set Space}
    (hKT : K ⊆ (extChartAt Model p.val).target) {r : ℝ} (hr : 0 < r) (uv : UnitPair J α hs ht) :
    transversePairKernel A J α hs ht p K r uv ≤ 8/r^2 := by
  by_cases huv : uv ∈ (unitChartDomain J α hs ht p.val K) ×ˢ (unitChartDomain J α hs ht p.val K)
  · rw [transversePairKernel,indicator_of_mem huv]
    have hsrc := (unitChart_mem J α hs ht p.val hKT huv.2).1
    obtain ⟨h₁,h₂,h₃,_⟩ := unitChartPlane J α hs ht p.val uv.2 hsrc
    have ht' := norm_transverse_le (unitChartFirst J α hs ht p.val uv.2)
      (unitChartSecond J α hs ht p.val uv.2)
      (unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1) h₁ h₂ h₃
    have hp : ((1+‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖/r)⁻¹)^6 ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      apply inv_le_one_of_one_le₀
      have : 0 ≤ ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖/r := by positivity
      linarith
    calc
      _ = A.partition p uv.1.val.proj*(radialCoefficient r
          ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖*
          ‖unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2‖^2) := by ring
      _ ≤ radialCoefficient r ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖*
          ‖unitTransverse J α hs ht p.val (unitChartBase J α hs ht p.val uv.1) uv.2‖^2 :=
        mul_le_of_le_one_left (mul_nonneg (radialCoefficient_nonneg _ _) (sq_nonneg _)) (A.partition.le_one _ _)
      _ ≤ radialCoefficient r ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖*
          ‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ht' 2) (radialCoefficient_nonneg _ _)
      _ ≤ (8/r^2)*((1+‖unitChartBase J α hs ht p.val uv.2-unitChartBase J α hs ht p.val uv.1‖/r)⁻¹)^6 :=
        radialCoefficient_quadratic_profile hr (norm_nonneg _)
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hp
  · rw [transversePairKernel,indicator_of_notMem huv]
    positivity

omit [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma transversePairKernel_integrable (p : A.centers) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p.val).target)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r) : Integrable (transversePairKernel A J α hs ht p K r) (μ.prod μ) := by
  apply (integrable_const (8/r^2)).mono'
    (transversePairKernel_measurable A J α hs ht p hK hKT hr).aestronglyMeasurable
  apply ae_of_all
  intro uv
  rw [Real.norm_eq_abs,abs_of_nonneg (transversePairKernel_nonneg A J α hs ht p K r uv)]
  exact transversePairKernel_bound A J α hs ht p hKT hr uv

end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section

noncomputable section
open _root_.MeasureTheory Filter
open scoped Topology ENNReal
namespace TamingCompatibility
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integral_sqrt_mul_sqrt_tendsto_eventually {ι : Type*} {l : Filter ι}
    (f g : ι → Ω → ℝ) (hf : ∀ᶠ i in l, Integrable (f i) μ) (hg : ∀ᶠ i in l, Integrable (g i) μ)
    (hfp : ∀ i x, 0 ≤ f i x) (hgp : ∀ i x, 0 ≤ g i x)
    (C : ℝ) (hb : ∀ᶠ i in l, (∫ x, f i x ∂μ) ≤ C)
    (hl : Tendsto (fun i => ∫ x, g i x ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, Real.sqrt (f i x)*Real.sqrt (g i x) ∂μ) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun i => integral_nonneg fun x => by positivity)
  · filter_upwards [hf,hg,hb] with i hi hj hk
    exact (integral_sqrt_mul_sqrt_le (f i) (g i) hi hj (hfp i) (hgp i)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hk) (Real.sqrt_nonneg _))
  · simpa only [Real.sqrt_zero,mul_zero,Function.comp_def] using
      (tendsto_const_nhds (x := Real.sqrt C)).mul (Real.continuous_sqrt.tendsto 0 |>.comp hl)
end TamingCompatibility

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory Filter
open Hermitian UnitaryFrame PlaneVariation Concentration
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
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

include hE hD hG in
lemma separating_current_angular_transverse_limit
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers)
    {K : Set Space} (hK : IsCompact K) (hKT : K ⊆ (extChartAt Model p.val).target) :
    Tendsto (fun r : ℝ => ∫ uv,
      Real.sqrt (euclideanAngularGlobal A J α hs ht E p uv *
        radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv)) *
      Real.sqrt (transversePairKernel A J α hs ht p K r uv.swap) ∂μ.prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,_,hbound⟩ := separating_current_euclidean_radial_angular A J α hs ht E hE D hD μ hann p
  apply integral_sqrt_mul_sqrt_tendsto_eventually (C := C)
    (fun r uv => euclideanAngularGlobal A J α hs ht E p uv *
      radialCoefficient r (euclideanDistanceGlobal A J α hs ht E p uv))
    (fun r uv => transversePairKernel A J α hs ht p K r uv.swap)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact weighted_radial_integrable _ _
      (euclideanAngularGlobal_measurable A J α hs ht E p)
      (euclideanDistanceGlobal_measurable A J α hs ht E p)
      (euclideanAngularGlobal_nonneg A J α hs ht E p)
      (euclideanDistanceGlobal_nonneg A J α hs ht E p)
      (euclideanAngularGlobal_integrable A J α hs ht E μ p) hr
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (transversePairKernel_integrable A J α hs ht p hK hKT μ hr).swap
  · exact fun r uv => mul_nonneg (euclideanAngularGlobal_nonneg A J α hs ht E p uv) (radialCoefficient_nonneg _ _)
  · exact fun r uv => transversePairKernel_nonneg A J α hs ht p K r uv.swap
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hbound r hr).1
  · simp_rw [integral_prod_swap]
    exact separating_probability_transverse_product_limit A J α hs ht G hG μ hann p hK hKT
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SecondVariationLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter _root_.MeasureTheory PlaneVariation Concentration Hermitian UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [SecondCountableTopology X] [ConnectedSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel unitSecondCountable

include hE hD hG in
lemma separating_current_second_variation_limit_oai
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) (p : A.centers) :
    Tendsto (fun r : ℝ => ∫ uv, secondVariationDensity A J α hs ht E p r uv ∂μ.prod μ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨P,C,hP,hC,hbound⟩ := secondVariationDensity_bound A J α hs ht E hE p
  let w := euclideanAngularGlobal A J α hs ht E p
  let d := euclideanDistanceGlobal A J α hs ht E p
  let f := fun r uv => w uv*radialCoefficient r (d uv)*d uv
  let g := fun r uv => Real.sqrt (w uv*radialCoefficient r (d uv))*
    Real.sqrt (transversePairKernel A J α hs ht p (E p).concentrationCompact r uv.swap)
  have hi (r : ℝ) (hr : 0 < r) : Integrable (f r) (μ.prod μ) :=
    weighted_radial_linear_integrable w d (euclideanAngularGlobal_measurable A J α hs ht E p)
      (euclideanDistanceGlobal_measurable A J α hs ht E p)
      (euclideanAngularGlobal_nonneg A J α hs ht E p) (euclideanDistanceGlobal_nonneg A J α hs ht E p)
      (euclideanAngularGlobal_integrable A J α hs ht E μ p) hr
  have hj (r : ℝ) (hr : 0 < r) : Integrable (g r) (μ.prod μ) := by
    have ha := sqrt_memLp_two (fun uv => w uv*radialCoefficient r (d uv))
      (weighted_radial_integrable w d (euclideanAngularGlobal_measurable A J α hs ht E p)
        (euclideanDistanceGlobal_measurable A J α hs ht E p)
        (euclideanAngularGlobal_nonneg A J α hs ht E p) (euclideanDistanceGlobal_nonneg A J α hs ht E p)
        (euclideanAngularGlobal_integrable A J α hs ht E μ p) hr)
      (fun uv => mul_nonneg (euclideanAngularGlobal_nonneg A J α hs ht E p uv) (radialCoefficient_nonneg _ _))
    have hb := sqrt_memLp_two (fun uv : UnitPair J α hs ht => transversePairKernel A J α hs ht p (E p).concentrationCompact r uv.swap)
      ((transversePairKernel_integrable A J α hs ht p (E p).concentrationCompact_compact
        (E p).concentrationCompact_target μ hr).swap)
      (fun uv => transversePairKernel_nonneg A J α hs ht p (E p).concentrationCompact r uv.swap)
    exact ha.integrable_mul hb
  have hf : Tendsto (fun r : ℝ => ∫ uv, f r uv ∂μ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    separating_current_euclidean_radial_linear_limit A J α hs ht E hE D hD μ hann p
  have hg : Tendsto (fun r : ℝ => ∫ uv, g r uv ∂μ.prod μ) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    separating_current_angular_transverse_limit A J α hs ht E hE D hD G hG μ hann p
      (E p).concentrationCompact_compact (E p).concentrationCompact_target
  apply squeeze_zero' (g := fun r => 15*P*(∫ uv, f r uv ∂μ.prod μ)+
    6*P*(∫ uv, g r uv ∂μ.prod μ)+C*r^4) (Eventually.of_forall fun r => integral_nonneg
    (secondVariationDensity_nonneg A J α hs ht E p r))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hb := integral_mono (secondVariationDensity_integrable A J α hs ht E hE μ p hr)
      (((hi r hr).const_mul (15*P)).add ((hj r hr).const_mul (6*P)) |>.add (integrable_const (C*r^4)))
      (hbound r hr)
    simp only [Pi.add_apply] at hb
    have hab : Integrable (fun uv => 15*P*f r uv+6*P*g r uv) (μ.prod μ) :=
      ((hi r hr).const_mul _).add ((hj r hr).const_mul _)
    have ha : Integrable (fun uv => 15*P*f r uv) (μ.prod μ) := (hi r hr).const_mul _
    have hb' : Integrable (fun uv => 6*P*g r uv) (μ.prod μ) := (hj r hr).const_mul _
    rw [integral_add hab (integrable_const _), integral_add ha hb',
      integral_const_mul,integral_const_mul] at hb
    simpa only [integral_const,probReal_univ,one_smul] using hb
  · have hr : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [mul_zero,add_zero,zero_pow (by decide : (4:ℕ) ≠ 0)] using
      ((hf.const_mul (15*P)).add (hg.const_mul (6*P))).add ((hr.pow 4).const_mul C)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_second_variation_limit_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.separating_current_second_variation_limit_oai.{u_1}
