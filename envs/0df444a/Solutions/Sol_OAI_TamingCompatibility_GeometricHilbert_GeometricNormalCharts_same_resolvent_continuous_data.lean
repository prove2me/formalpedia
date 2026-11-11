-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_continuous_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:13:52.063194+00:00
-- url     : https://prove2.me/submissions/f72d62bf-6121-478f-bec6-c3b7de17906c

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc033
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalCandidate_evolution_of_bounds
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_globalCorrection_continuous_bounds

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_VariationalResolvent
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped RealInnerProductSpace

namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

lemma resolvent_nonnegative (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (hc : IsCoercive (energy i D)) (f : H) : 0 ≤ ⟪f, resolvent i D hc f⟫ := by
  change 0 ≤ ⟪f, i (weakSolution i D hc f)⟫
  rw [← weakSolution_identity i D hc f (weakSolution i D hc f)]
  exact add_nonneg (real_inner_self_nonneg) (real_inner_self_nonneg)

end TamingCompatibility.Variational

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolvent
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
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
open ManifoldForms ManifoldHodge ManifoldLocalization Filter Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeResolvent_nonnegative (r : ℝ) (f : L2 A J α hs ht true) :
    0 ≤ ⟪f,hodgeResolvent A J α hs ht r f⟫ := by
  unfold hodgeResolvent
  split_ifs with hr
  · exact Variational.resolvent_nonnegative _ _ _ f
  · exact real_inner_self_nonneg

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolventDifferential
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

lemma hodgeResolvent_differential_inverse (r : ℝ) (hr : 0 < r)
    (a : PreL2 A J α hs ht true) :
    hodgeResolvent A J α hs ht r (smoothL2 A J α hs ht true
      (a+r^2 • hodgeLaplacian A J α hs ht a)) = smoothL2 A J α hs ht true a := by
  have he : hodgeWeakSolution A J α hs ht r hr (smoothL2 A J α hs ht true
      (a+r^2 • hodgeLaplacian A J α hs ht a)) = hodgeSmooth A J α hs ht a := by
    apply hodgeWeakSolution_unique A J α hs ht r hr
    intro v
    rw [map_add,map_smul,inner_add_left,real_inner_smul_left,hodgeLaplacian_green_weak]
    rfl
  rw [hodgeResolvent_eq A J α hs ht r hr,ContinuousLinearMap.comp_apply,he]
  rfl

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeResolventParameters
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
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

lemma hodgeWeakSolution_parameter (r s : ℝ) (hr : 0 < r) (hs' : 0 < s)
    (f : L2 A J α hs ht true) :
    hodgeWeakSolution A J α hs ht r hr
      (r^2 • f + (s^2-r^2) • hodgeResolvent A J α hs ht s f) =
      s^2 • hodgeWeakSolution A J α hs ht s hs' f := by
  apply hodgeWeakSolution_unique A J α hs ht r hr
  intro v
  rw [map_smul, map_smul, real_inner_smul_left, real_inner_smul_left,
    inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h := hodgeWeakSolution_identity A J α hs ht s hs' f v
  rw [hodgeResolvent_eq A J α hs ht s hs', ContinuousLinearMap.comp_apply] at h ⊢
  nlinarith only [h]

end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)

lemma hodgeResolvent_eigenvalue_positive_le_one (f : L2 A J α hs ht true)
    (hf : f ≠ 0) (x : ℝ) (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    0 < x ∧ x ≤ 1 := by
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hp := hodgeResolvent_nonnegative A J α hs ht 1 f
  rw [hx, real_inner_smul_right, real_inner_self_eq_norm_sq] at hp
  have hx0 : 0 ≤ x := (mul_nonneg_iff_of_pos_right (sq_pos_of_pos hn)).mp hp
  have hb := hodgeResolvent_norm_le A J α hs ht 1 f
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg hx0] at hb
  have hx1 : x ≤ 1 := by nlinarith
  have hne : x ≠ 0 := by
    intro hz
    have hz' : hodgeResolvent A J α hs ht 1 f = hodgeResolvent A J α hs ht 1 0 := by
      rw [hx, hz, zero_smul, map_zero]
    exact hf (hodgeResolvent_injective A J α hs ht 1 zero_lt_one hz')
  exact ⟨lt_of_le_of_ne hx0 (Ne.symm hne), hx1⟩

lemma hodgeResolvent_eigenvector_parameter (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeResolvent A J α hs ht r f = (x / (r^2+(1-r^2)*x)) • f := by
  have hdpos : 0 < r^2 + (1-r^2)*x := by
    have hr2 := sq_pos_of_pos hr
    have hp := mul_nonneg hr2.le (sub_nonneg.mpr hx1)
    by_cases hz : x = 0
    · simpa only [hz, mul_zero, add_zero] using hr2
    · have hxp : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hz)
      nlinarith
  have hd := ne_of_gt hdpos
  have h := congrArg (hodgeInclusion A J α hs ht)
    (hodgeWeakSolution_parameter A J α hs ht r 1 hr zero_lt_one f)
  rw [map_smul] at h
  simp only [← ContinuousLinearMap.comp_apply, ← hodgeResolvent_eq A J α hs ht _] at h
  simp only [one_pow, one_smul, hx] at h
  rw [smul_smul, ← add_smul, map_smul] at h
  calc
    hodgeResolvent A J α hs ht r f =
        (r^2+(1-r^2)*x)⁻¹ • ((r^2+(1-r^2)*x) • hodgeResolvent A J α hs ht r f) := by
      rw [inv_smul_smul₀ hd]
    _ = (r^2+(1-r^2)*x)⁻¹ • (x • f) := by rw [h]
    _ = (x / (r^2+(1-r^2)*x)) • f := by
      rw [smul_smul]; congr 1; ring

lemma hodgeRegularization_sq_eigenvector (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    (hodgeRegularization A J α hs ht r ^ 2) f =
      (x / (r^2+(1-r^2)*x))^6 • f := by
  have he := hodgeResolvent_eigenvector_parameter A J α hs ht r hr f x hx0 hx1 hx
  have hp (n : ℕ) : (hodgeResolvent A J α hs ht r ^ n) f =
      (x / (r^2+(1-r^2)*x))^n • f := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, he, smul_smul]
      congr 1
  change ((hodgeResolvent A J α hs ht r ^ 3)^2) f = _
  rw [← pow_mul]
  exact hp 6

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeSpectralHeat
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
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
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeSpectralHeat_zero : hodgeSpectralHeat A J α hs ht D hD 0 = 1 := by
  ext f
  apply (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv.injective
  ext x
  rw [hodgeSpectralHeat_repr]
  simp only [hodgeHeatMultiplier, max_self, neg_zero, zero_mul, Real.exp_zero, one_smul,
    one_apply_eq_self]

lemma hodgeSpectralHeat_eigenvector (t x : ℝ) (f : L2 A J α hs ht true)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeSpectralHeat A J α hs ht D hD t f = hodgeHeatMultiplier t x • f := by
  classical
  let v : Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x :=
    ⟨f, Module.End.mem_eigenspace_iff.mpr hx⟩
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  have hv : E.symm (lp.single 2 x v) = f :=
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv_symm_apply_single v
  have hv' : E f = lp.single 2 x v := by rw [← hv, E.apply_symm_apply]
  apply E.injective
  apply lp.ext
  funext y
  change E (hodgeSpectralHeat A J α hs ht D hD t f) y = E (hodgeHeatMultiplier t x • f) y
  rw [hodgeSpectralHeat_repr, map_smul]
  change hodgeHeatMultiplier t y • E f y = hodgeHeatMultiplier t x • E f y
  rw [hv']
  by_cases hy : y = x
  · subst y; rfl
  · simp [lp.single_apply, hy]

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatSmoothing
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeBoundedSpectralMultiplier_repr (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (f : L2 A J α hs ht true) (x : ℝ) :
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
      (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f) x =
      m x • (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv f x := by
  change ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
    ((hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv.symm _)) x = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma hodgeBoundedSpectralMultiplier_eigenvector (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (x : ℝ) (f : L2 A J α hs ht true)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f = m x • f := by
  classical
  let v : Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x :=
    ⟨f, Module.End.mem_eigenspace_iff.mpr hx⟩
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  have hv : E.symm (lp.single 2 x v) = f :=
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv_symm_apply_single v
  have hv' : E f = lp.single 2 x v := by rw [← hv, E.apply_symm_apply]
  apply E.injective
  apply lp.ext
  funext y
  change E (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f) y = E (m x • f) y
  rw [hodgeBoundedSpectralMultiplier_repr, map_smul]
  change m y • E f y = m x • E f y
  rw [hv']
  by_cases hy : y = x
  · subst y; rfl
  · simp [lp.single_apply, hy]

lemma hodgeBoundedSpectralMultiplier_symmetric (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (f g : L2 A J α hs ht true) :
    ⟪hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f,g⟫ =
      ⟪f,hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm g⟫ := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  rw [← E.inner_map_map (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm f) g,
    ← E.inner_map_map f (hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm g),
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  rw [hodgeBoundedSpectralMultiplier_repr, hodgeBoundedSpectralMultiplier_repr]
  change ⟪m x • (E f x).val, (E g x).val⟫ = ⟪(E f x).val, m x • (E g x).val⟫
  exact (real_inner_smul_left (E f x).val (E g x).val (m x)).trans
    (real_inner_smul_right (E f x).val (E g x).val (m x)).symm

end TamingCompatibility.GeometricHilbert

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

lemma hodgeSpectralHeat_symmetric (t : ℝ) (f g : L2 A J α hs ht true) :
    ⟪hodgeSpectralHeat A J α hs ht D hD t f,g⟫ =
      ⟪f,hodgeSpectralHeat A J α hs ht D hD t g⟫ := by
  exact hodgeBoundedSpectralMultiplier_symmetric A J α hs ht D hD
    (hodgeHeatMultiplier t) 1 zero_le_one
    (fun x => (abs_of_pos (hodgeHeatMultiplier_pos t x)).trans_le (hodgeHeatMultiplier_le_one t x)) f g

attribute [local instance] unitMeasurable unitBorel
end TamingCompatibility.GeometricHilbert

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatIdentification
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
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
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

include D hD in
lemma hodgeSpectral_ext (T U : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true)
    (he : ∀ (x : ℝ) (f : L2 A J α hs ht true),
      hodgeResolvent A J α hs ht 1 f = x • f → T f = U f) : T = U := by
  let L := T-U
  have hi : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x) ≤ L.ker := by
    apply iSup_le
    intro x f hf
    change T f-U f = 0
    exact sub_eq_zero.mpr (he x f (Module.End.mem_eigenspace_iff.mp hf))
  have hcl : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,
      hodgeResolvent_eigenspaces_total A J α hs ht D hD]
    simp
  have htop : ⊤ ≤ L.ker := by
    rw [← hcl]
    exact Submodule.topologicalClosure_minimal _ hi (ContinuousLinearMap.isClosed_ker L)
  ext f
  have hf : T f-U f = 0 := htop (Submodule.mem_top)
  exact sub_eq_zero.mp hf

lemma hodgeBoundedSpectralMultiplier_commutes (m : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ x, |m x| ≤ K) (T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true)
    (hT : ∀ f, hodgeResolvent A J α hs ht 1 (T f) = T (hodgeResolvent A J α hs ht 1 f)) :
    hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm * T =
      T * hodgeBoundedSpectralMultiplier A J α hs ht D hD m K hK hm := by
  apply hodgeSpectral_ext A J α hs ht D hD
  intro x f hx
  have hTx : hodgeResolvent A J α hs ht 1 (T f) = x • T f := by rw [hT, hx, map_smul]
  rw [mul_apply_eq_comp, mul_apply_eq_comp,
    hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD m K hK hm x (T f) hTx,
    hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD m K hK hm x f hx,
    map_smul]

attribute [local instance] unitMeasurable unitBorel
end TamingCompatibility.GeometricHilbert
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeResolvent_unit_spectral :
    hodgeResolvent A J α hs ht 1 =
      hodgeBoundedSpectralMultiplier A J α hs ht D hD unitSymbol 1 zero_le_one unitSymbol_bound := by
  apply hodgeSpectral_ext A J α hs ht D hD
  intro x f hx
  rw [hodgeBoundedSpectralMultiplier_eigenvector A J α hs ht D hD _ _ _ _ x f hx, hx]
  by_cases hf : f = 0
  · simp [hf]
  · obtain ⟨hx0,hx1⟩ := hodgeResolvent_eigenvalue_positive_le_one A J α hs ht f hf x hx
    rw [unitSymbol, max_eq_right hx0.le, min_eq_right hx1]

lemma hodgeResolvent_rate_repr (f : L2 A J α hs ht true) (x : ℝ) :
    hodgeSpectralRate x • (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
      (hodgeResolvent A J α hs ht 1 f) x =
    (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
      (f-hodgeResolvent A J α hs ht 1 f) x := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  have hc : E (hodgeResolvent A J α hs ht 1 f) x = unitSymbol x • E f x := by
    calc
      E (hodgeResolvent A J α hs ht 1 f) x = E
          (hodgeBoundedSpectralMultiplier A J α hs ht D hD unitSymbol 1 zero_le_one unitSymbol_bound f) x :=
        congrArg (fun v => E v x) (congrArg (fun T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => T f)
          (hodgeResolvent_unit_spectral A J α hs ht D hD))
      _ = _ := hodgeBoundedSpectralMultiplier_repr A J α hs ht D hD _ _ _ _ f x
  have hcval := congrArg Subtype.val hc
  have hsub : (E (f-hodgeResolvent A J α hs ht 1 f) x).val =
      (E f x).val-(E (hodgeResolvent A J α hs ht 1 f) x).val := by
    rw [map_sub]
    rfl
  apply Subtype.ext
  change hodgeSpectralRate x • (E (hodgeResolvent A J α hs ht 1 f) x).val =
    (E (f-hodgeResolvent A J α hs ht 1 f) x).val
  change (E (hodgeResolvent A J α hs ht 1 f) x).val = unitSymbol x • (E f x).val at hcval
  rw [hsub,hcval]
  by_cases hz : (E f x).val = 0
  · simp [hz]
  · have he : hodgeResolvent A J α hs ht 1 (E f x).val = x • (E f x).val :=
      Module.End.mem_eigenspace_iff.mp (E f x).property
    obtain ⟨hx0,hx1⟩ := hodgeResolvent_eigenvalue_positive_le_one A J α hs ht _ hz x he
    have hi : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr hx1
    have hscalar : hodgeSpectralRate x * unitSymbol x = 1-unitSymbol x := by
      rw [unitSymbol, max_eq_right hx0.le, min_eq_right hx1,
        hodgeSpectralRate, max_eq_right (sub_nonneg.mpr hi)]
      field_simp
    rw [smul_smul,hscalar,sub_smul,one_smul]

lemma hodgeSpectralHeat_inner_series (t : ℝ) (f g : L2 A J α hs ht true) :
    ⟪hodgeSpectralHeat A J α hs ht D hD t f,g⟫ =
      ∑' x : ℝ, hodgeHeatMultiplier t x *
        ⟪(hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv f x,
          (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv g x⟫ := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  rw [← E.inner_map_map, lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  rw [hodgeSpectralHeat_repr]
  exact real_inner_smul_left (E f x).val (E g x).val _

lemma hodgeHeatMultiplier_hasDerivAt (t x : ℝ) (ht' : 0 < t) :
    HasDerivAt (fun s => hodgeHeatMultiplier s x)
      (-hodgeSpectralRate x * hodgeHeatMultiplier t x) t := by
  have hlin : HasDerivAt (fun s : ℝ => -s*hodgeSpectralRate x) (-hodgeSpectralRate x) t := by
    simpa only [id_eq, Pi.neg_apply, neg_one_mul] using
      ((hasDerivAt_id t).neg).mul_const (hodgeSpectralRate x)
  have he := hlin.exp
  have hp : ∀ᶠ s : ℝ in 𝓝 t, 0 < s := Ioi_mem_nhds ht'
  have heq : (fun s => hodgeHeatMultiplier s x) =ᶠ[𝓝 t]
      (fun s => Real.exp (-s*hodgeSpectralRate x)) := hp.mono (fun s hs' => by
    simp only [hodgeHeatMultiplier, max_eq_left hs'.le])
  have hd : Real.exp (-t*hodgeSpectralRate x) * -hodgeSpectralRate x =
      -hodgeSpectralRate x * hodgeHeatMultiplier t x := by
    simp only [hodgeHeatMultiplier,max_eq_left ht'.le]
    ring
  rw [hd] at he
  exact he.congr_of_eventuallyEq heq

lemma heatScalarSeries_hasDerivAt (a b : ℝ → ℝ) (ha : Summable a) (hb : Summable b)
    (hr : ∀ x, hodgeSpectralRate x * a x = b x) (t : ℝ) (ht' : 0 < t) :
    HasDerivAt (fun s => ∑' x : ℝ, hodgeHeatMultiplier s x * a x)
      (-(∑' x : ℝ, hodgeHeatMultiplier t x * b x)) t := by
  have hd (x s : ℝ) (hsp : s ∈ Ioi (0:ℝ)) :
      HasDerivAt (fun z => hodgeHeatMultiplier z x * a x)
        (-hodgeHeatMultiplier s x * b x) s := by
    have hh := (hodgeHeatMultiplier_hasDerivAt s x hsp).mul_const (a x)
    have heq : (-hodgeSpectralRate x * hodgeHeatMultiplier s x) * a x =
        -hodgeHeatMultiplier s x * b x := by rw [← hr x]; ring
    rw [heq] at hh
    exact hh
  have hbound (x s : ℝ) (_hsp : s ∈ Ioi (0:ℝ)) :
      ‖-hodgeHeatMultiplier s x * b x‖ ≤ ‖b x‖ := by
    rw [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_pos (hodgeHeatMultiplier_pos s x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hodgeHeatMultiplier_le_one s x)
  have hsum0 : Summable (fun x => hodgeHeatMultiplier t x * a x) := by
    apply Summable.of_norm_bounded ha.norm
    intro x
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (hodgeHeatMultiplier_pos t x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hodgeHeatMultiplier_le_one t x)
  have hh := hasDerivAt_tsum_of_isPreconnected hb.norm isOpen_Ioi isPreconnected_Ioi
    hd hbound ht' hsum0 ht'
  have heq : (∑' x : ℝ, -hodgeHeatMultiplier t x * b x) =
      -(∑' x : ℝ, hodgeHeatMultiplier t x * b x) := by
    simp only [neg_mul,tsum_neg]
  rw [heq] at hh
  exact hh

lemma hodgeSpectralHeat_resolvent_hasDerivAt (f g : L2 A J α hs ht true)
    (t : ℝ) (ht' : 0 < t) :
    HasDerivAt (fun s => ⟪hodgeSpectralHeat A J α hs ht D hD s
      (hodgeResolvent A J α hs ht 1 f),g⟫)
      (-⟪hodgeSpectralHeat A J α hs ht D hD t
        (f-hodgeResolvent A J α hs ht 1 f),g⟫) t := by
  let E := (hodgeSpectralSum A J α hs ht D hD).linearIsometryEquiv
  let a := fun x : ℝ => ⟪E (hodgeResolvent A J α hs ht 1 f) x,E g x⟫
  let b := fun x : ℝ => ⟪E (f-hodgeResolvent A J α hs ht 1 f) x,E g x⟫
  have hr (x : ℝ) : hodgeSpectralRate x * a x = b x := by
    have hh := congrArg (fun v : Module.End.eigenspace (hodgeResolvent A J α hs ht 1).toLinearMap x =>
      ⟪v.val,(E g x).val⟫) (hodgeResolvent_rate_repr A J α hs ht D hD f x)
    change ⟪hodgeSpectralRate x • (E (hodgeResolvent A J α hs ht 1 f) x).val,(E g x).val⟫ = b x at hh
    exact (real_inner_smul_left (E (hodgeResolvent A J α hs ht 1 f) x).val
      (E g x).val (hodgeSpectralRate x)).symm.trans hh
  have ha : Summable a := lp.summable_inner (E (hodgeResolvent A J α hs ht 1 f)) (E g)
  have hb : Summable b := lp.summable_inner (E (f-hodgeResolvent A J α hs ht 1 f)) (E g)
  have hh := heatScalarSeries_hasDerivAt a b ha hb hr t ht'
  refine (hh.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    exact hodgeSpectralHeat_inner_series A J α hs ht D hD s _ g
  · exact congrArg Neg.neg (hodgeSpectralHeat_inner_series A J α hs ht D hD t _ g)

lemma hodgeSpectralHeat_smooth_hasDerivAt (a : PreL2 A J α hs ht true)
    (g : L2 A J α hs ht true) (t : ℝ) (ht' : 0 < t) :
    HasDerivAt (fun s => ⟪hodgeSpectralHeat A J α hs ht D hD s
      (smoothL2 A J α hs ht true a),g⟫)
      (-⟪hodgeSpectralHeat A J α hs ht D hD t
        (smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)),g⟫) t := by
  have hi := hodgeResolvent_differential_inverse A J α hs ht 1 zero_lt_one a
  simp only [one_pow,one_smul] at hi
  rw [map_add (smoothL2 A J α hs ht true)] at hi
  have hh := hodgeSpectralHeat_resolvent_hasDerivAt A J α hs ht D hD
    (smoothL2 A J α hs ht true a +
      smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)) g t ht'
  rw [hi, add_sub_cancel_left] at hh
  exact hh

lemma hodgeSpectralHeat_weak_hasDerivAt (f : L2 A J α hs ht true)
    (a : PreL2 A J α hs ht true) (t : ℝ) (ht' : 0 < t) :
    HasDerivAt (fun s => ⟪hodgeSpectralHeat A J α hs ht D hD s f,
      smoothL2 A J α hs ht true a⟫)
      (-⟪hodgeSpectralHeat A J α hs ht D hD t f,
        smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t := by
  have hh := hodgeSpectralHeat_smooth_hasDerivAt A J α hs ht D hD a f t ht'
  have he : (fun s => ⟪hodgeSpectralHeat A J α hs ht D hD s f,
      smoothL2 A J α hs ht true a⟫) =
      (fun s => ⟪hodgeSpectralHeat A J α hs ht D hD s
        (smoothL2 A J α hs ht true a),f⟫) := by
    funext s
    rw [hodgeSpectralHeat_symmetric]
    exact real_inner_comm _ _
  have hd : ⟪hodgeSpectralHeat A J α hs ht D hD t
      (smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)),f⟫ =
      ⟪hodgeSpectralHeat A J α hs ht D hD t f,
        smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫ := by
    rw [hodgeSpectralHeat_symmetric]
    exact real_inner_comm _ _
  rw [← he,hd] at hh
  exact hh
end TamingCompatibility.GeometricHilbert
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.WeakHeat
open Set Filter _root_.MeasureTheory Metric
open scoped Topology RealInnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma integral_eq_of_dense_weak (S : Set H) (hS : Dense S) (f g : ℝ → H)
    {a b : ℝ} (hg : ContinuousOn g (uIcc a b))
    (hd : ∀ w ∈ S, ∀ t ∈ uIcc a b,
      HasDerivAt (fun s => ⟪f s,w⟫) ⟪g t,w⟫ t) :
    (∫ t in a..b, g t) = f b-f a := by
  have hi : IntervalIntegrable g volume a b := hg.intervalIntegrable
  have he (w : H) (hw : w ∈ S) : ⟪∫ t in a..b, g t,w⟫ = ⟪f b-f a,w⟫ := by
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (hd w hw)
      ((hg.inner continuousOn_const).intervalIntegrable)
    have hc := (innerSL ℝ w).intervalIntegral_comp_comm hi
    simp only [innerSL_apply_apply] at hc
    calc
      ⟪∫ t in a..b, g t,w⟫ = ⟪w,∫ t in a..b, g t⟫ := real_inner_comm _ _
      _ = ∫ t in a..b, ⟪w,g t⟫ := hc.symm
      _ = ∫ t in a..b, ⟪g t,w⟫ := intervalIntegral.integral_congr
        (fun _ _ => real_inner_comm _ _)
      _ = ⟪f b-f a,w⟫ := by rw [hh,inner_sub_left]
  have hclosed : _root_.IsClosed {w : H | ⟪∫ t in a..b, g t,w⟫ = ⟪f b-f a,w⟫} :=
    isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  have hsub := closure_minimal he hclosed
  rw [hS.closure_eq] at hsub
  exact ext_inner_right ℝ (fun w => hsub (mem_univ w))

lemma hasDerivAt_of_dense_weak (S : Set H) (hS : Dense S) (f g : ℝ → H)
    {U : Set ℝ} (hU : IsOpen U) (hconv : Convex ℝ U) (hg : ContinuousOn g U)
    (hd : ∀ w ∈ S, ∀ t ∈ U, HasDerivAt (fun s => ⟪f s,w⟫) ⟪g t,w⟫ t)
    {t : ℝ} (ht : t ∈ U) : HasDerivAt f (g t) t := by
  have he (s : ℝ) (hs : s ∈ U) : f s = f t + ∫ u in t..s, g u := by
    have hseg : uIcc t s ⊆ U := by simpa only [segment_eq_uIcc] using hconv.segment_subset ht hs
    have hh := integral_eq_of_dense_weak S hS f g (hg.mono hseg)
      (fun w hw u hu => hd w hw u (hseg hu))
    rw [hh]
    abel
  have hct := hg.continuousAt (hU.mem_nhds ht)
  have hm : StronglyMeasurableAtFilter g (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter hU hg t ht
  have hp := (intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable g volume t t from IntervalIntegrable.refl) hm hct).const_add (f t)
  apply hp.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds ht] with s hs
  exact he s hs

lemma zero_of_resolvent_weak (R : H →L[ℝ] H) (hRinj : Function.Injective R)
    (hRsym : ∀ u v, ⟪R u,v⟫ = ⟪u,R v⟫)
    (hRpos : ∀ u, ⟪R u,R u⟫ ≤ ⟪u,R u⟫)
    (S : Set H) (hS : Dense S) (U : ℝ → H) {T : ℝ} (hT : 0 ≤ T)
    (hU : ContinuousOn U (Icc 0 T)) (hzero : U 0 = 0)
    (hweak : ∀ a ∈ S, ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s => ⟪U s,R a⟫) (-⟪U t,a-R a⟫) t) :
    ∀ t ∈ Icc 0 T, U t = 0 := by
  let V : ℝ → H := fun t => R (U t)
  let G : ℝ → H := fun t => R (U t)-U t
  have hV : ContinuousOn V (Icc 0 T) := R.continuous.comp_continuousOn hU
  have hG : ContinuousOn G (Icc 0 T) := hV.sub hU
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt V (G t) t := by
    apply hasDerivAt_of_dense_weak S hS V G isOpen_Ioo (convex_Ioo 0 T)
      (hG.mono Ioo_subset_Icc_self) _ ht
    intro a ha s hs
    have hh := hweak a ha s hs
    have hf : (fun t => ⟪V t,a⟫) = (fun t => ⟪U t,R a⟫) := by
      funext t
      exact hRsym _ _
    rw [hf]
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [G, inner_sub_left, inner_sub_right, hRsym, neg_sub]
  let E : ℝ → ℝ := fun t => ⟪V t,V t⟫
  have hEd (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt E (2*⟪G t,V t⟫) t := by
    convert! (hd t ht).inner ℝ (hd t ht) using 1
    all_goals try with_reducible_and_instances rfl
    rw [real_inner_comm (V t) (G t)]
    ring
  have hEn (t : ℝ) (ht : t ∈ Ioo 0 T) : deriv E t ≤ 0 := by
    rw [(hEd t ht).deriv]
    have hp := hRpos (U t)
    dsimp [G,V]
    rw [inner_sub_left]
    linarith
  have hanti : AntitoneOn E (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) (hV.inner hV)
    · rw [interior_Icc]
      exact fun t ht => (hEd t ht).differentiableAt.differentiableWithinAt
    · simpa only [interior_Icc] using hEn
  intro t ht
  have hle := hanti ⟨le_rfl,hT⟩ ht ht.1
  have he0 : E 0 = 0 := by simp [E,V,hzero]
  rw [he0] at hle
  have hvt : V t = 0 := inner_self_eq_zero.mp (le_antisymm hle (real_inner_self_nonneg))
  apply hRinj
  simpa [V] using hvt

end TamingCompatibility.GeometricHilbert.WeakHeat
end

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in

lemma hodgeResolvent_energy_le (r : ℝ) (hr : 0 < r) (f : L2 A J α hs ht true) :
    ⟪hodgeResolvent A J α hs ht r f,hodgeResolvent A J α hs ht r f⟫ ≤
      ⟪f,hodgeResolvent A J α hs ht r f⟫ := by
  have he := hodgeWeakSolution_identity A J α hs ht r hr f
    (hodgeWeakSolution A J α hs ht r hr f)
  have hi : hodgeInclusion A J α hs ht (hodgeWeakSolution A J α hs ht r hr f) =
      hodgeResolvent A J α hs ht r f := by rw [hodgeResolvent_eq]; rfl
  rw [hi] at he
  have hn := mul_nonneg (sq_nonneg r) (real_inner_self_nonneg (x :=
    hodgeWeakDerivative A J α hs ht (hodgeWeakSolution A J α hs ht r hr f)))
  linarith

include D hD in

lemma hodgeResolvent_smooth_core (a : PreL2 A J α hs ht true) :
    ∃ b : PreL2 A J α hs ht true,
      smoothL2 A J α hs ht true b = hodgeResolvent A J α hs ht 1
        (smoothL2 A J α hs ht true a) ∧
      smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht b) =
        smoothL2 A J α hs ht true a - smoothL2 A J α hs ht true b := by
  obtain ⟨b,hb⟩ := hodgeGraphResolvent_smooth A J α hs ht D hD 1 zero_lt_one 1 a
  have hi := congrArg (hodgeInclusion A J α hs ht) hb
  rw [hodgeInclusion_smooth,hodgeGraphResolvent_inclusion_power, pow_one,
    hodgeInclusion_smooth] at hi
  refine ⟨b,hi,?_⟩
  have hinv := hodgeResolvent_differential_inverse A J α hs ht 1 zero_lt_one b
  simp only [one_pow,one_smul] at hinv
  rw [map_add (smoothL2 A J α hs ht true)] at hinv
  have hsum := hodgeResolvent_injective A J α hs ht 1 zero_lt_one (hinv.trans hi)
  exact eq_sub_of_add_eq' hsum

include D hD in

lemma hodgeWeakHeat_zero (U : ℝ → L2 A J α hs ht true) {T : ℝ} (hT : 0 ≤ T)
    (hU : ContinuousOn U (Icc 0 T)) (hzero : U 0 = 0)
    (hweak : ∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
        (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t) :
    ∀ t ∈ Icc 0 T, U t = 0 := by
  apply WeakHeat.zero_of_resolvent_weak (hodgeResolvent A J α hs ht 1)
    (hodgeResolvent_injective A J α hs ht 1 zero_lt_one)
    (hodgeResolvent_symmetric A J α hs ht 1)
    (hodgeResolvent_energy_le A J α hs ht 1 zero_lt_one)
    (Set.range (smoothL2 A J α hs ht true)) (smoothL2_dense A J α hs ht true)
    U hT hU hzero
  rintro _ ⟨a,rfl⟩ t ht'
  obtain ⟨b,hb,hDb⟩ := hodgeResolvent_smooth_core A J α hs ht D hD a
  have hh := hweak b t ht'
  rw [hDb,hb] at hh
  exact hh

include D hD in

lemma hodgeWeakHeat_eq_spectral (f : L2 A J α hs ht true)
    (U : ℝ → L2 A J α hs ht true) {T : ℝ} (hT : 0 ≤ T)
    (hU : ContinuousOn U (Icc 0 T)) (hzero : U 0 = f)
    (hweak : ∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
        (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t) :
    ∀ t ∈ Icc 0 T, U t = hodgeSpectralHeat A J α hs ht D hD t f := by
  have hh := hodgeWeakHeat_zero A J α hs ht D hD
    (fun t => U t-hodgeSpectralHeat A J α hs ht D hD t f) hT
    (hU.sub (hodgeSpectralHeat_continuous A J α hs ht D hD f).continuousOn) ?_ ?_
  · intro t ht'
    exact sub_eq_zero.mp (hh t ht')
  · simp [hzero,hodgeSpectralHeat_zero]
  · intro a t ht'
    have hd := (hweak a t ht').sub
      (hodgeSpectralHeat_weak_hasDerivAt A J α hs ht D hD f a t ht'.1)
    convert! hd using 1
    · funext s
      exact inner_sub_left _ _ _
    · rw [inner_sub_left]
      ring

end TamingCompatibility.GeometricHilbert

end
end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWeakCompact
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.WeakHeat
open Set Filter Topology
open scoped Topology RealInnerProductSpace
variable {H T I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [TopologicalSpace T]

lemma inner_continuousOn_of_dense (D : I → H) (hD : DenseRange D)
    (U : T → H) (S : Set T) {C : ℝ} (hC : 0 ≤ C) (hU : ∀ t ∈ S, ‖U t‖ ≤ C)
    (hweak : ∀ a, ContinuousOn (fun t => ⟪U t,D a⟫) S) (v : H) :
    ContinuousOn (fun t => ⟪U t,v⟫) S := by
  intro t ht
  apply Metric.continuousWithinAt_iff'.mpr
  intro ε hε
  have hp : 0 < C+1 := by linarith
  obtain ⟨a,ha⟩ := hD.exists_dist_lt v (div_pos hε (mul_pos (show (0:ℝ)<4 by norm_num) hp))
  have ha' : ‖v-D a‖ < ε/(4*(C+1)) := by simpa only [dist_eq_norm] using ha
  have herr : C*‖v-D a‖ < ε/4 := by
    calc
      _ ≤ (C+1)*‖v-D a‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C+1)*(ε/(4*(C+1))) := mul_lt_mul_of_pos_left ha' hp
      _ = _ := by field_simp
  have he (s : T) (hs : s ∈ S) : dist ⟪U s,v⟫ ⟪U s,D a⟫ < ε/4 := by
    rw [Real.dist_eq,← inner_sub_right]
    exact ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hU s hs) (norm_nonneg _))).trans_lt herr
  have hh := Metric.continuousWithinAt_iff'.mp (hweak a t ht) (ε/2) (by linarith)
  filter_upwards [hh,self_mem_nhdsWithin] with s hs hsS
  have hd := dist_triangle4 ⟪U s,v⟫ ⟪U s,D a⟫ ⟪U t,D a⟫ ⟪U t,v⟫
  have he₁ := he s hsS
  have he₂ := he t ht
  rw [dist_comm ⟪U t,D a⟫ ⟪U t,v⟫] at hd
  linarith

lemma continuousOn_of_weak_compact_range (U : T → H) (S : Set T)
    (K : Set H) (hK : IsCompact K) (hUK : ∀ t ∈ S, U t ∈ K)
    (hweak : ∀ v : H, ContinuousOn (fun t => ⟪U t,v⟫) S) : ContinuousOn U S := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : K → H → ℝ := fun x v => ⟪x.val,v⟫
  have hF : Continuous F := continuous_pi (fun _ => continuous_subtype_val.inner continuous_const)
  have hFi : Function.Injective F := by
    intro x y h
    apply Subtype.ext
    apply ext_inner_right ℝ
    intro v
    exact congrFun h v
  have hFe := (hF.isClosedEmbedding hFi).isEmbedding
  let V : S → K := fun t => ⟨U t.val,hUK t.val t.property⟩
  have hV : Continuous V := hFe.continuous_iff.mpr (continuous_pi (fun v =>
    (continuousOn_iff_continuous_domRestrict.mp (hweak v))))
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hV)

lemma compact_symmetric_continuousOn (R : H →L[ℝ] H) (hR : IsCompactOperator R)
    (hRs : ∀ u v, ⟪R u,v⟫ = ⟪u,R v⟫)
    (D : I → H) (hD : DenseRange D) (U : T → H) (S : Set T)
    {C : ℝ} (hC : 0 ≤ C) (hU : ∀ t ∈ S, ‖U t‖ ≤ C)
    (hweak : ∀ a, ContinuousOn (fun t => ⟪U t,D a⟫) S) :
    ContinuousOn (fun t => R (U t)) S := by
  obtain ⟨K,hK,hRK⟩ := hR.image_closedBall_subset_compact C
  apply continuousOn_of_weak_compact_range _ S K hK
  · intro t ht
    exact hRK ⟨U t,by simpa only [Metric.mem_closedBall,dist_zero_right] using hU t ht,rfl⟩
  · intro v
    simp_rw [hRs]
    exact inner_continuousOn_of_dense D hD U S hC hU hweak (R v)

end TamingCompatibility.GeometricHilbert.WeakHeat

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeBoundedWeakHeat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] in
lemma hodgeResolvent_laplacian_core (a : PreL2 A J α hs ht true) :
    hodgeResolvent A J α hs ht 1
      (smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)) =
    smoothL2 A J α hs ht true a -
      hodgeResolvent A J α hs ht 1 (smoothL2 A J α hs ht true a) := by
  have hi := hodgeResolvent_differential_inverse A J α hs ht 1 zero_lt_one a
  simp only [one_pow,one_smul,map_add] at hi
  exact eq_sub_of_add_eq' hi

omit [T2Space X] in
lemma hodgeSpectralHeat_resolvent (t : ℝ) (f : L2 A J α hs ht true) :
    hodgeSpectralHeat A J α hs ht D hD t (hodgeResolvent A J α hs ht 1 f) =
      hodgeResolvent A J α hs ht 1 (hodgeSpectralHeat A J α hs ht D hD t f) := by
  have he := hodgeBoundedSpectralMultiplier_commutes A J α hs ht D hD
    (hodgeHeatMultiplier t) 1 zero_le_one
    (fun x => (abs_of_pos (hodgeHeatMultiplier_pos t x)).trans_le (hodgeHeatMultiplier_le_one t x))
    (hodgeResolvent A J α hs ht 1) (fun _ => rfl)
  exact congrArg (fun T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => T f) he

include D hD in
lemma hodgeBoundedWeakHeat_eq_spectral (f : L2 A J α hs ht true)
    (U : ℝ → L2 A J α hs ht true) {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hU : ∀ t ∈ Icc 0 T, ‖U t‖ ≤ C)
    (hc : ∀ a : PreL2 A J α hs ht true,
      ContinuousOn (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (Icc 0 T))
    (hzero : U 0 = f)
    (hweak : ∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioo 0 T,
      HasDerivAt (fun s => ⟪U s,smoothL2 A J α hs ht true a⟫)
        (-⟪U t,smoothL2 A J α hs ht true (hodgeLaplacian A J α hs ht a)⟫) t) :
    ∀ t ∈ Icc 0 T, U t = hodgeSpectralHeat A J α hs ht D hD t f := by
  let R := hodgeResolvent A J α hs ht 1
  have hcont : ContinuousOn (fun t => R (U t)) (Icc 0 T) :=
    WeakHeat.compact_symmetric_continuousOn R
      (hodgeResolvent_compact A J α hs ht D hD 1 zero_lt_one)
      (hodgeResolvent_symmetric A J α hs ht 1)
      (smoothL2 A J α hs ht true) (smoothL2_dense A J α hs ht true)
      U (Icc 0 T) hC hU hc
  have he := hodgeWeakHeat_eq_spectral A J α hs ht D hD (R f)
    (fun t => R (U t)) hT hcont (congrArg R hzero) ?_
  · intro t ht'
    apply hodgeResolvent_injective A J α hs ht 1 zero_lt_one
    exact (he t ht').trans (hodgeSpectralHeat_resolvent A J α hs ht D hD t f)
  · intro a t ht'
    obtain ⟨b,hb,hDb⟩ := hodgeResolvent_smooth_core A J α hs ht D hD a
    have hh := hweak b t ht'
    rw [hDb,hb] at hh
    dsimp only [R]
    have hsym (u v : L2 A J α hs ht true) :
        ⟪hodgeResolvent A J α hs ht 1 u,v⟫ = ⟪u,hodgeResolvent A J α hs ht 1 v⟫ :=
      hodgeResolvent_symmetric A J α hs ht 1 u v
    simp_rw [hsym]
    rw [hodgeResolvent_laplacian_core A J α hs ht a]
    exact hh

end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeVolterraKernel
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
namespace TamingCompatibility.GeometricHilbert.VolterraBounds
open _root_.MeasureTheory Set Metric
open scoped Topology
variable {X B : Type*} [PseudoMetricSpace X]

lemma weight_one_le (N : ℕ) {t : ℝ} (ht : 0 < t) (x y : X) :
    1 ≤ weight N t x y := by
  apply one_le_pow₀
  have := div_nonneg (dist_nonneg (x := x) (y := y)) (Real.sqrt_pos.2 ht).le
  linarith

end TamingCompatibility.GeometricHilbert.VolterraBounds

end
end

end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeHeatWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.VolterraKernel
open _root_.MeasureTheory Set VolterraBounds
variable {X B : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [NormedRing B]
  (μ : Measure X)

lemma HeatBound.weight_zero {N : ℕ} {T A : ℝ} {K : Kernel (X := X) (B := B)}
    (h : HeatBound μ N T A K) : HeatBound μ 0 T A K := by
  have hb (t : ℝ) (ht : t ∈ Ioc 0 T) (x y : X) :
      ‖K t x y‖ ≤ weight N t x y*‖K t x y‖ := by
    exact le_mul_of_one_le_left (norm_nonneg _) (weight_one_le N ht.1 x y)
  have hr (t : ℝ) (ht : t ∈ Ioc 0 T) (x : X) :
      Integrable (fun y => ‖K t x y‖) μ := by
    apply (h.row_int t ht x).mono' (((kernel_section K h.measurable t).comp_measurable
      (measurable_const.prodMk measurable_id)).norm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun y => by simpa using hb t ht x y
  have hc (t : ℝ) (ht : t ∈ Ioc 0 T) (y : X) :
      Integrable (fun x => ‖K t x y‖) μ := by
    apply (h.col_int t ht y).mono' (((kernel_section K h.measurable t).comp_measurable
      (measurable_id.prodMk measurable_const)).norm.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by simpa using hb t ht x y
  refine ⟨h.measurable,h.nonneg,?_,?_,?_,?_,?_⟩
  · intro t ht x y
    simpa only [weight,pow_zero,one_mul] using (hb t ht x y).trans (h.sup t ht x y)
  · intro t ht x
    simpa only [weight,pow_zero,one_mul] using hr t ht x
  · intro t ht x
    simpa only [weight,pow_zero,one_mul] using
      (integral_mono (hr t ht x) (h.row_int t ht x) (fun y => hb t ht x y)).trans (h.row t ht x)
  · intro t ht y
    simpa only [weight,pow_zero,one_mul] using hc t ht y
  · intro t ht y
    simpa only [weight,pow_zero,one_mul] using
      (integral_mono (hc t ht y) (h.col_int t ht y) (fun x => hb t ht x y)).trans (h.col t ht y)

end TamingCompatibility.GeometricHilbert.VolterraKernel

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_ResolventGammaScalar
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization _root_.MeasureTheory Set
open scoped Manifold ContDiff RealInnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeHeatGamma_eigenvector (r : ℝ)
    (x : ℝ) (f : L2 A J α hs ht true) (hf : f ≠ 0)
    (hx : hodgeResolvent A J α hs ht 1 f = x • f) :
    hodgeHeatGamma A J α hs ht D hD r f =
      (120 * (x/(r^2+(1-r^2)*x))^6) • f := by
  obtain ⟨hx0,hx1⟩ := hodgeResolvent_eigenvalue_positive_le_one A J α hs ht f hf x hx
  have hxinv : 1 ≤ x⁻¹ := (one_le_inv₀ hx0).mpr hx1
  have hrate : hodgeSpectralRate x = x⁻¹-1 := max_eq_right (sub_nonneg.mpr hxinv)
  have he : (∫ s : ℝ in Ioi 0,
      hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) =
      (∫ s : ℝ in Ioi 0, hodgeGammaWeight s * Real.exp (-(r^2*s)*hodgeSpectralRate x)) • f := by
    rw [← integral_smul_const]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hsp
    dsimp only
    rw [hodgeSpectralHeat_eigenvector A J α hs ht D hD _ x f hx]
    simp only [hodgeHeatMultiplier, max_eq_left (mul_nonneg (sq_nonneg r) hsp.le), smul_smul]
  change (∫ s : ℝ in Ioi 0, hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) = _
  rw [he, hodgeGammaWeight_laplace r (hodgeSpectralRate x) (le_max_left 0 (x⁻¹-1))]
  have hd : r^2+(1-r^2)*x ≠ 0 := by
    have hp := mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hx1)
    apply ne_of_gt
    nlinarith
  have hz := ne_of_gt (show 0 < 1+r^2*hodgeSpectralRate x by
    have hp := mul_nonneg (sq_nonneg r) (le_max_left 0 (x⁻¹-1)); dsimp [hodgeSpectralRate] <;> linarith)
  have heq : 1/(1+r^2*hodgeSpectralRate x) = x/(r^2+(1-r^2)*x) := by
    rw [hrate] at hz ⊢
    field_simp [ne_of_gt hx0, hd, hz]
    ring
  rw [heq]

lemma hodgeHeatGamma_eq_sixth_power (r : ℝ) (hr : 0 < r) :
    hodgeHeatGamma A J α hs ht D hD r = (120 : ℝ) • (hodgeRegularization A J α hs ht r ^ 2) := by
  let L := hodgeHeatGamma A J α hs ht D hD r - (120 : ℝ) • (hodgeRegularization A J α hs ht r ^ 2)
  have hi : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x) ≤ L.ker := by
    apply iSup_le
    intro x f hf
    have hx := Module.End.mem_eigenspace_iff.mp hf
    change L f = 0
    by_cases hzero : f = 0
    · subst f; exact map_zero L
    · obtain ⟨hx0,hx1⟩ := hodgeResolvent_eigenvalue_positive_le_one A J α hs ht f hzero x hx
      dsimp [L]
      rw [sub_apply, smul_apply,
        hodgeHeatGamma_eigenvector A J α hs ht D hD r x f hzero hx,
        hodgeRegularization_sq_eigenvector A J α hs ht r hr f x hx0.le hx1 hx,
        smul_smul, sub_self]
  have hcl : (⨆ x : ℝ, Module.End.eigenspace
      (hodgeResolvent A J α hs ht 1).toLinearMap x).topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,
      hodgeResolvent_eigenspaces_total A J α hs ht D hD]
    simp
  have htop : ⊤ ≤ L.ker := by
    rw [← hcl]
    exact Submodule.topologicalClosure_minimal _ hi (ContinuousLinearMap.isClosed_ker L)
  ext f
  have hf : L f = 0 := htop (Submodule.mem_top)
  exact sub_eq_zero.mp hf

lemma hodgeRegularization_sq_eq_heat_integral (r : ℝ) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    (hodgeRegularization A J α hs ht r ^ 2) f = (1/120 : ℝ) •
      (∫ s : ℝ in Ioi 0,
        hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) := by
  have he := congrArg (fun T : L2 A J α hs ht true →L[ℝ] L2 A J α hs ht true => T f)
    (hodgeHeatGamma_eq_sixth_power A J α hs ht D hD r hr)
  change (∫ s : ℝ in Ioi 0,
    hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) =
      (120 : ℝ) • (hodgeRegularization A J α hs ht r ^ 2) f at he
  rw [he, smul_smul]
  norm_num

end TamingCompatibility.GeometricHilbert

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
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGammaSplit
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.frameMap_apply _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalDifferential_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalGauge_zero _root_.OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.normalMap_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization Set _root_.MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeGammaTailAction_bound {T r : ℝ} (hT : 0 ≤ T) (f : L2 A J α hs ht true) :
    ‖hodgeGammaTailAction A J α hs ht D hD T r f‖ ≤
      (1/120 : ℝ) * HodgeKernelBounds.gammaTail (T/r^2) * ‖f‖ := by
  have hcut : 0 ≤ T/r^2 := div_nonneg hT (sq_nonneg r)
  have hsub : Ioi (T/r^2) ⊆ Ioi (0:ℝ) := fun _ hx => hcut.trans_lt hx
  have hi := (hodgeHeatGamma_integrable A J α hs ht D hD r f).mono_set hsub
  have hw := hodgeGammaWeight_integrable.mono_set hsub
  have hh : ‖∫ s : ℝ in Ioi (T/r^2),
      hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f‖ ≤
      HodgeKernelBounds.gammaTail (T/r^2)*‖f‖ := by
    calc
      _ ≤ ∫ s : ℝ in Ioi (T/r^2),
          ‖hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ s : ℝ in Ioi (T/r^2), hodgeGammaWeight s*‖f‖ := by
        apply integral_mono_ae hi.norm (hw.mul_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
        have hs0 : 0 ≤ s := (hcut.trans_lt hsp).le
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hodgeGammaWeight_nonneg hs0)]
        exact mul_le_mul_of_nonneg_left (hodgeSpectralHeat_norm_le A J α hs ht D hD _ f)
          (hodgeGammaWeight_nonneg hs0)
      _ = _ := by rw [integral_mul_const]; rfl
  unfold hodgeGammaTailAction
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/120)]
  exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans_eq (by ring)

lemma hodgeGammaTailAction_rapid (N : ℕ) {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    ‖hodgeGammaTailAction A J α hs ht D hD T r f‖ ≤
      ((1/120 : ℝ) * HodgeKernelBounds.moment 5 (1/2) * (N.factorial : ℝ) * (2/T)^N) *
        r^(2*N)*‖f‖ := by
  apply (hodgeGammaTailAction_bound A J α hs ht D hD hT.le f).trans
  have hh := HodgeKernelBounds.gammaTail_small_scale N hT hr
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh
    (by norm_num : (0:ℝ) ≤ 1/120)) (norm_nonneg f)
  convert hb using 1 <;> first | rfl | ring

lemma hodgeRegularization_gamma_split {T r : ℝ} (hT : 0 ≤ T) (hr : 0 < r)
    (f : L2 A J α hs ht true) :
    (hodgeRegularization A J α hs ht r ^ 2) f =
      (1/120 : ℝ) • (∫ s : ℝ in Ioc 0 (T/r^2),
        hodgeGammaWeight s • hodgeSpectralHeat A J α hs ht D hD (r^2*s) f) +
      hodgeGammaTailAction A J α hs ht D hD T r f := by
  have hi := hodgeHeatGamma_integrable A J α hs ht D hD r f
  have hcut : 0 ≤ T/r^2 := div_nonneg hT (sq_nonneg r)
  rw [hodgeRegularization_sq_eq_heat_integral A J α hs ht D hD r hr f,
    ← Ioc_union_Ioi_eq_Ioi hcut,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hi.mono_set (fun _ hx => hx.1)) (hi.mono_set (fun _ hx => hcut.trans_lt hx)),smul_add]
  rfl

lemma hodgeRegularization_gamma_test_split {T r : ℝ} (hT : 0 ≤ T) (hr : 0 < r)
    (f g : L2 A J α hs ht true) :
    ⟪(hodgeRegularization A J α hs ht r ^ 2) f,g⟫ =
      (1/120 : ℝ) * (∫ s : ℝ in Ioc 0 (T/r^2),
        hodgeGammaWeight s * ⟪hodgeSpectralHeat A J α hs ht D hD (r^2*s) f,g⟫) +
      ⟪hodgeGammaTailAction A J α hs ht D hD T r f,g⟫ := by
  rw [hodgeRegularization_gamma_split A J α hs ht D hD hT hr f,inner_add_left,real_inner_smul_left]
  congr 2
  have hi := (hodgeHeatGamma_integrable A J α hs ht D hD r f).mono_set
    (show Ioc 0 (T/r^2) ⊆ Ioi (0:ℝ) from fun _ hx => hx.1)
  rw [real_inner_comm,← integral_inner hi g]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    dsimp only
    rw [real_inner_smul_right,real_inner_comm]

end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeContinuousParametrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

variable (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

include hE D hD in
lemma globalCandidate_continuous_eq_spectral (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      (∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => globalError J α ht A E T t p.1 p.2)) ∧
      ∀ v : X → FrameSpace A, Continuous v →
      ∃ f : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪f,smoothL2 A J α hs ht true a⟫ =
            ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
        (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
          ⟪hodgeSpectralHeat A J α hs ht D hD t f,smoothL2 A J α hs ht true a⟫ =
            kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
            kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨T,L,C,hT,hT1,hL,hC,_hCc,hEc,hcancel⟩ := globalCorrection_continuous_bounds A J α hs ht E hE n
  refine ⟨T,L,C,hT,hT1,hL,hC,hEc,?_⟩
  intro v hv
  obtain ⟨f,U,M,hM,hzero,hbound,hf,hpair,hcont,hweak⟩ :=
    globalCandidate_evolution_of_bounds A J α hs ht E hE hT hT1
      (hL.weight_zero _) (hC.weight_zero _) hcancel v hv
  have he := hodgeBoundedWeakHeat_eq_spectral A J α hs ht D hD f U hT.le hM hbound hcont hzero hweak
  refine ⟨f,hf,?_⟩
  intro a t ht'
  rw [← he t ⟨ht'.1.le,ht'.2⟩]
  exact hpair a t ht'

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_HeatFlow_HodgeContinuousResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter _root_.MeasureTheory
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
attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE D hD in
lemma same_resolvent_continuous_data_oai (n : ℕ) :
    let := geometricMetricSpace J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A E) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A E T) ∧
      (∀ t ∈ Ioc 0 T, Continuous (fun p : X × X => globalError J α ht A E T t p.1 p.2)) ∧
      ∀ v : X → FrameSpace A, Continuous v →
      ∃ f : L2 A J α hs ht true,
        (∀ a : PreL2 A J α hs ht true,
          ⟪f,smoothL2 A J α hs ht true a⟫ =
            ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
        (∀ r : ℝ, 0 < r → ∀ a : PreL2 A J α hs ht true,
          ⟪(hodgeRegularization A J α hs ht r ^ 2) f,smoothL2 A J α hs ht true a⟫ =
            (1/120 : ℝ) * (∫ s : ℝ in Ioc 0 (T/r^2), hodgeGammaWeight s *
              (kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val (r^2*s) +
               kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val (r^2*s))) +
            ⟪hodgeGammaTailAction A J α hs ht D hD T r f,smoothL2 A J α hs ht true a⟫) ∧
        (∀ N : ℕ, ∀ r : ℝ, 0 < r →
          ‖hodgeGammaTailAction A J α hs ht D hD T r f‖ ≤
            ((1/120 : ℝ) * HodgeKernelBounds.moment 5 (1/2) * (N.factorial : ℝ) * (2/T)^N) *
              r^(2*N)*‖f‖) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  obtain ⟨T,L,C,hT,hT1,hL,hC,hEc,hheat⟩ := globalCandidate_continuous_eq_spectral A J α hs ht E hE D hD n
  refine ⟨T,L,C,hT,hT1,hL,hC,hEc,?_⟩
  intro v hv
  obtain ⟨f,hf,hpair⟩ := hheat v hv
  refine ⟨f,hf,?_,fun N r hr => hodgeGammaTailAction_rapid A J α hs ht D hD N hT hr f⟩
  intro r hr a
  rw [hodgeRegularization_gamma_test_split A J α hs ht D hD hT.le hr]
  congr 2
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsp
  have hsq : 0 < r^2 := sq_pos_of_pos hr
  have hst : r^2*s ∈ Ioc 0 T := ⟨mul_pos hsq hsp.1,by
    have hh := (le_div_iff₀ hsq).mp hsp.2
    simpa only [mul_comm] using hh⟩
  rw [hpair a _ hst]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_continuous_data_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.same_resolvent_continuous_data_oai.{u_1}
