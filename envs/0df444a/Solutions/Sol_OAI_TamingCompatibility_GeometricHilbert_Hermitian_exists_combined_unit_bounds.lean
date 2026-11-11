-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_combined_unit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:35:45.068619+00:00
-- url     : https://prove2.me/submissions/13990b15-d69d-4b3d-a55c-206383fab691

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc034
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_combinedForm_global_lower
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_Hermitian_exists_positive_combination

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCoefficientBounds
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_complexLine (J : AlmostComplexStructure X) (β : TwoForm X) (p : X)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback β (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      eval β ((extChartAt Model p).symm y) (mfderiv Model Model (extChartAt Model p).symm y v)
        (J.endomorphism _ (mfderiv Model Model (extChartAt Model p).symm y v)) := by
  have hi := coordinateJ_intertwine J p hy v
  change (inverseChartEquiv p y hy).toContinuousLinearMap (coordinateJ J p y v) =
    J.endomorphism _ ((inverseChartEquiv p y hy).toContinuousLinearMap v) at hi
  rw [inverseChartEquiv_coe] at hi
  change β _ ((mfderiv Model Model (extChartAt Model p).symm y) ∘ ![v,coordinateJ J p y v]) = _
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact hi

end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactPositiveBilinear
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility
open Set

lemma compact_positive_bilinear_bounds {Y E : Type*} [TopologicalSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
    {K : Set Y} (hK : IsCompact K) {g : Y → E →L[ℝ] E →L[ℝ] ℝ}
    (hg : ContinuousOn g K) (hpos : ∀ z ∈ K, ∀ v : E, v ≠ 0 → 0 < g z v v) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : E,
      m*‖v‖^2 ≤ g z v v ∧ g z v v ≤ M*‖v‖^2 := by
  by_cases hne : K.Nonempty
  · let q : Y × E → ℝ := fun x => g x.1 x.2 x.2
    have hq : ContinuousOn q (K ×ˢ Metric.sphere (0:E) 1) :=
      ((hg.comp continuousOn_fst (fun _ hx => hx.1)).clm_apply continuousOn_snd).clm_apply
        continuousOn_snd
    obtain ⟨x,hx,hmin⟩ := (hK.prod (isCompact_sphere (0:E) 1)).exists_isMinOn
      (hne.prod (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1))) hq
    have hxnorm : ‖x.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx.2
    have hqx : 0 < q x := hpos x.1 hx.1 x.2 (by intro h; simp [h] at hxnorm)
    obtain ⟨y,hy,hmax⟩ := (hK.prod (isCompact_sphere (0:E) 1)).exists_isMaxOn
      (hne.prod (NormedSpace.sphere_nonempty.mpr (by norm_num : (0:ℝ) ≤ 1))) hq
    refine ⟨q x,max (q y) 1,hqx,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
    intro z hz v
    by_cases hv : v = 0
    · simp [hv]
    · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      let w := ‖v‖⁻¹ • v
      have hw : w ∈ Metric.sphere (0:E) 1 := by
        simp [w,norm_smul,inv_mul_cancel₀ hnv]
      have hid : g z w w * ‖v‖^2 = g z v v := by
        simp only [w,map_smul,_root_.smul_apply,smul_eq_mul]
        field_simp
      have hlo := mul_le_mul_of_nonneg_right (hmin (show (z,w) ∈ K ×ˢ Metric.sphere (0:E) 1 from ⟨hz,hw⟩)) (sq_nonneg ‖v‖)
      have hup := mul_le_mul_of_nonneg_right
        ((hmax (show (z,w) ∈ K ×ˢ Metric.sphere (0:E) 1 from ⟨hz,hw⟩)).trans (le_max_left (q y) 1)) (sq_nonneg ‖v‖)
      change q x * ‖v‖^2 ≤ g z w w * ‖v‖^2 at hlo
      change g z w w * ‖v‖^2 ≤ max (q y) 1 * ‖v‖^2 at hup
      rw [hid] at hlo hup
      exact ⟨hlo,hup⟩
  · refine ⟨1,1,zero_lt_one,zero_lt_one,?_⟩
    intro z hz
    exact (hne ⟨z,hz⟩).elim
end TamingCompatibility

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianUnitMetric
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldVolume
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J)

include hs ht in
lemma chartMetric_compact_bounds (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : Space,
      m*‖v‖^2 ≤ chartMetric J α p z v v ∧ chartMetric J α p z v v ≤ M*‖v‖^2 :=
  compact_positive_bilinear_bounds hK (((hs.invariantPart J).metricCoords J p).continuousOn.mono hKT)
    (fun _z hz v hv => chartMetric_pos J α ht p (hKT hz) v hv)

include hs ht in
lemma chartMetric_unit_norm_bounds (p : X) {K : Set Space} (hK : IsCompact K)
    (hKT : K ⊆ (extChartAt Model p).target) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ z ∈ K, ∀ v : Space,
      chartMetric J α p z v v = 1 → m ≤ ‖v‖^2 ∧ ‖v‖^2 ≤ M := by
  obtain ⟨a,b,ha,hb,hbound⟩ := chartMetric_compact_bounds J α hs ht p hK hKT
  refine ⟨1/b,1/a,by positivity,by positivity,?_⟩
  intro z hz v hv
  obtain ⟨hlo,hup⟩ := hbound z hz v
  rw [hv] at hlo hup
  exact ⟨(div_le_iff₀ hb).mpr (by simpa only [mul_comm] using hup),
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hlo)⟩

lemma inverse_coordinates_eval (p : X) {z : Space} (hz : z ∈ (extChartAt Model p).target)
    (β : TwoForm X) (u : TangentSpace Model ((extChartAt Model p).symm z)) :
    ∃ v : Space,
      chartMetric J α p z v v = (hermitianMetric J α hs ht).inner _ u u ∧
      ManifoldForms.pullback β (extChartAt Model p).symm z ![v,coordinateJ J p z v] =
        eval β ((extChartAt Model p).symm z) u (J.endomorphism _ u) := by
  let L := inverseChartEquiv p z hz
  have he : mfderiv Model Model (extChartAt Model p).symm z (L.symm u) = u := by
    rw [← inverseChartEquiv_coe p z hz]
    exact L.apply_symm_apply u
  refine ⟨L.symm u,?_,?_⟩
  · rw [chartMetric_derivative J α p hz,he]
    rfl
  · rw [pullback_complexLine J β p hz,he]

lemma unitEvaluation_lower_of_chart (p : X) {K : Set Space} {c : ℝ}
    (β : TwoForm X) (hβ : IsSmooth β)
    (hbound : ∀ z ∈ K, ∀ v : Space, chartMetric J α p z v v = 1 →
      c ≤ ManifoldForms.pullback β (extChartAt Model p).symm z ![v,coordinateJ J p z v])
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source)
    (hzK : extChartAt Model p u.val.proj ∈ K) :
    c ≤ unitEvaluation J (hermitianMetric J α hs ht) β hβ u := by
  let z := extChartAt Model p u.val.proj
  have hz : z ∈ (extChartAt Model p).target := (extChartAt Model p).map_source hu
  have hb : ∀ w : TangentSpace Model ((extChartAt Model p).symm z),
      (hermitianMetric J α hs ht).inner _ w w = 1 →
      c ≤ eval β ((extChartAt Model p).symm z) w (J.endomorphism _ w) := by
    intro w hw
    obtain ⟨v,hv,he⟩ := inverse_coordinates_eval J α hs ht p hz β w
    exact he ▸ hbound z hzK v (hv.trans hw)
  have hbase : (extChartAt Model p).symm z = u.val.proj := (extChartAt Model p).left_inv hu
  rw [hbase] at hb
  exact hb u.val.2 u.property
end TamingCompatibility.ManifoldVolume

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianGlobalLower
attribute [-instance] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeEnergy_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix _root_.MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)
variable (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

include hD hH hweak hB hdual hU hτ hρ hK hφone hK₀ in

theorem exists_combined_unit_bounds_oai (hR1 : 2*R ≤ 1) :
    ∃ a c r C : ℝ, 0 < a ∧ 0 < c ∧ 0 < r ∧ r ≤ 2*R ∧ 0 ≤ C ∧
      ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) r, ∀ b, ∀ hb : b ∈ K₀,
      let β := combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))
      (∀ u : MetricUnit (hermitianMetric J α hs ht),
        -C ≤ unitEvaluation J (hermitianMetric J α hs ht) β.val β.property u) ∧
      (∀ u : MetricUnit (hermitianMetric J α hs ht),
        u.val.proj ∈ (extChartAt Model p.val).symm '' Metric.closedBall b s →
        c/s^2 ≤ unitEvaluation J (hermitianMetric J α hs ht) β.val β.property u) := by
  obtain ⟨a,c,δ,ha,hc',hδ,hpos⟩ := exists_positive_combination
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1
  have hnear : ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ K, s+‖y-b‖ < min δ R → ∀ v : Space,
      0 ≤ ManifoldForms.pullback
        (combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := by
    intro s hsr b hb y hy hn v
    exact (hpos s hsr b hb y hy (lt_of_lt_of_le hn (min_le_left _ _)) v).1
  obtain ⟨C,hC,hglobal⟩ := combinedForm_global_lower
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 a (min δ R) ha.le
      (lt_min hδ hR) (min_le_right _ _) hnear
  obtain ⟨m,M,hm,_hM,hmetric⟩ := chartMetric_unit_norm_bounds J α hs ht p.val hK
    (hKU.trans (hUD.trans (D p).domain_subset))
  let r := min R (δ/4)
  have hr : 0 < r := lt_min hR (by positivity)
  have hrR : r ≤ 2*R := (min_le_left R (δ/4)).trans (by linarith)
  refine ⟨a,c*m,r,C,ha,by positivity,hr,hrR,hC,?_⟩
  intro s hsr b hb
  let β := combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))
  have hsR : s ∈ Ioc (0:ℝ) (2*R) := ⟨hsr.1,hsr.2.trans hrR⟩
  refine ⟨hglobal s hsR b hb,?_⟩
  intro u hu
  have hballK : Metric.closedBall b s ⊆ K :=
    (Metric.closedBall_subset_closedBall hsR.2).trans (hcenters b hb)
  obtain ⟨z,hz,hzu⟩ := hu
  have hzT := (D p).domain_subset (hUD (hKU (hballK hz)))
  have huSrc : u.val.proj ∈ (extChartAt Model p.val).source :=
    hzu ▸ (extChartAt Model p.val).map_target hzT
  have he : extChartAt Model p.val u.val.proj = z := by
    rw [← hzu,(extChartAt Model p.val).right_inv hzT]
  apply unitEvaluation_lower_of_chart J α hs ht p.val β.val β.property
    (K := Metric.closedBall b s) ?_ u huSrc (he ▸ hz)
  intro y hy v hv
  have hyd : ‖y-b‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
  have hn : s+‖y-b‖ < δ := by
    have hsd := hsr.2.trans (min_le_right R (δ/4))
    linarith
  have hval := (hpos s hsR b hb y (hballK hy) hn v).2 hyd
  have hmv := (hmetric y (hballK hy) v hv).1
  apply le_trans _ hval
  have hmul := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hmv (sq_nonneg s)) hc'.le
  simpa only [mul_div_assoc] using hmul
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_combined_unit_bounds_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.Hermitian.exists_combined_unit_bounds_oai.{u_1}
