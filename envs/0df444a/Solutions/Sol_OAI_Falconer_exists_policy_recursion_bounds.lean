-- Prove2me | solution 1 for OAI.Falconer.exists_policy_recursion_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:20:34.631649+00:00
-- url     : https://prove2.me/submissions/faf2fbf8-956a-4039-bd0e-00d3c66dba1f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_exists_far_data_bound
import Theorems.Thm_OAI_Falconer_exists_policy_positive_common_budgets

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_FinsetSchur
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finset_bipartite_schur {α β : Type*} (A : Finset α) (B : Finset β)
    (G : α → β → Prop) [DecidableRel G] (u : α → ℝ) (v : β → ℝ) (d : ℝ)
    (hrow : ∀ a ∈ A, ((B.filter (G a)).card : ℝ) ≤ d)
    (hcol : ∀ b ∈ B, ((A.filter (fun a => G a b)).card : ℝ) ≤ d) :
    (∑ a ∈ A, ∑ b ∈ B, if G a b then u a*v b else 0) ≤
      d/2*((∑ a ∈ A, u a^2)+(∑ b ∈ B, v b^2)) := by
  have hp (a : α) (b : β) : 2*(if G a b then u a*v b else 0) ≤
      (if G a b then u a^2 else 0)+(if G a b then v b^2 else 0) := by
    split_ifs
    · nlinarith [sq_nonneg (u a-v b)]
    · norm_num
  have hs := Finset.sum_le_sum (s := A) (fun a _ =>
    Finset.sum_le_sum (s := B) (fun b _ => hp a b))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hs
  have hR : (∑ a ∈ A, ∑ b ∈ B, if G a b then u a^2 else 0) ≤ d*(∑ a ∈ A, u a^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hrow a ha) (sq_nonneg _)
  have hC : (∑ a ∈ A, ∑ b ∈ B, if G a b then v b^2 else 0) ≤ d*(∑ b ∈ B, v b^2) := by
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcol b hb) (sq_nonneg _)
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_AllDimensionalGraphGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Geometry of the retained graph in arbitrary dimension

The graph tests use orthogonal distance to a line and one scalar longitudinal
constraint. Each longitudinal constraint is in the unknown endpoint's own
cap direction. In particular these bounds do not divide by the angle between
the two endpoint directions.
-/

namespace Falconer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Moving a unit direction changes the perpendicular test by at most twice
its angular displacement times the size of the tested vector. -/
theorem perpendicularPart_direction_error {w z : E} (hw : ‖w‖ = 1) (hz : ‖z‖ = 1)
    (v : E) :
    ‖perpendicularPart w v - perpendicularPart z v‖ ≤ 2 * ‖w-z‖ * ‖v‖ := by
  have he : perpendicularPart w v - perpendicularPart z v =
      inner ℝ z v • (z-w) + inner ℝ (z-w) v • w := by
    simp only [perpendicularPart, inner_sub_left, sub_smul, smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖inner ℝ z v • (z-w)‖ + ‖inner ℝ (z-w) v • w‖ := norm_add_le _ _
    _ = |inner ℝ z v| * ‖z-w‖ + |inner ℝ (z-w) v| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hw, mul_one]
    _ ≤ (‖z‖ * ‖v‖) * ‖z-w‖ + (‖z-w‖ * ‖v‖) := by
      exact add_le_add (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm z v)
        (norm_nonneg _)) (abs_real_inner_le_norm (z-w) v)
    _ = _ := by rw [hz, one_mul, norm_sub_rev z w]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_GridCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Candidate grid counts in any ambient dimension

The remaining unknown cell in a retained graph edge is confined to a small
ball. Its integer coordinate labels therefore lie in a product of short
integer intervals. This gives the dimension-dependent degree factor.
-/

namespace Falconer

/-- Euclidean distance bounds every integer coordinate difference. -/
theorem grid_coordinate_bound {d L : ℕ} {s r : ℝ} (hs : 0 < s)
    (hL : r * s ≤ L) {z w : Fin d → ℤ}
    (hz : ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) (i : Fin d) :
    |z i - w i| ≤ (L : ℤ) := by
  have hi := (PiLp.norm_apply_le (scaledGridPoint s z - scaledGridPoint s w) i).trans hz
  change |(z i : ℝ) / s - (w i : ℝ) / s| ≤ r at hi
  rw [← sub_div, abs_div, abs_of_pos hs] at hi
  have hb : |(z i : ℝ) - (w i : ℝ)| ≤ (L : ℝ) :=
    ((div_le_iff₀ hs).mp hi).trans hL
  exact_mod_cast hb

/-- A finite family in a coordinate box has at most `(2L+1)^d` labels. -/
theorem grid_box_card {d L : ℕ} (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ∀ i, |z i - w i| ≤ (L : ℤ)) :
    S.card ≤ (2 * L + 1)^d := by
  classical
  let shift : (Fin d → ℤ) → (Fin d → ℤ) := fun z i => z i - w i
  have hi : Function.Injective shift := by
    intro u v huv
    funext i
    have hi := congrFun huv i
    dsimp [shift] at hi
    omega
  have hsub : S.image shift ⊆
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (abs_le.mp (hS u hu i))
  have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    S.card = (S.image shift).card := (Finset.card_image_of_injective S hi).symm
    _ ≤ (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ))).card :=
      Finset.card_le_card hsub
    _ = (2 * L + 1)^d := by simp [Fintype.card_piFinset, hcard]

/-- Ball count at a chosen grid center, with explicit integer radius. -/
theorem grid_ball_card {d L : ℕ} {s r : ℝ} (hs : 0 < s) (hL : r * s ≤ L)
    (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ‖scaledGridPoint s z - scaledGridPoint s w‖ ≤ r) :
    S.card ≤ (2 * L + 1)^d :=
  grid_box_card S w (fun z hz i => grid_coordinate_bound hs hL (hS z hz) i)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphSchur
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Positive Schur step for the all-dimensional graph estimate

The finite Schur inequality applies to arbitrary index types. The graph
geometry and degrees retain the ambient dimension. A partition of unity
costs no factor equal to the number of caps.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

/-- Positive Schur bound for a complex amplitude on a finite graph. -/
theorem finite_graph_schur {ι : Type*} (S : Finset ι)
    (G : ι → ι → Prop) (F : ι → ℂ) (D : ℝ)
    (hrow : ∀ a ∈ S, ((S.filter (G a)).card : ℝ) ≤ D)
    (hcol : ∀ b ∈ S, ((S.filter (fun a => G a b)).card : ℝ) ≤ D) :
    (∑ a ∈ S, ∑ b ∈ S, if G a b then ‖F a * star (F b)‖ else 0) ≤
      D * ∑ a ∈ S, ‖F a‖^2 := by
  have h := PlanarFalconer.finset_bipartite_schur S S G
    (fun a => ‖F a‖) (fun a => ‖F a‖) D hrow hcol
  simp only [norm_mul, norm_star] at ⊢
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

/-- Summing a nonnegative angular partition of unity preserves the Schur
bound without a cap-count factor. -/
theorem partition_graph_schur {ι κ : Type*} (S : Finset ι) (K : Finset κ)
    (G : κ → ι → ι → Prop) (F : ι → ℂ) (weight : κ → ℝ) (D : ℝ)
    (hweight : ∀ k ∈ K, 0 ≤ weight k) (hpartition : ∑ k ∈ K, weight k = 1)
    (hrow : ∀ k ∈ K, ∀ a ∈ S, ((S.filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ K, ∀ b ∈ S, ((S.filter (fun a => G k a b)).card : ℝ) ≤ D) :
    ‖∑ k ∈ K, weight k • (∑ a ∈ S, ∑ b ∈ S,
      if G k a b then F a * star (F b) else 0)‖ ≤ D * ∑ a ∈ S, ‖F a‖^2 := by
  calc
    _ ≤ ∑ k ∈ K, ‖weight k • (∑ a ∈ S, ∑ b ∈ S,
        if G k a b then F a * star (F b) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ K, weight k * (D * ∑ a ∈ S, ‖F a‖^2) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight k hk)]
      apply mul_le_mul_of_nonneg_left _ (hweight k hk)
      calc
        _ ≤ ∑ a ∈ S, ∑ b ∈ S, ‖if G k a b then F a * star (F b) else 0‖ := by
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => norm_sum_le _ _))
        _ = ∑ a ∈ S, ∑ b ∈ S, if G k a b then ‖F a * star (F b)‖ else 0 := by
          simp only [apply_ite norm, norm_zero]
        _ ≤ _ := finite_graph_schur S (G k) F D (hrow k hk) (hcol k hk)
    _ = _ := by rw [← Finset.sum_mul, hpartition, one_mul]

/-- Integrated retained-edge estimate. The domain can include both angular
variables and the radial variable with its nonnegative cutoff measure. -/
theorem integral_partition_graph_schur {X ι κ : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (K : Finset κ)
    (G : κ → ι → ι → Prop) (F : ι → X → ℂ) (weight : κ → X → ℝ) (D : ℝ)
    (hF : ∀ a ∈ S, Integrable (fun x => ‖F a x‖^2) μ)
    (hweight : ∀ x k, k ∈ K → 0 ≤ weight k x)
    (hpartition : ∀ x, ∑ k ∈ K, weight k x = 1)
    (hrow : ∀ k ∈ K, ∀ a ∈ S, ((S.filter (G k a)).card : ℝ) ≤ D)
    (hcol : ∀ k ∈ K, ∀ b ∈ S, ((S.filter (fun a => G k a b)).card : ℝ) ≤ D) :
    ‖∫ x, ∑ k ∈ K, weight k x • (∑ a ∈ S, ∑ b ∈ S,
      if G k a b then F a x * star (F b x) else 0) ∂μ‖ ≤
      D * ∑ a ∈ S, ∫ x, ‖F a x‖^2 ∂μ := by
  have hbound := norm_integral_le_of_norm_le ((integrable_finsetSum S hF).const_mul D)
    (Filter.Eventually.of_forall (fun x => partition_graph_schur S K G
      (fun a => F a x) (fun k => weight k x) D (hweight x) (hpartition x) hrow hcol))
  simpa only [integral_const_mul, integral_finsetSum S hF] using hbound

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_RadialShellMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem sourceAngularShellMeasure_mass_le (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) :
    sourceAngularShellMeasure v Ψ univ ≤ ENNReal.ofReal (4*B) := by
  let A : ℝ := (2:ℝ)^v
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  unfold sourceAngularShellMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (Ψ (r/A)/A)) ≤ _
  calc
    _ ≤ ∫⁻ r in Ioi (0:ℝ), (Iic (4*A)).indicator (fun _ => ENNReal.ofReal (B/A)) r := by
      apply lintegral_mono
      intro r
      dsimp only
      by_cases hr : r ≤ 4*A
      · rw [indicator_of_mem (show r ∈ Iic (4*A) from hr)]
        exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb _) hA.le)
      · rw [indicator_of_notMem (show r ∉ Iic (4*A) from hr)]
        rw [hs _ ((lt_div_iff₀ hA).mpr (lt_of_not_ge hr)), zero_div, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (B/A) * ENNReal.ofReal (4*A) := by
      rw [lintegral_indicator measurableSet_Iic, lintegral_const, Measure.restrict_apply_univ,
        Measure.restrict_apply measurableSet_Iic]
      rw [inter_comm, Ioi_inter_Iic, Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal (4*B) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hB hA.le)]
      congr 1
      rw [mul_left_comm, div_mul_cancel₀ _ hA.ne']

theorem sourceAngularShellMeasure_finite (v : ℝ) (Ψ : ℝ → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ t, Ψ t ≤ B)
    (hs : ∀ t, 4 < t → Ψ t = 0) : IsFiniteMeasure (sourceAngularShellMeasure v Ψ) :=
  ⟨(sourceAngularShellMeasure_mass_le v Ψ hB hb hs).trans_lt ENNReal.ofReal_lt_top⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SphericalEnergy
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Independent angular energy in every dimension

The angular measure is the actual sphere measure obtained from Euclidean
Lebesgue measure by polar coordinates. The radial measure is the same
nonnegative shell cutoff used by the scalar reconstruction. Both angular
variables remain independent in this energy.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem sphereMoment_nonneg {d : ℕ} (U : ℝ × Sphere d → ℂ) (r : ℝ) :
    0 ≤ sphereMoment U r := integral_nonneg (fun _ => sq_nonneg _)

theorem sphereMoment_measurable {d : ℕ} (U : ℝ × Sphere d → ℂ)
    (hU : Measurable U) : Measurable (sphereMoment U) :=
  (hU.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

theorem sphere_norm_square_integrable {d : ℕ} (U : Sphere d → ℂ) (hU : Measurable U)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ w, ‖U w‖ ≤ C) :
    Integrable (fun w => ‖U w‖^2) (sphereMeasure d) := by
  apply Integrable.of_bound (hU.norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb w)

theorem sphereMoment_le {d : ℕ} (U : ℝ × Sphere d → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖U z‖ ≤ C) (r : ℝ) :
    sphereMoment U r ≤ C^2 * (sphereMeasure d).real univ := by
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb (r,w))

theorem sphere_product_square_integral {d : ℕ} (U V : Sphere d → ℂ) :
    (∫ z : Sphere d × Sphere d, ‖U z.1 * V z.2‖^2 ∂(sphereMeasure d).prod (sphereMeasure d)) =
      (∫ w, ‖U w‖^2 ∂sphereMeasure d) * (∫ w, ‖V w‖^2 ∂sphereMeasure d) := by
  simp only [norm_mul, mul_pow]
  exact integral_prod_mul (fun w => ‖U w‖^2) (fun w => ‖V w‖^2)

/-- Bounded measurable endpoint transforms give an integrable square on
the full radial and independent angular product. -/
theorem angular_product_square_integrable {d : ℕ} (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    Integrable (fun z : ℝ × (Sphere d × Sphere d) =>
      ‖U (z.1,z.2.1) * V (z.1,z.2.2)‖^2)
      ((PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
        ((sphereMeasure d).prod (sphereMeasure d))) := by
  have hmU : Measurable (fun z : ℝ × (Sphere d × Sphere d) => U (z.1,z.2.1)) :=
    hU.comp (measurable_fst.prodMk measurable_snd.fst)
  have hmV : Measurable (fun z : ℝ × (Sphere d × Sphere d) => V (z.1,z.2.2)) :=
    hV.comp (measurable_fst.prodMk measurable_snd.snd)
  apply Integrable.of_bound ((hmU.mul hmV).norm.pow_const 2).aestronglyMeasurable ((C*D)^2)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hD)).mpr
  change ‖U (z.1,z.2.1) * V (z.1,z.2.2)‖ ≤ C * D
  rw [norm_mul]
  exact mul_le_mul (hbU _) (hbV _) (norm_nonneg _) hC

theorem independentAngularEnergy_product_integral {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    independentAngularEnergy a v Ψ U V = (2 : ℝ)^((d : ℝ)*(v-a)) *
      ∫ z : ℝ × (Sphere d × Sphere d), ‖U (z.1,z.2.1) * V (z.1,z.2.2)‖^2
        ∂(PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
          ((sphereMeasure d).prod (sphereMeasure d)) := by
  have hi := angular_product_square_integrable v Ψ U V hU hV hC hD hbU hbV
  rw [independentAngularEnergy, integral_prod _ hi]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  exact (sphere_product_square_integral (fun w => U (r,w)) (fun w => V (r,w))).symm

/-- Schur integration produces precisely the independent child energies
defined with the sphere measure in the original ambient dimension. -/
theorem independentAngularEnergy_graph_schur {d : ℕ} {ι κ : Type*}
    (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (S : Finset ι) (K : Finset κ) (G : κ → ι → ι → Prop)
    (U V : ι → ℝ × Sphere d → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ z, ‖U i z‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ z, ‖V i z‖ ≤ D i)
    (weight : κ → ℝ × (Sphere d × Sphere d) → ℝ) (degree : ℝ)
    (hweight : ∀ z k, k ∈ K → 0 ≤ weight k z)
    (hpartition : ∀ z, ∑ k ∈ K, weight k z = 1)
    (hrow : ∀ k ∈ K, ∀ i ∈ S, ((S.filter (G k i)).card : ℝ) ≤ degree)
    (hcol : ∀ k ∈ K, ∀ j ∈ S, ((S.filter (fun i => G k i j)).card : ℝ) ≤ degree) :
    (2 : ℝ)^((d : ℝ)*(v-a)) *
      ‖∫ z : ℝ × (Sphere d × Sphere d), ∑ k ∈ K, weight k z •
        (∑ i ∈ S, ∑ j ∈ S, if G k i j then
          (U i (z.1,z.2.1) * V i (z.1,z.2.2)) *
            star (U j (z.1,z.2.1) * V j (z.1,z.2.2)) else 0)
        ∂(PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
          ((sphereMeasure d).prod (sphereMeasure d))‖ ≤
      degree * ∑ i ∈ S, independentAngularEnergy a v Ψ (U i) (V i) := by
  classical
  let μ := (PlanarFalconer.sourceAngularShellMeasure v Ψ).prod
    ((sphereMeasure d).prod (sphereMeasure d))
  let F := fun i (z : ℝ × (Sphere d × Sphere d)) =>
    U i (z.1,z.2.1) * V i (z.1,z.2.2)
  have hF (i : ι) (hi : i ∈ S) : Integrable (fun z => ‖F i z‖^2) μ :=
    angular_product_square_integrable v Ψ (U i) (V i) (hU i hi) (hV i hi)
      (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)
  have hb := integral_partition_graph_schur μ S K G F weight degree hF
    hweight hpartition hrow hcol
  have he (i : ι) (hi : i ∈ S) : independentAngularEnergy a v Ψ (U i) (V i) =
      (2 : ℝ)^((d : ℝ)*(v-a)) * ∫ z, ‖F i z‖^2 ∂μ :=
    independentAngularEnergy_product_integral a v Ψ (U i) (V i) (hU i hi) (hV i hi)
      (hC i hi) (hD i hi) (hbU i hi) (hbV i hi)
  calc
    _ ≤ (2 : ℝ)^((d : ℝ)*(v-a)) * (degree * ∑ i ∈ S, ∫ z, ‖F i z‖^2 ∂μ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = degree * ∑ i ∈ S, independentAngularEnergy a v Ψ (U i) (V i) := by
      have hs : (∑ i ∈ S, independentAngularEnergy a v Ψ (U i) (V i)) =
          (2 : ℝ)^((d : ℝ)*(v-a)) * ∑ i ∈ S, ∫ z, ‖F i z‖^2 ∂μ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl he
      rw [hs]
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SharedAngular
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Shared-angle energy and the independent-angle bound

The shell conversion uses one shared angular variable. Cauchy--Schwarz
transfers it to the positive independent-angle energy with exactly the
same endpoint symbols and radial measure.
-/

namespace Falconer
open Set MeasureTheory

theorem independentAngularIntegrand_integrable {d : ℕ} (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    Integrable (fun r => sphereMoment U r * sphereMoment V r)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  apply Integrable.of_bound
    ((sphereMoment_measurable U hU).mul (sphereMoment_measurable V hV)).aestronglyMeasurable
    ((C^2 * (sphereMeasure d).real univ) * (D^2 * (sphereMeasure d).real univ))
  filter_upwards with r
  change ‖sphereMoment U r * sphereMoment V r‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))]
  exact mul_le_mul (sphereMoment_le U hC hbU r) (sphereMoment_le V hD hbV r)
    (sphereMoment_nonneg V r) (by positivity)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_EndpointTransform
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Original endpoint transforms in arbitrary dimension

The spatial measure argument is already restricted to its cell. A child
therefore uses the same endpoint symbol and the original restricted law.
The exact finite-measure splitting keeps the model-mass factors explicit.
-/

namespace Falconer
open MeasureTheory

theorem endpoint_integrand_norm {d : ℕ} (b : Space d → Sphere d → ℂ)
    (r : ℝ) (w : Sphere d) (x : Space d) :
    ‖Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w‖ = ‖b x w‖ := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem measurable_endpointTransform {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (M : ℝ) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) :
    Measurable (fun z : ℝ × Sphere d => endpointTransform ρ M b z.1 z.2) := by
  have hf : Measurable (fun z : (ℝ × Sphere d) × Space d =>
      Complex.exp (Complex.I * (z.1.1 : ℂ) * (inner ℝ (z.1.2 : Space d) z.2 : ℂ)) *
        b z.2 z.1.2) := by
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_snd.prodMk measurable_fst.snd)
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν := ρ)).measurable
  exact (measurable_const (a := (M⁻¹ : ℝ))).smul hi

theorem endpoint_integrand_integrable {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {C : ℝ} (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    Integrable (fun x => Complex.exp (Complex.I * (r : ℂ) *
      (inner ℝ (w : Space d) x : ℂ)) * b x w) ρ := by
  apply (integrable_const C).mono
  · apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · fun_prop
    · exact hb.comp (measurable_id.prodMk measurable_const)
  · filter_upwards with x
    exact (endpoint_integrand_norm b r w x).trans_le ((hC x w).trans (le_abs_self C))

theorem endpointTransform_norm_le {d : ℕ} (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    {M C : ℝ} (hM : 0 < M) (b : Space d → Sphere d → ℂ)
    (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    ‖endpointTransform ρ M b r w‖ ≤ C * ρ.real Set.univ / M := by
  unfold endpointTransform
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hM)]
  have hb := norm_integral_le_of_norm_le_const (μ := ρ)
    (Filter.Eventually.of_forall (fun x => (endpoint_integrand_norm b r w x).trans_le (hC x w)))
  calc
    _ ≤ M⁻¹ * (C * ρ.real Set.univ) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hM.le)
    _ = _ := by ring

/-- Exact model-mass splitting of one endpoint transform. -/
theorem endpointTransform_sum {d : ℕ} {ι : Type*} (S : Finset ι)
    (ρ : ι → Measure (Space d)) [∀ i, IsFiniteMeasure (ρ i)]
    (Ma Mp : ℝ) (hMp : Mp ≠ 0) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) {C : ℝ} (hC : ∀ x w, ‖b x w‖ ≤ C)
    (r : ℝ) (w : Sphere d) :
    endpointTransform (∑ i ∈ S, ρ i) Ma b r w =
      (Mp / Ma) • ∑ i ∈ S, endpointTransform (ρ i) Mp b r w := by
  simp only [endpointTransform]
  rw [integral_finsetSum_measure (fun i _ => endpoint_integrand_integrable (ρ i) b hb hC r w)]
  rw [← Finset.smul_sum, smul_smul]
  congr 1
  rw [div_mul_eq_mul_div, mul_inv_cancel₀ hMp, one_div]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTerminal
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal independent angular energies in every dimension

Only the sup norm of the actual endpoint symbols and the two original
cell masses enter the stopping estimate. The radial shell measure is
normalized, so its total mass has no frequency factor.
-/

namespace Falconer
open MeasureTheory Set

theorem independentAngularEnergy_bound {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbU : ∀ z, ‖U z‖ ≤ C) (hbV : ∀ z, ‖V z‖ ≤ D) :
    independentAngularEnergy a v Ψ U V ≤
      (2:ℝ)^((d:ℝ)*(v-a)) * (C^2*D^2*(sphereMeasure d).real univ^2) *
        (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  have hb : ∀ r, ‖sphereMoment U r*sphereMoment V r‖ ≤
      C^2*D^2*(sphereMeasure d).real univ^2 := by
    intro r
    rw [Real.norm_eq_abs,abs_of_nonneg
      (mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))]
    calc
      _ ≤ (C^2*(sphereMeasure d).real univ)*(D^2*(sphereMeasure d).real univ) :=
        mul_le_mul (sphereMoment_le U hC hbU r) (sphereMoment_le V hD hbV r)
          (sphereMoment_nonneg V r) (by positivity)
      _ = _ := by ring
  unfold independentAngularEnergy
  have hnorm := norm_integral_le_of_norm_le_const
    (μ := PlanarFalconer.sourceAngularShellMeasure v Ψ) (Filter.Eventually.of_forall hb)
  have hn : 0 ≤ ∫ r, sphereMoment U r*sphereMoment V r
      ∂PlanarFalconer.sourceAngularShellMeasure v Ψ :=
    integral_nonneg (fun r => mul_nonneg (sphereMoment_nonneg U r) (sphereMoment_nonneg V r))
  rw [Real.norm_eq_abs,abs_of_nonneg hn] at hnorm
  exact (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_eq (by ring)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_OscillatoryExpansion
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Oscillatory spatial expansion before absolute values

The product of an endpoint transform and a conjugate transform is written
as the exact two-point integral with displacement phase. The identity uses
the original spatial measures and does not assume spatial smoothness.
-/

namespace Falconer
open MeasureTheory
open scoped ComplexConjugate

theorem exponential_mul_conj (s t : ℝ) :
    Complex.exp (Complex.I * (s : ℂ)) * star (Complex.exp (Complex.I * (t : ℂ))) =
      Complex.exp (Complex.I * ((s-t : ℝ) : ℂ)) := by
  rw [show star (Complex.exp (Complex.I * (t : ℂ))) =
      Complex.exp (-Complex.I * (t : ℂ)) by simp [← Complex.exp_conj]]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem endpointTransform_mul_star {d : ℕ}
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M P : ℝ) (b c : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform μ M b r w * star (endpointTransform ν P c r w) =
      (M⁻¹ * P⁻¹) • ∫ z : Space d × Space d,
        Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ)) *
          (b z.1 w * star (c z.2 w)) ∂μ.prod ν := by
  have hid (x y : Space d) :
      (Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) x : ℂ)) * b x w) *
        star (Complex.exp (Complex.I * (r : ℂ) * (inner ℝ (w : Space d) y : ℂ)) * c y w) =
      Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (x-y) : ℝ) : ℂ)) *
        (b x w * star (c y w)) := by
    rw [star_mul]
    have he := exponential_mul_conj (r * inner ℝ (w : Space d) x)
      (r * inner ℝ (w : Space d) y)
    push_cast at he
    rw [show r * inner ℝ (w : Space d) (x-y) =
      r * inner ℝ (w : Space d) x - r * inner ℝ (w : Space d) y by
        rw [inner_sub_right, mul_sub]]
    push_cast
    rw [← he]
    ring_nf
  simp only [endpointTransform, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm,
    smul_smul]
  rw [mul_comm P⁻¹ M⁻¹]
  congr 1
  change _ * conj (∫ x, _ ∂ν) = _
  rw [← integral_conj, ← integral_prod_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => hid z.1 z.2)

/-- Equation `graph:phase`, with four possibly different endpoint laws and
with the symbols retained inside the original spatial integral. -/
theorem endpointTransform_four_point {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' : ℝ) (b b' c c' : Space d → Sphere d → ℂ)
    (r : ℝ) (w v : Sphere d) :
    (endpointTransform μ M b r w * endpointTransform ν P c r v) *
      star (endpointTransform μ' M' b' r w * endpointTransform ν' P' c' r v) =
    ((M⁻¹ * M'⁻¹) * (P⁻¹ * P'⁻¹)) •
      ∫ z : (Space d × Space d) × (Space d × Space d),
        Complex.exp (Complex.I * ((r *
          (inner ℝ (w : Space d) (z.1.1-z.1.2) +
           inner ℝ (v : Space d) (z.2.1-z.2.2)) : ℝ) : ℂ)) *
          ((b z.1.1 w * star (b' z.1.2 w)) * (c z.2.1 v * star (c' z.2.2 v)))
        ∂(μ.prod μ').prod (ν.prod ν') := by
  rw [show (endpointTransform μ M b r w * endpointTransform ν P c r v) *
      star (endpointTransform μ' M' b' r w * endpointTransform ν' P' c' r v) =
      (endpointTransform μ M b r w * star (endpointTransform μ' M' b' r w)) *
      (endpointTransform ν P c r v * star (endpointTransform ν' P' c' r v)) by
        rw [star_mul]; ring]
  rw [endpointTransform_mul_star, endpointTransform_mul_star,
    smul_mul_smul_comm, ← integral_prod_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  have he : Complex.exp (Complex.I * ((r *
      (inner ℝ (w : Space d) (z.1.1-z.1.2) +
       inner ℝ (v : Space d) (z.2.1-z.2.2)) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((r * inner ℝ (w : Space d) (z.1.1-z.1.2) : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((r * inner ℝ (v : Space d) (z.2.1-z.2.2) : ℝ) : ℂ)) := by
    rw [mul_add, Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [he]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyDescriptors
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem policyDescriptor_origin (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) :
    ∃ b u : ℕ, a ≤ b ∧ u ≤ t ∧ b+100*q < u ∧
      descriptorAnchor d = policyDepth A N q b u ∧ 0 < descriptorLength d ∧
      b ≤ descriptorAnchor d-descriptorLength d ∧ descriptorAnchor d+descriptorLength d ≤ u := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,hb,hu,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  exact ⟨z.1,z.2,hb,hu,hwide,originDescriptor_anchor A hd,
    originDescriptor_length A hq huN hwide hd⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularPair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The two independent angular variables in one graph term

For fixed spatial points, the four-point phase separates into two sphere
integrals. A nonstationary bound in either variable can thus be used without
any angle separation or pointwise truncation of the amplitude.
-/

namespace Falconer
open MeasureTheory

theorem angular_pair_factorization {d : ℕ} (Λ : ℝ) (v₁ v₂ : Space d)
    (b₁ b₂ : Sphere d → ℂ) :
    (∫ z : Sphere d × Sphere d,
      Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (z.1 : Space d) v₁ : ℂ)+(inner ℝ (z.2 : Space d) v₂ : ℂ))) *
          b₁ z.1 * b₂ z.2 ∂(sphereMeasure d).prod (sphereMeasure d)) =
      (∫ w, sphereOscillator Λ v₁ w*b₁ w ∂sphereMeasure d) *
        (∫ w, sphereOscillator Λ v₂ w*b₂ w ∂sphereMeasure d) := by
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [sphereOscillator]
  rw [mul_add,Complex.exp_add]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularPairSwap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Fubini for the spatially expanded angular term

Bounded measurable amplitudes on finite original laws are sufficient.
There is no spatial differentiability requirement and no change of the
point labels in the two endpoint factors.
-/

namespace Falconer
open MeasureTheory

theorem angular_pair_spatial_swap {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (Λ : ℝ) (v₁ v₂ : X → Space d)
    (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (b₁ b₂ : X → Sphere d → ℂ)
    (hb₁ : Measurable (Function.uncurry b₁)) (hb₂ : Measurable (Function.uncurry b₂))
    {B C : ℝ} (hB : 0 ≤ B) (_hC : 0 ≤ C)
    (hbound₁ : ∀ x w, ‖b₁ x w‖ ≤ B) (hbound₂ : ∀ x w, ‖b₂ x w‖ ≤ C) :
    (∫ z : Sphere d × Sphere d, ∫ x,
      Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (z.1 : Space d) (v₁ x) : ℂ)+(inner ℝ (z.2 : Space d) (v₂ x) : ℂ))) *
          b₁ x z.1 * b₂ x z.2 ∂μ ∂(sphereMeasure d).prod (sphereMeasure d)) =
      ∫ x, (∫ w, sphereOscillator Λ (v₁ x) w*b₁ x w ∂sphereMeasure d) *
        (∫ w, sphereOscillator Λ (v₂ x) w*b₂ x w ∂sphereMeasure d) ∂μ := by
  let F : X × (Sphere d × Sphere d) → ℂ := fun p =>
    Complex.exp (Complex.I*(Λ : ℂ)*
      ((inner ℝ (p.2.1 : Space d) (v₁ p.1) : ℂ)+
       (inner ℝ (p.2.2 : Space d) (v₂ p.1) : ℂ))) * b₁ p.1 p.2.1 * b₂ p.1 p.2.2
  have hm : Measurable F := by
    apply Measurable.mul
    · apply Measurable.mul
      · fun_prop
      · exact hb₁.comp (measurable_fst.prodMk measurable_snd.fst)
    · exact hb₂.comp (measurable_fst.prodMk measurable_snd.snd)
  have hnorm (p : X × (Sphere d × Sphere d)) : ‖F p‖ ≤ B*C := by
    have hexp : ‖Complex.exp (Complex.I*(Λ : ℂ)*
        ((inner ℝ (p.2.1 : Space d) (v₁ p.1) : ℂ)+
         (inner ℝ (p.2.2 : Space d) (v₂ p.1) : ℂ)))‖ = 1 := by
      simp [Complex.norm_exp]
    simp only [F,norm_mul,hexp,one_mul]
    exact mul_le_mul (hbound₁ _ _) (hbound₂ _ _) (norm_nonneg _) hB
  have hi : Integrable F (μ.prod ((sphereMeasure d).prod (sphereMeasure d))) :=
    Integrable.of_bound hm.aestronglyMeasurable (B*C) (Filter.Eventually.of_forall hnorm)
  calc
    _ = ∫ x, ∫ z : Sphere d × Sphere d, F (x,z)
        ∂(sphereMeasure d).prod (sphereMeasure d) ∂μ := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      exact angular_pair_factorization Λ (v₁ x) (v₂ x) (b₁ x) (b₂ x)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FourPointCaps
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact cap expansion of an endpoint cross term

Each cap weight stays inside the original four-point amplitude. The only
factor removed from the integral is the product of the four model-mass
normalizations. The measures are the original restricted endpoint laws.
-/

namespace Falconer
open MeasureTheory
open scoped ComplexConjugate

theorem endpointCapCrossTerm_four_point {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    (b b' c c' : Space d → Sphere d → ℂ) (η θ : Sphere d → ℝ) :
    endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ =
      ((M⁻¹*M'⁻¹)*(P⁻¹*P'⁻¹)) •
        expandedCapTerm ((μ.prod μ').prod (ν.prod ν')) v Ψ
          (fun x => x.1.1-x.1.2) (fun x => x.2.1-x.2.2)
          (fun x w => capPairAmplitude η b b' x.1 w)
          (fun x w => capPairAmplitude θ c c' x.2 w) := by
  unfold endpointCapCrossTerm expandedCapTerm
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with r
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards with z
  rw [endpointTransform_four_point]
  rw [mul_smul_comm, ← integral_const_mul, ← integral_smul, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [capPairAmplitude]
  have he : Complex.I * ((r *
      (inner ℝ (z.1 : Space d) (x.1.1-x.1.2) +
       inner ℝ (z.2 : Space d) (x.2.1-x.2.2)) : ℝ) : ℂ) =
      Complex.I*(r : ℂ)*
        ((inner ℝ (z.1 : Space d) (x.1.1-x.1.2) : ℂ)+
         (inner ℝ (z.2 : Space d) (x.2.1-x.2.2) : ℂ)) := by
    push_cast
    ring
  rw [he]
  apply congrArg (fun z : ℂ => ((M⁻¹*M'⁻¹)*(P⁻¹*P'⁻¹)) • z)
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem DyadicCube.cover_descendants {d : ℕ} (Q : DyadicCube d) (n : ℕ) :
    Q.carrier = ⋃ p ∈ cubePaths d n, (Q.descendant p).carrier := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := Q.mem_descendant_at_depth n hx
    exact mem_iUnion₂.mpr ⟨p, hp, hxp⟩
  · exact iUnion₂_subset fun p _ => Q.descendant_subset p

/-- Exact disjoint measure decomposition; no boundaries or extra spatial
cutoffs are added to the original law. -/
theorem DyadicCube.restrict_descendants {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) :
    μ.restrict Q.carrier = ∑ p ∈ cubePaths d n, μ.restrict (Q.descendant p).carrier := by
  rw [Q.cover_descendants n]
  rw [Measure.restrict_biUnion_finset]
  · simp only [Measure.sum_fintype, Finset.univ_eq_attach]
    exact Finset.sum_attach (cubePaths d n) (fun p => μ.restrict (Q.descendant p).carrier)
  · intro p hp q hq hpq
    exact Q.descendants_disjoint ((mem_cubePaths d n p).mp hp |>.trans
      ((mem_cubePaths d n q).mp hq).symm) hpq
  · intro p
    exact (Q.descendant p).measurable

theorem DyadicCube.restrict_occupiedPaths {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) (n : ℕ) :
    μ.restrict Q.carrier =
      ∑ p ∈ Q.occupiedPaths μ n, μ.restrict (Q.descendant p).carrier := by
  rw [Q.restrict_descendants μ n]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpo
  apply Measure.restrict_eq_zero.mpr
  have hz : ¬ 0 < μ (Q.descendant p).carrier := by
    intro hpos
    exact hpo (Finset.mem_filter.mpr ⟨hp, hpos⟩)
  exact le_antisymm (le_of_not_gt hz) bot_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DyadicTransforms
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact splitting into occupied dyadic cells

This is the spatial splitting in `graph:splitting`, for the original law
and the same measurable endpoint symbol on every descendant.
-/

namespace Falconer
open MeasureTheory

theorem DyadicCube.endpointTransform_split {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (n : ℕ)
    (Ma Mp : ℝ) (hMp : Mp ≠ 0) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict Q.carrier) Ma b r w =
      (Mp / Ma) • ∑ p ∈ Q.occupiedPaths μ n,
        endpointTransform (μ.restrict (Q.descendant p).carrier) Mp b r w := by
  conv_lhs => rw [Q.restrict_occupiedPaths μ n]
  exact endpointTransform_sum (Q.occupiedPaths μ n)
    (fun p => μ.restrict (Q.descendant p).carrier) Ma Mp hMp b hb hC r w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EnergySplitting
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact independent-energy expansion on the original dyadic cells

The two endpoint laws and their symbols are unchanged when passing to
occupied descendants. The identity keeps every complex cross term inside
the angular--radial integral, where nonstationary localization is applied.
-/

namespace Falconer
open MeasureTheory

theorem complex_sum_square {ι : Type*} (S : Finset ι) (F : ι → ℂ) :
    ((‖∑ i ∈ S, F i‖^2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, F i * star (F j) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem integral_cross_sum_norm {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (F : ι → X → ℂ) :
    ‖∫ x, ∑ i ∈ S, ∑ j ∈ S, F i x * star (F j x) ∂μ‖ =
      ∫ x, ‖∑ i ∈ S, F i x‖^2 ∂μ := by
  have he : (∫ x, ∑ i ∈ S, ∑ j ∈ S, F i x * star (F j x) ∂μ) =
      ((∫ x, ‖∑ i ∈ S, F i x‖^2 ∂μ : ℝ) : ℂ) := by
    simp_rw [← complex_sum_square]
    exact integral_ofReal
  rw [he, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]

theorem dyadicPairTransform_sum {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (n : ℕ) (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C)
    (z : ℝ × (Sphere d × Sphere d)) :
    endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2.1 *
      endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2.2 =
    ((Mp₁ / Ma₁) * (Mp₂ / Ma₂)) •
      ∑ p ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c p z := by
  rw [Q₁.endpointTransform_split μ n Ma₁ Mp₁ hMp₁ b hb hbB,
    Q₂.endpointTransform_split ν n Ma₂ Mp₂ hMp₂ c hc hcC,
    smul_mul_smul_comm, Finset.sum_product]
  congr 1
  simp only [dyadicPairTransform, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Exact expansion before any cross term is discarded or replaced by
its absolute value. The child masses are the chosen model masses. -/
theorem independentAngularEnergy_dyadic_expansion {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (n : ℕ) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (Ma₁ Ma₂ Mp₁ Mp₂ : ℝ) (hMa₁ : 0 < Ma₁) (hMa₂ : 0 < Ma₂)
    (hMp₁ : Mp₁ ≠ 0) (hMp₂ : Mp₂ ≠ 0)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (μ.restrict Q₁.carrier) Ma₁ b z.1 z.2)
      (fun z => endpointTransform (ν.restrict Q₂.carrier) Ma₂ c z.1 z.2) =
    (2 : ℝ)^((d : ℝ)*(v-a)) * ((Mp₁/Ma₁)*(Mp₂/Ma₂))^2 *
      ‖∫ z, ∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        ∑ col ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
          dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c row z *
            star (dyadicPairTransform Q₁ Q₂ μ ν Mp₁ Mp₂ b c col z)
        ∂angularProductMeasure d v Ψ‖ := by
  rw [independentAngularEnergy_product_integral a v Ψ _ _
    (measurable_endpointTransform _ _ b hb) (measurable_endpointTransform _ _ c hc)
    (show 0 ≤ B * (μ.restrict Q₁.carrier).real Set.univ / Ma₁ by positivity)
    (show 0 ≤ C * (ν.restrict Q₂.carrier).real Set.univ / Ma₂ by positivity)
    (fun z => endpointTransform_norm_le _ hMa₁ b hbB z.1 z.2)
    (fun z => endpointTransform_norm_le _ hMa₂ c hcC z.1 z.2)]
  simp_rw [dyadicPairTransform_sum Q₁ Q₂ μ ν n Ma₁ Ma₂ Mp₁ Mp₂ hMp₁ hMp₂ b c hb hc hbB hcC,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, integral_cross_sum_norm]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CapCrossIntegral
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The original cap cross term as one product-measure integral

This is the bridge between the radial/angular nonstationary estimates
and the finite graph expansion. Its integrability follows from bounded
endpoint symbols and the finite radial shell law.
-/

namespace Falconer
open Set MeasureTheory

theorem weighted_endpoint_cross_integrable {d : ℕ} (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (η θ : Sphere d → ℝ) (U U' V V' : ℝ × Sphere d → ℂ)
    (hη : Measurable η) (hθ : Measurable θ)
    (hU : Measurable U) (hU' : Measurable U') (hV : Measurable V) (hV' : Measurable V')
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B₁ B₂ B₃ B₄ : ℝ} (hB₁ : ∀ z, ‖U z‖ ≤ B₁) (hB₂ : ∀ z, ‖U' z‖ ≤ B₂)
    (hB₃ : ∀ z, ‖V z‖ ≤ B₃) (hB₄ : ∀ z, ‖V' z‖ ≤ B₄) :
    Integrable (fun z : ℝ × (Sphere d × Sphere d) =>
      ((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
        ((U (z.1,z.2.1)*V (z.1,z.2.2))*star (U' (z.1,z.2.1)*V' (z.1,z.2.2))))
      (angularProductMeasure d v Ψ) := by
  have hp₁ : Measurable (fun z : ℝ × (Sphere d × Sphere d) => (z.1,z.2.1)) :=
    measurable_fst.prodMk measurable_snd.fst
  have hp₂ : Measurable (fun z : ℝ × (Sphere d × Sphere d) => (z.1,z.2.2)) :=
    measurable_fst.prodMk measurable_snd.snd
  have hUV := (hU.comp hp₁).mul (hV.comp hp₂)
  have hUV' := (hU'.comp hp₁).mul (hV'.comp hp₂)
  have hweight : Measurable (fun z : ℝ × (Sphere d × Sphere d) =>
      (η z.2.1 : ℂ)*(θ z.2.2 : ℂ)) :=
    (Complex.measurable_ofReal.comp (hη.comp measurable_snd.fst)).mul
      (Complex.measurable_ofReal.comp (hθ.comp measurable_snd.snd))
  apply Integrable.of_bound (hweight.mul
    (hUV.mul (Complex.continuous_conj.measurable.comp hUV'))).aestronglyMeasurable
    ((B₁*B₃)*(B₂*B₄))
  filter_upwards with z
  change ‖((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
    ((U (z.1,z.2.1)*V (z.1,z.2.2))*star (U' (z.1,z.2.1)*V' (z.1,z.2.2)))‖ ≤ _
  have hw : |η z.2.1| * |θ z.2.2| ≤ 1 :=
    (mul_le_mul (hηnorm _) (hθnorm _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hp : ‖U (z.1,z.2.1)‖*‖V (z.1,z.2.2)‖ ≤ B₁*B₃ :=
    mul_le_mul (hB₁ (z.1,z.2.1)) (hB₃ (z.1,z.2.2)) (norm_nonneg _)
      ((norm_nonneg (U (z.1,z.2.1))).trans (hB₁ (z.1,z.2.1)))
  have hp' : ‖U' (z.1,z.2.1)‖*‖V' (z.1,z.2.2)‖ ≤ B₂*B₄ :=
    mul_le_mul (hB₂ (z.1,z.2.1)) (hB₄ (z.1,z.2.2)) (norm_nonneg _)
      ((norm_nonneg (U' (z.1,z.2.1))).trans (hB₂ (z.1,z.2.1)))
  have hpp := mul_le_mul hp hp' (by positivity : 0 ≤ ‖U' (z.1,z.2.1)‖*‖V' (z.1,z.2.2)‖)
    ((by positivity : 0 ≤ ‖U (z.1,z.2.1)‖*‖V (z.1,z.2.2)‖).trans hp)
  simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul hw hpp (by positivity) zero_le_one).trans_eq (one_mul _)

theorem endpointCapCrossTerm_integrable {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM : 0 < M) (hM' : 0 < M') (hP : 0 < P) (hP' : 0 < P')
    (b b' c c' : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hb' : Measurable (Function.uncurry b'))
    (hc : Measurable (Function.uncurry c)) (hc' : Measurable (Function.uncurry c'))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (_hB : 0 ≤ B)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hb'B : ∀ x w, ‖b' x w‖ ≤ B)
    (hcB : ∀ x w, ‖c x w‖ ≤ B) (hc'B : ∀ x w, ‖c' x w‖ ≤ B) :
    Integrable (fun z : ℝ × (Sphere d × Sphere d) => ((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
        ((endpointTransform μ M b z.1 z.2.1*endpointTransform ν P c z.1 z.2.2)*
          star (endpointTransform μ' M' b' z.1 z.2.1*endpointTransform ν' P' c' z.1 z.2.2))
) (angularProductMeasure d v Ψ) := by
  exact weighted_endpoint_cross_integrable v Ψ η θ
    (fun z => endpointTransform μ M b z.1 z.2)
    (fun z => endpointTransform μ' M' b' z.1 z.2)
    (fun z => endpointTransform ν P c z.1 z.2)
    (fun z => endpointTransform ν' P' c' z.1 z.2)
    hη hθ (measurable_endpointTransform μ M b hb)
    (measurable_endpointTransform μ' M' b' hb')
    (measurable_endpointTransform ν P c hc)
    (measurable_endpointTransform ν' P' c' hc') hηnorm hθnorm
    (fun z => endpointTransform_norm_le μ hM b hbB z.1 z.2)
    (fun z => endpointTransform_norm_le μ' hM' b' hb'B z.1 z.2)
    (fun z => endpointTransform_norm_le ν hP c hcB z.1 z.2)
    (fun z => endpointTransform_norm_le ν' hP' c' hc'B z.1 z.2)

theorem endpointCapCrossTerm_product_integral {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (M M' P P' v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM : 0 < M) (hM' : 0 < M') (hP : 0 < P) (hP' : 0 < P')
    (b b' c c' : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hb' : Measurable (Function.uncurry b'))
    (hc : Measurable (Function.uncurry c)) (hc' : Measurable (Function.uncurry c'))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hb'B : ∀ x w, ‖b' x w‖ ≤ B)
    (hcB : ∀ x w, ‖c x w‖ ≤ B) (hc'B : ∀ x w, ‖c' x w‖ ≤ B) :
    endpointCapCrossTerm μ μ' ν ν' M M' P P' v Ψ b b' c c' η θ =
      ∫ z, ((η z.2.1 : ℂ)*(θ z.2.2 : ℂ))*
        ((endpointTransform μ M b z.1 z.2.1*endpointTransform ν P c z.1 z.2.2)*
          star (endpointTransform μ' M' b' z.1 z.2.1*endpointTransform ν' P' c' z.1 z.2.2))
        ∂angularProductMeasure d v Ψ := by
  exact (integral_prod _ (endpointCapCrossTerm_integrable μ μ' ν ν' M M' P P' v Ψ
    hM hM' hP hP' b b' c c' hb hb' hc hc' η θ hη hθ hηnorm hθnorm
    hB hbB hb'B hcB hc'B)).symm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_DyadicCapTerms
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cap terms on the original dyadic descendants

The finite graph expansion and the analytic endpoint cross terms use the
same restricted laws and model masses. These identities connect them
without changing the spatial labels or taking an absolute value early.
-/

namespace Falconer
open Set MeasureTheory

theorem dyadicCapIntegrand_integrable {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η θ : Sphere d → ℝ) (hη : Measurable η) (hθ : Measurable θ)
    (hηnorm : ∀ w, |η w| ≤ 1) (hθnorm : ∀ w, |θ w| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    Integrable (dyadicCapIntegrand Q₁ Q₂ μ ν M₁ M₂ b c η θ row col)
      (angularProductMeasure d v Ψ) := by
  unfold dyadicCapIntegrand
  simpa only [dyadicCapIntegrand,dyadicPairTransform,Complex.real_smul,Complex.ofReal_mul] using
    endpointCapCrossTerm_integrable (μ.restrict (Q₁.descendant row.1).carrier)
      (μ.restrict (Q₁.descendant col.1).carrier) (ν.restrict (Q₂.descendant row.2).carrier)
      (ν.restrict (Q₂.descendant col.2).carrier) M₁ M₁ M₂ M₂ v Ψ
      hM₁ hM₁ hM₂ hM₂ b b c c hb hb hc hc η θ hη hθ hηnorm hθnorm hB hbB hbB hcB hcB

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The actual dyadic centers as one translated integer grid

The graph packing estimates apply to centers of descendants of the
original parent cube. Their integer labels and common translation are
identified exactly, in every ambient dimension.
-/

namespace Falconer
attribute [local instance] Classical.propDecidable

/-- The translation includes half a child side. Its contribution cancels
in every displacement used by the retained graph. -/
theorem DyadicCube.descendant_center_grid {d n : ℕ} (Q : DyadicCube d)
    (p : List (Fin d → Bool)) (hp : p.length = n) :
    (Q.descendant p).center =
      WithLp.toLp 2 (fun i => Q.origin i + (Q.side / (2 : ℝ)^n)/2) +
        scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) := by
  ext i
  simp only [PiLp.add_apply, scaledGridPoint_apply,
    Q.descendant_center, hp]
  field_simp

theorem DyadicCube.center_sub_eq_grid_sub {d n : ℕ} (Q : DyadicCube d)
    (p q : List (Fin d → Bool)) (hp : p.length = n) (hq : q.length = n) :
    (Q.descendant p).center - (Q.descendant q).center =
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode p) -
      scaledGridPoint ((2 : ℝ)^n / Q.side) (dyadicCode q) := by
  rw [Q.descendant_center_grid p hp, Q.descendant_center_grid q hq]
  abel

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SphereNormalization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable sphere normalization with a fixed value at zero -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem normalizeToSphere_measurable (w₀ : Sphere d) :
    Measurable (normalizeToSphere w₀) := by
  apply Measurable.subtype_mk
  exact Measurable.ite (by simp)
    measurable_const (measurable_id.norm.inv.smul measurable_id)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension-dependent normalization and branch ledger

The critical slope is `d / 2`. Both copies of a profile are needed for
the cancellation of the spatial normalization. The last-potential bound
uses the last interval with a defined two-depth potential, even when the
final interval itself is shorter.
-/

namespace Falconer
open scoped BigOperators

theorem dyadic_rpow_change_base {N : ℕ} (hN : 0 < N) (x : ℝ) :
    ((2 : ℝ)^N) ^ (x / (N : ℝ)) = (2 : ℝ)^x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_AngularTubeCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The mean and exceptional mass of a finite original tube count -/

namespace Falconer
open MeasureTheory Set
open scoped ENNReal

theorem angularTubeEvent_measurable {d : ℕ} (v : Space d) (W : ℝ) :
    MeasurableSet (angularTubeEvent v W) := by
  have hc : Continuous (fun w : Sphere d => v-inner ℝ (w:Space d) v • (w:Space d)) :=
    continuous_const.sub ((continuous_subtype_val.inner (𝕜 := ℝ) continuous_const).smul continuous_subtype_val)
  exact measurableSet_le hc.norm.measurable measurable_const

theorem finiteTubeCount_eq_sum {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (w : Sphere d) :
    (finiteTubeCount S v W w : ℝ≥0∞) =
      ∑ i ∈ S, (angularTubeEvent (v i) W).indicator (fun _ => (1:ℝ≥0∞)) w := by
  classical
  simp only [finiteTubeCount,Finset.natCast_card_filter,Set.indicator_apply]

theorem finiteTubeCount_measurable {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) :
    Measurable (fun w : Sphere d => (finiteTubeCount S v W w : ℝ≥0∞)) := by
  simp_rw [finiteTubeCount_eq_sum]
  exact Finset.measurable_sum S (fun i _ =>
    measurable_const.indicator (angularTubeEvent_measurable (v i) W))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ConditionalCollision
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Returning full-conditional projection tests to the original cell law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem conditional_product_mass_reconstruct (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (Q : Set (Space d)) (hQ : μ Q ≠ 0) (A : Set (Space d × Space d)) :
    (μ Q)^2 * ((ProbabilityTheory.cond μ Q).prod (ProbabilityTheory.cond μ Q)) A =
      ((μ.restrict Q).prod (μ.restrict Q)) A := by
  rw [ProbabilityTheory.cond,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,Measure.smul_apply,smul_eq_mul,smul_eq_mul]
  calc
    _ = (μ Q*(μ Q)⁻¹)*(μ Q*(μ Q)⁻¹)*
        ((μ.restrict Q).prod (μ.restrict Q)) A := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hQ (measure_ne_top μ Q)]; simp

theorem conditional_projection_to_restriction (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (Q : Set (Space d)) (hQ : μ Q ≠ 0) (w : Space d) (W : ℝ) {F : ℝ≥0∞}
    (h : projectionCollision (ProbabilityTheory.cond μ Q) w W ≤ F) :
    ((μ.restrict Q).prod (μ.restrict Q))
      {z : Space d × Space d | |inner ℝ w (z.1-z.2)| ≤ W} ≤ F*(μ Q)^2 := by
  rw [← conditional_product_mass_reconstruct μ Q hQ, mul_comm F]
  apply mul_le_mul' le_rfl
  simpa only [projectionCollision,real_inner_comm w] using h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParallelGood
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal parallel-test good sets and their directional buffer -/

namespace Falconer
open Set MeasureTheory Metric
open scoped ENNReal

theorem finiteTubeCount_direction_transfer {d : ℕ} {ι : Type*}
    (S : Finset ι) (v : ι → Space d) {w u : Sphere d}
    {δ M W₀ W₁ : ℝ} (hδ : 0 ≤ δ) (_hM : 0 ≤ M)
    (hclose : dist w u ≤ δ) (hbound : ∀ i ∈ S, ‖v i‖ ≤ M)
    (hwidth : W₁+2*δ*M ≤ W₀) :
    finiteTubeCount S v W₁ u ≤ finiteTubeCount S v W₀ w := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,ht⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi,?_⟩
  change ‖perpendicularPart (w:Space d) (v i)‖ ≤ W₀
  have herror := perpendicularPart_direction_error (sphere_norm w) (sphere_norm u) (v i)
  have hdist : ‖(w:Space d)-(u:Space d)‖ ≤ δ := by
    simpa only [Subtype.dist_eq,dist_eq_norm] using hclose
  have hb : 2*‖(w:Space d)-(u:Space d)‖*‖v i‖ ≤ 2*δ*M :=
    mul_le_mul (mul_le_mul_of_nonneg_left hdist (by norm_num)) (hbound i hi)
      (norm_nonneg _) (mul_nonneg (by norm_num) hδ)
  have htri := norm_sub_le_norm_sub_add_norm_sub (perpendicularPart (w:Space d) (v i))
    (perpendicularPart (u:Space d) (v i)) 0
  simp only [sub_zero] at htri
  change ‖perpendicularPart (u:Space d) (v i)‖ ≤ W₁ at ht
  linarith

namespace Regularization
variable {d : ℕ}

theorem parallelGoodSet_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) (W T : ℝ) :
    MeasurableSet (parallelGoodSet Q ρ g p P W T) := by
  classical
  unfold parallelGoodSet
  split_ifs
  · exact measurableSet_le (finiteTubeCount_measurable _ _ _) measurable_const
  · exact MeasurableSet.empty

theorem parallelGoodSet_buffer (Q : DyadicCube d) (ρ : Measure (Space d))
    (g p : ℕ) (P : CellPath d) {W₀ W₁ T δ : ℝ} (hδ : 0 ≤ δ)
    (hwidth : W₁+2*δ*(10*((d:ℝ)+1)/(2:ℝ)^g) ≤ W₀)
    {w u : Sphere d} (hw : w ∈ parallelGoodSet Q ρ g p P W₀ T)
    (hclose : dist w u ≤ δ) : u ∈ parallelGoodSet Q ρ g p P W₁ T := by
  classical
  by_cases hocc : 0 < ρ (Q.descendant P).carrier
  · simp only [parallelGoodSet,ite_eq_left hocc,mem_ofPred_eq] at hw ⊢
    have hc := finiteTubeCount_direction_transfer (parallelTestCells Q ρ g p P)
      (fun c => (Q.descendant c).center-(Q.descendant P).center) hδ
      (by positivity : 0 ≤ 10*((d:ℝ)+1)/(2:ℝ)^g) hclose ?_ hwidth
    · exact (Nat.cast_le.mpr hc).trans hw
    · intro c hc
      have h := (mem_ball.mp (Finset.mem_filter.mp hc).2.2).le
      simpa only [dist_eq_norm] using h
  · simp only [parallelGoodSet,ite_eq_right hocc,mem_empty_iff_false] at hw

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TestWidths
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The width and buffer scales of the all-dimensional tests

These are the exponents 500 and 50 in the all-dimensional test family.
-/

namespace Falconer

theorem angularTestWidth_gap (N : ℕ) (σ : ℝ) {J : ℕ} (hJ : 0 < J) (i n : ℕ) :
    angularTestWidth N σ J i n-angularTestWidth N σ J (i+1) n =
      ((2:ℝ)^N)^(500*σ)/((J:ℝ)*(2:ℝ)^n) := by
  have hj : (J:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hJ.ne'
  simp only [angularTestWidth,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

theorem uniform_angularTestWidth_gap {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) (C : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g n : ℕ, g ≤ n → ∀ i : ℕ,
      angularTestWidth N σ J (i+1) n+
        (C/(2:ℝ)^g)*angularTestRadius N σ (n-g) ≤
      angularTestWidth N σ J i n := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 450*σ) (C*(J:ℝ))
  refine ⟨N₀,?_⟩
  intro N hN g n hgn i
  have hj : 0 < (J:ℝ) := Nat.cast_pos.mpr hJ
  have hR : 0 < (2:ℝ)^N := by positivity
  have hconst := mul_le_mul_of_nonneg_right (hN₀ N hN)
    (by positivity : 0 ≤ ((2:ℝ)^N)^(50*σ))
  have he : ((2:ℝ)^N)^(450*σ)*((2:ℝ)^N)^(50*σ) =
      ((2:ℝ)^N)^(500*σ) := by rw [← Real.rpow_add hR]; congr 1; ring
  rw [he] at hconst
  have hp : (2:ℝ)^g*(2:ℝ)^(n-g) = (2:ℝ)^n := by
    rw [← pow_add,Nat.add_sub_of_le hgn]
  have hb : (C/(2:ℝ)^g)*angularTestRadius N σ (n-g) ≤
      ((2:ℝ)^N)^(500*σ)/((J:ℝ)*(2:ℝ)^n) := by
    calc
      _ ≤ (C/(2:ℝ)^g)*(1/(2:ℝ)^(n-g)*((2:ℝ)^N)^(50*σ)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = (C*(J:ℝ)*((2:ℝ)^N)^(50*σ))/((J:ℝ)*(2:ℝ)^n) := by
        rw [← hp]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hconst (by positivity)
  rw [← angularTestWidth_gap N σ hJ i n] at hb
  linarith

theorem dyadic_suffix_error {a p t : ℕ} (h : a+t ≤ 2*p) :
    (1/(2:ℝ)^p)^2/(1/(2:ℝ)^a) ≤ 1/(2:ℝ)^t := by
  have he : (1/(2:ℝ)^p)^2/(1/(2:ℝ)^a) = (2:ℝ)^a/((2:ℝ)^p)^2 := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h
  simpa only [pow_add,pow_mul,one_mul,mul_comm 2 p] using hp

theorem uniform_suffix_test_width {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) (C K : ℝ) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p t : ℕ, a+t ≤ 2*p → ∀ i ≤ J,
      C/(2:ℝ)^t+K*((1/(2:ℝ)^p)^2/(1/(2:ℝ)^a)) ≤
        angularTestWidth N σ J i t := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 500*σ) (C+K)
  refine ⟨N₀,?_⟩
  intro N hN a p t hapt i hi
  calc
    _ ≤ C/(2:ℝ)^t+K*(1/(2:ℝ)^t) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (dyadic_suffix_error hapt) hK)
    _ = (C+K)/(2:ℝ)^t := by ring
    _ ≤ ((2:ℝ)^N)^(500*σ)/(2:ℝ)^t :=
      div_le_div_of_nonneg_right (hN₀ N hN) (by positivity)
    _ ≤ _ := angularTestWidth_lower N σ hJ hi t

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionGood
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable projection tests on the full conditional probability -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem measurable_projectionCollision (μ : Measure (Space d)) [IsFiniteMeasure μ] (W : ℝ) :
    Measurable (fun w : Sphere d => projectionCollision μ (w:Space d) W) := by
  let S := {p : Sphere d × (Space d × Space d) |
    |inner ℝ (p.2.1-p.2.2) (p.1:Space d)| ≤ W}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_le (by fun_prop) measurable_const
  exact measurable_measure_prodMk_left hS

theorem measurableSet_projectionGoodSet (μ : Measure (Space d)) [IsFiniteMeasure μ] (W T : ℝ) :
    MeasurableSet (projectionGoodSet μ W T) :=
  measurableSet_le (measurable_projectionCollision μ W) measurable_const

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionBuffer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Directional buffers for the actual full-law projection test -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projectionCollision_direction_transfer (μ : Measure (Space d))
    {D δ W W' : ℝ} (hD : 0 ≤ D) (_hδ : 0 ≤ δ)
    (hsupport : ∀ᵐ z : Space d × Space d ∂μ.prod μ, ‖z.1-z.2‖ ≤ D)
    {v w : Space d} (hvw : ‖v-w‖ ≤ δ) (hwidth : W+D*δ ≤ W') :
    projectionCollision μ v W ≤ projectionCollision μ w W' := by
  apply measure_mono_ae
  filter_upwards [hsupport] with z hz
  intro htest
  have hinner : |inner ℝ (z.1-z.2) (w-v)| ≤ D*δ := by
    have hnorm : ‖w-v‖ ≤ δ := by simpa only [norm_sub_rev] using hvw
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hz hnorm (norm_nonneg _) hD)
  have he : inner ℝ (z.1-z.2) w = inner ℝ (z.1-z.2) v+inner ℝ (z.1-z.2) (w-v) := by
    rw [inner_sub_right]
    ring
  change |inner ℝ (z.1-z.2) v| ≤ W at htest
  change |inner ℝ (z.1-z.2) w| ≤ W'
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add htest hinner).trans hwidth)

theorem projectionGoodSet_buffer (μ : Measure (Space d))
    {D δ W W' T : ℝ} (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hsupport : ∀ᵐ z : Space d × Space d ∂μ.prod μ, ‖z.1-z.2‖ ≤ D)
    {v w : Sphere d} (hvw : dist v w ≤ δ) (hwidth : W+D*δ ≤ W')
    (hw : w ∈ projectionGoodSet μ W' T) : v ∈ projectionGoodSet μ W T := by
  have hd : ‖(v:Space d)-(w:Space d)‖ ≤ δ := by
    simpa only [Subtype.dist_eq,dist_eq_norm] using hvw
  exact (projectionCollision_direction_transfer μ hD hδ hsupport hd hwidth).trans hw

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalProjectionBuffer
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection buffers for the full original conditional laws -/

namespace Falconer.Regularization
open Set MeasureTheory
variable {d : ℕ}

theorem conditional_pair_diameter (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d) :
    ∀ᵐ z : Space d × Space d ∂
      (ProbabilityTheory.cond ρ (Q.descendant P).carrier).prod
        (ProbabilityTheory.cond ρ (Q.descendant P).carrier),
      ‖z.1-z.2‖ ≤ Real.sqrt d*(Q.side/(2:ℝ)^P.length) := by
  have hs : ∀ᵐ z ∂ProbabilityTheory.cond ρ (Q.descendant P).carrier,
      z ∈ (Q.descendant P).carrier :=
    ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant P).measurable (fun _ hz => hz)
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [hs] with x hx
  filter_upwards [hs] with y hy
  have hh := (Q.descendant P).dist_le (by rw [Q.descendant_side]; positivity) hx hy
  simpa only [dist_eq_norm,Q.descendant_side] using hh

theorem conditional_projection_buffer (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d)
    {δ W W' T : ℝ} (hδ : 0 ≤ δ) {v w : Sphere d} (hvw : dist v w ≤ δ)
    (hwidth : W+(Real.sqrt d/(2:ℝ)^P.length)*δ ≤ W')
    (hw : w ∈ projectionGoodSet (ProbabilityTheory.cond ρ (Q.descendant P).carrier) W' T) :
    v ∈ projectionGoodSet (ProbabilityTheory.cond ρ (Q.descendant P).carrier) W T := by
  apply projectionGoodSet_buffer _ (by positivity) hδ _ hvw hwidth hw
  simpa only [hQ,mul_one_div] using conditional_pair_diameter Q (by rw [hQ]; norm_num) ρ P

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ConditionalProjectionTest
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal occupied-anchor projection tests -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

namespace Regularization

theorem conditionalProjectionGoodSet_measurable (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d) (W T : ℝ) :
    MeasurableSet (conditionalProjectionGoodSet Q ρ P W T) := by
  classical
  unfold conditionalProjectionGoodSet
  split_ifs
  · exact measurableSet_projectionGoodSet _ _ _
  · exact MeasurableSet.empty

theorem conditionalProjectionGoodSet_buffer (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (P : CellPath d)
    {δ W W' T : ℝ} (hδ : 0 ≤ δ) {v w : Sphere d} (hvw : dist v w ≤ δ)
    (hwidth : W+(Real.sqrt d/(2:ℝ)^P.length)*δ ≤ W')
    (hw : w ∈ conditionalProjectionGoodSet Q ρ P W' T) :
    v ∈ conditionalProjectionGoodSet Q ρ P W T := by
  classical
  unfold conditionalProjectionGoodSet at hw ⊢
  split_ifs at hw ⊢ with hocc
  · exact conditional_projection_buffer Q hQ ρ P hδ hvw hwidth hw
  · exact False.elim hw

end Regularization
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorTests
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual all-dimensional tests indexed by policy descriptors

The policy list is scalar. Its tests use original occupied cells and the
full conditional probability of the current ambient-dimensional class.
The tolerance is the manuscript's 500-sigma width at every level.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)

variable {d : ℕ}

theorem descriptorGoodDirections_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (P : List (Fin d → Bool)) (b : PolicyDescriptor) :
    MeasurableSet (descriptorGoodDirections Q ρ m N σ J i P b) := by
  cases b with
  | parallel g p => exact Regularization.parallelGoodSet_measurable _ _ _ _ _ _ _
  | projection p t => exact Regularization.conditionalProjectionGoodSet_measurable _ _ _ _ _

theorem descriptor_projection_original_bound (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i p t : ℕ)
    (P : List (Fin d → Bool)) (w : Sphere d)
    (hw : w ∈ descriptorGoodDirections Q ρ m N σ J i P (.projection p t)) :
    ((ρ.restrict (Q.descendant P).carrier).prod (ρ.restrict (Q.descendant P).carrier))
      {z : Space d × Space d | |inner ℝ (w:Space d) (z.1-z.2)| ≤ angularTestWidth N σ J i t} ≤
      ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
        Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ)) *
          (ρ (Q.descendant P).carrier)^2 := by
  classical
  unfold descriptorGoodDirections Regularization.conditionalProjectionGoodSet at hw
  split_ifs at hw with hocc
  · exact conditional_projection_to_restriction ρ _ hocc.ne' _ _ hw
  · exact False.elim hw

theorem uniform_descriptor_direction_buffer {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) {C : ℝ} (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (b : PolicyDescriptor), descriptorValid N b →
      ∀ (P : List (Fin d → Bool)), P.length = descriptorAnchor b →
      ∀ (i : ℕ) (w u : Sphere d),
        dist w u ≤ C*angularTestRadius N σ (descriptorLength b) →
        w ∈ descriptorGoodDirections Q ρ m N σ J i P b →
        u ∈ descriptorGoodDirections Q ρ m N σ J (i+1) P b := by
  obtain ⟨N₁,h₁⟩ := uniform_angularTestWidth_gap hσ hJ
    (20*((d:ℝ)+1)*C) (by positivity)
  obtain ⟨N₂,h₂⟩ := uniform_angularTestWidth_gap hσ hJ
    (Real.sqrt d*C) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ _ m b hb P hP i w u hwu hw
  cases b with
  | parallel g p =>
    apply Regularization.parallelGoodSet_buffer Q ρ g p P
      (mul_nonneg hC (angularTestRadius_pos N σ (p-g)).le) ?_ hw hwu
    convert h₁ N ((le_max_left _ _).trans hN) g p hb.1 i using 1 <;> first | rfl | ring
  | projection p t =>
    apply Regularization.conditionalProjectionGoodSet_buffer Q hQ ρ P
      (mul_nonneg hC (angularTestRadius_pos N σ (t-p)).le)
      (by simpa only [dist_comm, descriptorLength] using hwu) ?_ hw
    have hh := h₂ N ((le_max_right _ _).trans hN) p t hb.1 i
    dsimp only [descriptorAnchor] at hP
    rw [hP]
    convert hh using 1 <;> first | rfl | ring

theorem policy_descriptor_valid (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) {b : PolicyDescriptor}
    (hb : b ∈ PlanarFalconer.policyDescriptorList A N q a t) : descriptorValid N b := by
  obtain ⟨s,u,_,hut,_,_,hpos,_,hbound⟩ := PlanarFalconer.policyDescriptor_origin A hq hb
  cases b <;> simp only [descriptorLength,descriptorAnchor,descriptorValid] at hpos hbound ⊢ <;>
    omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DescriptorMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual anchored masks and retained pair tests in every dimension

The angular set at an anchor is tested against the full conditional law.
Masks use finite spherical nets at one eighth of the manuscript's buffer
radius. Their construction is independent of the number of anchor cells.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff Topology
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
variable {d : ℕ}

theorem descriptorEndpointGood_measurable (Q : DyadicCube d) (ρ : Measure (Space d))
    [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) :
    MeasurableSet (descriptorEndpointGood Q ρ m N σ J i b) := by
  classical
  have hm : MeasurableSet (⋂ p ∈ cubePaths d (descriptorAnchor b),
      {z : Space d × Sphere d | z.1 ∈ (Q.descendant p).carrier →
        z.2 ∈ descriptorGoodDirections Q ρ m N σ J i p b}) := by
    apply Finset.measurableSet_biInter
    intro p _
    convert ((Q.descendant p).measurable.preimage measurable_fst).compl.union
      ((descriptorGoodDirections_measurable Q ρ m N σ J i p b).preimage measurable_snd) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_ofPred_eq,mem_union,mem_compl_iff,mem_preimage,imp_iff_not_or]
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp [descriptorEndpointGood]

theorem descriptorEndpointGood_on_cell (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (p : List (Fin d → Bool)) (hp : p.length = descriptorAnchor b)
    {x : Space d} (hx : x ∈ (Q.descendant p).carrier) (w : Sphere d) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b ↔
      w ∈ descriptorGoodDirections Q ρ m N σ J i p b := by
  constructor
  · exact fun h => h p ((mem_cubePaths _ _ _).mpr hp) hx
  · intro hw q hq hxq
    have hqp : q = p := by
      by_contra hn
      exact Set.disjoint_left.mp
        (Q.descendants_disjoint (((mem_cubePaths _ _ _).mp hq).trans hp.symm) hn) hxq hx
    simpa only [hqp] using hw

theorem uniform_descriptorEndpointGood_buffer {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (b : PolicyDescriptor), descriptorValid N b →
      ∀ (i : ℕ) (x : Space d) (w u : Sphere d),
        dist w u ≤ angularTestRadius N σ (descriptorLength b) →
        (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b →
        (x,u) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptor_direction_buffer (d := d) hσ hJ (C := 1) (by norm_num)
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m b hb i x w u hwu hw P hP hx
  apply h₀ N hN Q hQ ρ m b hb P ((mem_cubePaths _ _ _).mp hP) i w u
  · simpa only [one_mul] using hwu
  · exact hw P hP hx

theorem descriptorPairTests_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (B : Finset PolicyDescriptor) :
    MeasurableSet (descriptorPairTests w₀ Q ρ m N σ J i B) := by
  classical
  have hm := (normalizeToSphere_measurable w₀).comp (measurable_fst.sub measurable_snd)
  have hset : MeasurableSet (⋂ b ∈ B, {z : Space d × Space d |
      (z.1,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b ∧
      (z.2,normalizeToSphere w₀ (z.1-z.2)) ∈ descriptorEndpointGood Q ρ m N σ J i b}) := by
    apply Finset.measurableSet_biInter
    intro b _
    exact ((descriptorEndpointGood_measurable Q ρ m N σ J i b).preimage
      (measurable_fst.prodMk hm)).inter
        ((descriptorEndpointGood_measurable Q ρ m N σ J i b).preimage
          (measurable_snd.prodMk hm))
  convert hset using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp [descriptorPairTests]

theorem descriptorPairTests_mono (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    {A B : Finset PolicyDescriptor} (hAB : A ⊆ B) :
    descriptorPairTests w₀ Q ρ m N σ J i B ⊆ descriptorPairTests w₀ Q ρ m N σ J i A :=
  fun _ hz b hb => hz b (hAB hb)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CollisionFubini
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fubini regrouping for original four-point collision measures -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem four_pair_lintegral_regroup (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (F : (Space d × Space d) × (Space d × Space d) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂(μ.prod ν).prod (μ.prod ν)) =
      ∫⁻ xx, ∫⁻ yy, F ((xx.1,yy.1),(xx.2,yy.2)) ∂ν.prod ν ∂μ.prod μ := by
  calc
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ x', ∫⁻ y', F ((x,y),(x',y')) ∂ν ∂μ ∂ν ∂μ := by
      rw [lintegral_prod _ hF.aemeasurable,
        lintegral_prod _ hF.lintegral_prod_right'.aemeasurable]
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro y
      exact lintegral_prod _ ((hF.comp (by fun_prop)).aemeasurable)
    _ = ∫⁻ x, ∫⁻ x', ∫⁻ y, ∫⁻ y', F ((x,y),(x',y')) ∂ν ∂ν ∂μ ∂μ := by
      apply lintegral_congr
      intro x
      apply lintegral_lintegral_swap
      have hm : Measurable (fun z : (Space d × Space d) × Space d => F ((x,z.1.1),(z.1.2,z.2))) :=
        hF.comp (by fun_prop)
      exact hm.lintegral_prod_right'.aemeasurable
    _ = _ := by
      have hm : Measurable (fun z : (Space d × Space d) × (Space d × Space d) =>
          F ((z.1.1,z.2.1),(z.1.2,z.2.2))) := hF.comp (by fun_prop)
      rw [lintegral_prod _ hm.lintegral_prod_right'.aemeasurable]
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro x'
      exact (lintegral_prod (fun yy : Space d × Space d => F ((x,yy.1),(x',yy.2)))
        ((hF.comp (by fun_prop)).aemeasurable)).symm

theorem pair_collision_fiber_bound (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : Set ((Space d × Space d) × (Space d × Space d))) (hS : MeasurableSet S)
    (K : ℝ≥0∞)
    (hbound : ∀ᵐ xx ∂μ.prod μ,
      (ν.prod ν) {yy | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S} ≤ K) :
    ((μ.prod ν).prod (μ.prod ν)) S ≤ (μ univ)^2*K := by
  have hm : Measurable (S.indicator (fun _ => (1:ℝ≥0∞))) := measurable_const.indicator hS
  have he := four_pair_lintegral_regroup μ ν _ hm
  rw [lintegral_indicator hS,lintegral_const] at he
  simp only [one_mul,Measure.restrict_apply_univ] at he
  have hinner (xx : Space d × Space d) :
      (∫⁻ yy, S.indicator (fun _ => (1:ℝ≥0∞)) ((xx.1,yy.1),(xx.2,yy.2)) ∂ν.prod ν) =
      (ν.prod ν) {yy | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S} := by
    change (∫⁻ yy, {yy : Space d × Space d | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S}.indicator
      (fun _ => (1:ℝ≥0∞)) yy ∂ν.prod ν) = _
    have hmeas : MeasurableSet {yy : Space d × Space d | ((xx.1,yy.1),(xx.2,yy.2)) ∈ S} :=
      hS.preimage (show Measurable (fun yy : Space d × Space d => ((xx.1,yy.1),(xx.2,yy.2))) by fun_prop)
    rw [lintegral_indicator hmeas]
    simp
  simp_rw [hinner] at he
  rw [he]
  calc
    _ ≤ ∫⁻ _xx, K ∂μ.prod μ := lintegral_mono_ae hbound
    _ = _ := by
      rw [lintegral_const,← univ_prod_univ,Measure.prod_prod]
      simp only [pow_two,mul_comm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_Bins
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem diagonal_bin_mass_le {ι : Type*} [Countable ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (I : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise fun i j => Disjoint (I i) (I j)) (w : ℝ)
    (hdiam : ∀ i x, x ∈ I i → ∀ y, y ∈ I i → |x-y| ≤ w) :
    (∑' i, (μ (I i))^2) ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have hd : Pairwise fun i j => Disjoint (I i ×ˢ I i) (I j ×ˢ I j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.1 hj.1
  calc
    (∑' i, (μ (I i))^2) = ∑' i, (μ.prod μ) (I i ×ˢ I i) := by
      simp only [Measure.prod_prod, pow_two]
    _ = (μ.prod μ) (⋃ i, I i ×ˢ I i) :=
      (measure_iUnion hd (fun i => (hmeas i).prod (hmeas i))).symm
    _ ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
      apply measure_mono
      intro z hz
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact hdiam i z.1 hi.1 z.2 hi.2

theorem realBin_measurable (w : ℝ) (j : ℤ) : MeasurableSet (realBin w j) :=
  measurableSet_Ico

theorem realBin_disjoint {w : ℝ} (hw : 0 < w) :
    Pairwise fun i j => Disjoint (realBin w i) (realBin w j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : ((i+1 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxj.1.trans' hm)) hxi.2
  · have hc : ((j+1 : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxi.1.trans' hm)) hxj.2

theorem realBin_diameter (w : ℝ) (j : ℤ) {x y : ℝ}
    (hx : x ∈ realBin w j) (hy : y ∈ realBin w j) : |x-y| ≤ w := by
  simp only [realBin, Set.mem_Ico, Int.cast_add, Int.cast_one] at hx hy
  apply abs_le.mpr
  constructor <;> nlinarith

theorem real_bin_collision_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) :
    (∑' j : ℤ, (μ (realBin w j))^2) ≤
      (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} :=
  diagonal_bin_mass_le μ (realBin w) (realBin_measurable w) (realBin_disjoint hw) w
    (fun j _ hx _ hy => realBin_diameter w j hx hy)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BinOffsets
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem ennreal_offset_cauchy (a b : ℤ → ℝ≥0∞) (h : ℤ) :
    (∑' j : ℤ, a j*b (j-h)) ≤
      (∑' j : ℤ, (a j)^2)^(1/2 : ℝ) * (∑' j : ℤ, (b j)^2)^(1/2 : ℝ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ) hpq
    (measurable_of_countable a).aemeasurable
    (measurable_of_countable (fun j => b (j-h))).aemeasurable
  simp only [lintegral_count, ENNReal.rpow_two] at hh
  have he : (∑' j : ℤ, (b (j-h))^2) = ∑' j : ℤ, (b j)^2 :=
    (Equiv.subRight h).tsum_eq (fun j => (b j)^2)
  simpa only [one_div, he, Pi.mul_apply] using hh

 theorem realBin_cover {w : ℝ} (hw : 0 < w) (x : ℝ) :
    x ∈ realBin w ⌊x/w⌋ := by
  constructor
  · exact (le_div_iff₀ hw).mp (Int.floor_le (x/w))
  · simpa only [Int.cast_add,Int.cast_one] using
      (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/w))

 theorem offset_rectangles_mass_le (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (h : ℤ) :
    (μ.prod ν) (⋃ j : ℤ, realBin w j ×ˢ realBin w (j-h)) ≤
      binL2Norm μ w * binL2Norm ν w := by
  apply (measure_iUnion_le _).trans
  simp only [Measure.prod_prod]
  exact ennreal_offset_cauchy (fun j => μ (realBin w j)) (fun j => ν (realBin w j)) h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_BinKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem binKernelConstant_ne_top : binKernelConstant ≠ ∞ := by
  have hs := (Real.summable_one_div_int_add_rpow (1/2) 2).mpr (by norm_num)
  have ht : Summable (fun h : ℤ => 4/((h:ℝ)+1/2)^2) := by
    simpa only [Real.rpow_two,sq_abs,mul_one_div] using hs.mul_left 4
  exact ht.tsum_ofReal_ne_top

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BinBands
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem realBin_band_offset {w C s₀ x y : ℝ} (hw : 0 < w)
    (hb : |x-y-s₀| ≤ C*w) {i j : ℤ}
    (hi : x ∈ realBin w i) (hj : y ∈ realBin w j) :
    i-j-⌊s₀/w⌋ ∈ bandOffsets C := by
  have hi1 : (i:ℝ) ≤ x/w := (le_div_iff₀ hw).mpr hi.1
  have hi2 : x/w < (i:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hi.2
  have hj1 : (j:ℝ) ≤ y/w := (le_div_iff₀ hw).mpr hj.1
  have hj2 : y/w < (j:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hj.2
  have hm1 := Int.floor_le (s₀/w)
  have hm2 := Int.lt_floor_add_one (s₀/w)
  have hb' : |x/w-y/w-s₀/w| ≤ C := by
    rw [← sub_div,← sub_div,abs_div,abs_of_pos hw]
    exact (div_le_iff₀ hw).mpr hb
  obtain ⟨hl,hu⟩ := abs_le.mp hb'
  have hC := Nat.le_ceil C
  apply Finset.mem_Icc.mpr
  constructor
  · have h : -((⌈C⌉₊:ℕ):ℝ)-2 ≤ (i:ℝ)-(j:ℝ)-(⌊s₀/w⌋:ℝ) := by linarith
    exact_mod_cast h
  · have h : (i:ℝ)-(j:ℝ)-(⌊s₀/w⌋:ℝ) ≤ ((⌈C⌉₊:ℕ):ℝ)+2 := by linarith
    exact_mod_cast h

 theorem real_bin_shifted_band_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) (C s₀ : ℝ) :
    (μ.prod ν) {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ≤
      ((bandOffsets C).card : ℝ≥0∞) * (binL2Norm μ w * binL2Norm ν w) := by
  let m : ℤ := ⌊s₀/w⌋
  have hs : {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ⊆
      ⋃ h ∈ bandOffsets C, ⋃ j : ℤ, realBin w j ×ˢ realBin w (j-(h+m)) := by
    intro z hz
    let i : ℤ := ⌊z.1/w⌋
    let j : ℤ := ⌊z.2/w⌋
    have hi := realBin_cover hw z.1
    have hj := realBin_cover hw z.2
    refine mem_iUnion.mpr ⟨i-j-m,mem_iUnion.mpr ⟨realBin_band_offset hw hz hi hj,?_⟩⟩
    apply mem_iUnion.mpr
    refine ⟨i,hi,?_⟩
    have he : i-(i-j-m+m)=j := by omega
    simpa only [he] using hj
  calc
    _ ≤ (μ.prod ν) (⋃ h ∈ bandOffsets C, ⋃ j : ℤ,
        realBin w j ×ˢ realBin w (j-(h+m))) := measure_mono hs
    _ ≤ ∑ h ∈ bandOffsets C, (μ.prod ν) (⋃ j : ℤ,
        realBin w j ×ˢ realBin w (j-(h+m))) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ bandOffsets C, binL2Norm μ w * binL2Norm ν w :=
      Finset.sum_le_sum (fun h _ => offset_rectangles_mass_le μ ν w (h+m))
    _ = _ := by simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_BinEstimates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem binL2Norm_mul_self (μ : Measure ℝ) (w : ℝ) :
    binL2Norm μ w * binL2Norm μ w = ∑' j : ℤ, (μ (realBin w j))^2 := by
  unfold binL2Norm
  rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
  norm_num

theorem real_bin_shifted_self_band_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) (C s₀ : ℝ) :
    (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ≤
      ((bandOffsets C).card : ℝ≥0∞) *
        (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have h := real_bin_shifted_band_bound μ μ hw C s₀
  rw [binL2Norm_mul_self] at h
  exact h.trans (mul_le_mul_right (real_bin_collision_bound μ hw) _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_DistanceLinearization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual distance Taylor error for the suffix reduction

The error estimate is dimension independent before insertion of the cube
diameter. Its proof is the exact squared-norm identity, so no differentiable
extension across the diagonal is needed.
-/

namespace Falconer
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_linearization_bounds (u v : E) (hu : 0 < ‖u‖) :
    0 ≤ ‖v‖-inner ℝ (‖u‖⁻¹ • u) v ∧
      ‖v‖-inner ℝ (‖u‖⁻¹ • u) v ≤ ‖v-u‖^2/(2*‖u‖) := by
  have hi : inner ℝ (‖u‖⁻¹ • u) v = inner ℝ u v/‖u‖ := by
    rw [real_inner_smul_left]
    ring
  rw [hi]
  have hb : inner ℝ u v/‖u‖ ≤ ‖v‖ := by
    apply (div_le_iff₀ hu).mpr
    exact (real_inner_le_norm u v).trans_eq (mul_comm _ _)
  have he : 2*‖u‖*(‖v‖-inner ℝ u v/‖u‖) =
      ‖v-u‖^2-(‖v‖-‖u‖)^2 := by
    have hs := norm_sub_sq_real v u
    rw [real_inner_comm u v] at hs
    field_simp
    nlinarith
  refine ⟨sub_nonneg.mpr hb,?_⟩
  apply (le_div_iff₀ (mul_pos (by norm_num) hu)).mpr
  nlinarith [sq_nonneg (‖v‖-‖u‖)]

theorem norm_linearization_abs_le (u v : E) (hu : 0 < ‖u‖) :
    |‖v‖-inner ℝ (‖u‖⁻¹ • u) v| ≤ ‖v-u‖^2/(2*‖u‖) := by
  rw [abs_of_nonneg (norm_linearization_bounds u v hu).1]
  exact (norm_linearization_bounds u v hu).2

omit [InnerProductSpace ℝ E] in
theorem pair_displacement_bound (x y c₁ c₂ : E) {δ₁ δ₂ : ℝ}
    (h₁ : ‖x-c₁‖ ≤ δ₁) (h₂ : ‖y-c₂‖ ≤ δ₂) :
    ‖(x-y)-(c₁-c₂)‖ ≤ δ₁+δ₂ := by
  have he : (x-y)-(c₁-c₂) = (x-c₁)-(y-c₂) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add h₁ h₂)

/-- Original distances on a pair of small cubes have the required
quadratic error relative to their center direction. -/
theorem DyadicCube.distance_linearization {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g : ℝ} (hg : 0 < g) (hsep : g ≤ ‖P.center-Q.center‖)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    |dist x y-inner ℝ (‖P.center-Q.center‖⁻¹ • (P.center-Q.center)) (x-y)| ≤
      2*(d:ℝ)*P.side^2/g := by
  have hQp : 0 < Q.side := by rw [hQ]; exact hP
  have hδ : ‖(x-y)-(P.center-Q.center)‖ ≤ 2*Real.sqrt d*P.side := by
    have h₁ := P.dist_le hP.le hx (P.center_mem hP)
    have h₂ := Q.dist_le hQp.le hy (Q.center_mem hQp)
    rw [hQ] at h₂
    simpa only [dist_eq_norm,two_mul,mul_add,add_mul] using
      pair_displacement_bound x y P.center Q.center h₁ h₂
  have hsquare : ‖(x-y)-(P.center-Q.center)‖^2 ≤ 4*(d:ℝ)*P.side^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hδ
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)]
  have hnorm : 0 < ‖P.center-Q.center‖ := hg.trans_le hsep
  rw [dist_eq_norm]
  apply (norm_linearization_abs_le _ _ hnorm).trans
  calc
    _ ≤ (4*(d:ℝ)*P.side^2)/(2*‖P.center-Q.center‖) :=
      div_le_div_of_nonneg_right hsquare (by positivity)
    _ ≤ (4*(d:ℝ)*P.side^2)/(2*g) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hsep (by norm_num))
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixCollision
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The local collision estimate in the all-dimensional suffix step

A projection test on the entire second conditional cell controls every
translated collision window. Quadratic distance linearization transfers
that test to the original distance pushforward, before any cell grouping.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem projection_shifted_band_bound (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (e : Space d) {w : ℝ} (hw : 0 < w) (C s : ℝ) :
    (μ.prod μ) {z : Space d × Space d | |inner ℝ e (z.1-z.2)-s| ≤ C*w} ≤
      ((PlanarFalconer.bandOffsets C).card : ℝ≥0∞) *
        (μ.prod μ) {z : Space d × Space d | |inner ℝ e (z.1-z.2)| ≤ w} := by
  let f : Space d → ℝ := fun y => inner ℝ e y
  have hf : Measurable f := by dsimp [f]; fun_prop
  let ν := Measure.map f μ
  have he (v s : ℝ) :
      (ν.prod ν) {z : ℝ × ℝ | |z.1-z.2-s| ≤ v} =
      (μ.prod μ) {z : Space d × Space d | |inner ℝ e (z.1-z.2)-s| ≤ v} := by
    rw [show ν.prod ν = Measure.map (Prod.map f f) (μ.prod μ) from
      Measure.map_prod_map μ μ hf hf,Measure.map_apply (hf.prodMap hf) (by measurability)]
    congr 1
    ext z
    change |f z.1-f z.2-s| ≤ v ↔ |inner ℝ e (z.1-z.2)-s| ≤ v
    simp only [f,inner_sub_right]
  have h := PlanarFalconer.real_bin_shifted_self_band_bound ν hw C s
  rw [he] at h
  have hz := he w 0
  simp only [sub_zero] at hz
  rwa [hz] at h

theorem affine_distance_collision {x x' y y' e : Space d} {w : ℝ}
    (hx : |dist x y-inner ℝ e (x-y)| ≤ w)
    (hx' : |dist x' y'-inner ℝ e (x'-y')| ≤ w)
    (hc : |dist x y-dist x' y'| ≤ w) :
    |inner ℝ e (y-y')-inner ℝ e (x-x')| ≤ 3*w := by
  have he : inner ℝ e (y-y')-inner ℝ e (x-x') =
      -(inner ℝ e (x-y)-inner ℝ e (x'-y')) := by
    simp only [inner_sub_right]
    ring
  rw [he,abs_neg]
  obtain ⟨h₁,h₂⟩ := abs_le.mp hx
  obtain ⟨h₃,h₄⟩ := abs_le.mp hx'
  obtain ⟨h₅,h₆⟩ := abs_le.mp hc
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem local_distance_collision_bound (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) (e : Space d) {w : ℝ} (hw : 0 < w)
    (haff : ∀ x ∈ P.carrier, ∀ y ∈ Q.carrier, |dist x y-inner ℝ e (x-y)| ≤ w)
    {H : ℝ≥0∞}
    (hproj : ((ν.restrict Q.carrier).prod (ν.restrict Q.carrier))
      {z : Space d × Space d | |inner ℝ e (z.1-z.2)| ≤ w} ≤ H) :
    (((μ.restrict P.carrier).prod (ν.restrict Q.carrier)).prod
      ((μ.restrict P.carrier).prod (ν.restrict Q.carrier)))
        {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} ≤
      (μ P.carrier)^2 * (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞)*H) := by
  apply (pair_collision_fiber_bound (μ.restrict P.carrier) (ν.restrict Q.carrier)
    _ (by measurability) (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞)*H) ?_).trans_eq
      (by simp)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem P.measurable),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem P.measurable)] with xx hx hx'
  apply le_trans _ (mul_le_mul' le_rfl hproj)
  apply le_trans _ (projection_shifted_band_bound (ν.restrict Q.carrier) e hw 3
    (inner ℝ e (xx.1-xx.2)))
  apply measure_mono_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem Q.measurable),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem Q.measurable)] with yy hy hy'
  intro hc
  exact affine_distance_collision (haff xx.1 hx yy.1 hy) (haff xx.2 hx' yy.2 hy') hc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SuffixDirection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transferring the suffix witness test to the cell-center direction

The test is imposed on the full conditional law in the witness direction.
Only the direction changes; its quadratic error is absorbed by the test
width before the original-law collision estimate is used.
-/

namespace Falconer
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalized_difference_le (u v : E) (hu : 0 < ‖u‖) (hv : 0 < ‖v‖) :
    ‖‖v‖⁻¹ • v - ‖u‖⁻¹ • u‖ ≤ 2*‖v-u‖/‖u‖ := by
  have he : ‖v‖⁻¹ • v - ‖u‖⁻¹ • u =
      ‖u‖⁻¹ • (v-u) + (‖v‖⁻¹-‖u‖⁻¹) • v := by module
  have hnorm : ‖(‖v‖⁻¹-‖u‖⁻¹) • v‖ = |‖u‖-‖v‖|/‖u‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ = |(‖v‖⁻¹-‖u‖⁻¹)*‖v‖| := by rw [abs_mul,abs_of_pos hv]
      _ = |(‖u‖-‖v‖)/‖u‖| := by congr 1; field_simp
      _ = _ := by rw [abs_div,abs_of_pos hu]
  rw [he]
  calc
    _ ≤ ‖‖u‖⁻¹ • (v-u)‖ + ‖(‖v‖⁻¹-‖u‖⁻¹) • v‖ := norm_add_le _ _
    _ = ‖v-u‖/‖u‖ + |‖u‖-‖v‖|/‖u‖ := by
      rw [hnorm,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hu]
      ring
    _ ≤ ‖v-u‖/‖u‖ + ‖v-u‖/‖u‖ := by
      exact add_le_add le_rfl (div_le_div_of_nonneg_right
        (by simpa only [abs_sub_comm] using abs_norm_sub_norm_le v u) hu.le)
    _ = _ := by ring

theorem DyadicCube.pair_direction_approximation {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g : ℝ} (hg : 0 < g) (hsep : g ≤ ‖P.center-Q.center‖)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) (hxy : x ≠ y) :
    ‖‖x-y‖⁻¹ • (x-y) - ‖P.center-Q.center‖⁻¹ • (P.center-Q.center)‖ ≤
      4*Real.sqrt d*P.side/g := by
  have hQp : 0 < Q.side := by rwa [hQ]
  have hδ : ‖(x-y)-(P.center-Q.center)‖ ≤ 2*Real.sqrt d*P.side := by
    have h₁ := P.dist_le hP.le hx (P.center_mem hP)
    have h₂ := Q.dist_le hQp.le hy (Q.center_mem hQp)
    rw [hQ] at h₂
    simpa only [dist_eq_norm,two_mul,mul_add,add_mul] using
      pair_displacement_bound x y P.center Q.center h₁ h₂
  calc
    _ ≤ 2*‖(x-y)-(P.center-Q.center)‖/‖P.center-Q.center‖ :=
      normalized_difference_le _ _ (hg.trans_le hsep) (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
    _ ≤ 2*(2*Real.sqrt d*P.side)/g :=
      div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hδ (by norm_num)) hg hsep
    _ = _ := by ring

theorem cell_projection_direction_transfer {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (Q : DyadicCube d)
    (hQ : 0 ≤ Q.side) (e f : Space d) {κ w W : ℝ} (hκ : 0 ≤ κ)
    (hef : ‖e-f‖ ≤ κ) (hwidth : w+κ*Real.sqrt d*Q.side ≤ W) :
    ((μ.restrict Q.carrier).prod (μ.restrict Q.carrier))
      {z : Space d × Space d | |inner ℝ e (z.1-z.2)| ≤ w} ≤
    ((μ.restrict Q.carrier).prod (μ.restrict Q.carrier))
      {z : Space d × Space d | |inner ℝ f (z.1-z.2)| ≤ W} := by
  apply measure_mono_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem Q.measurable),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem Q.measurable)] with z hz₁ hz₂
  intro hz
  have hdist := Q.dist_le hQ hz₁ hz₂
  rw [dist_eq_norm] at hdist
  have herr : |inner ℝ (f-e) (z.1-z.2)| ≤ κ*Real.sqrt d*Q.side := by
    calc
      _ ≤ ‖f-e‖*‖z.1-z.2‖ := abs_real_inner_le_norm _ _
      _ ≤ κ*(Real.sqrt d*Q.side) := mul_le_mul
        (by simpa only [norm_sub_rev] using hef) hdist (norm_nonneg _) hκ
      _ = _ := by ring
  have hid : inner ℝ f (z.1-z.2) =
      inner ℝ e (z.1-z.2)+inner ℝ (f-e) (z.1-z.2) := by
    rw [inner_sub_left]; ring
  change |inner ℝ e (z.1-z.2)| ≤ w at hz
  show |inner ℝ f (z.1-z.2)| ≤ W
  rw [hid]
  exact ((abs_add_le _ _).trans (add_le_add hz herr)).trans hwidth

theorem suffix_witness_projection_transfer {d : ℕ}
    (ν : Measure (Space d)) [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g w W : ℝ} (hg : 0 < g) (hsep : g ≤ ‖P.center-Q.center‖)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) (hxy : x ≠ y)
    (hwidth : w+4*(d:ℝ)*P.side^2/g ≤ W) :
    ((ν.restrict Q.carrier).prod (ν.restrict Q.carrier))
      {z : Space d × Space d |
        |inner ℝ (‖P.center-Q.center‖⁻¹ • (P.center-Q.center)) (z.1-z.2)| ≤ w} ≤
    ((ν.restrict Q.carrier).prod (ν.restrict Q.carrier))
      {z : Space d × Space d | |inner ℝ (‖x-y‖⁻¹ • (x-y)) (z.1-z.2)| ≤ W} := by
  apply cell_projection_direction_transfer ν Q (by rw [hQ]; exact hP.le) _ _
    (show 0 ≤ 4*Real.sqrt d*P.side/g by positivity)
    (by simpa only [norm_sub_rev] using P.pair_direction_approximation Q hP hQ hg hsep hx hy hxy)
  rw [hQ]
  convert hwidth using 1
  all_goals try with_reducible_and_instances rfl
  rw [show 4*Real.sqrt (d:ℝ)*P.side/g*Real.sqrt d*P.side =
    4*(Real.sqrt d)^2*P.side^2/g by ring,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FiniteMeasureProducts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem finite_measure_prod_sum {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (S : Finset ι) (T : Finset κ) (μ : ι → Measure α) (ν : κ → Measure β)
    [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)] :
    (∑ i ∈ S, μ i).prod (∑ j ∈ T, ν j) = ∑ i ∈ S, ∑ j ∈ T, (μ i).prod (ν j) := by
  apply Measure.ext_prod
  intro s t hs ht
  simp only [Measure.prod_prod,Measure.finsetSum_apply,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem finite_measure_restrict_sum {α ι : Type*} [MeasurableSpace α]
    (S : Finset ι) (μ : ι → Measure α) (A : Set α) :
    (∑ i ∈ S, μ i).restrict A = ∑ i ∈ S, (μ i).restrict A := by
  ext s hs
  simp only [Measure.restrict_apply hs,Measure.finsetSum_apply]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FiniteBinComparison
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem ennreal_sq_bound_sqrt {x y F : ℝ≥0∞} (h : x^2 ≤ F*y^2) :
    x ≤ F^(1/2:ℝ)*y := by
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hh
  simp only [← ENNReal.rpow_two,← ENNReal.rpow_mul] at hh
  norm_num at hh
  exact hh

theorem bin_cross_from_squares (α β : Measure ℝ) (w : ℝ) {F a b : ℝ≥0∞}
    (ha : (binL2Norm α w)^2 ≤ F*a^2) (hb : (binL2Norm β w)^2 ≤ F*b^2) :
    (∑' k : ℤ, α (realBin w k)*β (realBin w k)) ≤ F*(a*b) := by
  have hcross := ennreal_offset_cauchy (fun k => α (realBin w k))
    (fun k => β (realBin w k)) 0
  simp only [sub_zero] at hcross
  have hh := hcross.trans (mul_le_mul' (ennreal_sq_bound_sqrt ha) (ennreal_sq_bound_sqrt hb))
  have hs : F^(1/2:ℝ)*F^(1/2:ℝ) = F := by
    rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
    norm_num
  apply hh.trans_eq
  calc
    _ = (F^(1/2:ℝ)*F^(1/2:ℝ))*(a*b) := mul_mul_mul_comm _ _ _ _
    _ = _ := by rw [hs]

theorem finite_bin_collision_comparison {ι : Type*} (S : Finset ι)
    (α β : ι → Measure ℝ) [∀ i, IsFiniteMeasure (α i)] [∀ i, IsFiniteMeasure (β i)]
    (w : ℝ) (E : Set (ℝ × ℝ)) (F : ℝ≥0∞)
    (hnorm : ∀ i ∈ S, (binL2Norm (α i) w)^2 ≤ F*((β i) univ)^2)
    (hcoarse : ∀ i ∈ S, ∀ j ∈ S,
      (∃ k : ℤ, α i (realBin w k) ≠ 0 ∧ α j (realBin w k) ≠ 0) →
      ((β i).prod (β j)) E = (β i univ)*(β j univ)) :
    (binL2Norm (∑ i ∈ S, α i) w)^2 ≤
      F*((∑ i ∈ S, β i).prod (∑ i ∈ S, β i)) E := by
  classical
  have hpair (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      (∑' k : ℤ, α i (realBin w k)*α j (realBin w k)) ≤ F*((β i).prod (β j)) E := by
    by_cases hh : ∃ k : ℤ, α i (realBin w k) ≠ 0 ∧ α j (realBin w k) ≠ 0
    · rw [hcoarse i hi j hj hh]
      exact bin_cross_from_squares _ _ w (hnorm i hi) (hnorm j hj)
    · have hz (k : ℤ) : α i (realBin w k)*α j (realBin w k) = 0 := by
        by_cases hi0 : α i (realBin w k) = 0
        · simp [hi0]
        · have hj0 : α j (realBin w k) = 0 := by
            by_contra hj0
            exact hh ⟨k,hi0,hj0⟩
          simp [hj0]
      simp only [hz,tsum_zero,zero_le]
  rw [pow_two,binL2Norm_mul_self]
  simp only [Measure.finsetSum_apply,pow_two,Finset.sum_mul,Finset.mul_sum]
  simp_rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, F*((β i).prod (β j)) E :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ = _ := by
      rw [finite_measure_prod_sum]
      simp only [Measure.finsetSum_apply,Finset.mul_sum]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixGrouping
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coarse grouping of the actual all-dimensional distance cells

Two fine distance distributions sharing one bin force all distances of
their full cell pairs into a common coarse collision band. The width
constant retains the ambient dimension explicitly.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem cellDistance_mass (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) : cellDistance μ ν P Q univ = μ P.carrier*ν Q.carrier := by
  rw [cellDistance,Measure.map_apply (by fun_prop) MeasurableSet.univ,preimage_univ,
    ← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ,Measure.restrict_apply_univ]

theorem cellDistance_bin_witness (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (w : ℝ) (k : ℤ) (hm : cellDistance μ ν P Q (PlanarFalconer.realBin w k) ≠ 0) :
    ∃ x ∈ P.carrier, ∃ y ∈ Q.carrier, dist x y ∈ PlanarFalconer.realBin w k := by
  rw [cellDistance,Measure.map_apply (by fun_prop) (PlanarFalconer.realBin_measurable w k)] at hm
  have hae : ∀ᵐ z ∂(μ.restrict P.carrier).prod (ν.restrict Q.carrier),
      z.1 ∈ P.carrier ∧ z.2 ∈ Q.carrier := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem P.measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem Q.measurable)] with z hx hy
    exact ⟨hx,hy⟩
  obtain ⟨z,hz,hmem⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm (ae_restrict_of_ae hae)
  exact ⟨z.1,hmem.1,z.2,hmem.2,hz⟩

theorem cell_distance_variation (P Q : DyadicCube d) (hP : 0 ≤ P.side)
    (hQ : Q.side = P.side) {x x' y y' : Space d}
    (hx : x ∈ P.carrier) (hx' : x' ∈ P.carrier)
    (hy : y ∈ Q.carrier) (hy' : y' ∈ Q.carrier) :
    |dist x y-dist x' y'| ≤ 2*Real.sqrt d*P.side := by
  have h₁ := P.dist_le hP hx hx'
  have h₂ := Q.dist_le (by rwa [hQ]) hy hy'
  rw [hQ] at h₂
  have hh := dist_dist_dist_le x y x' y'
  rw [Real.dist_eq] at hh
  exact hh.trans ((add_le_add h₁ h₂).trans_eq (by ring))

theorem shared_bin_full_cell_collision
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q P' Q' : DyadicCube d) (hP : 0 ≤ P.side)
    (hQ : Q.side = P.side) (hP' : P'.side = P.side) (hQ' : Q'.side = P.side)
    (α β : Measure ℝ) (hα : α ≤ cellDistance μ ν P Q)
    (hβ : β ≤ cellDistance μ ν P' Q') {w : ℝ} (hw : w ≤ P.side)
    (hbin : ∃ k : ℤ, α (PlanarFalconer.realBin w k) ≠ 0 ∧
      β (PlanarFalconer.realBin w k) ≠ 0) :
    ((cellDistance μ ν P Q).prod (cellDistance μ ν P' Q'))
      {z : ℝ × ℝ | |z.1-z.2| ≤ (1+4*Real.sqrt d)*P.side} =
      (cellDistance μ ν P Q univ)*(cellDistance μ ν P' Q' univ) := by
  obtain ⟨k,hk₁,hk₂⟩ := hbin
  have hfull₁ : cellDistance μ ν P Q (PlanarFalconer.realBin w k) ≠ 0 := by
    intro hz
    exact hk₁ (le_antisymm ((hα _).trans_eq hz) bot_le)
  have hfull₂ : cellDistance μ ν P' Q' (PlanarFalconer.realBin w k) ≠ 0 := by
    intro hz
    exact hk₂ (le_antisymm ((hβ _).trans_eq hz) bot_le)
  obtain ⟨x,hx,y,hy,hxy⟩ := cellDistance_bin_witness μ ν P Q w k hfull₁
  obtain ⟨x',hx',y',hy',hx'y'⟩ := cellDistance_bin_witness μ ν P' Q' w k hfull₂
  have hdist := PlanarFalconer.realBin_diameter w k hxy hx'y'
  have hmem (A B : DyadicCube d) :
      ∀ᵐ z ∂(μ.restrict A.carrier).prod (ν.restrict B.carrier),
        z.1 ∈ A.carrier ∧ z.2 ∈ B.carrier := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem A.measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem B.measurable)] with z hz₁ hz₂
    exact ⟨hz₁,hz₂⟩
  have hgood : ∀ᵐ z ∂((μ.restrict P.carrier).prod (ν.restrict Q.carrier)).prod
      ((μ.restrict P'.carrier).prod (ν.restrict Q'.carrier)),
      |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ (1+4*Real.sqrt d)*P.side := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hmem P Q),
      Measure.quasiMeasurePreserving_snd.ae (hmem P' Q')] with z hz hz'
    have h₁ := cell_distance_variation P Q hP hQ hz.1 hx hz.2 hy
    have h₂ := cell_distance_variation P' Q' (by rwa [hP'])
      (hQ'.trans hP'.symm) hz'.1 hx' hz'.2 hy'
    rw [hP'] at h₂
    obtain ⟨h₁l,h₁r⟩ := abs_le.mp h₁
    obtain ⟨h₂l,h₂r⟩ := abs_le.mp h₂
    obtain ⟨h₃l,h₃r⟩ := abs_le.mp hdist
    apply abs_le.mpr
    constructor <;> nlinarith
  rw [cellDistance,cellDistance,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (by measurability)]
  change (((μ.restrict P.carrier).prod (ν.restrict Q.carrier)).prod
      ((μ.restrict P'.carrier).prod (ν.restrict Q'.carrier)))
      {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ (1+4*Real.sqrt d)*P.side} = _
  rw [measure_congr (Filter.eventuallyEq_univ.mpr hgood),← univ_prod_univ,Measure.prod_prod]
  simp only [Measure.map_apply (continuous_fst.dist continuous_snd).measurable
    MeasurableSet.univ,preimage_univ]

/-- The full suffix cell grouping. Local projection tests apply to the
entire second conditional cell; the selected submeasure may be arbitrary. -/
theorem finite_suffix_cell_comparison {ι : Type*} (S : Finset ι)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : ι → DyadicCube d) (e : ι → Space d)
    (α : ι → Measure ℝ) [∀ i, IsFiniteMeasure (α i)]
    {s w : ℝ} (hs : 0 ≤ s) (hw : 0 < w) (hws : w ≤ s)
    (hP : ∀ i ∈ S, (P i).side = s) (hQ : ∀ i ∈ S, (Q i).side = s)
    (hα : ∀ i ∈ S, α i ≤ cellDistance μ ν (P i) (Q i))
    (haff : ∀ i ∈ S, ∀ x ∈ (P i).carrier, ∀ y ∈ (Q i).carrier,
      |dist x y-inner ℝ (e i) (x-y)| ≤ w)
    (F : ℝ≥0∞)
    (hproj : ∀ i ∈ S, ((ν.restrict (Q i).carrier).prod (ν.restrict (Q i).carrier))
      {z : Space d × Space d | |inner ℝ (e i) (z.1-z.2)| ≤ w} ≤
        F*(ν (Q i).carrier)^2) :
    (PlanarFalconer.binL2Norm (∑ i ∈ S, α i) w)^2 ≤
      (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞)*F) *
        ((∑ i ∈ S, cellDistance μ ν (P i) (Q i)).prod
          (∑ i ∈ S, cellDistance μ ν (P i) (Q i)))
          {z : ℝ × ℝ | |z.1-z.2| ≤ (1+4*Real.sqrt d)*s} := by
  apply PlanarFalconer.finite_bin_collision_comparison S α
    (fun i => cellDistance μ ν (P i) (Q i)) w _ _
  · intro i hi
    have hlocal := local_distance_collision_bound μ ν (P i) (Q i) (e i) hw
      (haff i hi) (hproj i hi)
    rw [pow_two,PlanarFalconer.binL2Norm_mul_self]
    apply (PlanarFalconer.real_bin_collision_bound (α i) hw).trans
    apply (Measure.prod_mono (hα i hi) (hα i hi) _).trans
    rw [cellDistance,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_apply (by fun_prop) (by measurability)]
    apply hlocal.trans_eq
    change μ (P i).carrier ^ 2 *
      (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) * (F * ν (Q i).carrier ^ 2)) =
      (((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) * F) *
        (cellDistance μ ν (P i) (Q i) univ)^2
    rw [cellDistance_mass]
    ring
  · intro i hi j hj hbin
    have hP0 : 0 ≤ (P i).side := by rwa [hP i hi]
    have he := shared_bin_full_cell_collision μ ν (P i) (Q i) (P j) (Q j) hP0
      ((hQ i hi).trans (hP i hi).symm)
      ((hP j hj).trans (hP i hi).symm)
      ((hQ j hj).trans (hP i hi).symm)
      (α i) (α j) (hα i hi) (hα j hj) (by rwa [hP i hi]) hbin
    simpa only [hP i hi] using he

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RetainedPairs
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition into the suffix cells having a witness

Only actual original-law restrictions occur. Empty intersections with the
parent's good-pair set contribute zero, so retaining witnessed cells is an
exact identity, before their full cell measures are used for comparison.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem testedCellPair_eq_zero (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (hw : ¬ ∃ x ∈ P.carrier, ∃ y ∈ Q.carrier, (x,y) ∈ G) :
    testedCellPair μ ν P Q G = 0 := by
  apply Measure.restrict_eq_zero.mpr
  rw [Measure.prod_restrict,Measure.restrict_apply hG]
  have he : G ∩ (P.carrier ×ˢ Q.carrier) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hw ⟨z.1,hz.2.1,z.2,hz.2.2,hz.1⟩
  rw [he,measure_empty]

theorem testedCellPair_split (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (n : ℕ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    testedCellPair μ ν P Q G =
      ∑ c ∈ retainedCellPairs μ ν P Q n G,
        testedCellPair μ ν (P.descendant c.1) (Q.descendant c.2) G := by
  rw [testedCellPair,P.restrict_occupiedPaths μ n,Q.restrict_occupiedPaths ν n,
    PlanarFalconer.finite_measure_prod_sum]
  rw [← Finset.sum_product (P.occupiedPaths μ n) (Q.occupiedPaths ν n)
    (fun c : List (Fin d → Bool) × List (Fin d → Bool) =>
      (μ.restrict (P.descendant c.1).carrier).prod (ν.restrict (Q.descendant c.2).carrier)),
    PlanarFalconer.finite_measure_restrict_sum]
  change (∑ c ∈ P.occupiedPaths μ n ×ˢ Q.occupiedPaths ν n,
      testedCellPair μ ν (P.descendant c.1) (Q.descendant c.2) G) = _
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hn
  apply testedCellPair_eq_zero μ ν _ _ G hG
  intro hw
  exact hn (Finset.mem_filter.mpr ⟨hc,hw⟩)

theorem testedCellDistance_split (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (n : ℕ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    testedCellDistance μ ν P Q G =
      ∑ c ∈ retainedCellPairs μ ν P Q n G,
        testedCellDistance μ ν (P.descendant c.1) (Q.descendant c.2) G := by
  rw [testedCellDistance,testedCellPair_split μ ν P Q n G hG,
    Measure.map_finset_sum (by fun_prop)]
  rfl

theorem testedCellDistance_le (μ ν : Measure (Space d))
    (P Q : DyadicCube d) (G : Set (Space d × Space d)) :
    testedCellDistance μ ν P Q G ≤ cellDistance μ ν P Q := by
  exact Measure.map_mono Measure.restrict_le_self (by fun_prop)

theorem full_retained_distance_le (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (n : ℕ) (G H : Set (Space d × Space d))
    (hcover : ∀ c ∈ retainedCellPairs μ ν P Q n G,
      (P.descendant c.1).carrier ×ˢ (Q.descendant c.2).carrier ⊆ H) :
    (∑ c ∈ retainedCellPairs μ ν P Q n G,
      cellDistance μ ν (P.descendant c.1) (Q.descendant c.2)) ≤
        testedCellDistance μ ν P Q H := by
  have he (c : List (Fin d → Bool) × List (Fin d → Bool))
      (hc : c ∈ retainedCellPairs μ ν P Q n G) :
      cellDistance μ ν (P.descendant c.1) (Q.descendant c.2) =
        testedCellDistance μ ν (P.descendant c.1) (Q.descendant c.2) H := by
    unfold cellDistance testedCellDistance testedCellPair
    rw [Measure.prod_restrict,Measure.restrict_restrict'
      ((P.descendant c.1).measurable.prod (Q.descendant c.2).measurable),
      inter_eq_right.mpr (hcover c hc)]
  rw [Finset.sum_congr rfl he]
  unfold testedCellDistance
  rw [← Measure.map_finset_sum (by fun_prop)]
  apply Measure.map_mono _ (by fun_prop)
  unfold testedCellPair
  rw [P.restrict_occupiedPaths μ n,Q.restrict_occupiedPaths ν n,
    PlanarFalconer.finite_measure_prod_sum,
    ← Finset.sum_product (P.occupiedPaths μ n) (Q.occupiedPaths ν n)
      (fun c : List (Fin d → Bool) × List (Fin d → Bool) =>
        (μ.restrict (P.descendant c.1).carrier).prod (ν.restrict (Q.descendant c.2).carrier)),
    PlanarFalconer.finite_measure_restrict_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => bot_le)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixReduction
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original-law suffix collision reduction

This is the analytic suffix step before substituting the profile test
threshold. The only test used is a projection collision test on each full
second cell, in the direction of an actual witness pair. The full retained
cell pairs are required to satisfy the child tests; no witness-dependent
restriction of the tested conditional law is made.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem tested_suffix_collision_bound
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (P Q : DyadicCube d) (n : ℕ) (G H : Set (Space d × Space d))
    (hG : MeasurableSet G) (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g w W : ℝ} (hg : 0 < g) (hw : 0 < w)
    (hws : w ≤ P.side/(2:ℝ)^n)
    (hsmall : 2*(d:ℝ)*(P.side/(2:ℝ)^n)^2/g ≤ w)
    (hwidth : w+4*(d:ℝ)*(P.side/(2:ℝ)^n)^2/g ≤ W)
    (hsep : ∀ c ∈ retainedCellPairs μ ν P Q n G,
      g ≤ ‖(P.descendant c.1).center-(Q.descendant c.2).center‖)
    (F : ℝ≥0∞)
    (hproj : ∀ c ∈ retainedCellPairs μ ν P Q n G,
      ∃ x ∈ (P.descendant c.1).carrier, ∃ y ∈ (Q.descendant c.2).carrier,
        x ≠ y ∧ ((ν.restrict (Q.descendant c.2).carrier).prod
          (ν.restrict (Q.descendant c.2).carrier))
          {z : Space d × Space d | |inner ℝ (‖x-y‖⁻¹ • (x-y)) (z.1-z.2)| ≤ W} ≤
            F*(ν (Q.descendant c.2).carrier)^2)
    (hchild : ∀ c ∈ retainedCellPairs μ ν P Q n G,
      (P.descendant c.1).carrier ×ˢ (Q.descendant c.2).carrier ⊆ H)
    (C : ℝ) :
    ((testedCellDistance μ ν P Q G).prod (testedCellDistance μ ν P Q G))
      {z : ℝ × ℝ | |z.1-z.2| ≤ C*w} ≤
    (((PlanarFalconer.bandOffsets C).card : ℝ≥0∞) *
      ((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) * F) *
      ((testedCellDistance μ ν P Q H).prod (testedCellDistance μ ν P Q H))
        {z : ℝ × ℝ | |z.1-z.2| ≤ (1+4*Real.sqrt d)*(P.side/(2:ℝ)^n)} := by
  let S := retainedCellPairs μ ν P Q n G
  let P' := fun c : List (Fin d → Bool) × List (Fin d → Bool) => P.descendant c.1
  let Q' := fun c : List (Fin d → Bool) × List (Fin d → Bool) => Q.descendant c.2
  let e := fun c => ‖(P' c).center-(Q' c).center‖⁻¹ • ((P' c).center-(Q' c).center)
  have hlen (c) (hc : c ∈ S) : c.1.length = n ∧ c.2.length = n := by
    obtain ⟨hc,_⟩ := Finset.mem_filter.mp hc
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hc
    exact ⟨(mem_cubePaths d n c.1).mp (Finset.mem_filter.mp h₁).1,
      (mem_cubePaths d n c.2).mp (Finset.mem_filter.mp h₂).1⟩
  have hs₁ (c) (hc : c ∈ S) : (P' c).side = P.side/(2:ℝ)^n := by
    dsimp only [P']
    rw [P.descendant_side,(hlen c hc).1]
  have hs₂ (c) (hc : c ∈ S) : (Q' c).side = P.side/(2:ℝ)^n := by
    dsimp only [Q']
    rw [Q.descendant_side,(hlen c hc).2,hQ]
  have hspos (c) (hc : c ∈ S) : 0 < (P' c).side := by rw [hs₁ c hc]; positivity
  have hside (c) (hc : c ∈ S) : (Q' c).side = (P' c).side :=
    (hs₂ c hc).trans (hs₁ c hc).symm
  have hp (c) (hc : c ∈ S) :
      ((ν.restrict (Q' c).carrier).prod (ν.restrict (Q' c).carrier))
        {z : Space d × Space d | |inner ℝ (e c) (z.1-z.2)| ≤ w} ≤
          F*(ν (Q' c).carrier)^2 := by
    obtain ⟨x,hx,y,hy,hxy,hxyproj⟩ := hproj c hc
    apply le_trans _ hxyproj
    exact suffix_witness_projection_transfer ν (P' c) (Q' c) (hspos c hc) (hside c hc)
      hg (hsep c hc) hx hy hxy (by simpa only [hs₁ c hc] using hwidth)
  have hbin := finite_suffix_cell_comparison S μ ν P' Q' e
    (fun c => testedCellDistance μ ν (P' c) (Q' c) G)
    (show 0 ≤ P.side/(2:ℝ)^n by positivity) hw hws hs₁ hs₂
    (fun c _ => testedCellDistance_le μ ν (P' c) (Q' c) G)
    (fun c hc x hx y hy =>
      ((P' c).distance_linearization (Q' c) (hspos c hc) (hside c hc) hg (hsep c hc) hx hy).trans
        (by simpa only [hs₁ c hc] using hsmall)) F hp
  have hcoarse := full_retained_distance_le μ ν P Q n G H hchild
  have hfine := PlanarFalconer.real_bin_shifted_band_bound
    (testedCellDistance μ ν P Q G) (testedCellDistance μ ν P Q G) hw C 0
  simp only [sub_zero,← pow_two] at hfine
  change (PlanarFalconer.binL2Norm
    (∑ c ∈ retainedCellPairs μ ν P Q n G,
      testedCellDistance μ ν (P.descendant c.1) (Q.descendant c.2) G) w)^2 ≤ _ at hbin
  rw [← testedCellDistance_split μ ν P Q n G hG] at hbin
  apply (hfine.trans (mul_le_mul' le_rfl hbin)).trans
  have hh := mul_le_mul' (le_refl
    (((PlanarFalconer.bandOffsets C).card : ℝ≥0∞) *
      ((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) * F))
    (Measure.prod_mono hcoarse hcoarse
      {z : ℝ × ℝ | |z.1-z.2| ≤ (1+4*Real.sqrt d)*(P.side/(2:ℝ)^n)})
  simpa only [mul_assoc,S,P',Q'] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PositiveTests
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full-cell projection estimates extracted from actual retained pairs -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem DyadicCube.mem_ancestor (Q : DyadicCube d) (P : List (Fin d → Bool))
    (g : ℕ) {x : Space d} (hx : x ∈ (Q.descendant P).carrier) :
    x ∈ (Q.descendant (P.take g)).carrier := by
  rw [← List.take_append_drop g P, Q.descendant_append] at hx
  exact (Q.descendant (P.take g)).descendant_subset (P.drop g) hx

theorem descriptorEndpointGood_reached (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    (P : List (Fin d → Bool)) (hg : descriptorAnchor b ≤ P.length)
    {x y : Space d} (hx : x ∈ (Q.descendant P).carrier)
    (hy : y ∈ (Q.descendant P).carrier) (w : Sphere d) :
    (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b ↔
      (y,w) ∈ descriptorEndpointGood Q ρ m N σ J i b := by
  have hl : (P.take (descriptorAnchor b)).length = descriptorAnchor b := by
    rw [List.length_take, Nat.min_eq_left hg]
  rw [descriptorEndpointGood_on_cell Q ρ m N σ J i b _ hl
    (Q.mem_ancestor P _ hx), descriptorEndpointGood_on_cell Q ρ m N σ J i b _ hl
    (Q.mem_ancestor P _ hy)]

theorem retained_projection_test (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i a p t : ℕ) (hap : a ≤ p)
    (X Y : List (Fin d → Bool)) (hY : Y.length = a)
    (B : Finset PolicyDescriptor) (hb : PolicyDescriptor.projection p t ∈ B)
    (G : Set (Space d × Space d))
    (hG : G ⊆ descriptorPairTests w₀ Q ρ m N σ J i B)
    (hne : ∀ x ∈ (Q.descendant X).carrier, ∀ y ∈ (Q.descendant Y).carrier, x ≠ y) :
    ∀ c ∈ retainedCellPairs ρ ρ (Q.descendant X) (Q.descendant Y) (p-a) G,
      ∃ x ∈ ((Q.descendant X).descendant c.1).carrier,
        ∃ y ∈ ((Q.descendant Y).descendant c.2).carrier, x ≠ y ∧
        ((ρ.restrict ((Q.descendant Y).descendant c.2).carrier).prod
          (ρ.restrict ((Q.descendant Y).descendant c.2).carrier))
          {z : Space d × Space d |
            |inner ℝ (‖x-y‖⁻¹ • (x-y)) (z.1-z.2)| ≤ angularTestWidth N σ J i t} ≤
          ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
            Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ)) *
              (ρ ((Q.descendant Y).descendant c.2).carrier)^2 := by
  intro c hc
  obtain ⟨hocc,x,hx,y,hy,hxy⟩ := Finset.mem_filter.mp hc
  have hlen : c.2.length = p-a :=
    (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp (Finset.mem_product.mp hocc).2).1
  have hanchor : (Y++c.2).length = descriptorAnchor (.projection p t) := by
    simp only [List.length_append,hY,hlen,descriptorAnchor]
    omega
  have hy' : y ∈ (Q.descendant (Y++c.2)).carrier := by
    simpa only [Q.descendant_append] using hy
  have hgood := ((hG hxy) (.projection p t) hb).2
  have htest := (descriptorEndpointGood_on_cell Q ρ m N σ J i (.projection p t)
    (Y++c.2) hanchor hy' (normalizeToSphere w₀ (x-y))).mp hgood
  have hbound := descriptor_projection_original_bound Q ρ m N σ J i p t
    (Y++c.2) (normalizeToSphere w₀ (x-y)) htest
  have hneq : x ≠ y := hne x ((Q.descendant X).descendant_subset c.1 hx)
    y ((Q.descendant Y).descendant_subset c.2 hy)
  refine ⟨x,hx,y,hy,hneq,?_⟩
  simpa only [Q.descendant_append,normalizeToSphere_coe_of_ne w₀
    (sub_ne_zero.mpr hneq),NormedSpace.normalize] using hbound

theorem DyadicCube.pair_ne_of_separation (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g : ℝ} (hsep : g ≤ ‖P.center-Q.center‖)
    (hsmall : 2*Real.sqrt d*P.side < g)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) : x ≠ y := by
  have hQp : 0 < Q.side := by rwa [hQ]
  have h₁ := P.dist_le hP.le hx (P.center_mem hP)
  have h₂ := Q.dist_le hQp.le hy (Q.center_mem hQp)
  rw [hQ] at h₂
  have hδ : ‖(x-y)-(P.center-Q.center)‖ ≤ 2*Real.sqrt d*P.side := by
    simpa only [dist_eq_norm,two_mul,mul_add,add_mul] using
      pair_displacement_bound x y P.center Q.center h₁ h₂
  intro he
  rw [he,sub_self,zero_sub,norm_neg] at hδ
  linarith

theorem DyadicCube.pair_sphere_direction_dist (w₀ : Sphere d) (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g : ℝ} (hg : 0 < g) (hsep : g ≤ ‖P.center-Q.center‖)
    (hsmall : 2*Real.sqrt d*P.side < g)
    {x y x' y' : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier)
    (hx' : x' ∈ P.carrier) (hy' : y' ∈ Q.carrier) :
    dist (normalizeToSphere w₀ (x-y)) (normalizeToSphere w₀ (x'-y')) ≤
      8*Real.sqrt d*P.side/g := by
  have hxy := P.pair_ne_of_separation Q hP hQ hsep hsmall hx hy
  have hxy' := P.pair_ne_of_separation Q hP hQ hsep hsmall hx' hy'
  rw [Subtype.dist_eq,dist_eq_norm,normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hxy),
    normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hxy')]
  change ‖‖x-y‖⁻¹ • (x-y)-‖x'-y'‖⁻¹ • (x'-y')‖ ≤ _
  calc
    _ ≤ ‖‖x-y‖⁻¹ • (x-y)-‖P.center-Q.center‖⁻¹ • (P.center-Q.center)‖ +
        ‖‖P.center-Q.center‖⁻¹ • (P.center-Q.center)-‖x'-y'‖⁻¹ • (x'-y')‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 4*Real.sqrt d*P.side/g+4*Real.sqrt d*P.side/g :=
      add_le_add (P.pair_direction_approximation Q hP hQ hg hsep hx hy hxy)
        (by simpa only [norm_sub_rev] using
          P.pair_direction_approximation Q hP hQ hg hsep hx' hy' hxy')
    _ = _ := by ring

theorem uniform_full_cell_tests_of_witness {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (B : Finset PolicyDescriptor), (∀ b ∈ B, descriptorValid N b) →
      ∀ (p : ℕ) (X Y : List (Fin d → Bool)), X.length = p → Y.length = p →
      (∀ b ∈ B, descriptorAnchor b ≤ p) →
      ∀ (g : ℝ), 0 < g → g ≤ ‖(Q.descendant X).center-(Q.descendant Y).center‖ →
      2*Real.sqrt d*(Q.descendant X).side < g →
      (∀ b ∈ B, 8*Real.sqrt d*(Q.descendant X).side/g ≤
        angularTestRadius N σ (descriptorLength b)) →
      ∀ (i : ℕ) (w₀ : Sphere d) (x y : Space d),
      x ∈ (Q.descendant X).carrier → y ∈ (Q.descendant Y).carrier →
      (x,y) ∈ descriptorPairTests w₀ Q ρ m N σ J i B →
      (Q.descendant X).carrier ×ˢ (Q.descendant Y).carrier ⊆
        descriptorPairTests w₀ Q ρ m N σ J (i+1) B := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorEndpointGood_buffer (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m B hB p X Y hX hY hanchor g hg hsep hsmall hrad i w₀ x y hx hy hgood
  have hQp : 0 < Q.side := by rw [hQ]; norm_num
  have hside : (Q.descendant Y).side = (Q.descendant X).side := by
    rw [Q.descendant_side,Q.descendant_side,hX,hY]
  intro z hz b hb
  have hdist := (Q.descendant X).pair_sphere_direction_dist w₀ (Q.descendant Y)
    (Q.descendant_side_pos hQp X) hside hg hsep hsmall hx hy hz.1 hz.2
  constructor
  · apply h₀ N hN Q hQ ρ m b (hB b hb) i z.1
      (normalizeToSphere w₀ (x-y)) (normalizeToSphere w₀ (z.1-z.2))
      (hdist.trans (hrad b hb))
    exact (descriptorEndpointGood_reached Q ρ m N σ J i b X
      (by rw [hX]; exact hanchor b hb) hx hz.1 _).mp (hgood b hb).1
  · apply h₀ N hN Q hQ ρ m b (hB b hb) i z.2
      (normalizeToSphere w₀ (x-y)) (normalizeToSphere w₀ (z.1-z.2))
      (hdist.trans (hrad b hb))
    exact (descriptorEndpointGood_reached Q ρ m N σ J i b Y
      (by rw [hY]; exact hanchor b hb) hy hz.2 _).mp (hgood b hb).2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SuffixScales
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The suffix scale hypotheses in the manuscript's separated geometry -/

namespace Falconer
open Set MeasureTheory

theorem sqrt_dimension_le (d : ℕ) : Real.sqrt (d : ℝ) ≤ (d : ℝ)+1 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (d : ℝ),Nat.cast_nonneg (α := ℝ) d]

theorem dyadic_side_le_radius {σ : ℝ} (hσ : 0 ≤ σ) (N L : ℕ) :
    1/(2:ℝ)^L ≤ angularTestRadius N σ L := by
  apply le_min
  · exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  · exact le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity))

theorem suffix_linearization_scale (d : ℕ) {a p t : ℕ} (hapt : a+t ≤ 2*p) :
    2*(d:ℝ)*(1/(2:ℝ)^p)^2/(100*((d:ℝ)+1)/(2:ℝ)^a) ≤ 1/(2:ℝ)^t := by
  have hc : 2*(d:ℝ)/(100*((d:ℝ)+1)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  calc
    _ = (2*(d:ℝ)/(100*((d:ℝ)+1))) *
        ((1/(2:ℝ)^p)^2/(1/(2:ℝ)^a)) := by field_simp
    _ ≤ 1*((1/(2:ℝ)^p)^2/(1/(2:ℝ)^a)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := by simpa only [one_mul] using dyadic_suffix_error hapt

theorem suffix_direction_small (d : ℕ) {a p : ℕ} (hap : a ≤ p) :
    2*Real.sqrt d*(1/(2:ℝ)^p) < 100*((d:ℝ)+1)/(2:ℝ)^a := by
  calc
    _ ≤ 2*((d:ℝ)+1)*(1/(2:ℝ)^a) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (sqrt_dimension_le d) (by norm_num))
        (dyadic_side_mono hap) (by positivity) (by positivity)
    _ < 100*((d:ℝ)+1)/(2:ℝ)^a := by
      have hp : 0 < ((d:ℝ)+1)/(2:ℝ)^a := by positivity
      calc
        _ = 2*(((d:ℝ)+1)/(2:ℝ)^a) := by ring
        _ < 100*(((d:ℝ)+1)/(2:ℝ)^a) := mul_lt_mul_of_pos_right (by norm_num) hp
        _ = _ := by ring

theorem suffix_direction_buffer (d : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (N : ℕ) {a p L : ℕ} (hap : a ≤ p) (hL : L ≤ p-a) :
    8*Real.sqrt d*(1/(2:ℝ)^p)/(100*((d:ℝ)+1)/(2:ℝ)^a) ≤
      angularTestRadius N σ L := by
  have hc : 8*Real.sqrt d/(100*((d:ℝ)+1)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by
      have hs := sqrt_dimension_le d
      nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have hp : (2:ℝ)^a*(2:ℝ)^(p-a) = (2:ℝ)^p := by
    rw [← pow_add,Nat.add_sub_of_le hap]
  calc
    _ = (8*Real.sqrt d/(100*((d:ℝ)+1)))*(1/(2:ℝ)^(p-a)) := by
      rw [← hp]
      field_simp
    _ ≤ 1/(2:ℝ)^(p-a) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc
        (by positivity : 0 ≤ 1/(2:ℝ)^(p-a))
    _ ≤ 1/(2:ℝ)^L := dyadic_side_mono hL
    _ ≤ _ := dyadic_side_le_radius hσ N L

theorem uniform_suffix_witness_width (d : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p t : ℕ, a+t ≤ 2*p → ∀ i ≤ J,
      1/(2:ℝ)^t+4*(d:ℝ)*(1/(2:ℝ)^p)^2/(100*((d:ℝ)+1)/(2:ℝ)^a) ≤
        angularTestWidth N σ J i t := by
  obtain ⟨N₀,h₀⟩ := uniform_suffix_test_width hσ hJ 1
    (4*(d:ℝ)/(100*((d:ℝ)+1))) (by positivity)
  refine ⟨N₀,?_⟩
  intro N hN a p t hapt i hi
  convert h₀ N hN a p t hapt i hi using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

theorem DyadicCube.separated_pairs_lower {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    (hsep : 125*((d:ℝ)+1)*P.side ≤ ‖P.center-Q.center‖)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    100*((d:ℝ)+1)*P.side ≤ ‖x-y‖ := by
  have hQp : 0 < Q.side := by rwa [hQ]
  have h₁ := P.dist_le hP.le hx (P.center_mem hP)
  have h₂ := Q.dist_le hQp.le hy (Q.center_mem hQp)
  rw [hQ] at h₂
  have hδ : ‖(x-y)-(P.center-Q.center)‖ ≤ 2*Real.sqrt d*P.side := by
    simpa only [dist_eq_norm,two_mul,mul_add,add_mul] using
      pair_displacement_bound x y P.center Q.center h₁ h₂
  have hnorm : ‖P.center-Q.center‖ ≤ ‖x-y‖+‖(x-y)-(P.center-Q.center)‖ := by
    have he : P.center-Q.center = (x-y)-((x-y)-(P.center-Q.center)) := by abel
    calc
      _ = ‖(x-y)-((x-y)-(P.center-Q.center))‖ := congrArg norm he
      _ ≤ _ := norm_sub_le _ _
  have hs := mul_le_mul_of_nonneg_right (sqrt_dimension_le d) hP.le
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RegularizedCellCounts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual descendant counts for a single regularized profile -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem RegularizedProfileData.cell_mass_upper {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a : ℕ} (ha : a ≤ N) (X : CellPath d) (hX : X.length = a) :
    (ρ (Q.descendant X).carrier).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam-m ((a:ℝ)/N)) := by
  by_cases hp : 0 < ρ (Q.descendant X).carrier
  · exact (h.cells a ha X hX hp).2.trans_eq
      (Real.rpow_add (by positivity) _ _).symm
  · have hz : ρ (Q.descendant X).carrier = 0 := le_antisymm (le_of_not_gt hp) bot_le
    rw [hz,ENNReal.toReal_zero]
    positivity

theorem RegularizedProfileData.descendant_count {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X : CellPath d) (hX : X.length = a) :
    (((Q.descendant X).occupiedPaths ρ (p-a)).card : ℝ) ≤
      ((2:ℝ)^N)^(m ((p:ℝ)/N)-m ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) := by
  let := h.probability
  let R := (2:ℝ)^N
  let ℓ := ((d:ℝ)+1)*lam
  let lo := R^(-ℓ-m ((p:ℝ)/N))
  let S := (Q.descendant X).occupiedPaths ρ (p-a)
  have hlo : 0 < lo := by dsimp [lo,R]; positivity
  have hmass (z : CellPath d) (hz : z ∈ S) :
      lo ≤ (ρ ((Q.descendant X).descendant z).carrier).toReal := by
    have hz' : z ∈ cubePaths d (p-a) ∧
        0 < ρ ((Q.descendant X).descendant z).carrier := by
      simpa only [S,DyadicCube.occupiedPaths,Finset.mem_filter] using hz
    obtain ⟨hz,hpos⟩ := hz'
    have hlen : (X++z).length = p := by
      simp only [List.length_append,hX,(mem_cubePaths _ _ _).mp hz]
      omega
    have hh := (h.cells p hp (X++z) hlen
      (by simpa only [Q.descendant_append] using hpos)).1
    simpa only [Q.descendant_append,lo,R,ℓ,sub_eq_add_neg,neg_mul,
      Real.rpow_add (by positivity : 0 < (2:ℝ)^N)] using hh
  have he : ρ (Q.descendant X).carrier =
      ∑ z ∈ S, ρ ((Q.descendant X).descendant z).carrier := by
    have hh := congrArg (fun ν : Measure (Space d) => ν univ)
      ((Q.descendant X).restrict_occupiedPaths ρ (p-a))
    simpa only [Measure.restrict_apply_univ,Measure.finsetSum_apply,S] using hh
  have hr : (ρ (Q.descendant X).carrier).toReal =
      ∑ z ∈ S, (ρ ((Q.descendant X).descendant z).carrier).toReal := by
    rw [he,ENNReal.toReal_sum]
    intro z _
    exact measure_ne_top ρ _
  have hc : (S.card:ℝ)*lo ≤ R^(ℓ-m ((a:ℝ)/N)) := by
    calc
      _ = ∑ _z ∈ S, lo := by simp
      _ ≤ ∑ z ∈ S, (ρ ((Q.descendant X).descendant z).carrier).toReal :=
        Finset.sum_le_sum hmass
      _ = (ρ (Q.descendant X).carrier).toReal := hr.symm
      _ ≤ _ := h.cell_mass_upper (hap.trans hp) X hX
  apply (le_div_iff₀ hlo).mpr at hc
  apply hc.trans_eq
  dsimp only [lo,R,ℓ]
  rw [← Real.rpow_sub (by positivity)]
  congr 1
  ring

theorem RegularizedProfileData.pair_count {Q : DyadicCube d}
    {ρ : Measure (Space d)} {N : ℕ} {s lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N s lam m)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : CellPath d) (hX : X.length = a) (hY : Y.length = a) :
    ((((Q.descendant X).occupiedPaths ρ (p-a)) ×ˢ
      ((Q.descendant Y).occupiedPaths ρ (p-a))).card : ℝ) ≤
      ((2:ℝ)^N)^(2*(m ((p:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  rw [Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ ((2:ℝ)^N)^(m ((p:ℝ)/N)-m ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) *
        ((2:ℝ)^N)^(m ((p:ℝ)/N)-m ((a:ℝ)/N)+2*((d:ℝ)+1)*lam) :=
      mul_le_mul (h.descendant_count hap hp X hX) (h.descendant_count hap hp Y hY)
        (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_NearGraph
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The near part of the independent angular energy

Nearness is imposed on both actual center displacements. Integer grid
packing gives a dimensional degree bound; positive Schur integration then
controls this part by the sum of the original child energies. No angular
localization or separation of the two parent cells is used.
-/

namespace Falconer
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem DyadicCube.neighbor_card {d n L : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (A : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (a : List (Fin d → Bool)) (ha : a.length = n)
    {τ : ℝ} (hL : τ*((2:ℝ)^n/Q.side) ≤ L) :
    (A.filter (fun p => ‖(Q.descendant p).center-(Q.descendant a).center‖ ≤ τ)).card ≤
      (2*L+1)^d := by
  classical
  let T := A.filter (fun p => ‖(Q.descendant p).center-(Q.descendant a).center‖ ≤ τ)
  have hinj : Set.InjOn dyadicCode (↑T : Set (List (Fin d → Bool))) := by
    intro p hp q hq he
    exact dyadicCode_injective_at_depth (hA p (Finset.mem_filter.mp hp).1)
      (hA q (Finset.mem_filter.mp hq).1) he
  rw [← Finset.card_image_of_injOn hinj]
  apply grid_ball_card (show 0 < (2:ℝ)^n/Q.side by positivity) hL _ (dyadicCode a)
  intro z hz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hp,hnear⟩ := Finset.mem_filter.mp hp
  rwa [← Q.center_sub_eq_grid_sub p a (hA p hp) ha]

theorem nearDyadicEdge_symm {d : ℕ} (Q₁ Q₂ : DyadicCube d) (τ : ℝ)
    (row col : List (Fin d → Bool) × List (Fin d → Bool)) :
    nearDyadicEdge Q₁ Q₂ τ row col ↔ nearDyadicEdge Q₁ Q₂ τ col row := by
  simp only [nearDyadicEdge,norm_sub_rev]

theorem nearDyadic_degree {d n L : ℕ} (Q₁ Q₂ : DyadicCube d)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (A B : Finset (List (Fin d → Bool)))
    (hA : ∀ p ∈ A, p.length = n) (hB : ∀ p ∈ B, p.length = n)
    {τ : ℝ} (hL₁ : τ*((2:ℝ)^n/Q₁.side) ≤ L)
    (hL₂ : τ*((2:ℝ)^n/Q₂.side) ≤ L)
    (row : List (Fin d → Bool) × List (Fin d → Bool)) (hr : row ∈ A ×ˢ B) :
    ((A ×ˢ B).filter (nearDyadicEdge Q₁ Q₂ τ row)).card ≤ (2*L+1)^(2*d) := by
  have heq : (A ×ˢ B).filter (nearDyadicEdge Q₁ Q₂ τ row) =
      (A.filter (fun p => ‖(Q₁.descendant p).center-(Q₁.descendant row.1).center‖ ≤ τ)) ×ˢ
      (B.filter (fun p => ‖(Q₂.descendant p).center-(Q₂.descendant row.2).center‖ ≤ τ)) := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_product,nearDyadicEdge]
    tauto
  rw [heq,Finset.card_product]
  calc
    _ ≤ (2*L+1)^d*(2*L+1)^d := Nat.mul_le_mul
      (Q₁.neighbor_card hQ₁ A hA row.1 (hA _ (Finset.mem_product.mp hr).1) hL₁)
      (Q₂.neighbor_card hQ₂ B hB row.2 (hB _ (Finset.mem_product.mp hr).2) hL₂)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- The near contribution after exact model-mass splitting. This is the
analytic near reduction before the profile normalization. -/
theorem dyadic_near_energy_bound {d n L : ℕ} (Q₁ Q₂ : DyadicCube d)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (M₁ M₂ : ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C)
    {τ : ℝ} (hL₁ : τ*((2:ℝ)^n/Q₁.side) ≤ L)
    (hL₂ : τ*((2:ℝ)^n/Q₂.side) ≤ L)
    (a p v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    (2:ℝ)^((d:ℝ)*(v-a)) *
      ‖∫ z, ∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        ∑ col ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
          if nearDyadicEdge Q₁ Q₂ τ row col then
            dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c row z *
              star (dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c col z) else 0
        ∂angularProductMeasure d v Ψ‖ ≤
    (2:ℝ)^((d:ℝ)*(p-a)) * ((2*L+1)^(2*d):ℕ) *
      ∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) M₁ b z.1 z.2)
          (fun z => endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) M₂ c z.1 z.2) := by
  let S := Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n
  let U := fun row : List (Fin d → Bool) × List (Fin d → Bool) => fun z : ℝ × Sphere d =>
    endpointTransform (μ.restrict (Q₁.descendant row.1).carrier) M₁ b z.1 z.2
  let V := fun row : List (Fin d → Bool) × List (Fin d → Bool) => fun z : ℝ × Sphere d =>
    endpointTransform (ν.restrict (Q₂.descendant row.2).carrier) M₂ c z.1 z.2
  let bound₁ := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    B*(μ.restrict (Q₁.descendant row.1).carrier).real Set.univ/M₁
  let bound₂ := fun row : List (Fin d → Bool) × List (Fin d → Bool) =>
    C*(ν.restrict (Q₂.descendant row.2).carrier).real Set.univ/M₂
  have hdg (row : List (Fin d → Bool) × List (Fin d → Bool)) (hr : row ∈ S) :
      (S.filter (nearDyadicEdge Q₁ Q₂ τ row)).card ≤ (2*L+1)^(2*d) :=
    nearDyadic_degree Q₁ Q₂ hQ₁ hQ₂ _ _
      (fun q hq => (mem_cubePaths d n q).mp (Finset.mem_filter.mp hq).1)
      (fun q hq => (mem_cubePaths d n q).mp (Finset.mem_filter.mp hq).1) hL₁ hL₂ row hr
  have hcol (col : List (Fin d → Bool) × List (Fin d → Bool)) (hc : col ∈ S) :
      (S.filter (fun row => nearDyadicEdge Q₁ Q₂ τ row col)).card ≤ (2*L+1)^(2*d) := by
    simpa only [nearDyadicEdge_symm Q₁ Q₂ τ _ col] using hdg col hc
  have hs := independentAngularEnergy_graph_schur p v Ψ S ({()} : Finset Unit)
    (fun _ => nearDyadicEdge Q₁ Q₂ τ) U V
    (fun _ _ => measurable_endpointTransform _ _ _ hb)
    (fun _ _ => measurable_endpointTransform _ _ _ hc)
    bound₁ bound₂ (fun _ _ => by dsimp [bound₁]; positivity)
    (fun _ _ => by dsimp [bound₂]; positivity)
    (fun _ _ z => endpointTransform_norm_le _ hM₁ b hbB z.1 z.2)
    (fun _ _ z => endpointTransform_norm_le _ hM₂ c hcC z.1 z.2)
    (fun _ _ => 1) ((2*L+1)^(2*d):ℕ)
    (by intros; norm_num) (by intros; simp)
    (fun _ _ row hr => by exact_mod_cast hdg row hr)
    (fun _ _ col hc => by exact_mod_cast hcol col hc)
  simp only [Finset.sum_singleton,one_smul] at hs
  have hexp : (2:ℝ)^((d:ℝ)*(v-a)) =
      (2:ℝ)^((d:ℝ)*(p-a))*(2:ℝ)^((d:ℝ)*(v-p)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  rw [hexp]
  simpa only [mul_assoc,S,U,V,dyadicPairTransform,angularProductMeasure] using
    mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg (by norm_num) ((d:ℝ)*(p-a)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileNear
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized near reduction for the actual regularized profile

The child energies retain the original endpoint symbols. No separation of
the parent cells is imposed; the near relation is on their two internal
center displacements, as in the manuscript.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem profile_near_prefactor {N : ℕ} (hN : 0 < N)
    (d : ℕ) (m : ℝ → ℝ) (a p : ℕ) (lam : ℝ) :
    (profileModelMass m N p/profileModelMass m N a)^4 *
      (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) *
      ((2:ℝ)^N)^(2*(m ((p:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) =
    ((2:ℝ)^N)^(-2*((m ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
      (m ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hr : (profileModelMass m N p/profileModelMass m N a)^4 =
      ((2:ℝ)^N)^(-4*(m ((p:ℝ)/N)-m ((a:ℝ)/N))) := by
    unfold profileModelMass
    rw [← Real.rpow_sub hR,← Real.rpow_natCast,← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [hr,← dyadic_rpow_change_base hN ((d:ℝ)*((p:ℝ)-a)),
    ← Real.rpow_add hR,← Real.rpow_add hR]
  congr 1
  ring

theorem profile_near_reduction (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C E : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C)
    (hchild : ∀ row ∈ (Q.descendant X).occupiedPaths ρ (p-a) ×ˢ
        (Q.descendant Y).occupiedPaths ρ (p-a),
      independentAngularEnergy p v Ψ
        (fun z => endpointTransform
          (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
          (profileModelMass m N p) b z.1 z.2)
        (fun z => endpointTransform
          (ρ.restrict ((Q.descendant Y).descendant row.2).carrier)
          (profileModelMass m N p) c z.1 z.2) ≤ E) :
    profileNearEnergy (Q.descendant X) (Q.descendant Y) ρ m N a p v Ψ b c ≤
      ((2*(10*(d+1))+1)^(2*d):ℕ) *
      ((2:ℝ)^N)^(-2*((m ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
        (m ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam)*E := by
  let := hreg.probability
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hside (Z : List (Fin d → Bool)) (hZ : Z.length = a) :
      (Q.descendant Z).side = 1/(2:ℝ)^a := by rw [Q.descendant_side,hZ,hQ]
  have hgeom (Z : List (Fin d → Bool)) (hZ : Z.length = a) :
      (10*((d:ℝ)+1)/(2:ℝ)^p)*((2:ℝ)^(p-a)/(Q.descendant Z).side) ≤
        (10*(d+1):ℕ) := by
    have he : (2:ℝ)^a*(2:ℝ)^(p-a) = (2:ℝ)^p := by
      rw [← pow_add,Nat.add_sub_of_le hap]
    rw [hside Z hZ]
    push_cast
    apply le_of_eq
    calc
      _ = 10*((d:ℝ)+1)*((2:ℝ)^a*(2:ℝ)^(p-a))/(2:ℝ)^p := by
        field_simp
      _ = _ := by rw [he]; field_simp
  have hM : 0 < profileModelMass m N p := by unfold profileModelMass; positivity
  have hn := dyadic_near_energy_bound (Q.descendant X) (Q.descendant Y)
    (Q.descendant_side_pos hQpos X) (Q.descendant_side_pos hQpos Y)
    ρ ρ (profileModelMass m N p) (profileModelMass m N p) hM hM b c hb hc
    hB hC hbB hcC (hgeom X hX) (hgeom Y hY) a p v Ψ
  have hs := Finset.sum_le_sum hchild
  rw [Finset.sum_const,nsmul_eq_mul] at hs
  have hrows := hreg.pair_count hap hp X Y hX hY
  have hsum := hs.trans (mul_le_mul_of_nonneg_right hrows hE)
  unfold profileNearEnergy
  rw [mul_assoc]
  apply (mul_le_mul_of_nonneg_left hn (by positivity)).trans
  calc
    _ = ((profileModelMass m N p/profileModelMass m N a)^4 *
        (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) * ((2*(10*(d+1))+1)^(2*d):ℕ)) *
        ∑ row ∈ (Q.descendant X).occupiedPaths ρ (p-a) ×ˢ
          (Q.descendant Y).occupiedPaths ρ (p-a),
          independentAngularEnergy p v Ψ
            (fun z => endpointTransform
              (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
              (profileModelMass m N p) b z.1 z.2)
            (fun z => endpointTransform
              (ρ.restrict ((Q.descendant Y).descendant row.2).carrier)
              (profileModelMass m N p) c z.1 z.2) := by ring
    _ ≤ ((profileModelMass m N p/profileModelMass m N a)^4 *
        (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) * ((2*(10*(d+1))+1)^(2*d):ℕ)) *
        (((2:ℝ)^N)^(2*(m ((p:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam)*E) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((2*(10*(d+1))+1)^(2*d):ℕ) *
        ((profileModelMass m N p/profileModelMass m N a)^4 *
          (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) *
          ((2:ℝ)^N)^(2*(m ((p:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam))*E := by ring
    _ = _ := by rw [profile_near_prefactor hN]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularEnvelopeGraph
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual profile graph estimate on the admissible energy envelope

Restriction to a child is implemented by the existing spatial cell symbol.
The original restricted endpoint integral is unchanged, and the support
condition is propagated explicitly to the child's good set.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem finiteEnvelopeMaximum_nonneg {ι : Type*} (S : Finset ι) (F : ι → ℝ) :
    0 ≤ finiteEnvelopeMaximum S F :=
  le_csSup ((S.finite_toSet.image F).insert 0).bddAbove (Or.inl rfl)

theorem finiteEnvelopeMaximum_le {ι : Type*} (S : Finset ι) (F : ι → ℝ)
    {H : ℝ} (hH : 0 ≤ H) (h : ∀ i ∈ S, F i ≤ H) :
    finiteEnvelopeMaximum S F ≤ H := by
  change sSup (insert (0:ℝ) (F '' (S : Set ι))) ≤ H
  apply csSup_le (show (insert (0:ℝ) (F '' (S : Set ι))).Nonempty from ⟨0,Or.inl rfl⟩)
  intro x hx
  rcases hx with rfl | ⟨i,hi,rfl⟩
  · exact hH
  · exact h i hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ReachedMasks
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Removing reached masks after passing to positive energy

A reached anchor mask is spatially constant on its descendant cell. It
can therefore be taken outside that endpoint transform. Its bounded
angular factor is removed only from the positive independent energy.
-/

namespace Falconer
open Set MeasureTheory

theorem endpointTransform_angular_factor {d : ℕ} (ρ : Measure (Space d))
    (M : ℝ) (b : Space d → Sphere d → ℂ) (m : Sphere d → ℂ)
    (r : ℝ) (w : Sphere d) :
    endpointTransform ρ M (fun x w => m w * b x w) r w =
      m w * endpointTransform ρ M b r w := by
  unfold endpointTransform
  have he : (fun x => Complex.exp (Complex.I * (r : ℂ) *
      (inner ℝ (w : Space d) x : ℂ)) * (m w * b x w)) =
      fun x => m w * (Complex.exp (Complex.I * (r : ℂ) *
        (inner ℝ (w : Space d) x : ℂ)) * b x w) := by
    funext x
    ring
  rw [he, integral_const_mul, mul_smul_comm]

theorem sphereMoment_factor_le {d : ℕ} (U : ℝ × Sphere d → ℂ)
    (hU : Measurable U) (m : Sphere d → ℂ) (hm : Measurable m)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmB : ∀ w, ‖m w‖ ≤ B) (hUC : ∀ z, ‖U z‖ ≤ C) (r : ℝ) :
    sphereMoment (fun z => m z.2 * U z) r ≤ B^2 * sphereMoment U r := by
  have hmU : Measurable (fun w => m w * U (r,w)) :=
    hm.mul (hU.comp (measurable_const.prodMk measurable_id))
  have hbound (w : Sphere d) : ‖m w * U (r,w)‖ ≤ B*C := by
    rw [norm_mul]
    exact mul_le_mul (hmB w) (hUC _) (norm_nonneg _) hB
  have hleft := sphere_norm_square_integrable _ hmU (mul_nonneg hB hC) hbound
  have hright := (sphere_norm_square_integrable (fun w => U (r,w))
    (hU.comp (measurable_const.prodMk measurable_id)) hC (fun w => hUC _)).const_mul (B^2)
  change (∫ w, ‖m w * U (r,w)‖^2 ∂sphereMeasure d) ≤
    B^2 * (∫ w, ‖U (r,w)‖^2 ∂sphereMeasure d)
  rw [← integral_const_mul]
  apply integral_mono hleft hright
  intro w
  change ‖m w * U (r,w)‖^2 ≤ B^2 * ‖U (r,w)‖^2
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (norm_nonneg _) hB).mpr (hmB w)) (sq_nonneg _)

/-- Removing two reached angular factors costs only their squared sup
norms. Every unreached spatial mask remains inside its endpoint transform. -/
theorem independentAngularEnergy_remove_factors {d : ℕ} (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (U V : ℝ × Sphere d → ℂ) (hU : Measurable U) (hV : Measurable V)
    (m n : Sphere d → ℂ) (hm : Measurable m) (hn : Measurable n)
    {B C D E : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hmB : ∀ w, ‖m w‖ ≤ B) (hnC : ∀ w, ‖n w‖ ≤ C)
    (hUD : ∀ z, ‖U z‖ ≤ D) (hVE : ∀ z, ‖V z‖ ≤ E) :
    independentAngularEnergy a v Ψ (fun z => m z.2 * U z) (fun z => n z.2 * V z) ≤
      (B^2*C^2) * independentAngularEnergy a v Ψ U V := by
  have hUm : Measurable (fun z : ℝ × Sphere d => m z.2 * U z) :=
    (hm.comp measurable_snd).mul hU
  have hVn : Measurable (fun z : ℝ × Sphere d => n z.2 * V z) :=
    (hn.comp measurable_snd).mul hV
  have hUmB (z : ℝ × Sphere d) : ‖m z.2 * U z‖ ≤ B*D := by
    rw [norm_mul]
    exact mul_le_mul (hmB _) (hUD _) (norm_nonneg _) hB
  have hVnC (z : ℝ × Sphere d) : ‖n z.2 * V z‖ ≤ C*E := by
    rw [norm_mul]
    exact mul_le_mul (hnC _) (hVE _) (norm_nonneg _) hC
  have hi := independentAngularIntegrand_integrable v Ψ _ _ hUm hVn
    (mul_nonneg hB hD) (mul_nonneg hC hE) hUmB hVnC
  have hj := (independentAngularIntegrand_integrable v Ψ U V hU hV hD hE hUD hVE).const_mul
    (B^2*C^2)
  have hpoint (r : ℝ) :
      sphereMoment (fun z => m z.2 * U z) r * sphereMoment (fun z => n z.2 * V z) r ≤
        (B^2*C^2) * (sphereMoment U r * sphereMoment V r) := by
    calc
      _ ≤ (B^2 * sphereMoment U r) * (C^2 * sphereMoment V r) :=
        mul_le_mul (sphereMoment_factor_le U hU m hm hB hD hmB hUD r)
          (sphereMoment_factor_le V hV n hn hC hE hnC hVE r)
          (sphereMoment_nonneg _ _) (mul_nonneg (sq_nonneg _) (sphereMoment_nonneg _ _))
      _ = _ := by ring
  unfold independentAngularEnergy
  calc
    _ ≤ (2 : ℝ)^((d : ℝ)*(v-a)) *
        ∫ r, (B^2*C^2) * (sphereMoment U r * sphereMoment V r)
          ∂PlanarFalconer.sourceAngularShellMeasure v Ψ :=
      mul_le_mul_of_nonneg_left (integral_mono hi hj hpoint) (by positivity)
    _ = _ := by rw [integral_const_mul]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ReachedMaskJets
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized mask derivatives at reached anchors

Reached masks agree as ambient functions throughout a child cell. All their
ambient jets therefore agree too. Radius normalization makes each fixed
order uniformly bounded before any scale or descriptor is selected.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff

theorem descriptorAmbientMask_reached_eq {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (X : List (Fin d → Bool))
    (hb : descriptorAnchor b ≤ X.length) {x : Space d}
    (hx : x ∈ (Q.descendant X).carrier) :
    descriptorAmbientMask Q ρ m N σ J i b S x =
      descriptorAmbientMask Q ρ m N σ J i b S (Q.descendant X).center := by
  let p := X.take (descriptorAnchor b)
  let q := X.drop (descriptorAnchor b)
  have hp : p.length = descriptorAnchor b := by
    simp only [p,List.length_take,Nat.min_eq_left hb]
  have hprefix (y : Space d) (hy : y ∈ (Q.descendant X).carrier) :
      y ∈ (Q.descendant p).carrier := by
    have he : X = p++q := (List.take_append_drop _ _).symm
    rw [he,Q.descendant_append] at hy
    exact (Q.descendant p).descendant_subset q hy
  funext z
  rw [descriptorAmbientMask_on_cell Q ρ m N σ J i b S p hp (hprefix x hx),
    descriptorAmbientMask_on_cell Q ρ m N σ J i b S p hp
      (hprefix _ ((Q.descendant X).center_mem (Q.descendant_side_pos hQ X)))]

theorem normalizedDescriptorJet_reached {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ) (v : Fin k → Space d)
    (X : List (Fin d → Bool)) (hb : descriptorAnchor b ≤ X.length) {x : Space d}
    (hx : x ∈ (Q.descendant X).carrier) (w : Sphere d) :
    normalizedDescriptorJet Q ρ m N σ J i b S k v x w =
      normalizedDescriptorJet Q ρ m N σ J i b S k v (Q.descendant X).center w := by
  unfold normalizedDescriptorJet
  rw [descriptorAmbientMask_reached_eq Q hQ ρ m N σ J i b S X hb hx]


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetProduct
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Indexed products of actual normalized descriptor derivatives

The index set distinguishes repeated descriptors. Its total derivative
order controls the norm independently of the number of undifferentiated
masks. Reached factors split off as one angular function on each cell.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

theorem descriptorJetProduct_reached_split {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (k : ι → ℕ)
    (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (X : List (Fin d → Bool)) {x : Space d} (hx : x ∈ (Q.descendant X).carrier)
    (w : Sphere d) :
    descriptorJetProduct Q ρ m N σ J i F b S k v x w =
      descriptorJetProduct Q ρ m N σ J i
        (F.filter (fun j => descriptorAnchor (b j) ≤ X.length)) b S k v (Q.descendant X).center w *
      descriptorJetProduct Q ρ m N σ J i
        (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w := by
  classical
  unfold descriptorJetProduct
  have hsplit := (Finset.prod_filter_mul_prod_filter_not F
    (fun j => descriptorAnchor (b j) ≤ X.length)
    (fun j => normalizedDescriptorJet Q ρ m N σ J i (b j) (S (b j)) (k j) (v j w) x w)).symm
  rw [show F.filter (fun j => ¬descriptorAnchor (b j) ≤ X.length) =
    F.filter (fun j => X.length < descriptorAnchor (b j)) by ext j; simp] at hsplit
  refine hsplit.trans ?_
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact normalizedDescriptorJet_reached Q hQ ρ m N σ J i (b j) (S (b j)) (k j)
    (v j w) X (Finset.mem_filter.mp hj).2 hx w

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetMeasurable
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurability of the actual anchored mask jets

The spatial variable only selects one of finitely many Borel anchor cells.
Within such a cell all angular jets are derivatives of its fixed smooth mask.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
open scoped ContDiff
attribute [local instance] Classical.propDecidable

 theorem normalizedDescriptorJet_anchor_sum {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ)
    (v : Fin k → Space d) (x : Space d) (w : Sphere d) :
    normalizedDescriptorJet Q ρ m N σ J i b S k v x w =
      ∑ p ∈ cubePaths d (descriptorAnchor b),
        if x ∈ (Q.descendant p).carrier then
          (((descriptorMaskRadius N σ b)^k *
            (iteratedFDeriv ℝ k
              (capCutoffAmbient (descriptorMaskRadius N σ b)
                (descriptorMaskRadius_pos N σ b) S
                (descriptorGoodDirections Q ρ m N σ J (i+1) p b)) w) v : ℝ) : ℂ)
        else 0 := by
  classical
  by_cases hx : x ∈ Q.carrier
  · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth (descriptorAnchor b) hx
    rw [Finset.sum_eq_single p]
    · have he := funext (descriptorAmbientMask_on_cell Q ρ m N σ J i b S p
        ((mem_cubePaths d _ p).mp hp) hxp)
      simp only [normalizedDescriptorJet,he,ite_eq_left hxp]
    · intro q hq hqp
      have hdis := Q.descendants_disjoint
        (((mem_cubePaths d _ q).mp hq).trans ((mem_cubePaths d _ p).mp hp).symm) hqp
      exact ite_eq_right (fun hq => Set.disjoint_left.mp hdis hq hxp)
    · exact fun hn => (hn hp).elim
  · have hz : normalizedDescriptorJet Q ρ m N σ J i b S k v x w = 0 := by
      simp only [normalizedDescriptorJet,descriptorAmbientMask_off_parent Q ρ m N σ J i b S hx,
        iteratedFDeriv_fun_zero,Pi.zero_apply,zero_apply,mul_zero,Complex.ofReal_zero]
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro p _
    exact ite_eq_right (fun hp => hx (Q.descendant_subset p hp))

 theorem normalizedDescriptorJet_measurable {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PolicyDescriptor) (S : Finset (Sphere d)) (k : ℕ)
    (v : Sphere d → Fin k → Space d) (hv : Measurable v) :
    Measurable (fun z : Space d × Sphere d =>
      normalizedDescriptorJet Q ρ m N σ J i b S k (v z.2) z.1 z.2) := by
  classical
  simp_rw [normalizedDescriptorJet_anchor_sum]
  apply Finset.measurable_sum
  intro p _
  let f := capCutoffAmbient (descriptorMaskRadius N σ b)
    (descriptorMaskRadius_pos N σ b) S
    (descriptorGoodDirections Q ρ m N σ J (i+1) p b)
  have hf : ContDiff ℝ ∞ f := capCutoffAmbient_contDiff (descriptorMaskRadius_pos N σ b) S _
  have he : Continuous (fun z : Space d × (Fin k → Space d) =>
      (iteratedFDeriv ℝ k f z.1) z.2) :=
    ((hf.continuous_iteratedFDeriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp continuous_fst).eval continuous_snd
  have hm : Measurable (fun w : Sphere d =>
      (((descriptorMaskRadius N σ b)^k * (iteratedFDeriv ℝ k f w) (v w) : ℝ) : ℂ)) :=
    ((he.measurable.comp (continuous_subtype_val.measurable.prodMk hv)).const_mul _).complex_ofReal
  exact (hm.comp measurable_snd).ite
    ((Q.descendant p).measurable.preimage measurable_fst) measurable_const

 theorem descriptorJetProduct_measurable {d : ℕ} {ι : Type*} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hv : ∀ j ∈ F, Measurable (v j)) :
    Measurable (Function.uncurry (descriptorJetProduct Q ρ m N σ J i F b S k v)) := by
  apply Finset.measurable_prod
  intro j hj
  exact normalizedDescriptorJet_measurable Q ρ m N σ J i (b j) (S (b j)) (k j) (v j) (hv j hj)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_DescriptorJetRemoval
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reached differentiated masks in positive independent energy

Every unreached occurrence remains in the endpoint transform. The cost of
removing reached factors depends on the fixed total jet order, not on the
number of undifferentiated masks or the scale.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

theorem descriptorJetBound_one_le (d K : ℕ) : 1 ≤ descriptorJetBound d K :=
  (normalizedDescriptorJet_order_bound d K).choose_spec.1

theorem descriptorJetProduct_norm_le {d K : ℕ} {ι : Type*} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hsep : ∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
      descriptorMaskRadius N σ (b j)/2 ≤ dist w z)
    (horder : (∑ j ∈ F, k j) ≤ K)
    (hv : ∀ j ∈ F, ∀ w l, ‖v j w l‖ ≤ 1) (x : Space d) (w : Sphere d) :
    ‖descriptorJetProduct Q ρ m N σ J i F b S k v x w‖ ≤ (descriptorJetBound d K)^K := by
  have hA := descriptorJetBound_one_le d K
  have hbound := (normalizedDescriptorJet_order_bound d K).choose_spec.2
  rw [descriptorJetProduct,norm_prod]
  calc
    _ ≤ ∏ j ∈ F, (descriptorJetBound d K)^(k j) := by
      apply Finset.prod_le_prod (fun j _ => norm_nonneg _)
      intro j hj
      exact hbound Q ρ m N σ J i (b j) (S (b j)) (hsep j hj) (k j)
        ((Finset.single_le_sum (fun l _ => Nat.zero_le (k l)) hj).trans horder)
        (v j w) (hv j hj w) x w
    _ = (descriptorJetBound d K)^(∑ j ∈ F, k j) := Finset.prod_pow_eq_pow_sum F k _
    _ ≤ (descriptorJetBound d K)^K := pow_le_pow_right₀ hA horder

/-- Evaluate the spatial parameter before proving angular measurability. -/
theorem descriptorJetProduct_fixed_measurable {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (F : Finset ι)
    (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (hv : ∀ j ∈ F, Measurable (v j)) (x : Space d) :
    Measurable (fun w => descriptorJetProduct Q ρ m N σ J i F b S k v x w) := by
  exact (descriptorJetProduct_measurable Q ρ m N σ J i F b S k v hv).of_uncurry_left

/-- Bounded angular factors can be removed from two finite endpoint laws. -/
theorem independentAngularEnergy_endpoint_remove_factors {d : ℕ}
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (f g : Space d → Sphere d → ℂ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfC : ∀ x w, ‖f x w‖ ≤ C) (hgD : ∀ x w, ‖g x w‖ ≤ D)
    (p q : Sphere d → ℂ) (hp : Measurable p) (hq : Measurable q)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpA : ∀ w, ‖p w‖ ≤ A) (hqB : ∀ w, ‖q w‖ ≤ B)
    (a t : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure t Ψ)] :
    independentAngularEnergy a t Ψ
      (fun z => p z.2 * endpointTransform μ M f z.1 z.2)
      (fun z => q z.2 * endpointTransform ν P g z.1 z.2) ≤
    A^2*B^2*independentAngularEnergy a t Ψ
      (fun z => endpointTransform μ M f z.1 z.2)
      (fun z => endpointTransform ν P g z.1 z.2) := by
  exact independentAngularEnergy_remove_factors a t Ψ _ _
    (measurable_endpointTransform μ M f hf) (measurable_endpointTransform ν P g hg)
    p q hp hq hA hB
    (div_nonneg (mul_nonneg hC measureReal_nonneg) hM.le)
    (div_nonneg (mul_nonneg hD measureReal_nonneg) hP.le)
    hpA hqB (fun z => endpointTransform_norm_le μ hM f hfC z.1 z.2)
    (fun z => endpointTransform_norm_le ν hP g hgD z.1 z.2)

 theorem endpointTransform_descriptorJetProduct_split {d : ℕ} {ι : Type*}
    (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (b : ι → PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere d))
    (k : ι → ℕ) (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (X : List (Fin d → Bool)) (μ : Measure (Space d)) (M : ℝ)
    (f : Space d → Sphere d → ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict (Q.descendant X).carrier) M
      (fun x w => descriptorJetProduct Q ρ m N σ J i F b S k v x w * f x w) r w =
    descriptorJetProduct Q ρ m N σ J i
      (F.filter (fun j => descriptorAnchor (b j) ≤ X.length)) b S k v (Q.descendant X).center w *
    endpointTransform (μ.restrict (Q.descendant X).carrier) M
      (fun x w => descriptorJetProduct Q ρ m N σ J i
        (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w * f x w) r w := by
  classical
  rw [← endpointTransform_angular_factor (μ.restrict (Q.descendant X).carrier) M
    (fun x w => descriptorJetProduct Q ρ m N σ J i
      (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w * f x w)
    (fun w => descriptorJetProduct Q ρ m N σ J i
      (F.filter (fun j => descriptorAnchor (b j) ≤ X.length)) b S k v (Q.descendant X).center w) r w]
  unfold endpointTransform
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (Q.descendant X).measurable] with x hx
  rw [descriptorJetProduct_reached_split Q hQ ρ m N σ J i F b S k v X hx w]
  ring

 theorem independentAngularEnergy_descriptorJets_remove {d K : ℕ} {ι τ : Type*}
    (Q : DyadicCube d) (hQ : 0 < Q.side)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (F : Finset ι) (G : Finset τ) (b : ι → PolicyDescriptor) (c : τ → PolicyDescriptor)
    (S : PolicyDescriptor → Finset (Sphere d)) (k : ι → ℕ) (l : τ → ℕ)
    (v : (j : ι) → Sphere d → Fin (k j) → Space d)
    (u : (j : τ) → Sphere d → Fin (l j) → Space d)
    (hsepF : ∀ j ∈ F, ∀ w ∈ S (b j), ∀ z ∈ S (b j), w ≠ z →
      descriptorMaskRadius N σ (b j)/2 ≤ dist w z)
    (hsepG : ∀ j ∈ G, ∀ w ∈ S (c j), ∀ z ∈ S (c j), w ≠ z →
      descriptorMaskRadius N σ (c j)/2 ≤ dist w z)
    (horderF : (∑ j ∈ F, k j) ≤ K) (horderG : (∑ j ∈ G, l j) ≤ K)
    (hv : ∀ j ∈ F, ∀ w t, ‖v j w t‖ ≤ 1) (hu : ∀ j ∈ G, ∀ w t, ‖u j w t‖ ≤ 1)
    (hvm : ∀ j ∈ F, Measurable (v j)) (hum : ∀ j ∈ G, Measurable (u j))
    (X Y : List (Fin d → Bool)) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M₁ M₂ : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (f g : Space d → Sphere d → ℂ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hfC : ∀ x w, ‖f x w‖ ≤ C₁) (hgC : ∀ x w, ‖g x w‖ ≤ C₂)
    (a t : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure t Ψ)] :
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M₁
        (fun x w => descriptorJetProduct Q ρ m N σ J i F b S k v x w * f x w) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) M₂
        (fun x w => descriptorJetProduct Q ρ m N σ J i G c S l u x w * g x w) z.1 z.2) ≤
    ((descriptorJetBound d K)^K)^2 * ((descriptorJetBound d K)^K)^2 *
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M₁
        (fun x w => descriptorJetProduct Q ρ m N σ J i
          (F.filter (fun j => X.length < descriptorAnchor (b j))) b S k v x w * f x w) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) M₂
        (fun x w => descriptorJetProduct Q ρ m N σ J i
          (G.filter (fun j => Y.length < descriptorAnchor (c j))) c S l u x w * g x w) z.1 z.2) := by
  classical
  simp_rw [endpointTransform_descriptorJetProduct_split Q hQ ρ m N σ J i F b S k v,
    endpointTransform_descriptorJetProduct_split Q hQ ρ m N σ J i G c S l u]
  let A := (descriptorJetBound d K)^K
  have hA : 0 ≤ A := pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le d K)) K
  have hF (H : Finset ι) (hH : H ⊆ F) (x : Space d) (w : Sphere d) :
      ‖descriptorJetProduct Q ρ m N σ J i H b S k v x w‖ ≤ A :=
    descriptorJetProduct_norm_le Q ρ m N σ J i H b S k v
      (fun j hj => hsepF j (hH hj)) ((Finset.sum_le_sum_of_subset hH).trans horderF)
      (fun j hj => hv j (hH hj)) x w
  have hG (H : Finset τ) (hH : H ⊆ G) (x : Space d) (w : Sphere d) :
      ‖descriptorJetProduct Q ρ m N σ J i H c S l u x w‖ ≤ A :=
    descriptorJetProduct_norm_le Q ρ m N σ J i H c S l u
      (fun j hj => hsepG j (hH hj)) ((Finset.sum_le_sum_of_subset hH).trans horderG)
      (fun j hj => hu j (hH hj)) x w
  let FX := F.filter (fun j => X.length < descriptorAnchor (b j))
  let GY := G.filter (fun j => Y.length < descriptorAnchor (c j))
  let RX := F.filter (fun j => descriptorAnchor (b j) ≤ X.length)
  let RY := G.filter (fun j => descriptorAnchor (c j) ≤ Y.length)
  let f' := fun x w => descriptorJetProduct Q ρ m N σ J i FX b S k v x w * f x w
  let g' := fun x w => descriptorJetProduct Q ρ m N σ J i GY c S l u x w * g x w
  have hf' : Measurable (Function.uncurry f') :=
    (descriptorJetProduct_measurable Q ρ m N σ J i FX b S k v
      (fun j hj => hvm j ((Finset.filter_subset _ _) hj))).mul hf
  have hg' : Measurable (Function.uncurry g') :=
    (descriptorJetProduct_measurable Q ρ m N σ J i GY c S l u
      (fun j hj => hum j ((Finset.filter_subset _ _) hj))).mul hg
  have hf'C (x : Space d) (w : Sphere d) : ‖f' x w‖ ≤ A*C₁ := by
    change ‖descriptorJetProduct Q ρ m N σ J i FX b S k v x w * f x w‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hF FX (Finset.filter_subset _ _) x w) (hfC x w) (norm_nonneg _) hA
  have hg'C (x : Space d) (w : Sphere d) : ‖g' x w‖ ≤ A*C₂ := by
    change ‖descriptorJetProduct Q ρ m N σ J i GY c S l u x w * g x w‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hG GY (Finset.filter_subset _ _) x w) (hgC x w) (norm_nonneg _) hA
  exact independentAngularEnergy_endpoint_remove_factors
    (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier)
    hM₁ hM₂ f' g' hf' hg' (mul_nonneg hA hC₁) (mul_nonneg hA hC₂) hf'C hg'C
    (fun w => descriptorJetProduct Q ρ m N σ J i RX b S k v (Q.descendant X).center w)
    (fun w => descriptorJetProduct Q ρ m N σ J i RY c S l u (Q.descendant Y).center w)
    (descriptorJetProduct_fixed_measurable Q ρ m N σ J i RX b S k v
      (fun j hj => hvm j ((Finset.filter_subset _ _) hj)) _)
    (descriptorJetProduct_fixed_measurable Q ρ m N σ J i RY c S l u
      (fun j hj => hum j ((Finset.filter_subset _ _) hj)) _)
    hA hA (hF RX (Finset.filter_subset _ _) _) (hG RY (Finset.filter_subset _ _) _) a t Ψ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FactorizedAngularState
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The factorized symbols used by recursive angular states

The descriptor list is part of the type: every descriptor occurs once,
with an explicitly recorded jet. Passing to a deeper cell filters that
list and keeps the same spatial and smooth angular multipliers.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

namespace DescriptorJetSymbol
variable {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}

 theorem multiplier_measurable (f : DescriptorJetSymbol n K L F D) (A : ℝ) :
    Measurable (Function.uncurry (f.multiplier A)) :=
  (f.spatial_measurable.comp measurable_fst).mul measurable_const |>.mul
    f.angular_control.measurable

 theorem multiplier_bound (f : DescriptorJetSymbol n K L F D) {A : ℝ} (hA : 0 < A)
    (x : Space (n+2)) (w : Sphere (n+2)) : ‖f.multiplier A x w‖ ≤ A⁻¹ := by
  rw [multiplier,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hA.le)]
  calc
    _ ≤ (1*A⁻¹)*1 := mul_le_mul
      (mul_le_mul_of_nonneg_right (f.spatial_bound x) (inv_nonneg.mpr hA.le))
      (f.angular_control.bound x w) (norm_nonneg _) (by positivity)
    _ = _ := by ring

 theorem value_measurable (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (n+2))) (A : ℝ) :
    Measurable (Function.uncurry (f.value Q ρ m N σ J i S A)) := by
  have hp := descriptorJetProduct_measurable Q ρ m N σ J i F id S
    (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors) (fun _ _ => measurable_const)
  exact hp.mul (f.multiplier_measurable A)

 theorem value_norm_le (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hsep : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (x : Space (n+2)) (w : Sphere (n+2)) :
    ‖f.value Q ρ m N σ J i S A x w‖ ≤ ((descriptorJetBound (n+2) K)^K)*A⁻¹ := by
  rw [value,norm_mul]
  exact mul_le_mul
    (descriptorJetProduct_norm_le Q ρ m N σ J i F id S
      (fun b => (f.jet b).order) (fun b _ => (f.jet b).vectors)
      hsep f.order_le (fun b _ _ => (f.jet b).norm_vectors) x w)
    (f.multiplier_bound hA x w) (norm_nonneg _)
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)

 theorem energy_remove_reached (f g : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (hQ : 0 < Q.side)
    (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hsep : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z →
      descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (X Y : List (Fin (n+2) → Bool))
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a t : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure t Ψ)] :
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M
        (f.value Q ρ m N σ J i S A) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) P
        (g.value Q ρ m N σ J i S A) z.1 z.2) ≤
    ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
    independentAngularEnergy a t Ψ
      (fun z => endpointTransform (μ.restrict (Q.descendant X).carrier) M
        ((f.restrict (F.filter (fun b => X.length < descriptorAnchor b))
          (Finset.filter_subset _ _)).value Q ρ m N σ J i S A) z.1 z.2)
      (fun z => endpointTransform (ν.restrict (Q.descendant Y).carrier) P
        ((g.restrict (F.filter (fun b => Y.length < descriptorAnchor b))
          (Finset.filter_subset _ _)).value Q ρ m N σ J i S A) z.1 z.2) := by
  exact independentAngularEnergy_descriptorJets_remove Q hQ ρ m N σ J i F F id id S
    (fun b => (f.jet b).order) (fun b => (g.jet b).order)
    (fun b _ => (f.jet b).vectors) (fun b _ => (g.jet b).vectors)
    hsep hsep f.order_le g.order_le
    (fun b _ _ => (f.jet b).norm_vectors) (fun b _ _ => (g.jet b).norm_vectors)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const)
    X Y μ ν hM hP (f.multiplier A) (g.multiplier A)
    (f.multiplier_measurable A) (g.multiplier_measurable A)
    (inv_nonneg.mpr hA.le) (inv_nonneg.mpr hA.le)
    (f.multiplier_bound hA) (g.multiplier_bound hA) a t Ψ

end DescriptorJetSymbol
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FarCellGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual cell geometry used by the far transition

The fixed separation constant may be chosen as 2000(d+1).  Comparable
point displacements at a dyadic depth then give cells satisfying that
separation, while a center displacement outside the near graph remains
large throughout both cells.
-/

namespace Falconer
open Set Metric
variable {d : ℕ}

theorem DyadicCube.point_center_bound (P : DyadicCube d) (hP : 0 < P.side)
    {ℓ : ℝ} (hside : P.side ≤ ℓ) {x : Space d} (hx : x ∈ P.carrier) :
    dist x P.center ≤ ((d:ℝ)+1)*ℓ := by
  exact (P.dist_le hP.le hx (P.center_mem hP)).trans
    ((mul_le_mul_of_nonneg_left hside (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (sqrt_dimension_le d) (hP.le.trans hside)))

theorem DyadicCube.far_centers_force_far_points (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {ℓ : ℝ}
    (hPs : P.side ≤ ℓ) (hQs : Q.side ≤ ℓ)
    (hfar : 10*((d:ℝ)+1)*ℓ < dist P.center Q.center)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    8*((d:ℝ)+1)*ℓ < dist x y := by
  have hpx := P.point_center_bound hP hPs hx
  have hqy := Q.point_center_bound hQ hQs hy
  have ht := (dist_triangle P.center x Q.center).trans
    (add_le_add (le_refl _) (dist_triangle x y Q.center))
  rw [dist_comm P.center x] at ht
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FourPointPartition
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original four-point partitions before far rebinning

Each internal pair keeps its original two endpoint restrictions. These
identities allow a nonnegative kernel bound to discard a far-label
selection and then repartition at the common comparable-displacement depth.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem DyadicCube.pair_restrict_occupiedPaths {d : ℕ} (P : DyadicCube d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (n : ℕ) :
    (μ.restrict P.carrier).prod (μ.restrict P.carrier) =
      ∑ u ∈ P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n,
        (μ.restrict (P.descendant u.1).carrier).prod (μ.restrict (P.descendant u.2).carrier) := by
  rw [P.restrict_occupiedPaths μ n,PlanarFalconer.finite_measure_prod_sum,Finset.sum_product]

theorem originalFourPointMeasure_partition {d : ℕ} (P Q : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ) :
    originalFourPointMeasure P Q μ ν =
      ∑ u ∈ P.occupiedPaths μ n ×ˢ P.occupiedPaths μ n,
        ∑ v ∈ Q.occupiedPaths ν n ×ˢ Q.occupiedPaths ν n,
          fourPointChildMeasure P Q μ ν u v := by
  rw [originalFourPointMeasure,P.pair_restrict_occupiedPaths μ n,
    Q.pair_restrict_occupiedPaths ν n,PlanarFalconer.finite_measure_prod_sum]
  rfl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FarOriginalSupport
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Far-label elimination under a positive original-law bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

theorem sum_pair_reassociate {α β M : Type*} [AddCommMonoid M]
    (A : Finset α) (B : Finset β) (F : (α × α) → (β × β) → M) :
    (∑ row ∈ A ×ˢ B, ∑ col ∈ A ×ˢ B, F (row.1,col.1) (row.2,col.2)) =
      ∑ u ∈ A ×ˢ A, ∑ v ∈ B ×ˢ B, F u v := by
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

 theorem originalFourPoint_lintegral_rows {d : ℕ} (P Q : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (n : ℕ) (U : Set ((Space d × Space d) × (Space d × Space d)))
    (F : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞) :
    (∑ row ∈ P.occupiedPaths μ n ×ˢ Q.occupiedPaths ν n,
      ∑ col ∈ P.occupiedPaths μ n ×ˢ Q.occupiedPaths ν n,
        ∫⁻ z in U, F z ∂fourPointChildMeasure P Q μ ν (row.1,col.1) (row.2,col.2)) =
      ∫⁻ z in U, F z ∂originalFourPointMeasure P Q μ ν := by
  rw [sum_pair_reassociate (P.occupiedPaths μ n) (Q.occupiedPaths ν n)
    (fun u v => ∫⁻ z in U, F z ∂fourPointChildMeasure P Q μ ν u v),
    originalFourPointMeasure_partition P Q μ ν n]
  simp only [PlanarFalconer.finite_measure_restrict_sum,lintegral_finsetSum_measure]

 theorem fourPointChildMeasure_far_support {d a h : ℕ}
    (Q : DyadicCube d) (hQ : Q.side = 1) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (hah : a ≤ h) (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (row col : List (Fin d → Bool) × List (Fin d → Bool))
    (hrow : row ∈ (Q.descendant X).occupiedPaths ρ (h-a) ×ˢ (Q.descendant Y).occupiedPaths ρ (h-a))
    (hcol : col ∈ (Q.descendant X).occupiedPaths ρ (h-a) ×ˢ (Q.descendant Y).occupiedPaths ρ (h-a))
    (hfar : ¬nearDyadicEdge (Q.descendant X) (Q.descendant Y)
      (10*((d:ℝ)+1)/(2:ℝ)^h) row col) :
    ∀ᵐ z ∂fourPointChildMeasure (Q.descendant X) (Q.descendant Y) ρ ρ
      (row.1,col.1) (row.2,col.2), z ∈ farDisplacementRegion d a h := by
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hside (Z : List (Fin d → Bool)) (hZ : Z.length = a) :
      (Q.descendant Z).side = (2:ℝ)^(-(a:ℝ)) := by
    rw [Q.descendant_side,hQ,hZ,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,one_div]
  have hchild (Z : List (Fin d → Bool)) (hZ : Z.length = a)
      (p : List (Fin d → Bool)) (hp : p ∈ (Q.descendant Z).occupiedPaths ρ (h-a)) :
      ((Q.descendant Z).descendant p).side = (2:ℝ)^(-(h:ℝ)) := by
    rw [(Q.descendant Z).descendant_side,
      (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hp).1,
      Q.descendant_side,hQ,hZ,div_div,← pow_add,Nat.add_sub_of_le hah,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  obtain ⟨hr₁,hr₂⟩ := Finset.mem_product.mp hrow
  obtain ⟨hc₁,hc₂⟩ := Finset.mem_product.mp hcol
  unfold fourPointChildMeasure
  rw [Measure.prod_restrict,Measure.prod_restrict,Measure.prod_restrict]
  filter_upwards [ae_restrict_mem
    ((((Q.descendant X).descendant row.1).measurable.prod
      ((Q.descendant X).descendant col.1).measurable).prod
      (((Q.descendant Y).descendant row.2).measurable.prod
        ((Q.descendant Y).descendant col.2).measurable))] with z hz
  have hu (Z : List (Fin d → Bool)) (hZ : Z.length = a)
      (p q : List (Fin d → Bool)) (x y : Space d)
      (hx : x ∈ ((Q.descendant Z).descendant p).carrier)
      (hy : y ∈ ((Q.descendant Z).descendant q).carrier) :
      dist x y ≤ 2*((d:ℝ)+1)*(2:ℝ)^(-(a:ℝ)) := by
    have h := (Q.descendant Z).dist_le (Q.descendant_side_pos hQpos Z).le
      ((Q.descendant Z).descendant_subset p hx) ((Q.descendant Z).descendant_subset q hy)
    rw [hside Z hZ] at h
    have h' := mul_le_mul_of_nonneg_right (sqrt_dimension_le d)
      (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-(a:ℝ)))
    have hd : 0 ≤ ((d:ℝ)+1)*(2:ℝ)^(-(a:ℝ)) := by positivity
    linarith
  refine ⟨max_le (hu X hX row.1 col.1 _ _ hz.1.1 hz.1.2)
    (hu Y hY row.2 col.2 _ _ hz.2.1 hz.2.2),?_⟩
  have hτ : 10*((d:ℝ)+1)/(2:ℝ)^h = 10*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,div_eq_mul_inv]
  have hnot : ¬(dist ((Q.descendant X).descendant row.1).center
        ((Q.descendant X).descendant col.1).center ≤ 10*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) ∧
      dist ((Q.descendant Y).descendant row.2).center
        ((Q.descendant Y).descendant col.2).center ≤ 10*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ))) := by
    simpa only [nearDyadicEdge,hτ,dist_eq_norm,norm_sub_rev] using hfar
  by_cases hx : dist ((Q.descendant X).descendant row.1).center
      ((Q.descendant X).descendant col.1).center ≤ 10*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ))
  · have hy := lt_of_not_ge (fun hy => hnot ⟨hx,hy⟩)
    have hg := DyadicCube.far_centers_force_far_points _ _
      ((Q.descendant Y).descendant_side_pos (Q.descendant_side_pos hQpos Y) row.2)
      ((Q.descendant Y).descendant_side_pos (Q.descendant_side_pos hQpos Y) col.2)
      (hchild Y hY row.2 hr₂).le (hchild Y hY col.2 hc₂).le hy hz.2.1 hz.2.2
    exact hg.trans_le (le_max_right _ _)
  · have hg := DyadicCube.far_centers_force_far_points _ _
      ((Q.descendant X).descendant_side_pos (Q.descendant_side_pos hQpos X) row.1)
      ((Q.descendant X).descendant_side_pos (Q.descendant_side_pos hQpos X) col.1)
      (hchild X hX row.1 hr₁).le (hchild X hX col.1 hc₁).le (lt_of_not_ge hx) hz.1.1 hz.1.2
    exact hg.trans_le (le_max_left _ _)

 theorem originalFourPoint_far_rows_le {d a h : ℕ}
    (Q : DyadicCube d) (hQ : Q.side = 1) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (hah : a ≤ h) (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (F : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞) :
    (∑ row ∈ (Q.descendant X).occupiedPaths ρ (h-a) ×ˢ (Q.descendant Y).occupiedPaths ρ (h-a),
      ∑ col ∈ (Q.descendant X).occupiedPaths ρ (h-a) ×ˢ (Q.descendant Y).occupiedPaths ρ (h-a),
        if nearDyadicEdge (Q.descendant X) (Q.descendant Y) (10*((d:ℝ)+1)/(2:ℝ)^h) row col
        then 0 else ∫⁻ z, F z ∂fourPointChildMeasure (Q.descendant X) (Q.descendant Y)
          ρ ρ (row.1,col.1) (row.2,col.2)) ≤
      ∫⁻ z in farDisplacementRegion d a h, F z
        ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ := by
  rw [← originalFourPoint_lintegral_rows (Q.descendant X) (Q.descendant Y) ρ ρ (h-a)]
  apply Finset.sum_le_sum
  intro row hr
  apply Finset.sum_le_sum
  intro col hc
  by_cases hf : nearDyadicEdge (Q.descendant X) (Q.descendant Y) (10*((d:ℝ)+1)/(2:ℝ)^h) row col
  · simp only [ite_eq_left hf]; exact bot_le
  · rw [ite_eq_right hf,Measure.restrict_eq_self_of_ae_mem
      (fourPointChildMeasure_far_support Q hQ ρ hah X Y hX hY row col hr hc hf)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_PositiveSuffix
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual policy suffix transition for positive distance counts -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor descriptorLength)
attribute [local instance] Classical.propDecidable
variable {d : ℕ}

theorem suffix_policy_projection_mem (A : ℕ → ℝ) {N q a t : ℕ}
    (ht : t ≤ N) (hw : a+100*q < t)
    (hs : a+t < 2*PlanarFalconer.policyDepth A N q a t) :
    PolicyDescriptor.projection (PlanarFalconer.policyDepth A N q a t) t ∈
      PlanarFalconer.policyDescriptorList A N q a t := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      le_rfl,le_rfl,hw⟩
  · apply Finset.mem_union_right
    simp [hs]

theorem policy_descriptor_end_bounds (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {b : PolicyDescriptor} (hb : b ∈ PlanarFalconer.policyDescriptorList A N q a t) :
    descriptorAnchor b ≤ t ∧ descriptorLength b ≤ t-a := by
  obtain ⟨u,v,hau,hvt,_,_,_,hleft,hright⟩ := PlanarFalconer.policyDescriptor_origin A hq hb
  omega

/-- The suffix collision estimate uses the actual tested pair measures,
with a coarser policy list at the next smoothing index. -/
theorem uniform_policy_suffix_collision {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
        (q a p t i : ℕ), 0 < q → t ≤ N → a+100*q < t →
        p = PlanarFalconer.policyDepth A N q a t → a+t < 2*p → i ≤ J →
      ∀ (w₀ : Sphere d) (X Y : List (Fin d → Bool)), X.length = a → Y.length = a →
      125*((d:ℝ)+1)*(Q.descendant X).side ≤
        ‖(Q.descendant X).center-(Q.descendant Y).center‖ →
      ((testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J i q a t)).prod
        (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J i q a t)))
        {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^t} ≤
      (((PlanarFalconer.bandOffsets (100*((d:ℝ)+1))).card : ℝ≥0∞) *
        ((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) *
        ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
          Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ))) *
      ((testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J (i+1) q a p)).prod
        (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (policyTestPairs w₀ Q ρ m A N σ J (i+1) q a p)))
        {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^p} := by
  obtain ⟨N₁,h₁⟩ := uniform_suffix_witness_width d hσ hJ
  obtain ⟨N₂,h₂⟩ := uniform_full_cell_tests_of_witness (d := d) hσ hJ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ _ m A q a p t i hq htN hwide hp hapt hi w₀ X Y hX hY hsep
  have hne := PlanarFalconer.policyBlocks_nonempty hq htN hwide
  have hpi := PlanarFalconer.policyDepth_interior A hq hne
  rw [← hp] at hpi
  have hap : a ≤ p := by omega
  have hpt : p ≤ t := by omega
  have hQp : 0 < Q.side := by rw [hQ]; norm_num
  have hPX : (Q.descendant X).side = 1/(2:ℝ)^a := by rw [Q.descendant_side,hX,hQ]
  have hPY : (Q.descendant Y).side = (Q.descendant X).side := by
    rw [Q.descendant_side,Q.descendant_side,hX,hY]
  have hsmallSide : (Q.descendant X).side/(2:ℝ)^(p-a) = 1/(2:ℝ)^p := by
    rw [hPX,div_div,← pow_add,Nat.add_sub_of_le hap]
  let G := policyTestPairs w₀ Q ρ m A N σ J i q a t
  let H := policyTestPairs w₀ Q ρ m A N σ J (i+1) q a p
  let g := 100*((d:ℝ)+1)/(2:ℝ)^a
  have hg : 0 < g := by dsimp [g]; positivity
  have hpoints {x y : Space d} (hx : x ∈ (Q.descendant X).carrier)
      (hy : y ∈ (Q.descendant Y).carrier) : g ≤ ‖x-y‖ := by
    simpa only [g,hPX,div_eq_mul_inv,one_mul] using
      (Q.descendant X).separated_pairs_lower (Q.descendant Y)
        (Q.descendant_side_pos hQp X) hPY hsep hx hy
  have hlength (c : List (Fin d → Bool) × List (Fin d → Bool))
      (hc : c ∈ retainedCellPairs ρ ρ (Q.descendant X) (Q.descendant Y) (p-a) G) :
      c.1.length = p-a ∧ c.2.length = p-a := by
    obtain ⟨hc,_⟩ := Finset.mem_filter.mp hc
    exact ⟨(mem_cubePaths _ _ _).mp (Finset.mem_filter.mp (Finset.mem_product.mp hc).1).1,
      (mem_cubePaths _ _ _).mp (Finset.mem_filter.mp (Finset.mem_product.mp hc).2).1⟩
  have hcenters (c) (hc : c ∈ retainedCellPairs ρ ρ (Q.descendant X) (Q.descendant Y) (p-a) G) :
      g ≤ ‖((Q.descendant X).descendant c.1).center-((Q.descendant Y).descendant c.2).center‖ :=
    hpoints ((Q.descendant X).descendant_subset c.1
      (((Q.descendant X).descendant c.1).center_mem
        ((Q.descendant X).descendant_side_pos (Q.descendant_side_pos hQp X) c.1)))
      ((Q.descendant Y).descendant_subset c.2
        (((Q.descendant Y).descendant c.2).center_mem
          ((Q.descendant Y).descendant_side_pos (Q.descendant_side_pos hQp Y) c.2)))
  have hproj := retained_projection_test w₀ Q ρ m N σ J i a p t hap X Y hY
    (PlanarFalconer.policyDescriptorList A N q a t)
    (by rw [hp]; exact suffix_policy_projection_mem A htN hwide (by simpa only [← hp] using hapt))
    G (fun _ h => h) (fun x hx y hy => sub_ne_zero.mp (norm_pos_iff.mp (hg.trans_le (hpoints hx hy))))
  have hchild (c) (hc : c ∈ retainedCellPairs ρ ρ (Q.descendant X) (Q.descendant Y) (p-a) G) :
      ((Q.descendant X).descendant c.1).carrier ×ˢ ((Q.descendant Y).descendant c.2).carrier ⊆ H := by
    obtain ⟨hxlen,hylen⟩ := hlength c hc
    obtain ⟨_,x,hx,y,hy,hxy⟩ := Finset.mem_filter.mp hc
    have hsub := PlanarFalconer.policyDescriptorList_mono A (N := N) (q := q) (le_refl a) hpt
    have hboth := descriptorPairTests_mono w₀ Q ρ m N σ J i hsub hxy
    have hX' : (X++c.1).length = p := by simp only [List.length_append,hX,hxlen]; omega
    have hY' : (Y++c.2).length = p := by simp only [List.length_append,hY,hylen]; omega
    have hside : (Q.descendant (X++c.1)).side = 1/(2:ℝ)^p := by rw [Q.descendant_side,hX',hQ]
    have hh := h₂ N ((le_max_right _ _).trans hN) Q hQ ρ m
      (PlanarFalconer.policyDescriptorList A N q a p)
      (fun b hb => policy_descriptor_valid A hq (hpt.trans htN) hb)
      p (X++c.1) (Y++c.2) hX' hY'
      (fun b hb => (policy_descriptor_end_bounds A hq hb).1)
      g hg (by simpa only [Q.descendant_append] using hcenters c hc)
      (by rw [hside]; exact suffix_direction_small d hap)
      (fun b hb => by
        rw [hside]
        exact suffix_direction_buffer d hσ.le N hap
          (policy_descriptor_end_bounds A hq hb).2)
      i w₀ x y (by simpa only [Q.descendant_append] using hx)
      (by simpa only [Q.descendant_append] using hy) hboth
    simpa only [Q.descendant_append, H, policyTestPairs] using hh
  have hbound := tested_suffix_collision_bound ρ ρ (Q.descendant X) (Q.descendant Y)
    (p-a) G H (descriptorPairTests_measurable w₀ Q ρ m N σ J i _)
    (Q.descendant_side_pos hQp X) hPY hg (by positivity : 0 < 1/(2:ℝ)^t)
    (by rw [hsmallSide]; exact dyadic_side_mono hpt)
    (by rw [hsmallSide]; exact suffix_linearization_scale d (by omega))
    (by rw [hsmallSide]; exact h₁ N ((le_max_left _ _).trans hN) a p t (by omega) i hi)
    hcenters _ hproj hchild (100*((d:ℝ)+1))
  rw [hsmallSide] at hbound
  simp only [div_eq_mul_inv,one_mul] at hbound ⊢
  apply hbound.trans
  apply mul_le_mul' le_rfl
  apply measure_mono
  intro z hz
  change |z.1-z.2| ≤ _ at hz
  change |z.1-z.2| ≤ _
  apply hz.trans
  have hs := sqrt_dimension_le d
  have he : 1+4*Real.sqrt d ≤ 100*((d:ℝ)+1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  simpa only [mul_one,one_mul,div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ 1/(2:ℝ)^p)

theorem positiveCollisionCount_ne_top (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q a t : ℕ) (X Y : List (Fin d → Bool)) :
    positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y ≠ ⊤ := by
  unfold positiveCollisionCount
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

theorem positive_suffix_prefactor (N : ℕ) (M K : ℝ) {a p t : ℕ}
    (hap : a ≤ p) (hpt : p ≤ t) :
    ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*M)) *
        ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^K) =
      ENNReal.ofReal (((2:ℝ)^N)^K) *
        ENNReal.ofReal ((2:ℝ)^(p-a)*((2:ℝ)^N)^(4*M)) := by
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp : (2:ℝ)^(t-a) = (2:ℝ)^(p-a)*(2:ℝ)^(t-p) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  field_simp

theorem uniform_policy_suffix_count {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (A : ℕ → ℝ)
        (q a p t i : ℕ), 0 < q → t ≤ N → a+100*q < t →
        p = PlanarFalconer.policyDepth A N q a t → a+t < 2*p → i ≤ J →
      ∀ (w₀ : Sphere d) (X Y : List (Fin d → Bool)), X.length = a → Y.length = a →
      125*((d:ℝ)+1)*(Q.descendant X).side ≤
        ‖(Q.descendant X).center-(Q.descendant Y).center‖ →
      positiveCollisionCount w₀ Q ρ m A N σ J i q a t X Y ≤
        (((PlanarFalconer.bandOffsets (100*((d:ℝ)+1))).card : ℝ≥0∞) *
          ((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞) *
          ENNReal.ofReal (((2:ℝ)^N)^(
            Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ))) *
        positiveCollisionCount w₀ Q ρ m A N σ J (i+1) q a p X Y := by
  obtain ⟨N₀,h₀⟩ := uniform_policy_suffix_collision (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m A q a p t i hq htN hwide hp hapt hi w₀ X Y hX hY hsep
  have hc := h₀ N hN Q hQ ρ m A q a p t i hq htN hwide hp hapt hi w₀ X Y hX hY hsep
  have hpi := PlanarFalconer.policyDepth_interior A hq
    (PlanarFalconer.policyBlocks_nonempty hq htN hwide)
  rw [← hp] at hpi
  have hap : a ≤ p := by omega
  have hpt : p ≤ t := by omega
  unfold positiveCollisionCount
  apply (mul_le_mul' (le_refl (ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)))) hc).trans_eq
  let K := Regularization.profileDrop m N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ
  let B : ℝ≥0∞ := ((PlanarFalconer.bandOffsets (100*((d:ℝ)+1))).card : ℝ≥0∞) *
    ((PlanarFalconer.bandOffsets 3).card : ℝ≥0∞)
  let C : ℝ≥0∞ := ((testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
    (policyTestPairs w₀ Q ρ m A N σ J (i+1) q a p)).prod
    (testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
    (policyTestPairs w₀ Q ρ m A N σ J (i+1) q a p)))
      {z : ℝ × ℝ | |z.1-z.2| ≤ (100*((d:ℝ)+1))/(2:ℝ)^p}
  change ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) *
      (B*ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^K)*C) =
    (B*ENNReal.ofReal (((2:ℝ)^N)^K)) *
      (ENNReal.ofReal ((2:ℝ)^(p-a)*((2:ℝ)^N)^(4*m a))*C)
  calc
    _ = B*(ENNReal.ofReal ((2:ℝ)^(t-a)*((2:ℝ)^N)^(4*m a)) *
        ENNReal.ofReal ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^K))*C := by ring
    _ = _ := by rw [positive_suffix_prefactor N (m a) K hap hpt]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_NearFarSplit
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact angular near/far splitting before taking absolute values -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

private theorem integral_selected_sum {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (G : ι → ι → Prop) (F : ι → ι → X → ℂ)
    (hF : ∀ i ∈ S, ∀ j ∈ S, Integrable (F i j) μ) :
    (∫ x, ∑ i ∈ S, ∑ j ∈ S, if G i j then F i j x else 0 ∂μ) =
      ∑ i ∈ S, ∑ j ∈ S, if G i j then (∫ x, F i j x ∂μ) else 0 := by
  have hi (i) (hi : i ∈ S) (j) (hj : j ∈ S) :
      Integrable (fun x => if G i j then F i j x else 0) μ := by
    by_cases h : G i j
    · simpa only [ite_eq_left h] using hF i hi j hj
    · simp only [ite_eq_right h]; exact integrable_zero _ _ _
  rw [integral_finsetSum _ (fun i h => integrable_finsetSum _ (hi i h))]
  apply Finset.sum_congr rfl
  intro i h
  rw [integral_finsetSum _ (hi i h)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : G i j <;> simp only [h,ite_true, if_true,ite_false, if_false,integral_zero]

theorem norm_integral_near_far {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (G : ι → ι → Prop) (F : ι → ι → X → ℂ)
    (hF : ∀ i ∈ S, ∀ j ∈ S, Integrable (F i j) μ) :
    ‖∫ x, ∑ i ∈ S, ∑ j ∈ S, F i j x ∂μ‖ ≤
      ‖∫ x, ∑ i ∈ S, ∑ j ∈ S, if G i j then F i j x else 0 ∂μ‖ +
        ∑ i ∈ S, ∑ j ∈ S, if G i j then 0 else ‖∫ x, F i j x ∂μ‖ := by
  have hfull : (∫ x, ∑ i ∈ S, ∑ j ∈ S, F i j x ∂μ) =
      ∑ i ∈ S, ∑ j ∈ S, ∫ x, F i j x ∂μ := by
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (hF i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum _ (hF i hi)
  rw [hfull,integral_selected_sum μ S G F hF]
  have hsplit : (∑ i ∈ S, ∑ j ∈ S, ∫ x, F i j x ∂μ) =
      (∑ i ∈ S, ∑ j ∈ S, if G i j then (∫ x, F i j x ∂μ) else 0) +
      (∑ i ∈ S, ∑ j ∈ S, if G i j then 0 else (∫ x, F i j x ∂μ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : G i j <;> simp only [h,ite_true, if_true,ite_false, if_false,zero_add,add_zero]
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases h : G i j <;> simp only [h,ite_true, if_true,ite_false, if_false,norm_zero,le_refl]

 theorem profile_energy_near_far {d : ℕ} (P₁ P₂ : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (profile : ℝ → ℝ) (N a h : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (ρ.restrict P₁.carrier) (profileModelMass profile N a) b z.1 z.2)
      (fun z => endpointTransform (ρ.restrict P₂.carrier) (profileModelMass profile N a) c z.1 z.2) ≤
    profileNearEnergy P₁ P₂ ρ profile N a h v Ψ b c +
      ((profileModelMass profile N h/profileModelMass profile N a)^4*
        (2:ℝ)^((d:ℝ)*(v-a))) *
        ∑ row ∈ P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a),
          ∑ col ∈ P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a),
            if nearDyadicEdge P₁ P₂ (10*((d:ℝ)+1)/(2:ℝ)^h) row col then 0 else
              ‖∫ z, dyadicPairTransform P₁ P₂ ρ ρ (profileModelMass profile N h)
                  (profileModelMass profile N h) b c row z *
                star (dyadicPairTransform P₁ P₂ ρ ρ (profileModelMass profile N h)
                  (profileModelMass profile N h) b c col z)
                ∂angularProductMeasure d v Ψ‖ := by
  have hMa : 0 < profileModelMass profile N a := by unfold profileModelMass; positivity
  have hMh : 0 < profileModelMass profile N h := by unfold profileModelMass; positivity
  let F := fun row col z => dyadicPairTransform P₁ P₂ ρ ρ (profileModelMass profile N h)
      (profileModelMass profile N h) b c row z *
    star (dyadicPairTransform P₁ P₂ ρ ρ (profileModelMass profile N h)
      (profileModelMass profile N h) b c col z)
  have hi (row col) : Integrable (F row col) (angularProductMeasure d v Ψ) := by
    have hcross :=
      dyadicCapIntegrand_integrable P₁ P₂ ρ ρ (profileModelMass profile N h)
        (profileModelMass profile N h) v Ψ hMh hMh b c hb hc (fun _ => 1) (fun _ => 1)
        measurable_const measurable_const (by intro; norm_num) (by intro; norm_num) hB hbB hcB row col
    have heq : dyadicCapIntegrand P₁ P₂ ρ ρ (profileModelMass profile N h)
        (profileModelMass profile N h) b c (fun _ => 1) (fun _ => 1) row col = F row col := by
      funext z
      simp only [dyadicCapIntegrand,one_mul,one_smul]
      rfl
    rwa [heq] at hcross
  have he := independentAngularEnergy_dyadic_expansion P₁ P₂ ρ ρ (h-a) a v Ψ
    (profileModelMass profile N a) (profileModelMass profile N a)
    (profileModelMass profile N h) (profileModelMass profile N h) hMa hMa
    hMh.ne' hMh.ne' b c hb hc hB hB hbB hcB
  have hp : ((profileModelMass profile N h/profileModelMass profile N a)*
      (profileModelMass profile N h/profileModelMass profile N a))^2 =
      (profileModelMass profile N h/profileModelMass profile N a)^4 := by ring
  rw [hp] at he
  rw [he]
  have hs := norm_integral_near_far (angularProductMeasure d v Ψ)
    (P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a))
    (nearDyadicEdge P₁ P₂ (10*((d:ℝ)+1)/(2:ℝ)^h)) F (fun i _ j _ => hi i j)
  have hb := mul_le_mul_of_nonneg_left hs (show 0 ≤
      (profileModelMass profile N h/profileModelMass profile N a)^4*
        (2:ℝ)^((d:ℝ)*(v-a)) by positivity)
  simpa only [profileNearEnergy,F,mul_add,mul_assoc,mul_left_comm,mul_comm] using hb

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_VectorSphereKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original displacement phase in normalized spherical coordinates -/

namespace Falconer
open MeasureTheory

theorem norm_smul_normalizeToSphere {d : ℕ} (w₀ : Sphere d) (v : Space d) :
    ‖v‖ • (normalizeToSphere w₀ v : Space d) = v := by
  by_cases hv : v = 0
  · simp only [hv, norm_zero, zero_smul]
  · rw [normalizeToSphere_coe_of_ne w₀ hv]
    exact NormedSpace.norm_smul_normalize v

theorem sphereOscillator_normalized {d : ℕ} (w₀ : Sphere d)
    (r : ℝ) (v : Space d) (w : Sphere d) :
    sphereOscillator r v w =
      Complex.exp (Complex.I*((r*‖v‖):ℂ)*
        (inner ℝ (w:Space d) (normalizeToSphere w₀ v:Space d):ℂ)) := by
  have hi : inner ℝ (w:Space d) v =
      ‖v‖*inner ℝ (w:Space d) (normalizeToSphere w₀ v:Space d) := by
    nth_rw 1 [← norm_smul_normalizeToSphere w₀ v]
    rw [inner_smul_right]
  rw [sphereOscillator, hi]
  push_cast
  congr 1
  ring

theorem vectorSphereIntegral_eq_oscillation {d : ℕ} (w₀ : Sphere d)
    (r : ℝ) (v : Space d) (B : Sphere d → ℂ) :
    (∫ w, sphereOscillator r v w*B w ∂sphereMeasure d) =
      sphereOscillation (r*‖v‖) (normalizeToSphere w₀ v) B := by
  apply integral_congr_ae
  filter_upwards with w
  rw [sphereOscillator_normalized w₀]
  simp only [Complex.ofReal_mul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_OriginalAngularKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact original-point spherical kernel before the far decomposition -/

namespace Falconer
open Set MeasureTheory

theorem expandedCapTerm_spatial_kernel {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (v₁ v₂ : X → Space d) (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (b₁ b₂ : X → Sphere d → ℂ)
    (hb₁ : Measurable (Function.uncurry b₁)) (hb₂ : Measurable (Function.uncurry b₂))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x w, ‖b₁ x w‖ ≤ B₁) (hbound₂ : ∀ x w, ‖b₂ x w‖ ≤ B₂) :
    expandedCapTerm μ v Ψ v₁ v₂ b₁ b₂ =
      ∫ x, ∫ r,
        (∫ w, sphereOscillator r (v₁ x) w*b₁ x w ∂sphereMeasure d)*
        (∫ w, sphereOscillator r (v₂ x) w*b₂ x w ∂sphereMeasure d)
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ ∂μ := by
  have hm (u : X → Space d) (hu : Measurable u) (b : X → Sphere d → ℂ)
      (hb : Measurable (Function.uncurry b)) :
      Measurable (fun p : ℝ × X => ∫ w, sphereOscillator p.1 (u p.2) w*b p.2 w
        ∂sphereMeasure d) := by
    have hh : Measurable (fun p : (ℝ × X) × Sphere d =>
        sphereOscillator p.1.1 (u p.1.2) p.2*b p.1.2 p.2) := by
      apply Measurable.mul
      · unfold sphereOscillator
        fun_prop
      · exact hb.comp (measurable_fst.snd.prodMk measurable_snd)
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  have hbound (u : X → Space d) (b : X → Sphere d → ℂ) (C : ℝ)
      (hb : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (x : X) :
      ‖∫ w, sphereOscillator r (u x) w*b x w ∂sphereMeasure d‖ ≤
        C*(sphereMeasure d).real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards with w
    simpa only [norm_mul,sphereOscillator_norm,one_mul] using hb x w
  let G : ℝ × X → ℂ := fun p =>
    (∫ w, sphereOscillator p.1 (v₁ p.2) w*b₁ p.2 w ∂sphereMeasure d)*
    (∫ w, sphereOscillator p.1 (v₂ p.2) w*b₂ p.2 w ∂sphereMeasure d)
  have hG : Measurable G := (hm v₁ hv₁ b₁ hb₁).mul (hm v₂ hv₂ b₂ hb₂)
  have hi : Integrable G ((PlanarFalconer.sourceAngularShellMeasure v Ψ).prod μ) := by
    apply Integrable.of_bound hG.aestronglyMeasurable
      ((B₁*(sphereMeasure d).real univ)*(B₂*(sphereMeasure d).real univ))
    filter_upwards with p
    exact (norm_mul _ _).le.trans (mul_le_mul (hbound v₁ b₁ B₁ hbound₁ p.1 p.2)
      (hbound v₂ b₂ B₂ hbound₂ p.1 p.2) (norm_nonneg _) (by positivity))
  calc
    _ = ∫ r, ∫ x, G (r,x) ∂μ ∂PlanarFalconer.sourceAngularShellMeasure v Ψ := by
      apply integral_congr_ae
      filter_upwards with r
      exact angular_pair_spatial_swap μ r v₁ v₂ hv₁ hv₂ b₁ b₂ hb₁ hb₂ hB₁ hB₂ hbound₁ hbound₂
    _ = _ := integral_integral_swap hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CrossOriginalKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original four-point kernel for a mixed endpoint cross term -/

namespace Falconer
open Set MeasureTheory

theorem endpoint_cross_original_kernel {d : ℕ}
    (μ μ' ν ν' : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcB : ∀ x w, ‖c x w‖ ≤ B) :
    (∫ z, (endpointTransform μ M b z.1 z.2.1 * endpointTransform ν P c z.1 z.2.2) *
      star (endpointTransform μ' M b z.1 z.2.1 * endpointTransform ν' P c z.1 z.2.2)
      ∂angularProductMeasure d v Ψ) =
    ((M⁻¹*M⁻¹)*(P⁻¹*P⁻¹)) •
      ∫ z : (Space d × Space d) × (Space d × Space d), ∫ r,
        (∫ w, sphereOscillator r (z.1.1-z.1.2) w*(b z.1.1 w*star (b z.1.2 w))
          ∂sphereMeasure d)*
        (∫ w, sphereOscillator r (z.2.1-z.2.2) w*(c z.2.1 w*star (c z.2.2 w))
          ∂sphereMeasure d)
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ ∂(μ.prod μ').prod (ν.prod ν') := by
  have he := endpointCapCrossTerm_product_integral μ μ' ν ν' M M P P v Ψ
    hM hM hP hP b b c c hb hb hc hc (fun _ => 1) (fun _ => 1)
    measurable_const measurable_const (by intro; norm_num) (by intro; norm_num)
    hB hbB hbB hcB hcB
  simp only [Complex.ofReal_one,one_mul] at he
  rw [← he,endpointCapCrossTerm_four_point]
  let b₁ : ((Space d × Space d) × (Space d × Space d)) →
      Sphere d → ℂ := fun z w => b z.1.1 w*star (b z.1.2 w)
  let b₂ : ((Space d × Space d) × (Space d × Space d)) →
      Sphere d → ℂ := fun z w => c z.2.1 w*star (c z.2.2 w)
  have hb₁ : Measurable (Function.uncurry b₁) :=
    (hb.comp (measurable_fst.fst.fst.prodMk measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp
        (hb.comp (measurable_fst.fst.snd.prodMk measurable_snd)))
  have hb₂ : Measurable (Function.uncurry b₂) :=
    (hc.comp (measurable_fst.snd.fst.prodMk measurable_snd)).mul
      (Complex.continuous_conj.measurable.comp
        (hc.comp (measurable_fst.snd.snd.prodMk measurable_snd)))
  have hbound₁ (z) (w) : ‖b₁ z w‖ ≤ B^2 := by
    simpa only [b₁,norm_mul,norm_star,pow_two] using
      mul_le_mul (hbB z.1.1 w) (hbB z.1.2 w) (norm_nonneg _) hB
  have hbound₂ (z) (w) : ‖b₂ z w‖ ≤ B^2 := by
    simpa only [b₂,norm_mul,norm_star,pow_two] using
      mul_le_mul (hcB z.2.1 w) (hcB z.2.2 w) (norm_nonneg _) hB
  have h₁ : (fun z w => capPairAmplitude (fun _ => 1) b b z.1 w) = b₁ := by
    funext z w; simp only [capPairAmplitude,Complex.ofReal_one,one_mul,b₁]
  have h₂ : (fun z w => capPairAmplitude (fun _ => 1) c c z.2 w) = b₂ := by
    funext z w; simp only [capPairAmplitude,Complex.ofReal_one,one_mul,b₂]
  rw [h₁,h₂,expandedCapTerm_spatial_kernel _ v Ψ _ _ (by fun_prop) (by fun_prop)
    b₁ b₂ hb₁ hb₂ (sq_nonneg _) (sq_nonneg _) hbound₁ hbound₂]


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateEnvelope
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supremum of the factorized recursive angular states

The supremum varies the actual finite jets and the bounded smooth/spatial
multipliers. The displayed descriptor lists and all normalization data stay
fixed. Reached deletion maps each such symbol into the exact shorter list.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

theorem jetStateBound_nonneg {n : ℕ} (K : ℕ) (A : ℝ)
    (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) :
    0 ≤ jetStateBound K A μ ν M P a v Ψ := by
  unfold jetStateBound
  positivity

 theorem jetStateEnergy_bound {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D) :
    jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g ≤
      jetStateBound K A μ ν M P a v Ψ := by
  have hbase : 0 ≤ descriptorJetBound (n+2) K :=
    zero_le_one.trans (descriptorJetBound_one_le _ _)
  unfold jetStateBound
  apply independentAngularEnergy_bound a v Ψ
  · positivity
  · positivity
  · intro z
    exact endpointTransform_norm_le μ hM _ (f.value_norm_le Q ρ m N σ J i S hF hA) z.1 z.2
  · intro z
    exact endpointTransform_norm_le ν hP _ (g.value_norm_le Q ρ m N σ J i S hG hA) z.1 z.2

 theorem jetStateValues_bddAbove {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    BddAbove (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ) := by
  refine ⟨jetStateBound K A μ ν M P a v Ψ,?_⟩
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · exact jetStateBound_nonneg K A μ ν M P a v Ψ
  · exact jetStateEnergy_bound Q ρ m N σ J i S hF hG hA μ ν hM hP a v Ψ f g

 theorem jetStateEnergy_le_envelope {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f : DescriptorJetSymbol n K L F D) (g : DescriptorJetSymbol n K L G D) :
    jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g ≤
      jetStateEnvelope n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ :=
  le_csSup (jetStateValues_bddAbove Q ρ m N σ J i S hF hG hA μ ν hM hP a v Ψ)
    (Or.inr ⟨f,g,rfl⟩)

 theorem jetStateEnvelope_remove_reached {n K L : ℕ} {D : ℝ} (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (hQ : 0 < Q.side) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (X Y : List (Fin (n+2) → Bool))
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ ≤
    ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
      jetStateEnvelope n K L D
        (F.filter (fun b => X.length < descriptorAnchor b))
        (F.filter (fun b => Y.length < descriptorAnchor b))
        Q ρ m N σ J i S A
        (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ := by
  have hFX : ∀ b ∈ F.filter (fun b => X.length < descriptorAnchor b),
      ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z :=
    fun b hb => hF b (Finset.mem_filter.mp hb).1
  have hFY : ∀ b ∈ F.filter (fun b => Y.length < descriptorAnchor b),
      ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z :=
    fun b hb => hF b (Finset.mem_filter.mp hb).1
  apply csSup_le (show (jetStateValues n K L D F F Q ρ m N σ J i S A
    (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ).Nonempty
    from ⟨0,Or.inl rfl⟩)
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · have hzero : 0 ≤ jetStateEnvelope n K L D _ _ Q ρ m N σ J i S A
        (μ.restrict (Q.descendant X).carrier) (ν.restrict (Q.descendant Y).carrier) M P a v Ψ :=
      le_csSup (jetStateValues_bddAbove Q ρ m N σ J i S hFX hFY hA _ _ hM hP a v Ψ)
        (Or.inl rfl)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hzero
  · exact (f.energy_remove_reached g Q hQ ρ m N σ J i S hF hA X Y μ ν hM hP a v Ψ).trans
      (mul_le_mul_of_nonneg_left
        (jetStateEnergy_le_envelope Q ρ m N σ J i S hFX hFY hA _ _ hM hP a v Ψ _ _)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateCrossKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original four-point kernel for a single dyadic cross term -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem jetState_cross_original_kernel {m K L : ℕ} {Dq : ℝ}
    {F G : Finset PolicyDescriptor}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A)
    (μ μ' ν ν' : Measure (Space (m+3)))
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    (∫ z, (endpointTransform μ M (f.value Q ρ profile N σ J i S A) z.1 z.2.1 *
          endpointTransform ν P (g.value Q ρ profile N σ J i S A) z.1 z.2.2) *
        star (endpointTransform μ' M (f.value Q ρ profile N σ J i S A) z.1 z.2.1 *
          endpointTransform ν' P (g.value Q ρ profile N σ J i S A) z.1 z.2.2)
      ∂angularProductMeasure (m+3) v Ψ) =
      ((M⁻¹*M⁻¹)*(P⁻¹*P⁻¹)) •
        ∫ z, jetStateOriginalKernel f g w₀ Q ρ profile N σ J i S A A v Ψ z
          ∂(μ.prod μ').prod (ν.prod ν') := by
  have hB : 0 ≤ (descriptorJetBound (m+3) K)^K*A⁻¹ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hA.le)
  have h := endpoint_cross_original_kernel μ μ' ν ν' hM hP v Ψ
    (f.value Q ρ profile N σ J i S A) (g.value Q ρ profile N σ J i S A)
    (f.value_measurable Q ρ profile N σ J i S A)
    (g.value_measurable Q ρ profile N σ J i S A) hB
    (f.value_norm_le Q ρ profile N σ J i S hF hA)
    (g.value_norm_le Q ρ profile N σ J i S hG hA)
  apply h.trans
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  unfold jetStateOriginalKernel
  apply integral_congr_ae
  filter_upwards with r
  rw [vectorSphereIntegral_eq_oscillation w₀,vectorSphereIntegral_eq_oscillation w₀,
    dist_eq_norm,dist_eq_norm]

theorem dyadic_jetState_original_kernel {m K L : ℕ} {Dq : ℝ}
    {F G : Finset PolicyDescriptor}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    [IsFiniteMeasure ρ] (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (P₁ P₂ : DyadicCube (m+3))
    {M : ℝ} (hM : 0 < M) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (row col : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool)) :
    (∫ z, dyadicPairTransform P₁ P₂ ρ ρ M M
        (f.value Q ρ profile N σ J i S A) (g.value Q ρ profile N σ J i S A) row z *
      star (dyadicPairTransform P₁ P₂ ρ ρ M M
        (f.value Q ρ profile N σ J i S A) (g.value Q ρ profile N σ J i S A) col z)
      ∂angularProductMeasure (m+3) v Ψ) =
      ((M⁻¹*M⁻¹)*(M⁻¹*M⁻¹)) •
        ∫ z, jetStateOriginalKernel f g w₀ Q ρ profile N σ J i S A A v Ψ z
          ∂fourPointChildMeasure P₁ P₂ ρ ρ (row.1,col.1) (row.2,col.2) :=
  jetState_cross_original_kernel f g w₀ Q ρ profile N σ J i S hF hG hA
    _ _ _ _ hM hM v Ψ

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateChildren
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual graph children in the factorized angular envelope -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

 theorem childJetStateMaximum_nonneg (n K L : ℕ) (D : ℝ) (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (X Y : List (Fin (n+2) → Bool)) (j : ℕ) (M a v : ℝ) (Ψ : ℝ → ℝ) :
    0 ≤ childJetStateMaximum n K L D F Q ρ m N σ J i S A X Y j M a v Ψ :=
  finiteEnvelopeMaximum_nonneg _ _

 theorem childJetStateEnvelope_le {n K L : ℕ} (D : ℝ) (F : Finset PolicyDescriptor)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (X Y : List (Fin (n+2) → Bool)) (j : ℕ) (M a v : ℝ) (Ψ : ℝ → ℝ)
    (row : List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool))
    (hrow : row ∈ (Q.descendant X).occupiedPaths ρ j ×ˢ (Q.descendant Y).occupiedPaths ρ j) :
    jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) M M a v Ψ ≤
    childJetStateMaximum n K L D F Q ρ m N σ J i S A X Y j M a v Ψ := by
  let V : (List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool)) → ℝ := fun c =>
    jetStateEnvelope n K L D F F Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant c.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant c.2).carrier) M M a v Ψ
  let T := (Q.descendant X).occupiedPaths ρ j ×ˢ (Q.descendant Y).occupiedPaths ρ j
  change V row ≤ sSup (insert 0 (V '' (T : Set _)))
  apply le_csSup ((T.finite_toSet.image V).insert 0).bddAbove
  exact Or.inr ⟨row,hrow,rfl⟩

 theorem childJetStateEnergy_le {n K L : ℕ} {D : ℝ} {F : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (hQ : 0 < Q.side)
    (ρ : Measure (Space (n+2))) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) {a p : ℕ} (hap : a ≤ p)
    (X Y : List (Fin (n+2) → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (row : List (Fin (n+2) → Bool) × List (Fin (n+2) → Bool))
    (hrow : row ∈ (Q.descendant X).occupiedPaths ρ (p-a) ×ˢ
      (Q.descendant Y).occupiedPaths ρ (p-a))
    {M : ℝ} (hM : 0 < M) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f g : DescriptorJetSymbol n K L F D) :
    jetStateEnergy Q ρ m N σ J i S A
      (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
      (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) M M p v Ψ f g ≤
    ((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
      childJetStateMaximum n K L D (F.filter (fun b => p < descriptorAnchor b))
        Q ρ m N σ J i S A X Y (p-a) M p v Ψ := by
  have hx := Finset.mem_product.mp hrow
  have hxlen : (X++row.1).length = p := by
    rw [List.length_append,hX,(mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hx.1).1]
    omega
  have hylen : (Y++row.2).length = p := by
    rw [List.length_append,hY,(mem_cubePaths _ _ _).mp (Finset.mem_filter.mp hx.2).1]
    omega
  have hstart := jetStateEnergy_le_envelope Q ρ m N σ J i S hF hF hA
    (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
    (ρ.restrict ((Q.descendant Y).descendant row.2).carrier) hM hM p v Ψ f g
  have hremove := jetStateEnvelope_remove_reached (K := K) (L := L) (D := D) F Q hQ ρ m N σ J i S hF hA
    (X++row.1) (Y++row.2) ρ ρ hM hM p v Ψ
  simp only [Q.descendant_append,hxlen,hylen] at hremove
  apply (hstart.trans hremove).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact childJetStateEnvelope_le D (F.filter (fun b => p < descriptorAnchor b))
    Q ρ m N σ J i S A X Y (p-a) M p v Ψ row hrow

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateNear
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Near and terminal bounds for the exact factorized angular states -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open PlanarFalconer (PolicyDescriptor descriptorAnchor)

 theorem profile_near_jetState {n K L : ℕ} {D : ℝ} {F : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (hQ : Q.side = 1) (ρ : Measure (Space (n+2)))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : List (Fin (n+2) → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (f g : DescriptorJetSymbol n K L F D) :
    profileNearEnergy (Q.descendant X) (Q.descendant Y) ρ m N a p v Ψ
      (f.value Q ρ (fun t => m (t/N)) N σ J i S A)
      (g.value Q ρ (fun t => m (t/N)) N σ J i S A) ≤
    ((2*(10*((n+2)+1))+1)^(2*(n+2)):ℕ) *
      ((2:ℝ)^N)^(-2*(profileExcess (d := n+2) m N p-profileExcess (d := n+2) m N a)+
        4*(((n+2:ℕ):ℝ)+1)*lam)*
      (((descriptorJetBound (n+2) K)^K)^2 * ((descriptorJetBound (n+2) K)^K)^2 *
        childJetStateMaximum n K L D (F.filter (fun b => p < descriptorAnchor b))
          Q ρ (fun t => m (t/N)) N σ J i S A X Y (p-a) (profileModelMass m N p) p v Ψ) := by
  let := hreg.probability
  have hbase : 0 ≤ descriptorJetBound (n+2) K := zero_le_one.trans (descriptorJetBound_one_le _ _)
  have hbound : 0 ≤ (descriptorJetBound (n+2) K)^K*A⁻¹ := by positivity
  have hMp : 0 < profileModelMass m N p := by unfold profileModelMass; positivity
  have hchild0 : 0 ≤ ((descriptorJetBound (n+2) K)^K)^2 *
      ((descriptorJetBound (n+2) K)^K)^2 *
        childJetStateMaximum n K L D (F.filter (fun b => p < descriptorAnchor b))
          Q ρ (fun t => m (t/N)) N σ J i S A X Y (p-a) (profileModelMass m N p) p v Ψ :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (childJetStateMaximum_nonneg n K L D _ Q ρ _ N σ J i S A X Y (p-a) _ p v Ψ)
  apply profile_near_reduction Q hQ ρ hreg hN hap hp X Y hX hY v Ψ
    (f.value Q ρ (fun t => m (t/N)) N σ J i S A)
    (g.value Q ρ (fun t => m (t/N)) N σ J i S A)
    (f.value_measurable _ _ _ _ _ _ _ _ _) (g.value_measurable _ _ _ _ _ _ _ _ _)
    hbound hbound
    hchild0
    (f.value_norm_le _ _ _ _ _ _ _ _ hF hA) (g.value_norm_le _ _ _ _ _ _ _ _ hF hA)
  intro row hrow
  exact childJetStateEnergy_le Q (by rw [hQ]; norm_num) ρ (fun t => m (t/N))
    N σ J i S hF hA hap X Y hX hY row hrow hMp v Ψ f g

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateNearFar
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The near/far decomposition for actual recursive angular states

All descriptor factors remain in the far integrals. The intermediate
child model masses cancel exactly when these integrals are opened.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
attribute [local instance] Classical.propDecidable

 theorem jetState_energy_near_far {m K L : ℕ} {Dq : ℝ}
    {F G : Finset PolicyDescriptor}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    [IsFiniteMeasure ρ] (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (P₁ P₂ : DyadicCube (m+3))
    (a h : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    jetStateEnergy Q ρ (fun s => profile (s/N)) N σ J i S A
      (ρ.restrict P₁.carrier) (ρ.restrict P₂.carrier)
      (profileModelMass profile N a) (profileModelMass profile N a) a v Ψ f g ≤
    profileNearEnergy P₁ P₂ ρ profile N a h v Ψ
      (f.value Q ρ (fun s => profile (s/N)) N σ J i S A)
      (g.value Q ρ (fun s => profile (s/N)) N σ J i S A) +
    ((2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*(profileModelMass profile N a)⁻¹^4)*
      ∑ row ∈ P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a),
        ∑ col ∈ P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a),
          if nearDyadicEdge P₁ P₂ (10*(((m+3:ℕ):ℝ)+1)/(2:ℝ)^h) row col then 0 else
            ‖∫ z, jetStateOriginalKernel f g w₀ Q ρ (fun s => profile (s/N)) N σ J i S A A v Ψ z
              ∂fourPointChildMeasure P₁ P₂ ρ ρ (row.1,col.1) (row.2,col.2)‖ := by
  let Ma := profileModelMass profile N a
  let Mh := profileModelMass profile N h
  let V := P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a)
  let b := f.value Q ρ (fun s => profile (s/N)) N σ J i S A
  let c := g.value Q ρ (fun s => profile (s/N)) N σ J i S A
  have hB : 0 ≤ (descriptorJetBound (m+3) K)^K*A⁻¹ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hA.le)
  have hMa : 0 < Ma := by dsimp [Ma,profileModelMass]; positivity
  have hMh : 0 < Mh := by dsimp [Mh,profileModelMass]; positivity
  have hs := profile_energy_near_far P₁ P₂ ρ profile N a h v Ψ b c
    (f.value_measurable _ _ _ _ _ _ _ _ _) (g.value_measurable _ _ _ _ _ _ _ _ _) hB
    (f.value_norm_le _ _ _ _ _ _ _ _ hF hA) (g.value_norm_le _ _ _ _ _ _ _ _ hG hA)
  have hweight : 0 ≤ (Mh⁻¹*Mh⁻¹)*(Mh⁻¹*Mh⁻¹) := by positivity
  have hterm (row col : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool)) :
      ‖∫ z, dyadicPairTransform P₁ P₂ ρ ρ Mh Mh b c row z *
        star (dyadicPairTransform P₁ P₂ ρ ρ Mh Mh b c col z)
        ∂angularProductMeasure (m+3) v Ψ‖ =
      ((Mh⁻¹*Mh⁻¹)*(Mh⁻¹*Mh⁻¹))*
        ‖∫ z, jetStateOriginalKernel f g w₀ Q ρ (fun s => profile (s/N)) N σ J i S A A v Ψ z
          ∂fourPointChildMeasure P₁ P₂ ρ ρ (row.1,col.1) (row.2,col.2)‖ := by
    rw [dyadic_jetState_original_kernel f g w₀ Q ρ (fun s => profile (s/N)) N σ J i S
      hF hG hA P₁ P₂ hMh v Ψ row col,norm_smul,Real.norm_eq_abs,abs_of_nonneg hweight]
  have hsum :
      (∑ row ∈ V, ∑ col ∈ V,
        if nearDyadicEdge P₁ P₂ (10*(((m+3:ℕ):ℝ)+1)/(2:ℝ)^h) row col then 0 else
          ‖∫ z, dyadicPairTransform P₁ P₂ ρ ρ Mh Mh b c row z *
            star (dyadicPairTransform P₁ P₂ ρ ρ Mh Mh b c col z)
            ∂angularProductMeasure (m+3) v Ψ‖) =
      ((Mh⁻¹*Mh⁻¹)*(Mh⁻¹*Mh⁻¹))*
      ∑ row ∈ V, ∑ col ∈ V,
        if nearDyadicEdge P₁ P₂ (10*(((m+3:ℕ):ℝ)+1)/(2:ℝ)^h) row col then 0 else
          ‖∫ z, jetStateOriginalKernel f g w₀ Q ρ (fun s => profile (s/N)) N σ J i S A A v Ψ z
            ∂fourPointChildMeasure P₁ P₂ ρ ρ (row.1,col.1) (row.2,col.2)‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro row _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro col _
    by_cases hn : nearDyadicEdge P₁ P₂ (10*(((m+3:ℕ):ℝ)+1)/(2:ℝ)^h) row col
    · simp only [ite_eq_left hn,mul_zero]
    · simpa only [ite_eq_right hn] using hterm row col
  have hcancel : ((Mh/Ma)^4*(2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)))*
      ((Mh⁻¹*Mh⁻¹)*(Mh⁻¹*Mh⁻¹)) =
      (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*Ma⁻¹^4 := by
    field_simp
  change _ ≤ _ + ((Mh/Ma)^4*(2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)))*_ at hs
  rw [hsum,← mul_assoc,hcancel] at hs
  exact hs

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_JetStateFarOriginal
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual angular energy bounded on the reassembled original far law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
attribute [local instance] Classical.propDecidable

 theorem jetState_energy_near_original_far {m K L a h : ℕ} {Dq : ℝ}
    {F G : Finset PolicyDescriptor}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (hQ : Q.side = 1)
    (ρ : Measure (Space (m+3))) [IsFiniteMeasure ρ]
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (hah : a ≤ h)
    (X Y : List (Fin (m+3) → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    ENNReal.ofReal (jetStateEnergy Q ρ (fun s => profile (s/N)) N σ J i S A
      (ρ.restrict (Q.descendant X).carrier) (ρ.restrict (Q.descendant Y).carrier)
      (profileModelMass profile N a) (profileModelMass profile N a) a v Ψ f g) ≤
    ENNReal.ofReal (profileNearEnergy (Q.descendant X) (Q.descendant Y) ρ profile N a h v Ψ
      (f.value Q ρ (fun s => profile (s/N)) N σ J i S A)
      (g.value Q ρ (fun s => profile (s/N)) N σ J i S A)) +
    ENNReal.ofReal ((2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*(profileModelMass profile N a)⁻¹^4)*
      ∫⁻ z in farDisplacementRegion (m+3) a h,
        ENNReal.ofReal ‖jetStateOriginalKernel f g w₀ Q ρ (fun s => profile (s/N))
          N σ J i S A A v Ψ z‖
        ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ := by
  let V := (Q.descendant X).occupiedPaths ρ (h-a) ×ˢ (Q.descendant Y).occupiedPaths ρ (h-a)
  let kernel := jetStateOriginalKernel f g w₀ Q ρ (fun s => profile (s/N)) N σ J i S A A v Ψ
  let near := nearDyadicEdge (Q.descendant X) (Q.descendant Y)
    (10*(((m+3:ℕ):ℝ)+1)/(2:ℝ)^h)
  have hterm (row col : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool)) :
      0 ≤ if near row col then 0 else ‖∫ z, kernel z
        ∂fourPointChildMeasure (Q.descendant X) (Q.descendant Y) ρ ρ
          (row.1,col.1) (row.2,col.2)‖ := by split_ifs <;> positivity
  have hsum : ENNReal.ofReal (∑ row ∈ V, ∑ col ∈ V,
      if near row col then 0 else ‖∫ z, kernel z
        ∂fourPointChildMeasure (Q.descendant X) (Q.descendant Y) ρ ρ
          (row.1,col.1) (row.2,col.2)‖) ≤
    ∑ row ∈ V, ∑ col ∈ V, if near row col then 0 else
      ∫⁻ z, ENNReal.ofReal ‖kernel z‖
        ∂fourPointChildMeasure (Q.descendant X) (Q.descendant Y) ρ ρ
          (row.1,col.1) (row.2,col.2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun row _ => Finset.sum_nonneg (fun col _ => hterm row col))]
    apply Finset.sum_le_sum
    intro row _
    rw [ENNReal.ofReal_sum_of_nonneg (fun col _ => hterm row col)]
    apply Finset.sum_le_sum
    intro col _
    by_cases hn : near row col
    · simp only [ite_eq_left hn,ENNReal.ofReal_zero,le_refl]
    · simp only [ite_eq_right hn]
      simpa only [← ofReal_norm] using
        (enorm_integral_le_lintegral_enorm (μ := fourPointChildMeasure
          (Q.descendant X) (Q.descendant Y) ρ ρ (row.1,col.1) (row.2,col.2)) kernel)
  have hfar := originalFourPoint_far_rows_le Q hQ ρ hah X Y hX hY
    (fun z => ENNReal.ofReal ‖kernel z‖)
  have hc : 0 ≤ (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*(profileModelMass profile N a)⁻¹^4 := by positivity
  have hn : 0 ≤ profileNearEnergy (Q.descendant X) (Q.descendant Y) ρ profile N a h v Ψ
      (f.value Q ρ (fun s => profile (s/N)) N σ J i S A)
      (g.value Q ρ (fun s => profile (s/N)) N σ J i S A) := by
    unfold profileNearEnergy
    positivity
  have hb := ENNReal.ofReal_le_ofReal (jetState_energy_near_far f g w₀ Q ρ profile N σ J i S
    hF hG hA (Q.descendant X) (Q.descendant Y) a h v Ψ)
  have hsum0 := Finset.sum_nonneg (fun row (_ : row ∈ V) =>
    Finset.sum_nonneg (fun col (_ : col ∈ V) => hterm row col))
  rw [ENNReal.ofReal_add hn (mul_nonneg hc hsum0),ENNReal.ofReal_mul hc] at hb
  exact hb.trans (add_le_add le_rfl (mul_le_mul' le_rfl (hsum.trans hfar)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarData
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric data for the actual far branch

These are scale and descriptor conditions to be verified by the recursive
policy. They are not additional published inputs.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

theorem base_one (D : JetStateFarData m B) : 1 ≤ (2:ℝ)^D.N := one_le_pow₀ (by norm_num)

end JetStateFarData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_FarAngularStep
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The conditional angular far branch, with the actual near child

This is the analytic far step of the recursive argument. Its inputs are
geometric scale data; only the cited gnomonic and quadratic stationary
results are published hypotheses.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

 theorem exists_far_angular_step
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M q : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C Cerr : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ 0 ≤ Cerr ∧
      ∀ (D : JetStateFarData m B), D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss →
      ∀ (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3)),
      ENNReal.ofReal (D.energy f g Ψ) ≤ ENNReal.ofReal (D.nearBound K L Ψ) +
        (∑ b ∈ Finset.Icc (D.a+9) (D.h+6), D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b) +
        ENNReal.ofReal D.prefactor *
          (2+((Finset.Icc (D.a+9) (D.h+6)).card:ℝ≥0∞)) *
          ENNReal.ofReal (Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss))*D.originalMeasure univ := by
  obtain ⟨B,C,Cerr,hB,hC,hCerr,hfar⟩ := exists_far_data_bound hgnomonic hquadratic
    m K L M q hM hML hΨ hpos hs hW hΨW
  refine ⟨B,C,Cerr,hB,hC,hCerr,?_⟩
  intro D hloss horder f g w₀
  let := D.regular.probability
  have htail (s : ℝ) (hs4 : 4 < s) : Ψ s = 0 := by
    by_contra hn
    have hh := (hs s hn).2
    linarith
  let := PlanarFalconer.sourceAngularShellMeasure_finite (D.t:ℝ) Ψ hW hΨW htail
  have hnear := profile_near_jetState D.Q D.unit D.ρ D.regular D.N_pos D.σ D.J D.i
    D.masks D.separated D.Z_pos D.ah (show D.h ≤ D.N by have := D.ht; have := D.tN; omega)
    D.X D.Y D.X_length D.Y_length D.t Ψ f g
  have hfull := jetState_energy_near_original_far f g w₀ D.Q D.unit D.ρ D.profile D.N D.σ
    D.J D.i D.masks D.separated D.separated D.Z_pos D.ah D.X D.Y D.X_length D.Y_length D.t Ψ
  have he := hfull.trans (add_le_add (ENNReal.ofReal_le_ofReal hnear)
    (hfar D hloss horder f g w₀))
  simpa only [JetStateFarData.energy,JetStateFarData.nearBound,JetStateFarData.prefactor,
    JetStateFarData.originalMeasure,JetStateFarData.kernel,add_assoc,Nat.reduceAdd] using he

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_InheritedPolicyState
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

 theorem remainingPolicyDescriptors_drop (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ} (hap : a ≤ p) :
    (remainingPolicyDescriptors A N q a₀ t₀ a).filter (fun d => p < descriptorAnchor d) =
      remainingPolicyDescriptors A N q a₀ t₀ p := by
  ext d
  simp only [remainingPolicyDescriptors,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,hap.trans_lt h.2⟩,h.2⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarEnvelope
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The far reduction for the full recursive symbol supremum -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

theorem envelope_le_of_energy_le (D : JetStateFarData m B) (K L : ℕ) (Ψ : ℝ → ℝ)
    {H : ℝ≥0∞} (h : ∀ f g : DescriptorJetSymbol (m+1) K L D.F D.Dq,
      ENNReal.ofReal (D.energy f g Ψ) ≤ H) : ENNReal.ofReal (D.envelope K L Ψ) ≤ H := by
  by_cases htop : H = ⊤
  · simp only [htop,le_top]
  apply ENNReal.ofReal_le_of_le_toReal
  apply csSup_le (show (jetStateValues (m+1) K L D.Dq D.F D.F D.Q D.ρ
      (fun t => D.profile (t/D.N)) D.N D.σ D.J D.i D.masks D.Z
      (D.ρ.restrict (D.Q.descendant D.X).carrier) (D.ρ.restrict (D.Q.descendant D.Y).carrier)
      (profileModelMass D.profile D.N D.a) (profileModelMass D.profile D.N D.a)
      D.a D.t Ψ).Nonempty from ⟨0,Or.inl rfl⟩)
  intro r hr
  rcases hr with rfl | ⟨f,g,rfl⟩
  · exact ENNReal.toReal_nonneg
  · exact (ENNReal.ofReal_le_iff_le_toReal htop).mp (h f g)

end JetStateFarData

theorem exists_far_envelope_step
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M q : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C Cerr : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ 0 ≤ Cerr ∧
      ∀ (D : JetStateFarData m B), D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss → ∀ w₀ : Sphere (m+3),
      ENNReal.ofReal (D.envelope K L Ψ) ≤ ENNReal.ofReal (D.nearBound K L Ψ) +
        (∑ b ∈ Finset.Icc (D.a+9) (D.h+6), D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b) +
        D.farError K Cerr := by
  obtain ⟨B,C,Cerr,hB,hC,hCerr,hstep⟩ := exists_far_angular_step hgnomonic hquadratic
    m K L M q hM hML hΨ hpos hs hW hΨW
  refine ⟨B,C,Cerr,hB,hC,hCerr,?_⟩
  intro D hloss horder w₀
  apply D.envelope_le_of_energy_le
  intro f g
  exact hstep D hloss horder f g w₀

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_ProfileGraphBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The model masses pay for both graph errors

The child masses cancel before estimating. Only the two parent profile
values remain, so the combined normalization costs at most R^(5d).
-/

namespace Falconer

theorem graph_error_mass_cancellation {M₁ M₂ U₁ U₂ : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) :
    ((U₁/M₁)*(U₂/M₂))^2 * |(U₁⁻¹*U₁⁻¹)*(U₂⁻¹*U₂⁻¹)| =
      (M₁⁻¹)^2*(M₂⁻¹)^2 := by
  rw [abs_of_pos (by positivity)]
  field_simp

theorem profile_graph_error_weight_bound (d : ℕ) {N a p : ℕ}
    (hN : 0 < N) (m₁ m₂ : ℝ → ℝ) {v : ℝ} (hv : v ≤ N)
    (hm₁ : m₁ ((a:ℝ)/N) ≤ d) (hm₂ : m₂ ((a:ℝ)/N) ≤ d) :
    (2:ℝ)^((d:ℝ)*(v-a)) *
        ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
          (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        |((profileModelMass m₁ N p)⁻¹*(profileModelMass m₁ N p)⁻¹)*
          ((profileModelMass m₂ N p)⁻¹*(profileModelMass m₂ N p)⁻¹)| ≤
      ((2:ℝ)^N)^(5*(d:ℝ)) := by
  have hM (m : ℝ → ℝ) (j : ℕ) : 0 < profileModelMass m N j := by
    unfold profileModelMass
    positivity
  have hR : 0 < (2:ℝ)^N := by positivity
  have hRone : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hm (m : ℝ → ℝ) : ((profileModelMass m N a)⁻¹)^2 =
      ((2:ℝ)^N)^(2*m ((a:ℝ)/N)) := by
    unfold profileModelMass
    rw [← Real.rpow_neg hR.le,← Real.rpow_natCast,← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [mul_assoc,graph_error_mass_cancellation (hM m₁ a) (hM m₂ a) (hM m₁ p) (hM m₂ p),
    hm m₁,hm m₂,← dyadic_rpow_change_base hN ((d:ℝ)*(v-a)),
    ← mul_assoc,← Real.rpow_add hR,← Real.rpow_add hR]
  apply Real.rpow_le_rpow_of_exponent_le hRone
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hfrac : (d:ℝ)*(v-a)/N ≤ d := by
    apply (div_le_iff₀ hNR).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d,Nat.cast_nonneg (α := ℝ) a]
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarError
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The uniform original-law remainder in the far reduction -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

 theorem originalMeasure_mass_le_one (D : JetStateFarData m B) : D.originalMeasure univ ≤ 1 := by
  let := D.regular.probability
  have hprod (Z : List (Fin (m+3) → Bool)) :
      ((D.ρ.restrict (D.Q.descendant Z).carrier).prod
        (D.ρ.restrict (D.Q.descendant Z).carrier)) univ =
      D.ρ (D.Q.descendant Z).carrier*D.ρ (D.Q.descendant Z).carrier := by
    rw [← univ_prod_univ,Measure.prod_prod,Measure.restrict_apply_univ]
  unfold originalMeasure originalFourPointMeasure
  rw [← univ_prod_univ,Measure.prod_prod,hprod,hprod]
  have hx : D.ρ (D.Q.descendant D.X).carrier ≤ 1 :=
    (measure_mono (subset_univ _)).trans_eq (measure_univ : D.ρ univ = 1)
  have hy : D.ρ (D.Q.descendant D.Y).carrier ≤ 1 :=
    (measure_mono (subset_univ _)).trans_eq (measure_univ : D.ρ univ = 1)
  calc
    _ ≤ (1*1)*(1*1) := mul_le_mul' (mul_le_mul' hx hx) (mul_le_mul' hy hy)
    _ = 1 := by norm_num

 theorem prefactor_bound (D : JetStateFarData m B) :
    D.prefactor ≤ ((2:ℝ)^D.N)^(5*((m+3:ℕ):ℝ)) := by
  have ha : D.a ≤ D.N := by have := D.ah; have := D.ht; have := D.tN; omega
  have hprofile : D.profile ((D.a:ℝ)/D.N) ≤ (m+3:ℕ) :=
    (D.regular.range _ ⟨by positivity,(div_le_one (Nat.cast_pos.mpr D.N_pos)).mpr (Nat.cast_le.mpr ha)⟩).2
  have hp := profile_graph_error_weight_bound (m+3) (a := D.a) (p := D.a) D.N_pos
    D.profile D.profile (Nat.cast_le.mpr D.tN) hprofile hprofile
  have hm : profileModelMass D.profile D.N D.a ≠ 0 := by unfold profileModelMass; positivity
  have habs : |(profileModelMass D.profile D.N D.a)⁻¹*(profileModelMass D.profile D.N D.a)⁻¹*
      ((profileModelMass D.profile D.N D.a)⁻¹*(profileModelMass D.profile D.N D.a)⁻¹)| =
      (profileModelMass D.profile D.N D.a)⁻¹^4 := by
    rw [abs_of_nonneg (by unfold profileModelMass; positivity)]
    ring
  simpa only [prefactor,div_self hm,mul_one,one_mul,one_pow,habs] using hp

 theorem band_count_le (D : JetStateFarData m B) :
    2+(Finset.Icc (D.a+9) (D.h+6)).card ≤ D.N+3 := by
  rw [Nat.card_Icc]
  have := D.ht
  have := D.tN
  omega

 theorem farError_bound (D : JetStateFarData m B) (K : ℕ) {Cerr : ℝ} (hC : 0 ≤ Cerr) :
    D.farError K Cerr ≤ ENNReal.ofReal
      ((D.N+3:ℕ)*Cerr*(B^K*D.Z⁻¹)^4*
        ((2:ℝ)^D.N)^(5*((m+3:ℕ):ℝ)-D.loss)) := by
  have hcount : (2+(Finset.Icc (D.a+9) (D.h+6)).card:ℝ≥0∞) ≤ (D.N+3:ℕ) := by
    exact_mod_cast D.band_count_le
  have hpf := ENNReal.ofReal_le_ofReal D.prefactor_bound
  have hc : 0 ≤ Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss) := by positivity
  calc
    D.farError K Cerr ≤ ENNReal.ofReal (((2:ℝ)^D.N)^(5*((m+3:ℕ):ℝ))) *
        (D.N+3:ℕ)*ENNReal.ofReal (Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss))*1 :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' hpf hcount) le_rfl) D.originalMeasure_mass_le_one
    _ = _ := by
      rw [mul_one,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.rpow_sub (by positivity : 0 < (2:ℝ)^D.N),Real.rpow_neg (by positivity : 0 ≤ (2:ℝ)^D.N)]
      ring

end JetStateFarData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FarErrorOrder
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed truncation orders and arbitrary-power far remainders -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

 theorem exists_far_truncation_orders (m : ℕ) {σ loss : ℝ}
    (hσ : 0 < σ) : ∃ M q : ℕ, 1 ≤ M ∧
      loss ≤ (16*σ)*(((m+2:ℕ):ℝ)/2+(q:ℝ)) ∧
      -(16*σ)*(M:ℝ)+2*(m+3) ≤ -loss := by
  obtain ⟨j,hj⟩ := exists_nat_ge ((loss+2*(m+3))/(16*σ))
  obtain ⟨q,hq⟩ := exists_nat_ge (loss/(16*σ))
  have hj' := (div_le_iff₀ (by positivity : 0 < 16*σ)).mp hj
  have hq' := (div_le_iff₀ (by positivity : 0 < 16*σ)).mp hq
  refine ⟨j+1,q,by omega,?_,?_⟩
  · have hm : 0 ≤ (16*σ)*((m+2:ℕ):ℝ)/2 := by positivity
    nlinarith
  · push_cast
    nlinarith

 theorem eventual_far_error_absorbed (m K : ℕ) {B Cerr ε : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ Cerr) (hε : 0 < ε) (T : ℝ) :
    ∃ N₀ : ℕ, ∀ (D : JetStateFarData m B), N₀ ≤ D.N → 1 ≤ D.Z →
      T+5*((m+3:ℕ):ℝ)+ε ≤ D.loss →
      D.farError K Cerr ≤ ENNReal.ofReal (((2:ℝ)^D.N)^(-T)) := by
  obtain ⟨N₁,hpoly⟩ := PlanarFalconer.fixed_polynomial_subpower 1 (half_pos hε)
  obtain ⟨N₂,hconst⟩ := Regularization.fixed_constant_absorbed (half_pos hε)
    (Cerr*(B^K)^4)
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro D hN hZ hloss
  have hNpos : 1 ≤ D.N := (le_max_left _ _).trans hN
  have hp := hpoly D.N ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hc := hconst D.N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hR : 1 ≤ (2:ℝ)^D.N := D.base_one
  have hRp : 0 < (2:ℝ)^D.N := by positivity
  have hpoly' : ((D.N+3:ℕ):ℝ) ≤ ((2:ℝ)^D.N)^(ε/2) := by
    apply (show ((D.N+3:ℕ):ℝ) ≤ 4*(D.N:ℝ)+1 from ?_).trans
      (by simpa only [pow_one] using hp)
    push_cast
    have hn : (1:ℝ) ≤ D.N := by exact_mod_cast hNpos
    linarith
  have hcoeff : ((D.N+3:ℕ):ℝ)*Cerr*(B^K)^4 ≤ ((2:ℝ)^D.N)^ε := by
    calc
      _ = ((D.N+3:ℕ):ℝ)*(Cerr*(B^K)^4) := by ring
      _ ≤ ((2:ℝ)^D.N)^(ε/2)*((2:ℝ)^D.N)^(ε/2) :=
        mul_le_mul hpoly' hc (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hRp]; congr 1; ring
  have hz : D.Z⁻¹ ≤ 1 := (inv_le_one₀ D.Z_pos).mpr hZ
  have hb : (B^K*D.Z⁻¹)^4 ≤ (B^K)^4 := by
    apply pow_le_pow_left₀ (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz
      (pow_nonneg (zero_le_one.trans hB) K)
  apply (D.farError_bound K hC).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((D.N+3:ℕ):ℝ)*Cerr*(B^K)^4 *
        ((2:ℝ)^D.N)^(5*((m+3:ℕ):ℝ)-D.loss) := by gcongr
    _ ≤ ((2:ℝ)^D.N)^ε*((2:ℝ)^D.N)^(5*((m+3:ℕ):ℝ)-D.loss) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = ((2:ℝ)^D.N)^(ε+5*((m+3:ℕ):ℝ)-D.loss) := by
      rw [← Real.rpow_add hRp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hR (by linarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyFarStep
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual policy far reduction with an arbitrary-power error -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

theorem exists_policy_far_step
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K : ℕ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∃ (B C : ℝ) (N₀ : ℕ), 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (P : PolicyJetData m), P.σ = σ → N₀ ≤ P.N →
      P.a < P.splitDepth → 1 ≤ P.Z → ∀ w₀ : Sphere (m+3),
      ENNReal.ofReal (P.envelope K L Ψ) ≤ ENNReal.ofReal (P.nearBound K L Ψ) +
        (∑ b ∈ Finset.Icc (P.a+9) (P.splitDepth+6),
          P.collisionTerm w₀ (C*(B^K*P.Z⁻¹)^4) b) +
        ENNReal.ofReal (((2:ℝ)^P.N)^(-T)) := by
  let loss := T+5*((m+3:ℕ):ℝ)+1
  have hloss : 0 ≤ loss := by dsimp [loss]; positivity
  obtain ⟨M,q,hM,hnc,horder⟩ := exists_far_truncation_orders m (loss := loss) hσ
  refine ⟨2*M+(m+2)+1,?_⟩
  intro L hML
  obtain ⟨B,C,Cerr,hB,hC,hCerr,hstep⟩ := exists_far_envelope_step hgnomonic hquadratic
    m K L M q hM hML hΨ hpos hs hW hΨW
  obtain ⟨Nerr,herr⟩ := eventual_far_error_absorbed m K hB hCerr (by norm_num : (0:ℝ) < 1) T
  let Nscale := PolicyJetData.farThreshold B σ hB hσ hσ1 m
  refine ⟨B,C,max Nerr Nscale,hB,hC,?_⟩
  intro P hσP hN hfar hZ w₀
  have hpσ : 0 < P.σ := by simpa only [hσP] using hσ
  have hpσ1 : P.σ ≤ 1 := by simpa only [hσP] using hσ1
  have hNscale : PolicyJetData.farThreshold B P.σ hB hpσ hpσ1 m ≤ P.N := by
    simpa only [hσP] using (le_max_right Nerr Nscale).trans hN
  let D := P.farData B hB hpσ hpσ1 hNscale hfar loss hloss
  have hncD : D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) := by
    change loss ≤ (16*P.σ)*_
    simpa only [hσP] using hnc
  have horderD : -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss := by
    change -(16*P.σ)*(M:ℝ)+2*(m+3) ≤ -loss
    simpa only [hσP] using horder
  have he := herr D ((le_max_left Nerr Nscale).trans hN) hZ
    (show T+5*((m+3:ℕ):ℝ)+1 ≤ D.loss from le_refl _)
  have hresult := (hstep D hncD horderD w₀).trans (add_le_add le_rfl he)
  change ENNReal.ofReal (P.envelope K L Ψ) ≤ _ at hresult
  exact hresult

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_PolicyJetChildren
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual policy states at the child cells of an angular step -/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

namespace PolicyJetData
variable {m : ℕ}

theorem child_envelope (P : PolicyJetData m) (K L p : ℕ) (hap : P.a ≤ p)
    (row : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool))
    (hrow : row ∈ (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
      (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a)) (Ψ : ℝ → ℝ) :
    (P.child p hap row hrow).envelope K L Ψ =
      jetStateEnvelope (m+1) K L 1
        (P.list.filter (fun b => p < PlanarFalconer.descriptorAnchor b))
        (P.list.filter (fun b => p < PlanarFalconer.descriptorAnchor b))
        P.Q P.ρ (fun t => P.profile (t/P.N)) P.N P.σ P.J P.i P.masks P.Z
        (P.ρ.restrict ((P.Q.descendant P.X).descendant row.1).carrier)
        (P.ρ.restrict ((P.Q.descendant P.Y).descendant row.2).carrier)
        (profileModelMass P.profile P.N p) (profileModelMass P.profile P.N p) p P.t Ψ := by
  simp only [envelope,child,list,DyadicCube.descendant_append,
    PlanarFalconer.remainingPolicyDescriptors_drop P.policy P.N P.q P.a₀ P.t₀ hap]

theorem graphChild_le (P : PolicyJetData m) (K L p : ℕ) (hap : P.a ≤ p)
    (Ψ : ℝ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hchild : ∀ row, ∀ hrow : row ∈
      (P.Q.descendant P.X).occupiedPaths P.ρ (p-P.a) ×ˢ
        (P.Q.descendant P.Y).occupiedPaths P.ρ (p-P.a),
      (P.child p hap row hrow).envelope K L Ψ ≤ M) :
    P.graphChild K L p Ψ ≤ M := by
  apply finiteEnvelopeMaximum_le _ _ hM
  intro row hrow
  simpa only [child_envelope] using hchild row hrow

theorem nearBound_eq (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ) :
    P.nearBound K L Ψ =
      ((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ)*
        ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
          profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam)*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
          P.graphChild K L P.splitDepth Ψ) := rfl

end PolicyJetData
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyBranchCoefficients
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dimension-dependent coefficient payments in the scalar branch ledger -/

namespace Falconer
open Set MeasureTheory

theorem graph_loss_le_branch_reserve (d : ℕ) {lam σ : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) :
    (1000*((d:ℝ)+1)+32*d)*σ+4*((d:ℝ)+1)*lam ≤
      4000*(dimensionalBranchReserve d lam σ+σ) := by
  unfold dimensionalBranchReserve
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hlam,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hσ]

theorem near_loss_le_branch_reserve (d : ℕ) {lam σ : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) :
    4*((d:ℝ)+1)*lam ≤ 4000*(dimensionalBranchReserve d lam σ+σ) :=
  (le_add_of_nonneg_left (by positivity : 0 ≤ (1000*((d:ℝ)+1)+32*d)*σ)).trans
    (graph_loss_le_branch_reserve d hlam hσ)

private theorem absorbed_power_coefficient {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x y z : ℝ, y ≤ z →
      C*((2:ℝ)^N)^(x+y) ≤ ((2:ℝ)^N)^(x+z+ε) := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hε C
  refine ⟨N₀,?_⟩
  intro N hN x y z hyz
  calc
    _ ≤ ((2:ℝ)^N)^ε*((2:ℝ)^N)^(x+y) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(ε+(x+y)) := (Real.rpow_add (by positivity) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (by linarith)

theorem eventual_policy_near_coefficient (m K : ℕ) {lam σ ε : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ P : PolicyJetData m, P.lam = lam → N₀ ≤ P.N →
      ((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ)*
        ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
          profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam)*
        (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2) ≤
      ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
        profileExcess (d := m+3) P.profile P.N P.a)+
        4000*(dimensionalBranchReserve (m+3) lam σ+σ)+ε) := by
  let C : ℝ := ((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2)
  obtain ⟨N₀,hN₀⟩ := absorbed_power_coefficient hε C
  refine ⟨N₀,?_⟩
  intro P hLam hN
  have he := hN₀ P.N hN
    (-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
      profileExcess (d := m+3) P.profile P.N P.a))
    (4*(((m+3:ℕ):ℝ)+1)*lam) (4000*(dimensionalBranchReserve (m+3) lam σ+σ))
    (near_loss_le_branch_reserve (m+3) hlam hσ)
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  rw [hLam]
  dsimp [C]
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyCommonBudgets
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One derivative budget for positive and angular policy steps -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap
open PlanarFalconer (policyDepth)

theorem PolicyJetData.envelope_nonneg {m : ℕ} (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ) :
    0 ≤ P.envelope K L Ψ := by
  classical
  unfold envelope jetStateEnvelope
  by_cases hb : BddAbove (jetStateValues (m+1) K L 1 P.list P.list P.Q P.ρ
      (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks P.Z
      (P.ρ.restrict (P.Q.descendant P.X).carrier)
      (P.ρ.restrict (P.Q.descendant P.Y).carrier)
      (profileModelMass P.profile P.N P.a) (profileModelMass P.profile P.N P.a) P.a P.t Ψ)
  · exact le_csSup hb (Or.inl rfl)
  · rw [csSup_of_not_bddAbove hb,Real.sSup_empty]


theorem PolicyGraphBound.weaken {m K L J N₀ : ℕ} {lam σ ε ε' T T' Z : ℝ} {Ψ : ℝ → ℝ}
    (h : PolicyGraphBound m K L J lam σ ε T Z N₀ Ψ) (he : ε ≤ ε') (hT : T' ≤ T) :
    PolicyGraphBound m K L J lam σ ε' T' Z N₀ Ψ := by
  intro P hLam hσ hJ hZ hN hi geometry M hM hchildren
  have hR : 1 ≤ (2:ℝ)^P.N := one_le_pow₀ (by norm_num)
  have hchild : ∀ row, ∀ hrow : row ∈
      (P.Q.descendant P.X).occupiedPaths P.ρ (geometry.p-P.a) ×ˢ
        (P.Q.descendant P.Y).occupiedPaths P.ρ (geometry.p-P.a),
      P.directWeight geometry.p lam σ ε *
        (P.child geometry.p geometry.ap row hrow).envelope K L Ψ ≤ M := by
    intro row hrow
    apply (mul_le_mul_of_nonneg_right ?_
      ((P.child geometry.p geometry.ap row hrow).envelope_nonneg K L Ψ)).trans (hchildren row hrow)
    unfold PolicyJetData.directWeight
    exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have herr : ((2:ℝ)^P.N)^(-T) ≤ ((2:ℝ)^P.N)^(-T') :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  exact (h P hLam hσ hJ hZ hN hi geometry M hM hchild).trans (add_le_add_right herr M)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyFarCoefficients
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact collision coefficients and their branch payments -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

namespace PolicyJetData
variable {m : ℕ}

theorem collisionTerm_eq (P : PolicyJetData m) (K : ℕ) (B : ℝ) {C : ℝ}
    (hC : 0 ≤ C) (w₀ : Sphere (m+3)) (b : ℕ) :
    P.collisionTerm w₀ (C*(B^K*P.Z⁻¹)^4) b =
      ENNReal.ofReal (P.collisionCoefficient K B C b)*
        farCollisionMaximum w₀ P.Q P.ρ (fun t => P.profile (t/P.N))
          P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a) := by
  unfold collisionTerm collisionCoefficient
  rw [← ENNReal.ofReal_toReal PlanarFalconer.binKernelConstant_ne_top,← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  congr 2
  ac_rfl

end PolicyJetData

theorem eventual_policy_far_coefficient (m K : ℕ) {B C lam σ ε : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (P : PolicyJetData m), P.lam = lam → 1 ≤ P.Z → N₀ ≤ P.N →
      ∀ b : ℕ, P.collisionCoefficient K B C b ≤ P.farWeight b lam σ ε := by
  let A : ℝ := C*(B^K)^4*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    PlanarFalconer.binKernelConstant.toReal
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hε A
  refine ⟨N₀,?_⟩
  intro P hLam hZ hN b
  have hz : P.Z⁻¹ ≤ 1 := (inv_le_one₀ P.Z_pos).mpr hZ
  have hb : 0 ≤ B^K := pow_nonneg (zero_le_one.trans hB) K
  have hpower : (B^K*P.Z⁻¹)^4 ≤ (B^K)^4 := by
    apply pow_le_pow_left₀ (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz hb
  have hA : C*(B^K*P.Z⁻¹)^4*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
      PlanarFalconer.binKernelConstant.toReal ≤ A := by
    dsimp [A]
    gcongr
  have hloss := near_loss_le_branch_reserve (m+3) hlam hσ
  unfold PolicyJetData.collisionCoefficient PolicyJetData.farWeight
  rw [hLam]
  calc
    _ ≤ A*((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N b-
        profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    _ ≤ ((2:ℝ)^P.N)^ε*((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N b-
        profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right (hN₀ P.N hN) (by positivity)
    _ = ((2:ℝ)^P.N)^(ε+(-2*(profileExcess (d := m+3) P.profile P.N b-
        profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*lam)) :=
      (Real.rpow_add (by positivity) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)

theorem eventual_policy_collisionTerm_payment (m K : ℕ) {B C lam σ ε : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hσ : 0 ≤ σ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (P : PolicyJetData m), P.lam = lam → 1 ≤ P.Z → N₀ ≤ P.N →
      ∀ (w₀ : Sphere (m+3)) (b : ℕ),
      P.collisionTerm w₀ (C*(B^K*P.Z⁻¹)^4) b ≤
        ENNReal.ofReal (((2:ℝ)^P.N)^(-ε/2)) *
          (ENNReal.ofReal (P.farWeight b lam σ ε)*
            farCollisionMaximum w₀ P.Q P.ρ (fun t => P.profile (t/P.N))
              P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a)) := by
  obtain ⟨N₀,hN₀⟩ := eventual_policy_far_coefficient m K hB hC hlam hσ (half_pos hε)
  refine ⟨N₀,?_⟩
  intro P hLam hZ hN w₀ b
  rw [P.collisionTerm_eq K B hC w₀ b,← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply (hN₀ P hLam hZ hN b).trans_eq
  unfold PolicyJetData.farWeight
  rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicyFarRecurrence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The near and collision successors of an actual far branch -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

theorem exists_policy_far_recurrence
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K : ℕ) {lam σ ε T : ℝ} (hlam : 0 ≤ lam)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hT : 0 ≤ T)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ u, 0 ≤ Ψ u)
    (hsupp : ∀ u, Ψ u ≠ 0 → u ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ u, Ψ u ≤ W) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∃ N₀ : ℕ,
      ∀ (P : PolicyJetData m), P.lam = lam → P.σ = σ →
      N₀ ≤ P.N → ∀ hsplit : P.a < P.splitDepth, 1 ≤ P.Z →
      ∀ (w₀ : Sphere (m+3)) (M : ℝ), 0 ≤ M →
      (∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (P.splitDepth-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (P.splitDepth-P.a),
        P.farWeight P.splitDepth lam σ ε *
          (P.child P.splitDepth hsplit.le row hrow).envelope K L Ψ ≤ M) →
      (∀ b ∈ Finset.Icc (P.a+9) (P.splitDepth+6),
        ENNReal.ofReal (P.farWeight b lam σ ε)*
          farCollisionMaximum w₀ P.Q P.ρ (fun t => P.profile (t/P.N))
            P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a) ≤ ENNReal.ofReal M) →
      P.envelope K L Ψ ≤ 2*M+((2:ℝ)^P.N)^(-T) := by
  obtain ⟨L₀,hfar⟩ := exists_policy_far_step hgnomonic hquadratic m K hσ hσ1 hT
    hΨ hpos hsupp hW hΨW
  obtain ⟨Nnear,hnear⟩ := eventual_policy_near_coefficient m K hlam hσ.le hε
  obtain ⟨Npoly,hpoly⟩ := PlanarFalconer.fixed_polynomial_subpower 1 (half_pos hε)
  refine ⟨L₀,?_⟩
  intro L hL
  obtain ⟨B,C,Nfar,hB,hC,hstep⟩ := hfar L hL
  obtain ⟨Ncoeff,hcoeff⟩ := eventual_policy_collisionTerm_payment m K hB hC hlam hσ.le hε
  refine ⟨max 1 (max (max Nnear Npoly) (max Nfar Ncoeff)),?_⟩
  intro P hLam hσP hN hsplit hZ w₀ M hM hchildren hcollisions
  have hN1 : 1 ≤ P.N := (le_max_left _ _).trans hN
  have hNall := (le_max_right _ _).trans hN
  have hNnear : Nnear ≤ P.N := (le_max_left _ _).trans ((le_max_left _ _).trans hNall)
  have hNpoly : Npoly ≤ P.N := (le_max_right _ _).trans ((le_max_left _ _).trans hNall)
  have hNfar : Nfar ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans hNall)
  have hNcoeff : Ncoeff ≤ P.N := (le_max_right _ _).trans ((le_max_right _ _).trans hNall)
  have hweight : 0 < P.farWeight P.splitDepth lam σ ε := by
    unfold PolicyJetData.farWeight
    positivity
  have hchild : P.graphChild K L P.splitDepth Ψ ≤ M/P.farWeight P.splitDepth lam σ ε := by
    apply P.graphChild_le K L P.splitDepth hsplit.le Ψ (div_nonneg hM hweight.le)
    intro row hrow
    apply (le_div_iff₀ hweight).mpr
    simpa only [mul_comm] using hchildren row hrow
  have hweighted : P.farWeight P.splitDepth lam σ ε*P.graphChild K L P.splitDepth Ψ ≤ M := by
    simpa only [mul_comm] using (le_div_iff₀ hweight).mp hchild
  have hchild0 : 0 ≤ P.graphChild K L P.splitDepth Ψ :=
    childJetStateMaximum_nonneg (m+1) K L 1 _ P.Q P.ρ _ P.N P.σ P.J P.i P.masks P.Z
      P.X P.Y (P.splitDepth-P.a) _ P.splitDepth P.t Ψ
  have hnearM : P.nearBound K L Ψ ≤ M := by
    rw [P.nearBound_eq]
    calc
      _ = (((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ)*
          ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
            profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam)*
          (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2))*
            P.graphChild K L P.splitDepth Ψ := by ring
      _ ≤ P.farWeight P.splitDepth lam σ ε*P.graphChild K L P.splitDepth Ψ :=
        mul_le_mul_of_nonneg_right (hnear P hLam hNnear) hchild0
      _ ≤ M := hweighted
  let S := Finset.Icc (P.a+9) (P.splitDepth+6)
  have hcard : S.card ≤ P.N+3 := by
    dsimp [S]
    rw [Nat.card_Icc]
    have hh : P.splitDepth ≤ P.t := Nat.sub_le _ _
    have ht := P.base_right.trans P.base_N
    omega
  have hpoly' : ((P.N+3:ℕ):ℝ) ≤ ((2:ℝ)^P.N)^(ε/2) := by
    apply (show ((P.N+3:ℕ):ℝ) ≤ 4*(P.N:ℝ)+1 from ?_).trans
      (by simpa only [pow_one] using hpoly P.N hNpoly)
    push_cast
    have hh : (1:ℝ) ≤ P.N := by exact_mod_cast hN1
    linarith
  have hcardE : (S.card:ℝ≥0∞) ≤ ENNReal.ofReal (((2:ℝ)^P.N)^(ε/2)) := by
    have hh := ENNReal.ofReal_le_ofReal ((Nat.cast_le.mpr hcard).trans hpoly')
    simpa only [ENNReal.ofReal_natCast] using hh
  have hsum : (∑ b ∈ S, P.collisionTerm w₀ (C*(B^K*P.Z⁻¹)^4) b) ≤ ENNReal.ofReal M := by
    calc
      _ ≤ ∑ _b ∈ S, ENNReal.ofReal (((2:ℝ)^P.N)^(-ε/2))*ENNReal.ofReal M := by
        apply Finset.sum_le_sum
        intro b hb
        exact (hcoeff P hLam hZ hNcoeff w₀ b).trans
          (mul_le_mul' le_rfl (hcollisions b hb))
      _ = (S.card:ℝ≥0∞)*(ENNReal.ofReal (((2:ℝ)^P.N)^(-ε/2))*ENNReal.ofReal M) := by simp
      _ ≤ ENNReal.ofReal (((2:ℝ)^P.N)^(ε/2))*
          (ENNReal.ofReal (((2:ℝ)^P.N)^(-ε/2))*ENNReal.ofReal M) :=
        mul_le_mul' hcardE le_rfl
      _ = ENNReal.ofReal M := by
        rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity)]
        have hc : ((2:ℝ)^P.N)^(ε/2)*((2:ℝ)^P.N)^(-ε/2) = 1 := by
          rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]
          convert Real.rpow_zero ((2:ℝ)^P.N) using 2
          all_goals try with_reducible_and_instances rfl
          ring
        rw [hc,ENNReal.ofReal_one,one_mul]
  have hbound := (hstep P hσP hNfar hsplit hZ w₀).trans
    (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hnearM) hsum) le_rfl)
  have heq : ENNReal.ofReal M+ENNReal.ofReal M+
      ENNReal.ofReal (((2:ℝ)^P.N)^(-T)) = ENNReal.ofReal (2*M+((2:ℝ)^P.N)^(-T)) := by
    rw [← ENNReal.ofReal_add hM hM,
      ← ENNReal.ofReal_add (add_nonneg hM hM) (by positivity)]
    congr 1
    ring
  rw [heq] at hbound
  have hh := (ENNReal.ofReal_le_iff_le_toReal ENNReal.ofReal_ne_top).mp hbound
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*M+((2:ℝ)^P.N)^(-T))] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PolicySuffixRecurrence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual positive suffix reduction with the scalar branch weight -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (policyDepth)

theorem exists_policy_positive_suffix_recurrence (m : ℕ) {lam σ ε : ℝ}
    (hlam : 0 ≤ lam) (hσ : 0 < σ) (hε : 0 < ε) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ P : PolicyJetData m,
      P.lam = lam → P.σ = σ → P.J = J → N₀ ≤ P.N → P.i ≤ P.J →
      P.a+100*P.q < P.t → P.a+P.t < 2*policyDepth P.policy P.N P.q P.a P.t →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ∀ (w₀ : Sphere (m+3)),
      P.positiveCount w₀ ≤ P.suffixWeight (policyDepth P.policy P.N P.q P.a P.t) lam σ ε *
        (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
          P.N P.σ P.J (P.i+1) P.q P.a (policyDepth P.policy P.N P.q P.a P.t) P.X P.Y).toReal := by
  obtain ⟨Ns,hs⟩ := uniform_policy_suffix_count (d := m+3) hσ hJ
  let C : ℝ := ((PlanarFalconer.bandOffsets (100*(((m+3:ℕ):ℝ)+1))).card:ℝ)*
    ((PlanarFalconer.bandOffsets 3).card:ℝ)
  obtain ⟨Nc,hc⟩ := Regularization.fixed_constant_absorbed hε C
  refine ⟨max Ns Nc,?_⟩
  intro P _hLam hσP hJP hN hi hwide hside hlo w₀
  let := P.regular.probability
  have hbound := hs P.N ((le_max_left _ _).trans hN) P.Q P.unit P.ρ
    (fun u => P.profile (u/P.N)) P.policy P.q P.a (policyDepth P.policy P.N P.q P.a P.t)
    P.t P.i P.q_pos (P.base_right.trans P.base_N) hwide rfl hside
    (by simpa only [hJP] using hi) w₀ P.X P.Y P.X_length P.Y_length hlo
  rw [← hσP,← hJP] at hbound
  have ht := ENNReal.toReal_mono (by
    apply ENNReal.mul_ne_top
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) ENNReal.ofReal_ne_top
    · exact positiveCollisionCount_ne_top w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
        P.N P.σ P.J (P.i+1) P.q P.a (policyDepth P.policy P.N P.q P.a P.t) P.X P.Y) hbound
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2:ℝ)^P.N)^(
      Regularization.profileDrop (fun u => P.profile (u/P.N)) P.N (((m+3:ℕ):ℝ)/2)
        (policyDepth P.policy P.N P.q P.a P.t) P.t+1000*(((m+3:ℕ):ℝ)+1)*P.σ))] at ht
  have hcoeff : C*((2:ℝ)^P.N)^(
      Regularization.profileDrop (fun u => P.profile (u/P.N)) P.N (((m+3:ℕ):ℝ)/2)
        (policyDepth P.policy P.N P.q P.a P.t) P.t+1000*(((m+3:ℕ):ℝ)+1)*P.σ) ≤
      P.suffixWeight (policyDepth P.policy P.N P.q P.a P.t) lam σ ε := by
    unfold PolicyJetData.suffixWeight
    rw [hσP]
    calc
      _ ≤ ((2:ℝ)^P.N)^ε*((2:ℝ)^P.N)^(
          Regularization.profileDrop (fun u => P.profile (u/P.N)) P.N (((m+3:ℕ):ℝ)/2)
            (policyDepth P.policy P.N P.q P.a P.t) P.t+1000*(((m+3:ℕ):ℝ)+1)*σ) :=
        mul_le_mul_of_nonneg_right (hc P.N ((le_max_right _ _).trans hN)) (by positivity)
      _ = ((2:ℝ)^P.N)^(ε+(
          Regularization.profileDrop (fun u => P.profile (u/P.N)) P.N (((m+3:ℕ):ℝ)/2)
            (policyDepth P.policy P.N P.q P.a P.t) P.t+1000*(((m+3:ℕ):ℝ)+1)*σ)) :=
        (Real.rpow_add (by positivity) _ _).symm
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
        have hr := graph_loss_le_branch_reserve (m+3) hlam hσ.le
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (m+3)) hσ.le]
  change _ ≤ (C*_)*_ at ht
  exact ht.trans (mul_le_mul_of_nonneg_right hcoeff ENNReal.toReal_nonneg)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PolicyRecursionBounds
attribute [-instance] _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common budget for all actual policy recurrences -/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap ContDiff
open PlanarFalconer (policyDepth)

theorem exists_policy_recursion_bounds_oai
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {lam σ ε T : ℝ} (hlam : 0 ≤ lam) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hε : 0 < ε) (hT : 0 ≤ T) {J : ℕ} (hJ : 0 < J)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ (K L : ℕ) (Z : ℝ) (N₀ : ℕ), minJet ≤ K ∧ 1 ≤ Z ∧
      PolicyRecursionBounds m K L J lam σ ε T Z N₀ Ψ := by
  obtain ⟨K,hminJet,hpositive⟩ := exists_policy_positive_common_budgets hgnomonic hquadratic
    m hlam hσ hσ1 hε hJ T φ Ψ hφ hΨ hpos hzero hone hV hΨV hsupp minJet
  obtain ⟨L₀,hfar⟩ := exists_policy_far_recurrence hgnomonic hquadratic m K
    hlam hσ hσ1 hε hT hsmooth hpos hsupp hV hΨV
  obtain ⟨L,Z,Np,hL,hZ,hgraph,hposstep⟩ := hpositive L₀
  obtain ⟨Nf,hfarstep⟩ := hfar L hL
  obtain ⟨Ns,hsuffix⟩ := exists_policy_positive_suffix_recurrence m hlam hσ hε hJ
  let N₀ := max Np (max Nf Ns)
  refine ⟨K,L,Z,N₀,hminJet,hZ,?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · have hg : PolicyGraphBound m K L J lam σ ε T Z Np Ψ :=
      hgraph.weaken (by linarith) (by linarith)
    intro P hLam hσP hJP hZP hN
    exact hg P hLam hσP hJP hZP ((le_max_left _ _).trans hN)
  · intro P hσP hLam hJP hZP hN
    exact hposstep P hσP hLam hJP hZP ((le_max_left _ _).trans hN)
  · intro P hLam hσP hN
    exact hfarstep P hLam hσP ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  · intro P hLam hσP hJP hN
    exact hsuffix P hLam hσP hJP ((le_max_right _ _).trans ((le_max_right _ _).trans hN))

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.exists_policy_recursion_bounds_oai := @OAI.Falconer.exists_policy_recursion_bounds_oai
