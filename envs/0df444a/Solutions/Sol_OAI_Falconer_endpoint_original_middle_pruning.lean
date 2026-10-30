-- Prove2me | solution 1 for OAI.Falconer.endpoint_original_middle_pruning
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:13:55.620297+00:00
-- url     : https://prove2.me/submissions/63180daa-a192-4524-b805-f4aaa9042290

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_controlled_endpoint_angular_gain
import Theorems.Thm_OAI_Falconer_endpoint_spherical_preparation

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

theorem perpendicularPart_sub (w u v : E) :
    perpendicularPart w (u-v) = perpendicularPart w u - perpendicularPart w v := by
  simp only [perpendicularPart, inner_sub_right, sub_smul]
  abel

/-- Orthogonal projection is a contraction. -/
theorem norm_perpendicularPart_le {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖ ≤ ‖v‖ := by
  have hn := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right, real_inner_comm v w, norm_smul, hw,
    mul_one, Real.norm_eq_abs, sq_abs] at hn
  change ‖v - inner ℝ w v • w‖ ≤ ‖v‖
  rw [real_inner_comm v w]
  nlinarith [norm_nonneg (v - inner ℝ v w • w), norm_nonneg v, sq_nonneg (inner ℝ v w)]

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
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTubes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A perpendicular tube test occupies two small direction caps

The centers are the two directions of the actual tested displacement.
This gives the angular measure bound used in the parallel-test average.
-/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem perpendicularPart_smul (w v : E) (a : ℝ) :
    perpendicularPart w (a • v) = a • perpendicularPart w v := by
  simp only [perpendicularPart,inner_smul_right,smul_sub,smul_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TubeAnchorNet
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite bounded anchor nets for the original direction-wise tube covers -/

namespace Falconer
open Set Metric
variable {d : ℕ}

theorem exists_bounded_anchor_net (D : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (Space d), (∀ a ∈ S, ‖a‖ ≤ D) ∧
      ∀ x : Space d, ‖x‖ ≤ D → ∃ a ∈ S, ‖x-a‖ ≤ δ := by
  classical
  obtain ⟨T,hT,hfin,hcover⟩ := (isCompact_closedBall (0 : Space d) D).finite_cover_balls hδ
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro a ha
    simpa only [mem_closedBall,dist_zero_right] using hT (hfin.mem_toFinset.mp ha)
  · intro x hx
    have hxc : x ∈ closedBall (0 : Space d) D := by simpa only [mem_closedBall,dist_zero_right] using hx
    obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hcover hxc)
    refine ⟨a,hfin.mem_toFinset.mpr ha,?_⟩
    simpa only [mem_ball,dist_eq_norm] using hxa.le

theorem perpendicular_anchor_rounding {w x a y b : Space d} (hw : ‖w‖ = 1)
    {ε δ : ℝ} (hx : ‖perpendicularPart w (x-a)‖ ≤ ε)
    (hy : ‖perpendicularPart w (y-a)‖ ≤ ε) (hb : ‖y-b‖ ≤ δ) :
    ‖perpendicularPart w (x-b)‖ ≤ 2*ε+δ := by
  have he : perpendicularPart w (x-b) =
      (perpendicularPart w (x-a)-perpendicularPart w (y-a))+perpendicularPart w (y-b) := by
    simp only [perpendicularPart,inner_sub_right]
    module
  rw [he]
  exact (norm_add_le _ _).trans
    (((add_le_add (norm_sub_le _ _) (norm_perpendicularPart_le hw _)).trans
      (add_le_add (add_le_add hx hy) hb)).trans_eq (by ring))

theorem rounded_tube_cover (w : Sphere d) (E : Set (Space d))
    (S G : Finset (Space d)) {ε δ : ℝ}
    (hnet : ∀ x ∈ E, ∃ b ∈ G, ‖x-b‖ ≤ δ)
    (hcover : ∀ x ∈ E, ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ J : Finset (Space d), J ⊆ G ∧ J.card ≤ S.card ∧
      ∀ x ∈ E, ∃ b ∈ J, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ 2*ε+δ := by
  classical
  let P := fun a : Space d => ∃ y ∈ E, ‖perpendicularPart (w:Space d) (y-a)‖ ≤ ε
  have hround (a : Space d) (ha : P a) :
      ∃ b ∈ G, ∀ x ∈ E, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε →
        ‖perpendicularPart (w:Space d) (x-b)‖ ≤ 2*ε+δ := by
    obtain ⟨y,hy,hya⟩ := ha
    obtain ⟨b,hb,hyb⟩ := hnet y hy
    exact ⟨b,hb,fun _ _ hx => perpendicular_anchor_rounding (sphere_norm w) hx hya hyb⟩
  let b : Space d → Space d := fun a => if ha : P a then (hround a ha).choose else 0
  let J := (S.filter P).image b
  refine ⟨J,?_,(Finset.card_image_le.trans (Finset.card_filter_le _ _)),?_⟩
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    have hp := (Finset.mem_filter.mp ha).2
    simpa only [b,dite_eq_left hp] using (hround a hp).choose_spec.1
  · intro x hx
    obtain ⟨a,ha,hxa⟩ := hcover x hx
    have hp : P a := ⟨x,hx,hxa⟩
    refine ⟨b a,Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩,rfl⟩,?_⟩
    simpa only [b,dite_eq_left hp] using (hround a hp).choose_spec.2 x hx hxa

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_TubeCoverChoice
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable choice of countably listed original-label tube covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W ι : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem tube_cover_uncovered_mass_measurable
    (μ : Measure X) [SFinite μ] (E : Set (X × W)) (hE : MeasurableSet E)
    (U : ι → W → Set X) (hU : ∀ i, MeasurableSet {p : W × X | p.2 ∈ U i p.1})
    (C : Finset ι) :
    Measurable (fun w => μ {x | (x,w) ∈ E ∧ ∀ i ∈ C, x ∉ U i w}) := by
  have hC : MeasurableSet {p : W × X | ∀ i ∈ C, p.2 ∉ U i p.1} := by
    simp only [ofPred_forall]
    exact C.measurableSet_biInter (fun i _ => (hU i).compl)
  exact measurable_measure_prodMk_left ((hE.preimage measurable_swap).inter hC)

theorem exists_measurable_tube_cover_choice
    (μ : Measure X) [SFinite μ] (E : Set (X × W)) (hE : MeasurableSet E)
    (U : ι → W → Set X) (hU : ∀ i, MeasurableSet {p : W × X | p.2 ∈ U i p.1})
    (C : ℕ → Finset ι)
    (hcover : ∀ w, ∃ n, μ {x | (x,w) ∈ E ∧ ∀ i ∈ C n, x ∉ U i w} = 0) :
    ∃ J : W → Finset ι, (∀ i, MeasurableSet {w | i ∈ J w}) ∧
      (∀ w, μ {x | (x,w) ∈ E ∧ ∀ i ∈ J w, x ∉ U i w} = 0) ∧
      ∀ w, ∃ n, J w = C n := by
  classical
  let j : W → ℕ := fun w => Nat.find (hcover w)
  have hj : Measurable j := measurable_find hcover (fun n =>
    measurableSet_eq_fun (tube_cover_uncovered_mass_measurable μ E hE U hU (C n)) measurable_const)
  refine ⟨fun w => C (j w),?_,?_,?_⟩
  · intro i
    exact hj ((Set.to_countable {n | i ∈ C n}).measurableSet)
  · intro w
    exact Nat.find_spec (hcover w)
  · intro w
    exact ⟨j w,rfl⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_TubeCoverEnumeration
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating the admissible finite lists from a bounded anchor net -/

namespace Falconer
open Set
variable {X : Type*}

theorem bounded_finset_enumeration (G : Finset X) (N : ℕ) :
    ∃ C : ℕ → Finset X, (∀ n, C n ⊆ G ∧ (C n).card ≤ N) ∧
      ∀ J : Finset X, J ⊆ G → J.card ≤ N → ∃ n, C n = J := by
  classical
  let S := G.powerset.filter (fun J => J.card ≤ N)
  have hs : (∅ : Finset X) ∈ S := by simp [S]
  have : Nonempty {J : Finset X // J ∈ S} := ⟨⟨∅,hs⟩⟩
  obtain ⟨f,hf⟩ := exists_surjective_nat {J : Finset X // J ∈ S}
  refine ⟨fun n => (f n).val,?_,?_⟩
  · intro n
    have hp := Finset.mem_filter.mp (f n).property
    exact ⟨Finset.mem_powerset.mp hp.1,hp.2⟩
  · intro J hJG hJN
    have hJS : J ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hJG,hJN⟩
    obtain ⟨n,hn⟩ := hf ⟨J,hJS⟩
    exact ⟨n,congrArg Subtype.val hn⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MeasurableTubeCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable bounded-grid covers of the original direction fibers -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem original_tube_cover_choice (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset (Space d),
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, J w ⊆ G ∧ (J w).card ≤ N) ∧
        ∀ w, μ {x | (x,w) ∈ E ∧ ∀ a ∈ J w,
          ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ} = 0 := by
  classical
  obtain ⟨G,hGb,hGn⟩ := exists_bounded_anchor_net (d := d) D hδ
  obtain ⟨C,hC,hCs⟩ := bounded_finset_enumeration G N
  let U : Space d → Sphere d → Set (Space d) := fun a w =>
    {x | ‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ}
  have hU (a : Space d) : MeasurableSet {p : Sphere d × Space d | p.2 ∈ U a p.1} := by
    dsimp [U,perpendicularPart]
    exact measurableSet_le (by fun_prop) measurable_const
  have hc : ∀ w : Sphere d, ∃ n, μ {x | (x,w) ∈ E ∧ ∀ a ∈ C n, x ∉ U a w} = 0 := by
    intro w
    obtain ⟨S,hSN,hS⟩ := hcover w
    obtain ⟨J,hJG,hJS,hJ⟩ := rounded_tube_cover w {x | (x,w) ∈ E} S G
      (fun x hx => hGn x (hbounded (x,w) hx)) hS
    obtain ⟨n,hn⟩ := hCs J hJG (hJS.trans hSN)
    refine ⟨n,?_⟩
    apply measure_mono_null (t := ∅) _ (measure_empty)
    intro x hx
    obtain ⟨a,ha,hxa⟩ := hJ x hx.1
    exact (hx.2 a (hn.symm ▸ ha) hxa).elim
  obtain ⟨J,hJ,hzero,hJC⟩ := exists_measurable_tube_cover_choice μ E hE U hU C hc
  refine ⟨G,hGb,J,hJ,?_,hzero⟩
  intro w
  obtain ⟨n,hn⟩ := hJC w
  simpa only [hn] using hC n

theorem finite_tube_cover_relation_measurable
    (G : Finset (Space d)) (J : Sphere d → Finset (Space d))
    (hJ : ∀ a, MeasurableSet {w | a ∈ J w}) (hJG : ∀ w, J w ⊆ G) (ε : ℝ) :
    MeasurableSet {t : Space d × Sphere d |
      ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
  have hm : MeasurableSet {t : Space d × Sphere d |
      ∃ a ∈ G, a ∈ J t.2 ∧ ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
    have hu : MeasurableSet (⋃ a ∈ G, {t : Space d × Sphere d |
        a ∈ J t.2 ∧ ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε}) := by
      apply G.measurableSet_biUnion
      intro a _
      have hp : MeasurableSet {t : Space d × Sphere d |
          ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ ε} := by
        dsimp [perpendicularPart]
        exact measurableSet_le (by fun_prop) measurable_const
      exact ((hJ a).preimage measurable_snd).inter hp
    convert hu using 1
    all_goals try with_reducible_and_instances rfl
    ext t
    simp only [mem_ofPred_eq,mem_iUnion,exists_prop]
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  constructor
  · rintro ⟨a,ha,hp⟩
    exact ⟨a,hJG t.2 ha,ha,hp⟩
  · rintro ⟨a,_,ha,hp⟩
    exact ⟨a,ha,hp⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_BadDirectionEnvelope
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A Borel envelope for geometric bad directions

The finite anchor net and the envelope depend only on the point law and the
geometric test, before a direction measure is selected.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem boundedTubeUnion_joint_measurable (D R : ℝ) (J : Finset (Space d)) :
    MeasurableSet {p : Sphere d × Space d | p.2 ∈ boundedTubeUnion D R J p.1} := by
  have hU : MeasurableSet (⋃ a ∈ J, {p : Sphere d × Space d |
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R}) := by
    apply J.measurableSet_biUnion
    intro a _
    unfold perpendicularPart
    exact measurableSet_le (by fun_prop) measurable_const
  have he : {p : Sphere d × Space d | ∃ a ∈ J,
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} =
      ⋃ a ∈ J, {p : Sphere d × Space d | ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} := by
    ext p
    simp only [mem_iUnion,mem_ofPred_eq,exists_prop]
  have hb : MeasurableSet {p : Sphere d × Space d | ‖p.2‖ ≤ D} :=
    measurableSet_le (by fun_prop) measurable_const
  have hU' : MeasurableSet {p : Sphere d × Space d | ∃ a ∈ J,
      ‖perpendicularPart (p.1:Space d) (p.2-a)‖ ≤ R} := by
    rw [he]
    exact hU
  change MeasurableSet ({p : Sphere d × Space d | ‖p.2‖ ≤ D} ∩ _)
  exact hb.inter hU'

theorem boundedTubeUnion_mass_measurable (μ : Measure (Space d)) [SFinite μ]
    (D R : ℝ) (J : Finset (Space d)) :
    Measurable (fun w : Sphere d => μ (boundedTubeUnion D R J w)) :=
  measurable_measure_prodMk_left (boundedTubeUnion_joint_measurable D R J)

theorem finiteBadDirections_measurable (μ : Measure (Space d)) [SFinite μ]
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) :
    MeasurableSet (finiteBadDirections μ G N D R a) := by
  classical
  have hU : MeasurableSet (⋃ J ∈ G.powerset,
      {w : Sphere d | J.card ≤ N ∧ a ≤ μ (boundedTubeUnion D R J w)}) := by
    apply G.powerset.measurableSet_biUnion
    intro J _
    exact (MeasurableSet.const _).inter
      (measurableSet_le measurable_const (boundedTubeUnion_mass_measurable μ D R J))
  convert hU using 1
  all_goals try with_reducible_and_instances rfl
  ext w
  simp only [finiteBadDirections,mem_iUnion,mem_ofPred_eq,exists_prop]

theorem original_bad_direction_mem_envelope (μ : Measure (Space d)) [SFinite μ]
    {D R δ : ℝ} (G : Finset (Space d)) (N : ℕ) (a : ℝ≥0∞)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hnet : ∀ x : Space d, ‖x‖ ≤ D → ∃ b ∈ G, ‖x-b‖ ≤ δ)
    (w : Sphere d) (S : Finset (Space d)) (hS : S.card ≤ N)
    (hmass : a ≤ μ {x | ∃ b ∈ S, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ R}) :
    w ∈ finiteBadDirections μ G N D (2*R+δ) a := by
  classical
  let E := boundedTubeUnion D R S w
  obtain ⟨J,hJG,hJS,hcover⟩ := rounded_tube_cover w E S G
    (fun x hx => hnet x hx.1) (fun _ hx => hx.2)
  refine ⟨J,Finset.mem_powerset.mpr hJG,hJS.trans hS,?_⟩
  have hrestrict : μ {x | ∃ b ∈ S, ‖perpendicularPart (w:Space d) (x-b)‖ ≤ R} ≤ μ E := by
    apply measure_mono_ae
    filter_upwards [hμ] with x hx hm
    exact ⟨hx,hm⟩
  apply (hmass.trans hrestrict).trans
  apply measure_mono
  intro x hx
  exact ⟨hx.1,hcover x hx⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_BadDirectionSelection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A measurable incidence witnessing every direction in the finite envelope -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem exists_finite_bad_incidence (μ : Measure (Space d)) [SFinite μ]
    (G : Finset (Space d)) (N : ℕ) (D R : ℝ) (a : ℝ≥0∞) :
    ∃ J : Sphere d → Finset (Space d), ∃ F : Set (Space d × Sphere d),
      MeasurableSet F ∧ (∀ w, J w ⊆ G ∧ (J w).card ≤ N) ∧
      (∀ x, MeasurableSet {w | x ∈ J w}) ∧
      (∀ p ∈ F, ‖p.1‖ ≤ D) ∧
      (∀ p ∈ F, ∃ x ∈ J p.2, ‖perpendicularPart (p.2:Space d) (p.1-x)‖ ≤ R) ∧
      ∀ (ν : Measure (Sphere d)) [SFinite ν],
        a*ν (finiteBadDirections μ G N D R a) ≤ (μ.prod ν) F := by
  classical
  let B := finiteBadDirections μ G N D R a
  have hB : MeasurableSet B := finiteBadDirections_measurable μ G N D R a
  obtain ⟨C,hC,hCs⟩ := bounded_finset_enumeration G N
  have hfind : ∀ w : Sphere d, ∃ n : ℕ,
      w ∉ B ∨ a ≤ μ (boundedTubeUnion D R (C n) w) := by
    intro w
    by_cases hw : w ∈ B
    · obtain ⟨J,hJG,hJN,hm⟩ := hw
      obtain ⟨n,rfl⟩ := hCs J (Finset.mem_powerset.mp hJG) hJN
      exact ⟨n,Or.inr hm⟩
    · exact ⟨0,Or.inl hw⟩
  let j : Sphere d → ℕ := fun w => Nat.find (hfind w)
  have hj : Measurable j := measurable_find hfind (fun n => hB.compl.union
    (measurableSet_le measurable_const (boundedTubeUnion_mass_measurable μ D R (C n))))
  let J : Sphere d → Finset (Space d) := fun w => C (j w)
  have hJ (x : Space d) : MeasurableSet {w | x ∈ J w} :=
    hj ((Set.to_countable {n | x ∈ C n}).measurableSet)
  let F : Set (Space d × Sphere d) := {p | p.2 ∈ B ∧ p.1 ∈ boundedTubeUnion D R (J p.2) p.2}
  have hF : MeasurableSet F := by
    have ht := finite_tube_cover_relation_measurable G J hJ (fun w => (hC (j w)).1) R
    have hb : MeasurableSet {p : Space d × Sphere d | ‖p.1‖ ≤ D} :=
      measurableSet_le (by fun_prop) measurable_const
    exact (hB.preimage measurable_snd).inter (hb.inter ht)
  refine ⟨J,F,hF,(fun w => hC (j w)),hJ,(fun _ hp => hp.2.1),(fun _ hp => hp.2.2),?_⟩
  intro ν _
  have hbound (w : Sphere d) : B.indicator (fun _ => a) w ≤ μ {x | (x,w) ∈ F} := by
    by_cases hw : w ∈ B
    · rw [indicator_of_mem hw]
      have hm := (Nat.find_spec (hfind w)).resolve_left (not_not.mpr hw)
      have he : {x | (x,w) ∈ F} = boundedTubeUnion D R (J w) w := by
        ext x
        simp only [F,mem_ofPred_eq,hw,true_and]
      rw [he]
      exact hm
    · rw [indicator_of_notMem hw]
      exact bot_le
  rw [Measure.prod_apply_symm hF]
  calc
    _ = ∫⁻ w, B.indicator (fun _ => a) w ∂ν := by
      rw [lintegral_indicator hB,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ _ := lintegral_mono hbound

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLossAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the concrete slice-selection losses into the planar gain -/

namespace Falconer
open Real Filter
open scoped Topology

theorem gaussian_scale_power {δ κ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    (δ^(-κ))^j = δ^(-((j:ℝ)*κ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicLossAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic number of dyadic tests fits inside the chosen power loss -/

namespace Falconer
open Real Filter
open scoped Topology

theorem dyadic_log_depth (N : ℕ) :
    1-Real.log (1/(2:ℝ)^N)/Real.log 2 = (N:ℝ)+1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [one_div,Real.log_inv,Real.log_pow]
  field_simp
  ring

theorem eventually_dyadic_loss_absorption {ε κ : ℝ} (hεκ : ε < κ) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ),
      0 < δ ∧ C*(1-Real.log δ/Real.log 2)*δ^(-ε) ≤ δ^(-κ) := by
  have hr : 0 < κ-ε := sub_pos.mpr hεκ
  have hp : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝[>] 0) (𝓝 0) := by
    have hp₀ : Tendsto (fun δ : ℝ => δ^(κ-ε)) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [Real.zero_rpow hr.ne'] using (Real.continuous_rpow_const hr.le).tendsto (0:ℝ)
    exact hp₀.mono_left nhdsWithin_le_nhds
  have hl := tendsto_log_mul_rpow_nhdsGT_zero hr
  have ht : Tendsto (fun δ : ℝ => C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_div,sub_zero,mul_zero] using (hp.sub (hl.div_const (Real.log 2))).const_mul C
  have hsmall := ht.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hsmall,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hs hδone
  have hδ := hδone.1
  refine ⟨hδ,?_⟩
  calc
    _ = (C*(δ^(κ-ε)-(Real.log δ*δ^(κ-ε))/Real.log 2))*δ^(-κ) := by
      calc
        _ = C*(1-Real.log δ/Real.log 2)*δ^((κ-ε)+(-κ)) := by congr 2; ring
        _ = C*(1-Real.log δ/Real.log 2)*(δ^(κ-ε)*δ^(-κ)) := by rw [Real.rpow_add hδ]
        _ = _ := by ring
    _ ≤ 1*δ^(-κ) := mul_le_mul_of_nonneg_right hs.le (Real.rpow_nonneg hδ.le _)
    _ = _ := one_mul _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointCountBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The strict dimension gap absorbs all endpoint tube-counting losses -/

namespace Falconer
open Real Filter
open scoped Topology

theorem endpoint_count_power {δ : ℝ} (hδ : 0 < δ) (C a κ s : ℝ) :
    (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 =
      ((6*C+35)^6*((6:ℝ)^s)^2)*δ^(2*s-3-6*a-5*κ) := by
  have hp (t : ℝ) (k : ℕ) : (δ^t)^k = δ^(t*(k:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
  rw [Real.mul_rpow (by norm_num) hδ.le,div_pow,mul_pow,mul_pow,
    hp (-1-κ) 3,hp a 6,hp (-κ) 2,hp s 2]
  calc
    _ = ((6*C+35)^6*((6:ℝ)^s)^2)*
        (δ^((-1-κ)*3)/δ^(a*6)*δ^(-κ*2)*δ^(s*2)) := by ring_nf
    _ = _ := by
      rw [← Real.rpow_sub hδ,← Real.rpow_add hδ,← Real.rpow_add hδ]
      congr 1
      ring_nf

theorem eventually_endpoint_count_budget {s a κ : ℝ}
    (hgap : 0 < 2*s-3-6*a-7*κ) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      (δ^(-1-κ))^3*((6*C+35)/δ^a)^6*(δ^(-κ)*(6*δ)^s)^2 < (δ^κ)^2 := by
  let K : ℝ := (6*C+35)^6*((6:ℝ)^s)^2
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show -(2*s-3-6*a-7*κ) < 0 by linarith)).eventually
    (eventually_gt_atTop K)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,?_⟩
  rw [endpoint_count_power hδ.1]
  calc
    _ < δ^(-(2*s-3-6*a-7*κ))*δ^(2*s-3-6*a-5*κ) :=
      mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = (δ^κ)^2 := by
      rw [← Real.rpow_add hδ.1,← Real.rpow_natCast,← Real.rpow_mul hδ.1.le]
      congr 1
      ring_nf

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointPowerAbsorption
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Strict power gaps used in endpoint row and triple selection -/

namespace Falconer
open Real Filter
open scoped Topology

theorem eventually_const_mul_rpow_lt {p q : ℝ} (hpq : q < p) (C : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ C*δ^p < δ^q := by
  have hh := (tendsto_rpow_neg_nhdsGT_zero (show q-p < 0 by linarith)).eventually
    (eventually_gt_atTop C)
  filter_upwards [hh,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hd hδ
  refine ⟨hδ.1,?_⟩
  calc
    _ < δ^(q-p)*δ^p := mul_lt_mul_of_pos_right hd (Real.rpow_pos_of_pos hδ.1 _)
    _ = _ := by rw [← Real.rpow_add hδ.1]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointDyadicScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic cutoff and power conversions for endpoint assembly -/

namespace Falconer
open Filter
open scoped Topology

theorem dyadic_inverse_tendsto :
    Tendsto (fun N : ℕ => 1/(2:ℝ)^N) atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [one_div,inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹)
        (by norm_num : (2:ℝ)⁻¹ < 1))
  · filter_upwards [] with N
    change 0 < 1/(2:ℝ)^N
    positivity

theorem dyadic_inverse_rpow (N : ℕ) (c : ℝ) :
    ((2:ℝ)^N)^(-c) = (1/(2:ℝ)^N)^c := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_neg (by positivity)]

theorem dyadic_loss_conversion (N : ℕ) (c : ℝ) :
    ((2:ℝ)^N)^c = (1/(2:ℝ)^N)^(-c) := by
  simpa only [neg_neg] using dyadic_inverse_rpow N (-c)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointRowBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two radial row deletions fit inside the original incidence budget -/

namespace Falconer
open Real Filter
open scoped Topology ENNReal

theorem eventually_endpoint_row_base {u τ c₁ c₂ : ℝ}
    (hu : 0 < u) (hc₁ : τ+10*u < c₁) (hc₂ : τ+10*u < c₂) (V : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4 := by
  have h₀ := eventually_const_mul_rpow_lt (show u < 2*u by linarith) (12*V)
  have h₁ := eventually_const_mul_rpow_lt (show u < c₁-τ-9*u by linarith) (12*V)
  have h₂ := eventually_const_mul_rpow_lt (show u < c₂-τ-9*u by linarith) (12*V)
  filter_upwards [h₀,h₁,h₂] with δ h₀ h₁ h₂
  exact ⟨h₀.1,by nlinarith [h₀.2,h₁.2,h₂.2]⟩

theorem endpoint_row_cost_power {δ : ℝ} (hδ : 0 < δ) (u τ c V : ℝ) :
    δ^(-6*u)*δ^(-3*u)*V*(δ^c/δ^τ) = V*δ^(c-τ-9*u) := by
  rw [← Real.rpow_sub hδ]
  calc
    _ = V*(δ^(-6*u)*δ^(-3*u)*δ^(c-τ)) := by ring
    _ = _ := by rw [← Real.rpow_add hδ,← Real.rpow_add hδ]; congr 1; ring_nf

theorem endpoint_row_base_ennreal {δ u τ c₁ c₂ V : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V)
    (Z A₁ A₂ : ℝ≥0∞) (hZ : Z ≤ ENNReal.ofReal V)
    (hA₁ : A₁ ≤ ENNReal.ofReal (δ^c₁)) (hA₂ : A₂ ≤ ENNReal.ofReal (δ^c₂))
    (hbudget : V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4) :
    ENNReal.ofReal (δ^(2*u))*Z+
      (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*Z)*(A₁/ENNReal.ofReal (δ^τ))+
      (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*Z)*(A₂/ENNReal.ofReal (δ^τ)) ≤
        ENNReal.ofReal (δ^u/4) := by
  have hterm (A : ℝ≥0∞) (c : ℝ) (hA : A ≤ ENNReal.ofReal (δ^c)) :
      (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*Z)*(A/ENNReal.ofReal (δ^τ)) ≤
        ENNReal.ofReal (V*δ^(c-τ-9*u)) := by
    calc
      _ ≤ (ENNReal.ofReal (δ^(-6*u))*ENNReal.ofReal (δ^(-3*u))*ENNReal.ofReal V)*
          (ENNReal.ofReal (δ^c)/ENNReal.ofReal (δ^τ)) :=
        mul_le_mul' (mul_le_mul' le_rfl hZ) (ENNReal.div_le_div_right hA _)
      _ = ENNReal.ofReal (δ^(-6*u)*δ^(-3*u)*V*(δ^c/δ^τ)) := by
        rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hδ _),
          ← ENNReal.ofReal_mul (by positivity)]
      _ = _ := by rw [endpoint_row_cost_power hδ]
  have hb : ENNReal.ofReal (δ^(2*u))*Z ≤ ENNReal.ofReal (V*δ^(2*u)) := by
    calc
      _ ≤ ENNReal.ofReal (δ^(2*u))*ENNReal.ofReal V := mul_le_mul' le_rfl hZ
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity),mul_comm]
  apply (add_le_add (add_le_add hb (hterm A₁ c₁ hA₁)) (hterm A₂ c₂ hA₂)).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hbudget

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointSelectionLosses
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One loss parameter for radial pruning, row selection and endpoint counting -/

namespace Falconer

theorem exists_endpoint_selection_losses {ε c₁ c₂ g : ℝ}
    (hε : 0 < ε) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hg : 0 < g) :
    ∃ u τ : ℝ, 0 < u ∧ 0 < τ ∧ u < ε ∧ 30*u < τ ∧
      τ+10*u < c₁ ∧ τ+10*u < c₂ ∧ 280*u < g := by
  let τ : ℝ := min c₁ c₂/2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτ₁ : 2*τ ≤ c₁ := by dsimp [τ]; linarith [min_le_left c₁ c₂]
  have hτ₂ : 2*τ ≤ c₂ := by dsimp [τ]; linarith [min_le_right c₁ c₂]
  let u : ℝ := min ε (min (τ/100) (g/560))/2
  have hu : 0 < u := by dsimp [u]; positivity
  have huε : 2*u ≤ ε := by dsimp [u]; linarith [min_le_left ε (min (τ/100) (g/560))]
  have huτ : 2*u ≤ τ/100 := by
    dsimp [u]
    linarith [(min_le_right ε (min (τ/100) (g/560))).trans (min_le_left (τ/100) (g/560))]
  have hug : 2*u ≤ g/560 := by
    dsimp [u]
    linarith [(min_le_right ε (min (τ/100) (g/560))).trans (min_le_right (τ/100) (g/560))]
  exact ⟨u,τ,hu,hτ,by linarith,by linarith,by linarith,by linarith,by linarith⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_EndpointMassRatios
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The common-triple mass and bad-triple thresholds are compatible -/

namespace Falconer
open Real Filter
open scoped Topology

theorem endpoint_common_mass_ratio {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    (δ^(2*u))^3/(2*(δ^(-6*u))^5) = (1/2)*δ^(36*u) := by
  have hp : (δ^(2*u))^3 = δ^(6*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hq : (δ^(-6*u))^5 = δ^(-30*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hp,hq]
  calc
    _ = (1/2)*(δ^(6*u)/δ^(-30*u)) := by ring
    _ = _ := by rw [← Real.rpow_sub hδ]; congr 2; ring

theorem endpoint_bad_mass_ratio {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    (δ^(2*u))^3/(4*(δ^(-6*u))^3) = (1/4)*δ^(24*u) := by
  have hp : (δ^(2*u))^3 = δ^(6*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  have hq : (δ^(-6*u))^3 = δ^(-18*u) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le]
    congr 1
    ring
  rw [hp,hq]
  calc
    _ = (1/4)*(δ^(6*u)/δ^(-18*u)) := by ring
    _ = _ := by rw [← Real.rpow_sub hδ]; congr 2; ring

theorem eventually_endpoint_mass_thresholds {u τ : ℝ}
    (hu : 0 < u) (hτ : 30*u < τ) :
    ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
      δ^(40*u) ≤ (δ^(2*u))^3/(2*(δ^(-6*u))^5) ∧
      δ^τ+2*δ^(-6*u)*δ^τ ≤ (δ^(2*u))^3/(4*(δ^(-6*u))^3) := by
  have hb := eventually_const_mul_rpow_lt (show 24*u < τ-6*u by linarith) 12
  have hm := eventually_const_mul_rpow_lt (show 36*u < 40*u by linarith) 2
  filter_upwards [hb,hm,Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hb hm hδ
  refine ⟨hδ.1,?_,?_⟩
  · rw [endpoint_common_mass_ratio hδ.1]
    linarith [hm.2]
  · rw [endpoint_bad_mass_ratio hδ.1]
    have hM : 1 ≤ δ^(-6*u) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ.1 hδ.2 (by linarith)
    have hh : δ^τ+2*δ^(-6*u)*δ^τ ≤ 3*δ^(-6*u)*δ^τ := by
      nlinarith [mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hδ.1.le τ)]
    have he : δ^(-6*u)*δ^τ = δ^(τ-6*u) := by rw [← Real.rpow_add hδ.1]; congr 1; ring
    rw [mul_assoc,he] at hh
    linarith [hb.2]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_EndpointAngularParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous scalar budgets for the endpoint angular application -/

namespace Falconer
open Real Filter
open scoped Topology

theorem exists_endpoint_angular_parameters {ε₀ c₁ c₂ s a : ℝ}
    (hε₀ : 0 < ε₀) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hgap : 0 < 2*s-3-6*a) (ha : a < 1/2)
    (Cm Large V Cpoint Ccover C H : ℝ) :
    ∃ u ε τ : ℝ, 0 < u ∧ 0 < ε ∧ 0 < τ ∧ ε < ε₀ ∧ ε < u ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        let δ := 1/(2:ℝ)^N
        ((N+1:ℕ):ℝ)*(Cm*δ^(-ε)) ≤ δ^(-u) ∧
        Large ≤ δ^(-u) ∧ Cpoint*δ^(-6*u) ≤ δ^(-40*u) ∧
        V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4 ∧
        δ^(40*u) ≤ (δ^(2*u))^3/(2*(δ^(-6*u))^5) ∧
        δ^τ+2*δ^(-6*u)*δ^τ ≤ (δ^(2*u))^3/(4*(δ^(-6*u))^3) ∧
        Ccover*δ^(-1-12*u) ≤ δ^(-1-40*u) ∧
        144*H*δ ≤ 3*(δ^a)^2 ∧
        (δ^(-1-40*u))^3*((6*C+35)/δ^a)^6*(δ^(-40*u)*(6*δ)^s)^2 < (δ^(40*u))^2 := by
  obtain ⟨u,τ,hu,hτ,huε,huτ,hc₁',hc₂',hug⟩ :=
    exists_endpoint_selection_losses hε₀ hc₁ hc₂ hgap
  let ε := u/2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεu : ε < u := by dsimp [ε]; linarith
  have hεε₀ : ε < ε₀ := hεu.trans huε
  have hdepth := eventually_dyadic_loss_absorption hεu Cm
  have hlarge := (tendsto_rpow_neg_nhdsGT_zero (show -u < 0 by linarith)).eventually
    (eventually_ge_atTop Large)
  have hcoef := eventually_const_mul_rpow_lt (show -40*u < -6*u by linarith) Cpoint
  have hbase := eventually_endpoint_row_base hu hc₁' hc₂' V
  have hmass := eventually_endpoint_mass_thresholds hu huτ
  have hcover := eventually_const_mul_rpow_lt (show -1-40*u < -1-12*u by linarith) Ccover
  have herr := eventually_const_mul_rpow_lt (show (0:ℝ) < 1-2*a by linarith) (48*H)
  have hcount := eventually_endpoint_count_budget
    (s := s) (a := a) (κ := 40*u) (by nlinarith [hug]) C
  have hready := hdepth.and (hlarge.and (hcoef.and (hbase.and (hmass.and
    (hcover.and (herr.and hcount))))))
  have hn := dyadic_inverse_tendsto.eventually hready
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hn
  refine ⟨u,ε,τ,hu,hε,hτ,hεε₀,hεu,N₀,?_⟩
  intro N hN
  rcases hN₀ N hN with ⟨hd,hL,hC,hB,hM,hT,hE,hF⟩
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨?_,hL,hC.2.le,hB.2,hM.2.1,hM.2.2,hT.2.le,?_,by simpa only [neg_mul] using hF.2⟩
  · have hh := hd.2
    rw [dyadic_log_depth N] at hh
    simpa only [Nat.cast_add,Nat.cast_one,mul_assoc,mul_comm,mul_left_comm] using hh
  · have hp : δ^(1-2*a)*(δ^a)^2 = δ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hδ.le,← Real.rpow_add hδ]
      norm_num only [Nat.cast_ofNat]
      rw [show 1-2*a+a*(2:ℝ) = 1 by ring,Real.rpow_one]
    have hh := mul_lt_mul_of_pos_right hE.2 (sq_pos_of_pos (Real.rpow_pos_of_pos hδ a))
    have heq : (48*H)*δ^(1-2*a)*(δ^a)^2 = (48*H)*δ := by rw [mul_assoc,hp]
    rw [Real.rpow_zero,one_mul,heq] at hh
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_OriginalDirectionChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Selecting a small direction chart on the original incidence labels -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem sphere_chart_pair_inner_nonnegative (w v c : Sphere d)
    (hw : dist w c ≤ 1/2) (hv : dist v c ≤ 1/2) :
    0 ≤ inner ℝ (w:Space d) (v:Space d) := by
  have hd : dist w v ≤ 1 := (dist_triangle w c v).trans (by rw [dist_comm c v]; linarith)
  have hn : ‖(w:Space d)-(v:Space d)‖ ≤ 1 := by simpa only [Subtype.dist_eq,dist_eq_norm] using hd
  have hsq := norm_sub_sq_real (w:Space d) (v:Space d)
  rw [sphere_norm,sphere_norm] at hsq
  nlinarith [norm_nonneg ((w:Space d)-(v:Space d))]

theorem original_direction_chart_selection
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [SFinite μ] [SFinite ν]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {ρ : ℝ} (hρ : 0 < ρ) {a : ℝ≥0∞}
    (hmean : ENNReal.ofReal ((2/ρ+1)^d)*a < (μ.prod ν) E) :
    ∃ c : Sphere d, a < (μ.prod (ν.restrict (closedBall c ρ))) E := by
  classical
  obtain ⟨S,_,hcover,hcard,_⟩ := finite_separated_cap_net d (show 0 < 2*ρ by positivity)
  have hcover' (w : Sphere d) : ∃ c ∈ S, dist w c ≤ ρ := by
    have hr : (2*ρ)/2 = ρ := by ring
    simpa only [hr] using hcover w
  let F : Sphere d → Set (Space d × Sphere d) := fun c => E ∩ (univ ×ˢ closedBall c ρ)
  have hsub : E ⊆ ⋃ c ∈ S, F c := by
    intro z hz
    obtain ⟨c,hc,hd⟩ := hcover' z.2
    exact mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,hz,mem_univ _,hd⟩⟩
  have hmass : (μ.prod ν) E ≤ ∑ c ∈ S, (μ.prod ν) (F c) :=
    (measure_mono hsub).trans (measure_biUnion_finset_le S F)
  have he (c : Sphere d) : (μ.prod ν) (F c) = (μ.prod (ν.restrict (closedBall c ρ))) E := by
    have hprod : μ.prod (ν.restrict (closedBall c ρ)) =
        (μ.prod ν).restrict (univ ×ˢ closedBall c ρ) := by
      simpa only [Measure.restrict_univ] using
        Measure.prod_restrict (μ := μ) (ν := ν) univ (closedBall c ρ)
    rw [hprod,Measure.restrict_apply hE]
  by_contra! hn
  have hsum : (μ.prod ν) E ≤ (S.card:ℝ≥0∞)*a := hmass.trans (by
    calc
      _ ≤ ∑ _c ∈ S, a := Finset.sum_le_sum (fun c _ => by rw [he]; exact hn c)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul])
  have hcard' : (S.card:ℝ≥0∞) ≤ ENNReal.ofReal ((2/ρ+1)^d) := by
    have hh : (S.card:ℝ) ≤ (2/ρ+1)^d := by
      have hr : 4/(2*ρ)+1 = 2/ρ+1 := by field_simp; ring
      simpa only [hr] using hcard
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hh
  exact (not_le_of_gt hmean) (hsum.trans (mul_le_mul' hcard' le_rfl))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-vector Gaussian band estimates for the angular slicing construction -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussianBandConstant_pos : 0 < gaussianBandConstant := by
  unfold gaussianBandConstant
  positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianPairBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regularized two-vector Gaussian band bounds -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussianPairBandConstant_pos : 0 < gaussianPairBandConstant := by
  unfold gaussianPairBandConstant
  have := gaussianBandConstant_pos
  positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianBox
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian bounds for nonsingular systems of linear bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {j : ℕ}

theorem coordinateBox_measurable (r : ℝ) : MeasurableSet (coordinateBox j r) := by
  simp only [coordinateBox,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

theorem coordinateBox_volume {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (Space j)) (coordinateBox j r) = ENNReal.ofReal ((2*r)^j) := by
  rw [← (PiLp.volume_preserving_toLp (Fin j)).measure_preimage
    (coordinateBox_measurable r).nullMeasurableSet]
  have he : (@WithLp.toLp 2 (Fin j → ℝ)) ⁻¹' coordinateBox j r =
      Set.pi univ (fun _ : Fin j => Icc (-r) r) := by
    ext x
    simp [coordinateBox,abs_le,Pi.le_def,forall_and]
  rw [he,volume_pi_pi]
  simp only [Real.volume_Icc,sub_neg_eq_add,← two_mul,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,← ENNReal.ofReal_pow (by positivity : 0 ≤ 2*r)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianRowMap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear maps and kernel planes for the Gaussian slicing parameters -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem coordinate_norm_le_card_mul (x : Space h) {r : ℝ}
    (hx : ∀ i, |x i| ≤ r) : ‖x‖ ≤ (h:ℝ)*r := by
  calc
    _ = ‖∑ i : Fin h, x i • EuclideanSpace.basisFun (Fin h) ℝ i‖ := by
      exact congrArg norm ((EuclideanSpace.basisFun (Fin h) ℝ).sum_repr x).symm
    _ ≤ ∑ i : Fin h, ‖x i • EuclideanSpace.basisFun (Fin h) ℝ i‖ := norm_sum_le _ _
    _ = ∑ i : Fin h, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,Real.norm_eq_abs,(EuclideanSpace.basisFun (Fin h) ℝ).norm_eq_one,mul_one]
    _ ≤ ∑ _ : Fin h, r := Finset.sum_le_sum (fun i _ => hx i)
    _ = _ := by simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianLocalBand
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Band mass inside a fixed neighborhood of a transverse row -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n : ℕ}

theorem gaussianLocalBandConstant_pos {ρ : ℝ} (hρ : 0 < ρ) :
    0 < gaussianLocalBandConstant n ρ := by
  unfold gaussianLocalBandConstant gaussianVolumeNormalization
  positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The north-hemisphere gnomonic chart

This is the explicit inverse gnomonic map, in Euclidean coordinates.
The measure identity used with this map is kept separate as a published
input; all the coordinate identities below are proved.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem northLift_continuous (n : ℕ) : Continuous (@northLift n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · simpa only [Fin.cons_succ] using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)

theorem gnomonicChart_continuous (n : ℕ) : Continuous (@gnomonicChart n) := by
  apply Continuous.subtype_mk
  exact ((northLift_continuous n).norm.inv₀ (fun x =>
    norm_ne_zero_iff.mpr (northLift_ne_zero x))).smul (northLift_continuous n)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FrameEmbedding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The linear isometry associated with a finite orthonormal frame -/

namespace Falconer
variable {d h : ℕ}

theorem frameLinearMap_orthonormal {v : Fin h → Space d} (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (frameLinearMap v ∘ (EuclideanSpace.basisFun (Fin h) ℝ).toBasis) := by
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  change inner ℝ (frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i))
    (frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ j)) = _
  simpa only [frameLinearMap_basis] using hv i j

theorem orthonormal_frame_embedding {v : Fin h → Space d} (hv : Orthonormal ℝ v) :
    ∃ e : Space h →ₗᵢ[ℝ] Space d,
      ∀ i, e (EuclideanSpace.basisFun (Fin h) ℝ i) = v i := by
  let e : Space h →ₗᵢ[ℝ] Space d := (frameLinearMap v).isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin h) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin h) ℝ).orthonormal (frameLinearMap_orthonormal hv)
  refine ⟨e,?_⟩
  intro i
  change frameLinearMap v (EuclideanSpace.basisFun (Fin h) ℝ i) = v i
  exact frameLinearMap_basis v i

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_TransverseFrame
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniformly transverse row frame for each fixed spherical chart -/

namespace Falconer
variable {n h : ℕ}

theorem exists_transverse_row_frame (hhn : h ≤ n) {w : Space (n+1)} (hw : ‖w‖ = 1) :
    ∃ e : Space h →ₗᵢ[ℝ] Space (n+1),
      ∀ i, inner ℝ w (e (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0 := by
  let u := EuclideanSpace.basisFun (Fin (n+1)) ℝ 0
  let R : Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) := (ℝ ∙ (u-w))ᗮ.reflection
  have hR : R u = w := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0).trans hw.symm)
  let f : Fin h → Fin (n+1) := fun i => ⟨i.val+1,by omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have he := congrArg Fin.val hij
    dsimp [f] at he
    omega
  let v : Fin h → Space (n+1) := fun i => R (EuclideanSpace.basisFun (Fin (n+1)) ℝ (f i))
  have hv : Orthonormal ℝ v := by
    exact ((EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.comp f hf).comp_linearIsometryEquiv R
  obtain ⟨e,he⟩ := orthonormal_frame_embedding hv
  refine ⟨e,fun i => ?_⟩
  rw [he,← hR]
  change inner ℝ (R u) (R (EuclideanSpace.basisFun (Fin (n+1)) ℝ (f i))) = 0
  rw [R.inner_map_map]
  exact (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal.2 (by
    intro heq
    have hz := congrArg Fin.val heq
    dsimp [f] at hz
    omega)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original direction labels in affine gnomonic coordinates -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

theorem gnomonicCoordinates_measurable : Measurable (@gnomonicCoordinates n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  fun_prop

theorem northLift_gnomonicCoordinates (w : Sphere (n+1))
    (hw : 0 < (w:Space (n+1)) 0) :
    northLift (gnomonicCoordinates w) = ((w:Space (n+1)) 0)⁻¹ • (w:Space (n+1)) := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [northLift_zero,PiLp.smul_apply,smul_eq_mul]
    exact (inv_mul_cancel₀ hw.ne').symm
  · simp only [northLift_succ,gnomonicCoordinates_apply,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv]
    exact mul_comm _ _

theorem gnomonicChart_gnomonicCoordinates (w : Sphere (n+1))
    (hw : 0 < (w:Space (n+1)) 0) :
    gnomonicChart (gnomonicCoordinates w) = w := by
  apply Subtype.ext
  change ‖northLift (gnomonicCoordinates w)‖⁻¹ • northLift (gnomonicCoordinates w) = _
  rw [northLift_gnomonicCoordinates w hw,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hw),sphere_norm,mul_one,inv_inv,smul_smul]
  rw [mul_inv_cancel₀ hw.ne',one_smul]

end Falconer

/-! # Explicit inverse and cone coordinates for the gnomonic measure formula -/

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transporting an original direction law to its affine chart -/

namespace Falconer
open Set Metric MeasureTheory
variable {n : ℕ}

theorem gnomonicCoordinates_map_recover (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ (w : Sphere (n+1)) ∂ν, 0 < (w:Space (n+1)) 0) :
    Measure.map gnomonicChart (Measure.map gnomonicCoordinates ν) = ν := by
  rw [Measure.map_map (gnomonicChart_continuous n).measurable gnomonicCoordinates_measurable]
  calc
    _ = Measure.map id ν := Measure.map_congr (by
      filter_upwards [hν] with w hw
      exact gnomonicChart_gnomonicCoordinates w hw)
    _ = ν := Measure.map_id

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TroublesomePair
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable troublesome pairs use the full original conditional source law -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem measurable_normalized_vector {X : Type*} [MeasurableSpace X]
    {f : X → Space d} (hf : Measurable f) :
    Measurable (fun x => NormedSpace.normalize (f x)) :=
  hf.norm.inv.smul hf

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerRectangle
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer rectangles arising from projected tube covers -/

namespace Falconer

theorem integer_near_real_bounds (z : ℤ) (x r : ℝ) (L : ℕ)
    (hz : |(z:ℝ)-x| ≤ r) (hL : r+1/2 ≤ (L:ℝ)) :
    round x-(L:ℤ) ≤ z ∧ z ≤ round x+(L:ℤ) := by
  have hh : |(z:ℝ)-(round x:ℝ)| ≤ (L:ℝ) :=
    ((abs_sub_le (z:ℝ) x (round x:ℝ)).trans
      (add_le_add hz (abs_sub_round x))).trans hL
  have hi : |z-round x| ≤ (L:ℤ) := by exact_mod_cast hh
  have h := abs_le.mp hi
  constructor <;> omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TripleGridRounding
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rounding bounded physical point sets in transverse coordinates -/

namespace Falconer
open Set Metric

theorem round_mesh_error {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |t-δ*(round (t/δ):ℝ)| ≤ δ/2 := by
  have he : t-δ*(round (t/δ):ℝ) = δ*(t/δ-(round (t/δ):ℝ)) := by field_simp
  rw [he,abs_mul,abs_of_pos hδ]
  have hh := mul_le_mul_of_nonneg_left (abs_sub_round (t/δ)) hδ.le
  nlinarith

theorem round_bound {δ R : ℝ} (hδ : 0 < δ) (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ))
    (t : ℝ) (ht : |t| ≤ R) : -(L:ℤ) ≤ round (t/δ) ∧ round (t/δ) ≤ (L:ℤ) := by
  have hh : |(round (t/δ):ℝ)| ≤ (L:ℝ) := by
    have hs := abs_sub_round (t/δ)
    have htri := abs_sub_le (round (t/δ):ℝ) (t/δ) 0
    rw [sub_zero,sub_zero,abs_sub_comm (round (t/δ):ℝ)] at htri
    have hd : |t/δ| ≤ R/δ := by
      rw [abs_div,abs_of_pos hδ]
      exact div_le_div_of_nonneg_right ht hδ.le
    linarith
  have hi : |round (t/δ)| ≤ (L:ℤ) := by exact_mod_cast hh
  exact abs_le.mp hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SliceNormalization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalizing the retained original-label slice laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalizedSliceLaw_apply (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) (S : Set X) :
    (normalizedSliceLaw μ hμ : Measure X) S = (μ univ)⁻¹*μ S := rfl

theorem normalizedSliceLaw_bound (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) (S : Set X) {L B : ℝ≥0∞}
    (hL : L ≤ μ univ) (hS : μ S ≤ B) :
    (normalizedSliceLaw μ hμ : Measure X) S ≤ L⁻¹*B := by
  rw [normalizedSliceLaw_apply]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr hL) hS

theorem normalizedSliceLaw_ae (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ univ ≠ 0) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂(normalizedSliceLaw μ hμ : Measure X), P x :=
  Measure.ae_smul_measure hP _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ActiveCoverScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original tube count after codimension-h slicing -/

namespace Falconer

theorem gaussian_active_cover_scale {δ ε κ q Nc D : ℝ} (h : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hεκ : ε ≤ κ) (hD : 0 ≤ D)
    (hNc : Nc ≤ δ^(-q-ε)) :
    (δ^(-κ))^11*(Nc*(2*(D*δ))^h) ≤
      (2*D)^h*(δ^(-κ))^12*δ^(-(q-(h:ℝ))) := by
  have hε : δ^(-ε) ≤ δ^(-κ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεκ)
  have hpower : δ^(-q-ε)*δ^h = δ^(-ε)*δ^(-(q-(h:ℝ))) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hδ,← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ ≤ (δ^(-κ))^11*(δ^(-q-ε)*(2*(D*δ))^h) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNc (by positivity)) (by positivity)
    _ = (2*D)^h*(δ^(-κ))^11*(δ^(-ε)*δ^(-(q-(h:ℝ)))) := by
      rw [show 2*(D*δ) = (2*D)*δ by ring,mul_pow]
      calc
        _ = (2*D)^h*(δ^(-κ))^11*(δ^(-q-ε)*δ^h) := by ring
        _ = _ := by rw [hpower]
    _ ≤ (2*D)^h*(δ^(-κ))^11*(δ^(-κ)*δ^(-(q-(h:ℝ)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hε (Real.rpow_nonneg hδ.le _)) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointApplicationNumerics
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar endpoint budgets in the form used by the controlled slice -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

theorem endpoint_stable_small {h : ℕ} {δ ρ : ℝ} (hδ : δ ≤ ρ)
    (hs : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) : 2*(h:ℝ)*δ < 1 := by
  have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
  have hn : (h+3:ℝ) ≥ 1 := by linarith
  have hb : (h:ℝ)*ρ ≤ 1/4 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hδ hh]

theorem endpoint_active_cover_power {h : ℕ} {δ ε u C ρ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hεu : ε ≤ u) (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hcount : (2*(1+2*(1/4)+C*((h+3:ℝ)*(2*ρ)+1)))^h*δ^(-1-12*u) ≤ δ^(-1-40*u)) :
    (δ^(-u))^11*(δ^(-(h+1:ℝ)-ε)*
      (2*(δ+(2*(1/4))*δ+(C*δ)*((h+3:ℝ)*(2*ρ)+1)))^h) ≤ δ^(-1-40*u) := by
  let D : ℝ := 1+2*(1/4)+C*((h+3:ℝ)*(2*ρ)+1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hh := gaussian_active_cover_scale h hδ hδ1 hεu hD
    (le_refl (δ^(-(h+1:ℝ)-ε)))
  have hr : δ+(2*(1/4))*δ+(C*δ)*((h+3:ℝ)*(2*ρ)+1) = D*δ := by dsimp [D]; ring
  rw [hr]
  have hq : -((h+1:ℝ)-(h:ℝ)) = -1 := by ring
  rw [hq] at hh
  simp only [gaussian_scale_power hδ,Nat.cast_ofNat] at hh
  have hp : δ^(-(12*u))*δ^((-1:ℝ)) = δ^(-1-12*u) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  rw [mul_assoc,hp] at hh
  simpa only [gaussian_scale_power hδ,Nat.cast_ofNat] using hh.trans hcount

theorem endpoint_bad_mass_ennreal {δ u τ : ℝ} (hδ : 0 < δ)
    (hbad : δ^τ+2*δ^(-6*u)*δ^τ ≤ (δ^(2*u))^3/(4*(δ^(-6*u))^3)) :
    ENNReal.ofReal (δ^τ)+2*ENNReal.ofReal ((δ^(-u))^6)*ENNReal.ofReal (δ^τ) ≤
      ENNReal.ofReal ((δ^(2*u))^3/(4*((δ^(-u))^6)^3)) := by
  have hp : (δ^(-u))^6 = δ^(-6*u) := by
    simpa only [Nat.cast_ofNat,neg_mul] using gaussian_scale_power hδ 6
  rw [hp]
  calc
    _ = ENNReal.ofReal (δ^τ+2*δ^(-6*u)*δ^τ) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 2*δ^(-6*u)),
        ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbad

theorem endpoint_selection_row_budget {δ u τ c₁ c₂ V : ℝ}
    (hδ : 0 < δ) (hV : 0 ≤ V) (Z A₁ A₂ : ℝ≥0∞)
    (hZ : Z ≤ ENNReal.ofReal V)
    (hA₁ : A₁ ≤ ENNReal.ofReal (δ^c₁)) (hA₂ : A₂ ≤ ENNReal.ofReal (δ^c₂))
    (hbase : V*δ^(2*u)+V*δ^(c₁-τ-9*u)+V*δ^(c₂-τ-9*u) ≤ δ^u/4) :
    ENNReal.ofReal (δ^(2*u))*Z+
      (ENNReal.ofReal ((δ^(-u))^6)*ENNReal.ofReal ((δ^(-u))^3)*Z)*(A₁/ENNReal.ofReal (δ^τ))+
      (ENNReal.ofReal ((δ^(-u))^6)*ENNReal.ofReal ((δ^(-u))^3)*Z)*(A₂/ENNReal.ofReal (δ^τ)) ≤
      ENNReal.ofReal (1/(4*δ^(-u))) := by
  have hh := endpoint_row_base_ennreal hδ hV Z A₁ A₂ hZ hA₁ hA₂ hbase
  have hp (j : ℕ) : (δ^(-u))^j = δ^(-((j:ℝ)*u)) := gaussian_scale_power hδ j
  have hi : δ^u/4 = 1/(4*δ^(-u)) := by rw [Real.rpow_neg hδ.le]; field_simp
  rw [hp 6,hp 3]
  simpa only [Nat.cast_ofNat,neg_mul,hi] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicCap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A small spherical cap has bounded original affine coordinates -/

namespace Falconer
open Metric MeasureTheory
variable {n : ℕ}

theorem gnomonic_cap_first_coordinate (w : Sphere (n+1))
    (hw : dist w (gnomonicChart (0 : Space n)) ≤ 1/2) :
    7/8 ≤ (w:Space (n+1)) 0 := by
  have hh := norm_sub_sq_real (w:Space (n+1)) (northLift (0 : Space n))
  rw [sphere_norm,northLift_zero_norm,inner_northLift_zero] at hh
  have hd : ‖(w:Space (n+1))-northLift (0 : Space n)‖ ≤ 1/2 := by
    simpa only [Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
  nlinarith [norm_nonneg ((w:Space (n+1))-northLift (0 : Space n))]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_SmallGnomonicCap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small chart law lies in the unit cube used by radial pruning -/

namespace Falconer
open Metric MeasureTheory
variable {n : ℕ}

lemma gnomonic_cap_coordinates_norm_le (w : Sphere (n+1)) {ρ : ℝ}
    (hw : dist w (gnomonicChart (0 : Space n)) ≤ ρ) (hρ : ρ ≤ 1/2) :
    ‖gnomonicCoordinates w‖ ≤ 2*ρ := by
  have hw0 := gnomonic_cap_first_coordinate w (hw.trans hρ)
  have hp : 0 < (w:Space (n+1)) 0 := by linarith
  let v : Space (n+1) := (w:Space (n+1))-northLift 0
  let t : Space n := WithLp.toLp 2 (fun i => v i.succ)
  have ht : ‖t‖ ≤ ‖v‖ := by
    have hs : ‖t‖^2 ≤ ‖v‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
      simp only [t]
      exact le_add_of_nonneg_left (sq_nonneg (v 0))
    nlinarith [norm_nonneg t,norm_nonneg v]
  have hv : ‖v‖ ≤ ρ := by
    simpa only [v,Subtype.dist_eq,gnomonicChart_zero_coe,dist_eq_norm] using hw
  have he : gnomonicCoordinates w = ((w:Space (n+1)) 0)⁻¹ • t := by
    ext i
    simp only [gnomonicCoordinates_apply,PiLp.smul_apply,smul_eq_mul,t,
      v,PiLp.sub_apply,northLift_succ,PiLp.zero_apply,sub_zero,div_eq_mul_inv]
    ring
  have hi : ((w:Space (n+1)) 0)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    linarith
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  exact (mul_le_mul_of_nonneg_left (ht.trans hv) (inv_nonneg.mpr hp.le)).trans
    (mul_le_mul_of_nonneg_right hi (by linarith [norm_nonneg v]))

lemma small_gnomonic_cap_law (ν : Measure (Sphere (n+1)))
    (hν : ∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space n)) ≤ 1/8) :
    ∀ᵐ p ∂Measure.map gnomonicCoordinates ν, ‖p‖ ≤ 1/4 := by
  rw [ae_map_iff gnomonicCoordinates_measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  filter_upwards [hν] with w hw
  have hh := gnomonic_cap_coordinates_norm_le w hw (by norm_num : (1/8:ℝ) ≤ 1/2)
  norm_num at hh ⊢
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteOverlap
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting heavy members of a finite family with bounded overlap -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {X ι : Type*} [MeasurableSpace X]
attribute [local instance] Classical.propDecidable

theorem finite_measure_sum_le_overlap (μ : Measure X) (I : Finset ι) (U : ι → Set X)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (L : ℕ)
    (hoverlap : ∀ x, (I.filter (fun i => x ∈ U i)).card ≤ L) :
    ∑ i ∈ I, μ (U i) ≤ (L:ℝ≥0∞)*μ univ := by
  classical
  have hp (x : X) : (∑ i ∈ I, (U i).indicator (fun _ => (1:ℝ≥0∞)) x) =
      ((I.filter (fun i => x ∈ U i)).card:ℝ≥0∞) := by
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp
  calc
    _ = ∑ i ∈ I, ∫⁻ x, (U i).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ :=
      Finset.sum_congr rfl (fun i hi => (lintegral_indicator_one (hU i hi)).symm)
    _ = ∫⁻ x, ∑ i ∈ I, (U i).indicator (fun _ => (1:ℝ≥0∞)) x ∂μ := by
      rw [lintegral_finsetSum' I (fun i hi => (measurable_const.indicator (hU i hi)).aemeasurable)]
    _ ≤ ∫⁻ _x, (L:ℝ≥0∞) ∂μ := lintegral_mono (fun x => by
      rw [hp]
      exact Nat.cast_le.mpr (hoverlap x))
    _ = _ := lintegral_const _

theorem heavy_family_card_bound (μ : Measure X) (I : Finset ι) (U : ι → Set X)
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (L : ℕ)
    (hoverlap : ∀ x, (I.filter (fun i => x ∈ U i)).card ≤ L)
    (F : ℝ≥0∞) (hheavy : ∀ i ∈ I, F ≤ μ (U i)) :
    (I.card:ℝ≥0∞)*F ≤ (L:ℝ≥0∞)*μ univ := by
  calc
    _ = ∑ _i ∈ I, F := by simp
    _ ≤ ∑ i ∈ I, μ (U i) := Finset.sum_le_sum hheavy
    _ ≤ _ := finite_measure_sum_le_overlap μ I U hU L hoverlap

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_IntegerBox
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product grid boxes for the general-dimensional tube count -/

namespace Falconer
open scoped BigOperators
variable {n : ℕ}

theorem integer_box_card (T : Finset (Fin n → ℤ)) (x : Fin n → ℝ) (r : ℝ) (L : ℕ)
    (hL : r+1/2 ≤ (L:ℝ)) (hT : ∀ z ∈ T, ∀ j, |(z j:ℝ)-x j| ≤ r) :
    T.card ≤ (2*L+1)^n := by
  classical
  let B (j : Fin n) := Finset.Icc (round (x j)-(L:ℤ)) (round (x j)+(L:ℤ))
  have hsub : T ⊆ Fintype.piFinset B := by
    intro z hz
    apply Fintype.mem_piFinset.mpr
    intro j
    exact Finset.mem_Icc.mpr (integer_near_real_bounds (z j) (x j) r L (hT z hz j) hL)
  have hB (j : Fin n) : (B j).card = 2*L+1 := by
    dsimp [B]
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans_eq (by simp only [Fintype.card_piFinset,hB,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GeneralGridRounding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded original point sets admit finite transverse lattice approximations -/

namespace Falconer
open Set Metric
variable {n : ℕ}

theorem euclideanRound_distance {δ : ℝ} (hδ : 0 < δ) (x : Space (n+1)) :
    dist x (euclideanIntegerGrid δ (euclideanRound δ x)) ≤ ((n+1:ℕ):ℝ)*δ/2 := by
  rw [dist_eq_norm]
  have hh := coordinate_norm_le_card_mul (x-euclideanIntegerGrid δ (euclideanRound δ x))
    (r := δ/2) (fun i => round_mesh_error hδ (x i))
  nlinarith

theorem euclideanRound_mem_box {δ R : ℝ} (hδ : 0 < δ) (L : ℕ)
    (hL : R/δ+1 ≤ (L:ℝ)) (x : Space (n+1)) (hx : ‖x‖ ≤ R) :
    euclideanRound δ x ∈ integerGridBox n L := by
  apply Fintype.mem_piFinset.mpr
  intro i
  exact Finset.mem_Icc.mpr (round_bound hδ L hL (x i) ((PiLp.norm_apply_le x i).trans hx))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_GridBallOverlap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform overlap of fixed-width lattice cells -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem grid_ball_overlap (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ}
    (hδ : 0 < δ) (L : ℕ) (hL : C+1/2 ≤ (L:ℝ)) (x : Space (n+1)) :
    (S.filter (fun z => ‖x-euclideanIntegerGrid δ z‖ ≤ C*δ)).card ≤ (2*L+1)^(n+1) := by
  apply integer_box_card _ (fun j => x j/δ) C L hL
  intro z hz j
  have hb := (PiLp.norm_apply_le (x-euclideanIntegerGrid δ z) j).trans (Finset.mem_filter.mp hz).2
  change |x j-δ*(z j:ℝ)| ≤ C*δ at hb
  have hd : |(x j-δ*(z j:ℝ))/δ| ≤ C := by
    rw [abs_div,abs_of_pos hδ]
    exact (div_le_iff₀ hδ).mpr hb
  have he : (x j-δ*(z j:ℝ))/δ = x j/δ-(z j:ℝ) := by field_simp
  rw [he,abs_sub_comm] at hd
  exact hd

theorem grid_ball_heavy_card (μ : Measure (Space (n+1)))
    (f : Space (n+1) → Space (n+1)) (hf : Measurable f)
    (S : Finset (Fin (n+1) → ℤ)) {δ C : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : C+1/2 ≤ (L:ℝ)) (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ S, F ≤ μ {x | ‖f x-euclideanIntegerGrid δ z‖ ≤ C*δ}) :
    (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  apply heavy_family_card_bound μ S
    (fun z => {x | ‖f x-euclideanIntegerGrid δ z‖ ≤ C*δ})
    (fun z _ => measurableSet_le (by fun_prop) measurable_const)
    ((2*L+1)^(n+1)) (fun x => grid_ball_overlap S hδ L hL (f x)) F hheavy

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyProjectedCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite cover of sources whose full projected local mass is heavy -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n : ℕ}

theorem heavy_projected_grid_cover (μ : Measure (Space (n+1)))
    (f : Space (n+1) → Space (n+1)) (hf : Measurable f)
    (T : Set (Space (n+1))) {R δ C : ℝ} (hδ : 0 < δ)
    (hT : ∀ z ∈ T, ‖f z‖ ≤ R) (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y | ‖f y-f z‖ ≤ C*δ})
    (L : ℕ) (hL : C+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ P : Finset (Space (n+1)),
      (∀ z ∈ T, ∃ p ∈ P, ‖f z-p‖ ≤ ((n+1:ℕ):ℝ)*δ) ∧
      (P.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  classical
  obtain ⟨N,hN⟩ := exists_nat_ge (R/δ+1)
  let I := integerGridBox n N
  let U (q : Fin (n+1) → ℤ) : Set (Space (n+1)) :=
    {y | ‖f y-euclideanIntegerGrid δ q‖ ≤ (C+((n+1:ℕ):ℝ))*δ}
  let H := I.filter (fun q => F ≤ μ (U q))
  let P := H.image (euclideanIntegerGrid δ)
  have hm := grid_ball_heavy_card μ f hf H hδ L hL F
    (fun q hq => (Finset.mem_filter.mp hq).2)
  refine ⟨P,?_,?_⟩
  · intro z hz
    let q := euclideanRound δ (f z)
    have hqI : q ∈ I := euclideanRound_mem_box hδ N hN (f z) (hT z hz)
    have hclose : ‖f z-euclideanIntegerGrid δ q‖ ≤ ((n+1:ℕ):ℝ)*δ := by
      have he := euclideanRound_distance hδ (f z)
      rw [dist_eq_norm] at he
      have hd : 0 ≤ ((n+1:ℕ):ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
      exact he.trans (by linarith)
    have hsub : {y | ‖f y-f z‖ ≤ C*δ} ⊆ U q := by
      intro y hy
      change ‖f y-euclideanIntegerGrid δ q‖ ≤ _
      calc
        _ ≤ ‖f y-f z‖+‖f z-euclideanIntegerGrid δ q‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C*δ+((n+1:ℕ):ℝ)*δ := add_le_add hy hclose
        _ = _ := by ring
    have hqH : q ∈ H := Finset.mem_filter.mpr ⟨hqI,(hheavy z hz).trans (measure_mono hsub)⟩
    exact ⟨_,Finset.mem_image.mpr ⟨q,hqH,rfl⟩,hclose⟩
  · have hc : (P.card:ℝ≥0∞) ≤ (H.card:ℝ≥0∞) := by exact_mod_cast Finset.card_image_le
    exact (mul_le_mul' hc le_rfl).trans hm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialFreezing
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freezing radial directions in a source cell away from its pin -/

namespace Falconer
open NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalize_distance_scaled {u v : E} {r : ℝ}
    (hu : r ≤ ‖u‖) (hv : v ≠ 0) :
    r*dist (normalize u) (normalize v) ≤ 2*dist u v := by
  have he : ‖u‖ • (normalize u-normalize v) =
      u-v+(‖v‖-‖u‖) • normalize v := by
    rw [smul_sub,norm_smul_normalize,sub_smul,norm_smul_normalize]
    abel
  have hb := norm_add_le (u-v) ((‖v‖-‖u‖) • normalize v)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    norm_smul,Real.norm_eq_abs,norm_normalize hv,mul_one] at hb
  have hn := abs_norm_sub_norm_le v u
  rw [norm_sub_rev v u] at hn
  rw [dist_eq_norm,dist_eq_norm]
  have hh := mul_le_mul_of_nonneg_right hu (norm_nonneg (normalize u-normalize v))
  linarith

theorem perpendicular_normalize_self (v : E) : perpendicularPart (normalize v) v = 0 := by
  by_cases hv : v = 0
  · simp [hv,perpendicularPart,NormedSpace.normalize]
  · have he : v = ‖v‖ • normalize v := (norm_smul_normalize v).symm
    calc
      _ = perpendicularPart (normalize v) (‖v‖ • normalize v) := congrArg _ he
      _ = ‖v‖ • perpendicularPart (normalize v) (normalize v) := perpendicularPart_smul _ _ _
      _ = 0 := by simp [perpendicularPart,norm_normalize hv]

theorem frozen_radial_tube_error (x c z y : E) {r D W : ℝ}
    (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hzx : z ≠ x)
    (hzc : ‖z-c‖ ≤ D) (hyc : ‖y-c‖ ≤ D)
    (htube : ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W) :
    ‖perpendicularPart (normalize (c-x)) (y-z)‖ ≤ W+8*D^2/r := by
  have hc0 : c-x ≠ 0 := norm_pos_iff.mp (hr.trans_le hcx)
  have hz0 : z-x ≠ 0 := sub_ne_zero.mpr hzx
  have hD : 0 ≤ D := (norm_nonneg _).trans hzc
  have hd : ‖normalize (c-x)-normalize (z-x)‖ ≤ 2*D/r := by
    apply (le_div_iff₀ hr).mpr
    have hh := normalize_distance_scaled hcx hz0
    have he : dist (c-x) (z-x) = ‖z-c‖ := by
      rw [dist_eq_norm,sub_sub_sub_cancel_right,norm_sub_rev]
    rw [he,dist_eq_norm] at hh
    nlinarith
  have hyz : ‖y-z‖ ≤ 2*D := by
    have hh := norm_sub_le_norm_sub_add_norm_sub y c z
    rw [norm_sub_rev c z] at hh
    linarith
  have hshift : perpendicularPart (normalize (z-x)) (y-z) =
      perpendicularPart (normalize (z-x)) (y-x) := by
    have he : y-z = (y-x)-(z-x) := by abel
    rw [he,perpendicularPart_sub,perpendicular_normalize_self,sub_zero]
  have herr := perpendicularPart_direction_error (norm_normalize hc0) (norm_normalize hz0) (y-z)
  have hu : ‖perpendicularPart (normalize (c-x)) (y-z) -
      perpendicularPart (normalize (z-x)) (y-z)‖ ≤ 8*D^2/r := by
    apply herr.trans
    calc
      _ ≤ 2*(2*D/r)*(2*D) := by gcongr
      _ = _ := by ring
  calc
    _ = ‖(perpendicularPart (normalize (c-x)) (y-z)-
        perpendicularPart (normalize (z-x)) (y-z))+
          perpendicularPart (normalize (z-x)) (y-z)‖ := by congr 1; abel
    _ ≤ ‖perpendicularPart (normalize (c-x)) (y-z)-
        perpendicularPart (normalize (z-x)) (y-z)‖+
          ‖perpendicularPart (normalize (z-x)) (y-z)‖ := norm_add_le _ _
    _ ≤ 8*D^2/r+W := add_le_add hu (by rw [hshift]; exact htube)
    _ = _ := add_comm _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FrozenHeavyCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual parallel tube covers of troublesome original source fibers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem perpendicularPart_idempotent (v z : Space (n+1)) (hv : ‖v‖ = 1) :
    perpendicularPart v (perpendicularPart v z) = perpendicularPart v z := by
  simp [perpendicularPart,inner_sub_right,inner_smul_right,hv]

theorem frozen_heavy_tube_cover (μ : Measure (Space (n+1))) (x c : Space (n+1))
    {r D δ C B : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y |
      ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ C*δ})
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ P : Finset (Space (n+1)),
      (∀ z ∈ T, ∃ p ∈ P,
        ‖perpendicularPart (normalize (c-x)) (z-p)‖ ≤ ((n+1:ℕ):ℝ)*δ) ∧
      (P.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  let v := normalize (c-x)
  have hv : ‖v‖ = 1 := norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))
  let f : Space (n+1) → Space (n+1) := perpendicularPart v
  have hf : Measurable f := by unfold f perpendicularPart; fun_prop
  have hbd : ∀ z ∈ T, ‖f z‖ ≤ B := fun z hz =>
    (norm_perpendicularPart_le hv z).trans (hT z hz).2.2
  have hmass : ∀ z ∈ T, F ≤ μ {y | ‖f y-f z‖ ≤ (C+1)*δ} := by
    intro z hz
    apply (hheavy z hz).trans
    apply measure_mono_ae
    filter_upwards [hsource] with y hy
    intro ht
    have hh := frozen_radial_tube_error x c z y hr hcx (hT z hz).1 (hT z hz).2.1 hy ht
    change ‖perpendicularPart v y-perpendicularPart v z‖ ≤ _
    rw [← perpendicularPart_sub]
    exact hh.trans (by nlinarith)
  obtain ⟨P,hP,hcard⟩ := heavy_projected_grid_cover μ f hf T hδ hbd F hmass L hL
  refine ⟨P,?_,hcard⟩
  intro z hz
  obtain ⟨p,hp,hclose⟩ := hP z hz
  refine ⟨p,hp,?_⟩
  have he : perpendicularPart v (z-p) = perpendicularPart v (f z-p) := by
    rw [perpendicularPart_sub,perpendicularPart_sub]
    dsimp [f]
    rw [perpendicularPart_idempotent v z hv]
  rw [he]
  exact (norm_perpendicularPart_le hv _).trans hclose

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_GaussianMomentScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common fixed coefficient for the original finite-scale moment bounds -/

namespace Falconer

theorem exists_gaussian_moment_coefficient (h : ℕ) (t q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (4*gaussianVectorBandConstant)^h*L*gaussianFrostmanFactor h t ≤ C*L ∧
      (2*gaussianPairBandConstant)^h*L*gaussianFrostmanFactor h q ≤ C*L ∧
      (2*gaussianPairBandConstant)^h*(|L*gaussianFrostmanFactor h q|+1) ≤ C*L := by
  let P := (4*gaussianVectorBandConstant)^h*gaussianFrostmanFactor h t
  let Q := (2*gaussianPairBandConstant)^h*gaussianFrostmanFactor h q
  let U := (2*gaussianPairBandConstant)^h*(|gaussianFrostmanFactor h q|+1)
  let C := |P|+|Q|+U+1
  have hG := gaussianPairBandConstant_pos
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hPC : P ≤ C := by dsimp [C]; linarith [le_abs_self P,abs_nonneg Q]
  have hQC : Q ≤ C := by dsimp [C]; linarith [le_abs_self Q,abs_nonneg P]
  have hUC : U ≤ C := by dsimp [C]; linarith [abs_nonneg P,abs_nonneg Q]
  refine ⟨C,hC,?_⟩
  intro L hL
  have hL0 : 0 ≤ L := by linarith
  refine ⟨?_,?_,?_⟩
  · simpa only [P,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hPC hL0
  · simpa only [Q,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hQC hL0
  · calc
      _ = (2*gaussianPairBandConstant)^h*(L*|gaussianFrostmanFactor h q|+1) := by
        rw [abs_mul,abs_of_nonneg hL0]
      _ ≤ (2*gaussianPairBandConstant)^h*(L*|gaussianFrostmanFactor h q|+L) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hL _) (by positivity)
      _ = U*L := by dsimp [U]; ring
      _ ≤ C*L := mul_le_mul_of_nonneg_right hUC hL0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EndpointChartGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform endpoint angular decay on a small original direction cap -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem endpoint_chart_angular_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C ρ : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsProbabilityMeasure ν],
      ∀ (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ ρ) →
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν).real E ≤ (1/(2:ℝ)^N)^c := by
  classical
  let s : ℝ := t-(h:ℝ)
  let a : ℝ := (2*s-3)/12
  have hs : 3/2 < s := by dsimp [s]; linarith
  have hs' : s < 2 := by dsimp [s]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have ha' : a < 1/2 := by dsimp [a]; linarith
  have hgap : 0 < 2*s-3-6*a := by dsimp [a]; linarith
  obtain ⟨ε₀,c₁,c₂,hε₀,hc₁,hc₂,Np,hprep⟩ := endpoint_spherical_preparation (h := h) hLW hζ ha
  obtain ⟨Cm,hCm,hcoeff⟩ := exists_gaussian_moment_coefficient h t (h+1:ℝ)
  let Mrow : ℝ := (h+3:ℝ)*(2*ρ)+1
  let Z : ℝ := Mrow+1
  let V : ℝ := (2*Z)^h
  let a₀ : ℝ := 4+4*(h:ℝ)
  let D : ℝ := 1+2*(1/4)+C*Mrow
  let B₀ : ℝ := (2:ℝ)^h*gaussianLocalBandConstant (h+2) ρ^h
  have hMrow : 0 < Mrow := by dsimp [Mrow]; positivity
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have ha₀ : 1 ≤ a₀ := by dsimp [a₀]; linarith [Nat.cast_nonneg (α := ℝ) h]
  have hD : 0 < D := by dsimp [D]; positivity
  have hB₀ : 0 < B₀ := by
    have hb := gaussianLocalBandConstant_pos (n := h+2) hρ
    dsimp [B₀]
    positivity
  obtain ⟨u,ε,τ,hu,hε,hτ,hεε₀,hεu,Ns,hscalar⟩ :=
    exists_endpoint_angular_parameters hε₀ hc₁ hc₂ hgap ha' Cm
      (4*(1+2*(2:ℝ)^h+1)) V ((4*a₀)^s) ((2*D)^h) C (h:ℝ)
  have hcut := dyadic_inverse_tendsto.eventually
    ((eventually_const_mul_rpow_lt (show u/2 < u by linarith) (1/B₀)).and
      (Ioc_mem_nhdsGT hρ))
  obtain ⟨Nc,hcut⟩ := eventually_atTop.mp hcut
  refine ⟨ε,u/2,hε,by positivity,Np+Ns+Nc,?_⟩
  intro N hN ι _ _ μ ν _ _ E J v hν hμ hμmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  let K : ℝ := δ^(-u)
  let L : ℝ := δ^(-ε)
  let Ncover : ℝ := δ^(-(h+1:ℝ)-ε)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨habs,hδρ'⟩ := hcut N (by omega)
  have hδρ : δ ≤ ρ := hδρ'.2
  have hδ1 : δ ≤ 1 := hδρ.trans (hρsmall.trans (by norm_num))
  obtain ⟨hcard,hlarge,hcoef,hbase,hmass,hbad,hcount,herror,hbudget⟩ := hscalar N (by omega)
  have hL : 1 ≤ L := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -ε ≤ 0 by linarith)
  have hK : 1 ≤ K := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (show -u ≤ 0 by linarith)
  have hCK : Cm*L ≤ K := by
    have hN1 : (1:ℝ) ≤ (N+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    exact (le_mul_of_one_le_left (by positivity : 0 ≤ Cm*L) hN1).trans hcard
  have hloss : L ≤ ((2:ℝ)^N)^ε₀ := by
    rw [dyadic_loss_conversion]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεε₀.le)
  have hcap : ∀ᵐ (w : Sphere (h+3)) ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ 1/8 := by
    filter_upwards [hν] with w hw
    exact hw.trans hρsmall
  obtain ⟨G,hG,hpairCost,htripleCost⟩ := hprep N (by omega) ν hcap
    (fun w j hj => (hνball w j hj).trans (ENNReal.ofReal_le_ofReal
      (by simpa only [Nat.cast_add,Nat.cast_one] using
        (mul_le_mul_of_nonneg_right hloss
          (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) (h+1:ℝ))))))
    (fun w r hr hr1 => (hslab w r (by simpa only [one_div] using hr) hr1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hloss
        (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
  let ν₀ : Measure (Space (h+2)) := Measure.map gnomonicCoordinates ν
  have hpos : ∀ᵐ (w : Sphere (h+3)) ∂ν, 0 < (w:Space (h+3)) 0 := by
    filter_upwards [hcap] with w hw
    have hh := gnomonic_cap_first_coordinate w (hw.trans (by norm_num : (1/8:ℝ) ≤ 1/2))
    linarith
  have hνeq : Measure.map gnomonicChart ν₀ = ν := gnomonicCoordinates_map_recover ν hpos
  have hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1 := by
    filter_upwards [small_gnomonic_cap_law ν hcap] with p hp
    linarith
  have hpair : ∀ᵐ w : Sphere (h+3) × Sphere (h+3) ∂ν.prod ν,
      0 ≤ inner ℝ (w.1:Space (h+3)) (w.2:Space (h+3)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcap,
      Measure.quasiMeasurePreserving_snd.ae hcap] with w hw hv
    exact sphere_chart_pair_inner_nonnegative w.1 w.2 (gnomonicChart (0 : Space (h+2)))
      (hw.trans (by norm_num)) (hv.trans (by norm_num))
  obtain ⟨B,hB⟩ := exists_transverse_row_frame (h := h) (n := h+2) (by omega)
    (sphere_norm (gnomonicChart (0 : Space (h+2))))
  have hKpow (j : ℕ) : K^j = δ^(-((j:ℝ)*u)) := gaussian_scale_power hδ j
  have hbox : volume (coordinateBox h ((1/4)*Mrow+δ)) ≤ ENNReal.ofReal V := by
    rw [coordinateBox_volume (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (by positivity)
    change 2*((1/4)*Mrow+δ) ≤ 2*(Mrow+1)
    nlinarith
  have hpc : (∫⁻ A, endpointPairCost ν₀ δ G A
      ∂(gaussianRows (h+3) h).restrict
        (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ)))) ≤
      ENNReal.ofReal (δ^c₁) := by
    apply (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    simpa only [endpointPairCost,dyadic_inverse_rpow] using hpairCost
  have htc : (∫⁻ A, endpointTripleCost ν₀ δ (2*δ^a) G A
      ∂(gaussianRows (h+3) h).restrict
        (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ)))) ≤
      ENNReal.ofReal (δ^c₂) := by
    apply (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    simpa only [endpointTripleCost,dyadic_inverse_rpow] using htripleCost
  have hrow := endpoint_selection_row_budget hδ hV _ _ _ hbox hpc htc hbase
  have hactive := endpoint_active_cover_power hδ hδ1 hεu.le hC hρ.le hcount
  have hsmall := endpoint_stable_small hδρ hstable
  have hbad' := endpoint_bad_mass_ennreal hδ hbad
  have hcoef' : K^6*(4*a₀)^s ≤ δ^(-(40*u)) := by
    rw [hKpow]
    simpa only [Nat.cast_ofNat,neg_mul,mul_neg,mul_comm] using hcoef
  have hmass' : δ^(40*u) ≤ (δ^(2*u))^3/(2*(K^6)^5) := by
    rw [hKpow]
    simpa only [Nat.cast_ofNat,neg_mul] using hmass
  obtain ⟨hCP,hCD,hCM⟩ := hcoeff L hL
  have hNc : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Ncover := by
    intro w
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hJN w)
  have hg := controlled_endpoint_angular_gain μ ν ν₀ hνeq B (gnomonicChart (0 : Space (h+2)))
    E J v G hG hρ.le hδρ hB hν hstable hsmall hμ hν₀ hμmass (by simp)
    (by positivity : 0 ≤ L) (by positivity : 0 ≤ L) (by linarith : (h:ℝ) < t)
    hμball hνball hpair hK (Real.rpow_pos_of_pos hδ _) hCP hCD hCM hcard hCK hlarge
    ha.le hC (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos hδ _)
    ha₀ le_rfl hbad' hmass' hactive hcoef' herror
    (by simpa only [neg_mul] using hbudget) hrow hE hJ hNc hEb hanchors hcover
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg.le
  have hlocal := gaussianLocalBandConstant_pos (n := h+2) hρ
  have hr' : B₀*(μ.prod ν).real E ≤ δ^u := by
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2:ℝ)^h),
      ENNReal.toReal_ofReal (pow_nonneg hlocal.le h),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/K),B₀,Measure.real,one_div,
      K,Real.rpow_neg hδ.le,inv_inv,ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le u),mul_assoc] using hr
  have hI : (μ.prod ν).real E ≤ (1/B₀)*δ^u := by
    calc
      _ = (1/B₀)*(B₀*(μ.prod ν).real E) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hr' (by positivity)
  exact hI.trans habs.2.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EndpointNormalize
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalization costs for the endpoint direction law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalizedSliceLaw_power_bound (ν : Measure Y) [IsFiniteMeasure ν]
    (hν : ν univ ≠ 0) {δ σ ε q r : ℝ} (hδ : 0 < δ) (_hr : 0 ≤ r)
    (hmass : ENNReal.ofReal (δ^σ) ≤ ν univ) (S : Set Y)
    (hS : ν S ≤ ENNReal.ofReal (δ^(-ε)*r^q)) :
    (normalizedSliceLaw ν hν : Measure Y) S ≤ ENNReal.ofReal (δ^(-ε-σ)*r^q) := by
  apply (normalizedSliceLaw_bound ν hν S hmass hS).trans_eq
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hδ σ),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.rpow_neg hδ.le]
  calc
    _ = (δ^(-ε)*δ^(-σ))*r^q := by ring
    _ = _ := by rw [← Real.rpow_add hδ]; congr 2

theorem incidence_le_normalized_direction (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [IsFiniteMeasure ν] (hν : ν univ ≠ 0) (hmass : ν univ ≤ 1)
    (E : Set (X × Y)) :
    (μ.prod ν) E ≤ (μ.prod (normalizedSliceLaw ν hν : Measure Y)) E := by
  change (μ.prod ν) E ≤ (μ.prod ((ν univ)⁻¹ • ν)) E
  rw [Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul]
  have hi : 1 ≤ (ν univ)⁻¹ := by
    simpa only [inv_one] using ENNReal.inv_le_inv.mpr hmass
  simpa only [one_mul,mul_one,mul_comm] using mul_le_mul_right hi ((μ.prod ν) E)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointSubprobability
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint small-cap gain for original subprobability direction laws -/

namespace Falconer
open Set MeasureTheory Real
open scoped ENNReal

theorem endpoint_chart_subprobability_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C ρ : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ w ∂ν, dist w (gnomonicChart (0 : Space (h+2))) ≤ ρ) →
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  obtain ⟨ε₀,c₀,hε₀,hc₀,N₀,hgain⟩ := endpoint_chart_angular_gain hLW ht ht' hζ hC hρ hρsmall hstable
  let ε := ε₀/2
  let c := min ε c₀
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hc : 0 < c := lt_min hε hc₀
  have hεle : ε ≤ ε₀ := by dsimp [ε]; linarith
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN ι _ _ μ ν _ _ E J v hν hμ hμmass hνmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ (2:ℝ)^N)
  have hpow {p q : ℝ} (hpq : p ≤ q) : δ^q ≤ δ^p :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hpq
  by_cases hmass : ν univ ≤ ENNReal.ofReal (δ^ε)
  · calc
      (μ.prod ν) E ≤ (μ.prod ν) univ := measure_mono (subset_univ _)
      _ = μ univ*ν univ := by rw [← univ_prod_univ,Measure.prod_prod]
      _ ≤ 1*ENNReal.ofReal (δ^ε) := mul_le_mul' hμmass hmass
      _ ≤ ENNReal.ofReal (δ^c) := by
        rw [one_mul]
        exact ENNReal.ofReal_le_ofReal (hpow (min_le_left _ _))
  · have hmass' : ENNReal.ofReal (δ^ε) ≤ ν univ := (lt_of_not_ge hmass).le
    have hν0 : ν univ ≠ 0 := ne_of_gt ((ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ ε)).trans_le hmass')
    let ν' : Measure (Sphere (h+3)) := normalizedSliceLaw ν hν0
    have hnorm (S : Set (Sphere (h+3))) (r q : ℝ) (hr : 0 ≤ r)
        (hS : ν S ≤ ENNReal.ofReal (δ^(-ε)*r^q)) :
        ν' S ≤ ENNReal.ofReal (δ^(-ε₀)*r^q) := by
      have hh := normalizedSliceLaw_power_bound ν hν0 hδ hr hmass' S hS
      have he : -ε-ε = -ε₀ := by dsimp [ε]; ring
      simpa only [he] using hh
    have hν'ball (w : Sphere (h+3)) (j : ℕ) (hj : j ≤ N) :
        ν' (Metric.ball w (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε₀)*(1/(2:ℝ)^j)^(h+1:ℝ)) :=
      hnorm _ _ _ (by positivity) (hνball w j hj)
    have hslab' (w : Sphere (h+3)) (r : ℝ) (hr : δ ≤ r) (hr1 : r ≤ 1) :
        ν' {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal (δ^(-ε₀)*r^ζ) :=
      hnorm _ r ζ (hδ.le.trans hr) (hslab w r hr hr1)
    have hL : δ^(-ε) ≤ δ^(-ε₀) := hpow (neg_le_neg hεle)
    have hg := hgain N hN ι μ ν' E J v (normalizedSliceLaw_ae ν hν0 hν) hμ hμmass
      (fun x j hj => (hμball x j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL
          (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) t))))
      hν'ball hslab' hE hJ
      (fun w => (hJN w).trans (hpow (by linarith : -(h+1:ℝ)-ε₀ ≤ -(h+1:ℝ)-ε)))
      hEb hanchors hcover
    have hg' : (μ.prod ν') E ≤ ENNReal.ofReal (δ^c₀) := by
      simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top (μ.prod ν') E)] using
        ENNReal.ofReal_le_ofReal hg
    exact (incidence_le_normalized_direction μ ν hν0 hνmass E).trans
      (hg'.trans (ENNReal.ofReal_le_ofReal (hpow (min_le_right _ _))))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedLaws
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotation transport of the original point and direction laws -/

namespace Falconer
open Set Metric MeasureTheory
variable {d : ℕ}

theorem sphereMap_distance (e : Space d ≃ₗᵢ[ℝ] Space d) (v w : Sphere d) :
    dist (sphereMap e v) (sphereMap e w) = dist v w := e.dist_map v w

theorem sphereMap_symm_apply (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e (sphereMap e.symm w) = w := by
  apply Subtype.ext
  exact e.apply_symm_apply w

theorem sphereMap_apply_symm (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) :
    sphereMap e.symm (sphereMap e w) = w := by
  apply Subtype.ext
  exact e.symm_apply_apply w

theorem sphereMap_ball_preimage (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    sphereMap e ⁻¹' ball w r = ball (sphereMap e.symm w) r := by
  rw [← sphereMap_symm_apply e w]
  ext v
  simp only [mem_preimage,mem_ball,sphereMap_distance]
  rw [sphereMap_apply_symm e]

theorem rotated_point_ball (μ : Measure (Space d)) (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x : Space d) (r : ℝ) :
    (Measure.map e μ) (ball x r) = μ (ball (e.symm x) r) := by
  rw [Measure.map_apply e.continuous.measurable measurableSet_ball]
  congr 1
  ext y
  change dist (e y) x < r ↔ dist y (e.symm x) < r
  rw [← e.apply_symm_apply x,e.dist_map,e.symm_apply_apply]

theorem rotated_direction_ball (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    (Measure.map (sphereMap e) ν) (ball w r) = ν (ball (sphereMap e.symm w) r) := by
  rw [Measure.map_apply (continuous_sphereMap e).measurable measurableSet_ball,
    sphereMap_ball_preimage]

theorem rotated_direction_slab (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) (w : Sphere d) (r : ℝ) :
    (Measure.map (sphereMap e) ν) {v : Sphere d | |inner ℝ (w:Space d) (v:Space d)| ≤ r} =
      ν {v : Sphere d | |inner ℝ (sphereMap e.symm w:Space d) (v:Space d)| ≤ r} := by
  have hm : MeasurableSet {v : Sphere d | |inner ℝ (w:Space d) (v:Space d)| ≤ r} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.map_apply (continuous_sphereMap e).measurable hm]
  congr 1
  ext v
  change |inner ℝ (w:Space d) (e (v:Space d))| ≤ r ↔ |inner ℝ (e.symm (w:Space d)) (v:Space d)| ≤ r
  rw [← e.inner_map_map (e.symm (w:Space d)) (v:Space d),e.apply_symm_apply]

theorem rotated_perpendicular_norm (e : Space d ≃ₗᵢ[ℝ] Space d) (w x a : Space d) :
    ‖perpendicularPart (e w) (e x-e a)‖ = ‖perpendicularPart w (x-a)‖ := by
  calc
    _ = ‖e (perpendicularPart w (x-a))‖ := by
      congr 1
      simp only [perpendicularPart,map_sub,map_smul,inner_sub_right,e.inner_map_map]
    _ = _ := e.norm_map _

theorem rotated_incidence (μ : Measure (Space d)) (ν : Measure (Sphere d))
    [SFinite μ] [SFinite ν] (e : Space d ≃ₗᵢ[ℝ] Space d)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E) :
    ((Measure.map e μ).prod (Measure.map (sphereMap e) ν))
      ((Prod.map e.symm (sphereMap e.symm)) ⁻¹' E) = (μ.prod ν) E := by
  have he := e.continuous.measurable
  have hw := (continuous_sphereMap e).measurable
  have hE' := hE.preimage (e.symm.continuous.measurable.prodMap
    (continuous_sphereMap e.symm).measurable)
  rw [Measure.map_prod_map μ ν he hw,Measure.map_apply (he.prodMap hw) hE']
  congr 1
  ext p
  change (e.symm (e p.1),sphereMap e.symm (sphereMap e p.2)) ∈ E ↔ p ∈ E
  rw [e.symm_apply_apply,sphereMap_apply_symm]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RotatedTubeData
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rotation of the original measurable tube relation and its finite labels -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ} {ι : Type*}

theorem rotatedTubeRelation_measurable (e : Space d ≃ₗᵢ[ℝ] Space d)
    {E : Set (Space d × Sphere d)} (hE : MeasurableSet E) :
    MeasurableSet (rotatedTubeRelation e E) :=
  hE.preimage (e.symm.continuous.measurable.prodMap (continuous_sphereMap e.symm).measurable)

theorem rotatedTubeRelation_point_bound (e : Space d ≃ₗᵢ[ℝ] Space d)
    {E : Set (Space d × Sphere d)} {D : ℝ} (hE : ∀ u ∈ E, ‖u.1‖ ≤ D) :
    ∀ u ∈ rotatedTubeRelation e E, ‖u.1‖ ≤ D := by
  intro u hu
  have hh := hE _ hu
  change ‖e.symm u.1‖ ≤ D at hh
  simpa only [e.symm.norm_map] using hh

theorem rotatedTubeRelation_cover [DecidableEq ι]
    (e : Space d ≃ₗᵢ[ℝ] Space d) {E : Set (Space d × Sphere d)}
    (J : Sphere d → Finset ι) (v : ι → Space d) {r : ℝ}
    (hE : ∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-v i)‖ ≤ r) :
    ∀ u ∈ rotatedTubeRelation e E, ∃ i ∈ J (sphereMap e.symm u.2),
      ‖perpendicularPart (u.2:Space d) (u.1-e (v i))‖ ≤ r := by
  intro u hu
  obtain ⟨i,hi,hp⟩ := hE _ hu
  refine ⟨i,hi,?_⟩
  have he := rotated_perpendicular_norm e (e.symm (u.2:Space d)) (e.symm u.1) (v i)
  rw [e.apply_symm_apply,e.apply_symm_apply] at he
  rw [he]
  exact hp

theorem rotated_point_norm_ae (μ : Measure (Space d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) :
    ∀ᵐ x ∂Measure.map e μ, ‖x‖ ≤ D := by
  rw [ae_map_iff e.continuous.measurable.aemeasurable
    (measurableSet_le measurable_norm measurable_const)]
  simpa only [e.norm_map] using hμ

theorem rotated_direction_cap_ae (ν : Measure (Sphere d))
    (e : Space d ≃ₗᵢ[ℝ] Space d) {w₀ : Sphere d} {ρ : ℝ}
    (hν : ∀ᵐ w ∂ν, dist w w₀ ≤ ρ) :
    ∀ᵐ w ∂Measure.map (sphereMap e) ν, dist w (sphereMap e w₀) ≤ ρ := by
  rw [ae_map_iff (continuous_sphereMap e).measurable.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)]
  simpa only [sphereMap_distance] using hν

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointOrientedGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint small-cap estimate in every orientation -/

namespace Falconer
open Set MeasureTheory Real
open scoped ENNReal

theorem endpoint_oriented_chart_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C ρ : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/8)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (w₀ : Sphere (h+3)) (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  obtain ⟨ε,c,hε,hc,N₀,hgain⟩ := endpoint_chart_subprobability_gain hLW ht ht' hζ hC hρ hρsmall hstable
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN ι _ _ μ ν _ _ w₀ E J v hν hμ hμmass hνmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let north : Sphere (h+3) := gnomonicChart (0 : Space (h+2))
  let e : Space (h+3) ≃ₗᵢ[ℝ] Space (h+3) :=
    (ℝ ∙ ((w₀:Space (h+3))-(north:Space (h+3))))ᗮ.reflection
  have he : sphereMap e w₀ = north := by
    apply Subtype.ext
    exact Submodule.reflection_sub ((sphere_norm w₀).trans (sphere_norm north).symm)
  let μ' := Measure.map e μ
  let ν' := Measure.map (sphereMap e) ν
  let E' := rotatedTubeRelation e E
  let J' : Sphere (h+3) → Finset ι := fun w => J (sphereMap e.symm w)
  let v' : ι → Space (h+3) := fun i => e (v i)
  have hν' : ∀ᵐ w ∂ν', dist w north ≤ ρ := by
    rw [← he]
    exact rotated_direction_cap_ae ν e hν
  have hμ'mass : μ' univ ≤ 1 := by
    simpa only [μ',Measure.map_apply e.continuous.measurable MeasurableSet.univ,preimage_univ] using hμmass
  have hν'mass : ν' univ ≤ 1 := by
    simpa only [ν',Measure.map_apply (continuous_sphereMap e).measurable MeasurableSet.univ,preimage_univ] using hνmass
  have hμ'ball (x : Space (h+3)) (j : ℕ) (hj : j ≤ N) :
      μ' (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t) := by
    rw [rotated_point_ball]
    exact hμball _ j hj
  have hν'ball (w : Sphere (h+3)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball w (1/(2:ℝ)^j)) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ)) := by
    rw [rotated_direction_ball]
    exact hνball _ j hj
  have hslab' (w : Sphere (h+3)) (r : ℝ) (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
      ν' {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ) := by
    rw [rotated_direction_slab]
    exact hslab _ r hr hr1
  have hg := hgain N hN ι μ' ν' E' J' v' hν' (rotated_point_norm_ae μ e hμ)
    hμ'mass hν'mass hμ'ball hν'ball hslab' (rotatedTubeRelation_measurable e hE)
    (fun i => (hJ i).preimage (continuous_sphereMap e.symm).measurable)
    (fun w => hJN (sphereMap e.symm w)) (rotatedTubeRelation_point_bound e hEb)
    (fun w i hi => by simpa only [v',e.norm_map] using hanchors (sphereMap e.symm w) i hi)
    (rotatedTubeRelation_cover e J v hcover)
  have hmass : (μ'.prod ν') E' = (μ.prod ν) E := rotated_incidence μ ν e E hE
  rw [hmass] at hg
  exact hg

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Slicing_SmallGaussianChart
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed direction-chart radius for the controlled Gaussian slice geometry -/

namespace Falconer

theorem exists_small_gaussian_chart_radius (h : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/2 ∧
      (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 ∧
      4*(h:ℝ)*ρ+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 := by
  let A : ℝ := 4*(h:ℝ)+1+8*(h:ℝ)*(h+2:ℝ)
  let ρ : ℝ := 1/(8*(A+1))
  have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have he : 8*(A+1)*ρ = 1 := by dsimp [ρ]; field_simp
  have hp : A*ρ ≤ 1/8 := by nlinarith
  have hcoef : (h:ℝ)*((h+2:ℝ)*2) ≤ A := by dsimp [A]; nlinarith
  refine ⟨ρ,hρ,?_,?_,?_⟩
  · nlinarith [mul_nonneg hA hρ.le]
  · have hb := mul_le_mul_of_nonneg_right hcoef hρ.le
    nlinarith
  · calc
      _ = A*ρ := by dsimp [A]; ring
      _ ≤ 1/8 := hp
      _ ≤ 1/4 := by norm_num

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EndpointChartRadius
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed small cap for the three-dimensional endpoint slice -/

namespace Falconer

theorem exists_endpoint_chart_radius (h : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/8 ∧ (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2 := by
  obtain ⟨r,hr,_,hst,_⟩ := exists_small_gaussian_chart_radius (h+1)
  have hcast : ((h+1:ℕ):ℝ)+2 = (h+3:ℝ) := by push_cast; ring
  rw [hcast] at hst
  refine ⟨min r (1/8),lt_min hr (by norm_num),min_le_right _ _,?_⟩
  have hh : (h:ℝ)*((h+3:ℝ)*(2*r)) ≤ ((h+1:ℕ):ℝ)*((h+3:ℝ)*(2*r)) :=
    mul_le_mul_of_nonneg_right (by push_cast; linarith) (by positivity)
  apply le_trans _ (hh.trans hst)
  gcongr
  exact min_le_left _ _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_EndpointAngularGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform endpoint angular gain in every ambient dimension h+3 -/

namespace Falconer
open Set MeasureTheory Real Filter
open scoped ENNReal Topology

theorem endpoint_dyadic_angular_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C : ℝ}
    (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2) (hζ : 0 < ζ)
    (hC : 0 ≤ C) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ (E : Set (Space (h+3) × Sphere (h+3)))
        (J : Sphere (h+3) → Finset ι) (v : ι → Space (h+3)),
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
      (∀ w, ((J w).card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε)) →
      (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4) →
      (∀ u ∈ E, ∃ i ∈ J u.2,
        ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ρ,hρ,hρsmall,hstable⟩ := exists_endpoint_chart_radius h
  obtain ⟨ε,c₁,hε,hc₁,N₁,hgain⟩ := endpoint_oriented_chart_gain hLW ht ht' hζ hC hρ hρsmall hstable
  let H : ℝ := (2/ρ+1)^(h+3)
  let c : ℝ := c₁/2
  have hc : 0 < c := by dsimp [c]; positivity
  have habs := dyadic_inverse_tendsto.eventually
    (eventually_const_mul_rpow_lt (show c < c₁ by dsimp [c]; linarith) H)
  obtain ⟨N₂,habs⟩ := eventually_atTop.mp habs
  refine ⟨ε,c,hε,hc,N₁+N₂,?_⟩
  intro N hN ι _ _ μ ν _ _ E J v hμ hμmass hνmass hμball hνball hslab hE hJ hJN hEb hanchors hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hH : H*δ^c₁ ≤ δ^c := (habs N (by omega)).2.le
  by_contra hn
  have hlarge : ENNReal.ofReal H*ENNReal.ofReal (δ^c₁) < (μ.prod ν) E := by
    apply lt_of_le_of_lt _ (lt_of_not_ge hn)
    rw [← ENNReal.ofReal_mul (by dsimp [H]; positivity)]
    exact ENNReal.ofReal_le_ofReal hH
  obtain ⟨w₀,hw₀⟩ := original_direction_chart_selection μ ν E hE hρ hlarge
  let ν' := ν.restrict (Metric.closedBall w₀ ρ)
  have hνsupport : ∀ᵐ w ∂ν', dist w w₀ ≤ ρ := ae_restrict_mem measurableSet_closedBall
  have hν'mass : ν' univ ≤ 1 := (Measure.restrict_le_self _).trans hνmass
  have hν'ball (w : Sphere (h+3)) (j : ℕ) (hj : j ≤ N) :
      ν' (Metric.ball w (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (δ^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ)) :=
    (Measure.restrict_le_self _).trans (hνball w j hj)
  have hslab' (w : Sphere (h+3)) (r : ℝ) (hr : δ ≤ r) (hr1 : r ≤ 1) :
      ν' {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
        ENNReal.ofReal (δ^(-ε)*r^ζ) :=
    (Measure.restrict_le_self _).trans (hslab w r hr hr1)
  have hg := hgain N (by omega) ι μ ν' w₀ E J v hνsupport hμ hμmass hν'mass
    hμball hν'ball hslab' hE hJ hJN hEb hanchors hcover
  exact (not_lt_of_ge hg) hw₀

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PowerIncidenceMass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Turning a power-small incidence into a power-small direction mass -/

namespace Falconer
open scoped ENNReal

theorem ennreal_mass_of_power_incidence {δ b c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hbc : 2*b ≤ c) (M : ℝ≥0∞)
    (h : ENNReal.ofReal (δ^b)*M ≤ ENNReal.ofReal (δ^c)) : M ≤ ENNReal.ofReal (δ^b) := by
  have h0 : ENNReal.ofReal (δ^b) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ _))
  have hh := mul_le_mul' (le_refl ((ENNReal.ofReal (δ^b))⁻¹)) h
  rw [← mul_assoc,ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top,one_mul] at hh
  apply hh.trans
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hδ _),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.rpow_neg hδ.le,← Real.rpow_add hδ]
  exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteAnchorLabels
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite anchor labels for the measurable original tube lists -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem finiteAnchorLabels_mem (G J : Finset (Space d)) (a : {a // a ∈ G}) :
    a ∈ finiteAnchorLabels G J ↔ a.val ∈ J := by
  classical
  exact Finset.mem_subtype

theorem finiteAnchorLabels_card (G J : Finset (Space d)) (hJG : J ⊆ G) :
    (finiteAnchorLabels G J).card = J.card := by
  classical
  rw [finiteAnchorLabels,Finset.card_subtype]
  congr 1
  exact Finset.filter_eq_self.mpr (fun a ha => hJG ha)

theorem finiteAnchorLabels_measurable (G : Finset (Space d)) (J : Sphere d → Finset (Space d))
    (hJ : ∀ a, MeasurableSet {w | a ∈ J w}) (a : {a // a ∈ G}) :
    MeasurableSet {w | a ∈ finiteAnchorLabels G (J w)} := by
  simpa only [finiteAnchorLabels_mem] using hJ a.val

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_OriginalCoverRestriction
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Null original fiber losses stay null for every retained slice -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X W : Type*} [MeasurableSpace X] [MeasurableSpace W]

theorem product_inter_eq_of_null_original_fibers
    (μ α : Measure X) (β : Measure W) [SFinite α] [SFinite β] (hα : α ≪ μ)
    (E F : Set (X × W)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hzero : ∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0) :
    (α.prod β) (E ∩ F) = (α.prod β) E := by
  have hz : (α.prod β) (E \ F) = 0 := by
    rw [Measure.prod_apply_symm (hE.diff hF)]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ (fun w => hα (hzero w))
  apply measure_congr
  have hnot : ∀ᵐ t ∂α.prod β, t ∉ E \ F := measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [hnot] with t ht
  simp only [mem_sdiff] at ht
  apply propext
  change t ∈ E ∩ F ↔ t ∈ E
  simp only [mem_inter_iff]
  tauto

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PreparedTubeRelation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing a pointwise covered relation without losing original fiber mass -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem prepare_original_tube_relation (μ : Measure (Space d)) [SFinite μ]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {D ε δ : ℝ} (hδ : 0 < δ) (N : ℕ)
    (hbounded : ∀ t ∈ E, ‖t.1‖ ≤ D)
    (hcover : ∀ w : Sphere d, ∃ S : Finset (Space d), S.card ≤ N ∧
      ∀ x, (x,w) ∈ E → ∃ a ∈ S, ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε) :
    ∃ G : Finset (Space d), (∀ a ∈ G, ‖a‖ ≤ D) ∧
      ∃ J : Sphere d → Finset {a // a ∈ G}, ∃ F : Set (Space d × Sphere d),
        MeasurableSet F ∧ F ⊆ E ∧
        (∀ a, MeasurableSet {w | a ∈ J w}) ∧ (∀ w, (J w).card ≤ N) ∧
        (∀ w, μ {x | (x,w) ∈ E ∧ (x,w) ∉ F} = 0) ∧
        ∀ t ∈ F, ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a.val)‖ ≤ 2*ε+δ := by
  classical
  obtain ⟨G,hGb,J,hJ,hJG,hzero⟩ := original_tube_cover_choice μ E hE hδ N hbounded hcover
  let C : Set (Space d × Sphere d) :=
    {t | ∃ a ∈ J t.2, ‖perpendicularPart (t.2:Space d) (t.1-a)‖ ≤ 2*ε+δ}
  have hC : MeasurableSet C := finite_tube_cover_relation_measurable G J hJ
    (fun w => (hJG w).1) _
  refine ⟨G,hGb,(fun w => finiteAnchorLabels G (J w)),E ∩ C,hE.inter hC,inter_subset_left,
    finiteAnchorLabels_measurable G J hJ,?_,?_,?_⟩
  · intro w
    rw [finiteAnchorLabels_card G (J w) (hJG w).1]
    exact (hJG w).2
  · intro w
    have he : {x | (x,w) ∈ E ∧ (x,w) ∉ E ∩ C} =
        {x | (x,w) ∈ E ∧ ∀ a ∈ J w, ¬‖perpendicularPart (w:Space d) (x-a)‖ ≤ 2*ε+δ} := by
      ext x
      constructor
      · rintro ⟨hx,hn⟩
        refine ⟨hx,fun a ha hp => hn ⟨hx,?_⟩⟩
        exact ⟨a,ha,hp⟩
      · rintro ⟨hx,hn⟩
        refine ⟨hx,fun ht => ?_⟩
        obtain ⟨a,ha,hp⟩ := ht.2
        exact hn a ha hp
    rw [he]
    exact hzero w
  · intro t ht
    obtain ⟨a,ha,hp⟩ := ht.2
    refine ⟨⟨a,(hJG t.2).1 ha⟩,?_,hp⟩
    exact (finiteAnchorLabels_mem G (J t.2) _).mpr ha

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_EndpointTubeGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint decay for arbitrary original finite fiber covers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem endpoint_dyadic_tube_gain (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) (hC : 0 ≤ C) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
        [IsFiniteMeasure μ] [IsFiniteMeasure ν],
      ∀ E : Set (Space (h+3) × Sphere (h+3)),
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
      (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
        ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
          ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
      MeasurableSet E → (∀ u ∈ E, ‖u.1‖ ≤ 1/4) →
      (∀ w : Sphere (h+3), ∃ S : Finset (Space (h+3)),
        (S.card : ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-ε) ∧
        ∀ x, (x,w) ∈ E → ∃ a ∈ S,
          ‖perpendicularPart (w:Space (h+3)) (x-a)‖ ≤ C*(1/(2:ℝ)^N)) →
      (μ.prod ν) E ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^c) := by
  classical
  obtain ⟨ε,c,hε,hc,N₀,hgain⟩ := endpoint_dyadic_angular_gain hLW ht ht' hζ
    (by linarith : 0 ≤ 2*C+1)
  refine ⟨ε,c,hε,hc,N₀,?_⟩
  intro N hN μ ν _ _ E hμ hμmass hνmass hμball hνball hslab hE hEb hcover
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨G,hG,J,F,hF,hFE,hJ,hcard,hzero,hcoverF⟩ :=
    prepare_original_tube_relation μ E hE hδ (Nat.floor (δ^(-(h+1:ℝ)-ε))) hEb (by
      intro w
      obtain ⟨S,hS,hcoverS⟩ := hcover w
      exact ⟨S,Nat.le_floor hS,hcoverS⟩)
  have hmass : (μ.prod ν) F = (μ.prod ν) E := by
    have hh := product_inter_eq_of_null_original_fibers μ μ ν Measure.AbsolutelyContinuous.rfl
      E F hE hF hzero
    simpa only [inter_eq_right.mpr hFE] using hh
  rw [← hmass]
  refine hgain N hN {a // a ∈ G} μ ν F J (fun a => a.val)
    hμ hμmass hνmass hμball hνball hslab hF hJ ?_
    (fun u hu => hEb u (hFE hu)) (fun _ i _ => hG i.val i.property) ?_
  · intro w
    have hh : ((J w).card : ℝ) ≤ (Nat.floor (δ^(-(h+1:ℝ)-ε)) : ℝ) := by exact_mod_cast hcard w
    exact hh.trans (Nat.floor_le (Real.rpow_nonneg hδ.le _))
  · intro u hu
    obtain ⟨a,ha,hp⟩ := hcoverF u hu
    refine ⟨a,ha,?_⟩
    nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_EndpointBadDirections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A universal Borel bad-direction envelope in the endpoint regime -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem endpoint_bad_direction_envelope (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ : Measure (Space (h+3))) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      ∃ B : Set (Sphere (h+3)), MeasurableSet B ∧
        {w : Sphere (h+3) | ∃ S : Finset (Space (h+3)), (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {x | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+3)) (x-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        ∀ (ν : Measure (Sphere (h+3))) [IsFiniteMeasure ν], ν univ ≤ 1 →
          (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N → ν (Metric.ball w (1/(2:ℝ)^j)) ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) →
          (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
            ν {u : Sphere (h+3) | |inner ℝ (w:Space (h+3)) (u:Space (h+3))| ≤ r} ≤
              ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ)) →
          ν B ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  classical
  obtain ⟨ε₀,c,hε₀,hc,N₀,hgain⟩ := endpoint_dyadic_tube_gain hLW ht ht' hζ
    (by linarith : 0 ≤ 2*C+1)
  let ε : ℝ := ε₀/2
  let b : ℝ := min ε (c/3)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hb : 0 < b := lt_min hε (by positivity)
  have hεle : ε ≤ ε₀ := by dsimp [ε]; linarith
  have hble : b ≤ ε₀ := (min_le_left _ _).trans hεle
  have hbc : 2*b ≤ c := by have hh := min_le_right ε (c/3); dsimp [b]; linarith
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ _ hμ hμball
  let δ : ℝ := 1/(2:ℝ)^N
  let count : ℕ := Nat.floor (δ^(-(h+1:ℝ)-b))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1)
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) : (1:ℝ) ≤ (2:ℝ)^N)
  have hL : δ^(-ε) ≤ δ^(-ε₀) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hεle)
  obtain ⟨G,hG,hnet⟩ := exists_bounded_anchor_net (d := h+3) (1/4) hδ
  let B := finiteBadDirections μ G count (1/4) ((2*C+1)*δ) (ENNReal.ofReal (δ^b))
  refine ⟨B,finiteBadDirections_measurable μ G count _ _ _,?_,?_⟩
  · rintro w ⟨S,hS,hmass⟩
    have hh := original_bad_direction_mem_envelope μ G count (ENNReal.ofReal (δ^b))
      hμ hnet w S (Nat.le_floor hS) hmass
    have he : 2*(C*δ)+δ = (2*C+1)*δ := by ring
    change w ∈ finiteBadDirections μ G count (1/4) (2*(C*δ)+δ) (ENNReal.ofReal (δ^b)) at hh
    rw [he] at hh
    exact hh
  · intro ν _ hνmass hνball hslab
    obtain ⟨J,F,hF,hJ,hJmeas,hFb,hcover,hlower⟩ :=
      exists_finite_bad_incidence μ G count (1/4) ((2*C+1)*δ) (ENNReal.ofReal (δ^b))
    have hcount : (count:ℝ) ≤ δ^(-(h+1:ℝ)-ε₀) :=
      (Nat.floor_le (Real.rpow_nonneg hδ.le _)).trans
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
    have hupper := hgain N hN μ ν F hμ (by simp) hνmass
      (fun x j hj => (hμball x j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) t))))
      (fun w j hj => (hνball w j hj).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (show 0 ≤ 1/(2:ℝ)^j by positivity) (h+1:ℝ)))))
      (fun w r hr hr1 => (hslab w r hr hr1).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (hδ.le.trans hr) ζ)))) hF hFb (by
          intro w
          refine ⟨J w,?_,?_⟩
          · exact (show ((J w).card:ℝ) ≤ count by exact_mod_cast (hJ w).2).trans hcount
          · intro x hx
            exact hcover (x,w) hx)
    exact ennreal_mass_of_power_incidence hδ hδ1 hbc (ν B) ((hlower ν).trans hupper)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ReverseRadialGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reverse radial caps bound collisions of original source directions -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

theorem perpendicularPart_neg_left (u v : Space n) :
    perpendicularPart (-u) v = perpendicularPart u v := by
  simp [perpendicularPart,neg_smul]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_TubeDirectionRobustness
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Robust tube covers under small unoriented changes of direction -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem tube_direction_point_bound {w v z : Space d} {η L r : ℝ}
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1) (hdir : ‖w-v‖ ≤ η)
    (hz : ‖z‖ ≤ L) (htube : ‖perpendicularPart w z‖ ≤ r) :
    ‖perpendicularPart v z‖ ≤ r+2*η*L := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hdir
  have he := perpendicularPart_direction_error hv hw z
  have htri := norm_sub_le_norm_sub_add_norm_sub (perpendicularPart v z) (perpendicularPart w z) 0
  simp only [sub_zero] at htri
  have hdir' : ‖v-w‖ ≤ η := by simpa only [norm_sub_rev] using hdir
  calc
    _ ≤ ‖perpendicularPart v z-perpendicularPart w z‖+‖perpendicularPart w z‖ := htri
    _ ≤ 2*‖v-w‖*‖z‖+r := add_le_add he htube
    _ ≤ 2*η*L+r := by gcongr
    _ = _ := by ring

theorem unoriented_tube_direction_point_bound {w v z : Space d} {η L r : ℝ}
    (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hdir : ‖w-v‖ ≤ η ∨ ‖w+v‖ ≤ η)
    (hz : ‖z‖ ≤ L) (htube : ‖perpendicularPart w z‖ ≤ r) :
    ‖perpendicularPart v z‖ ≤ r+2*η*L := by
  rcases hdir with hdir | hdir
  · exact tube_direction_point_bound hw hv hdir hz htube
  · have hh := tube_direction_point_bound hw (show ‖-v‖ = 1 by simpa using hv)
      (show ‖w-(-v)‖ ≤ η by simpa only [sub_neg_eq_add] using hdir) hz htube
    simpa only [perpendicularPart_neg_left] using hh

theorem tube_cover_direction_transport (μ : Measure (Space d))
    {w v : Space d} {D B η r : ℝ} (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hdir : ‖w-v‖ ≤ η ∨ ‖w+v‖ ≤ η)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (S : Finset (Space d)) (hS : ∀ a ∈ S, ‖a‖ ≤ B) :
    μ {x | ∃ a ∈ S, ‖perpendicularPart w (x-a)‖ ≤ r} ≤
      μ {x | ∃ a ∈ S, ‖perpendicularPart v (x-a)‖ ≤ r+2*η*(D+B)} := by
  apply measure_mono_ae
  filter_upwards [hμ] with x hx
  rintro ⟨a,ha,htube⟩
  refine ⟨a,ha,unoriented_tube_direction_point_bound hw hv hdir ?_ htube⟩
  exact (norm_sub_le x a).trans (add_le_add hx (hS a ha))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GoodDirectionMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One good witness direction rules out mass in a nearby heavy tube cover -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem mass_lt_of_good_direction_cover (μ : Measure (Space d))
    (Bad : Set (Sphere d)) (v : Sphere d) (hv : v ∉ Bad)
    (w : Space d) (hw : ‖w‖ = 1) {D B η r R : ℝ}
    (hdir : ‖w-(v:Space d)‖ ≤ η ∨ ‖w+(v:Space d)‖ ≤ η)
    (hwidth : r+2*η*(D+B) ≤ R) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (J : Finset (Space d)) (hJ : ∀ a ∈ J, ‖a‖ ≤ B) (N : ℕ) (hcard : J.card ≤ N)
    (a : ℝ≥0∞)
    (henvelope : ∀ S : Finset (Space d), S.card ≤ N →
      a ≤ μ {x | ∃ b ∈ S, ‖perpendicularPart (v:Space d) (x-b)‖ ≤ R} → v ∈ Bad)
    (T : Set (Space d))
    (hcover : ∀ x ∈ T, ∃ b ∈ J, ‖perpendicularPart w (x-b)‖ ≤ r) : μ T < a := by
  by_contra hn
  have hlarge : a ≤ μ T := le_of_not_gt hn
  apply hv
  apply henvelope J hcard
  apply hlarge.trans
  apply (measure_mono hcover).trans
  apply (tube_cover_direction_transport μ hw (sphere_norm v) hdir hμ J hJ).trans
  apply measure_mono
  rintro x ⟨b,hb,hxb⟩
  exact ⟨b,hb,hxb.trans hwidth⟩

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
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialSphereLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sphere-valued original radial laws, with a harmless diagonal value -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem originalRadialSphereLaw_apply (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (B : Set (Sphere d)) (hB : MeasurableSet B) :
    originalRadialSphereLaw w₀ ν G z B =
      ν {x | (z,x) ∈ G ∧ normalizeToSphere w₀ (x-z) ∈ B} := by
  have hm : Measurable (fun x : Space d => normalizeToSphere w₀ (x-z)) :=
    (normalizeToSphere_measurable w₀).comp (measurable_id.sub measurable_const)
  rw [originalRadialSphereLaw,Measure.map_apply hm hB,Measure.restrict_apply (hB.preimage hm)]
  congr 1
  ext x
  exact and_comm

theorem originalRadialSphereLaw_mass_le (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) :
    originalRadialSphereLaw w₀ ν G z Set.univ ≤ ν Set.univ := by
  rw [originalRadialSphereLaw_apply w₀ ν G z Set.univ MeasurableSet.univ]
  exact measure_mono (subset_univ _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_WitnessDirection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unoriented closeness of a witness direction to the source-cell center -/

namespace Falconer
open NormedSpace
variable {d : ℕ}

theorem cell_center_witness_direction (w₀ : Sphere d) (x c z : Space d)
    {r D : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hzx : z ≠ x)
    (hzc : ‖z-c‖ ≤ D) :
    ‖normalize (c-x)+(normalizeToSphere w₀ (x-z):Space d)‖ ≤ 2*D/r := by
  rw [normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hzx.symm)]
  have hn : normalize (x-z) = -normalize (z-x) := by
    rw [show x-z = -(z-x) by abel,normalize_neg]
  rw [hn,← sub_eq_add_neg]
  apply (le_div_iff₀ hr).mpr
  have hh := normalize_distance_scaled hcx (sub_ne_zero.mpr hzx)
  rw [dist_eq_norm,dist_eq_norm,sub_sub_sub_cancel_right,norm_sub_rev c z] at hh
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialBadWitness
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deleting original pairs whose witness direction is exceptional -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialBadWitness_measurable (w₀ : Sphere d) {G : Set (Space d × Space d)}
    (hG : MeasurableSet G) {B : Set (Sphere d)} (hB : MeasurableSet B) :
    MeasurableSet (radialBadWitness w₀ G B) :=
  hG.inter (hB.preimage ((normalizeToSphere_measurable w₀).comp
    (measurable_snd.sub measurable_fst)))

theorem radial_bad_witness_mass (w₀ : Sphere d) (μ ν : Measure (Space d))
    [SFinite μ] [SFinite ν] (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (B : Set (Sphere d)) (hB : MeasurableSet B) (c : ℝ≥0∞)
    (hsmall : ∀ᵐ z ∂μ, originalRadialSphereLaw w₀ ν G z B ≤ c) :
    (μ.prod ν) (radialBadWitness w₀ G B) ≤ c*μ univ := by
  rw [Measure.prod_apply (radialBadWitness_measurable w₀ hG hB)]
  have he (z : Space d) : ν {x | (z,x) ∈ radialBadWitness w₀ G B} =
      originalRadialSphereLaw w₀ ν G z B := by
    rw [originalRadialSphereLaw_apply w₀ ν G z B hB]
    rfl
  change (∫⁻ z, ν {x | (z,x) ∈ radialBadWitness w₀ G B} ∂μ) ≤ c*μ univ
  simp_rw [he]
  exact (lintegral_mono_ae hsmall).trans_eq (lintegral_const c)

theorem direction_good_of_not_radialBadWitness (w₀ : Sphere d)
    (G : Set (Space d × Space d)) (B : Set (Sphere d)) {z x : Space d}
    (hgood : (z,x) ∈ G \ radialBadWitness w₀ G B) :
    normalizeToSphere w₀ (x-z) ∉ B := by
  intro hb
  exact hgood.2 ⟨hgood.1,hb⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialSphereBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sphere law has exactly the original directional cap and plate bounds -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

theorem originalRadialSphereLaw_ball (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (hdiag : ∀ x, (z,x) ∈ G → x ≠ z)
    (w : Sphere d) (r : ℝ) :
    originalRadialSphereLaw w₀ ν G z (Metric.ball w r) =
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space d) < r} := by
  rw [originalRadialSphereLaw_apply w₀ ν G z (Metric.ball w r) measurableSet_ball]
  congr 1
  ext x
  by_cases hx : (z,x) ∈ G
  · simp only [mem_ofPred_eq,hx,true_and,Metric.mem_ball,Subtype.dist_eq,
      normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr (hdiag x hx))]
  · simp only [mem_ofPred_eq,hx,false_and]

theorem originalRadialSphereLaw_slab (w₀ : Sphere d) (ν : Measure (Space d))
    (G : Set (Space d × Space d)) (z : Space d) (hdiag : ∀ x, (z,x) ∈ G → x ≠ z)
    (w : Space d) (r : ℝ) :
    originalRadialSphereLaw w₀ ν G z {u : Sphere d | |inner ℝ w (u:Space d)| ≤ r} =
      ν {x | (z,x) ∈ G ∧ |inner ℝ w (normalize (x-z))| ≤ r} := by
  rw [originalRadialSphereLaw_apply w₀ ν G z _
    (measurableSet_le (by fun_prop) measurable_const)]
  congr 1
  ext x
  by_cases hx : (z,x) ∈ G
  · simp only [hx,true_and,mem_ofPred_eq,
      normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr (hdiag x hx))]
  · simp only [mem_ofPred_eq,hx,false_and]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_EndpointRadialBadDirections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The endpoint envelope deletes only power-small original witness pairs -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem endpoint_radial_bad_directions (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ C : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) (hC : 0 ≤ C) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+3)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (w₀ : Sphere (h+3)) (G : Set (Space (h+3) × Space (h+3))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → x ≠ z) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ,
        (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+3)) < 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) ∧
        (∀ w : Sphere (h+3), ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ν {x | (z,x) ∈ G ∧ |inner ℝ (w:Space (h+3)) (normalize (x-z))| ≤ r} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*r^ζ))) →
      ∃ B : Set (Sphere (h+3)), MeasurableSet B ∧
        {w : Sphere (h+3) | ∃ S : Finset (Space (h+3)),
          (S.card:ℝ) ≤ (1/(2:ℝ)^N)^(-(h+1:ℝ)-b) ∧
          ENNReal.ofReal ((1/(2:ℝ)^N)^b) ≤
            μ {z | ∃ v ∈ S, ‖perpendicularPart (w:Space (h+3)) (z-v)‖ ≤ C*(1/(2:ℝ)^N)}} ⊆ B ∧
        (μ.prod ν) (radialBadWitness w₀ G B) ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := endpoint_bad_direction_envelope hLW ht ht' hζ hC
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hdiag hμ hμball hdata
  obtain ⟨B,hB,hcontains,hbound⟩ := hN₀ N hN μ hμ hμball
  refine ⟨B,hB,hcontains,?_⟩
  have hsmall : ∀ᵐ z ∂μ, originalRadialSphereLaw w₀ ν G z B ≤
      ENNReal.ofReal ((1/(2:ℝ)^N)^b) := by
    filter_upwards [hdata] with z hz
    apply hbound (originalRadialSphereLaw w₀ ν G z)
      ((originalRadialSphereLaw_mass_le w₀ ν G z).trans hν)
    · intro w j hj
      rw [originalRadialSphereLaw_ball w₀ ν G z (hdiag z)]
      exact hz.1 w j hj
    · intro w r hr hr1
      rw [originalRadialSphereLaw_slab w₀ ν G z (hdiag z)]
      exact hz.2 w r hr hr1
  simpa only [measure_univ,mul_one] using radial_bad_witness_mass w₀ μ ν G hG B hB _ hsmall

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyCoverCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the fixed heavy-cover constant into the angular power margin -/

namespace Falconer
open Filter
open scoped ENNReal Topology

theorem heavy_cover_card_le {m : ℕ} {F K T : ℝ} (hF : 0 < F) (hK : 0 ≤ K)
    (h : (m:ℝ≥0∞)*ENNReal.ofReal F ≤ ENNReal.ofReal K) (hbudget : K ≤ T*F) :
    (m:ℝ) ≤ T := by
  have hm : ENNReal.ofReal ((m:ℝ)*F) ≤ ENNReal.ofReal K := by
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg m),ENNReal.ofReal_natCast] using h
  have hm' := (ENNReal.ofReal_le_ofReal_iff hK).mp hm
  nlinarith

theorem eventually_heavy_cover_card {q b K : ℝ} (hb : 0 < b) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ m : ℕ,
      (m:ℝ≥0∞)*ENNReal.ofReal ((1/(2:ℝ)^N)^(q+b/2)) ≤ ENNReal.ofReal K →
      (m:ℝ) ≤ (1/(2:ℝ)^N)^(-q-b) := by
  have he := eventually_const_mul_rpow_lt (show -b/2 < (0:ℝ) by linarith) K
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (dyadic_inverse_tendsto.eventually he)
  refine ⟨N₀,fun N hN m hm => ?_⟩
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  apply heavy_cover_card_le (Real.rpow_pos_of_pos hδ _) hK hm
  have hbound : K ≤ (1/(2:ℝ)^N)^(-b/2) := by
    have hh := (hN₀ N hN).2
    simpa only [Real.rpow_zero,mul_one] using hh.le
  apply hbound.trans_eq
  rw [← Real.rpow_add hδ]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialCollisionMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Measurable radial collision masses and the original-pin Fubini identity -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialCollisionRelation_measurable (δ : ℝ) :
    MeasurableSet {p : (Space d × Space d) × Space d |
      dist (normalize (p.2-p.1.2)) (normalize (p.1.1-p.1.2)) ≤ δ} := by
  exact measurableSet_le
    ((measurable_normalized_vector (measurable_snd.sub measurable_fst.snd)).dist
      (measurable_normalized_vector (measurable_fst.fst.sub measurable_fst.snd)))
    measurable_const

theorem radialCollisionMass_measurable (μ : Measure (Space d)) [SFinite μ] (δ : ℝ) :
    Measurable (radialCollisionMass μ δ) :=
  measurable_measure_prodMk_left (radialCollisionRelation_measurable δ)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_RepresentedPruning
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Threshold deletion using one witness only on represented pin fibers -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem represented_threshold_pruning (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (G : Set (X × Y)) (hG : MeasurableSet G)
    (K : X × Y → ℝ≥0∞) (hK : Measurable K) (F a : ℝ≥0∞)
    (hsmall : ∀ y, (∃ x, (x,y) ∈ G) → μ {x | (x,y) ∈ G ∧ F < K (x,y)} ≤ a) :
    ∃ H : Set (X × Y), MeasurableSet H ∧ H ⊆ G ∧
      (μ.prod ν) (G \ H) ≤ a*ν univ ∧ ∀ p ∈ H, K p ≤ F := by
  let H := G ∩ {p | K p ≤ F}
  have hH : MeasurableSet H := hG.inter (measurableSet_le hK measurable_const)
  refine ⟨H,hH,inter_subset_left,?_,fun p hp => hp.2⟩
  rw [Measure.prod_apply_symm (hG.diff hH)]
  apply (lintegral_mono _).trans_eq (lintegral_const a)
  intro y
  change μ {x | (x,y) ∈ G \ H} ≤ a
  by_cases hy : ∃ x, (x,y) ∈ G
  · apply (measure_mono _).trans (hsmall y hy)
    rintro x ⟨hx,hnot⟩
    exact ⟨hx,lt_of_not_ge (fun hk => hnot (show (x,y) ∈ H from ⟨hx,hk⟩))⟩
  · have he : {x | (x,y) ∈ G \ H} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun x hx => hy ⟨x,hx.1⟩
    rw [he,measure_empty]
    exact zero_le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BoundedFrozenHeavyCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Heavy radial fibers have bounded-anchor frozen tube covers -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem bounded_frozen_heavy_tube_cover (μ : Measure (Space (n+1))) (x c : Space (n+1))
    {r D δ C B : ℝ} (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (F : ℝ≥0∞)
    (hheavy : ∀ z ∈ T, F ≤ μ {y |
      ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ C*δ})
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) :
    ∃ J : Finset (Space (n+1)),
      (∀ a ∈ J, ‖a‖ ≤ B) ∧
      (∀ z ∈ T, ∃ a ∈ J, ‖perpendicularPart (normalize (c-x)) (z-a)‖ ≤
        (2*((n+1:ℕ):ℝ)+1)*δ) ∧
      (J.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ := by
  obtain ⟨P,hP,hcard⟩ := frozen_heavy_tube_cover μ x c hr hcx hδ hfreeze hsource T hT F hheavy L hL
  obtain ⟨K,hKb,hKn⟩ := exists_bounded_anchor_net (d := n+1) B hδ
  let w : Sphere (n+1) := ⟨normalize (c-x),by
    rw [Metric.mem_sphere,dist_zero_right]
    exact norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))⟩
  obtain ⟨J,hJK,hJP,hJ⟩ := rounded_tube_cover w T P K
    (fun z hz => hKn z (hT z hz).2.2) hP
  refine ⟨J,fun a ha => hKb a (hJK ha),?_,?_⟩
  · intro z hz
    obtain ⟨a,ha,hza⟩ := hJ z hz
    refine ⟨a,ha,?_⟩
    change ‖perpendicularPart (normalize (c-x)) (z-a)‖ ≤ _ at hza
    convert hza using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hc : (J.card:ℝ≥0∞) ≤ P.card := by exact_mod_cast hJP
    exact (mul_le_mul' hc le_rfl).trans hcard

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MiddleHeavyRadialMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A good witness controls the full conditional heavy radial fiber -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem radial_collision_le_tube_mass (μ : Measure (Space (n+1)))
    (x z : Space (n+1)) (hz : z ≠ x) {H δ W : ℝ}
    (hsource : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) (hwidth : H*δ ≤ W) :
    radialCollisionMass μ δ (z,x) ≤
      μ {y | ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W} := by
  apply measure_mono_ae
  filter_upwards [hsource] with y hy
  intro hclose
  have hv : ‖normalize (z-x)‖ = 1 := norm_normalize (sub_ne_zero.mpr hz)
  have hperp : ‖perpendicularPart (normalize (z-x)) (normalize (y-x))‖ ≤ δ := by
    have hh := norm_perpendicularPart_le hv (normalize (y-x)-normalize (z-x))
    rw [perpendicularPart_sub] at hh
    have he : perpendicularPart (normalize (z-x)) (normalize (z-x)) = 0 := by
      simp [perpendicularPart,hv]
    rw [he,sub_zero] at hh
    exact hh.trans hclose
  have he : perpendicularPart (normalize (z-x)) (y-x) =
      ‖y-x‖ • perpendicularPart (normalize (z-x)) (normalize (y-x)) := by
    rw [← perpendicularPart_smul,norm_smul_normalize]
  show ‖perpendicularPart (normalize (z-x)) (y-x)‖ ≤ W
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact (mul_le_mul hy hperp (norm_nonneg _) ((norm_nonneg _).trans hy)).trans hwidth

theorem middle_heavy_radial_mass_lt (μ : Measure (Space (n+1)))
    (x c : Space (n+1)) {r D δ θ C B H η R : ℝ}
    (hr : 0 < r) (hcx : r ≤ ‖c-x‖) (hδ : 0 < δ)
    (hfreeze : 8*D^2/r ≤ δ) (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D)
    (hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ B) (hpin : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H)
    (hwidth : H*θ ≤ C*δ)
    (Bad : Set (Sphere (n+1))) (v : Sphere (n+1)) (hv : v ∉ Bad)
    (hdir : ‖normalize (c-x)-(v:Space (n+1))‖ ≤ η ∨
      ‖normalize (c-x)+(v:Space (n+1))‖ ≤ η)
    (hrobust : (2*((n+1:ℕ):ℝ)+1)*δ+2*η*(B+B) ≤ R)
    (F a : ℝ≥0∞) (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (henvelope : ∀ S : Finset (Space (n+1)),
      (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ →
      a ≤ μ {z | ∃ b ∈ S, ‖perpendicularPart (v:Space (n+1)) (z-b)‖ ≤ R} → v ∈ Bad)
    (T : Set (Space (n+1)))
    (hT : ∀ z ∈ T, z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B ∧
      F < radialCollisionMass μ θ (z,x)) : μ T < a := by
  obtain ⟨J,hJ,hcover,hcard⟩ := bounded_frozen_heavy_tube_cover μ x c hr hcx hδ
    hfreeze hsource T (fun z hz => ⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1⟩)
    F (fun z hz => (hT z hz).2.2.2.le.trans
      (radial_collision_le_tube_mass μ x z (hT z hz).1 hpin hwidth)) L hL
  exact mass_lt_of_good_direction_cover μ Bad v hv _
    (norm_normalize (norm_pos_iff.mp (hr.trans_le hcx))) hdir hrobust hbounded J hJ
    J.card le_rfl a (fun S hS => henvelope S
      ((mul_le_mul' (by exact_mod_cast hS) le_rfl).trans hcard)) T hcover

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MiddleRadialPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-product middle-interval pruning with no choice of pin witnesses -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {n : ℕ}

theorem middle_radial_pruning (μ ν : Measure (Space (n+1)))
    [SFinite μ] [SFinite ν] (w₀ : Sphere (n+1))
    (G : Set (Space (n+1) × Space (n+1))) (hG : MeasurableSet G)
    (Bad : Set (Sphere (n+1))) (hBad : MeasurableSet Bad)
    (c : Space (n+1)) {r D δ θ C B H R : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hfreeze : 8*D^2/r ≤ δ)
    (hsource : ∀ᵐ y ∂μ, ‖y-c‖ ≤ D) (hbounded : ∀ᵐ y ∂μ, ‖y‖ ≤ B)
    (hgeom : ∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ D ∧ ‖z‖ ≤ B)
    (hpin : ∀ x, (∃ z, (z,x) ∈ G) →
      r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H)
    (hwidth : H*θ ≤ C*δ)
    (hrobust : (2*((n+1:ℕ):ℝ)+1)*δ+2*(2*D/r)*(B+B) ≤ R)
    (F a e : ℝ≥0∞) (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ))
    (henvelope : ∀ v : Sphere (n+1), ∀ S : Finset (Space (n+1)),
      (S.card:ℝ≥0∞)*F ≤ ((2*L+1)^(n+1):ℕ)*μ univ →
      a ≤ μ {z | ∃ b ∈ S, ‖perpendicularPart (v:Space (n+1)) (z-b)‖ ≤ R} → v ∈ Bad)
    (hbadmass : (μ.prod ν) (radialBadWitness w₀ G Bad) ≤ e) :
    ∃ G' : Set (Space (n+1) × Space (n+1)), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ e+a*ν univ ∧
      ∀ p ∈ G', radialCollisionMass μ θ p ≤ F := by
  let G₁ := G \ radialBadWitness w₀ G Bad
  have hG₁ : MeasurableSet G₁ := hG.diff (radialBadWitness_measurable w₀ hG hBad)
  have hsub : G₁ ⊆ G := sdiff_subset
  have hsmall (x : Space (n+1)) (hx : ∃ z, (z,x) ∈ G₁) :
      μ {z | (z,x) ∈ G₁ ∧ F < radialCollisionMass μ θ (z,x)} ≤ a := by
    obtain ⟨z,hz⟩ := hx
    have hzx := hgeom z x (hsub hz)
    have hpx := hpin x ⟨z,hsub hz⟩
    let v := normalizeToSphere w₀ (x-z)
    have hv : v ∉ Bad := direction_good_of_not_radialBadWitness w₀ G Bad hz
    apply le_of_lt
    apply middle_heavy_radial_mass_lt μ x c hr hpx.1 hδ hfreeze hsource hbounded
      hpx.2 hwidth Bad v hv (Or.inr (cell_center_witness_direction w₀ x c z hr
        hpx.1 hzx.1 hzx.2.1)) hrobust F a L hL (henvelope v)
    intro y hy
    have hh := hgeom y x (hsub hy.1)
    exact ⟨hh.1,hh.2.1,hh.2.2,hy.2⟩
  obtain ⟨G',hG',hG'sub,hdeleted,hbound⟩ := represented_threshold_pruning μ ν G₁ hG₁
    (radialCollisionMass μ θ) (radialCollisionMass_measurable μ θ) F a hsmall
  refine ⟨G',hG',hG'sub.trans hsub,?_,hbound⟩
  have hcover : G \ G' ⊆ radialBadWitness w₀ G Bad ∪ (G₁ \ G') := by
    intro p hp
    by_cases hb : p ∈ radialBadWitness w₀ G Bad
    · exact Or.inl hb
    · exact Or.inr ⟨⟨hp.1,hb⟩,hp.2⟩
  exact (measure_mono hcover).trans ((measure_union_le _ _).trans (add_le_add hbadmass hdeleted))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_EndpointMiddleRadial
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative middle-interval improvement from finite Loomis–Whitney -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem endpoint_middle_radial_pruning (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+3)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+3)) (G : Set (Space (h+3) × Space (h+3))), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z‖ ≤ 1/4) →
      (∀ᵐ z ∂μ, ‖z‖ ≤ 1/4) →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ,
        (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+3)) < 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) ∧
        (∀ w : Sphere (h+3), ∀ u : ℝ, 1/(2:ℝ)^N ≤ u → u ≤ 1 →
          ν {x | (z,x) ∈ G ∧ |inner ℝ (w:Space (h+3)) (normalize (x-z))| ≤ u} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*u^ζ))) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/r ≤ 1/(2:ℝ)^N →
      H*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖(0:Space (h+3))-x‖ ∧
        ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+3) × Space (h+3)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^((h+1:ℝ)+b/2)) := by
  let C : ℝ := 2*((h+3:ℕ):ℝ)+2
  let L : ℕ := h+6
  let K : ℕ := (2*L+1)^(h+3)
  obtain ⟨ε,b,hε,hb,N₁,hN₁⟩ := endpoint_radial_bad_directions hLW ht ht' hζ
    (show 0 ≤ C by dsimp [C]; positivity)
  obtain ⟨N₂,hN₂⟩ := eventually_heavy_cover_card (q := (h+1:ℝ)) (K := (K:ℝ)) hb (by positivity)
  refine ⟨ε,b,hε,hb,max N₁ N₂,?_⟩
  intro N hN μ ν _ _ hν w₀ G hG hgeom hμ hballs hcaps r H θ hr hfreeze hwidth hpin
  let δ : ℝ := 1/(2:ℝ)^N
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Bad,hBad,hcontains,hbadmass⟩ := hN₁ N ((le_max_left _ _).trans hN) μ ν hν
    w₀ G hG (fun z x hx => (hgeom z x hx).1.symm) hμ hballs hcaps
  have hL : 1+1+((h+2+1:ℕ):ℝ)+1/2 ≤ (L:ℝ) := by dsimp [L]; push_cast; linarith
  have hrobust : (2*((h+2+1:ℕ):ℝ)+1)*δ+2*(2*(1/4)/r)*(1/4+1/4) ≤ C*δ := by
    have he : 2*(2*(1/4:ℝ)/r)*(1/4+1/4) = 8*(1/4:ℝ)^2/r := by ring
    rw [he]
    dsimp [C]
    change 8*(1/4:ℝ)^2/r ≤ δ at hfreeze
    nlinarith
  have henv (v : Sphere (h+3)) (S : Finset (Space (h+3)))
      (hc : (S.card:ℝ≥0∞)*ENNReal.ofReal (δ^((h+1:ℝ)+b/2)) ≤
        ((2*L+1)^(h+2+1):ℕ)*μ univ)
      (hm : ENNReal.ofReal (δ^b) ≤
        μ {z | ∃ a ∈ S, ‖perpendicularPart (v:Space (h+3)) (z-a)‖ ≤ C*δ}) : v ∈ Bad := by
    apply hcontains
    refine ⟨S,?_,hm⟩
    apply hN₂ N ((le_max_right _ _).trans hN) S.card
    simpa only [measure_univ,mul_one,ENNReal.ofReal_natCast] using hc
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := middle_radial_pruning (θ := θ) (n := h+2) μ ν w₀ G hG
    Bad hBad 0 hr hδ hfreeze (by simpa only [sub_zero] using hμ) hμ
    (fun z x hx => ⟨(hgeom z x hx).1,by simpa only [sub_zero] using (hgeom z x hx).2,
      (hgeom z x hx).2⟩) hpin (by simpa only [one_mul] using hwidth) hrobust (ENNReal.ofReal (δ^((h+1:ℝ)+b/2)))
    (ENNReal.ofReal (δ^b)) (ENNReal.ofReal (δ^b)) L hL henv hbadmass
  refine ⟨G',hG',hsub,hdel.trans ?_,hbound⟩
  calc
    _ ≤ ENNReal.ofReal (δ^b)+ENNReal.ofReal (δ^b)*1 :=
      add_le_add le_rfl (mul_le_mul' le_rfl hν)
    _ = 2*ENNReal.ofReal (δ^b) := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoom
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive affine changes of scale preserve original radial directions -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem zoomPairSet_measurable (e : Space d ≃ₜ Space d)
    {G : Set (Space d × Space d)} (hG : MeasurableSet G) : MeasurableSet (zoomPairSet e G) :=
  hG.preimage (e.symm.measurable.prodMap e.symm.measurable)

theorem radial_collision_zoom (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z x : Space d) (θ : ℝ) :
    radialCollisionMass (Measure.map (radialZoom a ha.ne' c) μ) θ
      (radialZoom a ha.ne' c z,radialZoom a ha.ne' c x) = radialCollisionMass μ θ (z,x) := by
  let e := radialZoom a ha.ne' c
  unfold radialCollisionMass
  rw [Measure.map_apply e.measurable (by
    apply measurableSet_le _ measurable_const
    exact (measurable_normalized_vector (measurable_id.sub measurable_const)).dist measurable_const)]
  congr 1
  ext y
  dsimp only [e]
  simp only [mem_preimage,mem_ofPred_eq,radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomLaw
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original radial laws and source balls under positive affine rescaling -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_preimage_ball {a : ℝ} (ha : 0 < a) (c x : Space d) (r : ℝ) :
    radialZoom a ha.ne' c ⁻¹' Metric.ball x r = Metric.ball (c+a⁻¹ • x) (r/a) := by
  ext z
  have he : a • (z-c)-x = a • (z-(c+a⁻¹ • x)) := by
    simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
    abel
  simp only [mem_preimage,Metric.mem_ball,dist_eq_norm,radialZoom_apply]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ha,lt_div_iff₀ ha]
  rw [mul_comm a]

theorem radialZoom_ball_apply (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c x : Space d) (r : ℝ) :
    Measure.map (radialZoom a ha.ne' c) μ (Metric.ball x r) =
      μ (Metric.ball (c+a⁻¹ • x) (r/a)) := by
  rw [Measure.map_apply (radialZoom a ha.ne' c).measurable Metric.isOpen_ball.measurableSet,
    radialZoom_preimage_ball ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded supports and Frostman bounds survive the fixed cell normalization -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_norm {a : ℝ} (ha : 0 < a) (c x : Space d) :
    ‖radialZoom a ha.ne' c x‖ = a*‖x-c‖ := by
  rw [radialZoom_apply,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RadialZoomFiniteBalls
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale conditional balls and reverse caps after a fixed contraction -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_ae_iff (μ : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c : Space d) (P : Space d → Prop) :
    (∀ᵐ x ∂Measure.map (radialZoom a ha.ne' c) μ, P x) ↔
      ∀ᵐ x ∂μ, P (radialZoom a ha.ne' c x) := by
  have h := MeasurableEquiv.map_ae (radialZoom a ha.ne' c).toMeasurableEquiv μ
  change Filter.map (radialZoom a ha.ne' c) (ae μ) =
    ae (Measure.map (radialZoom a ha.ne' c) μ) at h
  rw [← h]
  rfl

theorem norm_radialZoom_sub {a : ℝ} (ha : 0 < a) (c x y : Space d) :
    ‖radialZoom a ha.ne' c x-radialZoom a ha.ne' c y‖ = a*‖x-y‖ := by
  rw [radialZoom_sub,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

theorem radialZoom_reverse_cap (ν : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z u : Space d) (r : ℝ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    Measure.map (radialZoom a ha.ne' c) ν
      {x | (radialZoom a ha.ne' c z,x) ∈ zoomPairSet (radialZoom a ha.ne' c) G ∧
        dist (normalize (x-radialZoom a ha.ne' c z)) u < r} =
      ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} := by
  let e := radialZoom a ha.ne' c
  have hm : MeasurableSet {x | (e z,x) ∈ zoomPairSet e G ∧
      dist (normalize (x-e z)) u < r} :=
    ((zoomPairSet_measurable e hG).preimage (measurable_const.prodMk measurable_id)).inter
      (measurableSet_lt ((measurable_normalized_vector
        (measurable_id.sub measurable_const)).dist measurable_const) measurable_const)
  rw [Measure.map_apply e.measurable hm]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
  dsimp only [e]
  rw [radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_MiddleRadialTransport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric data for middle-interval pruning after cell normalization -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal
variable {d : ℕ}

theorem radialZoom_quarter_bound {a : ℝ} (ha : 0 < a) (c z : Space d)
    (hz : ‖z-c‖ ≤ 1/(4*a)) : ‖radialZoom a ha.ne' c z‖ ≤ 1/4 := by
  rw [radialZoom_norm ha]
  calc
    _ ≤ a*(1/(4*a)) := mul_le_mul_of_nonneg_left hz ha.le
    _ = _ := by field_simp

theorem radialZoom_pin_distance {a r : ℝ} (ha : 0 < a) (c x : Space d)
    (hx : r ≤ ‖c-x‖) : a*r ≤ ‖(0:Space d)-radialZoom a ha.ne' c x‖ := by
  rw [zero_sub,norm_neg,radialZoom_norm ha,norm_sub_rev x c]
  exact mul_le_mul_of_nonneg_left hx ha.le

theorem radialZoom_pair_ae_bound (μ : Measure (Space d)) {a H : ℝ}
    (ha : 0 < a) (c x : Space d) (h : ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) :
    ∀ᵐ y ∂Measure.map (radialZoom a ha.ne' c) μ,
      ‖y-radialZoom a ha.ne' c x‖ ≤ a*H := by
  rw [radialZoom_ae_iff μ ha]
  filter_upwards [h] with y hy
  rw [norm_radialZoom_sub ha]
  exact mul_le_mul_of_nonneg_left hy ha.le

theorem radialZoom_reverse_slab (ν : Measure (Space d)) {a : ℝ} (ha : 0 < a)
    (c z u : Space d) (r : ℝ) (G : Set (Space d × Space d)) (hG : MeasurableSet G) :
    Measure.map (radialZoom a ha.ne' c) ν
      {x | (radialZoom a ha.ne' c z,x) ∈ zoomPairSet (radialZoom a ha.ne' c) G ∧
        |inner ℝ u (normalize (x-radialZoom a ha.ne' c z))| ≤ r} =
      ν {x | (z,x) ∈ G ∧ |inner ℝ u (normalize (x-z))| ≤ r} := by
  let e := radialZoom a ha.ne' c
  have hi : Measurable (fun x : Space d => inner ℝ u (normalize (x-e z))) :=
    measurable_const.inner (measurable_normalized_vector (measurable_id.sub measurable_const))
  have hm : MeasurableSet {x | (e z,x) ∈ zoomPairSet e G ∧
      |inner ℝ u (normalize (x-e z))| ≤ r} :=
    ((zoomPairSet_measurable e hG).preimage (measurable_const.prodMk measurable_id)).inter
      (measurableSet_le hi.abs measurable_const)
  rw [Measure.map_apply e.measurable hm]
  congr 1
  ext x
  simp only [mem_preimage,mem_ofPred_eq,mem_zoomPairSet]
  dsimp only [e]
  rw [radialZoom_sub,normalize_smul_of_pos ha]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialZoomPruning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pulling conditional radial pruning back to the unchanged original pair law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_pruning_unzoom (μ ν : Measure (Space d)) [SFinite μ] [SFinite ν]
    {a : ℝ} (ha : 0 < a) (c : Space d)
    (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (H : Set (Space d × Space d)) (hH : MeasurableSet H)
    (hsub : H ⊆ zoomPairSet (radialZoom a ha.ne' c) G)
    (θ : ℝ) (F E : ℝ≥0∞)
    (hdel : ((Measure.map (radialZoom a ha.ne' c) μ).prod
      (Measure.map (radialZoom a ha.ne' c) ν))
      (zoomPairSet (radialZoom a ha.ne' c) G \ H) ≤ E)
    (hbound : ∀ p ∈ H, radialCollisionMass (Measure.map (radialZoom a ha.ne' c) μ) θ p ≤ F) :
    ∃ G' : Set (Space d × Space d), MeasurableSet G' ∧ G' ⊆ G ∧
      (μ.prod ν) (G \ G') ≤ E ∧ ∀ p ∈ G', radialCollisionMass μ θ p ≤ F := by
  let e := radialZoom a ha.ne' c
  let G' := (Prod.map e e) ⁻¹' H
  have hG' : MeasurableSet G' := hH.preimage (e.measurable.prodMap e.measurable)
  refine ⟨G',hG',?_,?_,?_⟩
  · intro p hp
    exact (mem_zoomPairSet e G p.1 p.2).mp (hsub hp)
  · have he : (Prod.map e e) ⁻¹' (zoomPairSet e G \ H) = G \ G' := by
      ext p
      change ((e p.1,e p.2) ∈ zoomPairSet e G ∧ (e p.1,e p.2) ∉ H) ↔
        ((p.1,p.2) ∈ G ∧ (e p.1,e p.2) ∉ H)
      rw [mem_zoomPairSet]
    rw [← he,← Measure.map_apply (e.measurable.prodMap e.measurable)
      ((zoomPairSet_measurable e hG).diff hH),← Measure.map_prod_map μ ν e.measurable e.measurable]
    exact hdel
  · intro p hp
    have hh := hbound (e p.1,e p.2) hp
    rwa [radial_collision_zoom μ ha c p.1 p.2 θ] at hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_EndpointOriginalMiddle
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint middle-interval pruning in the original source-cell coordinates -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem endpoint_original_middle_pruning_oai (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} {t ζ : ℝ} (ht : (h:ℝ)+3/2 < t) (ht' : t < (h:ℝ)+2)
    (hζ : 0 < ζ) :
    ∃ ε b : ℝ, 0 < ε ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N ≥ N₀, ∀ (μ ν : Measure (Space (h+3)))
        [IsProbabilityMeasure μ] [IsFiniteMeasure ν], ν univ ≤ 1 →
      ∀ (_w₀ : Sphere (h+3)) (c : Space (h+3)) (a : ℝ), 0 < a →
      ∀ G : Set (Space (h+3) × Space (h+3)), MeasurableSet G →
      (∀ z x, (z,x) ∈ G → z ≠ x ∧ ‖z-c‖ ≤ 1/(4*a)) →
      (∀ᵐ z ∂μ, ‖z-c‖ ≤ 1/(4*a)) →
      (∀ x : Space (h+3), ∀ j : ℕ, j ≤ N → μ (Metric.ball x ((1/(2:ℝ)^j)/a)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t)) →
      (∀ᵐ z ∂μ,
        (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N →
          ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) (w:Space (h+3)) < 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) ∧
        (∀ w : Sphere (h+3), ∀ u : ℝ, 1/(2:ℝ)^N ≤ u → u ≤ 1 →
          ν {x | (z,x) ∈ G ∧ |inner ℝ (w:Space (h+3)) (normalize (x-z))| ≤ u} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*u^ζ))) →
      ∀ r H θ : ℝ, 0 < r → 8*(1/4:ℝ)^2/(a*r) ≤ 1/(2:ℝ)^N →
      (a*H)*θ ≤ 1/(2:ℝ)^N →
      (∀ x, (∃ z, (z,x) ∈ G) → r ≤ ‖c-x‖ ∧ ∀ᵐ y ∂μ, ‖y-x‖ ≤ H) →
      ∃ G' : Set (Space (h+3) × Space (h+3)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ 2*ENNReal.ofReal ((1/(2:ℝ)^N)^b) ∧
        ∀ p ∈ G', radialCollisionMass μ θ p ≤ ENNReal.ofReal ((1/(2:ℝ)^N)^((h+1:ℝ)+b/2)) := by
  obtain ⟨ε,b,hε,hb,N₀,hN₀⟩ := endpoint_middle_radial_pruning hLW ht ht' hζ
  refine ⟨ε,b,hε,hb,N₀,?_⟩
  intro N hN μ ν _ _ hν w₀ c a ha G hG hgeom hμ hball hcap r H θ hr hfreeze hwidth hpin
  let e := radialZoom a ha.ne' c
  have hν' : Measure.map e ν univ ≤ 1 := by
    simpa only [Measure.map_apply e.measurable MeasurableSet.univ,preimage_univ] using hν
  have hgeom' : ∀ z x, (z,x) ∈ zoomPairSet e G → z ≠ x ∧ ‖z‖ ≤ 1/4 := by
    intro z x hx
    have hh := hgeom (e.symm z) (e.symm x) hx
    refine ⟨fun he => hh.1 (congrArg e.symm he),?_⟩
    have hn := radialZoom_quarter_bound ha c (e.symm z) hh.2
    change ‖e (e.symm z)‖ ≤ 1/4 at hn
    simpa only [e.apply_symm_apply] using hn
  have hμ' : ∀ᵐ z ∂Measure.map e μ, ‖z‖ ≤ 1/4 := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hμ] with z hz
    exact radialZoom_quarter_bound ha c z hz
  have hball' : ∀ x : Space (h+3), ∀ j : ℕ, j ≤ N →
      Measure.map e μ (Metric.ball x (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^t) := by
    intro x j hj
    rw [radialZoom_ball_apply μ ha]
    exact hball _ j hj
  have hcap' : ∀ᵐ z ∂Measure.map e μ,
      (∀ w : Sphere (h+3), ∀ j : ℕ, j ≤ N →
        Measure.map e ν {x | (z,x) ∈ zoomPairSet e G ∧
          dist (normalize (x-z)) (w:Space (h+3)) < 1/(2:ℝ)^j} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*(1/(2:ℝ)^j)^(h+1:ℝ))) ∧
      (∀ w : Sphere (h+3), ∀ u : ℝ, 1/(2:ℝ)^N ≤ u → u ≤ 1 →
        Measure.map e ν {x | (z,x) ∈ zoomPairSet e G ∧
          |inner ℝ (w:Space (h+3)) (normalize (x-z))| ≤ u} ≤
            ENNReal.ofReal ((1/(2:ℝ)^N)^(-ε)*u^ζ)) := by
    rw [radialZoom_ae_iff μ ha]
    filter_upwards [hcap] with z hz
    constructor
    · intro w j hj
      rw [radialZoom_reverse_cap ν ha c z w _ G hG]
      exact hz.1 w j hj
    · intro w u hu hu1
      rw [radialZoom_reverse_slab ν ha c z w u G hG]
      exact hz.2 w u hu hu1
  have hpin' : ∀ x, (∃ z, (z,x) ∈ zoomPairSet e G) →
      a*r ≤ ‖(0:Space (h+3))-x‖ ∧ ∀ᵐ y ∂Measure.map e μ, ‖y-x‖ ≤ a*H := by
    intro x hx
    obtain ⟨z,hz⟩ := hx
    have hp := hpin (e.symm x) ⟨e.symm z,hz⟩
    have he : e (e.symm x) = x := e.apply_symm_apply x
    refine ⟨?_,?_⟩
    · have hd := radialZoom_pin_distance ha c (e.symm x) hp.1
      change a*r ≤ ‖(0:Space (h+3))-e (e.symm x)‖ at hd
      simpa only [he] using hd
    · have hb := radialZoom_pair_ae_bound μ ha c (e.symm x) hp.2
      change ∀ᵐ y ∂Measure.map e μ, ‖y-e (e.symm x)‖ ≤ a*H at hb
      simpa only [he] using hb
  haveI : IsProbabilityMeasure (Measure.map e μ) := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := hN₀ N hN (Measure.map e μ) (Measure.map e ν) hν'
    w₀ (zoomPairSet e G) (zoomPairSet_measurable e hG) hgeom' hμ' hball' hcap'
    (a*r) (a*H) θ (mul_pos ha hr) hfreeze hwidth hpin'
  exact radial_pruning_unzoom μ ν ha c G hG G' hG' hsub θ _ _ hdel hbound

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.endpoint_original_middle_pruning_oai := @OAI.Falconer.endpoint_original_middle_pruning_oai
