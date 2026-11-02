-- Prove2me | solution 1 for OAI.Problem047.removability_implies_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T06:16:57.140921+00:00
-- url     : https://prove2.me/submissions/9f5d21db-bba4-4b5d-b9ea-97e82f9f5fdd

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C011
import Theorems.Thm_OAI_CircleDomainRigidity_circleDomainRemovabilityRigidity_of_scalar_solver
import Theorems.Thm_OAI_CircleDomainRigidity_exteriorCoefficientAreaTheorem
import Theorems.Thm_OAI_CircleDomainRigidity_exteriorOmittedAreaTheorem
import Theorems.Thm_OAI_CircleDomainRigidity_finiteJordanModelUniformization
import Theorems.Thm_OAI_CircleDomainRigidity_koebeCircleDomainConjecture_of_constructed_quotient
import Theorems.Thm_OAI_CircleDomainRigidity_planarSobolevCoarea
import Theorems.Thm_OAI_CircleDomainRigidity_principalConductivityScalarSolver
import Theorems.Thm_OAI_CircleDomainRigidity_principalRealBeltrami
import Theorems.Thm_OAI_CircleDomainRigidity_smoothCompactMetricSphereUniformization
import Theorems.Thm_OAI_CircleDomainRigidity_smoothRegularJordanCollars
import Theorems.Thm_OAI_CircleDomainRigidity_unorientedFiniteCircleGreenFormula

section
-- module Solutions.Q146_CD.Compat
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_AnalyticWordBranch
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A branch through finite Baire words identifies an actual point of a
continuous image. This is the topological step for completed measurability. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem baireWordCylinder_nil : baireWordCylinder [] = univ := by
  ext b
  simp [baireWordCylinder]

 theorem baireWordCylinder_children (s : List ℕ) :
    (⋃ k, baireWordCylinder (k::s)) = baireWordCylinder s := by
  ext b
  simp only [mem_iUnion,baireWordCylinder,mem_ofPred_eq,List.length_cons,PiNat.res_succ]
  constructor
  · rintro ⟨k,hk⟩
    exact (List.cons.inj hk).2
  · intro hb
    exact ⟨b s.length,by rw [hb]⟩

 theorem isOpen_baireWordCylinder (s : List ℕ) : IsOpen (baireWordCylinder s) := by
  induction s with
  | nil => rw [baireWordCylinder_nil]; exact isOpen_univ
  | cons k s ih =>
    have he : baireWordCylinder (k::s) =
        (fun b : ℕ → ℕ => b s.length) ⁻¹' {k} ∩ baireWordCylinder s := by
      ext b
      simp only [baireWordCylinder,mem_ofPred_eq,List.length_cons,PiNat.res_succ,
        List.cons.injEq,mem_inter_iff,mem_preimage,mem_singleton_iff]
    rw [he]
    exact ((isOpen_discrete {k}).preimage (continuous_apply s.length)).inter ih

 theorem eq_of_prefix_closures {X : Type*} [MetricSpace X]
    {f : (ℕ → ℕ) → X} (hf : Continuous f) {b : ℕ → ℕ} {x : X}
    (hx : ∀ n, x ∈ closure (f '' PiNat.cylinder b n)) : x = f b := by
  by_contra hne
  have hd : 0 < dist x (f b) := dist_pos.mpr hne
  obtain ⟨V,⟨c,n,rfl⟩,hb,hV⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open
      (show b ∈ f ⁻¹' Metric.ball (f b) (dist x (f b)/2) from Metric.mem_ball_self (half_pos hd))
      (Metric.isOpen_ball.preimage hf)
  have he : PiNat.cylinder b n = PiNat.cylinder c n := PiNat.mem_cylinder_iff_eq.mp hb
  have hsub : f '' PiNat.cylinder b n ⊆ Metric.closedBall (f b) (dist x (f b)/2) := by
    rintro z ⟨a,ha,rfl⟩
    exact Metric.ball_subset_closedBall (hV (he ▸ ha))
  have hclosed := (closure_minimal hsub Metric.isClosed_closedBall) (hx n)
  exact (not_lt_of_ge (Metric.mem_closedBall.mp hclosed)) (half_lt_self hd)

 theorem mem_range_of_prefix_closures {X : Type*} [MetricSpace X]
    {f : (ℕ → ℕ) → X} (hf : Continuous f) {b : ℕ → ℕ} {x : X}
    (hx : ∀ n, x ∈ closure (f '' PiNat.cylinder b n)) : x ∈ range f :=
  ⟨b,(eq_of_prefix_closures hf hx).symm⟩

 theorem mem_range_of_word_hull_branch {X : Type*} [MetricSpace X]
    {f : (ℕ → ℕ) → X} (hf : Continuous f) (B : List ℕ → Set X) {x : X}
    (hroot : x ∈ B [])
    (hnext : ∀ s, x ∈ B s → ∃ k, x ∈ B (k::s))
    (hB : ∀ s, B s ⊆ closure (f '' baireWordCylinder s)) : x ∈ range f := by
  classical
  let pick (s : List ℕ) (hs : x ∈ B s) := Classical.choose (hnext s hs)
  have hpick (s : List ℕ) (hs : x ∈ B s) : x ∈ B (pick s hs :: s) :=
    Classical.choose_spec (hnext s hs)
  let p : ℕ → {s : List ℕ // x ∈ B s} :=
    Nat.rec ⟨[],hroot⟩ (fun _ s => ⟨pick s.val s.property :: s.val,hpick s.val s.property⟩)
  let b : ℕ → ℕ := fun n => pick (p n).val (p n).property
  have hres (n : ℕ) : PiNat.res b n = (p n).val := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change b n :: PiNat.res b n = b n :: (p n).val
      rw [ih]
  apply mem_range_of_prefix_closures hf (b := b)
  intro n
  have hh := hB (p n).val (p n).property
  have he : baireWordCylinder (p n).val = PiNat.cylinder b n := by
    rw [← hres n,PiNat.cylinder_eq_res]
    ext c
    simp only [baireWordCylinder,PiNat.res_length,mem_ofPred_eq]
  rwa [he] at hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_AnalyticFiniteMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Borel measures see continuous Baire images in their completion.
Measurable hulls of finite-prefix images have null child defects; outside
all defects, an infinite branch recovers a point of the actual image. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem nullMeasurableSet_baire_image_finite {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) : NullMeasurableSet (range f) μ := by
  classical
  let A : List ℕ → Set X := fun s => f '' baireWordCylinder s
  let B : List ℕ → Set X := fun s => toMeasurable μ (A s) ∩ closure (A s)
  have hB (s : List ℕ) : MeasurableSet (B s) :=
    (measurableSet_toMeasurable μ (A s)).inter isClosed_closure.measurableSet
  have hAB (s : List ℕ) : A s ⊆ B s :=
    fun _ hx => ⟨subset_toMeasurable μ _ hx,subset_closure hx⟩
  have hmeasure (s : List ℕ) : μ (B s) = μ (A s) :=
    le_antisymm ((measure_mono inter_subset_left).trans_eq (measure_toMeasurable (A s)))
      (measure_mono (hAB s))
  have hchildren (s : List ℕ) : (⋃ k, A (k::s)) = A s := by
    dsimp only [A]
    rw [← image_iUnion,baireWordCylinder_children]
  let N : List ℕ → Set X := fun s => B s \ ⋃ k, B (k::s)
  have hN (s : List ℕ) : μ (N s) = 0 := by
    have hc : A s ⊆ B s ∩ ⋃ k, B (k::s) := by
      intro x hx
      refine ⟨hAB s hx,?_⟩
      obtain ⟨k,hk⟩ := mem_iUnion.mp ((hchildren s).symm ▸ hx)
      exact mem_iUnion.mpr ⟨k,hAB (k::s) hk⟩
    have he : μ (B s ∩ ⋃ k, B (k::s)) = μ (B s) :=
      le_antisymm (measure_mono inter_subset_left)
        ((hmeasure s).le.trans (measure_mono hc))
    have hh := measure_sdiff inter_subset_left
      ((hB s).inter (MeasurableSet.iUnion (fun k => hB (k::s)))).nullMeasurableSet
      (measure_ne_top μ (B s ∩ ⋃ k, B (k::s)))
    rw [he,tsub_self] at hh
    simpa only [N,sdiff_inter,sdiff_self,empty_union] using hh
  have hnull : μ (⋃ s, N s) = 0 := measure_iUnion_null hN
  have heq : B [] =ᵐ[μ] range f := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    apply propext
    constructor
    · intro hroot
      apply mem_range_of_word_hull_branch hf B hroot
      · intro s hs
        by_contra hn
        apply hx
        exact mem_iUnion.mpr ⟨s,hs,by simpa only [mem_iUnion,not_exists] using hn⟩
      · exact fun s => inter_subset_right
    · intro hx
      apply hAB []
      simpa only [A,baireWordCylinder_nil,image_univ] using (show x ∈ range f from hx)
  exact (hB []).nullMeasurableSet.congr heq

 theorem nullMeasurableSet_analytic_finite {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {A : Set X} (hA : AnalyticSet A) : NullMeasurableSet A μ := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f,hf,rfl⟩
  · exact nullMeasurableSet_empty
  · exact nullMeasurableSet_baire_image_finite μ f hf

 theorem finiteTorusAnalyticMeasurability : FiniteTorusAnalyticMeasurability := by
  intro d E hE
  rw [AnalyticSet] at hE
  rcases hE with rfl | ⟨f,hf,rfl⟩
  · exact nullMeasurableSet_empty
  · exact nullMeasurableSet_baire_image_finite _ f hf

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeakProbabilityMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous family of weak probability laws is a measurable family of
measures. Closed-set evaluations are limits of continuous test integrals. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma measurable_measure_of_continuous_probability
    {X Z : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [HasOuterApproxClosed Z]
    {F : X → ProbabilityMeasure Z} (hF : Continuous F) :
    Measurable (fun x => (F x : Measure Z)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
  intro S hS
  apply measurable_of_tendsto_metrizable
    (fun n => ((ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
      (hS.apprSeq n)).comp hF).measurable)
  apply tendsto_pi_nhds.mpr
  intro x
  exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hS (F x : Measure Z)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactFiniteMeasureMeasurability
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Only the measurable inclusion of a compact weak family is needed for
Riesz representation. No replacement of the evaluation sigma algebra is made. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace CircleDomainRigidity

lemma measurable_measure_of_continuous_finite
    {X Z : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [HasOuterApproxClosed Z]
    {F : X → FiniteMeasure Z} (hF : Continuous F) :
    Measurable (fun x => (F x : Measure Z)) := by
  apply Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
  · intro S hS
    apply measurable_of_tendsto_metrizable
      (fun n => ((FiniteMeasure.continuous_lintegral_boundedContinuousFunction
        (hS.apprSeq n)).comp hF).measurable)
    apply tendsto_pi_nhds.mpr
    intro x
    exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hS (F x : Measure Z)
  · simpa only [← FiniteMeasure.ennreal_mass,Function.comp_def] using
      (ENNReal.continuous_coe.comp (FiniteMeasure.continuous_mass.comp hF)).measurable

lemma compact_finiteMeasure_measurable_le_borel
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [HasOuterApproxClosed Z] (S : Set (FiniteMeasure Z)) :
    (inferInstance : MeasurableSpace S) ≤ borel S := by
  have h : @Measurable S (Measure Z) (borel S) inferInstance
      (fun v => (v.val : Measure Z)) := by
    let : MeasurableSpace S := borel S
    let : BorelSpace S := ⟨rfl⟩
    exact measurable_measure_of_continuous_finite continuous_subtype_val
  change ((inferInstance : MeasurableSpace (Measure Z)).comap
    (fun v : FiniteMeasure Z => (v : Measure Z))).comap
      (fun v : S => v.val) ≤ borel S
  simpa only [MeasurableSpace.comap_comp,Function.comp_def] using h.comap_le

lemma measurable_finiteMeasure_integral
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (f : Z →ᵇ ℝ) : Measurable (fun v : FiniteMeasure Z => ∫ z, f z ∂(v : Measure Z)) := by
  have hv : Measurable (fun v : FiniteMeasure Z => (v : Measure Z)) := measurable_subtype_coe
  have hp := ((Measure.measurable_lintegral f.nnrealPart.measurable_coe_ennreal_comp).comp
    hv).ennreal_toReal
  have hn := ((Measure.measurable_lintegral (-f).nnrealPart.measurable_coe_ennreal_comp).comp
    hv).ennreal_toReal
  convert hp.sub hn using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub]
  simp only [Pi.sub_apply,Function.comp_def]
  rw [BoundedContinuousFunction.toReal_lintegral_coe_eq_integral,
    BoundedContinuousFunction.toReal_lintegral_coe_eq_integral]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureMajorants
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous test integrals on a compact family of finite measures and
the uniform positive mass needed for the compact duality construction. -/
open Set MeasureTheory
open scoped BoundedContinuousFunction ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]

lemma compact_family_positive_mass {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S) :
    ∃ m : ℝ≥0, 0 < m ∧ ∀ v ∈ S, m ≤ v.mass := by
  obtain ⟨v,hv,hmin⟩ := hS.exists_isMinOn hne FiniteMeasure.continuous_mass.continuousOn
  refine ⟨v.mass,?_,hmin⟩
  exact pos_iff_ne_zero.mpr ((FiniteMeasure.mass_nonzero_iff v).mpr (fun he => hz (he ▸ hv)))

lemma compactMeasureTestOperator_const (S : Set (FiniteMeasure Z)) (r : ℝ) (v : S) :
    compactMeasureTestOperator S (BoundedContinuousFunction.const Z r) v =
      r * (v.val.mass : ℝ) := by
  simp [compactMeasureTestOperator,integral_const,measureReal_def,
    ← FiniteMeasure.ennreal_mass,mul_comm]

lemma exists_compact_measure_constant_majorant {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (u : C(S,ℝ)) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ v : S,
      u v ≤ compactMeasureTestOperator S (BoundedContinuousFunction.const Z r) v := by
  obtain ⟨m,hm,hmass⟩ := compact_family_positive_mass hS hne hz
  have hm' : 0 < (m : ℝ) := hm
  refine ⟨‖u‖ / m,div_nonneg (norm_nonneg _) hm'.le,?_⟩
  intro v
  rw [compactMeasureTestOperator_const]
  have hv : (m : ℝ) ≤ v.val.mass := hmass v.val v.property
  calc
    u v ≤ ‖u‖ := u.apply_le_norm v
    _ = (‖u‖ / m) * m := (div_mul_cancel₀ _ hm'.ne').symm
    _ ≤ (‖u‖ / m) * (v.val.mass : ℝ) :=
      mul_le_mul_of_nonneg_left hv (div_nonneg (norm_nonneg _) hm'.le)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureBarycenter
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual barycenter measure of a law on a compact family.
Both its finite mass and its nonnegative continuous test integrals follow
from the measurable measure-valued inclusion, not an assumed identity. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {S : Set (FiniteMeasure Z)}

omit [TopologicalSpace Z] [BorelSpace Z] in
lemma measurable_compactMeasure_inclusion :
    Measurable (fun v : S => (v.val : Measure Z)) :=
  measurable_subtype_coe.comp measurable_subtype_coe

omit [TopologicalSpace Z] [BorelSpace Z] in
lemma compactMeasureBarycenter_apply (P : ProbabilityMeasure S)
    {E : Set Z} (hE : MeasurableSet E) :
    compactMeasureBarycenter P E = ∫⁻ v : S, (v.val : Measure Z) E ∂(P : Measure S) :=
  Measure.bind_apply hE measurable_compactMeasure_inclusion.aemeasurable

lemma compactMeasureBarycenter_finite (hS : IsCompact S) (P : ProbabilityMeasure S) :
    IsFiniteMeasure (compactMeasureBarycenter P) := by
  obtain ⟨C,hC⟩ := (hS.image FiniteMeasure.continuous_mass).bddAbove
  have hb : compactMeasureBarycenter P univ ≤ (C : ℝ≥0∞) := by
    rw [compactMeasureBarycenter_apply P MeasurableSet.univ]
    calc
      (∫⁻ v : S, (v.val : Measure Z) univ ∂(P : Measure S)) ≤
          ∫⁻ _v : S, (C : ℝ≥0∞) ∂(P : Measure S) := by
        apply lintegral_mono
        intro v
        change (v.val : Measure Z) univ ≤ (C : ℝ≥0∞)
        rw [← FiniteMeasure.ennreal_mass]
        exact_mod_cast hC (mem_image_of_mem FiniteMeasure.mass v.property)
      _ = C := by simp
  exact ⟨hb.trans_lt ENNReal.coe_lt_top⟩

omit [TopologicalSpace Z] [BorelSpace Z] in
lemma compactMeasureBarycenter_lintegral (P : ProbabilityMeasure S)
    {f : Z → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂compactMeasureBarycenter P) =
      ∫⁻ v : S, (∫⁻ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S) :=
  Measure.lintegral_bind measurable_compactMeasure_inclusion.aemeasurable hf.aemeasurable

lemma compactMeasureBarycenter_integral_nonneg [CompactSpace S]
    (P : ProbabilityMeasure S) (f : Z →ᵇ ℝ) (hf : ∀ z, 0 ≤ f z) :
    (∫ z, f z ∂compactMeasureBarycenter P) =
      ∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S) := by
  have hi (v : S) : 0 ≤ ∫ z, f z ∂(v.val : Measure Z) := integral_nonneg hf
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf)
      f.continuous.measurable.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hi)
      ((measurable_finiteMeasure_integral f).comp measurable_subtype_coe).aestronglyMeasurable]
  apply congrArg ENNReal.toReal
  rw [compactMeasureBarycenter_lintegral P f.continuous.measurable.ennreal_ofReal]
  apply lintegral_congr_ae
  exact Eventually.of_forall fun v =>
    (ofReal_integral_eq_lintegral_ofReal (f.integrable (μ := (v.val : Measure Z))) (Eventually.of_forall hf)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactPositiveFunctional
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact-space representation step for the measure-modulus dual:
a positive linear functional taking the constant one to one is a genuine
probability law. This is the existing Riesz representation theorem. -/
open Set MeasureTheory
open scoped CompactlySupported
noncomputable section
namespace CircleDomainRigidity

lemma exists_probability_of_compact_positive_functional
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    (h1 : Λ ⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩ = 1) :
    ∃ P : ProbabilityMeasure X, ∀ f : C_c(X,ℝ), ∫ x, f x ∂(P : Measure X) = Λ f := by
  let μ := RealRMK.rieszMeasure Λ
  have hm : μ univ = 1 := by
    apply (ENNReal.toReal_eq_one_iff _).mp
    have hi := RealRMK.integral_rieszMeasure Λ
      (⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩ : C_c(X,ℝ))
    rw [h1] at hi
    change (∫ _x : X, (1 : ℝ) ∂μ) = 1 at hi
    simpa only [integral_const, smul_eq_mul, mul_one, measureReal_def] using hi
  let : IsProbabilityMeasure μ := ⟨hm⟩
  exact ⟨⟨μ,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩,RealRMK.integral_rieszMeasure Λ⟩

lemma exists_probability_of_compact_positive_functional_trim
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [m : MeasurableSpace X] (hm : m ≤ borel X)
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    (h1 : Λ ⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩ = 1) :
    ∃ P : ProbabilityMeasure X, ∀ f : C_c(X,ℝ), Measurable f →
      (∫ x, f x ∂(P : Measure X)) = Λ f := by
  have hex : ∃ μ : @Measure X (borel X), μ univ = 1 ∧
      ∀ f : C_c(X,ℝ), (∫ x, f x ∂μ) = Λ f := by
    let : MeasurableSpace X := borel X
    let : BorelSpace X := ⟨rfl⟩
    obtain ⟨P,hP⟩ := exists_probability_of_compact_positive_functional Λ h1
    exact ⟨(P : Measure X),measure_univ,hP⟩
  obtain ⟨μ,hμ,hint⟩ := hex
  let ν : Measure X := μ.trim hm
  have hn : ν univ = 1 := by
    change μ.trim hm univ = 1
    rw [trim_measurableSet_eq hm MeasurableSet.univ]
    exact hμ
  let : IsProbabilityMeasure ν := ⟨hn⟩
  refine ⟨⟨ν,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩,?_⟩
  intro f hf
  change (∫ x, f x ∂μ.trim hm) = Λ f
  rw [← integral_trim hm hf.stronglyMeasurable]
  exact hint f

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CompactMajorantSeparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hahn–Banach separation for a compact family of measures and a
sublinear majorant cost. -/
open Set MeasureTheory
open scoped CompactlySupported
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_positive_functional_of_majorant_cost
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (p : C_c(X, ℝ) → ℝ)
    (phom : ∀ c : ℝ, 0 < c → ∀ f, p (c • f) = c * p f)
    (padd : ∀ f g, p (f+g) ≤ p f + p g)
    (pneg : ∀ f, (∀ x, 0 ≤ f x) → p (-f) = 0)
    (c : ℝ)
    (pconst : ∀ r : ℝ, r*c ≤ p
      (r • (⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩ : C_c(X,ℝ)))) :
    ∃ Λ : C_c(X,ℝ) →ₚ[ℝ] ℝ,
      Λ ⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩ = c ∧
      ∀ f, Λ f ≤ p f := by
  classical
  let oneX : C_c(X,ℝ) := ⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩
  let V : Submodule ℝ C_c(X,ℝ) := Submodule.span ℝ {oneX}
  let x₀ : X := Classical.choice inferInstance
  let ev : C_c(X,ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => f x₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let l : V →ₗ[ℝ] ℝ := c • (ev.comp V.subtype)
  have hl (f : V) : l f ≤ p f := by
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp f.property
    change c * ev f.val ≤ p f.val
    rw [← hr]
    simpa [ev,oneX,mul_comm] using pconst r
  obtain ⟨L,hL,hLp⟩ := exists_extension_of_le_sublinear
    (⟨V,l⟩ : C_c(X,ℝ) →ₗ.[ℝ] ℝ) p phom padd hl
  have hpos (f : C_c(X,ℝ)) (hf : 0 ≤ f) : 0 ≤ L f := by
    have hn := hLp (-f)
    rw [pneg f (fun x => hf x),map_neg] at hn
    linarith
  refine ⟨PositiveLinearMap.mk₀ L hpos,?_,hLp⟩
  have he := hL (⟨oneX,Submodule.mem_span_singleton_self oneX⟩ : V)
  change L oneX = c
  simpa [l,ev,oneX] using he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureMajorantCost
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual least L² cost of a bounded continuous majorant on a compact
family of finite measures. Feasibility follows from its positive minimum
mass; sublinearity follows from the triangle inequality in L². -/
open Set MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  (σ : Measure Z) [IsFiniteMeasure σ] (S : Set (FiniteMeasure Z))

attribute [local instance] OAI.CircleDomainRigidity.instFactLeENNRealOfNat_solutions
private lemma majorantNorms_bddBelow (u : C_c(S,ℝ)) : BddBelow (majorantNorms σ S u) :=
  ⟨0,fun _ ⟨_,_,he⟩ => he ▸ norm_nonneg _⟩

variable {S}

private lemma majorantNorms_nonempty (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S] (u : C_c(S,ℝ)) :
    (majorantNorms σ S u).Nonempty := by
  obtain ⟨r,_,hr⟩ := exists_compact_measure_constant_majorant hS hne hz u.toContinuousMap
  exact ⟨_,BoundedContinuousFunction.const Z r,hr,rfl⟩

lemma compactMeasureMajorantCost_nonneg (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S] (u : C_c(S,ℝ)) :
    0 ≤ compactMeasureMajorantCost σ S u :=
  le_csInf (majorantNorms_nonempty σ hS hne hz u)
    (fun _ ⟨_,_,he⟩ => he ▸ norm_nonneg _)

lemma le_compactMeasureMajorantCost (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S]
    (u : C_c(S,ℝ)) {a : ℝ}
    (ha : ∀ f : Z →ᵇ ℝ, (∀ v : S, u v ≤ compactMeasureTestOperator S f v) →
      a ≤ ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖) :
    a ≤ compactMeasureMajorantCost σ S u := by
  apply le_csInf (majorantNorms_nonempty σ hS hne hz u)
  rintro _ ⟨f,hf,rfl⟩
  exact ha f hf

lemma compactMeasureMajorantCost_le (u : C_c(S,ℝ)) (f : Z →ᵇ ℝ)
    (hf : ∀ v : S, u v ≤ compactMeasureTestOperator S f v) :
    compactMeasureMajorantCost σ S u ≤ ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ :=
  csInf_le (majorantNorms_bddBelow σ S u) ⟨f,hf,rfl⟩

lemma compactMeasureMajorantCost_nonpos (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S]
    (u : C_c(S,ℝ)) (hu : ∀ v, u v ≤ 0) : compactMeasureMajorantCost σ S u = 0 := by
  apply le_antisymm _ (compactMeasureMajorantCost_nonneg σ hS hne hz u)
  have hb := compactMeasureMajorantCost_le σ u (0 : Z →ᵇ ℝ)
    (fun v => by simpa using hu v)
  simpa using hb

lemma compactMeasureMajorantCost_smul_le (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S]
    (r : ℝ) (hr : 0 < r) (u : C_c(S,ℝ)) :
    compactMeasureMajorantCost σ S (r • u) ≤ r * compactMeasureMajorantCost σ S u := by
  have hdiv : compactMeasureMajorantCost σ S (r • u) / r ≤
      compactMeasureMajorantCost σ S u := by
    apply le_csInf (majorantNorms_nonempty σ hS hne hz u)
    rintro _ ⟨f,hf,rfl⟩
    apply (div_le_iff₀ hr).mpr
    have hb := compactMeasureMajorantCost_le σ (r • u) (r • f) (fun v => by
      simpa using mul_le_mul_of_nonneg_left (hf v) hr.le)
    simpa only [map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hr,smul_eq_mul,mul_comm] using hb
  have hb := (div_le_iff₀ hr).mp hdiv
  simpa only [mul_comm] using hb

lemma compactMeasureMajorantCost_smul (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S]
    (r : ℝ) (hr : 0 < r) (u : C_c(S,ℝ)) :
    compactMeasureMajorantCost σ S (r • u) = r * compactMeasureMajorantCost σ S u := by
  apply le_antisymm (compactMeasureMajorantCost_smul_le σ hS hne hz r hr u)
  have hb := compactMeasureMajorantCost_smul_le σ hS hne hz r⁻¹ (inv_pos.mpr hr) (r • u)
  rw [inv_smul_smul₀ hr.ne'] at hb
  have hc := mul_le_mul_of_nonneg_left hb hr.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] using hc

lemma compactMeasureMajorantCost_add (hS : IsCompact S) (hne : S.Nonempty)
    (hz : (0 : FiniteMeasure Z) ∉ S) [CompactSpace S] (u v : C_c(S,ℝ)) :
    compactMeasureMajorantCost σ S (u+v) ≤
      compactMeasureMajorantCost σ S u + compactMeasureMajorantCost σ S v := by
  have hb (f g : Z →ᵇ ℝ)
      (hf : ∀ a : S, u a ≤ compactMeasureTestOperator S f a)
      (hg : ∀ a : S, v a ≤ compactMeasureTestOperator S g a) :
      compactMeasureMajorantCost σ S (u+v) ≤
        ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ + ‖BoundedContinuousFunction.toLp 2 σ ℝ g‖ := by
    have hfg := compactMeasureMajorantCost_le σ (u+v) (f+g) (fun a => by
      simpa using add_le_add (hf a) (hg a))
    have hn := norm_add_le (BoundedContinuousFunction.toLp 2 σ ℝ f)
      (BoundedContinuousFunction.toLp 2 σ ℝ g)
    exact hfg.trans (by simpa only [map_add] using hn)
  have hu (f : Z →ᵇ ℝ) (hf : ∀ a : S, u a ≤ compactMeasureTestOperator S f a) :
      compactMeasureMajorantCost σ S (u+v) - ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ ≤
        compactMeasureMajorantCost σ S v := by
    apply le_csInf (majorantNorms_nonempty σ hS hne hz v)
    rintro _ ⟨g,hg,rfl⟩
    linarith [hb f g hf hg]
  have hv : compactMeasureMajorantCost σ S (u+v) - compactMeasureMajorantCost σ S v ≤
      compactMeasureMajorantCost σ S u := by
    apply le_csInf (majorantNorms_nonempty σ hS hne hz u)
    rintro _ ⟨f,hf,rfl⟩
    linarith [hu f hf]
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureFamilyModulusBasic
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise measure-family modulus: monotonicity, indexing invariance,
and the zero-modulus family of measures charging a fixed reference-null set.
Extended-valued admissible densities are retained throughout. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

variable {A B Z : Type*} [MeasurableSpace Z]

lemma measureFamilyModulus_le_admissible (σ : Measure Z) (K : A → FiniteMeasure Z)
    {h : Z → ℝ≥0∞} (hh : Measurable h)
    (ha : ∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ∫⁻ z, h z ^ 2 ∂σ :=
  iInf_le_of_le h (iInf_le_of_le hh (iInf_le_of_le ha le_rfl))

lemma exists_admissible_of_modulus_lt (σ : Measure Z) (K : A → FiniteMeasure Z)
    {ε : ℝ≥0∞} (hε : measureFamilyModulus A Z σ K < ε) :
    ∃ h : Z → ℝ≥0∞, Measurable h ∧
      (∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)) ∧ (∫⁻ z, h z ^ 2 ∂σ) < ε := by
  simpa only [measureFamilyModulus,iInf_lt_iff,exists_prop] using hε

lemma measureFamilyModulus_zero_iff (σ : Measure Z) (K : A → FiniteMeasure Z) :
    measureFamilyModulus A Z σ K = 0 ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ h : Z → ℝ≥0∞, Measurable h ∧
        (∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)) ∧ (∫⁻ z, h z ^ 2 ∂σ) < ε := by
  constructor
  · intro hm ε hε
    exact exists_admissible_of_modulus_lt σ K (hm ▸ hε)
  · intro he
    by_contra hm
    obtain ⟨h,hh,ha,hsmall⟩ := he (measureFamilyModulus A Z σ K) (pos_iff_ne_zero.mpr hm)
    exact (not_lt_of_ge (measureFamilyModulus_le_admissible σ K hh ha)) hsmall

lemma measureFamilyModulus_mono_range (σ : Measure Z)
    (K : A → FiniteMeasure Z) (L : B → FiniteMeasure Z) (hKL : range K ⊆ range L) :
    measureFamilyModulus A Z σ K ≤ measureFamilyModulus B Z σ L := by
  apply le_iInf
  intro h
  apply le_iInf
  intro hh
  apply le_iInf
  intro ha
  apply measureFamilyModulus_le_admissible σ K hh
  intro a
  obtain ⟨b,hb⟩ := hKL (mem_range_self a)
  simpa only [hb] using ha b

lemma measureFamilyModulus_eq_of_range_eq (σ : Measure Z)
    (K : A → FiniteMeasure Z) (L : B → FiniteMeasure Z) (hKL : range K = range L) :
    measureFamilyModulus A Z σ K = measureFamilyModulus B Z σ L :=
  le_antisymm (measureFamilyModulus_mono_range σ K L hKL.subset)
    (measureFamilyModulus_mono_range σ L K hKL.symm.subset)

lemma measureFamilyModulus_zero_of_charges_null_set
    (σ : Measure Z) (K : A → FiniteMeasure Z) {N : Set Z}
    (hN : MeasurableSet N) (hσN : σ N = 0) (hK : ∀ a, (K a : Measure Z) N ≠ 0) :
    measureFamilyModulus A Z σ K = 0 := by
  let h : Z → ℝ≥0∞ := N.indicator (fun _ => ∞)
  have hh : Measurable h := measurable_const.indicator hN
  have ha (a : A) : 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z) := by
    rw [lintegral_indicator hN]
    simp [lintegral_const, hK a]
  have he : ∫⁻ z, h z ^ 2 ∂σ = 0 := by
    have hp : (fun z => h z ^ 2) = h := by
      funext z
      by_cases hz : z ∈ N <;> simp [h,hz]
    rw [hp,lintegral_indicator hN]
    simp [lintegral_const,hσN]
  exact le_antisymm (he ▸ measureFamilyModulus_le_admissible σ K hh ha) bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ContinuousMeasureModulus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An admissible bounded continuous real function bounds the pointwise
modulus through its actual L² norm. Absolute values preserve admissibility. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ]

local instance localInst_r26ada9_1 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
lemma boundedContinuous_integral_sq_eq_norm_sq (f : Z →ᵇ ℝ) :
    (∫ z, f z ^ 2 ∂σ) = ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ ^ 2 := by
  let F : Lp ℝ 2 σ := BoundedContinuousFunction.toLp 2 σ ℝ f
  have he : F =ᵐ[σ] f := BoundedContinuousFunction.coeFn_toLp 2 σ ℝ f
  calc
    (∫ z, f z ^ 2 ∂σ) = ∫ z, (F z)^2 ∂σ := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      rw [hz]
    _ = inner ℝ F F := by
      rw [L2.inner_def]
      simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    _ = ‖F‖^2 := real_inner_self_eq_norm_sq _

lemma measureFamilyModulus_le_boundedContinuous_norm {A : Type*}
    (K : A → FiniteMeasure Z) (f : Z →ᵇ ℝ)
    (ha : ∀ a, 1 ≤ ∫ z, f z ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤
      ENNReal.ofReal (‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ ^ 2) := by
  let h : Z → ℝ≥0∞ := fun z => ENNReal.ofReal |f z|
  have hh : Measurable h := by
    simpa only [Real.norm_eq_abs] using f.continuous.norm.measurable.ennreal_ofReal
  have hb (a : A) : 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z) := by
    have hfi : Integrable f (K a : Measure Z) := f.integrable (μ := (K a : Measure Z))
    have hn : Integrable (fun z => |f z|) (K a : Measure Z) := by
      simpa only [Real.norm_eq_abs] using hfi.norm
    have hi : 1 ≤ ∫ z, |f z| ∂(K a : Measure Z) :=
      (ha a).trans (integral_mono hfi hn (fun z => le_abs_self (f z)))
    rw [← ofReal_integral_eq_lintegral_ofReal hn (Eventually.of_forall (fun z => abs_nonneg (f z)))]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hi
  have he : (∫⁻ z, h z ^ 2 ∂σ) =
      ENNReal.ofReal (‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ ^ 2) := by
    have hsq : (fun z => h z^2) = fun z => ENNReal.ofReal (f z^2) := by
      funext z
      simp only [h,← ENNReal.ofReal_pow (abs_nonneg _) 2,sq_abs]
    rw [hsq,← ofReal_integral_eq_lintegral_ofReal]
    · rw [boundedContinuous_integral_sq_eq_norm_sq σ f]
    · convert (f*f).integrable (μ := σ) using 1
      all_goals try with_reducible_and_instances rfl
      ext z
      simp only [pow_two,BoundedContinuousFunction.mul_apply]
    · exact Eventually.of_forall (fun z => sq_nonneg (f z))
  exact he ▸ measureFamilyModulus_le_admissible σ K hh hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureSeparation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive modulus separates the actual compact-family majorant cost
from a constant functional. The separating functional is constructed. -/
open Set Filter MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}

attribute [local instance] OAI.CircleDomainRigidity.instFactLeENNRealOfNat_solutions_1
lemma compactMeasureMajorantCost_const_lower
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (c : ℝ) (hc : 0 < c)
    (hmod : ENNReal.ofReal (c^2) < measureFamilyModulus S Z σ (fun v => v.val))
    (r : ℝ) : r*c ≤ compactMeasureMajorantCost σ S
      (r • (⟨1,HasCompactSupport.of_compactSpace (1 : C(S,ℝ))⟩ : C_c(S,ℝ))) := by
  by_cases hr : r ≤ 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hr hc.le).trans
      (compactMeasureMajorantCost_nonneg σ hS hne hz _)
  have hr : 0 < r := lt_of_not_ge hr
  apply le_compactMeasureMajorantCost σ hS hne hz
  intro f hf
  let g : Z →ᵇ ℝ := r⁻¹ • f
  have ha (v : S) : 1 ≤ ∫ z, g z ∂(v.val : Measure Z) := by
    have hv : r ≤ ∫ z, f z ∂(v.val : Measure Z) := by
      simpa [compactMeasureTestOperator] using hf v
    have hb := mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hr.le)
    simpa [g,BoundedContinuousFunction.smul_apply,integral_const_mul,
      inv_mul_cancel₀ hr.ne'] using hb
  have hb := measureFamilyModulus_le_boundedContinuous_norm σ (fun v : S => v.val) g ha
  have hsq : c^2 < ‖BoundedContinuousFunction.toLp 2 σ ℝ g‖^2 :=
    (ENNReal.ofReal_lt_ofReal_iff'.mp (hmod.trans_le hb)).1
  have hlin : c < ‖BoundedContinuousFunction.toLp 2 σ ℝ g‖ := by
    nlinarith [norm_nonneg (BoundedContinuousFunction.toLp 2 σ ℝ g)]
  have hnorm : ‖BoundedContinuousFunction.toLp 2 σ ℝ g‖ =
      r⁻¹ * ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
    simp only [g,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  rw [hnorm] at hlin
  have hmul := mul_lt_mul_of_pos_left hlin hr
  have hmul' : r*c < ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
    simpa only [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] using hmul
  exact hmul'.le

lemma exists_compact_measure_separating_functional
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (c : ℝ) (hc : 0 < c)
    (hmod : ENNReal.ofReal (c^2) < measureFamilyModulus S Z σ (fun v => v.val)) :
    ∃ Λ : C_c(S,ℝ) →ₚ[ℝ] ℝ,
      Λ ⟨1,HasCompactSupport.of_compactSpace (1 : C(S,ℝ))⟩ = c ∧
      ∀ u, Λ u ≤ compactMeasureMajorantCost σ S u := by
  let : Nonempty S := hne.to_subtype
  apply exists_compact_positive_functional_of_majorant_cost
    (compactMeasureMajorantCost σ S)
  · exact fun r hr u => compactMeasureMajorantCost_smul σ hS hne hz r hr u
  · exact compactMeasureMajorantCost_add σ hS hne hz
  · intro u hu
    exact compactMeasureMajorantCost_nonpos σ hS hne hz (-u) (fun v => by
      simpa using neg_nonpos.mpr (hu v))
  · exact compactMeasureMajorantCost_const_lower σ hS hne hz c hc hmod

lemma exists_compact_measure_test_plan [PolishSpace Z]
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (c : ℝ) (hc : 0 < c)
    (hmod : ENNReal.ofReal (c^2) < measureFamilyModulus S Z σ (fun v => v.val)) :
    ∃ P : ProbabilityMeasure S, ∀ f : Z →ᵇ ℝ,
      c * (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) ≤
        ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
  obtain ⟨Λ,hΛ1,hΛ⟩ := exists_compact_measure_separating_functional σ hS hne hz c hc hmod
  let L : C_c(S,ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ (c⁻¹ • Λ.toLinearMap)
    (fun u hu => mul_nonneg (inv_nonneg.mpr hc.le) (Λ.map_nonneg hu))
  have hL1 : L ⟨1,HasCompactSupport.of_compactSpace (1 : C(S,ℝ))⟩ = 1 := by
    change c⁻¹ * Λ _ = 1
    rw [hΛ1,inv_mul_cancel₀ hc.ne']
  obtain ⟨P,hP⟩ := exists_probability_of_compact_positive_functional_trim
    (compact_finiteMeasure_measurable_le_borel S) L hL1
  refine ⟨P,?_⟩
  intro f
  let u : C_c(S,ℝ) := ⟨compactMeasureTestOperator S f,
    HasCompactSupport.of_compactSpace (compactMeasureTestOperator S f)⟩
  have hi : c * (∫ v : S, u v ∂(P : Measure S)) = Λ u := by
    rw [hP u ((measurable_finiteMeasure_integral f).comp measurable_subtype_coe)]
    change c * (c⁻¹ * Λ u) = Λ u
    rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  have hb := (hΛ u).trans (compactMeasureMajorantCost_le σ u f (fun _ => le_rfl))
  rw [← hi] at hb
  exact hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedContinuousL2Dual
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The L² representation of a functional on bounded continuous tests.
Only the bound through their actual L² image is required. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance localInst_r26ada9_2 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
lemma exists_L2_pairing_of_boundedContinuous_bound
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ]
    (F : (Z →ᵇ ℝ) →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ f, F f ≤ C * ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖) :
    ∃ g : Lp ℝ 2 σ, ‖g‖ ≤ C ∧
      ∀ f : Z →ᵇ ℝ, (∫ z, g z * f z ∂σ) = F f := by
  let Q : (Z →ᵇ ℝ) →ₗ[ℝ] Lp ℝ 2 σ :=
    (BoundedContinuousFunction.toLp 2 σ ℝ).toLinearMap
  have hbound (f : Z →ᵇ ℝ) : ‖F f‖ ≤ C * ‖Q f‖ := by
    rw [Real.norm_eq_abs,abs_le]
    refine ⟨?_,hF f⟩
    have hn := hF (-f)
    change -(C * ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖) ≤ F f
    simpa only [map_neg,norm_neg,neg_neg] using neg_le_neg hn
  have hk : Q.ker ≤ F.ker := by
    intro f hf
    change Q f = 0 at hf
    change F f = 0
    have hn := hbound f
    rw [hf,norm_zero,mul_zero] at hn
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  let L : Q.range →ₗ[ℝ] ℝ :=
    ((Q.ker).liftQ F hk).comp Q.quotKerEquivRange.symm.toLinearMap
  have hL (f : Z →ᵇ ℝ) : L ⟨Q f,LinearMap.mem_range_self Q f⟩ = F f := by
    simp [L]
  have hLb (v : Q.range) : ‖L v‖ ≤ C * ‖v‖ := by
    obtain ⟨f,hf⟩ := v.property
    have hv : v = ⟨Q f,LinearMap.mem_range_self Q f⟩ := Subtype.ext hf.symm
    rw [hv,hL]
    exact hbound f
  let Lc : Q.range →L[ℝ] ℝ := L.mkContinuous C hLb
  obtain ⟨G,hG,hGn⟩ := exists_extension_norm_eq Q.range Lc
  let g : Lp ℝ 2 σ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 σ)).symm G
  refine ⟨g,?_,?_⟩
  · have hnorm : ‖Lc‖ ≤ C := Lc.opNorm_le_bound hC hLb
    calc
      ‖g‖ = ‖G‖ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 σ)).symm.norm_map G
      _ = ‖Lc‖ := hGn
      _ ≤ C := hnorm
  · intro f
    have hq : Q f =ᵐ[σ] f := BoundedContinuousFunction.coeFn_toLp 2 σ ℝ f
    calc
      (∫ z, g z * f z ∂σ) = inner ℝ g (Q f) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hq] with z hz
        simp only [Real.inner_apply,hz]
      _ = G (Q f) := InnerProductSpace.toDual_symm_apply
      _ = Lc ⟨Q f,LinearMap.mem_range_self Q f⟩ := hG ⟨Q f,LinearMap.mem_range_self Q f⟩
      _ = F f := hL f

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CompactMeasureL2Plan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact-family plan has an actual L² representing function on
bounded continuous tests. Positivity and Borel-set barycenter identities
are established separately from this linear representation step. -/
open Set Filter MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance instFactLeENNRealOfNat_solutions_2 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma exists_compact_measure_L2_test_plan
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (c : ℝ) (hc : 0 < c)
    (hmod : ENNReal.ofReal (c^2) < measureFamilyModulus S Z σ (fun v => v.val)) :
    ∃ (P : ProbabilityMeasure S) (g : Lp ℝ 2 σ), ‖g‖ ≤ c⁻¹ ∧
      ∀ f : Z →ᵇ ℝ,
        (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) =
          ∫ z, g z * f z ∂σ := by
  obtain ⟨P,hP⟩ := exists_compact_measure_test_plan σ hS hne hz c hc hmod
  have hI (f : Z →ᵇ ℝ) : Integrable
      (fun v : S => compactMeasureTestOperator S f v) (P : Measure S) := by
    apply (integrable_const ‖compactMeasureTestOperator S f‖).mono'
      ((measurable_finiteMeasure_integral f).comp measurable_subtype_coe).aestronglyMeasurable
    exact Eventually.of_forall (fun v => (compactMeasureTestOperator S f).norm_coe_le_norm v)
  let F : (Z →ᵇ ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ v : S, compactMeasureTestOperator S f v ∂(P : Measure S)
      map_add' := by
        intro f g
        simp only [map_add,ContinuousMap.add_apply]
        exact integral_add (hI f) (hI g)
      map_smul' := by
        intro r f
        simp only [map_smul,ContinuousMap.smul_apply,smul_eq_mul]
        exact integral_const_mul r _ }
  have hF (f : Z →ᵇ ℝ) : F f ≤ c⁻¹ * ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
    have hb := mul_le_mul_of_nonneg_left (hP f) (inv_nonneg.mpr hc.le)
    change (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) ≤ _
    simpa only [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] using hb
  obtain ⟨g,hg,hrep⟩ := exists_L2_pairing_of_boundedContinuous_bound σ F
    (inv_nonneg.mpr hc.le) hF
  exact ⟨P,g,hg,fun f => (hrep f).symm⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2PositiveTests
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of an L² function is detected by nonnegative bounded continuous
functions. The extension to L² uses continuity of the actual positive part. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance localInst_r26ada9_3 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
lemma boundedContinuous_toLp_posPart
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] (f : Z →ᵇ ℝ) :
    BoundedContinuousFunction.toLp 2 σ ℝ f⁺ =
      Lp.posPart (BoundedContinuousFunction.toLp 2 σ ℝ f) := by
  apply Lp.ext
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 σ ℝ f⁺,
    BoundedContinuousFunction.coeFn_toLp 2 σ ℝ f,
    Lp.coeFn_posPart (BoundedContinuousFunction.toLp 2 σ ℝ f)] with z hp hf hq
  rw [hp,hq,hf]
  rfl

lemma L2_nonneg_of_boundedContinuous_tests
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    [NormalSpace Z] [SecondCountableTopology Z]
    (σ : Measure Z) [IsFiniteMeasure σ] [σ.WeaklyRegular]
    (g : Lp ℝ 2 σ)
    (hg : ∀ f : Z →ᵇ ℝ, (∀ z, 0 ≤ f z) → 0 ≤ ∫ z, g z * f z ∂σ) :
    ∀ᵐ z ∂σ, 0 ≤ g z := by
  have hpos (v : Lp ℝ 2 σ) : 0 ≤ inner ℝ g (Lp.posPart v) := by
    refine (BoundedContinuousFunction.toLp_denseRange ℝ σ ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).induction_on v ?_ ?_
    · exact isClosed_le continuous_const (continuous_const.inner Lp.continuous_posPart)
    · intro f
      rw [← boundedContinuous_toLp_posPart σ f, L2.inner_def]
      have heq : (∫ z, inner ℝ (g z)
          (BoundedContinuousFunction.toLp 2 σ ℝ f⁺ z) ∂σ) =
          ∫ z, g z * (f⁺) z ∂σ := by
        apply integral_congr_ae
        filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 σ ℝ f⁺] with z hz
        simp only [hz,Real.inner_apply]
      rw [heq]
      apply hg
      intro z
      change 0 ≤ max (f z) 0
      exact le_max_right _ _
  let n : Lp ℝ 2 σ := Lp.negPart g
  have hn : inner ℝ g n = - inner ℝ n n := by
    rw [L2.inner_def,L2.inner_def,← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_negPart_eq_max g] with z hz
    change n z = max (-g z) 0 at hz
    simp only [Real.inner_apply]
    rcases le_total 0 (g z) with h | h
    · rw [max_eq_right (neg_nonpos.mpr h)] at hz
      rw [hz]
      ring
    · rw [max_eq_left (neg_nonneg.mpr h)] at hz
      rw [hz]
      ring
  have hz : n = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hp : 0 ≤ inner ℝ g n := hpos (-g)
    have hnn : 0 ≤ inner ℝ n n := real_inner_self_nonneg
    linarith
  filter_upwards [Lp.coeFn_negPart_eq_max g, Lp.coeFn_zero ℝ 2 σ] with z hn hzero
  change n z = max (-g z) 0 at hn
  rw [hz,hzero] at hn
  have h := le_max_left (-g z) 0
  rw [← hn] at h
  change -g z ≤ 0 at h
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compact-family plan has the actual nonnegative Borel L² density
of its barycenter. The identity is proved on Borel sets, not just tests. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

local instance instFactLeENNRealOfNat_solutions_3 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma L2_ofReal_energy_eq
    {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)
    (g : Lp ℝ 2 σ) (hg : ∀ᵐ z ∂σ, 0 ≤ g z) :
    (∫⁻ z, (ENNReal.ofReal (g z))^2 ∂σ) = ENNReal.ofReal (‖g‖^2) := by
  calc
    (∫⁻ z, (ENNReal.ofReal (g z))^2 ∂σ) =
        ∫⁻ z, ENNReal.ofReal ((g z)^2) ∂σ := by
      apply lintegral_congr_ae
      filter_upwards [hg] with z hz
      exact (ENNReal.ofReal_pow hz 2).symm
    _ = ENNReal.ofReal (∫ z, (g z)^2 ∂σ) :=
      (ofReal_integral_eq_lintegral_ofReal (Lp.memLp g).integrable_sq
        (Eventually.of_forall (fun z => sq_nonneg (g z)))).symm
    _ = ENNReal.ofReal (‖g‖^2) := by
      congr 1
      rw [← real_inner_self_eq_norm_sq g, L2.inner_def]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by simp [pow_two])

lemma compactMeasureBarycenter_eq_withDensity
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) [CompactSpace S] (P : ProbabilityMeasure S)
    (g : Lp ℝ 2 σ)
    (hrep : ∀ f : Z →ᵇ ℝ,
      (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) =
        ∫ z, g z * f z ∂σ) :
    (∀ᵐ z ∂σ, 0 ≤ g z) ∧
      compactMeasureBarycenter P = σ.withDensity (fun z => ENNReal.ofReal (g z)) := by
  have hg : ∀ᵐ z ∂σ, 0 ≤ g z := by
    apply L2_nonneg_of_boundedContinuous_tests σ g
    intro f hf
    rw [← hrep f]
    exact integral_nonneg (fun v => integral_nonneg hf)
  refine ⟨hg,?_⟩
  let : IsFiniteMeasure (compactMeasureBarycenter P) := compactMeasureBarycenter_finite hS P
  have hgi : Integrable g σ := (Lp.memLp g).integrable (by norm_num)
  let : IsFiniteMeasure (σ.withDensity (fun z => ENNReal.ofReal (g z))) :=
    isFiniteMeasure_withDensity ((lintegral_ofReal_ne_top_iff_integrable
      (Lp.aestronglyMeasurable g) hg).mpr hgi)
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  apply (ENNReal.toReal_eq_toReal_iff'
    (BoundedContinuousFunction.lintegral_lt_top_of_nnreal (compactMeasureBarycenter P) f).ne
    (BoundedContinuousFunction.lintegral_lt_top_of_nnreal
      (σ.withDensity (fun z => ENNReal.ofReal (g z))) f).ne).mp
  rw [BoundedContinuousFunction.toReal_lintegral_coe_eq_integral,
    BoundedContinuousFunction.toReal_lintegral_coe_eq_integral]
  let fR : Z →ᵇ ℝ := ⟨⟨fun z => (f z : ℝ), NNReal.continuous_coe.comp f.continuous⟩,
    f.map_bounded'⟩
  change (∫ z, fR z ∂compactMeasureBarycenter P) =
    ∫ z, fR z ∂σ.withDensity (fun z => ENNReal.ofReal (g z))
  rw [compactMeasureBarycenter_integral_nonneg P fR (fun z => (f z).coe_nonneg), hrep fR,
    integral_withDensity_eq_integral_toReal_smul (Lp.stronglyMeasurable g).measurable.ennreal_ofReal
      (Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hg] with z hz
  simp only [ENNReal.toReal_ofReal hz,smul_eq_mul]

lemma exists_compact_measure_density_plan
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (c : ℝ) (hc : 0 < c)
    (hmod : ENNReal.ofReal (c^2) < measureFamilyModulus S Z σ (fun v => v.val)) :
    ∃ (P : ProbabilityMeasure S) (q : Z → ℝ≥0∞), Measurable q ∧
      compactMeasureBarycenter P = σ.withDensity q ∧
      (∫⁻ z, q z^2 ∂σ) ≤ ENNReal.ofReal (c⁻¹^2) := by
  obtain ⟨P,g,hgn,hrep⟩ := exists_compact_measure_L2_test_plan σ hS hne hz c hc hmod
  obtain ⟨hg,hbar⟩ := compactMeasureBarycenter_eq_withDensity σ hS P g hrep
  refine ⟨P,fun z => ENNReal.ofReal (g z), (Lp.stronglyMeasurable g).measurable.ennreal_ofReal,
    hbar,?_⟩
  rw [L2_ofReal_energy_eq σ g hg]
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg g) hgn 2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureFamilyExceptional
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fuglede's elementary exceptional-family estimate: an L² reference
density has infinite integral only along a family of zero pointwise modulus. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

variable {A Z : Type*} [MeasurableSpace Z]

lemma measureFamilyModulus_zero_of_infinite_integral
    (σ : Measure Z) (K : A → FiniteMeasure Z) {g : Z → ℝ≥0∞}
    (hg : Measurable g) (hE : (∫⁻ z, g z ^ 2 ∂σ) ≠ ∞)
    (hK : ∀ a, ∫⁻ z, g z ∂(K a : Measure Z) = ∞) :
    measureFamilyModulus A Z σ K = 0 := by
  by_contra hm
  obtain ⟨δ,hδ,hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hE hm
  let c : ℝ≥0 := min δ 1
  have hc : 0 < c := lt_min hδ zero_lt_one
  have hc2 : c ^ 2 ≤ δ := by
    have hc1 : c ≤ 1 := min_le_right _ _
    have hcδ : c ≤ δ := min_le_left _ _
    calc
      c ^ 2 = c*c := pow_two c
      _ ≤ c := mul_le_of_le_one_right (show (0 : ℝ≥0) ≤ c from zero_le) hc1
      _ ≤ δ := hcδ
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  let h : Z → ℝ≥0∞ := fun z => c * g z
  have hh : Measurable h := measurable_const.mul hg
  have ha (a : A) : 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z) := by
    rw [lintegral_const_mul _ hg,hK a,ENNReal.mul_top hc0]
    exact le_top
  have he : ∫⁻ z, h z ^ 2 ∂σ = (c : ℝ≥0∞)^2 * ∫⁻ z, g z ^ 2 ∂σ := by
    simp only [h,mul_pow]
    exact lintegral_const_mul _ (hg.pow_const 2)
  have hb := measureFamilyModulus_le_admissible σ K hh ha
  rw [he] at hb
  have hc2' : (c : ℝ≥0∞)^2 ≤ δ := by exact_mod_cast hc2
  exact (not_lt_of_ge (hb.trans (mul_le_mul_left hc2' _))) hsmall

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureFamilyNullUnions
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable unions of pointwise zero-modulus families have zero modulus.
The admissible density is the square root of the sum of the squared
individual densities, so the argument keeps every family member. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_zero_of_countable_cover
    {A Z ι : Type*} [MeasurableSpace Z] [Countable ι]
    (σ : Measure Z) (K : A → FiniteMeasure Z) (S : ι → Set A)
    (hcover : ∀ a, ∃ i, a ∈ S i)
    (hz : ∀ i, measureFamilyModulus (S i) Z σ (fun a => K a.val) = 0) :
    measureFamilyModulus A Z σ K = 0 := by
  classical
  apply (measureFamilyModulus_zero_iff σ K).mpr
  intro ε hε
  obtain ⟨b,hb,hbsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  have hex (i : ι) := (measureFamilyModulus_zero_iff σ (fun a : S i => K a.val)).mp
    (hz i) (b i) (hb i)
  choose g hgm hga hge using hex
  let h : Z → ℝ≥0∞ := fun z => (∑' i, g i z ^ 2) ^ (1/2 : ℝ)
  have hh : Measurable h := (Measurable.tsum (fun i => (hgm i).pow_const 2)).pow_const (1/2 : ℝ)
  have hsq (z : Z) : h z ^ 2 = ∑' i, g i z ^ 2 := by
    dsimp only [h]
    rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
  have hdom (i : ι) (z : Z) : g i z ≤ h z := by
    have he : (g i z ^ 2) ^ (1/2 : ℝ) = g i z := by
      rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
      norm_num
    rw [← he]
    exact ENNReal.rpow_le_rpow (ENNReal.le_tsum (f := fun j => g j z ^ 2) i) (by norm_num)
  refine ⟨h,hh,?_,?_⟩
  · intro a
    obtain ⟨i,hai⟩ := hcover a
    exact (hga i ⟨a,hai⟩).trans (lintegral_mono (hdom i))
  · simp_rw [hsq]
    rw [lintegral_tsum (fun i => ((hgm i).pow_const 2).aemeasurable)]
    exact (ENNReal.tsum_le_tsum (fun i => (hge i).le)).trans_lt hbsum

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureFamilyNullRemoval
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing a pointwise zero-modulus family does not alter modulus.
Minkowski's inequality controls the arbitrarily cheap admissible repair. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_le_admissible_off_null_family
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (S : Set A) (hS : measureFamilyModulus S Z σ (fun a => K a.val) = 0)
    {h : Z → ℝ≥0∞} (hh : Measurable h)
    (ha : ∀ a, a ∉ S → 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ∫⁻ z, h z ^ 2 ∂σ := by
  have hroot : (measureFamilyModulus A Z σ K) ^ (1/2 : ℝ) ≤
      (∫⁻ z, h z ^ 2 ∂σ) ^ (1/2 : ℝ) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ _
    have hδ2 : (0 : ℝ≥0∞) < (δ : ℝ≥0∞)^2 := by positivity
    obtain ⟨g,hg,hga,hge⟩ := (measureFamilyModulus_zero_iff σ
      (fun a : S => K a.val)).mp hS _ hδ2
    have hsum : ∀ a, 1 ≤ ∫⁻ z, h z + g z ∂(K a : Measure Z) := by
      intro a
      by_cases has : a ∈ S
      · exact (hga ⟨a,has⟩).trans (lintegral_mono (fun _ => le_add_self))
      · exact (ha a has).trans (lintegral_mono (fun _ => le_self_add))
    have hnorm := ENNReal.lintegral_Lp_add_le (μ := σ) hh.aemeasurable hg.aemeasurable
      (p := (2 : ℝ)) (by norm_num)
    have hgroot : (∫⁻ z, g z ^ 2 ∂σ) ^ (1/2 : ℝ) ≤ δ := by
      have hle := ENNReal.rpow_le_rpow hge.le (by norm_num : (0 : ℝ) ≤ 1/2)
      simpa only [← ENNReal.rpow_two,← ENNReal.rpow_mul,
        show (2 : ℝ)*(1/2)=1 by norm_num,ENNReal.rpow_one] using hle
    calc
      (measureFamilyModulus A Z σ K) ^ (1/2 : ℝ) ≤
          (∫⁻ z, (h z+g z)^2 ∂σ) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow (measureFamilyModulus_le_admissible σ K (hh.add hg) hsum)
          (by norm_num)
      _ ≤ (∫⁻ z, h z ^ 2 ∂σ) ^ (1/2 : ℝ) +
          (∫⁻ z, g z ^ 2 ∂σ) ^ (1/2 : ℝ) := by
        simpa only [Pi.add_apply,ENNReal.rpow_two] using hnorm
      _ ≤ (∫⁻ z, h z ^ 2 ∂σ) ^ (1/2 : ℝ) + δ := add_le_add_right hgroot _
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 1/2)).mp hroot

lemma measureFamilyModulus_remove_null_family
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (S : Set A) (hS : measureFamilyModulus S Z σ (fun a => K a.val) = 0) :
    measureFamilyModulus A Z σ K =
      measureFamilyModulus (Sᶜ : Set A) Z σ (fun a => K a.val) := by
  apply le_antisymm
  · apply le_iInf
    intro h
    apply le_iInf
    intro hh
    apply le_iInf
    intro ha
    exact measureFamilyModulus_le_admissible_off_null_family σ K S hS hh
      (fun a has => ha ⟨a,has⟩)
  · apply measureFamilyModulus_mono_range
    rintro v ⟨a,rfl⟩
    exact mem_range_self a.val

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_CoareaInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar coarea and its finite-energy consequences

The planar scalar coarea identities specialize
Federer, *Geometric Measure Theory*, Springer (1969), §3.2.11 (coarea)
and §3.2.12 (weighted coarea),
DOI: 10.1007/978-3-642-62010-2. For a `C¹` real function on an open
subset of the Euclidean plane, the integral of the one-dimensional
Hausdorff measures of its fibers equals the integral of the norm of its
differential. The locally Lipschitz version follows from the stated
Lipschitz coarea theorem by a countable relatively compact covering.

`PlanarScalarCoarea` and `WeightedPlanarScalarCoarea` express these
specializations as propositions. They require neither finite energy nor
topological conclusions. The length function need only be Lebesgue
measurable; Borel measurability is unnecessary.

Finite area and finite squared differential imply finite integrated
length, and integer periodization
gives finite physical length for almost every circle-valued level.
-/

open Set MeasureTheory Metric
open scoped ENNReal

namespace CircleDomainRigidity

/-- The scalar fibers are measurable even though the function is only
assumed continuous on its open domain. -/
theorem measurableSet_scalar_level {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (t : ℝ) :
    MeasurableSet (D ∩ {z | f z = t}) := by
  classical
  have hm : Measurable (D.piecewise f (fun _ => 0)) :=
    hf.measurable_piecewise continuousOn_const hD.measurableSet
  have heq : D ∩ {z | f z = t} =
      D ∩ (D.piecewise f (fun _ => 0)) ⁻¹' {t} := by
    ext z
    by_cases hz : z ∈ D <;> simp [hz]
  rw [heq]
  exact hD.measurableSet.inter (hm (measurableSet_singleton t))

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2Series
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise sum of the cutoff differential norms is itself in L2,
with the sum of their L2 norms as a bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem l2_series_of_summable_norms {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (g : ℕ → X → ℝ)
    (hg : ∀ n, MemLp (g n) 2 μ)
    (hs : Summable (fun n => (eLpNorm (g n) 2 μ).toReal)) :
    MemLp (fun z => ∑' n, g n z) 2 μ ∧
      (eLpNorm (fun z => ∑' n, g n z) 2 μ).toReal ≤
        ∑' n, (eLpNorm (g n) 2 μ).toReal := by
  let F : ℕ → Lp ℝ 2 μ := fun n => (hg n).toLp (g n)
  have hnorm : Summable (fun n => ‖F n‖) := by
    simpa only [F, Lp.norm_toLp] using hs
  have hfinite : (∑' n, ‖F n‖ₑ) ≠ (⊤ : ℝ≥0∞) := by
    have hh := hs.tsum_ofReal_lt_top
    have he (n : ℕ) : ENNReal.ofReal (eLpNorm (g n) 2 μ).toReal = eLpNorm (g n) 2 μ :=
      ENNReal.ofReal_toReal (hg n).eLpNorm_ne_top
    simp_rw [he] at hh
    simpa only [F, Lp.enorm_toLp] using hh.ne
  have hvalues : ∀ᵐ z ∂μ, ∀ n, F n z = g n z :=
    ae_all_iff.mpr (fun n => (hg n).coeFn_toLp)
  have hae : (⇑(∑' n, F n) : X → ℝ) =ᵐ[μ] (fun z => ∑' n, g n z) := by
    filter_upwards [Lp.coeFn_tsum hfinite, hvalues] with z hz hv
    rw [hz]
    exact tsum_congr hv
  refine ⟨(Lp.memLp (∑' n, F n)).ae_eq hae, ?_⟩
  rw [← eLpNorm_congr_ae hae, ← Lp.norm_def]
  simpa only [F, Lp.norm_toLp] using norm_tsum_le_tsum_norm hnorm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2DominatingSubsequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L² convergence admits a cofinal subsequence with one L²
pointwise majorant. This will pass smooth line payments to a continuous
Sobolev limit without assuming an ACL representative theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_L2_dominating_subsequence {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 2 μ) atTop (𝓝 0)) :
    ∃ (σ : ℕ → ℕ) (P : X → ℝ), Tendsto σ atTop atTop ∧ Measurable P ∧
      (∀ x, 0 ≤ P x) ∧ MemLp P 2 μ ∧ (∀ᵐ x ∂μ, ∀ n, |f (σ n) x| ≤ P x) := by
  let δ := fun n : ℕ => (1/2:ℝ)^n
  have hδ (n : ℕ) : 0 < δ n := pow_pos (by norm_num) n
  have hδs : Summable δ := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun n => (eLpNorm (fun x => f n x-g x) 2 μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp hlim
  have hchoose (n : ℕ) : ∃ k, n ≤ k ∧ (eLpNorm (fun x => f k x-g x) 2 μ).toReal ≤ δ n := by
    obtain ⟨k,hk,hke⟩ := ((eventually_ge_atTop n).and (ht.eventually (gt_mem_nhds (hδ n)))).exists
    exact ⟨k,hk,hke.le⟩
  choose σ hσ hb using hchoose
  have hσt : Tendsto σ atTop atTop := tendsto_atTop_mono hσ tendsto_id
  let e := fun n x => f (σ n) x-g x
  have he (n : ℕ) : MemLp (e n) 2 μ := (hf _).sub hg
  have hes : Summable (fun n => (eLpNorm (e n) 2 μ).toReal) :=
    hδs.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) hb
  have hef : (∑' n, eLpNorm (e n) 2 μ) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_)) hδs.tsum_ofReal_lt_top
    rw [← ENNReal.ofReal_toReal (he n).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hser := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞) ≤ 2) (fun n => (he n).1) hef
  have hn : Summable (fun n => (eLpNorm (fun x => ‖e n x‖) 2 μ).toReal) := by
    simpa only [eLpNorm_norm _] using hes
  have hsum := (l2_series_of_summable_norms (fun n x => ‖e n x‖) (fun n => (he n).norm) hn).1
  let Q := fun x => ‖g x‖+∑' n, ‖e n x‖
  have hQ : MemLp Q 2 μ := hg.norm.add hsum
  have hQ0 (x : X) : 0 ≤ Q x := add_nonneg (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _))
  let P := fun x => max (hQ.aestronglyMeasurable.mk Q x) 0
  have hPQ : P =ᵐ[μ] Q := by
    filter_upwards [hQ.aestronglyMeasurable.ae_eq_mk] with x hx
    change max (hQ.aestronglyMeasurable.mk Q x) 0 = Q x
    rw [← hx,max_eq_left (hQ0 x)]
  refine ⟨σ,P,hσt,hQ.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const,
    (fun _ => le_max_right _ _),hQ.ae_eq hPQ.symm,?_⟩
  filter_upwards [hPQ,hser] with x hx hxs
  intro n
  rw [hx]
  have heq : f (σ n) x = g x+e n x := by dsimp only [e] <;> ring
  calc
    _ = ‖f (σ n) x‖ := Real.norm_eq_abs _ |>.symm
    _ ≤ ‖g x‖+‖e n x‖ := by rw [heq]; exact norm_add_le _ _
    _ ≤ Q x := by
      dsimp only [Q]
      exact add_le_add_right (hxs.le_tsum n (fun _ _ => norm_nonneg _)) _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_L2DominatedAeSubsequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong L² convergence has a cofinal subsequence with both a common
L² majorant and pointwise almost-everywhere convergence. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_L2_dominated_ae_subsequence {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 2 μ) atTop (𝓝 0)) :
    ∃ (ρ : ℕ → ℕ) (P : X → ℝ), Tendsto ρ atTop atTop ∧ Measurable P ∧
      (∀ x, 0 ≤ P x) ∧ MemLp P 2 μ ∧
      (∀ᵐ x ∂μ, (∀ n, |f (ρ n) x| ≤ P x) ∧
        Tendsto (fun n => f (ρ n) x) atTop (𝓝 (g x))) := by
  obtain ⟨σ, P, hσ, hP, hP0, hPL, hdom⟩ := exists_L2_dominating_subsequence hf hg hlim
  have hmeasure : TendstoInMeasure μ (fun n => f (σ n)) atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (hf := fun n => (hf (σ n)).aestronglyMeasurable) (hg := hg.aestronglyMeasurable) (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hlim.comp hσ)
  obtain ⟨τ, hτ, hconv⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨σ ∘ τ, P, hσ.comp hτ.tendsto_atTop, hP, hP0, hPL, ?_⟩
  filter_upwards [hdom, hconv] with x hxd hxc
  exact ⟨fun n => hxd (τ n), hxc⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureFamilyDominatedLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise admissibility passes through an almost-everywhere dominated
limit after removing, and then repairing, a zero-modulus family. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_zero_of_cover_two
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (S T : Set A) (hcover : ∀ a, a ∈ S ∨ a ∈ T)
    (hS : measureFamilyModulus S Z σ (fun a => K a.val) = 0)
    (hT : measureFamilyModulus T Z σ (fun a => K a.val) = 0) :
    measureFamilyModulus A Z σ K = 0 := by
  apply measureFamilyModulus_zero_of_countable_cover σ K
    (fun b : Bool => if b then T else S)
  · intro a
    rcases hcover a with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  · intro b
    cases b
    · exact hS
    · exact hT

lemma measureFamilyModulus_le_of_dominated_limit
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (f : ℕ → Z → ℝ) (g P : Z → ℝ)
    (hf : ∀ n, Measurable (f n)) (hf0 : ∀ n z, 0 ≤ f n z)
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hP : Measurable P) (hP0 : ∀ z, 0 ≤ P z) (hPL : MemLp P 2 σ)
    (hlim : ∀ᵐ z ∂σ, (∀ n, |f n z| ≤ P z) ∧
      Tendsto (fun n => f n z) atTop (𝓝 (g z)))
    (ha : ∀ a, ∀ᶠ n in atTop, 1 ≤ ∫⁻ z, ENNReal.ofReal (f n z) ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ∫⁻ z, ENNReal.ofReal (g z)^2 ∂σ := by
  classical
  obtain ⟨N,hbad,hNm,hN0⟩ := exists_measurable_superset_of_null
    (show σ {z | ¬ ((∀ n, |f n z| ≤ P z) ∧
      Tendsto (fun n => f n z) atTop (𝓝 (g z)))} = 0 from hlim)
  let S : Set A := {a | (K a : Measure Z) N ≠ 0 ∨
    (∫⁻ z, ENNReal.ofReal (P z) ∂(K a : Measure Z)) = ∞}
  have hS : measureFamilyModulus S Z σ (fun a => K a.val) = 0 := by
    apply measureFamilyModulus_zero_of_cover_two σ (fun a : S => K a.val)
      {a | (K a.val : Measure Z) N ≠ 0}
      {a | (∫⁻ z, ENNReal.ofReal (P z) ∂(K a.val : Measure Z)) = ∞}
    · intro a
      exact a.property
    · exact measureFamilyModulus_zero_of_charges_null_set σ _ hNm hN0
        (fun a => a.property)
    · apply measureFamilyModulus_zero_of_infinite_integral σ _ hP.ennreal_ofReal
      · have he : (∫⁻ z, ENNReal.ofReal (P z)^2 ∂σ) =
            ENNReal.ofReal (∫ z, P z^2 ∂σ) := by
          rw [ofReal_integral_eq_lintegral_ofReal hPL.integrable_sq
            (Eventually.of_forall (fun z => sq_nonneg (P z)))]
          apply lintegral_congr
          intro z
          exact (ENNReal.ofReal_pow (hP0 z) 2).symm
        rw [he]
        exact ENNReal.ofReal_ne_top
      · exact fun a => a.property
  apply measureFamilyModulus_le_admissible_off_null_family σ K S hS hg.ennreal_ofReal
  intro a has
  have hgood : (K a : Measure Z) N = 0 ∧
      (∫⁻ z, ENNReal.ofReal (P z) ∂(K a : Measure Z)) ≠ ∞ := by
    simpa only [S,mem_ofPred_eq,not_or,not_not] using has
  have hνgood : ∀ᵐ z ∂(K a : Measure Z), (∀ n, |f n z| ≤ P z) ∧
      Tendsto (fun n => f n z) atTop (𝓝 (g z)) := by
    have hN : ∀ᵐ z ∂(K a : Measure Z), z ∉ N :=
      (by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hgood.1)
    filter_upwards [hN] with z hz
    exact of_not_not (fun hn => hz (hbad hn))
  have hPi : Integrable P (K a : Measure Z) :=
    (lintegral_ofReal_ne_top_iff_integrable hP.aestronglyMeasurable
      (Eventually.of_forall hP0)).mp hgood.2
  have hfi (n : ℕ) : Integrable (f n) (K a : Measure Z) := by
    apply hPi.mono' (hf n).aestronglyMeasurable
    filter_upwards [hνgood] with z hz
    simpa only [Real.norm_eq_abs] using hz.1 n
  have hconv : Tendsto (fun n => ∫ z, f n z ∂(K a : Measure Z)) atTop
      (𝓝 (∫ z, g z ∂(K a : Measure Z))) := by
    apply tendsto_integral_of_dominated_convergence P (fun n => (hf n).aestronglyMeasurable)
      hPi
    · intro n
      filter_upwards [hνgood] with z hz
      simpa only [Real.norm_eq_abs] using hz.1 n
    · exact hνgood.mono (fun z hz => hz.2)
  have hgi : Integrable g (K a : Measure Z) := by
    apply hPi.mono' hg.aestronglyMeasurable
    filter_upwards [hνgood] with z hz
    rw [Real.norm_eq_abs]
    exact le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hz.2)
      (Eventually.of_forall (fun n => hz.1 n))
  have hlower : (1 : ℝ) ≤ ∫ z, g z ∂(K a : Measure Z) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hconv
    filter_upwards [ha a] with n hn
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n)
      (Eventually.of_forall (hf0 n))] at hn
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
    simpa only [ENNReal.toReal_one,ENNReal.toReal_ofReal (integral_nonneg (hf0 n))] using h
  rw [← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hg0)]
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hlower


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureFamilySignedLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The L² limit representative may have arbitrary values on a reference
null set. Taking its positive part preserves all limiting admissibility. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance localInst_r26ada9_4 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
lemma measureFamilyModulus_le_of_signed_L2_limit
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (f : ℕ → Z → ℝ) (g : Z → ℝ)
    (hf : ∀ n, Measurable (f n)) (hf0 : ∀ n z, 0 ≤ f n z)
    (hfL : ∀ n, MemLp (f n) 2 σ) (hg : Measurable g) (hgL : MemLp g 2 σ)
    (hlim : Tendsto (fun n => eLpNorm (fun z => f n z-g z) 2 σ) atTop (𝓝 0))
    (ha : ∀ a, ∀ᶠ n in atTop, 1 ≤ ∫⁻ z, ENNReal.ofReal (f n z) ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ENNReal.ofReal (‖hgL.toLp g‖^2) := by
  obtain ⟨ρ,P,hρ,hP,hP0,hPL,hpoint⟩ := exists_L2_dominated_ae_subsequence hfL hgL hlim
  have hp : ∀ᵐ z ∂σ, (∀ n, |f (ρ n) z| ≤ P z) ∧
      Tendsto (fun n => f (ρ n) z) atTop (𝓝 (max (g z) 0)) := by
    filter_upwards [hpoint] with z hz
    refine ⟨hz.1,?_⟩
    have h := hz.2.max (tendsto_const_nhds (x := (0 : ℝ)))
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact (max_eq_left (hf0 (ρ n) z)).symm
  have hmod := measureFamilyModulus_le_of_dominated_limit σ K
    (fun n => f (ρ n)) (fun z => max (g z) 0) P
    (fun n => hf (ρ n)) (fun n => hf0 (ρ n)) (hg.max measurable_const)
    (fun z => le_max_right _ _) hP hP0 hPL hp (fun a => hρ.eventually (ha a))
  refine hmod.trans ?_
  have heq : (∫⁻ z, ENNReal.ofReal (g z^2) ∂σ) = ENNReal.ofReal (‖hgL.toLp g‖^2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hgL.integrable_sq
      (Eventually.of_forall (fun z => sq_nonneg (g z)))]
    congr 1
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hgL.coeFn_toLp] with z hz
    simp only [hz,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  rw [← heq]
  apply lintegral_mono
  intro z
  change ENNReal.ofReal (max (g z) 0)^2 ≤ ENNReal.ofReal (g z^2)
  by_cases hz : 0 ≤ g z
  · rw [max_eq_left hz,ENNReal.ofReal_pow hz]
  · rw [max_eq_right (le_of_not_ge hz)]
    simp only [ENNReal.ofReal_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact bot_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AdmissibleL2Convex
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity of the actual L² classes with a nonnegative Borel,
pointwise-admissible representative for a specified family. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma admissibleL2Classes_convex {A Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) : Convex ℝ (admissibleL2Classes σ K) := by
  intro v hv w hw a b ha hb hab
  obtain ⟨f,hf,hfm,hf0,hfa,rfl⟩ := hv
  obtain ⟨g,hg,hgm,hg0,hga,rfl⟩ := hw
  let h : Z → ℝ := fun z => a*f z+b*g z
  have hL : MemLp h 2 σ := (hf.const_mul a).add (hg.const_mul b)
  refine ⟨h,hL,measurable_const.mul hfm |>.add (measurable_const.mul hgm),
    fun z => add_nonneg (mul_nonneg ha (hf0 z)) (mul_nonneg hb (hg0 z)),?_,?_⟩
  · intro i
    have he : (fun z => ENNReal.ofReal (h z)) = fun z =>
        ENNReal.ofReal a * ENNReal.ofReal (f z) +
          ENNReal.ofReal b * ENNReal.ofReal (g z) := by
      funext z
      dsimp only [h]
      rw [ENNReal.ofReal_add (mul_nonneg ha (hf0 z)) (mul_nonneg hb (hg0 z)),
        ENNReal.ofReal_mul ha,ENNReal.ofReal_mul hb]
    rw [he]
    have hadd := lintegral_add_left (μ := (K i : Measure Z))
      (f := fun z => ENNReal.ofReal a * ENNReal.ofReal (f z))
      (g := fun z => ENNReal.ofReal b * ENNReal.ofReal (g z))
      (measurable_const.mul hfm.ennreal_ofReal)
    rw [hadd,lintegral_const_mul _ hfm.ennreal_ofReal,
      lintegral_const_mul _ hgm.ennreal_ofReal]
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal a + ENNReal.ofReal b := by
        rw [← ENNReal.ofReal_add ha hb,hab,ENNReal.ofReal_one]
      _ ≤ ENNReal.ofReal a * ∫⁻ z, ENNReal.ofReal (f z) ∂(K i : Measure Z) +
          ENNReal.ofReal b * ∫⁻ z, ENNReal.ofReal (g z) ∂(K i : Measure Z) := by
        simpa only [mul_one] using add_le_add
          (mul_le_mul_right (hfa i) (ENNReal.ofReal a))
          (mul_le_mul_right (hga i) (ENNReal.ofReal b))
  · apply Lp.ext
    filter_upwards [hL.coeFn_toLp,hf.coeFn_toLp,hg.coeFn_toLp,
      Lp.coeFn_add (a • hf.toLp f) (b • hg.toLp g),
      Lp.coeFn_smul a (hf.toLp f),Lp.coeFn_smul b (hg.toLp g)] with z hz hfz hgz habz haz hbz
    rw [hz,habz]
    simp only [Pi.add_apply]
    rw [haz,hbz]
    simp only [Pi.smul_apply,smul_eq_mul,hfz,hgz]
    rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_HilbertWeakConvexApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak convergence gives strong approximants in each convex eventual
constraint set. This is the narrow Mazur step used for measure modulus. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma mem_closure_convex_of_weak_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : ℕ → E} {v : E} {S : Set E} (hS : Convex ℝ S)
    (hu : ∀ᶠ n in atTop, u n ∈ S)
    (hw : ∀ w : E, Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w))) :
    v ∈ closure S := by
  by_contra hv
  obtain ⟨L,c,hL,hLv⟩ := geometric_hahn_banach_closed_point hS.closure isClosed_closure hv
  let w : E := (InnerProductSpace.toDual ℝ E).symm L
  have he (x : E) : inner ℝ x w = L x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hl : Tendsto (fun n => L (u n)) atTop (𝓝 (L v)) := by
    simpa only [he] using hw w
  have hvle : L v ≤ c := le_of_tendsto hl (hu.mono (fun n hn => (hL _ (subset_closure hn)).le))
  exact (not_lt_of_ge hvle) hLv

lemma exists_strong_approximation_of_convex_eventual_constraints
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : ℕ → E} {v : E} (S : ℕ → Set E) (hS : ∀ n, Convex ℝ (S n))
    (hu : ∀ n, ∀ᶠ k in atTop, u k ∈ S n)
    (hw : ∀ w : E, Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w))) :
    ∃ a : ℕ → E, (∀ n, a n ∈ S n) ∧ Tendsto a atTop (𝓝 v) := by
  have hex (n : ℕ) : ∃ x ∈ S n, dist x v < 1 / ((n : ℝ)+1) := by
    have hc := mem_closure_convex_of_weak_limit (hS n) (hu n) hw
    simpa only [dist_comm] using Metric.mem_closure_iff.mp hc
      (1 / ((n : ℝ)+1)) (by positivity)
  choose a ha hd using hex
  refine ⟨a,ha,?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun n => dist_nonneg) (fun n => (hd n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_AdmissibleWeakLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A weak L² limit of nonnegative densities satisfying increasing
pointwise constraints bounds the modulus of their union. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance instFactLeENNRealOfNat_solutions_5 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma measureFamilyModulus_le_weak_limit
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) (K : A → FiniteMeasure Z)
    (S : ℕ → Set A) (hcover : ∀ a, ∀ᶠ n in atTop, a ∈ S n)
    (u : ℕ → Lp ℝ 2 σ) (v : Lp ℝ 2 σ)
    (hu : ∀ n, ∀ᶠ k in atTop, u k ∈ admissibleL2Classes σ (fun a : S n => K a.val))
    (hw : ∀ w : Lp ℝ 2 σ, Tendsto (fun n => inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w))) :
    measureFamilyModulus A Z σ K ≤ ENNReal.ofReal (‖v‖^2) := by
  obtain ⟨a,ha,hav⟩ := exists_strong_approximation_of_convex_eventual_constraints
    (fun n => admissibleL2Classes σ (fun b : S n => K b.val))
    (fun n => admissibleL2Classes_convex σ _) hu hw
  choose f hf hfm hf0 hfa heq using ha
  have heLp : Tendsto (fun n => eLpNorm (fun z => f n z-v z) 2 σ) atTop (𝓝 0) := by
    have hh := hav.edist (tendsto_const_nhds (x := v))
    simp only [edist_self] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    calc
      eLpNorm (fun z => f n z-v z) 2 σ =
          edist ((hf n).toLp (f n)) ((Lp.memLp v).toLp v) :=
        (Lp.edist_toLp_toLp (f n) v (hf n) (Lp.memLp v)).symm
      _ = edist (a n) v := by rw [heq n,Lp.toLp_coeFn]
  have hb := measureFamilyModulus_le_of_signed_L2_limit σ K f v hfm hf0 hf
    (Lp.stronglyMeasurable v).measurable (Lp.memLp v) heLp (fun b =>
      (hcover b).mono (fun n hn => hfa n ⟨b,hn⟩))
  simpa only [Lp.toLp_coeFn] using hb

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureFamilyBoundedSequence
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly bounded L² densities with eventual pointwise admissibility
bound the modulus of the whole family. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance instFactLeENNRealOfNat_solutions_6 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma measureFamilyModulus_le_of_bounded_L2_sequence
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) [IsSeparable σ]
    (K : A → FiniteMeasure Z) (f : ℕ → Z → ℝ)
    (hf : ∀ n, MemLp (f n) 2 σ) (hfm : ∀ n, Measurable (f n))
    (hf0 : ∀ n z, 0 ≤ f n z) {C : ℝ}
    (hnorm : ∀ n, ‖(hf n).toLp (f n)‖ ≤ C)
    (ha : ∀ a, ∀ᶠ n in atTop, 1 ≤ ∫⁻ z, ENNReal.ofReal (f n z) ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ENNReal.ofReal (C^2) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : TopologicalSpace.SeparableSpace (Lp ℝ 2 σ) := inferInstance
  obtain ⟨v,hv,ρ,hρ,hw⟩ := exists_hilbert_weak_subsequence
    (fun n => (hf n).toLp (f n)) C hnorm
  let S : ℕ → Set A := fun n => {a | ∀ k, n ≤ k →
    1 ≤ ∫⁻ z, ENNReal.ofReal (f k z) ∂(K a : Measure Z)}
  have hcover (a : A) : ∀ᶠ n in atTop, a ∈ S n := by
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ha a)
    exact eventually_atTop.mpr ⟨N,fun n hn k hk => hN k (hn.trans hk)⟩
  have hu (n : ℕ) : ∀ᶠ k in atTop,
      (hf (ρ k)).toLp (f (ρ k)) ∈ admissibleL2Classes σ (fun a : S n => K a.val) := by
    filter_upwards [hρ.tendsto_atTop.eventually (eventually_ge_atTop n)] with k hk
    exact ⟨f (ρ k),hf (ρ k),hfm (ρ k),hf0 (ρ k),
      fun a => a.property (ρ k) hk,rfl⟩
  exact (measureFamilyModulus_le_weak_limit σ K S hcover
    (fun k => (hf (ρ k)).toLp (f (ρ k))) v hu hw).trans
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg v) hv 2))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ExtendedDensityL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-energy extended density has a Borel real L² representative.
Its infinite values are retained separately as a reference-null Borel set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma lintegral_ofReal_toReal_eq_away_infinity
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (h : Z → ℝ≥0∞)
    (hnull : μ {z | h z = ∞} = 0) :
    (∫⁻ z, ENNReal.ofReal ((h z).toReal) ∂μ) = ∫⁻ z, h z ∂μ := by
  apply lintegral_congr_ae
  have he : ∀ᵐ z ∂μ, h z ≠ ∞ := by
    simpa only [ae_iff,not_not] using hnull
  exact he.mono (fun z hz => ENNReal.ofReal_toReal hz)

local instance localInst_r26ada9_5 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
lemma extended_density_L2
    {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)
    (h : Z → ℝ≥0∞) (hh : Measurable h) {D : ℝ} (hD : 0 ≤ D)
    (henergy : (∫⁻ z, h z^2 ∂σ) ≤ ENNReal.ofReal D) :
    Measurable (fun z => (h z).toReal) ∧
      ∃ hu : MemLp (fun z => (h z).toReal) 2 σ,
        ‖hu.toLp (fun z => (h z).toReal)‖^2 ≤ D ∧
        MeasurableSet {z | h z = ∞} ∧ σ {z | h z = ∞} = 0 := by
  have hm := hh.ennreal_toReal
  have hfinite : ∀ᵐ z ∂σ, h z ≠ ∞ := by
    have hs := ae_lt_top (hh.pow_const 2) (henergy.trans_lt ENNReal.ofReal_lt_top).ne
    filter_upwards [hs] with z hz
    intro ht
    simp only [ht,ENNReal.top_pow (by norm_num : (2:ℕ) ≠ 0),lt_self_iff_false] at hz
  have hE : (∫⁻ z, ENNReal.ofReal ((h z).toReal^2) ∂σ) ≤ ENNReal.ofReal D := by
    refine (lintegral_mono (fun z => ?_)).trans henergy
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    exact pow_le_pow_left' ENNReal.ofReal_toReal_le 2
  have hi : Integrable (fun z => (h z).toReal^2) σ :=
    ⟨(hm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun z => sq_nonneg ((h z).toReal)))).mpr
        (hE.trans_lt ENNReal.ofReal_lt_top)⟩
  let hu : MemLp (fun z => (h z).toReal) 2 σ :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hi
  refine ⟨hm,hu,?_,hh (measurableSet_singleton ∞),?_⟩
  · have heq : (∫ z, (h z).toReal^2 ∂σ) = ‖hu.toLp (fun z => (h z).toReal)‖^2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with z hz
      simp only [hz,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun z => sq_nonneg ((h z).toReal))),heq] at hE
    exact (ENNReal.ofReal_le_ofReal_iff hD).mp hE
  · simpa only [ae_iff,not_not] using hfinite

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureFamilyIncreasing
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing-family continuity of pointwise modulus. Infinite values of
the approximating densities are isolated in one Borel null set and repaired. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance instFactLeENNRealOfNat_solutions_7 : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma measureFamilyModulus_le_of_increasing_strict_bound
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) [IsSeparable σ]
    (K : A → FiniteMeasure Z) (S : ℕ → Set A) (hmono : Monotone S)
    (hcover : ∀ a, ∃ n, a ∈ S n) {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ n, measureFamilyModulus (S n) Z σ (fun a => K a.val) < ENNReal.ofReal D) :
    measureFamilyModulus A Z σ K ≤ ENNReal.ofReal D := by
  choose h hh ha he using (fun n => exists_admissible_of_modulus_lt σ
    (fun a : S n => K a.val) (hbound n))
  have hr (n : ℕ) := extended_density_L2 σ (h n) (hh n) hD (he n).le
  choose hm hu hnorm hNm hN0 using hr
  let N : Set Z := ⋃ n : ℕ, {z | h n z = ∞}
  have hN : MeasurableSet N := MeasurableSet.iUnion hNm
  have hσN : σ N = 0 := measure_iUnion_null hN0
  let B : Set A := {a | (K a : Measure Z) N ≠ 0}
  have hB : measureFamilyModulus B Z σ (fun a => K a.val) = 0 :=
    measureFamilyModulus_zero_of_charges_null_set σ _ hN hσN (fun a => a.property)
  rw [measureFamilyModulus_remove_null_family σ K B hB]
  have hn (n : ℕ) : ‖(hu n).toLp (fun z => (h n z).toReal)‖ ≤ Real.sqrt D := by
    nlinarith [hnorm n, norm_nonneg ((hu n).toLp (fun z => (h n z).toReal)),
      Real.sqrt_nonneg D,Real.sq_sqrt hD]
  have hb := measureFamilyModulus_le_of_bounded_L2_sequence σ
    (fun a : (Bᶜ : Set A) => K a.val) (fun n z => (h n z).toReal)
    hu hm (fun _ _ => ENNReal.toReal_nonneg) hn ?_
  · simpa only [Real.sq_sqrt hD] using hb
  · intro a
    obtain ⟨n,han⟩ := hcover a.val
    filter_upwards [eventually_ge_atTop n] with k hk
    have hνN : (K a.val : Measure Z) N = 0 := by
      simpa only [B,mem_compl_iff,mem_ofPred_eq,not_not] using a.property
    have hνk : (K a.val : Measure Z) {z | h k z = ∞} = 0 :=
      measure_mono_null (subset_iUnion (fun n => {z | h n z = ∞}) k) hνN
    rw [lintegral_ofReal_toReal_eq_away_infinity _ _ hνk]
    exact ha k ⟨a.val,hmono hk han⟩

lemma measureFamilyModulus_iUnion
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) [IsSeparable σ]
    (K : A → FiniteMeasure Z) (S : ℕ → Set A) (hmono : Monotone S)
    (hcover : ∀ a, ∃ n, a ∈ S n) :
    measureFamilyModulus A Z σ K =
      ⨆ n, measureFamilyModulus (S n) Z σ (fun a => K a.val) := by
  apply le_antisymm
  · by_contra hnot
    have hlt : (⨆ n, measureFamilyModulus (S n) Z σ (fun a => K a.val)) <
        measureFamilyModulus A Z σ K := lt_of_not_ge hnot
    obtain ⟨d,hd,hdm⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
    have hbound (n : ℕ) : measureFamilyModulus (S n) Z σ (fun a => K a.val) <
        ENNReal.ofReal (d : ℝ) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using (le_iSup
        (fun n => measureFamilyModulus (S n) Z σ (fun a => K a.val)) n).trans_lt hd
    have hb := measureFamilyModulus_le_of_increasing_strict_bound σ K S hmono hcover
      d.coe_nonneg hbound
    exact (not_lt_of_ge (by simpa only [ENNReal.ofReal_coe_nnreal] using hb)) hdm
  · apply iSup_le
    intro n
    apply measureFamilyModulus_mono_range
    rintro _ ⟨a,rfl⟩
    exact mem_range_self a.val

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ModulusFiniteBallCut
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite collection of small closed balls retains a prescribed strict
modulus threshold in a separable metric presentation. -/
open Set Function Filter MeasureTheory TopologicalSpace Metric
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_modulus_finite_closedBall_cut
    {X Z : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
    [MeasurableSpace Z] (σ : Measure Z) [IsSeparable σ] (K : X → FiniteMeasure Z)
    {C : Set X} {c : ℝ≥0∞} (hc : c < measureFamilyModulus C Z σ (fun x => K x.val))
    {r : ℝ} (hr : 0 < r) :
    ∃ N : ℕ, c < measureFamilyModulus
      ((C ∩ ⋃ j ∈ (↑(Finset.range (N+1)) : Set ℕ), closedBall (denseSeq X j) r) : Set X)
      Z σ (fun x => K x.val) := by
  let S : ℕ → Set C := fun N => {x | ∃ j ≤ N, dist x.val (denseSeq X j) ≤ r}
  have hm : Monotone S := by
    intro n m hnm x hx
    obtain ⟨j,hj,hxj⟩ := hx
    exact ⟨j,hj.trans hnm,hxj⟩
  have hu : ∀ x : C, ∃ n, x ∈ S n := by
    intro x
    obtain ⟨j,hj⟩ := Metric.denseRange_iff.mp (denseRange_denseSeq X) x.val r hr
    exact ⟨j,j,le_rfl,hj.le⟩
  rw [measureFamilyModulus_iUnion σ (fun x : C => K x.val) S hm hu] at hc
  obtain ⟨N,hN⟩ := lt_iSup_iff.mp hc
  refine ⟨N,?_⟩
  have hrange : range (fun x : S N => K x.val.val) =
      range (fun x : ((C ∩ ⋃ j ∈ (↑(Finset.range (N+1)) : Set ℕ),
        closedBall (denseSeq X j) r) : Set X) => K x.val) := by
    ext v
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨j,hj,hxj⟩ := x.property
      exact ⟨⟨x.val.val,x.val.property,mem_iUnion₂.mpr
        ⟨j,by simpa only [Finset.mem_coe,Finset.mem_range] using Nat.lt_succ_of_le hj,hxj⟩⟩,hx⟩
    · rintro ⟨x,hx⟩
      obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp x.property.2
      have hjN : j ≤ N := Nat.le_of_lt_succ (by simpa only [Finset.mem_coe,Finset.mem_range] using hj)
      exact ⟨⟨⟨x.val,x.property.1⟩,j,hjN,hxj⟩,hx⟩
  exact hN.trans_eq (measureFamilyModulus_eq_of_range_eq σ _ _ hrange)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteMeshCompactIntersection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite covers at successively smaller radii make the intersection
compact, and let a continuous image commute with the nested closures. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

lemma totallyBounded_diagonal_of_finite_mesh
    (C : ℕ → Set X) (hanti : Antitone C) (F : ℕ → Finset X)
    (hmesh : ∀ n, C (n+1) ⊆ ⋃ z ∈ (↑(F n) : Set X), closedBall z (1/((n:ℝ)+1)))
    (x : ℕ → X) (hx : ∀ n, x n ∈ C n) : TotallyBounded (range x) := by
  classical
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hε)).exists
  let E : Set X := (↑(F N) : Set X) ∪ (x '' (↑(Finset.range (N+1)) : Set ℕ))
  refine ⟨E,(F N).finite_toSet.union ((Finset.range (N+1)).finite_toSet.image x),?_⟩
  rintro y ⟨k,rfl⟩
  by_cases hk : N+1 ≤ k
  · have hm := hmesh N (hanti hk (hx k))
    obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp hm
    apply mem_iUnion₂.mpr
    refine ⟨z,Or.inl hz,?_⟩
    exact (mem_closedBall.mp hxz).trans_lt hN
  · apply mem_iUnion₂.mpr
    refine ⟨x k,Or.inr ⟨k,by simpa only [Finset.mem_coe,Finset.mem_range] using lt_of_not_ge hk,rfl⟩,?_⟩
    simpa only [mem_ball,dist_self] using hε

lemma compact_iInter_of_finite_mesh [CompleteSpace X]
    (C : ℕ → Set X) (hC : ∀ n, IsClosed (C n))
    (F : ℕ → Finset X)
    (hmesh : ∀ n, C (n+1) ⊆ ⋃ z ∈ (↑(F n) : Set X), closedBall z (1/((n:ℝ)+1))) :
    IsCompact (⋂ n, C n) := by
  have ht : TotallyBounded (⋂ n, C n) := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hε)).exists
    refine ⟨F N,(F N).finite_toSet,?_⟩
    intro x hx
    obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp (hmesh N (mem_iInter.mp hx (N+1)))
    exact mem_iUnion₂.mpr ⟨z,hz,(mem_closedBall.mp hxz).trans_lt hN⟩
  exact ht.isCompact_of_isClosed (isClosed_iInter hC)

lemma image_iInter_eq_iInter_closure_of_finite_mesh [CompleteSpace X]
    (C : ℕ → Set X) (hC : ∀ n, IsClosed (C n)) (hanti : Antitone C)
    (F : ℕ → Finset X)
    (hmesh : ∀ n, C (n+1) ⊆ ⋃ z ∈ (↑(F n) : Set X), closedBall z (1/((n:ℝ)+1)))
    (f : X → Y) (hf : Continuous f) :
    f '' (⋂ n, C n) = ⋂ n, closure (f '' C n) := by
  classical
  apply Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact mem_iInter.mpr (fun n => subset_closure (mem_image_of_mem f (mem_iInter.mp hx n)))
  · intro y hy
    have hex (n : ℕ) : ∃ x ∈ C n, dist (f x) y < 1/((n:ℝ)+1) := by
      obtain ⟨w,⟨x,hx,rfl⟩,hw⟩ := Metric.mem_closure_iff.mp (mem_iInter.mp hy n)
        (1/((n:ℝ)+1)) (by positivity)
      exact ⟨x,hx,by simpa only [dist_comm] using hw⟩
    choose x hx hd using hex
    have ht := totallyBounded_diagonal_of_finite_mesh C hanti F hmesh x hx
    have hk : IsCompact (closure (range x)) := ht.closure.isCompact_of_isClosed isClosed_closure
    obtain ⟨z,_,ρ,hρ,hlim⟩ := hk.isSeqCompact (fun n => subset_closure (mem_range_self n))
    have hz (n : ℕ) : z ∈ C n := by
      apply (hC n).mem_of_tendsto hlim
      filter_upwards [hρ.tendsto_atTop.eventually (eventually_ge_atTop n)] with k hk
      exact hanti hk (hx (ρ k))
    have hfy : Tendsto (fun n => f (x (ρ n))) atTop (𝓝 y) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun n => dist_nonneg) (fun n => (hd (ρ n)).le)
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hρ.tendsto_atTop)
    have heq : f z = y := tendsto_nhds_unique (hf.continuousAt.tendsto.comp hlim) hfy
    exact ⟨z,mem_iInter.mpr hz,heq⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ModulusFiniteMesh
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recursive finite ball cuts preserve the strict modulus threshold while
constructing a closed finite-mesh presentation with compact intersection. -/
open Set Function Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_modulus_finite_mesh
    {X Z : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
    [MeasurableSpace Z] (σ : Measure Z) [IsSeparable σ] (K : X → FiniteMeasure Z)
    {A : Set X} (hA : IsClosed A) {c : ℝ≥0∞}
    (hc : c < measureFamilyModulus A Z σ (fun x => K x.val)) :
    ∃ (C : ℕ → Set X) (F : ℕ → Finset X), C 0 = A ∧ (∀ n, IsClosed (C n)) ∧
      Antitone C ∧
      (∀ n, C (n+1) ⊆ ⋃ z ∈ (↑(F n) : Set X), closedBall z (1/((n:ℝ)+1))) ∧
      ∀ n, c < measureFamilyModulus (C n) Z σ (fun x => K x.val) := by
  classical
  let Q := {C : Set X // IsClosed C ∧ c < measureFamilyModulus C Z σ (fun x => K x.val)}
  let cut (n : ℕ) (C : Q) : ℕ := Classical.choose
    (exists_modulus_finite_closedBall_cut σ K C.property.2 (r := 1/((n:ℝ)+1)) (by positivity))
  let U (n k : ℕ) : Set X :=
    ⋃ j ∈ (↑(Finset.range (k+1)) : Set ℕ), closedBall (denseSeq X j) (1/((n:ℝ)+1))
  have hU (n k : ℕ) : IsClosed (U n k) :=
    (Finset.range (k+1)).finite_toSet.isClosed_biUnion (fun j _ => isClosed_closedBall)
  let step (n : ℕ) (C : Q) : Q := ⟨C.val ∩ U n (cut n C),C.property.1.inter (hU n _),
    Classical.choose_spec
      (exists_modulus_finite_closedBall_cut σ K C.property.2 (r := 1/((n:ℝ)+1)) (by positivity))⟩
  let p : ℕ → Q := Nat.rec ⟨A,hA,hc⟩ step
  let C (n : ℕ) : Set X := (p n).val
  let F (n : ℕ) : Finset X := (Finset.range (cut n (p n)+1)).image (denseSeq X)
  have hs (n : ℕ) : C (n+1) = C n ∩ U n (cut n (p n)) := rfl
  refine ⟨C,F,rfl,fun n => (p n).property.1,?_,?_,fun n => (p n).property.2⟩
  · exact antitone_nat_of_succ_le (fun n => hs n ▸ inter_subset_left)
  · intro n x hx
    rw [hs n] at hx
    obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx.2
    apply mem_iUnion₂.mpr
    refine ⟨denseSeq X j,?_,hxj⟩
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j,hj,rfl⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactPlanTestDensity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact plan satisfying the continuous L² test bound has the actual
Borel barycenter density with the same norm bound. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

attribute [local instance] OAI.CircleDomainRigidity.instFactLeENNRealOfNat_solutions_4
lemma compact_plan_density_of_test_bound
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) [CompactSpace S] (P : ProbabilityMeasure S)
    {c : ℝ} (hc : 0 < c)
    (htest : ∀ f : Z →ᵇ ℝ,
      c * (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) ≤
        ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖) :
    ∃ q : Z → ℝ≥0∞, Measurable q ∧ compactMeasureBarycenter P = σ.withDensity q ∧
      (∫⁻ z, q z^2 ∂σ) ≤ ENNReal.ofReal (c⁻¹^2) := by
  have hI (f : Z →ᵇ ℝ) : Integrable
      (fun v : S => compactMeasureTestOperator S f v) (P : Measure S) := by
    apply (integrable_const ‖compactMeasureTestOperator S f‖).mono'
      ((measurable_finiteMeasure_integral f).comp measurable_subtype_coe).aestronglyMeasurable
    exact Eventually.of_forall (fun v => (compactMeasureTestOperator S f).norm_coe_le_norm v)
  let F : (Z →ᵇ ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ v : S, compactMeasureTestOperator S f v ∂(P : Measure S)
      map_add' := by
        intro f g
        simp only [map_add,ContinuousMap.add_apply]
        exact integral_add (hI f) (hI g)
      map_smul' := by
        intro r f
        simp only [map_smul,ContinuousMap.smul_apply,smul_eq_mul]
        exact integral_const_mul r _ }
  have hF (f : Z →ᵇ ℝ) : F f ≤ c⁻¹ * ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
    have hb := mul_le_mul_of_nonneg_left (htest f) (inv_nonneg.mpr hc.le)
    change (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) ≤ _
    simpa only [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] using hb
  obtain ⟨g,hg,hrep⟩ := exists_L2_pairing_of_boundedContinuous_bound σ F
    (inv_nonneg.mpr hc.le) hF
  obtain ⟨hg0,hbar⟩ := compactMeasureBarycenter_eq_withDensity σ hS P g (fun f => (hrep f).symm)
  refine ⟨fun z => ENNReal.ofReal (g z), (Lp.stronglyMeasurable g).measurable.ennreal_ofReal,
    hbar,?_⟩
  rw [L2_ofReal_energy_eq σ g hg0]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg g) hg 2)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MeasurePlanWeakDuality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported probability plan with an L² barycenter gives the lower
modulus bound. All admissible tests retain their extended values. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_lower_of_barycenter
    {A Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) {S : Set (FiniteMeasure Z)}
    (P : ProbabilityMeasure S) (hsupp : ∀ᵐ v ∂(P : Measure S), v.val ∈ range K)
    {q : Z → ℝ≥0∞} (hq : Measurable q)
    (hbar : compactMeasureBarycenter P = σ.withDensity q)
    {c : ℝ≥0} (hc : 0 < c) (he : (∫⁻ z, q z^2 ∂σ) ≤ (c : ℝ≥0∞)⁻¹) :
    (c : ℝ≥0∞) ≤ measureFamilyModulus A Z σ K := by
  apply le_iInf
  intro h
  apply le_iInf
  intro hh
  apply le_iInf
  intro ha
  have hpay : (1 : ℝ≥0∞) ≤ ∫⁻ z, q z * h z ∂σ := by
    have hp : (1 : ℝ≥0∞) ≤ ∫⁻ v : S, (∫⁻ z, h z ∂(v.val : Measure Z)) ∂(P : Measure S) := by
      calc
        (1 : ℝ≥0∞) = ∫⁻ _v : S, 1 ∂(P : Measure S) := by simp
        _ ≤ _ := by
          apply lintegral_mono_ae
          filter_upwards [hsupp] with v hv
          obtain ⟨a,haeq⟩ := hv
          simpa only [← haeq] using ha a
    rw [← compactMeasureBarycenter_lintegral P hh,hbar,
      lintegral_withDensity_eq_lintegral_mul _ hq hh] at hp
    exact hp
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq σ hconj hq.aemeasurable hh.aemeasurable
  have hroot : (1 : ℝ≥0∞) ≤ (∫⁻ z, q z^2 ∂σ)^(1/2 : ℝ) *
      (∫⁻ z, h z^2 ∂σ)^(1/2 : ℝ) := by
    exact hpay.trans (by simpa only [Pi.mul_apply,ENNReal.rpow_two] using hcs)
  have hsqrt (x : ℝ≥0∞) : (x^(1/2 : ℝ))^2 = x := by
    rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
  have hsquare := pow_le_pow_left' hroot 2
  simp only [one_pow,mul_pow,hsqrt] at hsquare
  have hbound : (1 : ℝ≥0∞) ≤ (c : ℝ≥0∞)⁻¹ * ∫⁻ z, h z^2 ∂σ :=
    hsquare.trans (mul_le_mul_left he _)
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  calc
    (c : ℝ≥0∞) = c*1 := (mul_one _).symm
    _ ≤ c * ((c : ℝ≥0∞)⁻¹ * ∫⁻ z, h z^2 ∂σ) := mul_le_mul_right hbound _
    _ = _ := by rw [← mul_assoc,ENNReal.mul_inv_cancel hc0 ENNReal.coe_ne_top,one_mul]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ClosedProbabilitySupport
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support in a closed set is retained by weak limits of probability laws. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma isClosed_probability_supported_closed
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] {F : Set X} (hF : IsClosed F) :
    IsClosed {P : ProbabilityMeasure X | ∀ᵐ x ∂(P : Measure X), x ∈ F} := by
  have hsc : UpperSemicontinuous (fun P : ProbabilityMeasure X => (P : Measure X) F) :=
    upperSemicontinuous_iff_limsup_le.mpr (fun P =>
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto tendsto_id hF)
  have he : {P : ProbabilityMeasure X | ∀ᵐ x ∂(P : Measure X), x ∈ F} =
      {P : ProbabilityMeasure X | (1 : ℝ≥0∞) ≤ (P : Measure X) F} := by
    ext P
    change (∀ᵐ x ∂(P : Measure X), x ∈ F) ↔ (1 : ℝ≥0∞) ≤ (P : Measure X) F
    constructor
    · intro h
      have heq : F =ᵐ[(P : Measure X)] univ := h.mono (fun x hx => by show (x ∈ F) = (x ∈ univ); simp [hx])
      rw [measure_congr heq,measure_univ]
    · intro h
      have hm : (P : Measure X) F = 1 := le_antisymm ((measure_mono (subset_univ F)).trans_eq measure_univ) h
      have hc : (P : Measure X) Fᶜ = 0 := by
        rw [measure_compl hF.measurableSet (measure_ne_top _ _),hm,measure_univ,tsub_self]
      apply ae_iff.mpr
      change (P : Measure X) Fᶜ = 0
      exact hc
  rw [he]
  exact hsc.isClosed_preimage 1

lemma probability_supported_closed_of_tendsto
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] {P : ℕ → ProbabilityMeasure X} {Q : ProbabilityMeasure X}
    (hlim : Tendsto P atTop (𝓝 Q)) {F : Set X} (hF : IsClosed F)
    (hsupp : ∀ᶠ n in atTop, ∀ᵐ x ∂(P n : Measure X), x ∈ F) :
    ∀ᵐ x ∂(Q : Measure X), x ∈ F :=
  (isClosed_probability_supported_closed hF).mem_of_tendsto hlim hsupp

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactProbabilityBorel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On a compact metrizable space, countably many continuous test integrals
embed the probability laws in a countable product. Their weak topology is
Polish and its Borel sigma algebra is precisely the evaluation sigma algebra. -/
open Set Function Filter MeasureTheory TopologicalSpace Topology
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace CircleDomainRigidity

lemma compact_probability_borel
    (Z : Type*) [TopologicalSpace Z] [MetrizableSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] : BorelSpace (ProbabilityMeasure Z) := by
  let : MetricSpace Z := TopologicalSpace.metrizableSpaceMetric Z
  let : SeparableSpace (Z →ᵇ ℝ≥0) :=
    (ContinuousMap.isometryEquivBoundedOfCompact Z ℝ≥0).surjective.denseRange.separableSpace
      (ContinuousMap.isometryEquivBoundedOfCompact Z ℝ≥0).continuous
  obtain ⟨b, hb⟩ := exists_dense_seq (Z →ᵇ ℝ≥0)
  let e : ProbabilityMeasure Z → (ℕ → ℝ≥0) :=
    fun μ n => μ.toFiniteMeasure.testAgainstNN (b n)
  have hec : Continuous e := continuous_pi (fun n =>
    ProbabilityMeasure.continuous_testAgainstNN_eval (b n))
  have hei : Injective e := by
    intro μ ν heq
    apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding Z).injective
    apply FiniteMeasure.injective_toWeakDualBCNN
    apply DFunLike.ext
    intro f
    change μ.toFiniteMeasure.testAgainstNN f = ν.toFiniteMeasure.testAgainstNN f
    exact hb.induction_on f
      (isClosed_eq μ.toFiniteMeasure.testAgainstNN_lipschitz.continuous
        ν.toFiniteMeasure.testAgainstNN_lipschitz.continuous)
      (fun n => congrFun heq n)
  have he : IsClosedEmbedding e := hec.isClosedEmbedding hei
  have hem : Measurable e := by
    apply Measurable.of_eval
    intro n
    exact (Measure.measurable_lintegral ((ENNReal.continuous_coe.comp (b n).continuous).measurable)).ennreal_toNNReal.comp
      measurable_subtype_coe
  have hlo : (inferInstance : MeasurableSpace (ProbabilityMeasure Z)) ≤ borel (ProbabilityMeasure Z) := by
    have h : @Measurable (ProbabilityMeasure Z) (Measure Z)
        (borel (ProbabilityMeasure Z)) inferInstance (fun μ => (μ : Measure Z)) := by
      let : MeasurableSpace (ProbabilityMeasure Z) := borel (ProbabilityMeasure Z)
      let : BorelSpace (ProbabilityMeasure Z) := ⟨rfl⟩
      exact measurable_measure_of_continuous_probability continuous_id
    exact h.comap_le
  have hup : borel (ProbabilityMeasure Z) ≤ (inferInstance : MeasurableSpace (ProbabilityMeasure Z)) := by
    rw [he.isEmbedding.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
    exact hem.comap_le
  exact ⟨le_antisymm hlo hup⟩

lemma compact_probability_polish
    (Z : Type*) [TopologicalSpace Z] [MetrizableSpace Z] [CompactSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] : PolishSpace (ProbabilityMeasure Z) := by
  let : MetricSpace (ProbabilityMeasure Z) := TopologicalSpace.metrizableSpaceMetric _
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_CompleteEmbeddingGDelta
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A completely metrizable subspace of a metrizable space is a G-delta.
The open sets below bound the diameter of their inverse images. A sequence
approaching a point in all these sets is Cauchy in the complete source metric. -/
open Set Function Filter Topology TopologicalSpace
noncomputable section
namespace CircleDomainRigidity

lemma isGDelta_range_embedding
    {A B : Type*} [TopologicalSpace A] [IsCompletelyMetrizableSpace A]
    [TopologicalSpace B] [MetrizableSpace B] {f : A → B} (hf : IsEmbedding f) :
    IsGδ (range f) := by
  let := upgradeIsCompletelyMetrizable A
  let : MetricSpace B := metrizableSpaceMetric B
  let U : ℕ → Set B := fun n => ⋃₀ {V : Set B | IsOpen V ∧
    ∀ a b : A, f a ∈ V → f b ∈ V → dist a b < 1 / (n + 1 : ℝ)}
  have hU : ∀ n, IsOpen (U n) := fun n => isOpen_sUnion fun V hV => hV.1
  have hsub : ∀ n, range f ⊆ U n := by
    intro n y hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨V, hVo, hV⟩ := hf.isInducing.isOpen_iff.mp
      (Metric.isOpen_ball (x := x) (ε := (1 / (n + 1 : ℝ)) / 2))
    refine mem_sUnion.mpr ⟨V, ⟨hVo, ?_⟩, ?_⟩
    · intro a b ha hb
      have ha' : dist a x < (1 / (n + 1 : ℝ)) / 2 := by
        have haa : a ∈ f ⁻¹' V := ha
        rw [hV] at haa
        exact haa
      have hb' : dist b x < (1 / (n + 1 : ℝ)) / 2 := by
        have hbb : b ∈ f ⁻¹' V := hb
        rw [hV] at hbb
        exact hbb
      linarith [dist_triangle_right a b x]
    · have hx : x ∈ Metric.ball x ((1 / (n + 1 : ℝ)) / 2) :=
        Metric.mem_ball_self (by positivity)
      rwa [← hV] at hx
  have heq : range f = closure (range f) ∩ ⋂ n, U n := by
    apply Subset.antisymm
    · exact fun y hy => ⟨subset_closure hy, mem_iInter.mpr (fun n => hsub n hy)⟩
    · intro y hy
      obtain ⟨ys, hys, hlim⟩ := mem_closure_iff_seq_limit.mp hy.1
      choose xs hxs using hys
      have hflim : Tendsto (fun n => f (xs n)) atTop (𝓝 y) := by
        simpa only [hxs] using hlim
      have hc : CauchySeq xs := Metric.cauchySeq_iff.mpr (by
        intro ε hε
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        obtain ⟨V, hV, hyV⟩ := mem_sUnion.mp (mem_iInter.mp hy.2 n)
        obtain ⟨N, hN⟩ := eventually_atTop.mp (hflim (hV.1.mem_nhds hyV))
        exact ⟨N, fun i hi j hj => (hV.2 _ _ (hN i hi) (hN j hj)).trans hn⟩)
      obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
      exact ⟨x, tendsto_nhds_unique (hf.continuous.tendsto x |>.comp hx) hflim⟩
  rw [heq]
  exact isClosed_closure.isGδ.inter (IsGδ.iInter_of_isOpen hU)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactFiniteMeasureBorel
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact families of finite measures retain their original evaluation
sigma algebra. A countable continuous and measurable code proves both
compact-set measurability and the Borel structure on each compact family. -/
open Set Function Filter MeasureTheory TopologicalSpace Topology
open scoped Topology NNReal BoundedContinuousFunction
noncomputable section
namespace CircleDomainRigidity

lemma exists_finiteMeasure_countable_code
    (Z : Type*) [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] :
    ∃ e : FiniteMeasure Z → (ℕ → ℝ≥0), Continuous e ∧ Measurable e ∧ Injective e := by
  let : MetricSpace Z := metrizableSpaceMetric Z
  obtain ⟨f,hf⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := Z)
  have hfm : MeasurableEmbedding f := hf.continuous.measurableEmbedding hf.injective
  let X := ℕ → unitInterval
  let : SeparableSpace (X →ᵇ ℝ≥0) :=
    (ContinuousMap.isometryEquivBoundedOfCompact X ℝ≥0).surjective.denseRange.separableSpace
      (ContinuousMap.isometryEquivBoundedOfCompact X ℝ≥0).continuous
  obtain ⟨b,hb⟩ := exists_dense_seq (X →ᵇ ℝ≥0)
  let e : FiniteMeasure Z → (ℕ → ℝ≥0) :=
    fun v n => (v.map f).testAgainstNN (b n)
  have hec : Continuous e := continuous_pi (fun n =>
    (FiniteMeasure.continuous_testAgainstNN_eval (b n)).comp
      (FiniteMeasure.continuous_map hf.continuous))
  have hem : Measurable e := by
    apply Measurable.of_eval
    intro n
    have hm : Measurable (fun v : FiniteMeasure Z =>
        (v.map f : Measure X)) :=
      (Measure.measurable_map f hfm.measurable).comp measurable_subtype_coe
    exact (Measure.measurable_lintegral
      ((ENNReal.continuous_coe.comp (b n).continuous).measurable)).ennreal_toNNReal.comp hm
  refine ⟨e,hec,hem,?_⟩
  intro v w heq
  have hm : v.map f = w.map f := by
    apply FiniteMeasure.injective_toWeakDualBCNN
    apply DFunLike.ext
    intro g
    exact hb.induction_on g
      (isClosed_eq (v.map f).testAgainstNN_lipschitz.continuous
        (w.map f).testAgainstNN_lipschitz.continuous)
      (fun n => congrFun heq n)
  apply FiniteMeasure.toMeasure_injective
  exact hfm.map_injective (congrArg FiniteMeasure.toMeasure hm)

lemma compact_finiteMeasure_measurableSet
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) : MeasurableSet S := by
  obtain ⟨e,hec,hem,hei⟩ := exists_finiteMeasure_countable_code Z
  have hclosed : IsClosed (e '' S) := (hS.image hec).isClosed
  convert hem hclosed.measurableSet using 1
  all_goals try with_reducible_and_instances rfl
  exact (preimage_image_eq S hei).symm

lemma compact_finiteMeasure_borel
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) : BorelSpace S := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨e,hec,hem,hei⟩ := exists_finiteMeasure_countable_code Z
  have he : IsClosedEmbedding (fun v : S => e v.val) :=
    (hec.comp continuous_subtype_val).isClosedEmbedding (hei.comp Subtype.val_injective)
  have hm : Measurable (fun v : S => e v.val) := hem.comp measurable_subtype_coe
  refine ⟨le_antisymm (compact_finiteMeasure_measurable_le_borel S) ?_⟩
  rw [he.isEmbedding.eq_induced,borel_comap,← BorelSpace.measurable_eq]
  exact hm.comap_le

lemma compact_finiteMeasure_polish
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) : PolishSpace S := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨e,hec,_,hei⟩ := exists_finiteMeasure_countable_code Z
  have he : IsClosedEmbedding (fun v : S => e v.val) :=
    (hec.comp continuous_subtype_val).isClosedEmbedding (hei.comp Subtype.val_injective)
  exact he.polishSpace

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_NestedCompactTestPlan
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common continuous-test bound on decreasing compact measure families
passes to a plan supported on their intersection. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal BoundedContinuousFunction
noncomputable section
namespace CircleDomainRigidity

lemma exists_nested_compact_test_plan
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ]
    (T : ℕ → Set (FiniteMeasure Z)) (hT : ∀ n, IsCompact (T n))
    (hne : ∀ n, (T n).Nonempty) (hanti : Antitone T)
    (hz : (0 : FiniteMeasure Z) ∉ T 0) {c : ℝ} (hc : 0 < c)
    (hm : ∀ n, ENNReal.ofReal (c^2) < measureFamilyModulus (T n) Z σ (fun v => v.val)) :
    ∃ P : ProbabilityMeasure (T 0),
      (∀ᵐ v ∂(P : Measure (T 0)), v.val ∈ ⋂ n, T n) ∧
      ∀ f : Z →ᵇ ℝ,
        c * (∫ v : T 0, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure (T 0))) ≤
          ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
  classical
  let : CompactSpace (T 0) := isCompact_iff_compactSpace.mp (hT 0)
  let : BorelSpace (T 0) := compact_finiteMeasure_borel (hT 0)
  let : PolishSpace (T 0) := compact_finiteMeasure_polish (hT 0)
  let : PolishSpace (ProbabilityMeasure (T 0)) := compact_probability_polish (T 0)
  have hex (n : ℕ) : ∃ P : ProbabilityMeasure (T n), ∀ f : Z →ᵇ ℝ,
      c * (∫ v : T n, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure (T n))) ≤
        ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
    let : CompactSpace (T n) := isCompact_iff_compactSpace.mp (hT n)
    exact exists_compact_measure_test_plan σ (hT n) (hne n)
      (fun h => hz (hanti (Nat.zero_le n) h)) c hc (hm n)
  choose P hP using hex
  let j (n : ℕ) : T n → T 0 := fun v => ⟨v.val,hanti (Nat.zero_le n) v.property⟩
  have hjm (n : ℕ) : Measurable (j n) := by
    exact (show Measurable (fun v : T n => v.val) from measurable_subtype_coe).subtype_mk
  let Q (n : ℕ) : ProbabilityMeasure (T 0) := (P n).map (hjm n).aemeasurable
  obtain ⟨L,ρ,hρ,hlim⟩ := SeqCompactSpace.tendsto_subseq Q
  refine ⟨L,?_,?_⟩
  · have hs (n : ℕ) : ∀ᵐ v ∂(L : Measure (T 0)), v.val ∈ T n := by
      have hF : IsClosed {v : T 0 | v.val ∈ T n} :=
        (hT n).isClosed.preimage continuous_subtype_val
      apply probability_supported_closed_of_tendsto hlim hF
      filter_upwards [hρ.tendsto_atTop.eventually (eventually_ge_atTop n)] with k hk
      change ∀ᵐ v ∂(P (ρ k) : Measure (T (ρ k))).map (j (ρ k)), v.val ∈ T n
      apply (ae_map_iff (hjm (ρ k)).aemeasurable hF.measurableSet).mpr
      exact Eventually.of_forall (fun v => hanti hk v.property)
    filter_upwards [ae_all_iff.mpr hs] with v hv
    exact mem_iInter.mpr hv
  · intro f
    have ht : Tendsto (fun k => ∫ v : T 0, compactMeasureTestOperator (T 0) f v
        ∂(Q (ρ k) : Measure (T 0))) atTop
        (𝓝 (∫ v : T 0, compactMeasureTestOperator (T 0) f v ∂(L : Measure (T 0)))) :=
      (ProbabilityMeasure.continuous_integral_continuousMap
        (compactMeasureTestOperator (T 0) f)).continuousAt.tendsto.comp hlim
    apply le_of_tendsto (ht.const_mul c)
    apply Eventually.of_forall
    intro k
    change c * (∫ v : T 0, compactMeasureTestOperator (T 0) f v
      ∂(P (ρ k) : Measure (T (ρ k))).map (j (ρ k))) ≤ _
    rw [integral_map (hjm (ρ k)).aemeasurable
      (compactMeasureTestOperator (T 0) f).continuous.measurable.aestronglyMeasurable]
    exact hP (ρ k) f

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureContinuity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of pointwise modulus on decreasing compact measure families
avoiding zero. The limiting probability plan supplies the lower bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace CircleDomainRigidity

lemma compact_intersection_modulus_lower
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ]
    (T : ℕ → Set (FiniteMeasure Z)) (hT : ∀ n, IsCompact (T n))
    (hne : ∀ n, (T n).Nonempty) (hanti : Antitone T)
    (hz : (0 : FiniteMeasure Z) ∉ T 0) {c : ℝ≥0} (hc : 0 < c)
    (hm : ∀ n, (c : ℝ≥0∞) < measureFamilyModulus (T n) Z σ (fun v => v.val)) :
    (c : ℝ≥0∞) ≤ measureFamilyModulus (⋂ n, T n) Z σ (fun v => v.val) := by
  let : CompactSpace (T 0) := isCompact_iff_compactSpace.mp (hT 0)
  have hcr : (0 : ℝ) < c := hc
  have hsq : Real.sqrt (c : ℝ)^2 = c := Real.sq_sqrt c.coe_nonneg
  obtain ⟨P,hPs,hPt⟩ := exists_nested_compact_test_plan σ T hT hne hanti hz
    (Real.sqrt_pos.mpr hcr) (by simpa only [hsq,ENNReal.ofReal_coe_nnreal] using hm)
  obtain ⟨q,hq,hbar,he⟩ := compact_plan_density_of_test_bound σ (hT 0) P
    (Real.sqrt_pos.mpr hcr) hPt
  have he' : (∫⁻ z, q z^2 ∂σ) ≤ (c : ℝ≥0∞)⁻¹ := by
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    rw [inv_pow,hsq,ENNReal.ofReal_inv_of_pos hcr,ENNReal.ofReal_coe_nnreal]
  apply measureFamilyModulus_lower_of_barycenter σ (fun v : (⋂ n, T n) => v.val) P _ hq hbar hc he'
  filter_upwards [hPs] with v hv
  exact ⟨⟨v.val,hv⟩,rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CompactContinuousImageModulus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous presentation inside a compact family avoiding zero has a
compact subfamily retaining every prescribed strict modulus threshold. -/
open Set Function Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_zero_of_isEmpty
    {A Z : Type*} [IsEmpty A] [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) : measureFamilyModulus A Z σ K = 0 := by
  apply le_antisymm _ bot_le
  have h := measureFamilyModulus_le_admissible σ K
    (h := fun _ => 0) measurable_const (fun a => isEmptyElim a)
  change measureFamilyModulus A Z σ K ≤ 0
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),lintegral_zero] using h

lemma exists_compact_subfamily_of_continuous_image
    {X Z : Type*} [MetricSpace X] [CompleteSpace X] [SeparableSpace X] [Nonempty X]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {T : Set (FiniteMeasure Z)}
    (hT : IsCompact T) (hz : (0 : FiniteMeasure Z) ∉ T)
    (f : X → T) (hf : Continuous f) {c : ℝ≥0∞}
    (hc : c < measureFamilyModulus X Z σ (fun x => (f x).val)) :
    ∃ S : Set (FiniteMeasure Z), IsCompact S ∧ S ⊆ range (fun x => (f x).val) ∧
      c < measureFamilyModulus S Z σ (fun v => v.val) := by
  classical
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let : PolishSpace T := compact_finiteMeasure_polish hT
  let : MetricSpace T := metrizableSpaceMetric T
  obtain ⟨d,hcd,hd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hc
  have hd0 : 0 < d := by
    have hp : (0 : ℝ≥0∞) < d := (show (0 : ℝ≥0∞) ≤ c from zero_le).trans_lt hcd
    exact_mod_cast hp
  have heq : measureFamilyModulus (univ : Set X) Z σ (fun x => (f x.val).val) =
      measureFamilyModulus X Z σ (fun x => (f x).val) := by
    apply measureFamilyModulus_eq_of_range_eq
    ext v
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x,mem_univ x⟩,rfl⟩
  obtain ⟨C,F,_,hC,hanti,hmesh,hlarge⟩ := exists_modulus_finite_mesh σ
    (fun x => (f x).val) isClosed_univ (c := (d : ℝ≥0∞)) (heq.symm ▸ hd)
  have hne (n : ℕ) : (C n).Nonempty := by
    by_contra hn
    let : IsEmpty (C n) := ⟨fun x => hn ⟨x.val,x.property⟩⟩
    have hm := hlarge n
    rw [measureFamilyModulus_zero_of_isEmpty] at hm
    exact (not_lt_of_ge bot_le) hm
  let U (n : ℕ) : Set (FiniteMeasure Z) := Subtype.val '' closure (f '' C n)
  have hUc (n : ℕ) : IsCompact (U n) := isClosed_closure.isCompact.image continuous_subtype_val
  have hUn (n : ℕ) : (U n).Nonempty := by
    obtain ⟨x,hx⟩ := hne n
    exact ⟨(f x).val,⟨f x,subset_closure (mem_image_of_mem f hx),rfl⟩⟩
  have hUa : Antitone U := fun n m hnm => image_mono (closure_mono (image_mono (hanti hnm)))
  have hUz : (0 : FiniteMeasure Z) ∉ U 0 := by
    rintro ⟨w,_,hw⟩
    exact hz (hw ▸ w.property)
  have hUl (n : ℕ) : (d : ℝ≥0∞) < measureFamilyModulus (U n) Z σ (fun v => v.val) := by
    apply (hlarge n).trans_le
    apply measureFamilyModulus_mono_range
    rintro _ ⟨x,rfl⟩
    exact ⟨⟨(f x.val).val,⟨f x.val,subset_closure (mem_image_of_mem f x.property),rfl⟩⟩,rfl⟩
  have hlow := compact_intersection_modulus_lower σ U hUc hUn hUa hUz hd0 hUl
  let S : Set (FiniteMeasure Z) := (fun x => (f x).val) '' (⋂ n, C n)
  have hSc : IsCompact S := (compact_iInter_of_finite_mesh C hC F hmesh).image
    (continuous_subtype_val.comp hf)
  have hIS : (⋂ n, U n) ⊆ S := by
    intro v hv
    obtain ⟨w,_,hwv⟩ := mem_iInter.mp hv 0
    have hw : w ∈ ⋂ n, closure (f '' C n) := by
      apply mem_iInter.mpr
      intro n
      obtain ⟨w',hw',he⟩ := mem_iInter.mp hv n
      have heq : w' = w := Subtype.ext (he.trans hwv.symm)
      exact heq ▸ hw'
    rw [← image_iInter_eq_iInter_closure_of_finite_mesh C hC hanti F hmesh f hf] at hw
    obtain ⟨x,hx,hfx⟩ := hw
    exact ⟨x,hx,(congrArg Subtype.val hfx).trans hwv⟩
  refine ⟨S,hSc,?_ ,hcd.trans_le (hlow.trans ?_)⟩
  · rintro v ⟨x,_,rfl⟩
    exact mem_range_self x
  · apply measureFamilyModulus_mono_range
    rintro _ ⟨v,rfl⟩
    exact ⟨⟨v.val,hIS v.property⟩,rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureQuadraticSum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable square-sum of extended nonnegative densities. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_quadratic_sum_density {Z ι : Type*} [MeasurableSpace Z] [Countable ι]
    (σ : Measure Z) (g : ι → Z → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    ∃ h : Z → ℝ≥0∞, Measurable h ∧ (∀ i z, g i z ≤ h z) ∧
      (∫⁻ z, h z ^ 2 ∂σ) = ∑' i, ∫⁻ z, g i z ^ 2 ∂σ := by
  let h : Z → ℝ≥0∞ := fun z => (∑' i, g i z ^ 2) ^ (1/2 : ℝ)
  have hh : Measurable h :=
    (Measurable.tsum (fun i => (hg i).pow_const 2)).pow_const (1/2 : ℝ)
  have hsq (z : Z) : h z ^ 2 = ∑' i, g i z ^ 2 := by
    dsimp only [h]
    rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
  refine ⟨h,hh,?_,?_⟩
  · intro i z
    have he : (g i z ^ 2) ^ (1/2 : ℝ) = g i z := by
      rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
      norm_num
    rw [← he]
    exact ENNReal.rpow_le_rpow (ENNReal.le_tsum (f := fun j => g j z ^ 2) i) (by norm_num)
  · simp_rw [hsq]
    exact lintegral_tsum (fun i => ((hg i).pow_const 2).aemeasurable)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FiniteMeasureTightControl
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tightness estimate in the measure-modulus duality argument.
A finite Borel reference measure admits arbitrarily cheap L² densities
which charge every measure outside a compact set by at least one. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_finiteMeasure_control
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (T : Set (FiniteMeasure Z)) (h : Z → ℝ≥0∞), IsCompact T ∧ Measurable h ∧
      (∫⁻ z, h z ^ 2 ∂σ) < ε ∧
      ∀ v : FiniteMeasure Z, v ∉ T → 1 ≤ ∫⁻ z, h z ∂(v : Measure Z) := by
  classical
  obtain ⟨b,hb,hbsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' (Option ℕ)
  obtain ⟨δ,hδ,hδsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (measure_ne_top σ univ) (hb none).ne'
  let c : ℝ≥0 := min δ 1
  have hc : 0 < c := lt_min hδ zero_lt_one
  have hc2 : c ^ 2 ≤ δ := by
    have h1 : c ≤ 1 := min_le_right _ _
    have hδ' : c ≤ δ := min_le_left _ _
    calc
      c ^ 2 = c*c := pow_two c
      _ ≤ c := mul_le_of_le_one_right (show (0 : ℝ≥0) ≤ c from zero_le) h1
      _ ≤ δ := hδ'
  have hcsmall : (c : ℝ≥0∞)^2 * σ univ < b none := by
    exact (mul_le_mul_left (by exact_mod_cast hc2) _).trans_lt hδsmall
  let w (n : ℕ) : ℝ≥0 := n+1
  have hw (n : ℕ) : 0 < w n := by simp [w]
  have he (n : ℕ) : ∃ d : ℝ≥0, 0 < d ∧
      (d : ℝ≥0∞) * (w n : ℝ≥0∞)^2 < b (some n) := by
    exact ENNReal.exists_nnreal_pos_mul_lt (by simp) (hb (some n)).ne'
  choose d hd hdsmall using he
  have hK (n : ℕ) : ∃ K : Set Z, IsCompact K ∧ σ Kᶜ < d n := by
    obtain ⟨K,_,hK,hsmall⟩ := (MeasurableSet.univ : MeasurableSet (univ : Set Z)).exists_isCompact_sdiff_lt (μ := σ) (ε := (d n : ℝ≥0∞))
      (measure_ne_top σ univ) (by exact_mod_cast (hd n).ne')
    exact ⟨K,hK,by simpa only [← compl_eq_univ_sdiff] using hsmall⟩
  choose K hK hKsmall using hK
  let g : Option ℕ → Z → ℝ≥0∞
    | none => fun _ => c
    | some n => (K n)ᶜ.indicator (fun _ => w n)
  have hgm (i : Option ℕ) : Measurable (g i) := by
    cases i with
    | none => exact measurable_const
    | some n => exact measurable_const.indicator (hK n).measurableSet.compl
  have hge (i : Option ℕ) : (∫⁻ z, g i z ^ 2 ∂σ) < b i := by
    cases i with
    | none => simpa [g,lintegral_const] using hcsmall
    | some n =>
      have heq : (fun z => g (some n) z ^ 2) =
          (K n)ᶜ.indicator (fun _ => (w n : ℝ≥0∞)^2) := by
        funext z
        by_cases hz : z ∈ (K n)ᶜ <;> simp [g,hz]
      rw [heq,lintegral_indicator (hK n).measurableSet.compl]
      simp only [lintegral_const,Measure.restrict_apply_univ]
      exact (mul_le_mul_right (hKsmall n).le _).trans_lt
        (by simpa only [mul_comm] using hdsmall n)
  obtain ⟨h,hh,hdom,henergy⟩ := exists_quadratic_sum_density σ g hgm
  let T : Set (FiniteMeasure Z) :=
    {v | v.mass ≤ c⁻¹ ∧ ∀ n, v (K n)ᶜ ≤ (w n)⁻¹}
  have hu : Tendsto (fun n => (w n)⁻¹) atTop (𝓝 0) := by
    simpa [w,Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ≥0)).comp (tendsto_add_atTop_nat 1)
  have hTc : IsCompact T :=
    isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le c⁻¹ hu hK (Or.inl inferInstance)
  refine ⟨T,h,hTc,hh,?_,?_⟩
  · rw [henergy]
    exact (ENNReal.tsum_le_tsum (fun i => (hge i).le)).trans_lt hbsum
  · intro v hv
    by_contra hn
    have hi : (∫⁻ z, h z ∂(v : Measure Z)) < 1 := lt_of_not_ge hn
    have hm : v.mass ≤ c⁻¹ := by
      have hb₀ : (∫⁻ z, g none z ∂(v : Measure Z)) ≤ 1 :=
        (show (∫⁻ z, g none z ∂(v : Measure Z)) ≤ ∫⁻ z, h z ∂(v : Measure Z)
          from lintegral_mono (hdom none)).trans hi.le
      have hb : (c : ℝ≥0∞) * (v : Measure Z) univ ≤ 1 := by
        simpa only [g,lintegral_const] using hb₀
      rw [← FiniteMeasure.ennreal_mass] at hb
      have hb' : c * v.mass ≤ 1 := by exact_mod_cast hb
      have he : v.mass ≤ 1 / c := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hb')
      simpa only [one_div] using he
    have ht (n : ℕ) : v (K n)ᶜ ≤ (w n)⁻¹ := by
      have hb := (lintegral_mono (hdom (some n)) (μ := (v : Measure Z))).trans hi.le
      change (∫⁻ z, (K n)ᶜ.indicator (fun _ => (w n : ℝ≥0∞)) z ∂(v : Measure Z)) ≤ 1 at hb
      rw [lintegral_indicator (hK n).measurableSet.compl,lintegral_const,
        Measure.restrict_apply_univ,← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hb
      have hb' : w n * v (K n)ᶜ ≤ 1 := by exact_mod_cast hb
      have he : v (K n)ᶜ ≤ 1 / w n := (le_div_iff₀ (hw n)).mpr (by simpa only [mul_comm] using hb')
      simpa only [one_div] using he
    exact hv ⟨hm,ht⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureFamilySubadditivity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square root of pointwise 2-modulus is subadditive. This is the
quantitative form needed when discarding measures outside a compact set. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_sqrt_eq_iInf {A Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) :
    (measureFamilyModulus A Z σ K) ^ (1/2 : ℝ) =
      ⨅ (h : Z → ℝ≥0∞) (_ : Measurable h)
        (_ : ∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)),
        (∫⁻ z, h z ^ 2 ∂σ) ^ (1/2 : ℝ) := by
  change (ENNReal.orderIsoRpow (1/2) (by norm_num))
    (⨅ (h : Z → ℝ≥0∞) (_ : Measurable h)
      (_ : ∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)), ∫⁻ z, h z^2 ∂σ) = _
  simp only [OrderIso.map_iInf,ENNReal.orderIsoRpow_apply]

lemma measureFamilyModulus_sqrt_subadditive {A Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (K : A → FiniteMeasure Z) (S T : Set A)
    (hcover : S ∪ T = univ) :
    (measureFamilyModulus A Z σ K) ^ (1/2 : ℝ) ≤
      (measureFamilyModulus S Z σ (fun a => K a.val)) ^ (1/2 : ℝ) +
      (measureFamilyModulus T Z σ (fun a => K a.val)) ^ (1/2 : ℝ) := by
  rw [measureFamilyModulus_sqrt_eq_iInf σ (fun a : S => K a.val),
    measureFamilyModulus_sqrt_eq_iInf σ (fun a : T => K a.val)]
  simp_rw [ENNReal.iInf_add,ENNReal.add_iInf]
  apply le_iInf
  intro h
  apply le_iInf
  intro hh
  apply le_iInf
  intro ha
  apply le_iInf
  intro g
  apply le_iInf
  intro hg
  apply le_iInf
  intro ga
  have hsum : ∀ a, 1 ≤ ∫⁻ z, h z+g z ∂(K a : Measure Z) := by
    intro a
    have he : a ∈ S ∪ T := hcover ▸ mem_univ a
    rcases he with has | hat
    · exact (ha ⟨a,has⟩).trans (lintegral_mono (fun _ => le_self_add))
    · exact (ga ⟨a,hat⟩).trans (lintegral_mono (fun _ => le_add_self))
  apply (ENNReal.rpow_le_rpow
    (measureFamilyModulus_le_admissible σ K (hh.add hg) hsum) (by norm_num)).trans
  simpa only [Pi.add_apply,ENNReal.rpow_two] using
    ENNReal.lintegral_Lp_add_le (μ := σ) hh.aemeasurable hg.aemeasurable (p := (2 : ℝ)) (by norm_num)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureFamilyCompactLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact ambient family retains any prescribed strict modulus
threshold. This is the tightness localization for the Borel-image argument. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_modulus_localization
    {A Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] (K : A → FiniteMeasure Z)
    {c : ℝ≥0∞} (hc : c < measureFamilyModulus A Z σ K) :
    ∃ T : Set (FiniteMeasure Z), IsCompact T ∧
      c < measureFamilyModulus {a | K a ∈ T} Z σ (fun a => K a.val) := by
  have hr := ENNReal.rpow_lt_rpow hc (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨δ,hδ,hδlt⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hr
  have he : (0 : ℝ≥0∞) < (δ : ℝ≥0∞)^2 := by positivity
  obtain ⟨T,h,hT,hh,henergy,hcontrol⟩ := exists_compact_finiteMeasure_control σ he
  refine ⟨T,hT,?_⟩
  let S : Set A := {a | K a ∈ T}
  have hbad : measureFamilyModulus (Sᶜ : Set A) Z σ (fun a => K a.val) < (δ : ℝ≥0∞)^2 := by
    exact (measureFamilyModulus_le_admissible σ (fun a : (Sᶜ : Set A) => K a.val) hh
      (fun a => hcontrol (K a.val) a.property)).trans_lt henergy
  have hbadroot : (measureFamilyModulus (Sᶜ : Set A) Z σ (fun a => K a.val)) ^ (1/2 : ℝ) ≤ δ := by
    have hb := ENNReal.rpow_le_rpow hbad.le (by norm_num : (0 : ℝ) ≤ 1/2)
    simpa only [← ENNReal.rpow_two,← ENNReal.rpow_mul,
      show (2 : ℝ)*(1/2)=1 by norm_num,ENNReal.rpow_one] using hb
  by_contra hn
  have hgood : measureFamilyModulus S Z σ (fun a => K a.val) ≤ c := le_of_not_gt hn
  have hsplit := measureFamilyModulus_sqrt_subadditive σ K S Sᶜ (union_compl_self S)
  have hbound : (measureFamilyModulus A Z σ K) ^ (1/2 : ℝ) ≤ c ^ (1/2 : ℝ) + δ :=
    hsplit.trans (add_le_add (ENNReal.rpow_le_rpow hgood (by norm_num)) hbadroot)
  exact (not_lt_of_ge hbound) hδlt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PositiveMassCompactLocalization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! If zero is absent from the image, compact localization can also retain
a positive lower mass. The resulting compact family avoids zero. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_nonzero_modulus_localization
    {A Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] (K : A → FiniteMeasure Z)
    (hK : ∀ a, K a ≠ 0) {c : ℝ≥0∞}
    (hc : c < measureFamilyModulus A Z σ K) :
    ∃ T : Set (FiniteMeasure Z), IsCompact T ∧ (0 : FiniteMeasure Z) ∉ T ∧
      c < measureFamilyModulus {a | K a ∈ T} Z σ (fun a => K a.val) := by
  obtain ⟨T,hT,hmod⟩ := exists_compact_modulus_localization σ K hc
  let B : Set A := {a | K a ∈ T}
  let S : ℕ → Set B := fun n => {a | 1/((n:ℝ)+1) ≤ ((K a.val).mass : ℝ)}
  have hm : Monotone S := by
    intro n m hnm a ha
    have hnm' : (n:ℝ)+1 ≤ (m:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    exact (one_div_le_one_div_of_le (by positivity : 0 < (n:ℝ)+1) hnm').trans ha
  have hu : ∀ a : B, ∃ n, a ∈ S n := by
    intro a
    have hmass : 0 < ((K a.val).mass : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr ((FiniteMeasure.mass_nonzero_iff (K a.val)).mpr (hK a.val)))
    obtain ⟨n,hn⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hmass)).exists
    exact ⟨n,hn.le⟩
  rw [measureFamilyModulus_iUnion σ (fun a : B => K a.val) S hm hu] at hmod
  obtain ⟨N,hN⟩ := lt_iSup_iff.mp hmod
  let T' : Set (FiniteMeasure Z) := T ∩ {v | 1/((N:ℝ)+1) ≤ (v.mass : ℝ)}
  have hT' : IsCompact T' := hT.inter_right
    (isClosed_le continuous_const (NNReal.continuous_coe.comp FiniteMeasure.continuous_mass))
  have hz : (0 : FiniteMeasure Z) ∉ T' := by
    intro h
    have hp : 0 < 1/((N:ℝ)+1) := by positivity
    have hn : 1/((N:ℝ)+1) ≤ 0 := by simpa using h.2
    exact (not_le_of_gt hp) hn
  refine ⟨T',hT',hz,?_⟩
  have heq : range (fun a : S N => K a.val.val) =
      range (fun a : {a | K a ∈ T'} => K a.val) := by
    ext v
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨⟨a.val.val,a.val.property,a.property⟩,rfl⟩
    · rintro ⟨a,rfl⟩
      exact ⟨⟨⟨a.val,a.property.1⟩,a.property.2⟩,rfl⟩
  exact hN.trans_eq (measureFamilyModulus_eq_of_range_eq σ _ _ heq)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BorelImageCompactModulus
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact inner approximation for the pointwise modulus of a Borel image.
The compatible Polish topology is refined only after compact localization. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_subfamily_of_borel_image
    {A Z : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] (K : A → FiniteMeasure Z) (hKm : Measurable K)
    (hK : ∀ a, K a ≠ 0) {c : ℝ≥0∞}
    (hc : c < measureFamilyModulus A Z σ K) :
    ∃ S : Set (FiniteMeasure Z), IsCompact S ∧ S ⊆ range K ∧
      c < measureFamilyModulus S Z σ (fun v => v.val) := by
  classical
  obtain ⟨T,hT,hTz,hmod⟩ := exists_compact_nonzero_modulus_localization σ K hK hc
  let B : Set A := {a | K a ∈ T}
  have hBm : MeasurableSet B := hKm (compact_finiteMeasure_measurableSet hT)
  let : StandardBorelSpace B := hBm.standardBorel
  let := upgradeStandardBorel B
  let : BorelSpace T := compact_finiteMeasure_borel hT
  let : PolishSpace T := compact_finiteMeasure_polish hT
  let f : B → T := fun a => ⟨K a.val,a.property⟩
  have hfm : Measurable f := (hKm.comp measurable_subtype_coe).subtype_mk
  obtain ⟨t,hle,hfc,ht⟩ := hfm.exists_continuous
  have hbe : @BorelSpace B t inferInstance := by
    constructor
    rw [eq_borel_upgradeStandardBorel B,borel_eq_borel_of_le ht _ hle]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : TopologicalSpace B := t
  let : PolishSpace B := ht
  let : BorelSpace B := hbe
  let := upgradeIsCompletelyMetrizable B
  cases isEmpty_or_nonempty B with
  | inl hB =>
    have hz := measureFamilyModulus_zero_of_isEmpty σ (fun a : B => K a.val)
    rw [hz] at hmod
    exact (not_lt_of_ge bot_le hmod).elim
  | inr hB =>
    obtain ⟨S,hS,hSf,hSc⟩ := exists_compact_subfamily_of_continuous_image σ hT hTz f hfc hmod
    refine ⟨S,hS,?_,hSc⟩
    rintro v hv
    obtain ⟨a,ha⟩ := hSf hv
    exact ⟨a.val,ha⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_CompactMeasureDuality
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact measure-image dual conclusion for a compact family avoiding
zero, including support in that family and the original squared-norm bound. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma compact_measure_image_duality
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    (c : ℝ≥0) (hc : 0 < c)
    (hmod : (c : ℝ≥0∞) < measureFamilyModulus S Z σ (fun v => v.val)) :
    ∃ (η : ProbabilityMeasure (FiniteMeasure Z)) (q : Z → ℝ≥0∞),
      Measurable q ∧ (∀ᵐ v ∂(η : Measure (FiniteMeasure Z)), v ∈ S) ∧
      (∀ E, MeasurableSet E →
        (∫⁻ v, (v : Measure Z) E ∂(η : Measure (FiniteMeasure Z))) = σ.withDensity q E) ∧
      (∫⁻ z, q z^2 ∂σ) ≤ (c : ℝ≥0∞)⁻¹ := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hcr : (0 : ℝ) < c := hc
  have hsqrt : 0 < Real.sqrt (c : ℝ) := Real.sqrt_pos.mpr hcr
  have hsq : (Real.sqrt (c : ℝ))^2 = c := Real.sq_sqrt c.coe_nonneg
  have hm : ENNReal.ofReal ((Real.sqrt (c : ℝ))^2) <
      measureFamilyModulus S Z σ (fun v => v.val) := by simpa only [hsq,ENNReal.ofReal_coe_nnreal] using hmod
  obtain ⟨P,q,hq,hbar,he⟩ :=
    exists_compact_measure_density_plan σ hS hne hz (Real.sqrt (c : ℝ)) hsqrt hm
  have hval : Measurable (fun v : S => v.val) := measurable_subtype_coe
  let η : ProbabilityMeasure (FiniteMeasure Z) := P.map (f := (fun v : S => v.val)) (by first | exact hval.aemeasurable | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  refine ⟨η,q,hq,?_,?_,?_⟩
  · change ∀ᵐ v ∂(P : Measure S).map (fun v : S => v.val), v ∈ S
    apply (ae_map_iff hval.aemeasurable (compact_finiteMeasure_measurableSet hS)).mpr
    exact Eventually.of_forall (fun v => v.property)
  · intro E hE
    change (∫⁻ v, (v : Measure Z) E ∂(P : Measure S).map (fun v : S => v.val)) = _
    have hev : Measurable (fun v : FiniteMeasure Z => (v : Measure Z) E) :=
      (Measure.measurable_coe hE).comp measurable_subtype_coe
    rw [lintegral_map hev hval]
    rw [← compactMeasureBarycenter_apply P hE,hbar]
  · refine he.trans_eq ?_
    rw [inv_pow,hsq,ENNReal.ofReal_inv_of_pos hcr,ENNReal.ofReal_coe_nnreal]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasureImageDualityProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact p=2 Borel-image consequence of ADMS Theorem5.1 and Corollary5.2.
All compact approximation, separation, barycenter and null-family steps are
constructed. No duality input is assumed in this proof. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureImageDuality
    (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z] :
    MeasureImageDuality A Z := by
  classical
  intro K hK σ hσ c hc hmod
  let : IsFiniteMeasure σ := hσ
  let : MeasurableSingletonClass (FiniteMeasure Z) :=
    ⟨fun v => compact_finiteMeasure_measurableSet isCompact_singleton⟩
  by_cases hz : (0 : FiniteMeasure Z) ∈ range K
  · let η : ProbabilityMeasure (FiniteMeasure Z) := ⟨Measure.dirac 0,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
    refine ⟨η,fun _ => 0,measurable_const,?_,?_,?_⟩
    · change ∀ᵐ v ∂Measure.dirac (0 : FiniteMeasure Z), v ∈ range K
      filter_upwards [ae_eq_dirac (fun v : FiniteMeasure Z => v)] with v hv
      rw [hv]
      exact hz
    · intro E hE
      change (∫⁻ v : FiniteMeasure Z, (v : Measure Z) E ∂Measure.dirac 0) = σ.withDensity (fun _ => 0) E
      simp
    · simp
  · have hnonzero : ∀ a, K a ≠ 0 := by
      intro a ha
      exact hz ⟨a,ha⟩
    obtain ⟨S,hS,hSK,hSm⟩ := exists_compact_subfamily_of_borel_image σ K hK hnonzero hmod
    have hSn : S.Nonempty := by
      by_contra hn
      let : IsEmpty S := ⟨fun x => hn ⟨x.val,x.property⟩⟩
      rw [measureFamilyModulus_zero_of_isEmpty] at hSm
      exact (not_lt_of_ge bot_le) hSm
    have hSz : (0 : FiniteMeasure Z) ∉ S := fun h => hz (hSK h)
    obtain ⟨η,q,hq,hsupp,hbar,he⟩ := compact_measure_image_duality σ hS hSn hSz c hc hSm
    exact ⟨η,q,hq,hsupp.mono (fun v hv => hSK hv),hbar,he⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_GDeltaPolish
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A G-delta subset of a Polish space is Polish. It embeds as the closed
set of compatible tuples in the product of its open supersets. -/
open Set Function Topology
noncomputable section
namespace CircleDomainRigidity

lemma polishSpace_of_isGDelta {X : Type*} [TopologicalSpace X] [PolishSpace X]
    {s : Set X} (hs : IsGδ s) : PolishSpace s := by
  obtain ⟨U, hU, rfl⟩ := hs.eq_iInter_nat
  let : ∀ n, PolishSpace (U n) := fun n => (hU n).polishSpace
  let e : (⋂ n, U n) → X × (∀ n, U n) :=
    fun x => (x.val, fun n => ⟨x.val, mem_iInter.mp x.property n⟩)
  have hec : Continuous e := by fun_prop
  have he : IsEmbedding e :=
    .of_comp hec continuous_fst (show IsEmbedding (Prod.fst ∘ e) from .subtypeVal)
  have hr : range e = {p : X × (∀ n, U n) | ∀ n, p.1 = (p.2 n).val} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact fun _ => rfl
    · intro hp
      refine ⟨⟨p.1, mem_iInter.mpr (fun n => ?_)⟩, ?_⟩
      · rw [hp n]
        exact (p.2 n).property
      · apply Prod.ext
        · rfl
        · funext n
          exact Subtype.ext (hp n)
  have hc : IsClosed (range e) := by
    rw [hr, ofPred_forall]
    exact isClosed_iInter (fun n => isClosed_eq continuous_fst
      ((continuous_apply n).comp continuous_snd |>.subtype_val))
  exact (show IsClosedEmbedding e from ⟨he, hc⟩).polishSpace

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ProbabilityMeasureEmbedding
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable embedding of point spaces induces a measurable embedding
of probability laws. Its image is exactly the laws supported on the point image. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

lemma measurable_probability_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {f : A → B} (hf : Measurable f) :
    Measurable (fun μ : ProbabilityMeasure A => μ.map (f := f) hf.aemeasurable) := by
  exact ((Measure.measurable_map f hf).comp measurable_subtype_coe).subtype_mk

lemma probability_map_leftInverse {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {f : A → B} {g : B → A} (hf : Measurable f) (hg : Measurable g) (h : LeftInverse g f) :
    LeftInverse (fun ν : ProbabilityMeasure B => ν.map (f := g) hg.aemeasurable)
      (fun μ : ProbabilityMeasure A => μ.map (f := f) hf.aemeasurable) := by
  intro μ
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ : Measure A).map f).map g = (μ : Measure A)
  rw [Measure.map_map hg hf]
  have he : g ∘ f = id := funext h
  rw [he, Measure.map_id]

lemma range_probability_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Nonempty A] {f : A → B} (hf : MeasurableEmbedding f) :
    range (fun μ : ProbabilityMeasure A => μ.map (f := f) hf.measurable.aemeasurable) =
      {ν : ProbabilityMeasure B | (ν : Measure B) (range f)ᶜ = 0} := by
  ext ν
  constructor
  · rintro ⟨μ, rfl⟩
    change (μ : Measure A).map f (range f)ᶜ = 0
    rw [Measure.map_apply hf.measurable hf.measurableSet_range.compl]
    simp only [preimage_compl, preimage_range, compl_univ, measure_empty]
  · intro hν
    refine ⟨ν.map (f := hf.invFun) (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability), ?_⟩
    apply ProbabilityMeasure.toMeasure_injective
    change ((ν : Measure B).map hf.invFun).map f = (ν : Measure B)
    rw [Measure.map_map hf.measurable hf.measurable_invFun]
    have ha : ∀ᵐ b ∂(ν : Measure B), b ∈ range f := by
      simpa only [mem_compl_iff, not_not] using measure_eq_zero_iff_ae_notMem.mp hν
    have he : (f ∘ hf.invFun) =ᵐ[(ν : Measure B)] id := by
      filter_upwards [ha] with b hb
      obtain ⟨a, rfl⟩ := hb
      change f (hf.invFun (f a)) = f a
      rw [hf.leftInverse_invFun a]
    rw [Measure.map_congr he, Measure.map_id]

lemma measurableEmbedding_probability_map {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [Nonempty A]
    {f : A → B} (hf : MeasurableEmbedding f) :
    MeasurableEmbedding (fun μ : ProbabilityMeasure A => μ.map (f := f) hf.measurable.aemeasurable) := by
  apply MeasurableEmbedding.of_measurable_inverse (measurable_probability_map hf.measurable)
  · rw [range_probability_map hf]
    exact ((Measure.measurable_coe hf.measurableSet_range.compl).comp measurable_subtype_coe)
      (measurableSet_singleton 0)
  · exact measurable_probability_map hf.measurable_invFun
  · exact probability_map_leftInverse hf.measurable hf.measurable_invFun hf.leftInverse_invFun

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ProbabilityTopologicalEmbedding
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak push-forward along an embedding reflects convergence. The proof
uses the open-set form of portmanteau and the induced topology on the point space. -/
open Set Function Filter MeasureTheory TopologicalSpace Topology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma isEmbedding_probability_map
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
    [MetrizableSpace B] [FirstCountableTopology (ProbabilityMeasure B)]
    {f : A → B} (hf : IsEmbedding f) (hfm : MeasurableEmbedding f) :
    IsEmbedding (fun μ : ProbabilityMeasure A => μ.map (f := f) hfm.measurable.aemeasurable) := by
  let F : ProbabilityMeasure A → ProbabilityMeasure B := fun μ => μ.map (f := f) hfm.measurable.aemeasurable
  have hFc : Continuous F := ProbabilityMeasure.continuous_map hf.continuous
  apply IsEmbedding.mk' F
  · intro μ ν h
    apply ProbabilityMeasure.toMeasure_injective
    exact hfm.map_injective (congrArg ProbabilityMeasure.toMeasure h)
  · intro μ
    apply le_antisymm
    · change Tendsto id (comap F (𝓝 (F μ))) (𝓝 μ)
      apply tendsto_of_forall_isOpen_le_liminf'
      intro U hU
      obtain ⟨V, hV, hVU⟩ := hf.isInducing.isOpen_iff.mp hU
      have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
        (show Tendsto F (comap F (𝓝 (F μ))) (𝓝 (F μ)) from tendsto_comap) hV
      simpa only [id_eq, F, ProbabilityMeasure.toMeasure_map,
        Measure.map_apply hf.continuous.measurable hV.measurableSet, hVU] using h
    · exact hFc.continuousAt.le_comap

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_SupportedProbabilityGDelta
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Laws supported on a G-delta form a G-delta in the weak topology.
Closed-set evaluation is upper semicontinuous by portmanteau. -/
open Set Function Filter MeasureTheory Topology
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma isGDelta_probability_null_closed
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] {C : Set X} (hC : IsClosed C) :
    IsGδ {μ : ProbabilityMeasure X | (μ : Measure X) C = 0} := by
  have hsc : UpperSemicontinuous (fun μ : ProbabilityMeasure X => (μ : Measure X) C) :=
    upperSemicontinuous_iff_limsup_le.mpr (fun μ =>
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto tendsto_id hC)
  have heq : {μ : ProbabilityMeasure X | (μ : Measure X) C = 0} =
      ⋂ n : ℕ, {μ : ProbabilityMeasure X |
        (μ : Measure X) C < ENNReal.ofReal (1 / (n + 1 : ℝ))} := by
    ext μ
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h n
      rw [h]
      exact ENNReal.ofReal_pos.mpr (by positivity)
    · intro h
      apply le_antisymm _ zero_le
      have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
        simpa only [ENNReal.ofReal_zero, Function.comp_def] using
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact ge_of_tendsto' ht (fun n => (h n).le)
  rw [heq]
  exact IsGδ.iInter_of_isOpen (fun n => hsc.isOpen_preimage _)

lemma isGDelta_supported_probabilities
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] {S : Set X} (hS : IsGδ S) :
    IsGδ {μ : ProbabilityMeasure X | (μ : Measure X) Sᶜ = 0} := by
  obtain ⟨U, hU, rfl⟩ := hS.eq_iInter_nat
  have heq : {μ : ProbabilityMeasure X | (μ : Measure X) (⋂ n, U n)ᶜ = 0} =
      ⋂ n, {μ : ProbabilityMeasure X | (μ : Measure X) (U n)ᶜ = 0} := by
    ext μ
    simp only [mem_ofPred_eq, mem_iInter, compl_iInter, measure_iUnion_null_iff]
  rw [heq]
  exact IsGδ.iInter (fun n => isGDelta_probability_null_closed (hU n).isClosed_compl)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_PolishProbabilityProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weak probability laws on a Polish space are Polish, with the
measure-evaluation Borel structure. Embed the point space in the Hilbert cube;
the laws supported on its G-delta image form a G-delta in the compact law space. -/
open Set Function Filter MeasureTheory TopologicalSpace Topology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma polishProbabilityLaws (X : Type*) [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] : PolishProbabilityLaws X := by
  classical
  cases isEmpty_or_nonempty X with
  | inl hX => exact ⟨compact_probability_polish X, compact_probability_borel X⟩
  | inr hX =>
    let : MetricSpace X := metrizableSpaceMetric X
    obtain ⟨f, hf⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
    have hfm : MeasurableEmbedding f := hf.continuous.measurableEmbedding hf.injective
    let : BorelSpace (ProbabilityMeasure (ℕ → unitInterval)) := compact_probability_borel _
    let : PolishSpace (ProbabilityMeasure (ℕ → unitInterval)) := compact_probability_polish _
    have hF : IsEmbedding (fun μ : ProbabilityMeasure X => μ.map (f := f) hfm.measurable.aemeasurable) :=
      isEmbedding_probability_map hf hfm
    have hr : IsGδ (range (fun μ : ProbabilityMeasure X => μ.map (f := f) hfm.measurable.aemeasurable)) := by
      rw [range_probability_map hfm]
      exact isGDelta_supported_probabilities (isGDelta_range_embedding hf)
    let : PolishSpace (range (fun μ : ProbabilityMeasure X => μ.map (f := f) hfm.measurable.aemeasurable)) :=
      polishSpace_of_isGDelta hr
    have hp : PolishSpace (ProbabilityMeasure X) := hF.toHomeomorph.isClosedEmbedding.polishSpace
    refine ⟨hp, ?_⟩
    have hlo : (inferInstance : MeasurableSpace (ProbabilityMeasure X)) ≤
        borel (ProbabilityMeasure X) := by
      have h : @Measurable (ProbabilityMeasure X) (Measure X)
          (borel (ProbabilityMeasure X)) inferInstance (fun μ => (μ : Measure X)) := by
        let : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
        let : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
        exact measurable_measure_of_continuous_probability continuous_id
      exact h.comap_le
    have hup : borel (ProbabilityMeasure X) ≤
        (inferInstance : MeasurableSpace (ProbabilityMeasure X)) := by
      rw [hF.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
      exact (measurable_probability_map hfm.measurable).comap_le
    exact ⟨le_antisymm hlo hup⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_FiniteMeasureCoordinates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many measurable evaluations distinguish finite measures.
Finite intersections of a generating sequence form the required pi system. -/
open Set Function MeasureTheory MeasurableSpace
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity
variable (Z : Type*) [MeasurableSpace Z] [CountablyGenerated Z]

lemma measurableSet_measureCoordinateSet (s : Finset ℕ) :
    MeasurableSet (measureCoordinateSet Z s) := by
  exact MeasurableSet.biInter s.finite_toSet.countable (fun n _ => measurableSet_natGeneratingSequence n)

lemma measureCoordinateSet_union (s t : Finset ℕ) :
    measureCoordinateSet Z (s ∪ t) = measureCoordinateSet Z s ∩ measureCoordinateSet Z t := by
  ext x
  simp only [measureCoordinateSet, mem_iInter, Finset.mem_union, mem_inter_iff]
  aesop

lemma measureCoordinateSet_generates :
    generateFrom (range (measureCoordinateSet Z)) = (inferInstance : MeasurableSpace Z) := by
  apply le_antisymm
  · apply generateFrom_le
    rintro _ ⟨s, rfl⟩
    exact measurableSet_measureCoordinateSet Z s
  · apply (generateFrom_natGeneratingSequence Z).symm.le.trans
    apply generateFrom_mono
    rintro _ ⟨n, rfl⟩
    refine ⟨{n}, ?_⟩
    simp only [measureCoordinateSet, Finset.mem_singleton, iInter_iInter_eq_left]

lemma measurable_finiteMeasureCoordinates : Measurable (finiteMeasureCoordinates Z) := by
  apply Measurable.of_eval
  intro s
  exact (Measure.measurable_coe (measurableSet_measureCoordinateSet Z s)).comp
    measurable_subtype_coe

lemma injective_finiteMeasureCoordinates : Injective (finiteMeasureCoordinates Z) := by
  intro μ ν h
  apply FiniteMeasure.toMeasure_injective
  apply ext_of_generate_finite (range (measureCoordinateSet Z))
    (measureCoordinateSet_generates Z).symm
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ _
    exact ⟨s ∪ t, measureCoordinateSet_union Z s t⟩
  · rintro _ ⟨s, rfl⟩
    exact congrFun h s
  · have hh := congrFun h ∅
    simpa only [finiteMeasureCoordinates, measureCoordinateSet, Finset.notMem_empty,
      iInter_of_empty, iInter_univ] using hh

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurableBaireBranch
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable least-child choice constructs a Baire branch when each
finite-prefix membership set is measurable for the completed measure. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem exists_nullMeasurable_baire_branch {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : List ℕ → Set X)
    (hA : ∀ s, NullMeasurableSet (A s) μ)
    (hroot : A [] = univ) (hchild : ∀ s, A s ⊆ ⋃ k, A (k::s)) :
    ∃ b : X → (ℕ → ℕ), NullMeasurable b μ ∧
      ∀ x n, x ∈ A (PiNat.res (b x) n) := by
  classical
  let : MeasurableSpace (List ℕ) := ⊤
  have hAm (s : List ℕ) : @MeasurableSet (NullMeasurableSpace X μ) _ (A s) := hA s
  let p (s : List ℕ) (x : NullMeasurableSpace X μ) (k : ℕ) : Prop :=
    (x ∈ A s ∧ x ∈ A (k::s)) ∨ (x ∉ A s ∧ k = 0)
  have hp (s : List ℕ) (x : NullMeasurableSpace X μ) : ∃ k, p s x k := by
    by_cases hx : x ∈ A s
    · obtain ⟨k,hk⟩ := mem_iUnion.mp (hchild s hx)
      exact ⟨k,Or.inl ⟨hx,hk⟩⟩
    · exact ⟨0,Or.inr ⟨hx,rfl⟩⟩
  let next (s : List ℕ) (x : NullMeasurableSpace X μ) : ℕ := Nat.find (hp s x)
  have hnext (s : List ℕ) : Measurable (next s) := by
    apply measurable_find (hp s)
    intro k
    by_cases hk : k = 0
    · convert ((hAm s).inter (hAm (k::s))).union (hAm s).compl using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      simp only [p,hk,and_true,mem_union,mem_ofPred_eq]
      rfl
    · convert (hAm s).inter (hAm (k::s)) using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      simp only [p,hk,and_false,or_false,mem_ofPred_eq]
      rfl
  have hchosen (s : List ℕ) (x : NullMeasurableSpace X μ) (hx : x ∈ A s) :
      x ∈ A (next s x :: s) := by
    rcases Nat.find_spec (hp s x) with h | h
    · exact h.2
    · exact (h.1 hx).elim
  have hnextJoint : Measurable (fun q : List ℕ × NullMeasurableSpace X μ => next q.1 q.2) :=
    measurable_from_prod_countable_right hnext
  let state : ℕ → NullMeasurableSpace X μ → List ℕ :=
    Nat.rec (fun _ => []) (fun _ q x => next (q x) x :: q x)
  have hstate (n : ℕ) : Measurable (state n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      exact (measurable_of_countable (fun q : ℕ × List ℕ => q.1::q.2)).comp
        ((hnextJoint.comp (ih.prodMk measurable_id)).prodMk ih)
  have hinside (n : ℕ) (x : NullMeasurableSpace X μ) : x ∈ A (state n x) := by
    induction n with
    | zero => change x ∈ A []; rw [hroot]; trivial
    | succ n ih => exact hchosen (state n x) x ih
  let b (x : NullMeasurableSpace X μ) (n : ℕ) : ℕ := next (state n x) x
  have hb : Measurable b := Measurable.of_eval (fun n =>
    hnextJoint.comp ((hstate n).prodMk measurable_id))
  have hres (x : NullMeasurableSpace X μ) (n : ℕ) : PiNat.res (b x) n = state n x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change b x n :: PiNat.res (b x) n = b x n :: state n x
      rw [ih]
  refine ⟨b,hb,?_⟩
  intro x n
  exact (congrArg (fun s : List ℕ => x ∈ A s)
    (hres (show NullMeasurableSpace X μ from x) n)).mpr
    (hinside n (show NullMeasurableSpace X μ from x))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_BaireRightInverse
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous surjection from Baire space has a right inverse
measurable for any fixed completed finite Borel measure. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem exists_nullMeasurable_baire_rightInverse {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (g : (ℕ → ℕ) → X) (hg : Continuous g) (hsurj : Surjective g) :
    ∃ b : X → (ℕ → ℕ), NullMeasurable b μ ∧ ∀ x, g (b x) = x := by
  let A : List ℕ → Set X := fun s => g '' baireWordCylinder s
  have hA (s : List ℕ) : NullMeasurableSet (A s) μ :=
    nullMeasurableSet_analytic_finite μ ((isOpen_baireWordCylinder s).analyticSet_image hg)
  have hroot : A [] = univ := by
    simp only [A,baireWordCylinder_nil,image_univ,hsurj.range_eq]
  have hchild (s : List ℕ) : A s ⊆ ⋃ k, A (k::s) := by
    dsimp only [A]
    rw [← image_iUnion,baireWordCylinder_children]
  obtain ⟨b,hb,hbranch⟩ := exists_nullMeasurable_baire_branch μ A hA hroot hchild
  refine ⟨b,hb,?_⟩
  intro x
  symm
  apply eq_of_prefix_closures hg
  intro n
  have hx := hbranch x n
  have he : baireWordCylinder (PiNat.res (b x) n) = PiNat.cylinder (b x) n := by
    rw [PiNat.cylinder_eq_res]
    ext c
    simp only [baireWordCylinder,PiNat.res_length,mem_ofPred_eq]
  change x ∈ g '' baireWordCylinder (PiNat.res (b x) n) at hx
  exact subset_closure (he ▸ hx)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_BaireRangeSection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A completed-measure section on the range of a continuous Baire map.
The values off the range play no role in the lifting application. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

theorem exists_nullMeasurable_baire_rangeSection {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (g : (ℕ → ℕ) → X) (hg : Continuous g) :
    ∃ b : X → (ℕ → ℕ), NullMeasurable b μ ∧ ∀ x ∈ range g, g (b x) = x := by
  let A : List ℕ → Set X := fun s => g '' baireWordCylinder s ∪ (range g)ᶜ
  have hr : NullMeasurableSet (range g) μ := nullMeasurableSet_baire_image_finite μ g hg
  have hA (s : List ℕ) : NullMeasurableSet (A s) μ :=
    (nullMeasurableSet_analytic_finite μ
      ((isOpen_baireWordCylinder s).analyticSet_image hg)).union hr.compl
  have hroot : A [] = univ := by
    simp only [A, baireWordCylinder_nil, image_univ, union_compl_self]
  have hchild (s : List ℕ) : A s ⊆ ⋃ k, A (k::s) := by
    rintro x (hx | hx)
    · have : x ∈ ⋃ k, g '' baireWordCylinder (k::s) := by
        rw [← image_iUnion, baireWordCylinder_children]
        exact hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp this
      exact mem_iUnion.mpr ⟨k, Or.inl hk⟩
    · exact mem_iUnion.mpr ⟨0, Or.inr hx⟩
  obtain ⟨b, hb, hbranch⟩ := exists_nullMeasurable_baire_branch μ A hA hroot hchild
  refine ⟨b, hb, ?_⟩
  intro x hx
  symm
  apply eq_of_prefix_closures hg
  intro n
  have hh := (hbranch x n).resolve_right (not_not.mpr hx)
  have he : baireWordCylinder (PiNat.res (b x) n) = PiNat.cylinder (b x) n := by
    rw [PiNat.cylinder_eq_res]
    ext c
    simp only [baireWordCylinder, PiNat.res_length, mem_ofPred_eq]
  exact subset_closure (he ▸ hh)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_MeasurableRangeSection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable map from a standard Borel space admits a section on its
image measurable for any fixed completed finite Borel measure. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

theorem exists_nullMeasurable_rangeSection
    {A Y : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (K : A → Y) (hK : Measurable K) (μ : Measure Y) [IsFiniteMeasure μ] :
    ∃ s : Y → A, NullMeasurable s μ ∧ ∀ y ∈ range K, K (s y) = y := by
  let := upgradeStandardBorel A
  let graphMap : A → A × Y := fun a => (a, K a)
  have hg : AnalyticSet (range graphMap) := by
    simpa only [image_univ, graphMap, id_eq] using
      (MeasurableSet.univ.analyticSet_image (measurable_id.prodMk hK))
  rw [AnalyticSet] at hg
  obtain ⟨q, hq, hqr⟩ := hg.resolve_left (range_nonempty graphMap).ne_empty
  obtain ⟨b, hb, hbs⟩ := exists_nullMeasurable_baire_rangeSection μ
    (fun z => (q z).2) hq.snd
  refine ⟨fun y => (q (b y)).1, hq.fst.measurable.comp_nullMeasurable hb, ?_⟩
  intro y hy
  have hyr : y ∈ range (fun z => (q z).2) := by
    obtain ⟨a, rfl⟩ := hy
    have ha : graphMap a ∈ range q := hqr ▸ mem_range_self a
    obtain ⟨z, hz⟩ := ha
    exact ⟨z, congrArg Prod.snd hz⟩
  have hmem : q (b y) ∈ range graphMap := hqr.symm ▸ mem_range_self (b y)
  obtain ⟨a, ha⟩ := hmem
  have hfirst := congrArg Prod.fst ha
  have hsecond := congrArg Prod.snd ha
  change a = (q (b y)).1 at hfirst
  change K a = (q (b y)).2 at hsecond
  change K (q (b y)).1 = y
  rw [← hfirst, hsecond, hbs y hyr]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_ProbabilityImageLifting
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lift a probability supported on the image of a standard Borel code map.
A measurable range section and countable measure evaluations suffice
as a target encoding, with no probability-space topology hypothesis. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

theorem exists_probability_lift_of_measurable_injection
    {A B Y : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y]
    (K : A → B) (hK : Measurable K) (e : B → Y) (he : Measurable e)
    (hinj : Injective e) (η : ProbabilityMeasure B)
    (hrange : ∀ᵐ v ∂(η : Measure B), v ∈ range K) :
    ∃ P : ProbabilityMeasure A, P.map (f := K) hK.aemeasurable = η := by
  have : Nonempty A := by
    obtain ⟨v, a, ha⟩ := hrange.exists
    exact ⟨a⟩
  obtain ⟨s, hs, hsection⟩ := exists_nullMeasurable_rangeSection
    (e ∘ K) (he.comp hK) ((η : Measure B).map e)
  have ht : AEMeasurable (s ∘ e) (η : Measure B) := hs.aemeasurable.comp_measurable he
  refine ⟨η.map (f := (s ∘ e)) (by first | exact ht | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability), ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  change ((η : Measure B).map (s ∘ e)).map K = (η : Measure B)
  rw [AEMeasurable.map_map_of_aemeasurable hK.aemeasurable ht]
  have hh : (K ∘ (s ∘ e)) =ᵐ[(η : Measure B)] id := by
    filter_upwards [hrange] with v hv
    apply hinj
    exact hsection (e v) (by obtain ⟨a, rfl⟩ := hv; exact mem_range_self a)
  rw [Measure.map_congr hh, Measure.map_id]

/-- The exact published probability-lifting input for finite-measure images. -/
theorem measurePlanLifting (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z] :
    MeasurePlanLifting A Z := by
  intro K hK η hrange
  let : MetricSpace (Finset ℕ → ENNReal) := TopologicalSpace.metrizableSpaceMetric _
  exact exists_probability_lift_of_measurable_injection K hK (finiteMeasureCoordinates Z)
    (measurable_finiteMeasureCoordinates Z) (injective_finiteMeasureCoordinates Z) η hrange

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_StandardBorelEmbedding
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the standard Borel property through a measurable embedding,
using a compatible Polish topology that makes its image closed. -/
open Set Function MeasureTheory Topology
noncomputable section
namespace CircleDomainRigidity

lemma standardBorel_of_measurableEmbedding
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B]
    {f : A → B} (hf : MeasurableEmbedding f) : StandardBorelSpace A := by
  obtain ⟨t, htB, htP, hclosed, _⟩ := hf.measurableSet_range.isClopenable'
  let : TopologicalSpace B := t
  let : BorelSpace B := htB
  let : PolishSpace B := htP
  let ta : TopologicalSpace A := TopologicalSpace.induced f t
  let : TopologicalSpace A := ta
  have htop : IsClosedEmbedding f := ⟨⟨⟨rfl⟩, hf.injective⟩, hclosed⟩
  refine ⟨⟨ta, ?_, htop.polishSpace⟩⟩
  constructor
  change (inferInstance : MeasurableSpace A) = @borel A ta
  rw [borel_comap, ← BorelSpace.measurable_eq, hf.comap_eq]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_StandardBorelProbabilityProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Probability laws on a standard Borel space are standard Borel.
Embed the point space into Cantor space and identify the image of the
induced map on laws by its measurable support condition. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

lemma standardBorelProbabilityLaws (A : Type*) [MeasurableSpace A] [StandardBorelSpace A] :
    StandardBorelProbabilityLaws A := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hA =>
    have : IsEmpty (ProbabilityMeasure A) := ⟨fun μ => by
      have hm : (μ : Measure A) univ = 1 := measure_univ
      have hu : (univ : Set A) = ∅ := Set.eq_empty_of_isEmpty _
      rw [hu, measure_empty] at hm
      exact zero_ne_one hm⟩
    change StandardBorelSpace (ProbabilityMeasure A)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  | inr hA =>
    obtain ⟨f, hfm, hfi⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated A
    have hf : MeasurableEmbedding f := hfm.measurableEmbedding hfi
    let : BorelSpace (ProbabilityMeasure (ℕ → Bool)) := compact_probability_borel _
    let : PolishSpace (ProbabilityMeasure (ℕ → Bool)) := compact_probability_polish _
    exact standardBorel_of_measurableEmbedding (measurableEmbedding_probability_map hf)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_Conformal
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sphere conformality and circle-domain statements

The concrete Riemann-sphere charts define conformal equivalences,
round disks, and conformal removability. The two circle-domain statements
express unrestricted uniformization and rigidity under removability.
-/

noncomputable section

open Set
open scoped OnePoint

namespace CircleDomainRigidity

/-- The whole-sphere case of Koebe uniformization. -/
theorem circleDomainModel_univ :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f univ V :=
  ⟨univ, id, isCircleDomain_univ, isConformalEquivalence_id univ⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The published finite circle-uniformization input

Conway, *Functions of One Complex Variable II*, GTM 159 (1995),
Theorem 15.7.9, p. 106, gives circle uniformization of nondegenerate
finitely connected regions. `FiniteCircleUniformization` records only
its existence conclusion on the sphere, omitting normalization and
uniqueness. It is an explicit proposition parameter, not an axiom.

The complement components of a finite family of disjoint closed
connected sets are identified below. This checks the finiteness and
nondegeneracy hypotheses for completed surfaces, also after an arbitrary
sphere homeomorphism such as compact metric uniformization.
-/

open Set Function
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

theorem connectedComponentIn_finite_disjoint_closed
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (C : I → Set X) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    {i : I} {p : X} (hp : p ∈ C i) :
    connectedComponentIn (⋃ j, C j) p = C i := by
  classical
  let R : Set X := ⋃ j : {j : I // j ≠ i}, C j
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun j => hC j)
  have hCR : Disjoint (C i) R := by
    apply Set.disjoint_left.mpr
    intro x hx hxR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxR
    exact Set.disjoint_left.mp (hdisj j.property.symm) hx hj
  have hcover : (⋃ j, C j) ⊆ C i ∪ R := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  have hsub : connectedComponentIn (⋃ j, C j) p ⊆ C i := by
    have hs := isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (F := ⋃ j, C j) (x := p))
      (C i) R (hC i) hR ((connectedComponentIn_subset _ _).trans hcover)
      (by rw [hCR.inter_eq, inter_empty])
    rcases hs with h | h
    · exact h
    · exact fun x hx => (Set.disjoint_left.mp hCR hp
        (h (mem_connectedComponentIn (mem_iUnion.mpr ⟨i, hp⟩)))).elim
  exact hsub.antisymm ((hconn i).subset_connectedComponentIn hp (subset_iUnion C i))

theorem finite_nondegenerate_complement_of_disjoint_closed
    {I : Type*} [Finite I] {U : Set Sphere}
    (C : I → Set Sphere) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    (hneq : ∀ i, (C i).Nontrivial) (hcomp : Uᶜ = ⋃ i, C i) :
    FiniteNondegenerateComplement U := by
  have hcomponent {p : Sphere} (hp : p ∈ Uᶜ) :
      ∃ i, connectedComponentIn Uᶜ p = C i := by
    rw [hcomp] at hp ⊢
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨i, connectedComponentIn_finite_disjoint_closed C hC hconn hdisj hi⟩
  refine ⟨(finite_range C).subset ?_, ?_⟩
  · rintro B ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := hcomponent hp
    exact ⟨i, hi.symm⟩
  · intro p hp
    obtain ⟨i, hi⟩ := hcomponent hp
    simpa only [hi] using hneq i

theorem circle_model_of_finite_disjoint_complement
    (hfinite : FiniteCircleUniformization)
    {I : Type*} [Finite I] {U : Set Sphere} (hU : IsOpen U) (hconnU : IsConnected U)
    (C : I → Set Sphere) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    (hneq : ∀ i, (C i).Nontrivial) (hcomp : Uᶜ = ⋃ i, C i) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f U V := by
  by_cases hne : Uᶜ.Nonempty
  · exact hfinite U hU hconnU hne
      (finite_nondegenerate_complement_of_disjoint_closed C hC hconn hdisj hneq hcomp)
  · have hUniv : U = univ := by
      apply eq_univ_of_forall
      intro x
      by_contra hx
      exact hne ⟨x, hx⟩
    subst U
    exact circleDomainModel_univ

/-- After compact metric uniformization, the finite circle theorem gives
an actual bijection to a circle domain. It is conformal in every region
where the metric uniformization retained the original complex structure. -/
theorem circle_model_after_homeomorphism
    (hfinite : FiniteCircleUniformization)
    {I : Type*} [Finite I] {U W : Set Sphere} (hU : IsOpen U) (hconnU : IsConnected U)
    (C : I → Set Sphere) (hC : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsPreconnected (C i)) (hdisj : Pairwise (Disjoint on C))
    (hneq : ∀ i, (C i).Nontrivial) (hcomp : Uᶜ = ⋃ i, C i)
    (e : Sphere ≃ₜ Sphere) (hW : W ⊆ U) (he : IsConformalOn e W) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ BijOn f U V ∧ IsConformalOn f W ∧
        IsConformalEquivalence (f ∘ e.symm) (e '' U) V := by
  have hcomp' : (e '' U)ᶜ = ⋃ i, e '' C i := by
    rw [← e.image_compl, hcomp, image_iUnion]
  have hdisj' : Pairwise (Disjoint on fun i => e '' C i) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    have hzx : z = x := e.injective heq
    exact Set.disjoint_left.mp (hdisj hij) hx (hzx ▸ hz)
  obtain ⟨V, g, hV, hg⟩ := circle_model_of_finite_disjoint_complement hfinite
    (e.isOpenMap _ hU) (hconnU.image e e.continuous.continuousOn)
    (fun i => e '' C i) (fun i => e.isClosedMap _ (hC i))
    (fun i => (hconn i).image e e.continuous.continuousOn) hdisj'
    (fun i => (hneq i).image e.injective) hcomp'
  refine ⟨V, g ∘ e, hV, hg.bijOn.comp e.injective.bijOn_image,
    hg.1.comp he (fun p hp => ⟨p, hW hp, rfl⟩), ?_⟩
  have heq : (g ∘ e) ∘ e.symm = g := by funext p; simp only [Function.comp_apply, e.apply_symm_apply]
  simpa only [heq] using hg

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Uniformization_FiniteCompletionUniformization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite uniformization of the actual terminal-disk complement

The complementary components are exactly the closed physical terminal
caps. In particular they are finite and nondegenerate. The published
finite circle theorem therefore applies after compact metric
uniformization; the resulting map is conformal on the retained core.
-/

open Set Function Filter
open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem isConnected_openCompletedRegion {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i)))) :
    IsConnected (openCompletedRegion H) := by
  let S : Set ℂ := (⋃ i, closure (jordanInterior (H i)))ᶜ
  have hS : IsPreconnected S := isPreconnected_exterior_finite_jordanInteriors H hdisj
  have hinf : (∞ : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' S) := by
    have hmem : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ∈ S := by
      rw [coclosedCompact_eq_cocompact]
      exact (isCompact_iUnion fun i => isCompact_closure_jordanInterior (H i)).compl_mem_cocompact
    exact mem_closure_of_tendsto OnePoint.tendsto_coe_infty
      (hmem.mono fun z hz => ⟨z, hz, rfl⟩)
  have hsub : ((↑) : ℂ → Sphere) '' S ⊆ openCompletedRegion H := by
    rintro _ ⟨z, hz, rfl⟩ hb
    obtain ⟨i, x, hx, heq⟩ := mem_iUnion.mp hb
    have hxz : x = z := OnePoint.coe_injective heq
    exact hz (mem_iUnion.mpr ⟨i, hxz ▸ hx⟩)
  have hupper : openCompletedRegion H ⊆ closure (((↑) : ℂ → Sphere) '' S) := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
      apply subset_closure
      refine ⟨z, ?_, rfl⟩
      intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact hp (mem_iUnion.mpr ⟨i, z, hi, rfl⟩)
  refine ⟨⟨∞, ?_⟩, (hS.image _ OnePoint.continuous_coe.continuousOn).subset_closure hsub hupper⟩
  intro hb
  obtain ⟨i, z, _, heq⟩ := mem_iUnion.mp hb
  exact OnePoint.coe_ne_infty z heq

theorem uniformize_finite_completion_after_homeomorphism
    (hfinite : FiniteCircleUniformization)
    {I : Type*} [Finite I] (H : I → ℂ ≃ₜ ℂ)
    (hdisj : Pairwise (Disjoint on fun i => closure (jordanInterior (H i))))
    {W : Set Sphere} (e : Sphere ≃ₜ Sphere)
    (hW : W ⊆ openCompletedRegion H) (he : IsConformalOn e W) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ BijOn f (openCompletedRegion H) V ∧ IsConformalOn f W ∧
        IsConformalEquivalence (f ∘ e.symm) (e '' openCompletedRegion H) V := by
  apply circle_model_after_homeomorphism hfinite
    (isOpen_openCompletedRegion H) (isConnected_openCompletedRegion H hdisj)
    (fun i => closedTerminalCap (H i))
    (fun i => (isCompact_closedTerminalCap (H i)).isClosed)
    (fun i => isPreconnected_closedTerminalCap (H i)) (disjoint_closedTerminalCaps H hdisj)
    (fun i => nontrivial_closedTerminalCap (H i)) (compl_compl _) e hW he

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteJordanModelInput
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CircleDomainRigidity
open Set Function
open FiniteTransfer

lemma finiteCircleUniformization_jordanModels (hfinite : FiniteCircleUniformization) :
    FiniteJordanModelUniformization := by
  intro n H hd e
  obtain ⟨V,f,hV,_hb,_hc,hf⟩ :=
    uniformize_finite_completion_after_homeomorphism hfinite H hd (W := ∅) e
      (empty_subset _) (fun _ h => h.elim)
  exact ⟨V,f ∘ e.symm,hV,hf⟩

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskRayJordan
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compactified lifted ray bounds a Jordan disk after closing
along the positive boundary arc. Its entire filling stays in the unit disk. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem jordan_fill_subset_closed_unitDisk (H : ℂ ≃ₜ ℂ)
    (hf : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 1) :
    closure (jordanInterior H) ⊆ Metric.closedBall (0 : ℂ) 1 := by
  apply closed_jordanInterior_subset_of_unbounded_connected_compl H
  · simpa only [jordanInterior, Homeomorph.refl_apply, image_id,
      closure_ball _ one_ne_zero]
      using (isConnected_exterior_jordanInterior (Homeomorph.refl ℂ)).isPreconnected
  · intro hb
    apply NormedSpace.unbounded_univ ℝ ℂ
    have h := (isCompact_closedBall (0 : ℂ) 1).isBounded.union hb
    simpa only [union_compl_self] using h
  · intro z hz
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hf z hz)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskBoundarySide
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Away from the crosscut, a boundary arc of a filling has a whole relative
neighborhood in the closed disk on the same side. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem closed_disk_neighborhood_in_filling
    (H : ℂ ≃ₜ ℂ) (hU : jordanInterior H ⊆ Metric.ball 0 1)
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H))
    {ε : ℝ} (hε : 0 < ε)
    (hfront : Metric.ball x ε ∩ frontier (jordanInterior H) ⊆ Metric.sphere 0 1) :
    Metric.ball x ε ∩ Metric.closedBall 0 1 ⊆ closure (jordanInterior H) := by
  have hC : IsPreconnected (Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1) :=
    ((convex_ball x ε).inter (convex_ball (0 : ℂ) 1)).isPreconnected
  have hmiss : Disjoint (Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1)
      (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    intro z hz hf
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp (hfront ⟨hz.1, hf⟩)
    have hl : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz.2
    exact (ne_of_lt hl) hn
  have hsplit : Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ jordanInterior H ∨
      Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ (closure (jordanInterior H))ᶜ := by
    apply hC.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
    · exact disjoint_compl_right.mono_left subset_closure
    · intro z hz
      by_cases hi : z ∈ jordanInterior H
      · exact Or.inl hi
      · right
        intro hc
        apply Set.disjoint_left.mp hmiss hz
        rw [(jordanInterior_isOpen H).frontier_eq]
        exact ⟨hc, hi⟩
  have hinside : Metric.ball x ε ∩ Metric.ball (0 : ℂ) 1 ⊆ jordanInterior H := by
    rcases hsplit with hi | ho
    · exact hi
    · obtain ⟨z, hzB, hzU⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hx)
        (Metric.ball x ε) (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
      exact (ho ⟨hzB, hU hzU⟩ (subset_closure hzU)).elim
  intro z hz
  apply closure_mono hinside
  apply Metric.isOpen_ball.inter_closure
  simpa only [closure_ball _ one_ne_zero] using hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalDerivativeCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable local Lipschitz bounds that approximate the norm of the
actual differential. These are used to localize the published curve
coarea inequality without adding a weighted curve-coarea input. -/

open Set Filter Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

theorem exists_local_derivative_bound
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : x ∈ D) :
    ∃ U : Set ℂ, ∃ L : ℝ≥0, IsOpen U ∧ x ∈ U ∧ U ⊆ D ∧
      LipschitzOnWith L f U ∧ ∀ z ∈ U, (L : ℝ) ≤ ‖fderiv ℝ f z‖ + ε := by
  have hdf := (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).continuousAt
    (hD.mem_nhds hx)
  have hnear : {z | ‖fderiv ℝ f z - fderiv ℝ f x‖ < ε / 2} ∈ 𝓝 x := by
    have hc : ContinuousAt (fun z => ‖fderiv ℝ f z - fderiv ℝ f x‖) x :=
      (hdf.sub continuousAt_const).norm
    exact hc.preimage_mem_nhds (Iio_mem_nhds (by simpa using half_pos hε))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hD.mem_nhds hx) hnear)
  let L : ℝ≥0 := ⟨‖fderiv ℝ f x‖ + ε / 2, by positivity⟩
  refine ⟨ball x r, L, isOpen_ball, mem_ball_self hr, fun z hz => (hball hz).1, ?_, ?_⟩
  · apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hf.differentiableOn (by norm_num) z (hball hz).1).differentiableAt
        (hD.mem_nhds (hball hz).1)) ?_ (convex_ball x r)
    intro z hz
    change ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ f x‖ + ε / 2
    have hn := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f x)
    have hclose : ‖fderiv ℝ f z - fderiv ℝ f x‖ < ε / 2 := (hball hz).2
    linarith
  · intro z hz
    change ‖fderiv ℝ f x‖ + ε / 2 ≤ ‖fderiv ℝ f z‖ + ε
    have hn := norm_sub_norm_le (fderiv ℝ f x) (fderiv ℝ f z)
    rw [norm_sub_rev] at hn
    have hclose : ‖fderiv ℝ f z - fderiv ℝ f x‖ < ε / 2 := (hball hz).2
    linarith

theorem exists_countable_derivative_cover
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℕ → Set ℂ, ∃ L : ℕ → ℝ≥0,
      (∀ n, IsOpen (U n)) ∧ D ⊆ ⋃ n, U n ∧
      (∀ n, U n ⊆ D) ∧ (∀ n, LipschitzOnWith (L n) f (U n)) ∧
      ∀ n z, z ∈ U n → (L n : ℝ) ≤ ‖fderiv ℝ f z‖ + ε := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ => ∅, fun _ => 0, fun _ => isOpen_empty, empty_subset _,
      fun _ => empty_subset _, fun _ => ?_, ?_⟩
    · intro z hz
      exact hz.elim
    · simp
  let : Nonempty D := hne.to_subtype
  choose U L hU hxU hUD hLip hbound using
    fun x : D => exists_local_derivative_bound hD hf hε x.property
  have hcover : D ⊆ ⋃ x : D, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨q, hq⟩ := (IsLindelof.of_coe : IsLindelof D).indexed_countable_subcover U hU hcover
  exact ⟨fun n => U (q n), fun n => L (q n), fun n => hU (q n), hq,
    fun n => hUD (q n), fun n => hLip (q n), fun n => hbound (q n)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MonotoneL2Limit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nonnegative increasing finite sums with a uniform square-integral
bound have a finite L² limit almost everywhere. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_monotone_L2_limit {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} (hf : ∀ n, Measurable (f n))
    (hf2 : ∀ n, MemLp (f n) 2 μ) (hf0 : ∀ n x, 0 ≤ f n x)
    (hmono : ∀ x, Monotone (fun n => f n x)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, (∫ x, f n x^2 ∂μ) ≤ B) :
    ∃ P : X → ℝ, Measurable P ∧ (∀ x, 0 ≤ P x) ∧ MemLp P 2 μ ∧
      (∫ x, P x^2 ∂μ) ≤ B ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (P x)) ∧ ∀ n, f n x ≤ P x) := by
  let Q := fun x => ⨆ n, ENNReal.ofReal (f n x)
  have hQ : Measurable Q := Measurable.iSup (fun n => (hf n).ennreal_ofReal)
  have ht (x : X) : Tendsto (fun n => ENNReal.ofReal (f n x)) atTop (𝓝 (Q x)) :=
    tendsto_atTop_iSup (fun i j hij => ENNReal.ofReal_le_ofReal (hmono x hij))
  have hi : (∫⁻ x, Q x^2 ∂μ) ≤ ENNReal.ofReal B := by
    have hconv := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
      (fun n => ((hf n).ennreal_ofReal.pow_const 2).aemeasurable)
      (Eventually.of_forall (fun x i j hij => pow_le_pow_left' (ENNReal.ofReal_le_ofReal (hmono x hij)) 2))
      (Eventually.of_forall (fun x => ENNReal.Tendsto.pow (ht x)))
    apply le_of_tendsto hconv
    apply Eventually.of_forall
    intro n
    have he : (∫⁻ x, ENNReal.ofReal (f n x)^2 ∂μ) = ENNReal.ofReal (∫ x, f n x^2 ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hf2 n).integrable_sq
        (Eventually.of_forall (fun x => sq_nonneg (f n x)))]
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_pow (hf0 n x) 2).symm
    rw [he]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hfinite : ∀ᵐ x ∂μ, Q x ≠ ∞ := by
    filter_upwards [ae_lt_top (hQ.pow_const 2) (ne_of_lt (hi.trans_lt ENNReal.ofReal_lt_top))] with x hx
    intro he
    simp only [he,ENNReal.top_pow (by norm_num : (2:ℕ) ≠ 0),lt_self_iff_false] at hx
  let P := fun x => (Q x).toReal
  have hP : Measurable P := hQ.ennreal_toReal
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (P x)) ∧ ∀ n, f n x ≤ P x := by
    filter_upwards [hfinite] with x hx
    constructor
    · have h := (ENNReal.continuousAt_toReal hx).tendsto.comp (ht x)
      simpa only [Function.comp_def,ENNReal.toReal_ofReal (hf0 _ _)] using h
    · intro n
      have hle : ENNReal.ofReal (f n x) ≤ Q x := le_iSup (fun n => ENNReal.ofReal (f n x)) n
      simpa only [ENNReal.toReal_ofReal (hf0 _ _)] using ENNReal.toReal_mono hx hle
  have hPint : (∫⁻ x, ENNReal.ofReal (P x^2) ∂μ) ≤ ENNReal.ofReal B := by
    apply le_trans _ hi
    apply lintegral_mono
    intro x
    change ENNReal.ofReal ((Q x).toReal^2) ≤ Q x^2
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    exact pow_le_pow_left' ENNReal.ofReal_toReal_le 2
  have hPi : Integrable (fun x => P x^2) μ :=
    ⟨(hP.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => sq_nonneg (P x)))).mpr
        (hPint.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨P,hP,(fun _ => ENNReal.toReal_nonneg),
    (memLp_two_iff_integrable_sq hP.aestronglyMeasurable).mpr hPi,?_,hlim⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hPi (Eventually.of_forall (fun x => sq_nonneg (P x)))] at hPint
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hPint

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexCoareaJacobian
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Jacobian identity in regular complex coordinates. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

lemma complex_real_det_columns (B : ℂ →L[ℝ] ℂ) :
    B.det = (B 1).re * (B Complex.I).im - (B Complex.I).re * (B 1).im := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    ContinuousLinearMap.coe_coe, Matrix.cons_val_zero, Matrix.cons_val_one]

lemma coarea_covector_jacobian (A : ℂ →L[ℝ] ℝ) (B : ℂ →L[ℝ] ℂ)
    (h1 : A (B 1) = 1) (hI : A (B Complex.I) = 0) :
    ‖A‖ * |B.det| = ‖B Complex.I‖ := by
  rw [complexCovector_apply] at h1 hI
  let Δ := (B 1).re * (B Complex.I).im - (B Complex.I).re * (B 1).im
  have ha : A 1 * Δ = (B Complex.I).im := by
    dsimp only [Δ]
    linear_combination (B Complex.I).im * h1 - (B 1).im * hI
  have hb : A Complex.I * Δ = -(B Complex.I).re := by
    dsimp only [Δ]
    linear_combination -(B Complex.I).re * h1 + (B 1).re * hI
  have hs : (‖A‖ * |B.det|) ^ 2 = ‖B Complex.I‖ ^ 2 := by
    rw [mul_pow, sq_abs, complexCovector_norm_sq, complex_real_det_columns,
      Complex.sq_norm, Complex.normSq_apply]
    simp only [← pow_two]
    change ((A 1)^2 + (A Complex.I)^2) * Δ^2 = (B Complex.I).re^2 + (B Complex.I).im^2
    calc
      _ = (A 1 * Δ)^2 + (A Complex.I * Δ)^2 := by ring
      _ = (B Complex.I).re^2 + (B Complex.I).im^2 := by rw [ha, hb]; ring
  exact (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (norm_nonneg _)).mp hs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_HausdorffZeroCounting
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero-dimensional Hausdorff measure counts the points of an arbitrary
set. Finite subsets suffice for the lower bound on infinite sets. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma hausdorff_zero_finset {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (F : Finset X) :
    (μH[0] : Measure X) (F : Set X) = F.card := by
  rw [← sum_measure_singleton]
  simp only [Measure.hausdorffMeasure_zero_singleton, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma hausdorff_zero_eq_count {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (A : Set X) :
    (μH[0] : Measure X) A = Measure.count A := by
  classical
  by_cases hA : A.Finite
  · rw [← hA.coe_toFinset, hausdorff_zero_finset, Measure.count_apply_finset]
  · have hA : A.Infinite := hA
    rw [Measure.count_apply_infinite hA]
    apply top_unique
    apply le_of_tendsto' ENNReal.tendsto_nat_nhds_top
    intro n
    obtain ⟨F, hFA, hF⟩ := hA.exists_subset_card_eq n
    rw [← hF, ← hausdorff_zero_finset F]
    exact measure_mono hFA

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Probability_BorelFiberCounts
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite distinct-point witnesses make fiber counts universally
measurable. The image of each Borel configuration space is analytic. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma pointCount_eq_iSup {X : Type*} (S : Set X) :
    pointCount S = ⨆ n : ℕ, if finitePointWitness S n then (n : ℝ≥0∞) else 0 := by
  classical
  apply le_antisymm
  · rw [pointCount, ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let E := F.filter (· ∈ S)
    let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
    have hw : finitePointWitness S (Fintype.card E) :=
      ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective,
        fun i => (Finset.mem_filter.mp (e i).property).2⟩
    have hn : (Fintype.card E : ℝ≥0∞) ≤ ⨆ n : ℕ,
        if finitePointWitness S n then (n : ℝ≥0∞) else 0 :=
      (ite_eq_left hw).symm.le.trans (le_iSup
        (fun n : ℕ => if finitePointWitness S n then (n : ℝ≥0∞) else 0) _)
    simpa only [Finset.sum_boole, Fintype.card_coe] using hn
  · apply iSup_le
    intro n
    split_ifs with hn
    · obtain ⟨g, hg, hS⟩ := hn
      calc
        (n : ℝ≥0∞) = ∑' i : Fin n, if g i ∈ S then (1 : ℝ≥0∞) else 0 := by
          simp only [hS, ite_true, if_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ pointCount S := ENNReal.tsum_comp_le_tsum_of_injective hg
          (fun x => if x ∈ S then (1 : ℝ≥0∞) else 0)
    · exact zero_le

lemma pointCount_eq_hausdorff_zero {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {S : Set X} (hS : MeasurableSet S) :
    pointCount S = (μH[0] : Measure X) S := by
  rw [hausdorff_zero_eq_count, Measure.count_apply hS]
  exact (tsum_subtype S (fun _ => (1 : ℝ≥0∞))).symm.trans (ENNReal.tsum_set_one S)

lemma nullMeasurableSet_analytic_sfinite {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [SFinite μ]
    {A : Set X} (hA : AnalyticSet A) : NullMeasurableSet A μ := by
  have h := nullMeasurableSet_analytic_finite μ.toFinite hA
  change EventuallyMeasurableSet _ (ae μ) A
  change EventuallyMeasurableSet _ (ae μ.toFinite) A at h
  rcases h with ⟨B, hB, hBA⟩
  refine ⟨B, hB, ?_⟩
  simpa only [ae_toFinite] using hBA

lemma analytic_finite_fiber_witness
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {A : Set X} (hA : MeasurableSet A) {f : X → Y} (hf : Continuous f) (n : ℕ) :
    AnalyticSet {y | finitePointWitness (A ∩ f ⁻¹' {y}) n} := by
  let C : Set ((Fin n → X) × Y) := {p | Injective p.1 ∧
    (∀ i, p.1 i ∈ A) ∧ ∀ i, f (p.1 i) = p.2}
  have hci : MeasurableSet {p : (Fin n → X) × Y | Injective p.1} := by
    simp only [Injective, ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i = j
    · simp only [hij, implies_true, ofPred_true, MeasurableSet.univ]
    · simpa only [hij, imp_false, compl_ofPred] using
        (isClosed_eq (by fun_prop : Continuous (fun p : (Fin n → X) × Y => p.1 i))
          (by fun_prop : Continuous (fun p : (Fin n → X) × Y => p.1 j))).measurableSet.compl
  have hca : MeasurableSet {p : (Fin n → X) × Y | ∀ i, p.1 i ∈ A} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun i => hA.preimage (by fun_prop))
  have hcf : MeasurableSet {p : (Fin n → X) × Y | ∀ i, f (p.1 i) = p.2} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun i => (isClosed_eq
      (hf.comp (by fun_prop)) continuous_snd).measurableSet)
  have hc : MeasurableSet C := hci.inter (hca.inter hcf)
  have heq : Prod.snd '' C = {y | finitePointWitness (A ∩ f ⁻¹' {y}) n} := by
    ext y
    constructor
    · rintro ⟨⟨g, y⟩, hg, rfl⟩
      exact ⟨g, hg.1, fun i => ⟨hg.2.1 i, hg.2.2 i⟩⟩
    · rintro ⟨g, hg, hmem⟩
      exact ⟨(g, y), ⟨hg, (fun i => (hmem i).1), fun i => (hmem i).2⟩, rfl⟩
  rw [← heq]
  exact hc.analyticSet.image_of_continuous continuous_snd

lemma aemeasurable_hausdorff_zero_fiber
    {X Y : Type*} [MetricSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {A : Set X} (hA : MeasurableSet A) {f : X → Y} (hf : Continuous f)
    (μ : Measure Y) [SFinite μ] :
    AEMeasurable (fun y => (μH[0] : Measure X) (A ∩ f ⁻¹' {y})) μ := by
  have heq : (fun y => (μH[0] : Measure X) (A ∩ f ⁻¹' {y})) =
      fun y => ⨆ n : ℕ, if finitePointWitness (A ∩ f ⁻¹' {y}) n then (n : ℝ≥0∞) else 0 := by
    funext y
    rw [← pointCount_eq_hausdorff_zero (hA.inter (hf.measurable (measurableSet_singleton y))),
      pointCount_eq_iSup]
  rw [heq]
  apply NullMeasurable.aemeasurable
  change @Measurable (NullMeasurableSpace Y μ) ℝ≥0∞ _ _ _
  apply Measurable.iSup
  intro n
  exact Measurable.ite (nullMeasurableSet_analytic_sfinite μ
    (analytic_finite_fiber_witness hA hf n)) measurable_const measurable_const

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ShrinkingFiberCovers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCountableElemFirstUncountableIio
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covering a fiber by a shrinking family bounds its point count by the
lower limit of the number of covering images that contain the target. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma hausdorff_zero_fiber_le_liminf_cover
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    (A : Set X) (f : X → Y) (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (T : ℕ → ℕ → Set X) (hT : ∀ n k, ediam (T n k) ≤ r n)
    (hcover : ∀ n, A ⊆ ⋃ k, T n k) (y : Y) :
    (μH[0] : Measure X) (A ∩ f ⁻¹' {y}) ≤
      liminf (fun n => ∑' k, if y ∈ closure (f '' T n k) then (1 : ℝ≥0∞) else 0) atTop := by
  classical
  let I (n : ℕ) := {k : ℕ | (A ∩ f ⁻¹' {y} ∩ T n k).Nonempty}
  let S (n : ℕ) (k : I n) := A ∩ f ⁻¹' {y} ∩ T n k.val
  have hS : ∀ n k, ediam (S n k) ≤ r n := fun n k =>
    (ediam_mono inter_subset_right).trans (hT n k.val)
  have hcov : ∀ n, A ∩ f ⁻¹' {y} ⊆ ⋃ k : I n, S n k := by
    intro n x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover n hx.1)
    exact mem_iUnion.mpr ⟨⟨k, ⟨x, hx, hk⟩⟩, hx, hk⟩
  have h := Measure.hausdorffMeasure_le_liminf_tsum 0 (A ∩ f ⁻¹' {y}) r hr S
    (.of_forall hS) (.of_forall hcov)
  simp only [ENNReal.rpow_zero] at h
  apply h.trans
  apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
  apply Eventually.of_forall
  intro n
  rw [show (∑' _ : I n, (1 : ℝ≥0∞)) = ∑' k, (I n).indicator (fun _ => (1 : ℝ≥0∞)) k from
    tsum_subtype (I n) (fun _ => (1 : ℝ≥0∞))]
  apply ENNReal.tsum_le_tsum
  intro k
  simp only [indicator_apply]
  split_ifs with hk hy
  · exact le_rfl
  · obtain ⟨x, hx, hxT⟩ := hk
    have hfxy : f x = y := hx.2
    exact False.elim (hy (subset_closure ⟨x, hxT, hfxy⟩))
  · exact zero_le
  · exact zero_le

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_SmallHausdorffCovers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nearly optimal countable covers at a prescribed positive scale. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma iSup_nonempty_ediam {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (S : Set X) :
    (⨆ _ : S.Nonempty, ediam S) = ediam S := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · simp only [iSup_pos hS]

lemma exists_small_hausdorff_cover {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[1] : Measure X) A < ∞)
    (r ε : ℝ≥0∞) (hr : 0 < r) (hε : 0 < ε) :
    ∃ T : ℕ → Set X, A ⊆ ⋃ k, T k ∧ (∀ k, ediam (T k) ≤ r) ∧
      (∑' k, ediam (T k)) < (μH[1] : Measure X) A + ε := by
  have hle : (⨅ (T : ℕ → Set X) (_ : A ⊆ ⋃ k, T k) (_ : ∀ k, ediam (T k) ≤ r),
      ∑' k, ⨆ _ : (T k).Nonempty, ediam (T k) ^ (1 : ℝ)) ≤ (μH[1] : Measure X) A := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hlt := hle.trans_lt (ENNReal.lt_add_right hA.ne hε.ne')
  simp only [iInf_lt_iff] at hlt
  obtain ⟨T, hc, hd, hcost⟩ := hlt
  refine ⟨T, hc, hd, ?_⟩
  simpa only [ENNReal.rpow_one, iSup_nonempty_ediam] using hcost

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzFiberIntegralBound
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sharp one-dimensional coarea inequality from Hausdorff covers.
No rectifiability is needed. Closed images of the covers are measurable
majorants; Fatou's lemma passes their counting bounds to the fibers. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma lipschitz_fiber_integral_le
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[1] : Measure X) A < ∞)
    (L : ℝ≥0) (f : X → ℝ) (hf : LipschitzWith L f) :
    (∫⁻ y, (μH[0] : Measure X) (A ∩ f ⁻¹' {y})) ≤
      (L : ℝ≥0∞) * (μH[1] : Measure X) A := by
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hε : ∀ n, 0 < ε n := fun n => ENNReal.ofReal_pos.mpr (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose T hcover hdiam hcost using fun n =>
    exists_small_hausdorff_cover A hA (ε n) (ε n) (hε n) (hε n)
  let g : ℕ → ℝ → ℝ≥0∞ := fun n y =>
    ∑' k, if y ∈ closure (f '' T n k) then 1 else 0
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    apply Measurable.tsum
    intro k
    exact Measurable.ite isClosed_closure.measurableSet measurable_const measurable_const
  have hgint : ∀ n, (∫⁻ y, g n y) ≤
      (L : ℝ≥0∞) * ((μH[1] : Measure X) A + ε n) := by
    intro n
    calc
      (∫⁻ y, g n y) = ∑' k, volume (closure (f '' T n k)) := by
        rw [show g n = fun y => ∑' k, (closure (f '' T n k)).indicator
          (fun _ => (1 : ℝ≥0∞)) y by rfl]
        rw [lintegral_tsum (fun k => measurable_const.indicator
          isClosed_closure.measurableSet |>.aemeasurable)]
        simp only [lintegral_indicator isClosed_closure.measurableSet, lintegral_one,
          Measure.restrict_apply_univ]
      _ ≤ ∑' k, (L : ℝ≥0∞) * ediam (T n k) := by
        apply ENNReal.tsum_le_tsum
        intro k
        exact (Real.volume_le_diam _).trans ((ediam_closure _).le.trans (hf.ediam_image_le _))
      _ = (L : ℝ≥0∞) * ∑' k, ediam (T n k) := ENNReal.tsum_mul_left
      _ ≤ (L : ℝ≥0∞) * ((μH[1] : Measure X) A + ε n) := by
        gcongr
        exact (hcost n).le
  have hb : (∫⁻ y, (μH[0] : Measure X) (A ∩ f ⁻¹' {y})) ≤
      liminf (fun n => ∫⁻ y, g n y) atTop :=
    (lintegral_mono (hausdorff_zero_fiber_le_liminf_cover A f ε hεlim T hdiam hcover)).trans
      (lintegral_liminf_le hgm)
  apply hb.trans
  have ht : Tendsto (fun n => (L : ℝ≥0∞) * ((μH[1] : Measure X) A + ε n)) atTop
      (𝓝 ((L : ℝ≥0∞) * (μH[1] : Measure X) A)) := by
    simpa only [add_zero] using
      ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hεlim) (Or.inr ENNReal.coe_ne_top)
  rw [← ht.liminf_eq]
  exact liminf_le_liminf (.of_forall hgint)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzCoareaProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The published plane-to-line coarea input, with its exact finite-H1
Borel-set hypotheses. Both the completed measurability and the sharp
constant-one inequality are proved. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma planarLipschitzFiberCoarea : PlanarLipschitzFiberCoarea := by
  intro A hA hfin L f hf
  exact ⟨aemeasurable_hausdorff_zero_fiber hA hf.continuous volume,
    lipschitz_fiber_integral_le A hfin L f hf⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.StableBernstein_Estimates_PuncturedSard
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace StableBernstein.W30
open Set
open scoped ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem taylorWithinEval_eq_of_flat (g : ℝ → ℝ) (s : Set ℝ) (a b : ℝ)
    (n : ℕ) (hflat : ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedDerivWithin k g s a = 0) :
    taylorWithinEval g n s a b = g a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [taylorWithinEval_succ, ih (fun k hk hkn => hflat k hk (by omega)),
      hflat (n + 1) (by omega) le_rfl]
    simp

end StableBernstein.W30

namespace StableBernstein.W30
open Set
open scoped ContDiff BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iteratedDeriv_affine_line_local {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    (x v : E) (t : ℝ) (ht : x + t • v ∈ U) (k : ℕ) (hk : k ≤ 7) :
    iteratedDeriv k (fun s : ℝ => f (x + s • v)) t =
      iteratedFDeriv ℝ k f (x + t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let S : Set E := (fun z : E => x + z) ⁻¹' U
  have hS : IsOpen S := hU.preimage (continuous_const.add continuous_id)
  have hLS : IsOpen (L ⁻¹' S) := hS.preimage L.continuous
  have hs : ContDiffOn ℝ 7 (fun z : E => f (x + z)) S :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hz => hz)
  have htS : L t ∈ S := ht
  have h := L.iteratedFDerivWithin_comp_right hs hS.uniqueDiffOn
    hLS.uniqueDiffOn htS (i := k) (by exact_mod_cast hk)
  rw [(iteratedFDerivWithin_of_isOpen k hLS) htS,
    (iteratedFDerivWithin_of_isOpen k hS) htS] at h
  rw [iteratedDeriv_eq_iteratedFDeriv]
  simpa [Function.comp_def, L, iteratedFDeriv_comp_add_left,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using
    congrArg (fun T => T (fun _ : Fin k => (1 : ℝ))) h

theorem flat_taylor_bound_segment_local {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    (x y : E) (hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ U) (C : ℝ)
    (hflat : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 7 f (x + t • (y - x))‖ ≤ C) :
    |f y - f x| ≤ C * ‖y - x‖ ^ 7 / 720 := by
  let g : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hga (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 7 g t :=
    (hf.contDiffAt (hU.mem_nhds (hseg t ht))).comp t
      ((contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt)
  have hg : ContDiffOn ℝ 7 g (Icc (0 : ℝ) 1) :=
    fun t ht => (hga t ht).contDiffWithinAt
  have hd (k : ℕ) (hk : k ≤ 7) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin k g (Icc (0 : ℝ) 1) t =
        iteratedFDeriv ℝ k f (x + t • (y - x)) (fun _ => y - x) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hga t ht).of_le (by exact_mod_cast hk)) ht]
    exact iteratedDeriv_affine_line_local hU hf x (y - x) t (hseg t ht) k hk
  have hp : taylorWithinEval g 6 (Icc (0 : ℝ) 1) 0 1 = g 0 := by
    apply taylorWithinEval_eq_of_flat
    intro k hk hk6
    rw [hd k (by omega) 0 (by simp)]
    simpa using congrArg (fun T => T (fun _ : Fin k => y - x)) (hflat k hk hk6)
  have hC : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 7 g (Icc (0 : ℝ) 1) t‖ ≤ C * ‖y - x‖ ^ 7 := by
    intro t ht
    rw [hd 7 le_rfl t ht]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 7 f (x + t • (y - x))‖ * ‖y - x‖ ^ 7 := by
        simpa using (iteratedFDeriv ℝ 7 f (x + t • (y - x))).le_opNorm
          (fun _ : Fin 7 => y - x)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound t ht) (pow_nonneg (norm_nonneg _) _)
  have h := taylor_mean_remainder_bound (f := g) (n := 6)
    (a := 0) (b := 1) (x := 1) (C := C * ‖y - x‖ ^ 7)
    zero_le_one hg (by simp) hC
  rw [hp] at h
  simpa [g, Real.norm_eq_abs, Nat.factorial] using h

theorem flat_taylor_bound_convex_local {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    {s : Set E} (hs : Convex ℝ s) (hsU : s ⊆ U) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    (C : ℝ) (hflat : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0)
    (hbound : ∀ z ∈ s, ‖iteratedFDeriv ℝ 7 f z‖ ≤ C) :
    |f y - f x| ≤ C * ‖y - x‖ ^ 7 / 720 :=
  flat_taylor_bound_segment_local hU hf x y
    (fun _parameter ht => hsU (hs.add_smul_sub_mem hx hy ht)) C hflat fun _parameter ht =>
      hbound _ (hs.add_smul_sub_mem hx hy ht)

end StableBernstein.W30

namespace StableBernstein.W30
open Set MeasureTheory
open scoped ContDiff NNReal ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sixFlat_holderOn_local {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    {s K : Set E} (hs : Convex ℝ s) (hsU : s ⊆ U) (hKs : K ⊆ s)
    (hflat : ∀ x ∈ K, ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ s, ‖iteratedFDeriv ℝ 7 f z‖ ≤ C) :
    HolderOnWith ⟨C / 720, div_nonneg hC (by norm_num)⟩ 7 f K := by
  intro x hx y hy
  have h := flat_taylor_bound_convex_local hU hf hs hsU (hKs hx) (hKs hy) C (hflat x hx) hbound
  have hd : dist (f x) (f y) ≤ (C / 720) * dist x y ^ 7 := by
    simpa [Real.dist_eq, dist_eq_norm, abs_sub_comm, norm_sub_rev,
      div_mul_eq_mul_div] using h
  have he := ENNReal.ofReal_le_ofReal hd
  have hc720 : 0 ≤ C / 720 := div_nonneg hC (by norm_num)
  rw [ENNReal.ofReal_mul hc720, ENNReal.ofReal_pow dist_nonneg,
    ENNReal.ofReal_eq_coe_nnreal hc720] at he
  simpa only [edist_dist, NNReal.coe_ofNat, ENNReal.rpow_natCast, ENNReal.rpow_ofNat,
    NNReal.mk] using he

theorem volume_image_sixFlat_local_eq_zero [FiniteDimensional ℝ E]
    (hdim : (Module.finrank ℝ E : ℝ) < 7) {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    {s K : Set E} (hs : Convex ℝ s) (hsU : s ⊆ U) (hKs : K ⊆ s)
    (hflat : ∀ x ∈ K, ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ s, ‖iteratedFDeriv ℝ 7 f z‖ ≤ C) :
    volume (f '' K) = 0 := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  have hH := (sixFlat_holderOn_local hU hf hs hsU hKs hflat C hC hbound).hausdorffMeasure_image_le
    (by norm_num : (0 : ℝ≥0) < 7) (d := 1) (by norm_num)
  have hzero : (Measure.hausdorffMeasure 7 : Measure E) = 0 :=
    Real.hausdorffMeasure_of_finrank_lt (E := E) (d := 7)
      hdim
  have hz : volume (f '' K) ≤ 0 := by
    simpa [MeasureTheory.hausdorffMeasure_real, hzero] using hH
  exact le_antisymm hz zero_le

theorem exists_ball_sixFlat_image_null [FiniteDimensional ℝ E]
    (hdim : (Module.finrank ℝ E : ℝ) < 7)
    {f : E → ℝ} {U K : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 7 f U)
    (hKU : K ⊆ U)
    (hflat : ∀ x ∈ K, ∀ k : ℕ, 1 ≤ k → k ≤ 6 → iteratedFDeriv ℝ k f x = 0)
    {x : E} (hx : x ∈ K) :
    ∃ r : ℝ, 0 < r ∧ volume (f '' (K ∩ Metric.ball x r)) = 0 := by
  let C : ℝ := ‖iteratedFDeriv ℝ 7 f x‖ + 1
  have hC : 0 ≤ C := add_nonneg (norm_nonneg _) zero_le_one
  have hc : ContinuousAt (fun z => ‖iteratedFDeriv ℝ 7 f z‖) x :=
    ((hf.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt_iteratedFDeriv
      (by norm_num)).norm
  have he : {z : E | ‖iteratedFDeriv ℝ 7 f z‖ < C} ∈ 𝓝 x :=
    hc.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds (hKU hx)) he)
  refine ⟨r, hr, ?_⟩
  apply volume_image_sixFlat_local_eq_zero hdim hU hf (convex_ball x r)
    (fun _ hz => (hball hz).1) inter_subset_right
    (fun z hz => hflat z hz.1) C hC
  intro z hz
  exact (hball hz).2.le

end StableBernstein.W30

namespace Bernstein.Sard

section
open Set Filter MeasureTheory
open scoped Topology ContDiff

section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem regular_scalar_range [FiniteDimensional ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] ℝ) (hL : L ≠ 0) : L.range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  exact L.toLinearMap.surjective (fun h => hL (ContinuousLinearMap.coe_injective h))

theorem regular_scalar_kernel_dimension (L : E →L[ℝ] ℝ) (hL : L ≠ 0) :
    Module.finrank ℝ L.ker + 1 = Module.finrank ℝ E := by
  have hd := L.toLinearMap.finrank_range_add_finrank_ker
  have hr := regular_scalar_range L hL
  change L.toLinearMap.range = ⊤ at hr
  rw [hr] at hd
  simpa only [finrank_top, Module.finrank_self, Nat.add_comm] using hd

theorem exists_smooth_regular_stratum_chart (U : Set E) (hU : IsOpen U)
    (h : E → ℝ) (hh : ContDiffOn ℝ ∞ h U) (a : E) (ha : a ∈ U)
    (_ha0 : h a = 0) (hreg : fderiv ℝ h a ≠ 0) :
    ∃ (V : Set E) (W : Set (fderiv ℝ h a).ker)
      (ψ : (fderiv ℝ h a).ker → E) (q : E → (fderiv ℝ h a).ker),
      IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ IsOpen W ∧
      ContDiffOn ℝ ∞ ψ W ∧ MapsTo ψ W U ∧
      (∀ t ∈ W, h (ψ t) = 0 ∧ q (ψ t) = t) ∧
      (∀ x ∈ V, h x = 0 → q x ∈ W ∧ ψ (q x) = x) := by
  let L := fderiv ℝ h a
  have hr : L.range = ⊤ := regular_scalar_range L hreg
  have hs : HasStrictFDerivAt h L a :=
    (hh.contDiffAt (hU.mem_nhds ha)).hasStrictFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let hker := L.ker_closedComplemented_of_finiteDimensional_range
  let P : E →L[ℝ] L.ker := Classical.choose hker
  let φ := hs.implicitFunctionDataOfComplemented h L hr hker
  let e := φ.toOpenPartialHomeomorph
  have hae : a ∈ e.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have hg : ContDiffOn ℝ ∞ φ.prodFun U := by
    change ContDiffOn ℝ ∞ (fun x => (h x, P (x - a))) U
    exact hh.prodMk
      ((P.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
  have hcg : ContinuousAt (fderiv ℝ φ.prodFun) a :=
    (hg.continuousOn_fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt (hU.mem_nhds ha)
  obtain ⟨e₀, he₀⟩ := φ.isInvertible_fderiv_prodFun
  have hpoint : φ.pt = a := rfl
  have hnear : {x : E | ∃ A : E ≃L[ℝ] (ℝ × L.ker),
      (A : E →L[ℝ] (ℝ × L.ker)) = fderiv ℝ φ.prodFun x} ∈ 𝓝 a := by
    have H : Set.range ((↑) : (E ≃L[ℝ] (ℝ × L.ker)) →
        E →L[ℝ] (ℝ × L.ker)) ∈ 𝓝 (fderiv ℝ φ.prodFun a) := by
      simpa only [he₀, hpoint] using e₀.nhds
    exact hcg.preimage_mem_nhds H
  have hnbhd : {x : E | x ∈ U ∧ x ∈ e.source ∧
      ∃ A : E ≃L[ℝ] (ℝ × L.ker),
        (A : E →L[ℝ] (ℝ × L.ker)) = fderiv ℝ φ.prodFun x} ∈ 𝓝 a :=
    inter_mem (hU.mem_nhds ha) (inter_mem (e.open_source.mem_nhds hae) hnear)
  obtain ⟨V, hVs, hV, haV⟩ := mem_nhds_iff.mp hnbhd
  have hVU : V ⊆ U := fun x hx => (hVs hx).1
  have hVe : V ⊆ e.source := fun x hx => (hVs hx).2.1
  let T := e.target ∩ e.symm ⁻¹' V
  have hT : IsOpen T := e.isOpen_inter_preimage_symm hV
  have hTsm : ContDiffOn ℝ ∞ e.symm T := by
    intro p hp
    obtain ⟨A, hA⟩ := (hVs hp.2).2.2
    have hd : HasFDerivAt e (A : E →L[ℝ] (ℝ × L.ker)) (e.symm p) := by
      rw [hA]
      exact ((hg.differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds (hVU hp.2))).hasFDerivAt
    have hc : ContDiffAt ℝ ∞ e (e.symm p) :=
      hg.contDiffAt (hU.mem_nhds (hVU hp.2))
    exact (e.contDiffAt_symm hp.1 hd hc).contDiffWithinAt
  let W : Set L.ker := (fun t : L.ker => ((0 : ℝ), t)) ⁻¹' T
  let ψ : L.ker → E := fun t => e.symm (0, t)
  let q : E → L.ker := fun x => (e x).2
  have hW : IsOpen W := hT.preimage (continuous_const.prodMk continuous_id)
  have hψ : ContDiffOn ℝ ∞ ψ W :=
    hTsm.comp ((contDiff_const.prodMk contDiff_id).contDiffOn) (fun _ ht => ht)
  refine ⟨V, W, ψ, q, hV, haV, hVU, hW, hψ, ?_, ?_, ?_⟩
  · intro t ht
    exact hVU ht.2
  · intro t ht
    have hi := e.right_inv ht.1
    constructor
    · have hfirst := congrArg Prod.fst hi
      change h (ψ t) = 0 at hfirst
      exact hfirst
    · change (e (e.symm (0, t))).2 = t
      rw [hi]
  · intro x hx hx0
    have hcoords : e x = (0, (e x).2) := by
      apply Prod.ext
      · change h x = 0
        exact hx0
      · rfl
    have ht : (0, (e x).2) ∈ T := by
      rw [← hcoords]
      refine ⟨e.map_source (hVe hx), ?_⟩
      change e.symm (e x) ∈ V
      rw [e.left_inv (hVe hx)]
      exact hx
    refine ⟨ht, ?_⟩
    change e.symm (0, (e x).2) = x
    rw [← hcoords, e.left_inv (hVe hx)]

end FiniteDimensional

theorem restricted_fderiv_zero {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (U : Set E) (hU : IsOpen U) (W : Set K) (hW : IsOpen W)
    (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (ψ : K → E) (hψ : ContDiffOn ℝ ∞ ψ W) (hmap : MapsTo ψ W U)
    {t : K} (ht : t ∈ W) (hzero : fderiv ℝ f (ψ t) = 0) :
    fderiv ℝ (f ∘ ψ) t = 0 := by
  have hdf := (hf.differentiableOn (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (hU.mem_nhds (hmap ht))
  have hdψ := (hψ.differentiableOn (by simp)).differentiableAt (hW.mem_nhds ht)
  rw [fderiv_comp t hdf hdψ, hzero, ContinuousLinearMap.zero_comp]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem regular_stratum_local_image_null
    (U : Set E) (hU : IsOpen U) (f h : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U)
    (S : Set E) (hcrit : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hlevel : ∀ x ∈ S, h x = 0) (a : E) (haU : a ∈ U) (haS : a ∈ S)
    (hreg : fderiv ℝ h a ≠ 0)
    (lowerSard : ∀ W : Set (fderiv ℝ h a).ker, IsOpen W →
      ∀ g : (fderiv ℝ h a).ker → ℝ, ContDiffOn ℝ ∞ g W →
        volume (g '' {t | t ∈ W ∧ fderiv ℝ g t = 0}) = 0) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ volume (f '' (S ∩ V)) = 0 := by
  obtain ⟨V, W, ψ, q, hV, haV, hVU, hW, hψ, hmap, _, hrep⟩ :=
    exists_smooth_regular_stratum_chart U hU h hh a haU (hlevel a haS) hreg
  refine ⟨V, hV, haV, hVU, ?_⟩
  have hsm : ContDiffOn ℝ ∞ (f ∘ ψ) W := hf.comp hψ hmap
  have hnull := lowerSard W hW (f ∘ ψ) hsm
  apply measure_mono_null _ hnull
  rintro r ⟨x, ⟨hxS, hxV⟩, hxr⟩
  obtain ⟨hqx, hψqx⟩ := hrep x hxV (hlevel x hxS)
  refine ⟨q x, ⟨hqx, ?_⟩, ?_⟩
  · apply restricted_fderiv_zero U hU W hW f hf ψ hψ hmap hqx
    simpa only [hψqx] using hcrit x hxS
  · simpa only [Function.comp_apply, hψqx] using hxr

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem contDiffOn_iteratedFDeriv_component [FiniteDimensional ℝ E] [CompleteSpace E]
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (k : ℕ) (v : Fin k → E) :
    ContDiffOn ℝ ∞ (fun x => iteratedFDeriv ℝ k f x v) U := by
  let ev : (E [×k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℝ v
  intro x hx
  have hd : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ k f) x :=
    (hf.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right
      (WithTop.coe_le_coe.mpr (show (⊤ : ℕ∞) + (k : ℕ∞) ≤ ⊤ from le_top))
  exact (ev.contDiff.contDiffAt.comp x hd).contDiffWithinAt

theorem derivative_component_stratum_local_image_null
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (k : ℕ) (v : Fin k → E) (S : Set E)
    (hcrit : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hflat : ∀ x ∈ S, iteratedFDeriv ℝ k f x = 0)
    (a : E) (haU : a ∈ U) (haS : a ∈ S)
    (hreg : fderiv ℝ (fun x => iteratedFDeriv ℝ k f x v) a ≠ 0)
    (lowerSard : ∀ W : Set (fderiv ℝ (fun x => iteratedFDeriv ℝ k f x v) a).ker,
      IsOpen W → ∀ g : (fderiv ℝ (fun x => iteratedFDeriv ℝ k f x v) a).ker → ℝ,
      ContDiffOn ℝ ∞ g W → volume (g '' {t | t ∈ W ∧ fderiv ℝ g t = 0}) = 0) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ volume (f '' (S ∩ V)) = 0 := by
  apply regular_stratum_local_image_null U hU f
    (fun x => iteratedFDeriv ℝ k f x v) hf
    (contDiffOn_iteratedFDeriv_component U hU f hf k v) S hcrit
    (fun x hx => by rw [hflat x hx]; rfl) a haU haS hreg lowerSard

end

section
open Set MeasureTheory
open scoped ContDiff

theorem exists_regular_iteratedFDeriv_component
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (a : E) (ha : a ∈ U) (k : ℕ)
    (hne : iteratedFDeriv ℝ (k + 1) f a ≠ 0) :
    ∃ v : Fin k → E, fderiv ℝ (fun x => iteratedFDeriv ℝ k f x v) a ≠ 0 := by
  by_contra hnone
  push Not at hnone
  apply hne
  have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) a :=
    ((hf.contDiffAt (hU.mem_nhds ha)).iteratedFDeriv_right
      (m := ∞)
      (WithTop.coe_le_coe.mpr (show (⊤ : ℕ∞) + (k : ℕ∞) ≤ ⊤ from le_top))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  apply ContinuousMultilinearMap.ext
  intro m
  rw [iteratedFDeriv_succ_apply_left]
  let ev : (E [×k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℝ (Fin.tail m)
  have heval : fderiv ℝ (fun x => iteratedFDeriv ℝ k f x (Fin.tail m)) a =
      ev.comp (fderiv ℝ (iteratedFDeriv ℝ k f) a) :=
    (ev.hasFDerivAt.comp a hD.hasFDerivAt).fderiv
  have hz := congrArg (fun L : E →L[ℝ] ℝ => L (m 0)) (hnone (Fin.tail m))
  rw [heval] at hz
  exact hz

theorem image_null_of_locally_image_null
    {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    (f : E → ℝ) (S : Set E)
    (hlocal : ∀ a ∈ S, ∃ V : Set E, IsOpen V ∧ a ∈ V ∧
      volume (f '' (S ∩ V)) = 0) : volume (f '' S) = 0 := by
  choose V hV haV hnull using fun a : S => hlocal a a.property
  obtain ⟨C, hC, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  have hsub : f '' S ⊆ ⋃ a ∈ C, f '' (S ∩ V a) := by
    rintro r ⟨x, hx, hxr⟩
    have hxV : x ∈ ⋃ a : S, V a := mem_iUnion.mpr ⟨⟨x, hx⟩, haV ⟨x, hx⟩⟩
    rw [← hcover] at hxV
    obtain ⟨a, ha⟩ := mem_iUnion.mp hxV
    obtain ⟨haC, hxa⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨haC, ⟨x, ⟨hx, hxa⟩, hxr⟩⟩⟩
  exact measure_mono_null hsub ((measure_biUnion_null_iff hC).mpr (fun a _ => hnull a))

theorem nonflat_stratum_image_null
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U)
    (k : ℕ) (S : Set E) (hSU : S ⊆ U)
    (hcrit : ∀ x ∈ S, fderiv ℝ f x = 0)
    (hflat : ∀ x ∈ S, iteratedFDeriv ℝ k f x = 0)
    (hnext : ∀ x ∈ S, iteratedFDeriv ℝ (k + 1) f x ≠ 0)
    (lowerSard : ∀ L : E →L[ℝ] ℝ, L ≠ 0 →
      ∀ W : Set L.ker, IsOpen W → ∀ g : L.ker → ℝ,
      ContDiffOn ℝ ∞ g W → volume (g '' {t | t ∈ W ∧ fderiv ℝ g t = 0}) = 0) :
    volume (f '' S) = 0 := by
  apply image_null_of_locally_image_null f S
  intro a ha
  obtain ⟨v, hv⟩ := exists_regular_iteratedFDeriv_component U hU f hf a (hSU ha) k
    (hnext a ha)
  obtain ⟨V, hV, haV, _, hnull⟩ := derivative_component_stratum_local_image_null
    U hU f hf k v S hcrit hflat a (hSU ha) ha hv (lowerSard _ hv)
  exact ⟨V, hV, haV, hnull⟩

end

open Set MeasureTheory Manifold
open scoped ContDiff Topology
universe u

section Strata
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem criticalSet_subset_sixFlat_union_strata (U : Set E) (f : E → ℝ) :
    {x | x ∈ U ∧ fderiv ℝ f x = 0} ⊆
      sixFlatSet U f ∪ ⋃ i : Fin 5, nonflatCriticalStratum U f (i.val + 1) := by
  intro x hx
  have h1 : iteratedFDeriv ℝ 1 f x = 0 := by
    apply ContinuousMultilinearMap.ext
    intro v
    rw [iteratedFDeriv_one_apply, hx.2]
    rfl
  by_cases h2 : iteratedFDeriv ℝ 2 f x = 0
  · by_cases h3 : iteratedFDeriv ℝ 3 f x = 0
    · by_cases h4 : iteratedFDeriv ℝ 4 f x = 0
      · by_cases h5 : iteratedFDeriv ℝ 5 f x = 0
        · by_cases h6 : iteratedFDeriv ℝ 6 f x = 0
          · left
            refine ⟨hx.1, ?_⟩
            intro k hk1 hk6
            interval_cases k <;> assumption
          · right
            exact mem_iUnion.mpr ⟨⟨4, by decide⟩, hx.1, hx.2, h5, h6⟩
        · right
          exact mem_iUnion.mpr ⟨⟨3, by decide⟩, hx.1, hx.2, h4, h5⟩
      · right
        exact mem_iUnion.mpr ⟨⟨2, by decide⟩, hx.1, hx.2, h3, h4⟩
    · right
      exact mem_iUnion.mpr ⟨⟨1, by decide⟩, hx.1, hx.2, h2, h3⟩
  · right
    exact mem_iUnion.mpr ⟨⟨0, by decide⟩, hx.1, hx.2, h1, h2⟩

theorem sixFlatSet_image_null [FiniteDimensional ℝ E] [SecondCountableTopology E]
    (hdim : (Module.finrank ℝ E : ℝ) < 7)
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' sixFlatSet U f) = 0 := by
  apply image_null_of_locally_image_null f (sixFlatSet U f)
  intro x hx
  have hf7 : ContDiffOn ℝ 7 f U := hf.of_le
    (WithTop.coe_le_coe.mpr (show (7 : ℕ∞) ≤ ⊤ from le_top))
  obtain ⟨r, hr, hnull⟩ := StableBernstein.W30.exists_ball_sixFlat_image_null
    hdim hU hf7 (fun _ hz => hz.1) (fun z hz => hz.2) hx
  exact ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, hnull⟩
end Strata

theorem scalar_sard_finrank_eq (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E],
      Module.finrank ℝ E = n → n ≤ 6 →
      ∀ (U : Set E), IsOpen U → ∀ (f : E → ℝ), ContDiffOn ℝ ∞ f U →
        volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E instN instS instF instC inst2 hdim hn U hU f hf
    by_cases hn0 : n = 0
    · have : Subsingleton E := Module.finrank_zero_iff.mp (hdim.trans hn0)
      have hz : volume ({f 0} : Set ℝ) = 0 := measure_singleton _
      apply measure_mono_null _ hz
      rintro t ⟨x, _, hxt⟩
      simpa only [mem_singleton_iff, Subsingleton.elim x 0] using hxt.symm
    · have hlower : ∀ L : E →L[ℝ] ℝ, L ≠ 0 →
          ∀ W : Set L.ker, IsOpen W → ∀ g : L.ker → ℝ,
          ContDiffOn ℝ ∞ g W → volume (g '' {t | t ∈ W ∧ fderiv ℝ g t = 0}) = 0 := by
        intro L hL W hW g hg
        have hk := regular_scalar_kernel_dimension L hL
        rw [hdim] at hk
        have hkn : Module.finrank ℝ L.ker < n := by omega
        have hk6 : Module.finrank ℝ L.ker ≤ 6 := by omega
        exact ih (Module.finrank ℝ L.ker) hkn L.ker rfl hk6 W hW g hg
      have hflat : volume (f '' sixFlatSet U f) = 0 := by
        apply sixFlatSet_image_null _ U hU f hf
        have : Module.finrank ℝ E ≤ 6 := by simpa only [hdim] using hn
        exact lt_of_le_of_lt (Nat.cast_le.mpr this) (by norm_num)
      have hstrata : ∀ i : Fin 5,
          volume (f '' nonflatCriticalStratum U f (i.val + 1)) = 0 := by
        intro i
        apply nonflat_stratum_image_null U hU f hf (i.val + 1)
          (nonflatCriticalStratum U f (i.val + 1))
          (fun _ hx => hx.1) (fun _ hx => hx.2.1)
          (fun _ hx => hx.2.2.1) (fun _ hx => hx.2.2.2) hlower
      have hnull : volume (f '' sixFlatSet U f ∪
          ⋃ i : Fin 5, f '' nonflatCriticalStratum U f (i.val + 1)) = 0 :=
        measure_union_null hflat (measure_iUnion_null_iff.mpr hstrata)
      apply measure_mono_null _ hnull
      rintro t ⟨x, hx, hxt⟩
      rcases criticalSet_subset_sixFlat_union_strata U f hx with hxf | hxs
      · exact Or.inl ⟨x, hxf, hxt⟩
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxs
        exact Or.inr (mem_iUnion.mpr ⟨i, x, hxi, hxt⟩)

theorem scalar_sard_finrank_le_six
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    (hdim : Module.finrank ℝ E ≤ 6)
    (U : Set E) (hU : IsOpen U) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
    volume (f '' {x | x ∈ U ∧ fderiv ℝ f x = 0}) = 0 :=
  scalar_sard_finrank_eq (Module.finrank ℝ E) E rfl hdim U hU f hf

end Bernstein.Sard

open MeasureTheory Manifold Set Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_SardProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The planar scalar Sard theorem follows from finite-dimensional
scalar Sard. Only the dimension-two specialization is used here. -/
open Set MeasureTheory
open scoped ContDiff
namespace CircleDomainRigidity

/-- Smooth planar scalar functions have null critical-value sets. -/
theorem smoothPlanarSard : SmoothPlanarSard := by
  intro f hf _
  have h := Bernstein.Sard.scalar_sard_finrank_le_six (E := ℂ)
    (by rw [Complex.finrank_real_complex]; norm_num) univ isOpen_univ f hf.contDiffOn
  simpa only [mem_univ, true_and] using h

end CircleDomainRigidity

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_DerivativeLipschitzPartition
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A countable measurable partition on which a C1 curve has nearly
its pointwise derivative norm as a Lipschitz bound. -/
open Set Function Filter Topology
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma local_derivative_lipschitz_bound
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {x : ℝ} (hx : x ∈ D) {ε : ℝ} (hε : 0 < ε) :
    ∃ (U : Set ℝ) (K : ℝ≥0), IsOpen U ∧ x ∈ U ∧ U ⊆ D ∧
      LipschitzOnWith K γ U ∧ ∀ y ∈ U, (K : ℝ) ≤ ‖d y‖ + ε := by
  let K : ℝ≥0 := ⟨‖d x‖ + ε / 2, by positivity⟩
  have hK : ‖d x‖₊ < K := by
    change ‖d x‖ < ‖d x‖ + ε / 2
    linarith
  obtain ⟨V, hV, hLip⟩ := (hd x hx).exists_lipschitzOnWith_of_nnnorm_lt K hK
  have hn : {y : ℝ | (K : ℝ) < ‖d y‖ + ε} ∈ 𝓝 x := by
    apply ((hc.continuousAt (hD.mem_nhds hx)).norm.add_const ε).preimage_mem_nhds
    exact Ioi_mem_nhds (by change ‖d x‖ + ε / 2 < ‖d x‖ + ε; linarith)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (inter_mem hV (inter_mem (hD.mem_nhds hx) hn))
  exact ⟨U, K, hU, hxU, fun y hy => (hUsub hy).2.1,
    hLip.mono (fun y hy => (hUsub hy).1), fun y hy => (hUsub hy).2.2.le⟩

lemma derivative_lipschitz_partition
    {D : Set ℝ} (hD : IsOpen D) (hne : D.Nonempty)
    {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : ℕ → Set ℝ) (K : ℕ → ℝ≥0),
      (∀ n, MeasurableSet (A n)) ∧ Pairwise (Disjoint on A) ∧ (⋃ n, A n) = D ∧
      (∀ n, LipschitzOnWith (K n) γ (A n)) ∧
      ∀ n y, y ∈ A n → (K n : ℝ) ≤ ‖d y‖ + ε := by
  classical
  let : Nonempty D := hne.to_subtype
  choose U K hUo hxU hUD hLip hnorm using fun x : D =>
    local_derivative_lipschitz_bound hD hd hc x.property hε
  have hcov : D ⊆ ⋃ x : D, U x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hlin : IsLindelof D := (isLindelof_iff_lindelofSpace).mpr inferInstance
  obtain ⟨v, hv⟩ := hlin.indexed_countable_subcover U hUo hcov
  let A : ℕ → Set ℝ := disjointed (fun n => U (v n))
  have hAU : ∀ n, A n ⊆ U (v n) := fun n => disjointed_subset _ n
  refine ⟨A, fun n => K (v n), (fun n => MeasurableSet.disjointed (fun j => (hUo (v j)).measurableSet) n),
    disjoint_disjointed _, ?_, (fun n => (hLip (v n)).mono (hAU n)), ?_⟩
  · change (⋃ n, disjointed (fun j => U (v j)) n) = D
    rw [iUnion_disjointed]
    exact (iUnion_subset (fun n => hUD (v n))).antisymm hv
  · exact fun n y hy => hnorm (v n) y (hAU n hy)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CurveHausdorffUpper
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The upper arclength bound for a C1 plane curve, first with an arbitrary
positive error, then exactly on every bounded Borel subset of its domain. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma curve_hausdorff_upper_add_error
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {S : Set ℝ} (hS : MeasurableSet S) (hSD : S ⊆ D) {ε : ℝ} (hε : 0 < ε) :
    (μH[1] : Measure ℂ) (γ '' S) ≤
      (∫⁻ t in S, ENNReal.ofReal ‖d t‖) + ENNReal.ofReal ε * volume S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨A, K, hA, hdisj, hcover, hLip, hnorm⟩ :=
    derivative_lipschitz_partition hD (hne.mono hSD) hd hc hε
  have hsets : (⋃ n, S ∩ A n) = S := by
    rw [← inter_iUnion, hcover, inter_eq_left.mpr hSD]
  calc
    (μH[1] : Measure ℂ) (γ '' S) =
        (μH[1] : Measure ℂ) (⋃ n, γ '' (S ∩ A n)) := by rw [← image_iUnion, hsets]
    _ ≤ ∑' n, (μH[1] : Measure ℂ) (γ '' (S ∩ A n)) := measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ t in S ∩ A n, ENNReal.ofReal (‖d t‖ + ε) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hbound : (μH[1] : Measure ℂ) (γ '' (S ∩ A n)) ≤
          (K n : ℝ≥0∞) * volume (S ∩ A n) := by
        simpa only [ENNReal.rpow_one, hausdorffMeasure_real] using
          ((hLip n).mono inter_subset_right).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
      apply hbound.trans
      rw [← Measure.restrict_apply_univ, ← lintegral_const]
      apply setLIntegral_mono' (hS.inter (hA n))
      intro t ht
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal (hnorm n t ht.2)
    _ = ∫⁻ t in S, ENNReal.ofReal (‖d t‖ + ε) := by
      rw [← lintegral_iUnion (fun n => hS.inter (hA n))
        (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right), hsets]
    _ = (∫⁻ t in S, ENNReal.ofReal ‖d t‖) + ENNReal.ofReal ε * volume S := by
      simp_rw [ENNReal.ofReal_add (norm_nonneg _) hε.le]
      rw [lintegral_add_right (f := fun t => ENNReal.ofReal ‖d t‖)
        (g := fun _ => ENNReal.ofReal ε) measurable_const]
      simp only [lintegral_const, Measure.restrict_apply_univ]

lemma curve_hausdorff_upper
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hSD : S ⊆ D) :
    (μH[1] : Measure ℂ) (γ '' S) ≤ ∫⁻ t in S, ENNReal.ofReal ‖d t‖ := by
  have hεlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht := (tendsto_const_nhds (x := ∫⁻ t in S, ENNReal.ofReal ‖d t‖)).add
    (ENNReal.Tendsto.mul_const hεlim (Or.inr (hb.measure_lt_top (μ := volume)).ne))
  simp only [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht (fun (n : ℕ) => curve_hausdorff_upper_add_error hD hd hc hS hSD (ε := 1 / (n + 1 : ℝ)) (by exact one_div_pos.mpr (by positivity)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CurveLowerDistance
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A strict derivative gives lower distance bounds on a small interval.
These bounds will supply the reverse arclength inequality. -/
open Set Function Filter Topology
open scoped Topology NNReal
noncomputable section
namespace CircleDomainRigidity

lemma real_clm_eq_toSpanSingleton (d : ℝ →L[ℝ] ℂ) :
    d = ContinuousLinearMap.toSpanSingleton ℝ (d 1) := by
  apply ContinuousLinearMap.ext
  intro t
  change d t = t • d 1
  simpa using d.map_smul t (1 : ℝ)

lemma norm_real_clm_apply (d : ℝ →L[ℝ] ℂ) (t : ℝ) :
    ‖d t‖ = ‖d‖ * |t| := by
  have hn := congrArg norm (real_clm_eq_toSpanSingleton d)
  rw [ContinuousLinearMap.norm_toSpanSingleton] at hn
  have ht : d t = t • d 1 := by simpa using d.map_smul t (1 : ℝ)
  rw [ht, norm_smul, Real.norm_eq_abs, ← hn, mul_comm]

lemma local_curve_lower_distance
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {x : ℝ} (hx : x ∈ D) {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ D ∧
      (∀ y ∈ U, ‖d y‖ ≤ ‖d x‖ + δ) ∧
      ∀ a ∈ U, ∀ b ∈ U, (‖d x‖ - δ) * dist a b ≤ dist (γ a) (γ b) := by
  have hR := (hd x hx).sub (d x).hasStrictFDerivAt
  let K : ℝ≥0 := ⟨δ, hδ.le⟩
  obtain ⟨V, hV, hLip⟩ := hR.exists_lipschitzOnWith_of_nnnorm_lt K (by simpa [K])
  have hn : {y : ℝ | ‖d y‖ < ‖d x‖ + δ} ∈ 𝓝 x :=
    (hc.continuousAt (hD.mem_nhds hx)).norm.preimage_mem_nhds
      (Iio_mem_nhds (by linarith))
  obtain ⟨U, hUsub, hUo, hxU⟩ := mem_nhds_iff.mp (inter_mem hV (inter_mem (hD.mem_nhds hx) hn))
  refine ⟨U, hUo, hxU, (fun y hy => (hUsub hy).2.1),
    (fun y hy => (hUsub hy).2.2.le), ?_⟩
  intro a ha b hb
  have hr := lipschitzOnWith_iff_norm_sub_le.mp hLip (hUsub ha).1 (hUsub hb).1
  have hre : (γ a - d x a) - (γ b - d x b) = (γ a - γ b) - d x (a - b) := by
    rw [map_sub]
    abel
  simp only [Pi.sub_apply] at hr
  rw [hre] at hr
  have ht : ‖d x (a - b)‖ ≤ ‖γ a - γ b‖ + ‖(γ a - γ b) - d x (a - b)‖ := by
    have he : d x (a - b) = (γ a - γ b) - ((γ a - γ b) - d x (a - b)) := by abel
    nth_rw 1 [he]
    exact norm_sub_le _ _
  rw [norm_real_clm_apply] at ht
  change ‖(γ a - γ b) - d x (a - b)‖ ≤ δ * ‖a - b‖ at hr
  rw [Real.norm_eq_abs] at hr
  rw [Real.dist_eq, dist_eq_norm]
  nlinarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CurveHausdorffLower
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lower distance estimates on countably many pieces give the reverse
arclength bound for an injective C1 curve. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma lower_distance_hausdorff
    {γ : ℝ → ℂ} {U S : Set ℝ} (hSU : S ⊆ U) (k : ℝ≥0)
    (h : ∀ a ∈ U, ∀ b ∈ U, (k : ℝ) * dist a b ≤ dist (γ a) (γ b)) :
    (k : ℝ≥0∞) * volume S ≤ (μH[1] : Measure ℂ) (γ '' S) := by
  by_cases hk : k = 0
  · simp [hk]
  have hkR : (0 : ℝ) < k := by exact_mod_cast pos_iff_ne_zero.mpr hk
  let T : Set U := {x | (x : ℝ) ∈ S}
  let g : U → ℂ := fun x => γ x
  have hg : AntilipschitzWith k⁻¹ g := by
    apply AntilipschitzWith.of_le_mul_dist
    intro a b
    change dist (a : ℝ) (b : ℝ) ≤ (k⁻¹ : ℝ≥0) * dist (γ a) (γ b)
    rw [NNReal.coe_inv, inv_mul_eq_div, le_div_iff₀ hkR]
    simpa only [mul_comm] using h a a.property b b.property
  have hT : Subtype.val '' T = S := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hx
      exact ⟨⟨x, hSU hx⟩, hx, rfl⟩
  have hmeasure : (μH[1] : Measure U) T = volume S := by
    rw [← isometry_subtype_coe.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)), hT,
      hausdorffMeasure_real]
  have himage : g '' T = γ '' S := by
    change (γ ∘ Subtype.val) '' T = γ '' S
    rw [image_comp, hT]
  have hb := hg.le_hausdorffMeasure_image (by norm_num : (0 : ℝ) ≤ 1) T
  rw [hmeasure, himage, ENNReal.rpow_one, ENNReal.coe_inv hk] at hb
  have hk0 : (k : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hk
  calc
    (k : ℝ≥0∞) * volume S ≤ (k : ℝ≥0∞) * ((k : ℝ≥0∞)⁻¹ * (μH[1] : Measure ℂ) (γ '' S)) :=
      mul_le_mul' le_rfl hb
    _ = (μH[1] : Measure ℂ) (γ '' S) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hk0 ENNReal.coe_ne_top, one_mul]

lemma derivative_lower_distance_partition
    {D : Set ℝ} (hD : IsOpen D) (hne : D.Nonempty)
    {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : ℕ → Set ℝ) (k : ℕ → ℝ≥0),
      (∀ n, MeasurableSet (A n)) ∧ Pairwise (Disjoint on A) ∧ (⋃ n, A n) = D ∧
      (∀ n a, a ∈ A n → ∀ b ∈ A n, (k n : ℝ) * dist a b ≤ dist (γ a) (γ b)) ∧
      ∀ n y, y ∈ A n → ‖d y‖ ≤ (k n : ℝ) + ε := by
  classical
  let : Nonempty D := hne.to_subtype
  choose U hUo hxU hUD hnorm hdist using fun x : D =>
    local_curve_lower_distance hD hd hc x.property (show 0 < ε / 2 by linarith)
  let k : D → ℝ≥0 := fun x => ⟨max (‖d x‖ - ε / 2) 0, le_max_right _ _⟩
  have hkdist : ∀ x : D, ∀ a ∈ U x, ∀ b ∈ U x,
      (k x : ℝ) * dist a b ≤ dist (γ a) (γ b) := by
    intro x a ha b hb
    change max (‖d (x : ℝ)‖ - ε / 2) 0 * dist a b ≤ dist (γ a) (γ b)
    by_cases hx : 0 ≤ ‖d (x : ℝ)‖ - ε / 2
    · simpa only [max_eq_left hx] using hdist x a ha b hb
    · simp only [max_eq_right (le_of_not_ge hx), zero_mul, dist_nonneg]
  have hknorm : ∀ x : D, ∀ y ∈ U x, ‖d y‖ ≤ (k x : ℝ) + ε := by
    intro x y hy
    have hm := le_max_left (‖d (x : ℝ)‖ - ε / 2) 0
    have hn := hnorm x y hy
    change ‖d y‖ ≤ max (‖d (x : ℝ)‖ - ε / 2) 0 + ε
    linarith
  have hcov : D ⊆ ⋃ x : D, U x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hlin : IsLindelof D := (isLindelof_iff_lindelofSpace).mpr inferInstance
  obtain ⟨v, hv⟩ := hlin.indexed_countable_subcover U hUo hcov
  let A : ℕ → Set ℝ := disjointed (fun n => U (v n))
  have hAU : ∀ n, A n ⊆ U (v n) := fun n => disjointed_subset _ n
  refine ⟨A, fun n => k (v n),
    (fun n => MeasurableSet.disjointed (fun j => (hUo (v j)).measurableSet) n),
    disjoint_disjointed _, ?_, ?_, ?_⟩
  · change (⋃ n, disjointed (fun j => U (v j)) n) = D
    rw [iUnion_disjointed]
    exact (iUnion_subset (fun n => hUD (v n))).antisymm hv
  · exact fun n a ha b hb => hkdist (v n) a (hAU n ha) b (hAU n hb)
  · exact fun n y hy => hknorm (v n) y (hAU n hy)

lemma curve_hausdorff_lower_add_error
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    (hi : InjOn γ D) {S : Set ℝ} (hS : MeasurableSet S) (hSD : S ⊆ D)
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ t in S, ENNReal.ofReal ‖d t‖) ≤
      (μH[1] : Measure ℂ) (γ '' S) + ENNReal.ofReal ε * volume S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨A, k, hA, hdisj, hcover, hdist, hnorm⟩ :=
    derivative_lower_distance_partition hD (hne.mono hSD) hd hc hε
  have hsets : (⋃ n, S ∩ A n) = S := by
    rw [← inter_iUnion, hcover, inter_eq_left.mpr hSD]
  have hdj : Pairwise (Disjoint on fun n => S ∩ A n) :=
    fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right
  have hcont : ContinuousOn γ D := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have him : ∀ n, MeasurableSet (γ '' (S ∩ A n)) := fun n =>
    (hS.inter (hA n)).image_of_continuousOn_injOn
      (hcont.mono (inter_subset_left.trans hSD)) (hi.mono (inter_subset_left.trans hSD))
  have hidj : Pairwise (Disjoint on fun n => γ '' (S ∩ A n)) := fun i j hij =>
    (hdj hij).image hi (inter_subset_left.trans hSD) (inter_subset_left.trans hSD)
  calc
    (∫⁻ t in S, ENNReal.ofReal ‖d t‖) =
        ∑' n, ∫⁻ t in S ∩ A n, ENNReal.ofReal ‖d t‖ := by
      rw [← lintegral_iUnion (fun n => hS.inter (hA n)) hdj, hsets]
    _ ≤ ∑' n, ((μH[1] : Measure ℂ) (γ '' (S ∩ A n)) + ENNReal.ofReal ε * volume (S ∩ A n)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hb : (∫⁻ t in S ∩ A n, ENNReal.ofReal ‖d t‖) ≤
          ((k n : ℝ≥0∞) + ENNReal.ofReal ε) * volume (S ∩ A n) := by
        rw [← Measure.restrict_apply_univ, ← lintegral_const]
        apply setLIntegral_mono' (hS.inter (hA n))
        intro t ht
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (NNReal.coe_nonneg _) hε.le]
        exact ENNReal.ofReal_le_ofReal (hnorm n t ht.2)
      rw [add_mul] at hb
      exact hb.trans (add_le_add
        (lower_distance_hausdorff inter_subset_right (k n) (hdist n)) le_rfl)
    _ = (∑' n, (μH[1] : Measure ℂ) (γ '' (S ∩ A n))) +
        ENNReal.ofReal ε * ∑' n, volume (S ∩ A n) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ = (μH[1] : Measure ℂ) (γ '' S) + ENNReal.ofReal ε * volume S := by
      rw [← measure_iUnion hidj him, ← measure_iUnion hdj (fun n => hS.inter (hA n)),
        ← image_iUnion, hsets]

lemma curve_hausdorff_lower
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    (hi : InjOn γ D) {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hSD : S ⊆ D) :
    (∫⁻ t in S, ENNReal.ofReal ‖d t‖) ≤ (μH[1] : Measure ℂ) (γ '' S) := by
  have hεlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht := (tendsto_const_nhds (x := (μH[1] : Measure ℂ) (γ '' S))).add
    (ENNReal.Tendsto.mul_const hεlim (Or.inr (hb.measure_lt_top (μ := volume)).ne))
  simp only [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht (fun (n : ℕ) => curve_hausdorff_lower_add_error hD hd hc hi hS hSD
    (ε := 1 / (n + 1 : ℝ)) (one_div_pos.mpr (by positivity)))

lemma curve_hausdorff_eq_integral
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    (hi : InjOn γ D) {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hSD : S ⊆ D) :
    (μH[1] : Measure ℂ) (γ '' S) = ∫⁻ t in S, ENNReal.ofReal ‖d t‖ :=
  (curve_hausdorff_upper hD hd hc hS hb hSD).antisymm
    (curve_hausdorff_lower hD hd hc hi hS hb hSD)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_WeightedCurveLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The arclength identity as a measure identity and its weighted version. -/
open Set Function MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity

lemma curve_length_map_measure
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    (hi : InjOn γ D) {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hSD : S ⊆ D) :
    Measure.map (curveOnSet S γ)
      ((volume.restrict S).withDensity (fun t => ENNReal.ofReal ‖d t‖)) =
      (μH[1] : Measure ℂ).restrict (γ '' S) := by
  classical
  let g : ℝ → ℂ := curveOnSet S γ
  have hγ : ContinuousOn γ S := fun x hx => (hd x (hSD hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hγ.measurable_piecewise continuousOn_const hS
  apply Measure.ext
  intro B hB
  have hT : MeasurableSet (S ∩ g ⁻¹' B) := hS.inter (hg hB)
  have him : γ '' (S ∩ g ⁻¹' B) = B ∩ γ '' S := by
    ext z
    constructor
    · rintro ⟨t, ⟨ht, htB⟩, rfl⟩
      exact ⟨by simpa only [mem_preimage, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht] using htB, ⟨t, ht, rfl⟩⟩
    · rintro ⟨hz, t, ht, rfl⟩
      refine ⟨t, ⟨ht, ?_⟩, rfl⟩
      simpa only [mem_preimage, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht] using hz
  change Measure.map g _ B = _
  rw [Measure.map_apply hg hB, withDensity_apply _ (hg hB), Measure.restrict_restrict (hg hB),
    Measure.restrict_apply hB]
  rw [inter_comm (g ⁻¹' B) S, ← curve_hausdorff_eq_integral hD hd hc hi hT (hb.subset inter_subset_left)
    (inter_subset_left.trans hSD), him]

lemma weighted_curve_length
    {D : Set ℝ} (hD : IsOpen D) {γ : ℝ → ℂ} {d : ℝ → ℝ →L[ℝ] ℂ}
    (hd : ∀ x ∈ D, HasStrictFDerivAt γ (d x) x) (hc : ContinuousOn d D)
    (hi : InjOn γ D) {S : Set ℝ} (hS : MeasurableSet S) (hb : IsBounded S) (hSD : S ⊆ D)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ z in γ '' S, q z ∂μH[1]) =
      ∫⁻ t in S, q (γ t) * ENNReal.ofReal ‖d t‖ := by
  classical
  let g : ℝ → ℂ := curveOnSet S γ
  have hγ : ContinuousOn γ S := fun x hx => (hd x (hSD hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hγ.measurable_piecewise continuousOn_const hS
  have hdmeas : AEMeasurable (fun t => ENNReal.ofReal ‖d t‖) (volume.restrict S) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hc.mono hSD).norm).aemeasurable hS
  rw [← curve_length_map_measure hD hd hc hi hS hb hSD, lintegral_map hq hg,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun t => q (g t)) hdmeas (hq.comp hg).aemeasurable]
  apply setLIntegral_congr_fun hS
  intro t ht
  simp only [Pi.mul_apply, g, curveOnSet, piecewise_eq_of_mem S γ (fun _ => 0) ht, mul_comm]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_ShrinkingLengthFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diameter covers for codimension-one fibers. The estimate is also
useful on the critical set, where a positive chart Jacobian is unavailable. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma hausdorff_one_fiber_le_liminf_cover
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    (A : Set X) (f : X → Y) (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (T : ℕ → ℕ → Set X) (hT : ∀ n k, ediam (T n k) ≤ r n)
    (hcover : ∀ n, A ⊆ ⋃ k, T n k) (y : Y) :
    (μH[1] : Measure X) (A ∩ f ⁻¹' {y}) ≤
      liminf (fun n => ∑' k, if y ∈ closure (f '' T n k) then ediam (T n k) else 0) atTop := by
  let S (n k : ℕ) := A ∩ f ⁻¹' {y} ∩ T n k
  have hS : ∀ n k, ediam (S n k) ≤ r n := fun n k =>
    (ediam_mono inter_subset_right).trans (hT n k)
  have hcov : ∀ n, A ∩ f ⁻¹' {y} ⊆ ⋃ k, S n k := by
    intro n x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcover n hx.1)
    exact mem_iUnion.mpr ⟨k, hx, hk⟩
  have h := Measure.hausdorffMeasure_le_liminf_tsum 1 (A ∩ f ⁻¹' {y}) r hr S
    (.of_forall hS) (.of_forall hcov)
  simp only [ENNReal.rpow_one] at h
  apply h.trans
  apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
  apply Eventually.of_forall
  intro n
  apply ENNReal.tsum_le_tsum
  intro k
  split_ifs with hy
  · exact ediam_mono inter_subset_right
  · have hempty : S n k = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxT⟩
      exact hy (subset_closure ⟨x, hxT, hx.2⟩)
    simp only [hempty, ediam_empty]
    exact le_rfl

lemma iSup_nonempty_ediam_sq {X : Type*} [EMetricSpace X] (S : Set X) :
    (⨆ _ : S.Nonempty, ediam S ^ (2 : ℝ)) = ediam S ^ (2 : ℝ) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  · simp only [iSup_pos hS]

lemma exists_small_quadratic_hausdorff_cover
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[2] : Measure X) A < ∞)
    (r ε : ℝ≥0∞) (hr : 0 < r) (hε : 0 < ε) :
    ∃ T : ℕ → Set X, A ⊆ ⋃ k, T k ∧ (∀ k, ediam (T k) ≤ r) ∧
      (∑' k, ediam (T k) ^ (2 : ℕ)) < (μH[2] : Measure X) A + ε := by
  have hle : (⨅ (T : ℕ → Set X) (_ : A ⊆ ⋃ k, T k) (_ : ∀ k, ediam (T k) ≤ r),
      ∑' k, ⨆ _ : (T k).Nonempty, ediam (T k) ^ (2 : ℝ)) ≤ (μH[2] : Measure X) A := by
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup_of_le r (le_iSup_of_le hr le_rfl)
  have hlt := hle.trans_lt (ENNReal.lt_add_right hA.ne hε.ne')
  simp only [iInf_lt_iff] at hlt
  obtain ⟨T, hc, hd, hcost⟩ := hlt
  refine ⟨T, hc, hd, ?_⟩
  simp_rw [iSup_nonempty_ediam_sq] at hcost
  simpa only [ENNReal.rpow_two] using hcost

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LipschitzLengthFiberMajorant
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable majorant for the lengths of Lipschitz scalar fibers.
Only a finite two-dimensional Hausdorff measure is needed. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma exists_lipschitz_length_fiber_majorant
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[2] : Measure X) A < ∞)
    (L : ℝ≥0) (f : X → ℝ) (hf : LipschitzWith L f)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, (μH[1] : Measure X) (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      (∫⁻ y, G y) ≤ (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ) := by
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hε : ∀ n, 0 < ε n := fun n => ENNReal.ofReal_pos.mpr (by positivity)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose T hcover hdiam hcost using fun n =>
    exists_small_quadratic_hausdorff_cover A hA (ε n) δ (hε n) hδ
  let g : ℕ → ℝ → ℝ≥0∞ := fun n y =>
    ∑' k, if y ∈ closure (f '' T n k) then ediam (T n k) else 0
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    apply Measurable.tsum
    intro k
    exact Measurable.ite isClosed_closure.measurableSet measurable_const measurable_const
  have hgint : ∀ n, (∫⁻ y, g n y) ≤ (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ) := by
    intro n
    calc
      (∫⁻ y, g n y) = ∑' k, ediam (T n k) * volume (closure (f '' T n k)) := by
        rw [show g n = fun y => ∑' k, (closure (f '' T n k)).indicator
          (fun _ => ediam (T n k)) y by rfl]
        rw [lintegral_tsum (fun k => measurable_const.indicator
          isClosed_closure.measurableSet |>.aemeasurable)]
        simp only [lintegral_indicator isClosed_closure.measurableSet, lintegral_const,
          Measure.restrict_apply_univ]
      _ ≤ ∑' k, ediam (T n k) * ((L : ℝ≥0∞) * ediam (T n k)) := by
        apply ENNReal.tsum_le_tsum
        intro k
        apply mul_le_mul' le_rfl
        exact (Real.volume_le_diam _).trans ((ediam_closure _).le.trans (hf.ediam_image_le _))
      _ = (L : ℝ≥0∞) * ∑' k, ediam (T n k) ^ (2 : ℕ) := by
        simp_rw [mul_left_comm (ediam _) (L : ℝ≥0∞), ← pow_two]
        exact ENNReal.tsum_mul_left
      _ ≤ (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ) := by
        exact mul_le_mul' le_rfl (hcost n).le
  refine ⟨fun y => liminf (fun n => g n y) atTop, Measurable.liminf hgm,
    hausdorff_one_fiber_le_liminf_cover A f ε hεlim T hdiam hcover, ?_⟩
  apply (lintegral_liminf_le hgm).trans
  have hm : liminf (fun n => ∫⁻ y, g n y) atTop ≤
      liminf (fun _ : ℕ => (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ)) atTop :=
    liminf_le_liminf (Eventually.of_forall hgint)
  simpa only [liminf_const] using hm

lemma exists_exact_lipschitz_length_fiber_majorant
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : Set X) (hA : (μH[2] : Measure X) A < ∞)
    (L : ℝ≥0) (f : X → ℝ) (hf : LipschitzWith L f) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, (μH[1] : Measure X) (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      (∫⁻ y, G y) ≤ (L : ℝ≥0∞) * (μH[2] : Measure X) A := by
  let δ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hδ : ∀ n, 0 < δ n := fun n => ENNReal.ofReal_pos.mpr (by positivity)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose G hG hbound hint using fun n => exists_lipschitz_length_fiber_majorant A hA L f hf (δ n) (hδ n)
  refine ⟨fun y => ⨅ n, G n y, Measurable.iInf hG,
    (fun y => le_iInf (fun n => hbound n y)), ?_⟩
  have ht : Tendsto (fun n => (L : ℝ≥0∞) * ((μH[2] : Measure X) A + δ n)) atTop
      (𝓝 ((L : ℝ≥0∞) * (μH[2] : Measure X) A)) := by
    simpa only [add_zero] using
      ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hδlim) (Or.inr ENNReal.coe_ne_top)
  apply ge_of_tendsto' ht
  intro n
  exact (lintegral_mono (fun y => iInf_le (fun k => G k y) n)).trans (hint n)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_CriticalFiberLength
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical points of a C1 scalar planar map contribute zero fiber length
for almost every level. No assertion that C1 critical values have measure
zero is used. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma critical_fiber_majorant
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {A : Set ℂ} (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hAfin : (μH[2] : Measure ℂ) A < ∞)
    (hcrit : ∀ x ∈ A, fderiv ℝ f x = 0) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ G : ℝ → ℝ≥0∞, Measurable G ∧
      (∀ y, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) ≤ G y) ∧
      (∫⁻ y, G y) ≤ (ε : ℝ≥0∞) * (μH[2] : Measure ℂ) A := by
  obtain ⟨U, L, hU, hcover, hUD, hLip, hnorm⟩ :=
    exists_countable_derivative_cover hD hf (show (0 : ℝ) < ε from hε)
  let P : ℕ → Set ℂ := fun n => A ∩ disjointed U n
  have hP : ∀ n, MeasurableSet (P n) := fun n =>
    hA.inter (MeasurableSet.disjointed (fun j => (hU j).measurableSet) n)
  have hPA : ∀ n, P n ⊆ A := fun _ => inter_subset_left
  have hPU : ∀ n, P n ⊆ U n := fun n => inter_subset_right.trans (disjointed_subset U n)
  have hdj : Pairwise (Disjoint on P) := fun i j hij =>
    (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  have heqA : (⋃ n, P n) = A := by
    dsimp only [P]
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left.mpr (hAD.trans hcover)]
  have hLP : ∀ n, LipschitzOnWith ε f (P n) := by
    intro n
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro a ha b hb
    have hL : (L n : ℝ) ≤ ε := by
      have h := hnorm n a (hPU n ha)
      simpa only [hcrit a (hPA n ha), norm_zero, zero_add] using h
    exact ((hLip n).dist_le_mul a (hPU n ha) b (hPU n hb)).trans
      (mul_le_mul_of_nonneg_right hL (dist_nonneg))
  choose g hg heq using fun n => (hLP n).extend_real
  have hfin : ∀ n, (μH[2] : Measure ℂ) (P n) < ∞ := fun n =>
    (measure_mono (hPA n)).trans_lt hAfin
  choose G hG hbound hint using fun n =>
    exists_exact_lipschitz_length_fiber_majorant (P n) (hfin n) ε (g n) (hg n)
  have heqfiber : ∀ n y, P n ∩ (g n) ⁻¹' {y} = P n ∩ f ⁻¹' {y} := by
    intro n y
    ext x
    by_cases hx : x ∈ P n
    · simp only [mem_inter_iff, hx, true_and, mem_preimage, mem_singleton_iff, ← heq n hx]
    · simp only [mem_inter_iff, hx, false_and]
  refine ⟨fun y => ∑' n, G n y, Measurable.tsum hG, ?_, ?_⟩
  · intro y
    calc
      (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) =
          (μH[1] : Measure ℂ) (⋃ n, P n ∩ f ⁻¹' {y}) := by rw [← iUnion_inter, heqA]
      _ ≤ ∑' n, (μH[1] : Measure ℂ) (P n ∩ f ⁻¹' {y}) := measure_iUnion_le _
      _ ≤ ∑' n, G n y := ENNReal.tsum_le_tsum (fun n => by rw [← heqfiber]; exact hbound n y)
  · rw [lintegral_tsum (fun n => (hG n).aemeasurable)]
    calc
      (∑' n, ∫⁻ y, G n y) ≤ ∑' n, (ε : ℝ≥0∞) * (μH[2] : Measure ℂ) (P n) :=
        ENNReal.tsum_le_tsum hint
      _ = (ε : ℝ≥0∞) * (μH[2] : Measure ℂ) A := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion hdj hP, heqA]

lemma ae_zero_critical_fiber_length
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {A : Set ℂ} (hA : MeasurableSet A) (hAD : A ⊆ D)
    (hAfin : (μH[2] : Measure ℂ) A < ∞)
    (hcrit : ∀ x ∈ A, fderiv ℝ f x = 0) :
    ∀ᵐ y, (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) = 0 := by
  let ε : ℕ → ℝ≥0 := fun n => ⟨1 / (n + 1 : ℝ), by positivity⟩
  have hε : ∀ n, 0 < ε n := fun n => by change (0 : ℝ) < 1 / (n + 1 : ℝ); positivity
  choose G hG hbound hint using fun n => critical_fiber_majorant hD hf hA hAD hAfin hcrit (ε n) (hε n)
  let H : ℝ → ℝ≥0∞ := fun y => ⨅ n, G n y
  have hH : Measurable H := Measurable.iInf hG
  have hεlim : Tendsto (fun n => (ε n : ℝ≥0∞)) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have heq : (fun n => (ε n : ℝ≥0∞)) = fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
      funext n
      exact (ENNReal.ofReal_eq_coe_nnreal (by positivity)).symm
    rw [heq]
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using h
  have hintH : (∫⁻ y, H y) = 0 := by
    apply le_antisymm _ bot_le
    have ht := ENNReal.Tendsto.mul_const hεlim (Or.inr hAfin.ne)
    simp only [zero_mul] at ht
    apply ge_of_tendsto' ht
    intro n
    exact (lintegral_mono (fun y => iInf_le (fun k => G k y) n)).trans (hint n)
  filter_upwards [(lintegral_eq_zero_iff hH).mp hintH] with y hy
  apply le_antisymm _ bot_le
  change H y = 0 at hy
  exact (le_iInf (fun n => hbound n y)).trans_eq hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlaneCriticalFibers
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded plane sets have finite two-dimensional Hausdorff measure;
exhaustion therefore removes the finite-measure restriction in the
critical-fiber argument. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma bounded_plane_hausdorff_two_lt_top {A : Set ℂ} (hA : IsBounded A) :
    (μH[2] : Measure ℂ) A < ∞ := by
  have h := Complex.antilipschitz_equivRealProd.le_hausdorffMeasure_image
    (by norm_num : (0 : ℝ) ≤ 2) A
  rw [MeasureTheory.hausdorffMeasure_prod_real] at h
  apply h.trans_lt
  apply ENNReal.mul_lt_top
  · finiteness
  · exact (Complex.lipschitz_equivRealProd.isBounded_image hA).measure_lt_top

lemma measurableSet_planar_critical {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    MeasurableSet (D ∩ {z | fderiv ℝ f z = 0}) := by
  let g : ℂ → ℝ := D.piecewise (fun z => ‖fderiv ℝ f z‖) (fun _ => 0)
  have hc := (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).norm
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const hD.measurableSet
  have heq : D ∩ {z | fderiv ℝ f z = 0} = D ∩ g ⁻¹' {0} := by
    ext z
    by_cases hz : z ∈ D <;> simp [g, hz]
  rw [heq]
  exact hD.measurableSet.inter (hg (measurableSet_singleton _))

lemma ae_zero_planar_critical_fiber {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    ∀ᵐ y, (μH[1] : Measure ℂ) ((D ∩ {z | fderiv ℝ f z = 0}) ∩ f ⁻¹' {y}) = 0 := by
  let A : Set ℂ := D ∩ {z | fderiv ℝ f z = 0}
  have hA : MeasurableSet A := measurableSet_planar_critical hD hf
  let S : ℕ → Set ℂ := fun n => A ∩ closedBall 0 n
  have hS : ∀ n, MeasurableSet (S n) := fun _ => hA.inter isClosed_closedBall.measurableSet
  have hcover : (⋃ n, S n) = A := by
    simp only [S, ← inter_iUnion, iUnion_closedBall_nat, inter_univ]
  have hn : ∀ n, ∀ᵐ y, (μH[1] : Measure ℂ) (S n ∩ f ⁻¹' {y}) = 0 := by
    intro n
    apply ae_zero_critical_fiber_length hD hf (hS n)
    · exact inter_subset_left.trans inter_subset_left
    · exact bounded_plane_hausdorff_two_lt_top (isBounded_closedBall.subset inter_subset_right)
    · exact fun z hz => hz.1.2
  filter_upwards [ae_all_iff.mpr hn] with y hy
  change (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) = 0
  apply le_antisymm _ bot_le
  calc
    (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) =
        (μH[1] : Measure ℂ) (⋃ n, S n ∩ f ⁻¹' {y}) := by rw [← iUnion_inter, hcover]
    _ ≤ ∑' n, (μH[1] : Measure ℂ) (S n ∩ f ⁻¹' {y}) := measure_iUnion_le _
    _ = 0 := by simp only [hy, tsum_zero]

lemma ae_zero_weighted_planar_critical_fiber {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) (q : ℂ → ℝ≥0∞) :
    ∀ᵐ y, (∫⁻ z in ((D ∩ {z | fderiv ℝ f z = 0}) ∩ f ⁻¹' {y}), q z ∂μH[1]) = 0 := by
  filter_upwards [ae_zero_planar_critical_fiber hD hf] with y hy
  rw [Measure.restrict_eq_zero.mpr hy]
  exact lintegral_zero_measure q

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_RegularC1Chart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A local C1 normal form, retaining the actual first coordinate, on the
open domain of a scalar planar function. -/
open Set Filter Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_c1_planar_level_chart {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) {z : ℂ} (hzD : z ∈ D)
    (hz : fderiv ℝ f z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ (ℝ × ℝ), z ∈ e.source ∧ e.source ⊆ D ∧
      (∀ w, (e w).1 = f w) ∧ ContDiffOn ℝ 1 e e.source ∧
      ContDiffOn ℝ 1 e.symm e.target := by
  let L := fderiv ℝ f z
  have hL : L ≠ 0 := hz
  have hlin : (L : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    apply hL
    ext w
    exact congrArg (fun T : ℂ →ₗ[ℝ] ℝ => T w) h
  have hsurj : L.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hlin
  have hd : HasStrictFDerivAt f L z :=
    (hf.contDiffAt (hD.mem_nhds hzD)).hasStrictFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let p := hd.implicitFunctionDataOfComplemented f L hsurj
    L.ker_closedComplemented_of_finiteDimensional_range
  let k : L.ker ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_ker_planar_functional hL, Module.finrank_self])
  let c : (ℝ × L.ker) ≃L[ℝ] (ℝ × ℝ) :=
    ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) k
  let g : ℂ → ℝ × ℝ := c ∘ p.prodFun
  have hp : ContDiffOn ℝ 1 p.prodFun D := by
    apply hf.prodMk
    exact ((Classical.choose L.ker_closedComplemented_of_finiteDimensional_range).contDiff.comp
      (contDiff_id.sub contDiff_const)).contDiffOn
  have hg : ContDiffOn ℝ 1 g D := c.contDiff.comp_contDiffOn hp
  let d : ℂ ≃L[ℝ] (ℝ × L.ker) :=
    p.leftDeriv.equivProdOfSurjectiveOfIsCompl p.rightDeriv
      p.range_leftDeriv p.range_rightDeriv p.isCompl_ker
  have hgd : HasFDerivAt g ((d.trans c : ℂ ≃L[ℝ] (ℝ × ℝ)) : ℂ →L[ℝ] (ℝ × ℝ)) z :=
    c.hasFDerivAt.comp z p.hasStrictFDerivAt.hasFDerivAt
  have hgz := hg.contDiffAt (hD.mem_nhds hzD)
  let e₀ := hgz.toOpenPartialHomeomorph g hgd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hinv : (fderiv ℝ g z).IsInvertible := by
    rw [hgd.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  have hN : {w | w ∈ D ∧ (fderiv ℝ g w).IsInvertible} ∈ 𝓝 z := by
    apply inter_mem (hD.mem_nhds hzD)
    exact (hgz.continuousAt_fderiv (by simp)).preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds hinv)
  obtain ⟨U, hU, hUo, hzU⟩ := mem_nhds_iff.mp hN
  let e := e₀.restrOpen U hUo
  have he : (e : ℂ → ℝ × ℝ) = g := rfl
  have heD : e.source ⊆ D := fun w hw => (hU hw.2).1
  refine ⟨e, ⟨hgz.mem_toOpenPartialHomeomorph_source hgd (by simp), hzU⟩, heD,
    (fun _ => rfl), he ▸ hg.mono heD, ?_⟩
  intro y hy
  obtain ⟨d', hd'⟩ := (hU (e.map_target hy).2).2
  apply ContDiffAt.contDiffWithinAt
  apply e.contDiffAt_symm hy (f₀' := d')
  · rw [he, hd']
    exact (hg.contDiffAt (hD.mem_nhds (heD (e.map_target hy)))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) |>.hasFDerivAt
  · rw [he]
    exact hg.contDiffAt (hD.mem_nhds (heD (e.map_target hy)))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_ComplexC1LevelChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular scalar coordinates with both ambient spaces represented by ℂ. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_complex_c1_level_chart {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) {z : ℂ} (hzD : z ∈ D)
    (hz : fderiv ℝ f z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z ∈ e.source ∧ e.source ⊆ D ∧
      (∀ w, (e w).re = f w) ∧ ContDiffOn ℝ 1 e e.source ∧
      ContDiffOn ℝ 1 e.symm e.target := by
  obtain ⟨e, hz, heD, he, heC, hiC⟩ := exists_c1_planar_level_chart hD hf hzD hz
  let g := e.transHomeomorph Complex.equivRealProdCLM.symm.toHomeomorph
  refine ⟨g, hz, heD, ?_, ?_, ?_⟩
  · intro w
    exact he w
  · change ContDiffOn ℝ 1 (Complex.equivRealProdCLM.symm ∘ e) e.source
    exact Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn heC
  · change ContDiffOn ℝ 1 (e.symm ∘ Complex.equivRealProdCLM) g.target
    apply hiC.comp Complex.equivRealProdCLM.contDiff.contDiffOn
    intro y hy
    exact hy

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_VerticalLevelCurve
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical parameter curves of a C1 inverse level chart. -/
open Set Function MeasureTheory Metric Bornology
open scoped ENNReal Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma coareaVerticalLine_contDiff (t : ℝ) : ContDiff ℝ 1 (coareaVerticalLine t) :=
  contDiff_const.add (ContinuousLinearMap.toSpanSingleton ℝ Complex.I).contDiff

lemma coareaVerticalLine_hasFDerivAt (t s : ℝ) :
    HasFDerivAt (coareaVerticalLine t) (ContinuousLinearMap.toSpanSingleton ℝ Complex.I) s := by
  simpa only [coareaVerticalLine] using!
    (ContinuousLinearMap.toSpanSingleton ℝ Complex.I).hasFDerivAt.const_add (t : ℂ)

lemma coareaVerticalLine_injective (t : ℝ) : Injective (coareaVerticalLine t) := by
  intro a b h
  simpa only [coareaVerticalLine_im] using congrArg Complex.im h

lemma vertical_slice_bounded {T : Set ℂ} (hT : IsBounded T) (t : ℝ) :
    IsBounded ((coareaVerticalLine t) ⁻¹' T) := by
  apply (hT.isCompact_closure.image Complex.continuous_im).isBounded.subset
  intro s hs
  exact ⟨coareaVerticalLine t s, subset_closure hs, coareaVerticalLine_im t s⟩

lemma vertical_inverse_curve_fderiv_norm
    (e : OpenPartialHomeomorph ℂ ℂ) (heI : ContDiffOn ℝ 1 e.symm e.target)
    {t s : ℝ} (hs : coareaVerticalLine t s ∈ e.target) :
    ‖fderiv ℝ (e.symm ∘ coareaVerticalLine t) s‖ =
      ‖fderiv ℝ e.symm (coareaVerticalLine t s) Complex.I‖ := by
  have hd := ((heI.contDiffAt (e.open_target.mem_nhds hs)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  rw [(hd.comp s (coareaVerticalLine_hasFDerivAt t s)).fderiv]
  have hn := norm_real_clm_apply
    ((fderiv ℝ e.symm (coareaVerticalLine t s)).comp (ContinuousLinearMap.toSpanSingleton ℝ Complex.I)) 1
  simpa only [abs_one, mul_one, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hn.symm

lemma weighted_vertical_inverse_curve
    (e : OpenPartialHomeomorph ℂ ℂ) (heI : ContDiffOn ℝ 1 e.symm e.target)
    {T : Set ℂ} (hT : MeasurableSet T) (hb : IsBounded T) (hTe : T ⊆ e.target)
    (t : ℝ) {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    (∫⁻ z in (e.symm ∘ coareaVerticalLine t) '' ((coareaVerticalLine t) ⁻¹' T), q z ∂μH[1]) =
      ∫⁻ s in (coareaVerticalLine t) ⁻¹' T,
        q (e.symm (coareaVerticalLine t s)) * ENNReal.ofReal ‖fderiv ℝ e.symm (coareaVerticalLine t s) Complex.I‖ := by
  let V := (coareaVerticalLine t) ⁻¹' e.target
  have hV : IsOpen V := e.open_target.preimage (coareaVerticalLine_contDiff t).continuous
  have hcurve : ContDiffOn ℝ 1 (e.symm ∘ coareaVerticalLine t) V :=
    heI.comp (coareaVerticalLine_contDiff t).contDiffOn (fun _ h => h)
  have hd : ∀ s ∈ V, HasStrictFDerivAt (e.symm ∘ coareaVerticalLine t)
      (fderiv ℝ (e.symm ∘ coareaVerticalLine t) s) s := fun s hs =>
    (hcurve.contDiffAt (hV.mem_nhds hs)).hasStrictFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hc := hcurve.continuousOn_fderiv_of_isOpen hV (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hi : InjOn (e.symm ∘ coareaVerticalLine t) V := by
    intro a ha b hb heq
    exact coareaVerticalLine_injective t (e.symm.injOn ha hb heq)
  have hS : MeasurableSet ((coareaVerticalLine t) ⁻¹' T) := hT.preimage (coareaVerticalLine_contDiff t).continuous.measurable
  have hSV : (coareaVerticalLine t) ⁻¹' T ⊆ V := fun _ hs => hTe hs
  rw [weighted_curve_length hV hd hc hi hS (vertical_slice_bounded hb t) hSV hq]
  apply setLIntegral_congr_fun hS
  intro s hs
  dsimp only
  rw [vertical_inverse_curve_fderiv_norm e heI (hTe hs)]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedCoareaUnion
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable measurable disjoint assembly of the weighted coarea identity. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma measurableSet_restricted_scalar_level {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) {A : Set ℂ} (hA : MeasurableSet A)
    (hAD : A ⊆ D) (t : ℝ) : MeasurableSet (A ∩ {z | f z = t}) := by
  have he : A ∩ {z | f z = t} = A ∩ (D ∩ {z | f z = t}) := by
    ext z
    constructor
    · exact fun hz => ⟨hz.1, hAD hz.1, hz.2⟩
    · exact fun hz => ⟨hz.1, hz.2.2⟩
  rw [he]
  exact hA.inter (measurableSet_scalar_level hD hf t)

lemma weightedScalarLevelLength_iUnion {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (A : ℕ → Set ℂ)
    (hA : ∀ n, MeasurableSet (A n)) (hdj : Pairwise (Disjoint on A))
    (hAD : ∀ n, A n ⊆ D) (q : ℂ → ℝ≥0∞) (t : ℝ) :
    weightedScalarLevelLength (⋃ n, A n) f q t = ∑' n, weightedScalarLevelLength (A n) f q t := by
  simp only [weightedScalarLevelLength, iUnion_inter]
  apply lintegral_iUnion (fun n => measurableSet_restricted_scalar_level hD hf (hA n) (hAD n) t)
  exact fun i j hij => (hdj hij).mono inter_subset_left inter_subset_left

lemma weighted_coarea_iUnion {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContinuousOn f D) (A : ℕ → Set ℂ)
    (hA : ∀ n, MeasurableSet (A n)) (hdj : Pairwise (Disjoint on A))
    (hAD : ∀ n, A n ⊆ D) (q : ℂ → ℝ≥0∞)
    (hlocal : ∀ n, WeightedScalarCoareaIdentity (A n) f q) :
    WeightedScalarCoareaIdentity (⋃ n, A n) f q := by
  have heq : weightedScalarLevelLength (⋃ n, A n) f q =
      fun t => ∑' n, weightedScalarLevelLength (A n) f q t :=
    funext (weightedScalarLevelLength_iUnion hD hf A hA hdj hAD q)
  refine ⟨by rw [heq]; exact AEMeasurable.tsum (fun n => (hlocal n).1), ?_⟩
  rw [heq, lintegral_tsum (fun n => (hlocal n).1)]
  calc
    (∑' n, ∫⁻ t, weightedScalarLevelLength (A n) f q t) =
        ∑' n, ∫⁻ z in A n, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ :=
      tsum_congr (fun n => (hlocal n).2)
    _ = _ := (lintegral_iUnion hA hdj (fun z => q z * ENNReal.ofReal ‖fderiv ℝ f z‖)).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_LevelChartJacobian
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inverse level chart has the exact Jacobian factor needed by coarea. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma level_chart_inverse_jacobian
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (e : OpenPartialHomeomorph ℂ ℂ) (heD : e.source ⊆ D)
    (he : ∀ z, (e z).re = f z) (heI : ContDiffOn ℝ 1 e.symm e.target)
    {y : ℂ} (hy : y ∈ e.target) :
    ‖fderiv ℝ f (e.symm y)‖ * |(fderiv ℝ e.symm y).det| =
      ‖fderiv ℝ e.symm y Complex.I‖ := by
  have hA := (hf.contDiffAt (hD.mem_nhds (heD (e.map_target hy)))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hB := (heI.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hfun : (f ∘ e.symm) =ᶠ[𝓝 y] Complex.re := by
    filter_upwards [e.open_target.mem_nhds hy] with w hw
    change f (e.symm w) = w.re
    rw [← he, e.right_inv hw]
  have hder : (fderiv ℝ f (e.symm y)).comp (fderiv ℝ e.symm y) = Complex.reCLM :=
    ((hA.hasFDerivAt.comp y hB.hasFDerivAt).congr_of_eventuallyEq hfun.symm).unique
      Complex.reCLM.hasFDerivAt
  apply coarea_covector_jacobian
  · have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) hder
    simpa only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.one_re] using h
  · have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hder
    simpa only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.I_re] using h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_InverseChartCoarea
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact weighted coarea inside a single regular level chart. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal Topology ContDiff Classical
noncomputable section
namespace CircleDomainRigidity

lemma measurable_inverseChartWeight (e : OpenPartialHomeomorph ℂ ℂ)
    (heI : ContDiffOn ℝ 1 e.symm e.target) {T : Set ℂ} (hT : MeasurableSet T)
    (hTe : T ⊆ e.target) {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    Measurable (inverseChartWeight e T q) := by
  let E : ℂ → ℂ := T.piecewise e.symm (fun _ => 0)
  let R : ℂ → ℂ := T.piecewise (fun y => fderiv ℝ e.symm y Complex.I) (fun _ => 0)
  have hE : Measurable E := (heI.continuousOn.mono hTe).measurable_piecewise continuousOn_const hT
  have hR : Measurable R :=
    (((heI.continuousOn_fderiv_of_isOpen e.open_target (by norm_num)).clm_apply continuousOn_const).mono hTe).measurable_piecewise
      continuousOn_const hT
  have h := ((hq.comp hE).mul hR.norm.ennreal_ofReal).indicator hT
  have heq : inverseChartWeight e T q =
      T.indicator (fun y => q (E y) * ENNReal.ofReal ‖R y‖) := by
    funext y
    by_cases hy : y ∈ T <;> simp [inverseChartWeight, E, R, hy]
  rw [heq]
  exact h

lemma inverse_chart_fiber_eq
    {f : ℂ → ℝ} (e : OpenPartialHomeomorph ℂ ℂ) (he : ∀ z, (e z).re = f z)
    (heI : ContDiffOn ℝ 1 e.symm e.target) {T : Set ℂ} (hT : MeasurableSet T)
    (hb : IsBounded T) (hTe : T ⊆ e.target) {q : ℂ → ℝ≥0∞} (hq : Measurable q) (t : ℝ) :
    weightedScalarLevelLength (e.symm '' T) f q t =
      ∫⁻ s, inverseChartWeight e T q (coareaVerticalLine t s) := by
  have hset : (e.symm '' T) ∩ {z | f z = t} =
      (e.symm ∘ coareaVerticalLine t) '' ((coareaVerticalLine t) ⁻¹' T) := by
    ext z
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hfy⟩
      have hyr : y.re = t := by
        change f (e.symm y) = t at hfy
        rwa [← he, e.right_inv (hTe hy)] at hfy
      have heqy : coareaVerticalLine t y.im = y := by
        apply Complex.ext <;> simp [hyr]
      exact ⟨y.im, by rwa [mem_preimage, heqy], by simp only [comp_apply, heqy]⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨coareaVerticalLine t s, hs, rfl⟩, ?_⟩
      change f (e.symm (coareaVerticalLine t s)) = t
      rw [← he, e.right_inv (hTe hs), coareaVerticalLine_re]
  rw [weightedScalarLevelLength, hset, weighted_vertical_inverse_curve e heI hT hb hTe t hq]
  rw [← lintegral_indicator (hT.preimage (coareaVerticalLine_contDiff t).continuous.measurable)]
  apply lintegral_congr
  intro s
  by_cases hs : coareaVerticalLine t s ∈ T <;> simp [inverseChartWeight, hs]

lemma inverse_chart_energy_eq
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (e : OpenPartialHomeomorph ℂ ℂ) (heD : e.source ⊆ D)
    (he : ∀ z, (e z).re = f z) (heI : ContDiffOn ℝ 1 e.symm e.target)
    {T : Set ℂ} (hT : MeasurableSet T) (hTe : T ⊆ e.target) (q : ℂ → ℝ≥0∞) :
    (∫⁻ z in e.symm '' T, q z * ENNReal.ofReal ‖fderiv ℝ f z‖) =
      ∫⁻ y, inverseChartWeight e T q y := by
  have hd : ∀ y ∈ T, HasFDerivWithinAt e.symm (fderiv ℝ e.symm y) T y := fun y hy =>
    ((heI.contDiffAt (e.open_target.mem_nhds (hTe hy))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT hd (e.symm.injOn.mono hTe),
    inverseChartWeight, lintegral_indicator hT]
  apply setLIntegral_congr_fun hT
  intro y hy
  dsimp only
  have hj := level_chart_inverse_jacobian hD hf e heD he heI (hTe hy)
  calc
    ENNReal.ofReal |(fderiv ℝ e.symm y).det| *
        (q (e.symm y) * ENNReal.ofReal ‖fderiv ℝ f (e.symm y)‖) =
        q (e.symm y) * ENNReal.ofReal (‖fderiv ℝ f (e.symm y)‖ * |(fderiv ℝ e.symm y).det|) := by
      rw [ENNReal.ofReal_mul (norm_nonneg _)]
      ac_rfl
    _ = _ := by rw [hj]

lemma inverse_chart_weighted_coarea
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (e : OpenPartialHomeomorph ℂ ℂ) (heD : e.source ⊆ D)
    (he : ∀ z, (e z).re = f z) (heI : ContDiffOn ℝ 1 e.symm e.target)
    {T : Set ℂ} (hT : MeasurableSet T) (hb : IsBounded T) (hTe : T ⊆ e.target)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    WeightedScalarCoareaIdentity (e.symm '' T) f q := by
  let W := inverseChartWeight e T q
  have hW : Measurable W := measurable_inverseChartWeight e heI hT hTe hq
  let H : ℝ × ℝ → ℝ≥0∞ := fun p => W (Complex.measurableEquivRealProd.symm p)
  have hH : Measurable H := hW.comp Complex.measurableEquivRealProd.symm.measurable
  have hline (t s : ℝ) : coareaVerticalLine t s = Complex.measurableEquivRealProd.symm (t, s) := by
    apply Complex.ext <;> simp
  have hfun : weightedScalarLevelLength (e.symm '' T) f q = fun t => ∫⁻ s, H (t, s) := by
    funext t
    rw [inverse_chart_fiber_eq e he heI hT hb hTe hq]
    simp only [H, W, hline]
  refine ⟨by rw [hfun]; exact hH.lintegral_prod_right'.aemeasurable, ?_⟩
  rw [hfun, ← lintegral_prod H hH.aemeasurable, ← Measure.volume_eq_prod]
  have hm := (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).lintegral_comp hW
  exact hm.trans (inverse_chart_energy_eq hD hf e heD he heI hT hTe q).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RegularCoareaNeighborhood
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Each regular point has a neighborhood on all of whose Borel subsets
weighted coarea holds. Bounding the image keeps the line parameters bounded. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal Topology ContDiff Classical
noncomputable section
namespace CircleDomainRigidity

lemma isOpen_planar_regular {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    IsOpen (D ∩ {z | fderiv ℝ f z ≠ 0}) :=
  (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).isOpen_inter_preimage
    hD isClosed_singleton.isOpen_compl

lemma exists_regular_coarea_neighborhood {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) {x : ℂ} (hx : x ∈ D)
    (hr : fderiv ℝ f x ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ U ⊆ D ∩ {z | fderiv ℝ f z ≠ 0} ∧
      ∀ S : Set ℂ, MeasurableSet S → S ⊆ U →
        ∀ q : ℂ → ℝ≥0∞, Measurable q → WeightedScalarCoareaIdentity S f q := by
  obtain ⟨e, hxe, heD, he, heC, heI⟩ := exists_complex_c1_level_chart hD hf hx hr
  let U := (e.source ∩ e ⁻¹' ball (e x) 1) ∩ (D ∩ {z | fderiv ℝ f z ≠ 0})
  have hU : IsOpen U :=
    (e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball).inter (isOpen_planar_regular hD hf)
  refine ⟨U, hU, ⟨⟨hxe, mem_ball_self (by norm_num)⟩, hx, hr⟩, inter_subset_right, ?_⟩
  intro S hS hSU q hq
  have hSe : S ⊆ e.source := fun z hz => (hSU hz).1.1
  have hT : MeasurableSet (e '' S) :=
    hS.image_of_continuousOn_injOn (heC.continuousOn.mono hSe) (e.injOn.mono hSe)
  have hb : IsBounded (e '' S) := isBounded_ball.subset (by
    rintro y ⟨z, hz, rfl⟩
    exact (hSU hz).1.2)
  have hTe : e '' S ⊆ e.target := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_source (hSe hz)
  have h := inverse_chart_weighted_coarea hD hf e heD he heI hT hb hTe hq
  have heq : e.symm '' (e '' S) = S := by
    exact e.toPartialEquiv.symm_image_image_of_subset_source hSe
  rwa [heq] at h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_RegularCoareaProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted coarea on the noncritical part of a C1 planar domain. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma regular_weighted_coarea {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) :
    WeightedScalarCoareaIdentity (D ∩ {z | fderiv ℝ f z ≠ 0}) f q := by
  let R := D ∩ {z | fderiv ℝ f z ≠ 0}
  rcases R.eq_empty_or_nonempty with hempty | hne
  · change WeightedScalarCoareaIdentity R f q
    rw [hempty]
    constructor
    · have he : weightedScalarLevelLength ∅ f q = fun _ : ℝ => 0 := by
        funext t
        simp [weightedScalarLevelLength]
      rw [he]
      exact measurable_const.aemeasurable
    · simp [weightedScalarLevelLength]
  let : Nonempty R := hne.to_subtype
  choose U hU hxU hUR hco using fun x : R =>
    exists_regular_coarea_neighborhood hD hf x.property.1 x.property.2
  have hcover : R ⊆ ⋃ x : R, U x := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hlin : IsLindelof R := isLindelof_iff_lindelofSpace.mpr inferInstance
  obtain ⟨v, hv⟩ := hlin.indexed_countable_subcover U hU hcover
  let A : ℕ → Set ℂ := disjointed (fun n => U (v n))
  have hAU : ∀ n, A n ⊆ U (v n) := fun n => disjointed_subset _ n
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.disjointed (fun j => (hU (v j)).measurableSet) n
  have hAD : ∀ n, A n ⊆ D := fun n => (hAU n).trans ((hUR (v n)).trans inter_subset_left)
  have hlocal : ∀ n, WeightedScalarCoareaIdentity (A n) f q := fun n =>
    hco (v n) (A n) (hA n) (hAU n) q hq
  have heq : (⋃ n, A n) = R := by
    rw [show A = disjointed (fun n => U (v n)) by rfl, iUnion_disjointed]
    exact (iUnion_subset (fun n => hUR (v n))).antisymm hv
  have h := weighted_coarea_iUnion hD hf.continuousOn A hA (disjoint_disjointed _) hAD q hlocal
  rwa [heq] at h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_WeightedPlanarCoareaProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The planar nonnegative weighted C1 coarea formula. The critical set
is treated by diameter covers, and the regular set by actual inverse
charts, curve arclength, Fubini and change of variables. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

/-- Federer's nonnegative weighted scalar planar coarea identity. -/
theorem weightedPlanarScalarCoarea : WeightedPlanarScalarCoarea := by
  intro D hD f hf q hq
  let R := D ∩ {z | fderiv ℝ f z ≠ 0}
  let C := D ∩ {z | fderiv ℝ f z = 0}
  have hR : WeightedScalarCoareaIdentity R f q := regular_weighted_coarea hD hf hq
  have hCm : MeasurableSet C := measurableSet_planar_critical hD hf
  have hCD : C ⊆ D := inter_subset_left
  have hRC : Disjoint R C := by
    apply disjoint_left.mpr
    intro z hzR hzC
    exact hzR.2 hzC.2
  have hDC : D = R ∪ C := by
    ext z
    simp only [R, C, mem_union, mem_inter_iff, mem_ofPred_eq]
    tauto
  have hCzero : ∀ᵐ t, weightedScalarLevelLength C f q t = 0 :=
    ae_zero_weighted_planar_critical_fiber hD hf q
  have hsplit (t : ℝ) : weightedScalarLevelLength D f q t =
      weightedScalarLevelLength R f q t + weightedScalarLevelLength C f q t := by
    unfold weightedScalarLevelLength
    rw [hDC, union_inter_distrib_right]
    exact lintegral_union (measurableSet_restricted_scalar_level hD hf.continuousOn hCm hCD t)
      (hRC.mono inter_subset_left inter_subset_left)
  have heq : weightedScalarLevelLength D f q =ᵐ[volume] weightedScalarLevelLength R f q := by
    filter_upwards [hCzero] with t ht
    rw [hsplit t, ht, add_zero]
  have hCE : (∫⁻ z in C, q z * ENNReal.ofReal ‖fderiv ℝ f z‖) = 0 := by
    apply setLIntegral_eq_zero hCm
    intro z hz
    change q z * ENNReal.ofReal ‖fderiv ℝ f z‖ = 0
    have hz0 : fderiv ℝ f z = 0 := hz.2
    rw [hz0, norm_zero, ENNReal.ofReal_zero, mul_zero]
  refine ⟨hR.1.congr heq.symm, ?_⟩
  calc
    (∫⁻ t, weightedScalarLevelLength D f q t) = ∫⁻ t, weightedScalarLevelLength R f q t :=
      lintegral_congr_ae heq
    _ = ∫⁻ z in R, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ := hR.2
    _ = ∫⁻ z in D, q z * ENNReal.ofReal ‖fderiv ℝ f z‖ := by
      conv_rhs => rw [hDC, lintegral_union hCm hRC, hCE, add_zero]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_BoundaryArcComplement
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unused part of the unit circle after closing a crosscut is one
connected open arc, with its exact angular parameter interval. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma boundaryClosingArc_complement_image {a : ℂ} (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    (fun s : ℝ => standardCirclePoint (s : UnitAddCircle)) ''
        Ioo (unitCircleCut (normalizedArgument a)) 1 =
      Metric.sphere (0 : ℂ) 1 \ range (boundaryClosingArc a ha) := by
  let α := unitCircleCut (normalizedArgument a)
  have hα : 0 < α := boundary_angle_pos ha ha1
  have hα1 : α < 1 := (unitCircleCut_mem _).2
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨mem_sphere_zero_iff_norm.mpr (Circle.norm_coe _), ?_⟩
    rintro ⟨t, ht⟩
    have he := standardCirclePoint_injective ht
    change ((α*(t : ℝ) : ℝ) : UnitAddCircle) = (s : UnitAddCircle) at he
    have ht' : α * (t : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := by
      simpa only [zero_add] using boundary_arc_parameter_mem ha ha1 t
    have hs' : s ∈ Ico (0 : ℝ) (0 + 1) := by
      exact ⟨(hα.trans hs.1).le, by simpa using hs.2⟩
    have he' := (AddCircle.coe_eq_coe_iff_of_mem_Ico ht' hs').mp he
    have htle : α*(t : ℝ) ≤ α := mul_le_of_le_one_right hα.le t.property.2
    exact (not_lt_of_ge (he' ▸ htle)) hs.1
  · rintro ⟨hz, hznot⟩
    let s := unitCircleCut (normalizedArgument z)
    have hs : s ∈ Ico (0 : ℝ) 1 := unitCircleCut_mem _
    have he : standardCirclePoint (s : UnitAddCircle) = z := by
      rw [show (s : UnitAddCircle) = normalizedArgument z from AddCircle.coe_equivIco]
      exact standardCirclePoint_normalizedArgument (mem_sphere_zero_iff_norm.mp hz)
    have hsα : α < s := by
      by_contra! hh
      let t : PathTime := ⟨s/α, ⟨div_nonneg hs.1 hα.le, (div_le_one hα).mpr hh⟩⟩
      apply hznot
      refine ⟨t, ?_⟩
      change standardCirclePoint ((α*(s/α) : ℝ) : UnitAddCircle) = z
      rw [mul_div_cancel₀ s hα.ne']
      exact he
    exact ⟨s, ⟨hsα,hs.2⟩,he⟩

lemma isConnected_boundaryClosingArc_complement {a : ℂ} (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    IsConnected (Metric.sphere (0 : ℂ) 1 \ range (boundaryClosingArc a ha)) := by
  rw [← boundaryClosingArc_complement_image ha ha1]
  apply (isConnected_Ioo ((unitCircleCut_mem (normalizedArgument a)).2)).image
  exact ((continuous_subtype_val.comp
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous).comp
      (AddCircle.continuous_mk' (1 : ℝ))).continuousOn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskComponentBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Components of an open planar set cut by a disk are relatively closed,
and a component approaching an available circle point occupies its whole
small inner neighborhood. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma closure_component_inter_subset {V : Set ℂ} {x : ℂ} (hx : x ∈ V) :
    closure (connectedComponentIn V x) ∩ V ⊆ connectedComponentIn V x := by
  have hc : IsPreconnected (closure (connectedComponentIn V x) ∩ V) :=
    isPreconnected_connectedComponentIn.subset_closure
      (fun z hz => ⟨subset_closure hz, connectedComponentIn_subset V x hz⟩) inter_subset_left
  exact hc.subset_connectedComponentIn ⟨subset_closure (mem_connectedComponentIn hx), hx⟩
    inter_subset_right

lemma disk_component_boundary_neighborhood {E : Set ℂ} (hE : IsOpen E)
    {x z : ℂ} (hzE : z ∈ E)
    (hz : z ∈ closure (connectedComponentIn (E ∩ ball 0 1) x)) :
    ∃ r > 0, ball z r ∩ ball 0 1 ⊆ connectedComponentIn (E ∩ ball 0 1) x ∧
      ball z r ∩ sphere 0 1 ⊆ closure (connectedComponentIn (E ∩ ball 0 1) x) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hE z hzE
  have hS : IsPreconnected (ball z r ∩ ball (0 : ℂ) 1) :=
    ((convex_ball z r).inter (convex_ball 0 1)).isPreconnected
  obtain ⟨a, ha, haC⟩ := mem_closure_iff.1 hz (ball z r) isOpen_ball (mem_ball_self hr)
  have haV := connectedComponentIn_subset (E ∩ ball 0 1) x haC
  have hsub : ball z r ∩ ball 0 1 ⊆ E ∩ ball 0 1 := fun _ hy => ⟨hball hy.1, hy.2⟩
  have hSsub : ball z r ∩ ball 0 1 ⊆ connectedComponentIn (E ∩ ball 0 1) x := by
    have hh := hS.subset_connectedComponentIn ⟨ha, haV.2⟩ hsub
    rwa [← connectedComponentIn_eq haC] at hh
  refine ⟨r, hr, hSsub, ?_⟩
  intro y hy
  apply closure_mono hSsub
  apply isOpen_ball.inter_closure
  rw [closure_ball _ one_ne_zero]
  exact ⟨hy.1, sphere_subset_closedBall hy.2⟩

lemma disk_component_touches_available_circle {E : Set ℂ} (hE : IsOpen E)
    (hEc : IsPreconnected E) (hC : (E ∩ sphere (0 : ℂ) 1).Nonempty)
    {x : ℂ} (hx : x ∈ E ∩ ball 0 1) :
    (closure (connectedComponentIn (E ∩ ball 0 1) x) ∩ (E ∩ sphere 0 1)).Nonempty := by
  let V := E ∩ ball (0 : ℂ) 1
  let A := connectedComponentIn V x
  have hxA : x ∈ A := mem_connectedComponentIn hx
  have hAo : IsOpen A := (hE.inter isOpen_ball).connectedComponentIn
  have hAc : closure A ⊆ closedBall (0 : ℂ) 1 := by
    apply closure_minimal ((connectedComponentIn_subset V x).trans (inter_subset_right.trans ball_subset_closedBall)) isClosed_closedBall
  by_contra hempty
  have hclosed : closure A ∩ E ⊆ A := by
    intro y hy
    have hyn : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp (hAc hy.1)
    by_cases hylt : ‖y‖ < 1
    · exact closure_component_inter_subset hx ⟨hy.1, hy.2, mem_ball_zero_iff.mpr hylt⟩
    · exact (hempty ⟨y, hy.1, hy.2, mem_sphere_zero_iff_norm.mpr (le_antisymm hyn (not_lt.mp hylt))⟩).elim
  have hEA : E ⊆ A := hEc.subset_of_closure_inter_subset hAo ⟨x, hx.1, hxA⟩ hclosed
  obtain ⟨z, hzE, hzC⟩ := hC
  have hzV := connectedComponentIn_subset V x (hEA hzE)
  have hzlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hzV.2
  exact (ne_of_lt hzlt) (mem_sphere_zero_iff_norm.mp hzC)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedDiskIntersection
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A connected open plane set whose available unit-circle part is
connected has connected intersection with the open unit disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma disk_component_closure_contains_circle {E : Set ℂ} (hE : IsOpen E)
    (hEc : IsPreconnected E) (hC : IsPreconnected (E ∩ sphere (0 : ℂ) 1))
    (hCn : (E ∩ sphere (0 : ℂ) 1).Nonempty)
    {x : ℂ} (hx : x ∈ E ∩ ball 0 1) :
    E ∩ sphere 0 1 ⊆ closure (connectedComponentIn (E ∩ ball 0 1) x) := by
  let C := E ∩ sphere (0 : ℂ) 1
  let A := connectedComponentIn (E ∩ ball (0 : ℂ) 1) x
  let : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  let T : Set C := {z | z.val ∈ closure A}
  have hTc : IsClosed T := isClosed_closure.preimage continuous_subtype_val
  have hTo : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨r, hr, _, hclose⟩ := disk_component_boundary_neighborhood hE z.property.1 hz
    have hn : ∀ᶠ w : C in 𝓝 z, w.val ∈ ball z.val r :=
      continuous_subtype_val.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hn] with w hw
    exact hclose ⟨hw, w.property.2⟩
  have hTn : T.Nonempty := by
    obtain ⟨z, hzA, hzC⟩ := disk_component_touches_available_circle hE hEc hCn hx
    exact ⟨⟨z,hzC⟩,hzA⟩
  have hTu := (show IsClopen T from ⟨hTc,hTo⟩).eq_univ hTn
  intro z hz
  have hh : (⟨z,hz⟩ : C) ∈ T := hTu.symm ▸ mem_univ _
  exact hh

lemma isPreconnected_inter_disk_of_circle {E : Set ℂ} (hE : IsOpen E)
    (hEc : IsPreconnected E) (hC : IsPreconnected (E ∩ sphere (0 : ℂ) 1)) :
    IsPreconnected (E ∩ ball 0 1) := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  by_cases hCn : (E ∩ sphere (0 : ℂ) 1).Nonempty
  · let V := E ∩ ball (0 : ℂ) 1
    let A := connectedComponentIn V x
    have hCA := disk_component_closure_contains_circle hE hEc hC hCn hx
    have hCB := disk_component_closure_contains_circle hE hEc hC hCn hy
    obtain ⟨z, hz⟩ := hCn
    obtain ⟨r, hr, hsub, _⟩ := disk_component_boundary_neighborhood hE hz.1 (hCA hz)
    obtain ⟨b, hb, hbB⟩ := mem_closure_iff.1 (hCB hz) (ball z r) isOpen_ball (mem_ball_self hr)
    have hbV := connectedComponentIn_subset V y hbB
    have hbA : b ∈ A := hsub ⟨hb,hbV.2⟩
    have heq : connectedComponentIn V y = A :=
      (connectedComponentIn_eq hbB).trans (connectedComponentIn_eq hbA).symm
    refine ⟨A, connectedComponentIn_subset V x, mem_connectedComponentIn hx, ?_,
      isPreconnected_connectedComponentIn⟩
    rw [← heq]
    exact mem_connectedComponentIn hy
  · have hball : E ⊆ ball (0 : ℂ) 1 := by
      apply hEc.subset_of_closure_inter_subset isOpen_ball ⟨x,hx.1,hx.2⟩
      intro z hz
      rw [closure_ball _ one_ne_zero] at hz
      have hzn : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz.1
      have hne : ‖z‖ ≠ 1 := fun he => hCn ⟨z,hz.2,mem_sphere_zero_iff_norm.mpr he⟩
      exact mem_ball_zero_iff.mpr (lt_of_le_of_ne hzn hne)
    exact ⟨E, fun z hz => ⟨hz,hball hz⟩, hx.1, hy.1,hEc⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskCrosscutJordan
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two actual Jordan sides of a disk crosscut closed by one circle arc. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma disk_crosscut_norm_le {a : ℂ} (p : Path a 1) (ha : ‖a‖ = 1)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) (t : PathTime) : ‖p t‖ ≤ 1 := by
  by_cases ht0 : t = 0
  · simp only [ht0, p.source, ha, le_refl]
  by_cases ht1 : t = 1
  · simp only [ht1, p.target, norm_one, le_refl]
  exact (hp t ⟨lt_of_le_of_ne bot_le (Ne.symm ht0), lt_of_le_of_ne le_top ht1⟩).le

lemma disk_crosscut_circle_subset {a : ℂ} (p : Path a 1) (ha : ‖a‖ = 1)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) :
    range p ∩ sphere (0 : ℂ) 1 ⊆ range (boundaryClosingArc a ha) := by
  rintro z ⟨⟨t,rfl⟩,hz⟩
  by_cases ht0 : t = 0
  · exact ⟨1, by simp only [ht0, p.source, (boundaryClosingArc a ha).target]⟩
  by_cases ht1 : t = 1
  · exact ⟨0, by simp only [ht1, p.target, (boundaryClosingArc a ha).source]⟩
  have hh := hp t ⟨lt_of_le_of_ne bot_le (Ne.symm ht0), lt_of_le_of_ne le_top ht1⟩
  exact (ne_of_lt hh (mem_sphere_zero_iff_norm.mp hz)).elim

lemma exists_disk_crosscut_jordan (hsch : PlanarSchoenflies)
    {a : ℂ} (p : Path a 1) (hi : Injective p)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    ∃ H : ℂ ≃ₜ ℂ,
      frontier (jordanInterior H) = range p ∪ range (boundaryClosingArc a ha) ∧
      closure (jordanInterior H) ⊆ closedBall (0 : ℂ) 1 ∧
      jordanInterior H ⊆ ball (0 : ℂ) 1 := by
  obtain ⟨H,hH⟩ := exists_schoenflies_of_disk_crosscut hsch p hi hp ha ha1
  have hf : frontier (jordanInterior H) = range p ∪ range (boundaryClosingArc a ha) := by
    rw [frontier_jordanInterior_eq_circle_range H _ hH]
    have hr : range (fun z : Circle => circleOfClosedPath (p.trans (boundaryClosingArc a ha))
        ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z)) =
        range (circleOfClosedPath (p.trans (boundaryClosingArc a ha))) := by
      ext z
      constructor
      · rintro ⟨w,rfl⟩; exact mem_range_self _
      · rintro ⟨w,rfl⟩
        exact ⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) w, by simp⟩
    rw [hr,circleOfClosedPath_range]
    exact Path.trans_range _ _
  have hc : closure (jordanInterior H) ⊆ closedBall (0 : ℂ) 1 := by
    apply jordan_fill_subset_closed_unitDisk
    intro z hz
    rw [hf] at hz
    rcases hz with ⟨t,rfl⟩ | ⟨t,rfl⟩
    · exact disk_crosscut_norm_le p ha hp t
    · exact (boundaryClosingArc_norm _ _ t).le
  refine ⟨H,hf,hc,?_⟩
  have hh := interior_mono hc
  rwa [interior_closure_jordanInterior, interior_closedBall _ one_ne_zero] at hh

lemma disk_crosscut_exterior_circle {a : ℂ} (p : Path a 1) (ha : ‖a‖ = 1)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1)
    (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range p ∪ range (boundaryClosingArc a ha))
    (hinside : jordanInterior H ⊆ ball (0 : ℂ) 1) :
    (closure (jordanInterior H))ᶜ ∩ sphere (0 : ℂ) 1 =
      sphere (0 : ℂ) 1 \ range (boundaryClosingArc a ha) := by
  ext z
  constructor
  · rintro ⟨hz,hzs⟩
    exact ⟨hzs,fun h => hz (frontier_subset_closure (hf ▸ Or.inr h))⟩
  · rintro ⟨hzs,hza⟩
    refine ⟨?_,hzs⟩
    rw [closure_eq_self_union_frontier,hf]
    rintro (hzJ | hzp | hza')
    · have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp (hinside hzJ)
      exact ne_of_lt hn (mem_sphere_zero_iff_norm.mp hzs)
    · exact hza (disk_crosscut_circle_subset p ha hp ⟨hzp,hzs⟩)
    · exact hza hza'

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskCrosscutSides
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact open sides and relative frontiers for a disk crosscut ending at one. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma disk_crosscut_sides_at_one (hsch : PlanarSchoenflies)
    {a : ℂ} (p : Path a 1) (hi : Injective p)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = ball 0 1 \ range p ∧
      frontier U ∩ ball 0 1 = range p ∩ ball 0 1 ∧
      frontier V ∩ ball 0 1 = range p ∩ ball 0 1 := by
  obtain ⟨H,hf,_,hinside⟩ := exists_disk_crosscut_jordan hsch p hi hp ha ha1
  let E := (closure (jordanInterior H))ᶜ
  have hE : IsOpen E := isClosed_closure.isOpen_compl
  have hec : E ∩ sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 \ range (boundaryClosingArc a ha) :=
    disk_crosscut_exterior_circle p ha hp H hf hinside
  have hC : IsConnected (E ∩ sphere (0 : ℂ) 1) := by
    rw [hec]
    exact isConnected_boundaryClosingArc_complement ha ha1
  have hV : IsConnected (E ∩ ball (0 : ℂ) 1) := by
    refine ⟨?_, isPreconnected_inter_disk_of_circle hE
      (isConnected_exterior_jordanInterior H).isPreconnected hC.isPreconnected⟩
    obtain ⟨z,hzE,hzs⟩ := hC.nonempty
    apply closure_nonempty_iff.mp
    refine ⟨z, hE.inter_closure ?_⟩
    rw [closure_ball _ one_ne_zero]
    exact ⟨hzE,sphere_subset_closedBall hzs⟩
  have harc : Disjoint (range (boundaryClosingArc a ha)) (ball (0 : ℂ) 1) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t,rfl⟩ hz
    have hn := mem_ball_zero_iff.mp hz
    rw [boundaryClosingArc_norm] at hn
    exact lt_irrefl _ hn
  have hfront : frontier (jordanInterior H) ∩ ball (0 : ℂ) 1 = range p ∩ ball 0 1 := by
    rw [hf,union_inter_distrib_right,harc.inter_eq,union_empty]
  have hEf : frontier E = frontier (jordanInterior H) := by
    change frontier (closure (jordanInterior H))ᶜ = _
    rw [frontier_compl,frontier,closure_closure,interior_closure_jordanInterior,
      frontier,(jordanInterior_isOpen H).interior_eq]
  refine ⟨jordanInterior H,E ∩ ball 0 1,jordanInterior_isOpen H,hE.inter isOpen_ball,
    isConnected_jordanInterior H,hV,?_,?_,hfront,?_⟩
  · exact Set.disjoint_left.mpr (fun z hz hzE => hzE.1 (subset_closure hz))
  · ext z
    constructor
    · rintro (hz | ⟨hzE,hzb⟩)
      · refine ⟨hinside hz,?_⟩
        intro hzp
        have hzfront : z ∈ frontier (jordanInterior H) := hf ▸ Or.inl hzp
        rw [frontier,(jordanInterior_isOpen H).interior_eq] at hzfront
        exact hzfront.2 hz
      · refine ⟨hzb,fun hzp => hzE (frontier_subset_closure (hf ▸ Or.inl hzp))⟩
    · rintro ⟨hzb,hzp⟩
      by_cases hzJ : z ∈ jordanInterior H
      · exact Or.inl hzJ
      · right
        refine ⟨?_,hzb⟩
        change z ∉ closure (jordanInterior H)
        rw [closure_eq_self_union_frontier]
        rintro (hz | hz)
        · exact hzJ hz
        · have h := hfront ▸ (show z ∈ frontier (jordanInterior H) ∩ ball 0 1 from ⟨hz,hzb⟩)
          exact hzp h.1
  · rw [frontier_inter_open_inter isOpen_ball,hEf,hfront]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CrosscutSeparationProof
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disk crosscut separation derived from the retained planar Schoenflies input. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem unitDiskCrosscutSeparation (hsch : PlanarSchoenflies) :
    UnitDiskCrosscutSeparation := by
  intro p hi ha hb hp
  have hb0 : p 1 ≠ 0 := by
    intro h
    rw [h,norm_zero] at hb
    exact zero_ne_one hb
  let R := Homeomorph.mulLeft₀ (p 1) hb0
  let q : Path ((p 1)⁻¹ * p 0) 1 := {
    toFun := fun t => (p 1)⁻¹ * p t
    continuous_toFun := continuous_const.mul p.continuous
    source' := rfl
    target' := inv_mul_cancel₀ hb0 }
  have hqp (t : PathTime) : R (q t) = p t := by
    change p 1 * ((p 1)⁻¹ * p t) = p t
    rw [← mul_assoc,mul_inv_cancel₀ hb0,one_mul]
  have hqnorm (t : PathTime) : ‖q t‖ = ‖p t‖ := by
    change ‖(p 1)⁻¹ * p t‖ = ‖p t‖
    rw [norm_mul,norm_inv,hb,inv_one,one_mul]
  have hqa : ‖(p 1)⁻¹ * p 0‖ = 1 := (hqnorm 0).trans ha
  have hqa1 : (p 1)⁻¹ * p 0 ≠ 1 := by
    intro h
    have he : p 0 = p 1 := by
      rw [← hqp 0]
      change p 1 * ((p 1)⁻¹ * p 0) = p 1
      rw [h,mul_one]
    have hh : (0 : PathTime) = 1 := hi he
    exact zero_ne_one (congrArg (fun t : PathTime => (t : ℝ)) hh)
  have hqi : Injective q := fun s t he => hi (by rw [← hqp s,← hqp t,he])
  have hqpint : ∀ t ∈ Ioo (0 : PathTime) 1, ‖q t‖ < 1 := by
    intro t ht
    rw [hqnorm]
    exact hp t ht
  obtain ⟨U,V,hU,hV,hUc,hVc,hd,hu,hfu,hfv⟩ :=
    disk_crosscut_sides_at_one hsch q hqi hqpint hqa hqa1
  have hRnorm (z : ℂ) : ‖R z‖ = ‖z‖ := by
    change ‖p 1 * z‖ = ‖z‖
    rw [norm_mul,hb,one_mul]
  have hRb : R '' ball (0 : ℂ) 1 = ball (0 : ℂ) 1 := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      simpa only [mem_ball_zero_iff,hRnorm] using hw
    · intro hz
      refine ⟨R.symm z,?_,R.apply_symm_apply z⟩
      rw [mem_ball_zero_iff,← hRnorm, R.apply_symm_apply]
      exact mem_ball_zero_iff.mp hz
  have hRrange : R '' range q = range p := by
    rw [← range_comp]
    exact congrArg range (funext hqp)
  refine ⟨R '' U,R '' V,R.isOpenMap U hU,R.isOpenMap V hV,
    hUc.image R R.continuous.continuousOn,hVc.image R R.continuous.continuousOn,
    ?_,?_,?_,?_⟩
  · rw [disjoint_iff_inter_eq_empty,← image_inter R.injective,hd.inter_eq,image_empty]
  · rw [← image_union,hu,image_sdiff R.injective,hRb,hRrange]
  · rw [← R.image_frontier,← hRb,← image_inter R.injective,hfu,
      image_inter R.injective,hRrange,hRb]
  · rw [← R.image_frontier,← hRb,← image_inter R.injective,hfv,
      image_inter R.injective,hRrange,hRb]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_AlternatingBoundaryCoordinates
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
attribute [-simp] _root_.OAI.CircleDomainRigidity.HalfPlaneRay.compactify_top _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionData.node_cons _root_.OAI.CircleDomainRigidity.MarkedHit.HitFusionSplit.index_val _root_.OAI.CircleDomainRigidity.diskRayComplex_im _root_.OAI.CircleDomainRigidity.realIntervalPath_one _root_.OAI.CircleDomainRigidity.realIntervalPath_zero _root_.OAI.CircleDomainRigidity.reboundJumpBlock_cost _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_one _root_.OAI.CircleDomainRigidity.restrictTaggedPhysicalPath_zero _root_.OAI.CircleDomainRigidity.singlePieceBlock_cost _root_.OAI.CircleDomainRigidity.verticalCayleyPath_one _root_.OAI.CircleDomainRigidity.verticalCayleyPath_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact circle arcs for four points ordered by the fixed circle cut. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma standardCirclePoint_sub (θ φ : UnitAddCircle) :
    standardCirclePoint (θ-φ) = (standardCirclePoint φ)⁻¹ * standardCirclePoint θ := by
  simp only [standardCirclePoint,AddCircle.homeomorphCircle_apply,sub_eq_add_neg,
    AddCircle.toCircle_add,AddCircle.toCircle_neg,Circle.coe_mul,Circle.coe_inv]
  exact mul_comm _ _

lemma unitCircleCut_coe_of_mem {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    unitCircleCut (s : UnitAddCircle) = s := by
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0)
    (by simpa only [zero_add] using hs))

lemma alternating_boundary_rotated_arcs (θ : Fin 4 → UnitAddCircle)
    (hθ : StrictMono (unitCircleCut ∘ θ)) :
    let a := (standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ 2)
    let x := (standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ 1)
    let y := (standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ 3)
    ∃ ha : ‖a‖ = 1, a ≠ 1 ∧ x ∈ range (boundaryClosingArc a ha) ∧
      y ∈ Metric.sphere (0 : ℂ) 1 \ range (boundaryClosingArc a ha) := by
  let t : Fin 4 → ℝ := unitCircleCut ∘ θ
  have h01 : t 0 < t 1 := hθ (by decide)
  have h12 : t 1 < t 2 := hθ (by decide)
  have h23 : t 2 < t 3 := hθ (by decide)
  have h0 : 0 ≤ t 0 := (unitCircleCut_mem (θ 0)).1
  have h3 : t 3 < 1 := (unitCircleCut_mem (θ 3)).2
  have hd (i : Fin 4) : (((t i-t 0 : ℝ) : UnitAddCircle)) = θ i-θ 0 := by
    rw [AddCircle.coe_sub]
    exact congrArg₂ (·-·) AddCircle.coe_equivIco AddCircle.coe_equivIco
  have he (i : Fin 4) : (standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ i) =
      standardCirclePoint ((t i-t 0 : ℝ) : UnitAddCircle) := by
    rw [hd,standardCirclePoint_sub]
  have h2mem : t 2-t 0 ∈ Ico (0 : ℝ) 1 := ⟨by linarith,by linarith⟩
  have hcut : unitCircleCut (normalizedArgument
      ((standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ 2))) = t 2-t 0 := by
    rw [he,normalizedArgument_standardCirclePoint,unitCircleCut_coe_of_mem h2mem]
  have ha : ‖(standardCirclePoint (θ 0))⁻¹ * standardCirclePoint (θ 2)‖ = 1 := by
    rw [he]; exact Circle.norm_coe _
  refine ⟨ha,?_,?_,?_⟩
  · intro h
    have harg : normalizedArgument (1 : ℂ) = (0 : UnitAddCircle) := by
      rw [← standardCirclePoint_zero,normalizedArgument_standardCirclePoint]
    have hz := unitCircleCut_coe_of_mem (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
    rw [AddCircle.coe_zero] at hz
    rw [h,harg,hz] at hcut
    linarith
  · let u : PathTime := ⟨(t 1-t 0)/(t 2-t 0),⟨div_nonneg (by linarith) (by linarith),
      (div_le_one (by linarith)).mpr (by linarith)⟩⟩
    refine ⟨u,?_⟩
    change standardCirclePoint ((unitCircleCut (normalizedArgument _) * (u : ℝ) : ℝ) : UnitAddCircle) = _
    rw [hcut,he]
    congr 2
    exact mul_div_cancel₀ _ (by linarith)
  · rw [← boundaryClosingArc_complement_image ha (by
      intro h
      have harg : normalizedArgument (1 : ℂ) = (0 : UnitAddCircle) := by
        rw [← standardCirclePoint_zero,normalizedArgument_standardCirclePoint]
      have hz := unitCircleCut_coe_of_mem (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
      rw [AddCircle.coe_zero] at hz
      rw [h,harg,hz] at hcut
      linarith)]
    exact ⟨t 3-t 0,⟨by rw [hcut]; linarith,by linarith⟩,(he 3).symm⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DyadicPathApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
attribute [-simp] _root_.OAI.CircleDomainRigidity.leftHalf_one _root_.OAI.CircleDomainRigidity.leftHalf_zero _root_.OAI.CircleDomainRigidity.rightHalf_one _root_.OAI.CircleDomainRigidity.rightHalf_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic subdivision with quantitative oscillation and pointwise error
preservation when two replacement paths are concatenated. -/
open Set Function Filter Metric unitInterval
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma dist_leftHalf (s t : I) : dist (leftHalf s) (leftHalf t) = (1 / 2 : ℝ) * dist s t := by
  change |(s : ℝ) / 2 - (t : ℝ) / 2| = (1 / 2 : ℝ) * |(s : ℝ) - (t : ℝ)|
  rw [← sub_div, abs_div]
  norm_num
  ring

lemma dist_rightHalf (s t : I) : dist (rightHalf s) (rightHalf t) = (1 / 2 : ℝ) * dist s t := by
  change |((s : ℝ) + 1) / 2 - ((t : ℝ) + 1) / 2| = (1 / 2 : ℝ) * |(s : ℝ) - (t : ℝ)|
  rw [show ((s : ℝ) + 1) / 2 - ((t : ℝ) + 1) / 2 = ((s : ℝ) - t) / 2 by ring, abs_div]
  norm_num
  ring

lemma dyadicSmallOscillation_of_modulus {E : Type*} [PseudoMetricSpace E]
    (n : ℕ) (f : I → E) (ε : ℝ)
    (hf : ∀ s t, dist s t ≤ (1 / 2 : ℝ)^n → dist (f s) (f t) < ε) :
    dyadicSmallOscillation n f ε := by
  induction n generalizing f with
  | zero =>
      intro s t
      apply hf
      simp only [pow_zero]
      change |(s : ℝ) - (t : ℝ)| ≤ 1
      exact abs_le.mpr ⟨by linarith [s.property.1, t.property.2], by linarith [s.property.2, t.property.1]⟩
  | succ n ih =>
      constructor
      · apply ih
        intro s t hst
        apply hf
        rw [dist_leftHalf, pow_succ']
        exact mul_le_mul_of_nonneg_left hst (by norm_num : (0 : ℝ) ≤ 1 / 2)
      · apply ih
        intro s t hst
        apply hf
        rw [dist_rightHalf, pow_succ']
        exact mul_le_mul_of_nonneg_left hst (by norm_num : (0 : ℝ) ≤ 1 / 2)

lemma exists_dyadicSmallOscillation {E : Type*} [PseudoMetricSpace E]
    {f : I → E} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, dyadicSmallOscillation n f ε := by
  have hu := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  have ht : Tendsto (fun n : ℕ => (1 / 2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  exact ⟨n, dyadicSmallOscillation_of_modulus n f ε (fun s t hst => hmod (hst.trans_lt hn))⟩

lemma path_trans_pointwise_error {E : Type*} [MetricSpace E] {a b c : E}
    (γ₀ : Path a b) (γ₁ : Path b c) (f : I → E) {ε : ℝ}
    (h₀ : ∀ t, dist (γ₀ t) (f (leftHalf t)) < ε)
    (h₁ : ∀ t, dist (γ₁ t) (f (rightHalf t)) < ε) :
    ∀ t, dist ((γ₀.trans γ₁) t) (f t) < ε := by
  intro t
  rw [Path.trans_apply]
  split_ifs with ht
  · let s : I := ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.property.1, ht⟩⟩
    have hs : leftHalf s = t := by apply Subtype.ext; dsimp [leftHalf, s] <;> ring
    simpa only [hs] using h₀ s
  · let s : I := ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.mp ht).le, t.property.2⟩⟩
    have hs : rightHalf s = t := by apply Subtype.ext; dsimp [rightHalf, s] <;> ring
    simpa only [hs] using h₁ s

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DyadicPathReplacement
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replace a finely subdivided map by a path whose endpoints lie in a
fixed set, preserving a uniform error and a prescribed neighborhood. -/
open Set Function Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma dyadic_path_replacement
    {E : Type*} [MetricSpace E] {K : Set E} {τ δ r η : ℝ}
    (hδ : 3 * τ ≤ δ)
    (hjoin : ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
      ∃ γ : Path x y, (∀ t, dist (γ t) x < r) ∧
        (∀ t, ∃ c ∈ K, dist (γ t) c < η))
    (n : ℕ) (f k : I → E) (hk : ∀ t, k t ∈ K)
    (hosc : dyadicSmallOscillation n f τ) (hnear : ∀ t, dist (f t) (k t) < τ) :
    ∃ γ : Path (k 0) (k 1), (∀ t, dist (γ t) (f t) < r + 2 * τ) ∧
      (∀ t, ∃ c ∈ K, dist (γ t) c < η) := by
  induction n generalizing f k with
  | zero =>
      have hxy : dist (k 0) (k 1) < δ := by
        have h0 := hnear 0
        have h1 := hnear 1
        have h01 := hosc 0 1
        have ht := dist_triangle (k 0) (f 0) (k 1)
        have ht' := dist_triangle (f 0) (f 1) (k 1)
        rw [dist_comm (k 0) (f 0)] at ht
        linarith
      obtain ⟨γ, hγ, hKγ⟩ := hjoin (k 0) (hk 0) (k 1) (hk 1) hxy
      refine ⟨γ, ?_, hKγ⟩
      intro t
      have h0 := hnear 0
      have hos := hosc 0 t
      have hgt := hγ t
      have ht := dist_triangle (γ t) (k 0) (f t)
      have ht' := dist_triangle (k 0) (f 0) (f t)
      rw [dist_comm (k 0) (f 0)] at ht'
      linarith
  | succ n ih =>
      have hleft := ih (f ∘ leftHalf) (k ∘ leftHalf) (fun t => hk (leftHalf t))
        hosc.1 (fun t => hnear (leftHalf t))
      have hright := ih (f ∘ rightHalf) (k ∘ rightHalf) (fun t => hk (rightHalf t))
        hosc.2 (fun t => hnear (rightHalf t))
      simp only [comp_apply, leftHalf_zero, leftHalf_one] at hleft
      simp only [comp_apply, rightHalf_zero, rightHalf_one] at hright
      obtain ⟨γ₀, he₀, hn₀⟩ := hleft
      obtain ⟨γ₁, he₁, hn₁⟩ := hright
      refine ⟨γ₀.trans γ₁, path_trans_pointwise_error γ₀ γ₁ f he₀ he₁, ?_⟩
      intro t
      have ht : (γ₀.trans γ₁) t ∈ range γ₀ ∪ range γ₁ := by
        rw [← Path.trans_range]
        exact mem_range_self t
      rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
      · rw [← hs]
        exact hn₀ s
      · rw [← hs]
        exact hn₁ s

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SmallConnectedMetricSets
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small connected sets and finite chains used to construct arcs in a
compact locally connected metric space. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_uniform_small_connected_sets
    (X : Type*) [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : X, dist x y < δ →
      ∃ V : Set X, IsConnected V ∧ x ∈ V ∧ y ∈ V ∧
        ∀ a ∈ V, ∀ b ∈ V, dist a b < ε := by
  choose U hUsub hUopen hxU hUconn using fun x : X =>
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
      (inferInstance : LocallyConnectedSpace X) x (ball x (ε / 2))
      (ball_mem_nhds x (by linarith))
  have hcover : (univ : Set X) ⊆ ⋃ x, U x := fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨δ, hδ, hcoverδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ hUopen hcover
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  obtain ⟨c, hc⟩ := hcoverδ x (mem_univ x)
  refine ⟨U c, hUconn c, hc (mem_ball_self hδ), hc ?_, ?_⟩
  · exact mem_ball.mpr (by simpa only [dist_comm] using hxy)
  · intro a ha b hb
    have ha' := mem_ball.mp (hUsub c ha)
    have hb' := mem_ball.mp (hUsub c hb)
    have ht := dist_triangle a c b
    rw [dist_comm c b] at ht
    linarith

lemma metric_connected_reflTransGen
    {X : Type*} [MetricSpace X] [PreconnectedSpace X] {ε : ℝ} (hε : 0 < ε) (x y : X) :
    Relation.ReflTransGen (fun a b : X => dist a b < ε) x y := by
  let S := {z : X | Relation.ReflTransGen (fun a b : X => dist a b < ε) x z}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply Filter.mem_of_superset (ball_mem_nhds z hε)
    intro w hw
    exact hz.tail (by simpa only [mem_ball, dist_comm] using hw)
  have hSc : IsOpen Sᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply Filter.mem_of_superset (ball_mem_nhds z hε)
    intro w hw hwS
    exact hz (hwS.tail (mem_ball.mp hw))
  have hclosed : IsClosed S := by simpa only [compl_compl] using hSc.isClosed_compl
  have hEq : S = univ := (show IsClopen S from ⟨hclosed, hS⟩).eq_univ
    ⟨x, Relation.ReflTransGen.refl⟩
  exact (Set.eq_univ_iff_forall.mp hEq) y

lemma connected_set_metric_chain
    {X : Type*} [MetricSpace X] {S : Set X} (hS : IsConnected S)
    {ε : ℝ} (hε : 0 < ε) (x y : S) :
    Relation.ReflTransGen (fun a b : S => dist (a : X) (b : X) < ε) x y := by
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
  exact metric_connected_reflTransGen hε x y

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ConnectedSetPolygonalApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite metric chains give actual ambient paths arbitrarily close to a
connected set. These are the paths to be refined in the compact arc argument. -/
open Set Function Metric
open scoped unitInterval Topology
noncomputable section
namespace CircleDomainRigidity

lemma metric_chain_path_near_set
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {ε : ℝ} (hε : 0 < ε) {x y : S}
    (h : Relation.ReflTransGen (fun a b : S => dist (a : E) (b : E) < ε) x y) :
    ∃ γ : Path (x : E) (y : E), ∀ t, ∃ c ∈ S, dist (γ t) c < ε := by
  induction h with
  | refl =>
      refine ⟨Path.refl (x : E), fun t => ⟨x, x.property, ?_⟩⟩
      simpa using hε
  | @tail b c hprev hbc ih =>
      obtain ⟨γ, hγ⟩ := ih
      refine ⟨γ.trans (Path.segment (b : E) (c : E)), ?_⟩
      intro t
      have ht : γ.trans (Path.segment (b : E) (c : E)) t ∈
          range γ ∪ range (Path.segment (b : E) (c : E)) := by
        rw [← Path.trans_range]
        exact mem_range_self t
      rcases ht with ⟨u, hu⟩ | ⟨u, hu⟩
      · rw [← hu]
        exact hγ u
      · refine ⟨b, b.property, ?_⟩
        rw [← hu, Path.segment_apply, dist_lineMap_left, Real.norm_eq_abs,
          abs_of_nonneg u.property.1]
        exact (mul_le_mul_of_nonneg_right u.property.2 dist_nonneg).trans_lt (by simpa using hbc)

lemma connected_set_path_near
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : IsConnected S) {ε : ℝ} (hε : 0 < ε) {x y : E}
    (hx : x ∈ S) (hy : y ∈ S) :
    ∃ γ : Path x y, ∀ t, ∃ c ∈ S, dist (γ t) c < ε := by
  exact metric_chain_path_near_set hε (connected_set_metric_chain hS hε ⟨x, hx⟩ ⟨y, hy⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LocalApproximatePaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform local ambient paths near a compact locally connected set.
Their distance to the set can be prescribed independently of their diameter. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma uniform_local_approximate_paths
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) [LocallyConnectedSpace K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
      ∀ η : ℝ, 0 < η → ∃ γ : Path x y,
        (∀ t, dist (γ t) x < ε) ∧ (∀ t, ∃ c ∈ K, dist (γ t) c < η) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_small_connected_sets K (show 0 < ε / 3 by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy η hη
  obtain ⟨V, hV, hxV, hyV, hdiam⟩ := hlocal ⟨x, hx⟩ ⟨y, hy⟩ hxy
  have hS : IsConnected (Subtype.val '' V) := hV.image _ continuous_subtype_val.continuousOn
  have hxS : x ∈ Subtype.val '' V := ⟨⟨x, hx⟩, hxV, rfl⟩
  have hyS : y ∈ Subtype.val '' V := ⟨⟨y, hy⟩, hyV, rfl⟩
  obtain ⟨γ, hγ⟩ := connected_set_path_near hS (lt_min hη (show 0 < ε / 3 by linarith)) hxS hyS
  refine ⟨γ, ?_, ?_⟩
  · intro t
    obtain ⟨c, ⟨a, ha, rfl⟩, htc⟩ := hγ t
    have hd := hdiam a ha ⟨x, hx⟩ hxV
    have he := lt_of_lt_of_le htc (min_le_right η (ε / 3))
    have ht := dist_triangle (γ t) (a : E) x
    change dist (a : E) x < ε / 3 at hd
    linarith
  · intro t
    obtain ⟨c, ⟨a, ha, rfl⟩, htc⟩ := hγ t
    exact ⟨a, a.property, htc.trans_le (min_le_left η (ε / 3))⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactPathApproximationStep
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A path close to a compact locally connected set can be replaced,
with fixed endpoints and small uniform error, by a path arbitrarily closer
to that set. This is the step iterated to obtain an actual path in the set. -/
open Set Function Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma path_near_set_selector {E : Type*} [MetricSpace E] {K : Set E}
    {x y : E} (γ : Path x y) (hx : x ∈ K) (hy : y ∈ K) {τ : ℝ} (hτ : 0 < τ)
    (hnear : ∀ t, ∃ c ∈ K, dist (γ t) c < τ) :
    ∃ k : I → E, (∀ t, k t ∈ K) ∧ k 0 = x ∧ k 1 = y ∧
      ∀ t, dist (γ t) (k t) < τ := by
  classical
  let k : I → E := fun t => if t = 0 then x else if t = 1 then y else (hnear t).choose
  refine ⟨k, ?_, by simp [k], by simp [k], ?_⟩
  · intro t
    by_cases h0 : t = 0
    · simp only [k, ite_eq_left h0]
      exact hx
    · by_cases h1 : t = 1
      · simp only [k, ite_eq_right h0, ite_eq_left h1]
        exact hy
      · simp only [k, ite_eq_right h0, ite_eq_right h1]
        exact (hnear t).choose_spec.1
  · intro t
    by_cases h0 : t = 0
    · subst t
      simpa [k] using hτ
    · by_cases h1 : t = 1
      · subst t
        simpa [k] using hτ
      · simp only [k, ite_eq_right h0, ite_eq_right h1]
        exact (hnear t).choose_spec.2

lemma compact_path_approximation_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsCompact K) [LocallyConnectedSpace K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ K, ∀ γ : Path x y,
      (∀ t, ∃ c ∈ K, dist (γ t) c < ρ) →
      ∀ η : ℝ, 0 < η → ∃ β : Path x y,
        (∀ t, dist (β t) (γ t) < ε) ∧ (∀ t, ∃ c ∈ K, dist (β t) c < η) := by
  obtain ⟨δ, hδ, hlocal⟩ := uniform_local_approximate_paths hK (show 0 < ε / 4 by linarith)
  let ρ := min (δ / 4) (ε / 4)
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρδ : 3 * ρ ≤ δ := by
    have h := min_le_left (δ / 4) (ε / 4)
    dsimp [ρ]
    linarith
  have hρε : ε / 4 + 2 * ρ < ε := by
    have h := min_le_right (δ / 4) (ε / 4)
    dsimp [ρ]
    linarith
  refine ⟨ρ, hρ, ?_⟩
  intro x hx y hy γ hnear η hη
  obtain ⟨k, hk, hk0, hk1, hγk⟩ := path_near_set_selector γ hx hy hρ hnear
  obtain ⟨n, hosc⟩ := exists_dyadicSmallOscillation γ.continuous hρ
  have hjoin : ∀ a ∈ K, ∀ b ∈ K, dist a b < δ →
      ∃ β : Path a b, (∀ t, dist (β t) a < ε / 4) ∧
        (∀ t, ∃ c ∈ K, dist (β t) c < η) := fun a ha b hb hab =>
    hlocal a ha b hb hab η hη
  have h := dyadic_path_replacement hρδ hjoin n γ k hk hosc hγk
  rw [hk0, hk1] at h
  obtain ⟨β, hβ, hβK⟩ := h
  exact ⟨β, fun t => (hβ t).trans hρε, hβK⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ClosedSetPathLimit
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform limits of successively improved ambient paths lie in the
closed target set, retaining the endpoints and all summable error bounds. -/
open Set Function Filter Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma closed_set_path_limit
    {E : Type*} [MetricSpace E] [CompleteSpace E] {K : Set E} (hK : IsClosed K)
    {x y : E} (γ : ℕ → Path x y) (d η : ℕ → ℝ) (hd : Summable d) (hd0 : ∀ n, 0 ≤ d n)
    (hstep : ∀ n t, dist (γ n t) (γ (n + 1) t) ≤ d n)
    (hη : Tendsto η atTop (𝓝 0)) (hnear : ∀ n t, ∃ c ∈ K, dist (γ n t) c < η n) :
    ∃ β : Path x y, (∀ t, β t ∈ K) ∧
      ∀ n t, dist (γ n t) (β t) ≤ ∑' j, d (n + j) := by
  let F : ℕ → C(I, E) := fun n => (γ n).toContinuousMap
  have hdist : ∀ n, dist (F n) (F (n + 1)) ≤ d n := fun n =>
    (ContinuousMap.dist_le (hd0 n)).mpr (hstep n)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable d hdist hd)
  have hpt : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (g t)) := fun t =>
    (continuous_eval_const t).continuousAt.tendsto.comp hg
  have h0 : g 0 = x := by
    have h : Tendsto (fun _ : ℕ => x) atTop (𝓝 (g 0)) := by simpa [F] using hpt 0
    exact tendsto_nhds_unique h tendsto_const_nhds
  have h1 : g 1 = y := by
    have h : Tendsto (fun _ : ℕ => y) atTop (𝓝 (g 1)) := by simpa [F] using hpt 1
    exact tendsto_nhds_unique h tendsto_const_nhds
  let β : Path x y := { toContinuousMap := g, source' := h0, target' := h1 }
  refine ⟨β, ?_, ?_⟩
  · intro t
    choose c hc hdistance using fun n => hnear n t
    have hct : Tendsto c atTop (𝓝 (g t)) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hFe := Metric.tendsto_nhds.mp (hpt t) (ε / 2) (by linarith)
      have hηe := hη.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
      filter_upwards [hFe, hηe] with n hn hηn
      have hd' := hdistance n
      have ht := dist_triangle (c n) (F n t) (g t)
      rw [dist_comm (c n) (F n t)] at ht
      change dist (γ n t) (g t) < ε / 2 at hn
      change dist (c n) (g t) ≤ dist (γ n t) (c n) + dist (γ n t) (g t) at ht
      linarith
    exact hK.mem_of_tendsto hct (Eventually.of_forall hc)
  · intro n t
    have ht := dist_le_tsum_of_dist_le_of_tendsto d hdist hd hg n
    exact (ContinuousMap.dist_apply_le_dist t).trans ht

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_IteratedPathApproximation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dependent iteration of the proved path replacement step. -/
open Set Function Filter Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma iterate_path_approximations
    {E : Type*} [MetricSpace E] [CompleteSpace E] {K : Set E} (hK : IsClosed K)
    {x y : E} (d ρ : ℕ → ℝ) (hd : Summable d) (hd0 : ∀ n, 0 ≤ d n)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (γ₀ : Path x y) (hγ₀ : ∀ t, ∃ c ∈ K, dist (γ₀ t) c < ρ 0)
    (hstep : ∀ n, ∀ γ : Path x y,
      (∀ t, ∃ c ∈ K, dist (γ t) c < ρ n) →
      ∃ β : Path x y, (∀ t, dist (γ t) (β t) ≤ d n) ∧
        (∀ t, ∃ c ∈ K, dist (β t) c < ρ (n + 1))) :
    ∃ β : Path x y, (∀ t, β t ∈ K) ∧ ∀ t, dist (γ₀ t) (β t) ≤ ∑' n, d n := by
  let Stage (n : ℕ) := {γ : Path x y // ∀ t, ∃ c ∈ K, dist (γ t) c < ρ n}
  have hnext (n : ℕ) (p : Stage n) :
      ∃ q : Stage (n + 1), ∀ t, dist (p.val t) (q.val t) ≤ d n := by
    obtain ⟨β, he, hn⟩ := hstep n p.val p.property
    exact ⟨⟨β, hn⟩, he⟩
  let P : (n : ℕ) → Stage n := fun n => Nat.rec ⟨γ₀, hγ₀⟩ (fun j p => (hnext j p).choose) n
  have hPstep : ∀ n t, dist ((P n).val t) ((P (n + 1)).val t) ≤ d n := by
    intro n t
    exact (hnext n (P n)).choose_spec t
  obtain ⟨β, hβK, hβ⟩ := closed_set_path_limit hK (fun n => (P n).val) d ρ hd hd0 hPstep hρ
    (fun n => (P n).property)
  refine ⟨β, hβK, ?_⟩
  intro t
  simpa only [P, Nat.rec_zero, Nat.zero_add] using hβ 0 t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactLocalPaths
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact locally connected subsets of a Banach space have uniformly
small paths. Successive ambient replacements converge inside the set. -/
open Set Function Filter Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma compact_uniform_local_paths
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : IsCompact K) [LocallyConnectedSpace K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K, dist x y < δ →
      ∃ β : Path x y, (∀ t, β t ∈ K) ∧ ∀ t, dist (β t) x < ε := by
  obtain ⟨δ, hδ, hlocal⟩ := uniform_local_approximate_paths hK (show 0 < ε / 2 by linarith)
  let d : ℕ → ℝ := fun n => (ε / 8) * (1 / 2 : ℝ)^n
  have hdpos : ∀ n, 0 < d n := fun n => by dsimp [d] <;> positivity
  have hdsum : Summable d := summable_geometric_two.mul_left (ε / 8)
  have hdval : (∑' n, d n) = ε / 4 := by
    rw [show d = fun n => (ε / 8) * (1 / 2 : ℝ)^n by rfl, tsum_mul_left, tsum_geometric_two]
    ring
  choose ρ hρpos hreplace using fun n => compact_path_approximation_step hK (hdpos n)
  let τ : ℕ → ℝ := fun n => min (ρ n) (1 / (n + 1 : ℝ))
  have hτpos : ∀ n, 0 < τ n := fun n => lt_min (hρpos n) (by positivity)
  have hτlim : Tendsto τ atTop (𝓝 0) :=
    squeeze_zero (fun n => (hτpos n).le) (fun n => min_le_right _ _)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  obtain ⟨γ₀, hγ₀diam, hγ₀near⟩ := hlocal x hx y hy hxy (τ 0) (hτpos 0)
  have hstep : ∀ n, ∀ γ : Path x y,
      (∀ t, ∃ c ∈ K, dist (γ t) c < τ n) →
      ∃ β : Path x y, (∀ t, dist (γ t) (β t) ≤ d n) ∧
        (∀ t, ∃ c ∈ K, dist (β t) c < τ (n + 1)) := by
    intro n γ hn
    have hn' : ∀ t, ∃ c ∈ K, dist (γ t) c < ρ n := by
      intro t
      obtain ⟨c, hc, htc⟩ := hn t
      exact ⟨c, hc, htc.trans_le (min_le_left _ _)⟩
    obtain ⟨β, hβ, hβK⟩ := hreplace n x hx y hy γ hn' (τ (n + 1)) (hτpos (n + 1))
    exact ⟨β, fun t => by simpa only [dist_comm] using (hβ t).le, hβK⟩
  obtain ⟨β, hβK, hβ⟩ := iterate_path_approximations hK.isClosed d τ hdsum
    (fun n => (hdpos n).le) hτlim γ₀ hγ₀near hstep
  refine ⟨β, hβK, ?_⟩
  intro t
  have ht := hβ t
  rw [hdval, dist_comm] at ht
  have ht₀ := hγ₀diam t
  have htri := dist_triangle (β t) (γ₀ t) x
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactLocalPathConnectivity
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local path connectivity of compact locally connected metric spaces,
proved by small ambient approximations in the Kuratowski embedding. -/
open Set Metric Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma compact_subset_locallyPathConnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : IsCompact K) [LocallyConnectedSpace K] :
    LocallyPathConnectedSpace K := by
  apply locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr
  intro x U hU hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  obtain ⟨δ, hδ, hpaths⟩ := compact_uniform_local_paths hK hε
  apply mem_of_superset (Metric.ball_mem_nhds x hδ)
  intro y hy
  obtain ⟨β, hβK, hβsmall⟩ := hpaths x x.property y y.property (by simpa only [mem_ball, Subtype.dist_eq, dist_comm] using hy)
  let γ : Path x y :=
    { toFun := fun t => ⟨β t, hβK t⟩
      continuous_toFun := β.continuous.subtype_mk _
      source' := Subtype.ext β.source
      target' := Subtype.ext β.target }
  refine ⟨γ, fun t => hball ?_⟩
  exact hβsmall t

lemma compact_metric_locallyPathConnected
    (X : Type*) [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X] :
    LocallyPathConnectedSpace X := by
  let e : X ≃ₜ range (kuratowskiEmbedding X) :=
    (kuratowskiEmbedding.isometry X).isEmbedding.toHomeomorph
  let : LocallyConnectedSpace (range (kuratowskiEmbedding X)) :=
    e.isQuotientMap.isCoinducing.locallyConnectedSpace
  let : LocallyPathConnectedSpace (range (kuratowskiEmbedding X)) :=
    compact_subset_locallyPathConnected
      (isCompact_range (kuratowskiEmbedding.isometry X).continuous)
  exact e.isOpenEmbedding.locallyPathConnectedSpace

lemma compact_metric_connected_open_paths
    (X : Type*) [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (hconn : IsConnected U) : IsPathConnected U := by
  let := compact_metric_locallyPathConnected X
  exact hU.isConnected_iff_isPathConnected.mp hconn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Selection_ContinuousRunningMaximum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous running maximum for nonnegative continuous functions.
Using the norm of a curried map avoids any selection of maximizers. -/
open Set
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma le_runningMaximum (k : C(unitInterval, ℝ)) {s t : unitInterval} (hst : s ≤ t) :
    k s ≤ runningMaximum k t := by
  let F : C(unitInterval × unitInterval, ℝ) :=
    ⟨fun p => k (min p.1 p.2), k.continuous.comp (continuous_fst.min continuous_snd)⟩
  have hh := (F.curry t).norm_coe_le_norm s
  change ‖k (min t s)‖ ≤ runningMaximum k t at hh
  rw [min_eq_right hst, Real.norm_eq_abs] at hh
  exact (le_abs_self _).trans hh

lemma runningMaximum_mono (k : C(unitInterval, ℝ)) (hk : ∀ u, 0 ≤ k u) :
    Monotone (runningMaximum k) := by
  intro s t hst
  exact runningMaximum_le k hk (runningMaximum_nonneg k t)
    (fun u hu => le_runningMaximum k (hu.trans hst))

lemma runningMaximum_eq_of_constant (k : C(unitInterval, ℝ)) (hk : ∀ u, 0 ≤ k u)
    {s t : unitInterval} (hst : s ≤ t) (heq : ∀ u ∈ Icc s t, k u = k s) :
    runningMaximum k s = runningMaximum k t := by
  apply le_antisymm (runningMaximum_mono k hk hst)
  apply runningMaximum_le k hk (runningMaximum_nonneg k s)
  intro u hut
  by_cases hus : u ≤ s
  · exact le_runningMaximum k hus
  · rw [heq u ⟨le_of_not_ge hus, hut⟩]
    exact le_runningMaximum k le_rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathLoopErasure
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing a closed loop preserves every modulus of continuity and
cannot increase the diameter on any parameter interval. -/
open Set Function Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
variable {a b : unitInterval}

lemma erasePathLoop_of_le (g : C(unitInterval, X)) (hab : a ≤ b) (heq : g a = g b)
    {t : unitInterval} (ht : t ≤ a) : erasePathLoop g a b hab heq t = g t := by
  simp [erasePathLoop, ht.trans hab, min_eq_left ht]

lemma erasePathLoop_of_mem (g : C(unitInterval, X)) (hab : a ≤ b) (heq : g a = g b)
    {t : unitInterval} (ht : t ∈ Icc a b) : erasePathLoop g a b hab heq t = g a := by
  simp [erasePathLoop, ht.2, min_eq_right ht.1]

lemma erasePathLoop_of_ge (g : C(unitInterval, X)) (hab : a ≤ b) (heq : g a = g b)
    {t : unitInterval} (ht : b ≤ t) : erasePathLoop g a b hab heq t = g t := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa only [erasePathLoop_of_mem g hab heq ⟨hab, le_rfl⟩] using heq
  · simp [erasePathLoop, ht.not_ge]

lemma erasePathLoop_pair (g : C(unitInterval, X)) (hab : a ≤ b) (heq : g a = g b)
    {s t : unitInterval} (hst : s ≤ t) :
    erasePathLoop g a b hab heq s = erasePathLoop g a b hab heq t ∨
    ∃ u ∈ Icc s t, ∃ v ∈ Icc s t,
      erasePathLoop g a b hab heq s = g u ∧ erasePathLoop g a b hab heq t = g v := by
  by_cases hsa : s ≤ a
  · have hs := erasePathLoop_of_le g hab heq hsa
    by_cases hta : t ≤ a
    · exact Or.inr ⟨s, ⟨le_rfl, hst⟩, t, ⟨hst, le_rfl⟩, hs,
        erasePathLoop_of_le g hab heq hta⟩
    by_cases htb : t ≤ b
    · exact Or.inr ⟨s, ⟨le_rfl, hst⟩, a, ⟨hsa, le_of_not_ge hta⟩, hs,
        erasePathLoop_of_mem g hab heq ⟨le_of_not_ge hta, htb⟩⟩
    · exact Or.inr ⟨s, ⟨le_rfl, hst⟩, t, ⟨hst, le_rfl⟩, hs,
        erasePathLoop_of_ge g hab heq (le_of_not_ge htb)⟩
  by_cases hsb : s ≤ b
  · have hs := erasePathLoop_of_mem g hab heq ⟨le_of_not_ge hsa, hsb⟩
    by_cases htb : t ≤ b
    · exact Or.inl (hs.trans (erasePathLoop_of_mem g hab heq
        ⟨(le_of_not_ge hsa).trans hst, htb⟩).symm)
    · exact Or.inr ⟨b, ⟨hsb, le_of_not_ge htb⟩, t, ⟨hst, le_rfl⟩,
        hs.trans heq, erasePathLoop_of_ge g hab heq (le_of_not_ge htb)⟩
  · exact Or.inr ⟨s, ⟨le_rfl, hst⟩, t, ⟨hst, le_rfl⟩,
      erasePathLoop_of_ge g hab heq (le_of_not_ge hsb),
      erasePathLoop_of_ge g hab heq ((le_of_not_ge hsb).trans hst)⟩

lemma unitInterval_dist_le_of_mem_Icc {s t u v : unitInterval}
    (hu : u ∈ Icc s t) (hv : v ∈ Icc s t) : dist u v ≤ dist s t := by
  change |(u : ℝ) - v| ≤ |(s : ℝ) - t|
  have hu₁ : (s : ℝ) ≤ u := hu.1
  have hu₂ : (u : ℝ) ≤ t := hu.2
  have hv₁ : (s : ℝ) ≤ v := hv.1
  have hv₂ : (v : ℝ) ≤ t := hv.2
  rw [abs_of_nonpos (show (s : ℝ) - t ≤ 0 by linarith)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_PathIntervalOscillation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The diameter of a path image on a fixed parameter set is continuous
in the uniform metric. Loop deletion decreases every interval diameter. -/
open Set Function Metric Bornology
open scoped Topology unitInterval NNReal
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

lemma path_image_isBounded (S : Set unitInterval) (g : C(unitInterval, X)) :
    IsBounded (g '' S) :=
  (isCompact_range g.continuous).isBounded.subset (image_subset_range g S)

lemma pathOscillation_le_add (S : Set unitInterval) (g h : C(unitInterval, X)) :
    pathOscillation S g ≤ pathOscillation S h + 2 * dist g h := by
  apply diam_le_of_forall_dist_le (by unfold pathOscillation; positivity)
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  have h₁ := ContinuousMap.dist_apply_le_dist (f := g) (g := h) s
  have h₂ := ContinuousMap.dist_apply_le_dist (f := g) (g := h) t
  have h₃ := dist_le_diam_of_mem (path_image_isBounded S h)
    (mem_image_of_mem h hs) (mem_image_of_mem h ht)
  have h₄ := dist_triangle (g s) (h s) (g t)
  have h₅ := dist_triangle (h s) (h t) (g t)
  rw [dist_comm (h t) (g t)] at h₅
  dsimp [pathOscillation] at *
  linarith

lemma lipschitzWith_pathOscillation (S : Set unitInterval) :
    LipschitzWith 2 (pathOscillation (X := X) S) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  rw [Real.dist_eq]
  have h₁ := pathOscillation_le_add S g h
  have h₂ := pathOscillation_le_add S h g
  rw [dist_comm h g] at h₂
  change |pathOscillation S g - pathOscillation S h| ≤ 2 * dist g h
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma continuous_pathOscillation (S : Set unitInterval) :
    Continuous (pathOscillation (X := X) S) :=
  (lipschitzWith_pathOscillation S).continuous

lemma pathOscillation_erase_le (g : C(unitInterval, X))
    {a b : unitInterval} (hab : a ≤ b) (heq : g a = g b) (s t : unitInterval) :
    pathOscillation (Icc s t) (erasePathLoop g a b hab heq) ≤ pathOscillation (Icc s t) g := by
  apply diam_le_of_forall_dist_le Metric.diam_nonneg
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  wlog huv : u ≤ v generalizing u v
  · simpa only [dist_comm] using this v hv u hu (le_of_not_ge huv)
  rcases erasePathLoop_pair g hab heq huv with hsame | ⟨p, hp, q, hq, hup, hvq⟩
  · simpa only [hsame, dist_self] using (Metric.diam_nonneg (s := g '' Icc s t))
  · rw [hup, hvq]
    exact dist_le_diam_of_mem (path_image_isBounded (Icc s t) g)
      (mem_image_of_mem g ⟨hu.1.trans hp.1, hp.2.trans hv.2⟩)
      (mem_image_of_mem g ⟨hu.1.trans hq.1, hq.2.trans hv.2⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactLoopPathFamily
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact nonempty family of paths, stable under loop deletion.
It keeps the original image, endpoints and every uniform continuity bound. -/
open Set Function Filter Topology Metric
open scoped Topology UniformConvergence unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

lemma mem_loopPathFamily_self (f : C(unitInterval, X)) : f ∈ loopPathFamily f :=
  ⟨rfl, rfl, Subset.rfl, fun _ _ h => h⟩

lemma isClosed_loopPathFamily (f : C(unitInterval, X)) : IsClosed (loopPathFamily f) := by
  have hc : IsClosed {g : C(unitInterval, X) | range g ⊆ range f} := by
    simp only [range_subset_iff]
    simp only [ofPred_forall]
    exact isClosed_iInter fun t => (isCompact_range f.continuous).isClosed.preimage
      (continuous_eval_const t)
  have hm : IsClosed {g : C(unitInterval, X) |
      ∀ ε δ : ℝ, (∀ s t : unitInterval, dist s t ≤ δ → dist (f s) (f t) ≤ ε) →
        ∀ s t : unitInterval, dist s t ≤ δ → dist (g s) (g t) ≤ ε} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun ε => isClosed_iInter fun δ => isClosed_iInter fun _ =>
      isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
        isClosed_le ((continuous_eval_const s).dist (continuous_eval_const t)) continuous_const
  exact (isClosed_eq (continuous_eval_const 0) continuous_const).inter
    ((isClosed_eq (continuous_eval_const 1) continuous_const).inter (hc.inter hm))

lemma equicontinuous_loopPathFamily (f : C(unitInterval, X)) :
    Equicontinuous (fun g : loopPathFamily f => ((g : C(unitInterval, X)) : unitInterval → X)) := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 2) (by linarith)
  refine ⟨δ / 2, by linarith, ?_⟩
  intro y hy g
  have hh := g.property.2.2.2 (ε / 2) (δ / 2)
    (fun s t hst => (hmod (lt_of_le_of_lt hst (by linarith))).le) x y
    (by simpa only [dist_comm] using hy.le)
  exact hh.trans_lt (by linarith)

lemma isCompact_loopPathFamily [CompleteSpace X] (f : C(unitInterval, X)) : IsCompact (loopPathFamily f) := by
  have hcover : ⋃₀ {K : Set unitInterval | IsCompact K} = univ := by
    exact eq_univ_of_forall fun z => mem_sUnion.mpr ⟨{z}, isCompact_singleton, mem_singleton z⟩
  let : T2Space (unitInterval →ᵤ[{K : Set unitInterval | IsCompact K}] X) :=
    UniformOnFun.t2Space_of_covering hcover
  have he : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set unitInterval | IsCompact K} ∘
        (fun g : C(unitInterval, X) => (g : unitInterval → X))) :=
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hc := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (fun K hK => hK) he (fun K _ => (equicontinuous_loopPathFamily f).equicontinuousOn K)
    (fun _ _ z _ => ⟨range f, isCompact_range f.continuous, fun g hg =>
      hg.2.2.1 (mem_range_self z)⟩)
  rwa [(isClosed_loopPathFamily f).closure_eq] at hc

lemma erasePathLoop_mem (f g : C(unitInterval, X)) (hg : g ∈ loopPathFamily f)
    {a b : unitInterval} (hab : a ≤ b) (heq : g a = g b) :
    erasePathLoop g a b hab heq ∈ loopPathFamily f := by
  refine ⟨(erasePathLoop_of_le g hab heq bot_le).trans hg.1,
    (erasePathLoop_of_ge g hab heq le_top).trans hg.2.1, ?_, ?_⟩
  · rintro z ⟨t, rfl⟩
    by_cases ht : t ≤ b
    · change (Iic b).piecewise (fun t => g (min t a)) g t ∈ range f
      simpa only [Set.piecewise, mem_Iic, ht, ↓reduceIte] using hg.2.2.1 (mem_range_self (min t a))
    · change (Iic b).piecewise (fun t => g (min t a)) g t ∈ range f
      simpa only [Set.piecewise, mem_Iic, ht, ↓reduceIte] using hg.2.2.1 (mem_range_self t)
  · intro ε δ hmod s t hst
    have hε : 0 ≤ ε := by
      have hh := hmod s s
      by_cases hδ : 0 ≤ δ
      · simpa using hh (by simpa using hδ)
      · exact False.elim (hδ (dist_nonneg.trans hst))
    wlog horder : s ≤ t generalizing s t
    · simpa only [dist_comm] using this t s (by simpa only [dist_comm] using hst) (le_of_not_ge horder)
    rcases erasePathLoop_pair g hab heq horder with hsame | ⟨u, hu, v, hv, hsu, htv⟩
    · simpa only [hsame, dist_self] using hε
    · rw [hsu, htv]
      exact hg.2.2.2 ε δ hmod u v ((unitInterval_dist_le_of_mem_Icc hu hv).trans hst)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LoopOscillationMinimum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Minimizing a uniformly convergent sum of interval oscillations.
Every nonconstant loop can strictly decrease one term without increasing
any other term. -/
open Set Function Filter Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

lemma loopOscillationTerm_nonneg (n : ℕ) (g : C(unitInterval, X)) :
    0 ≤ loopOscillationTerm n g :=
  mul_nonneg (by positivity) (le_min zero_le_one Metric.diam_nonneg)

lemma loopOscillationTerm_le (n : ℕ) (g : C(unitInterval, X)) :
    loopOscillationTerm n g ≤ (1 / 2 : ℝ)^n := by
  exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_eq (mul_one _)

lemma summable_loopOscillationTerm (g : C(unitInterval, X)) :
    Summable (fun n => loopOscillationTerm n g) :=
  Summable.of_nonneg_of_le (fun n => loopOscillationTerm_nonneg n g)
    (fun n => loopOscillationTerm_le n g) summable_geometric_two

lemma continuous_loopOscillationCost : Continuous (loopOscillationCost (X := X)) := by
  apply continuous_tsum (fun n => continuous_const.mul
    (continuous_const.min (continuous_pathOscillation (pathTestInterval n)))) summable_geometric_two
  intro n g
  change ‖loopOscillationTerm n g‖ ≤ (1 / 2 : ℝ)^n
  rw [Real.norm_eq_abs, abs_of_nonneg (loopOscillationTerm_nonneg n g)]
  exact loopOscillationTerm_le n g

lemma loopOscillationCost_erase_lt (g : C(unitInterval, X))
    {a b : unitInterval} (hab : a ≤ b) (heq : g a = g b)
    (hstrict : ∃ n, pathTestInterval n ⊆ Icc a b ∧
      0 < pathOscillation (pathTestInterval n) g) :
    loopOscillationCost (erasePathLoop g a b hab heq) < loopOscillationCost g := by
  obtain ⟨n, hsub, hn⟩ := hstrict
  have hle : ∀ k, loopOscillationTerm k (erasePathLoop g a b hab heq) ≤
      loopOscillationTerm k g := by
    intro k
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact min_le_min_left 1 (pathOscillation_erase_le g hab heq _ _)
  have hz : pathOscillation (pathTestInterval n) (erasePathLoop g a b hab heq) = 0 := by
    apply le_antisymm _ Metric.diam_nonneg
    apply diam_le_of_forall_dist_le le_rfl
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [erasePathLoop_of_mem g hab heq (hsub hu),
      erasePathLoop_of_mem g hab heq (hsub hv), dist_self]
  have hlt : loopOscillationTerm n (erasePathLoop g a b hab heq) < loopOscillationTerm n g := by
    unfold loopOscillationTerm
    rw [hz, min_eq_right zero_le_one, mul_zero]
    exact mul_pos (by positivity) (lt_min zero_lt_one hn)
  exact Summable.tsum_lt_tsum hle hlt (summable_loopOscillationTerm _) (summable_loopOscillationTerm _)

lemma exists_loopOscillation_minimum [CompleteSpace X] (f : C(unitInterval, X)) :
    ∃ g ∈ loopPathFamily f, ∀ h ∈ loopPathFamily f, loopOscillationCost g ≤ loopOscillationCost h :=
  (isCompact_loopPathFamily f).exists_isMinOn ⟨f, mem_loopPathFamily_self f⟩
    continuous_loopOscillationCost.continuousOn

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LooplessPath
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A diameter minimizer has no nonconstant closed subpath. -/
open Set Function Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

lemma dense_interval_closure {a b : unitInterval} (hab : a < b) :
    Icc a b ⊆ closure (Ioo a b ∩ range (denseSeq unitInterval)) := by
  have hsub : Ioo a b ⊆ closure (Ioo a b ∩ range (denseSeq unitInterval)) := by
    intro t ht
    apply isOpen_Ioo.inter_closure
    exact ⟨ht, (denseRange_denseSeq unitInterval) t⟩
  simpa only [closure_Ioo hab.ne, closure_closure] using closure_mono hsub

lemma nonconstant_loop_detected (g : C(unitInterval, X))
    {a b : unitInterval} (hab : a ≤ b)
    (hnc : ∃ u ∈ Icc a b, g u ≠ g a) :
    ∃ n, pathTestInterval n ⊆ Icc a b ∧ 0 < pathOscillation (pathTestInterval n) g := by
  have hlt : a < b := hab.lt_of_ne (by
    intro he
    subst b
    obtain ⟨u, hu, hne⟩ := hnc
    exact hne (congrArg g (le_antisymm hu.2 hu.1)))
  let D := Ioo a b ∩ range (denseSeq unitInterval)
  have hclosure : Icc a b ⊆ closure D := dense_interval_closure hlt
  have hD : D.Nonempty := by
    obtain ⟨t, ht, htr⟩ := (denseRange_denseSeq unitInterval).inter_open_nonempty
      (Ioo a b) isOpen_Ioo (nonempty_Ioo.mpr hlt)
    exact ⟨t, ht, htr⟩
  obtain ⟨c, hc⟩ := hD
  have hne : ∃ s ∈ D, ∃ t ∈ D, g s ≠ g t := by
    by_contra! hall
    have heq : closure D ⊆ {t | g t = g c} := by
      apply closure_minimal _ (isClosed_eq g.continuous continuous_const)
      exact fun t ht => hall t ht c hc
    obtain ⟨u, hu, hnu⟩ := hnc
    exact hnu ((heq (hclosure hu)).trans (heq (hclosure ⟨le_rfl, hab⟩)).symm)
  obtain ⟨s, hs, t, ht, hst⟩ := hne
  wlog hord : s ≤ t generalizing s t
  · exact this t ht s hs hst.symm (le_of_not_ge hord)
  obtain ⟨i, rfl⟩ := hs.2
  obtain ⟨j, rfl⟩ := ht.2
  refine ⟨Nat.pair i j, ?_, ?_⟩
  · simp only [pathTestInterval, Nat.unpair_pair]
    exact Icc_subset_Icc hs.1.1.le ht.1.2.le
  · change 0 < Metric.diam (g '' pathTestInterval (Nat.pair i j))
    apply Metric.diam_pos _ (path_image_isBounded _ _)
    refine ⟨g (denseSeq unitInterval i), ?_, g (denseSeq unitInterval j), ?_, hst⟩
    · exact mem_image_of_mem g (by simpa only [pathTestInterval, Nat.unpair_pair, mem_Icc] using And.intro le_rfl hord)
    · exact mem_image_of_mem g (by simpa only [pathTestInterval, Nat.unpair_pair, mem_Icc] using And.intro hord le_rfl)

lemma exists_loopless_path [CompleteSpace X] (f : C(unitInterval, X)) :
    ∃ g ∈ loopPathFamily f, ∀ a b : unitInterval, a ≤ b → g a = g b →
      ∀ u ∈ Icc a b, g u = g a := by
  obtain ⟨g, hg, hmin⟩ := exists_loopOscillation_minimum f
  refine ⟨g, hg, ?_⟩
  intro a b hab heq
  by_contra! hbad
  have hstrict := loopOscillationCost_erase_lt g hab heq (nonconstant_loop_detected g hab hbad)
  exact hstrict.not_ge (hmin _ (erasePathLoop_mem f g hg hab heq))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LooplessTimeCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuous monotone coordinates on a loopless path. Prefix distances
separate distinct fibers; running maxima are constant on every pause. -/
open Set Function Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

lemma prefixDistance_eq_zero (g : C(unitInterval, X)) {a t : unitInterval} (ht : t ≤ a) :
    prefixDistance g a t = 0 := by
  change min 1 (infDist (g t) (g '' Iic a)) = 0
  rw [infDist_zero_of_mem (mem_image_of_mem g ht), min_eq_right zero_le_one]

lemma prefixDistance_pos (g : C(unitInterval, X))
    (hloop : ∀ s t : unitInterval, s ≤ t → g s = g t → ∀ u ∈ Icc s t, g u = g s)
    {a t : unitInterval} (hat : a ≤ t) (hne : g a ≠ g t) :
    0 < prefixDistance g a t := by
  apply lt_min zero_lt_one
  have hc : IsClosed (g '' Iic a) := (isClosed_Iic.isCompact.image g.continuous).isClosed
  rw [← infDist_pos_iff_notMem_closure (s := g '' Iic a) ⟨g 0, mem_image_of_mem g (show (0 : unitInterval) ≤ a from bot_le)⟩, hc.closure_eq]
  rintro ⟨u, hu, heq⟩
  exact hne ((hloop u t (hu.trans hat) heq a ⟨hu, hat⟩).trans heq)

lemma prefixRunning_eq_zero (g : C(unitInterval, X)) {a t : unitInterval} (ht : t ≤ a) :
    runningMaximum (prefixDistance g a) t = 0 := by
  apply le_antisymm _ (runningMaximum_nonneg _ _)
  exact runningMaximum_le _ (prefixDistance_nonneg g a) le_rfl
    (fun u hu => (prefixDistance_eq_zero g (hu.trans ht)).le)

lemma prefixRunning_eq_of_loop (g : C(unitInterval, X))
    (hloop : ∀ s t : unitInterval, s ≤ t → g s = g t → ∀ u ∈ Icc s t, g u = g s)
    (a : unitInterval) {s t : unitInterval} (hst : s ≤ t) (heq : g s = g t) :
    runningMaximum (prefixDistance g a) s = runningMaximum (prefixDistance g a) t := by
  apply runningMaximum_eq_of_constant _ (prefixDistance_nonneg g a) hst
  intro u hu
  change min 1 (infDist (g u) _) = min 1 (infDist (g s) _)
  rw [hloop s t hst heq u hu]

lemma dense_prefix_separates (g : C(unitInterval, X)) {s t : unitInterval}
    (hst : s < t) (hne : g s ≠ g t) :
    ∃ n, s < denseSeq unitInterval n ∧ denseSeq unitInterval n < t ∧
      g (denseSeq unitInterval n) ≠ g t := by
  by_contra! hall
  have hd : Ioo s t ∩ range (denseSeq unitInterval) ⊆ {u | g u = g t} := by
    rintro u ⟨hu, n, rfl⟩
    exact hall n hu.1 hu.2
  have hclosed : IsClosed {u | g u = g t} := isClosed_eq g.continuous continuous_const
  exact hne (closure_minimal hd hclosed (dense_interval_closure hst ⟨le_rfl, hst.le⟩))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_LooplessSeparatingCoordinate
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single continuous monotone real coordinate with exactly the fibers
of a loopless metric path. -/
open Set Function Metric TopologicalSpace
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity
variable {X : Type*} [MetricSpace X]

lemma summable_looplessCoordinateTerm (g : C(unitInterval, X)) (t : unitInterval) :
    Summable (fun n => looplessCoordinateTerm g n t) :=
  Summable.of_nonneg_of_le (fun n => looplessCoordinateTerm_nonneg g n t)
    (fun n => looplessCoordinateTerm_le g n t) summable_geometric_two

lemma looplessCoordinate_mono (g : C(unitInterval, X)) : Monotone (looplessCoordinate g) := by
  intro s t hst
  exact Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left
      (runningMaximum_mono _ (prefixDistance_nonneg _ _) hst) (by positivity))
    (summable_looplessCoordinateTerm g s) (summable_looplessCoordinateTerm g t)

lemma looplessCoordinate_eq_of_eq (g : C(unitInterval, X))
    (hloop : ∀ s t : unitInterval, s ≤ t → g s = g t → ∀ u ∈ Icc s t, g u = g s)
    {s t : unitInterval} (heq : g s = g t) : looplessCoordinate g s = looplessCoordinate g t := by
  wlog hst : s ≤ t generalizing s t
  · exact (this heq.symm (le_of_not_ge hst)).symm
  apply tsum_congr
  intro n
  change (1 / 2 : ℝ)^n * _ = (1 / 2 : ℝ)^n * _
  rw [prefixRunning_eq_of_loop g hloop _ hst heq]

lemma looplessCoordinate_lt_of_ne (g : C(unitInterval, X))
    (hloop : ∀ s t : unitInterval, s ≤ t → g s = g t → ∀ u ∈ Icc s t, g u = g s)
    {s t : unitInterval} (hst : s ≤ t) (hne : g s ≠ g t) :
    looplessCoordinate g s < looplessCoordinate g t := by
  have hlt : s < t := lt_of_le_of_ne hst (fun h => hne (congrArg g h))
  obtain ⟨n, hsn, hnt, hne'⟩ := dense_prefix_separates g hlt hne
  have hle : ∀ k, looplessCoordinateTerm g k s ≤ looplessCoordinateTerm g k t :=
    fun k => mul_le_mul_of_nonneg_left
      (runningMaximum_mono _ (prefixDistance_nonneg _ _) hst) (by positivity)
  have hterm : looplessCoordinateTerm g n s < looplessCoordinateTerm g n t := by
    change (1 / 2 : ℝ)^n * _ < (1 / 2 : ℝ)^n * _
    apply mul_lt_mul_of_pos_left _ (by positivity)
    rw [prefixRunning_eq_zero g hsn.le]
    exact (prefixDistance_pos g hloop hnt.le hne').trans_le (le_runningMaximum _ le_rfl)
  exact Summable.tsum_lt_tsum hle hterm
    (summable_looplessCoordinateTerm g s) (summable_looplessCoordinateTerm g t)

lemma looplessCoordinate_fibers (g : C(unitInterval, X))
    (hloop : ∀ s t : unitInterval, s ≤ t → g s = g t → ∀ u ∈ Icc s t, g u = g s)
    (s t : unitInterval) : looplessCoordinate g s = looplessCoordinate g t ↔ g s = g t := by
  constructor
  · intro h
    by_contra hne
    rcases le_total s t with hst | hts
    · exact (looplessCoordinate_lt_of_ne g hloop hst hne).ne h
    · exact (looplessCoordinate_lt_of_ne g hloop hts (Ne.symm hne)).ne h.symm
  · exact looplessCoordinate_eq_of_eq g hloop

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RealCoordinateSimplePath
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous real coordinate with exactly the same fibers as a path
reparametrizes that path injectively on the unit interval. -/
open Set Function
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma simplePath_of_real_coordinate {X : Type*} [TopologicalSpace X]
    (g : C(unitInterval, X)) (q : C(unitInterval, ℝ)) (hqmono : Monotone q)
    (hfibers : ∀ s t, q s = q t ↔ g s = g t) (hne : g 0 ≠ g 1) :
    ∃ β : Path (g 0) (g 1), Injective β ∧ range β ⊆ range g := by
  let e : unitInterval → range q := fun t => ⟨q t, mem_range_self t⟩
  have he : Continuous e := q.continuous.subtype_mk _
  have hes : Surjective e := by
    rintro ⟨x, t, rfl⟩
    exact ⟨t, rfl⟩
  let r : range q → unitInterval := fun z => Classical.choose z.property
  have hr (z : range q) : q (r z) = z := Classical.choose_spec z.property
  let α : range q → X := fun z => g (r z)
  have hαe : α ∘ e = g := by
    funext t
    apply (hfibers _ _).mp
    exact hr (e t)
  have hα : Continuous α :=
    (Topology.IsQuotientMap.of_surjective_continuous hes he).continuous_iff.mpr
      (hαe ▸ g.continuous)
  have hαinj : Injective α := by
    intro z w h
    apply Subtype.ext
    exact (hr z).symm.trans (((hfibers _ _).mpr h).trans (hr w))
  have hq : q 0 < q 1 := lt_of_le_of_ne (hqmono bot_le)
    (fun h => hne ((hfibers 0 1).mp h))
  have hqr : Icc (q 0) (q 1) ⊆ range q :=
    (intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from bot_le)
      q.continuous.continuousOn).trans (image_subset_range _ _)
  let p : unitInterval → range q := fun t =>
    ⟨q 0 + (q 1 - q 0) * (t : ℝ), hqr (by
      have ht₀ := t.property.1
      have ht₁ := t.property.2
      constructor <;> nlinarith)⟩
  have hp : Continuous p :=
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _
  have hp0 : (p 0 : ℝ) = q 0 := by simp [p]
  have hp1 : (p 1 : ℝ) = q 1 := by simp [p]
  have hpinj : Injective p := by
    intro s t h
    have hv := congrArg Subtype.val h
    change q 0 + (q 1 - q 0) * (s : ℝ) = q 0 + (q 1 - q 0) * (t : ℝ) at hv
    apply Subtype.ext
    nlinarith
  let β : Path (g 0) (g 1) :=
    { toFun := fun t => α (p t)
      continuous_toFun := hα.comp hp
      source' := (hfibers _ _).mp ((hr (p 0)).trans hp0)
      target' := (hfibers _ _).mp ((hr (p 1)).trans hp1) }
  refine ⟨β, hαinj.comp hpinj, ?_⟩
  rintro z ⟨t, rfl⟩
  exact ⟨r (p t), rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_SimpleArcsProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small path approximations give local path connectivity; minimization of interval oscillations erases loops,
and a monotone separating coordinate removes the remaining constant pauses. -/
open Set Function
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma exists_injective_subpath {X : Type*} [MetricSpace X] [CompleteSpace X]
    {x y : X} (γ : Path x y) (hne : x ≠ y) :
    ∃ β : Path x y, Injective β ∧ range β ⊆ range γ := by
  obtain ⟨g, hg, hloop⟩ := exists_loopless_path γ.toContinuousMap
  have hg0 : g 0 = x := hg.1.trans γ.source
  have hg1 : g 1 = y := hg.2.1.trans γ.target
  have hgne : g 0 ≠ g 1 := fun h => hne (hg0.symm.trans (h.trans hg1))
  obtain ⟨β, hβinj, hβrange⟩ := simplePath_of_real_coordinate g (looplessCoordinate g)
    (looplessCoordinate_mono g) (looplessCoordinate_fibers g hloop) hgne
  refine ⟨β.cast hg0.symm hg1.symm, hβinj, ?_⟩
  exact hβrange.trans hg.2.2.1

/-- Lorimer's connected-open simple-arc specialization. -/
theorem hasSimpleArcsInConnectedOpens_compact_metric
    (X : Type*) [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X] :
    HasSimpleArcsInConnectedOpens X := by
  intro U hU hconn x hx y hy hne
  obtain ⟨γ, hγ⟩ := (compact_metric_connected_open_paths X hU hconn).joinedIn x hx y hy
  obtain ⟨β, hβinj, hβrange⟩ := exists_injective_subpath γ hne
  exact ⟨β, hβinj, hβrange.trans (range_subset_iff.mpr hγ)⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_ThickenedContinuumDisk
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small open neighborhood of a connected subset of the closed disk
remains connected when restricted to the open disk. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_inner_disk_scale {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 1-r < δ := by
  obtain ⟨r,hr,hr1⟩ := exists_between (max_lt (by norm_num : (0 : ℝ) < 1)
    (by linarith : 1-δ < 1))
  exact ⟨r,(le_max_left _ _).trans_lt hr,hr1,by linarith [le_max_right (0 : ℝ) (1-δ)]⟩

lemma inner_disk_scale_dist {r : ℝ} (_hr : 0 < r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : dist (r • z) z ≤ 1-r := by
  calc
    dist (r • z) z = ‖(r-1) • z‖ := by rw [dist_eq_norm,sub_smul,one_smul]
    _ = (1-r) * ‖z‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_neg (sub_neg.mpr hr1)]; ring
    _ ≤ (1-r)*1 := mul_le_mul_of_nonneg_left hz (by linarith)
    _ = 1-r := mul_one _

lemma isConnected_thickening_inter_disk {A : Set ℂ} (hA : IsConnected A)
    (hAd : A ⊆ closedBall (0 : ℂ) 1) {δ : ℝ} (hδ : 0 < δ) :
    IsConnected (thickening δ A ∩ ball (0 : ℂ) 1) := by
  obtain ⟨r,hr,hr1,hrδ⟩ := exists_inner_disk_scale hδ
  let C := (fun z : ℂ => r • z) '' A
  have hC : IsConnected C := hA.image _ (continuous_const_smul (T := ℂ) r).continuousOn
  have hscaled (a : ℂ) (ha : a ∈ A) :
      r • a ∈ ball a δ ∩ ball (0 : ℂ) 1 := by
    have han : ‖a‖ ≤ 1 := mem_closedBall_zero_iff.mp (hAd ha)
    refine ⟨(inner_disk_scale_dist hr hr1 han).trans_lt hrδ,?_⟩
    rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_of_le_one_right hr.le han).trans_lt hr1
  have hCU : C ⊆ thickening δ A ∩ ball (0 : ℂ) 1 := by
    rintro z ⟨a,ha,rfl⟩
    exact ⟨mem_thickening_iff.mpr ⟨a,ha,(hscaled a ha).1⟩,(hscaled a ha).2⟩
  have hp : IsPreconnected (⋃ a : A, C ∪ (ball (a : ℂ) δ ∩ ball 0 1)) := by
    obtain ⟨c,hc⟩ := hC.nonempty
    apply isPreconnected_iUnion
    · exact ⟨c,mem_iInter.mpr (fun _ => Or.inl hc)⟩
    · intro a
      exact hC.isPreconnected.union (r • (a : ℂ)) ⟨a,a.property,rfl⟩ (hscaled a a.property)
        ((convex_ball (a : ℂ) δ).inter (convex_ball 0 1)).isPreconnected
  have he : (⋃ a : A, C ∪ (ball (a : ℂ) δ ∩ ball 0 1)) =
      thickening δ A ∩ ball (0 : ℂ) 1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha⟩ := mem_iUnion.mp hz
      rcases ha with h | h
      · exact hCU h
      · exact ⟨mem_thickening_iff.mpr ⟨a,a.property,h.1⟩,h.2⟩
    · rintro ⟨hz,hzb⟩
      obtain ⟨a,ha,hza⟩ := mem_thickening_iff.mp hz
      exact mem_iUnion.mpr ⟨⟨a,ha⟩,Or.inr ⟨hza,hzb⟩⟩
  obtain ⟨c,hc⟩ := hC.nonempty
  exact ⟨⟨c,hCU hc⟩,he ▸ hp⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CrosscutAvoidingContinuum
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A connected compact set in the closed disk can be replaced by a simple
crosscut with the same two boundary endpoints while avoiding a disjoint closed set. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma radial_segment_in_thickened_disk {A : Set ℂ} {a : ℂ} (ha : a ∈ A)
    (han : ‖a‖ = 1) {r δ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hrδ : 1-r < δ) :
    range (Path.segment a (r • a)) ⊆ insert a (thickening δ A ∩ ball (0 : ℂ) 1) := by
  rintro z ⟨t,rfl⟩
  by_cases ht0 : t = 0
  · exact Or.inl (by rw [ht0,(Path.segment a (r • a)).source])
  have ht : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
    (fun h => ht0 (Subtype.ext h.symm))
  let s : ℝ := 1-(t : ℝ)+(t : ℝ)*r
  have hsr : r ≤ s := by dsimp [s] <;> nlinarith [t.property.2]
  have hs : 0 < s := hr.trans_le hsr
  have hs1 : s < 1 := by dsimp [s] <;> nlinarith
  have he : Path.segment a (r • a) t = s • a := by
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,smul_smul,← add_smul]
    rfl
  rw [he]
  right
  refine ⟨mem_thickening_iff.mpr ⟨a,ha,?_⟩,?_⟩
  · exact (inner_disk_scale_dist hs hs1 han.le).trans_lt (by linarith)
  · rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos hs,han,mul_one]
    exact hs1

lemma exists_disk_crosscut_avoiding {A B : Set ℂ}
    (hAc : IsCompact A) (hA : IsConnected A) (hAd : A ⊆ closedBall (0 : ℂ) 1)
    (hBc : IsClosed B) (hAB : Disjoint A B)
    {a b : ℂ} (ha : a ∈ A) (hb : b ∈ A) (han : ‖a‖ = 1) (hbn : ‖b‖ = 1)
    (hab : a ≠ b) :
    ∃ p : Path a b, Injective p ∧
      (∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) ∧ Disjoint (range p) B := by
  obtain ⟨δ,hδ,hδB⟩ := hAc.exists_thickening_subset_open hBc.isOpen_compl
    (Set.disjoint_left.mp hAB)
  obtain ⟨r,hr,hr1,hrδ⟩ := exists_inner_disk_scale hδ
  let U := thickening δ A ∩ ball (0 : ℂ) 1
  have hU : IsOpen U := isOpen_thickening.inter isOpen_ball
  have hUc : IsConnected U := isConnected_thickening_inter_disk hA hAd hδ
  have hmem (x : ℂ) (hx : x ∈ A) : r • x ∈ U := by
    have hxn := mem_closedBall_zero_iff.mp (hAd hx)
    refine ⟨mem_thickening_iff.mpr ⟨x,hx,(inner_disk_scale_dist hr hr1 hxn).trans_lt hrδ⟩,?_⟩
    rw [mem_ball_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_of_le_one_right hr.le hxn).trans_lt hr1
  obtain ⟨η,hη⟩ := (hU.isConnected_iff_isPathConnected.mp hUc).joinedIn _ (hmem a ha) _ (hmem b hb)
  let γ := ((Path.segment a (r • a)).trans η).trans (Path.segment b (r • b)).symm
  have hγ : range γ ⊆ insert a (insert b U) := by
    rw [Path.trans_range,Path.trans_range,Path.symm_range]
    apply union_subset
    · apply union_subset
      · exact (radial_segment_in_thickened_disk ha han hr hr1 hrδ).trans
          (insert_subset_insert (subset_insert b U))
      · exact (range_subset_iff.mpr hη).trans ((subset_insert b U).trans (subset_insert a _))
    · intro z hz
      rcases radial_segment_in_thickened_disk hb hbn hr hr1 hrδ hz with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  obtain ⟨p,hpi,hpγ⟩ := exists_injective_subpath γ hab
  have hp := hpγ.trans hγ
  refine ⟨p,hpi,?_,?_⟩
  · intro t ht
    rcases hp (mem_range_self t) with he | he | hu
    · have he' : p t = p 0 := he.trans p.source.symm
      exact (ne_of_gt ht.1 (hpi he')).elim
    · have he' : p t = p 1 := he.trans p.target.symm
      exact (ne_of_lt ht.2 (hpi he')).elim
    · exact mem_ball_zero_iff.mp hu.2
  · apply Set.disjoint_left.mpr
    intro z hz hzB
    rcases hp hz with rfl | rfl | hu
    · exact Set.disjoint_left.mp hAB ha hzB
    · exact Set.disjoint_left.mp hAB hb hzB
    · exact hδB hu.1 hzB

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CrosscutBoundarySeparation
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A connected set in the closed disk avoiding a crosscut cannot join
its two boundary arcs. This includes continua that run along the circle. -/
open Set Function Metric Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma crosscut_closed_side_locally_open {a : ℂ} (p : Path a 1) (ha : ‖a‖ = 1)
    (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range p ∪ range (boundaryClosingArc a ha))
    (hinside : jordanInterior H ⊆ ball (0 : ℂ) 1)
    {z : ℂ} (hz : z ∈ closure (jordanInterior H)) (hzp : z ∉ range p) :
    ∃ ε > 0, ball z ε ∩ closedBall (0 : ℂ) 1 ⊆ closure (jordanInterior H) := by
  by_cases hzJ : z ∈ jordanInterior H
  · obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (jordanInterior_isOpen H) z hzJ
    exact ⟨ε,hε,fun _ h => subset_closure (hball h.1)⟩
  · have hzf : z ∈ frontier (jordanInterior H) := by
      rw [(jordanInterior_isOpen H).frontier_eq]
      exact ⟨hz,hzJ⟩
    have hc : IsClosed (range p) := (isCompact_range p.continuous).isClosed
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hc.isOpen_compl z hzp
    refine ⟨ε,hε,closed_disk_neighborhood_in_filling H hinside hzf hε ?_⟩
    rintro w ⟨hw,hwf⟩
    rw [hf] at hwf
    rcases hwf with hwp | ⟨t,rfl⟩
    · exact (hball hw hwp).elim
    · exact mem_sphere_zero_iff_norm.mpr (boundaryClosingArc_norm a ha t)

lemma connected_avoiding_crosscut_one_side {a : ℂ} (p : Path a 1) (ha : ‖a‖ = 1)
    (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range p ∪ range (boundaryClosingArc a ha))
    (hinside : jordanInterior H ⊆ ball (0 : ℂ) 1)
    {B : Set ℂ} (hB : IsPreconnected B) (hBd : B ⊆ closedBall (0 : ℂ) 1)
    (hBp : Disjoint B (range p)) :
    B ⊆ closure (jordanInterior H) ∨ B ⊆ (closure (jordanInterior H))ᶜ := by
  let T : Set B := {z | (z : ℂ) ∈ closure (jordanInterior H)}
  let : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp hB
  have hc : IsClosed T := isClosed_closure.preimage continuous_subtype_val
  have ho : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ε,hε,hball⟩ := crosscut_closed_side_locally_open p ha H hf hinside hz
      (fun h => Set.disjoint_left.mp hBp z.property h)
    have hn : ∀ᶠ w : B in 𝓝 z, (w : ℂ) ∈ ball z.val ε :=
      continuous_subtype_val.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hε))
    filter_upwards [hn] with w hw
    exact hball ⟨hw,hBd w.property⟩
  by_cases hn : T.Nonempty
  · left
    have h := (show IsClopen T from ⟨hc,ho⟩).eq_univ hn
    intro z hz
    have hzT : (⟨z,hz⟩ : B) ∈ T := h.symm ▸ mem_univ _
    exact hzT
  · right
    intro z hz hzc
    exact hn ⟨⟨z,hz⟩,hzc⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_DiskCrossingProof
attribute [-instance] _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alternating compact continua in the closed disk intersect, derived
from the existing Schoenflies input and the constructed simple crosscut. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem unitDiskAlternatingContinua (hsch : PlanarSchoenflies) : UnitDiskAlternatingContinua := by
  intro A B hAc hA hBc hB hAd hBd θ hθ h0 h2 h1 h3
  by_contra hn
  have hAB : Disjoint A B := Set.disjoint_left.mpr (fun z hzA hzB => hn ⟨z,hzA,hzB⟩)
  let z : Fin 4 → ℂ := fun i => standardCirclePoint (θ i)
  have hz0 : z 0 ≠ 0 := by
    intro h
    have he := Circle.norm_coe ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) (θ 0))
    change ‖z 0‖ = 1 at he
    rw [h,norm_zero] at he
    exact zero_ne_one he
  have h20 : z 2 ≠ z 0 := by
    intro h
    have he := congrArg unitCircleCut (standardCirclePoint_injective h)
    exact (ne_of_gt (hθ (by decide : (0 : Fin 4) < 2))) he
  obtain ⟨p,hpi,hpint,hpB⟩ := exists_disk_crosscut_avoiding hAc hA hAd hBc.isClosed hAB
    h2 h0 (Circle.norm_coe _) (Circle.norm_coe _) h20
  let R := Homeomorph.mulLeft₀ (z 0) hz0
  let q : Path ((z 0)⁻¹ * z 2) 1 := {
    toFun := fun t => (z 0)⁻¹ * p t
    continuous_toFun := continuous_const.mul p.continuous
    source' := by rw [p.source]
    target' := by rw [p.target,inv_mul_cancel₀ hz0] }
  have hqp (t : PathTime) : R (q t) = p t := by
    change z 0 * ((z 0)⁻¹ * p t) = p t
    rw [← mul_assoc,mul_inv_cancel₀ hz0,one_mul]
  have hRnorm (w : ℂ) : ‖R.symm w‖ = ‖w‖ := by
    change ‖(z 0)⁻¹ * w‖ = ‖w‖
    rw [norm_mul,norm_inv,show ‖z 0‖ = 1 from Circle.norm_coe _,inv_one,one_mul]
  have hqi : Injective q := fun s t he => hpi (by rw [← hqp s,← hqp t,he])
  have hqint : ∀ t ∈ Ioo (0 : PathTime) 1, ‖q t‖ < 1 := by
    intro t ht
    change ‖R.symm (p t)‖ < 1
    rw [hRnorm]
    exact hpint t ht
  obtain ⟨ha,ha1,hx,hy⟩ := alternating_boundary_rotated_arcs θ hθ
  obtain ⟨H,hf,_,hinside⟩ := exists_disk_crosscut_jordan hsch q hqi hqint ha ha1
  let C := R.symm '' B
  have hC : IsPreconnected C := hB.isPreconnected.image R.symm R.symm.continuous.continuousOn
  have hCd : C ⊆ closedBall (0 : ℂ) 1 := by
    rintro _ ⟨w,hw,rfl⟩
    rw [mem_closedBall_zero_iff,hRnorm]
    exact mem_closedBall_zero_iff.mp (hBd hw)
  have hCq : Disjoint C (range q) := by
    apply Set.disjoint_left.mpr
    rintro w ⟨b,hb,he⟩ ⟨t,ht⟩
    have hpt : p t = b := by
      rw [← hqp t,ht,← he,R.apply_symm_apply]
    exact Set.disjoint_left.mp hpB ⟨t,hpt⟩ hb
  have hxC : (z 0)⁻¹ * z 1 ∈ C := ⟨z 1,h1,rfl⟩
  have hyC : (z 0)⁻¹ * z 3 ∈ C := ⟨z 3,h3,rfl⟩
  have hxcl : (z 0)⁻¹ * z 1 ∈ closure (jordanInterior H) :=
    frontier_subset_closure (hf ▸ Or.inr hx)
  have hynot : (z 0)⁻¹ * z 3 ∉ closure (jordanInterior H) := by
    have he := disk_crosscut_exterior_circle q ha hqint H hf hinside
    have hh := he.symm ▸ hy
    exact hh.1
  rcases connected_avoiding_crosscut_one_side q ha H hf hinside hC hCd hCq with h | h
  · exact hynot (h hyC)
  · exact h hxC hxcl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PathSelectionProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions _root_.OAI.CircleDomainRigidity.finiteSphericalArea _root_.OAI.CircleDomainRigidity.instCompactSpaceElemHitConfigurationAmbientHitConfiguration _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeCoeKernelRectifiablePathMeasurePathLengthKernel _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instIsFiniteMeasurePathCostSpacePathCostMeasureValBasePathCodeLtENNRealCoeMeasureSetUnivTop _root_.OAI.CircleDomainRigidity.instIsFiniteMeasureRectifiableOccupationCode _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePathLengthMeasure _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimePhysicalTimeLength _root_.OAI.CircleDomainRigidity.instNullSingletonClassElemRealPathTimeRectifiableLengthCode _root_.OAI.CircleDomainRigidity.instStandardBorelSpaceTaggedPathOfCompleteSpaceOfSecondCountableTopology _root_.OAI.CircleDomainRigidity.sphereFirstCountableTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the published completed-measure path-selection input by
parametrizing the Borel relation with Baire space and selecting a branch. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 theorem borelPathRelationSelection : BorelPathRelationSelection := by
  intro μ R hR hfull
  have ha : AnalyticSet R := hR.analyticSet
  rw [AnalyticSet] at ha
  rcases ha with hempty | ⟨q,hq,hqR⟩
  · obtain ⟨α,hα⟩ := hfull (ContinuousMap.const PathTime OnePoint.infty)
    rw [hempty] at hα
    exact hα.elim
  · let g : (ℕ → ℕ) → C(PathTime, Sphere) := fun b => (q b).1
    have hsurj : Surjective g := by
      intro γ
      obtain ⟨α,hα⟩ := hfull γ
      rw [← hqR] at hα
      obtain ⟨b,hb⟩ := hα
      exact ⟨b,congrArg Prod.fst hb⟩
    obtain ⟨b,hb,hinv⟩ := exists_nullMeasurable_baire_rightInverse
      (μ : Measure C(PathTime, Sphere)) g hq.fst hsurj
    refine ⟨fun γ => (q (b γ)).2,hq.snd.measurable.comp_nullMeasurable hb,?_⟩
    intro γ
    have hmem : q (b γ) ∈ R := hqR ▸ mem_range_self (b γ)
    have he : q (b γ) = (γ,(q (b γ)).2) := Prod.ext (hinv γ) rfl
    rwa [he] at hmem

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.DiskMaximal_MaximalEstimates
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace DiskMaximalTools

lemma volume_dilate_five (x : ℂ) (r : ℝ) :
    volume (ball x (5*r)) = 25 * volume (ball x r) := by
  rw [Complex.volume_ball, Complex.volume_ball, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]
  norm_num [mul_pow]
  ring

/-- The actual Vitali weak-(1,1) estimate, with no assumed maximal inequality. -/
theorem weak_bound_bounded_family {ι : Type*} (t : Set ι) (x : ι → ℂ) (r : ι → ℝ)
    (ν : Measure ℂ) {R a : ℝ} (ha : 0 < a)
    (hr : ∀ i ∈ t, 0 < r i) (hR : ∀ i ∈ t, r i ≤ R)
    (hav : ∀ i ∈ t, ENNReal.ofReal a * volume (ball (x i) (r i)) ≤ ν (ball (x i) (r i))) :
    volume (⋃ i ∈ t, ball (x i) (r i)) ≤ (25 / ENNReal.ofReal a) * ν univ := by
  obtain ⟨u,hut,hdisj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    t x r R hR 5 (by norm_num)
  have huc : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun i hi => ⟨x i,mem_ball_self (hr i (hut hi))⟩)
  have : Countable u := huc.to_subtype
  have hsub : (⋃ i ∈ t, ball (x i) (r i)) ⊆ ⋃ i : u, ball (x i) (5*r i) := by
    intro y hy
    obtain ⟨i,hi,hy⟩ := mem_iUnion₂.mp hy
    obtain ⟨j,hj,hij⟩ := hcover i hi
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,hij hy⟩
  have hmass : (∑' i : u, ν (ball (x i) (r i))) ≤ ν univ := by
    rw [← measure_iUnion (fun (i j : u) hij => hdisj i.property j.property (fun h => hij (Subtype.ext h)))
      (fun _ => measurableSet_ball)]
    exact measure_mono (subset_univ _)
  calc
    _ ≤ volume (⋃ i : u, ball (x i) (5*r i)) := measure_mono hsub
    _ ≤ ∑' i : u, volume (ball (x i) (5*r i)) := measure_iUnion_le _
    _ = ∑' i : u, 25 * volume (ball (x i) (r i)) := by simp_rw [volume_dilate_five]
    _ ≤ ∑' i : u, (25 / ENNReal.ofReal a) * ν (ball (x i) (r i)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      have hb := hav i (hut i.property)
      calc
        _ = (25 / ENNReal.ofReal a) * (ENNReal.ofReal a * volume (ball (x i) (r i))) := by
          rw [← mul_assoc, ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) ENNReal.ofReal_ne_top]
        _ ≤ _ := by gcongr
    _ = (25 / ENNReal.ofReal a) * ∑' i : u, ν (ball (x i) (r i)) := by rw [ENNReal.tsum_mul_left]
    _ ≤ _ := by gcongr

lemma volume_disk_real (x : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball x r) = ENNReal.ofReal (Real.pi*r^2) := by
  rw [Complex.volume_ball,ENNReal.ofReal_mul Real.pi_nonneg,ENNReal.ofReal_pow hr]
  rw [← (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (NNReal.pi : ℝ) = (NNReal.pi : ℝ≥0∞))]
  exact mul_comm _ _

/-- All high-average balls of a finite measure have a common finite radius
bound; the bounded-family Vitali argument therefore controls every radius. -/
theorem weak_bound {ν : Measure ℂ} [IsFiniteMeasure ν] {a : ℝ} (ha : 0 < a) :
    volume {x : ℂ | ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal a * volume (ball x r) ≤ ν (ball x r)} ≤
      (25 / ENNReal.ofReal a) * ν univ := by
  let t : Set (ℂ × ℝ) := {p | 0 < p.2 ∧
    ENNReal.ofReal a * volume (ball p.1 p.2) ≤ ν (ball p.1 p.2)}
  let B : ℝ := (ν univ).toReal/(a*Real.pi)
  have hB : 0 ≤ B := div_nonneg ENNReal.toReal_nonneg (mul_pos ha Real.pi_pos).le
  have hR : ∀ p ∈ t, p.2 ≤ B+1 := by
    intro p hp
    have hh := hp.2.trans (measure_mono (subset_univ _))
    rw [volume_disk_real _ hp.1.le,← ENNReal.ofReal_mul ha.le] at hh
    have hh' : a*(Real.pi*p.2^2) ≤ (ν univ).toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hh
    have hs : p.2^2 ≤ B := (le_div_iff₀ (mul_pos ha Real.pi_pos)).mpr (by nlinarith)
    nlinarith [sq_nonneg (p.2-1)]
  have hweak := weak_bound_bounded_family t Prod.fst Prod.snd ν ha
    (fun _ hp => hp.1) hR (fun _ hp => hp.2)
  apply le_trans (measure_mono ?_) hweak
  intro x hx
  obtain ⟨r,hr,havg⟩ := hx
  exact mem_iUnion₂.mpr ⟨(x,r),⟨hr,havg⟩,mem_ball_self hr⟩

lemma measurable_ball_mass (ν : Measure ℂ) [SFinite ν] (r : ℝ) :
    Measurable (fun x : ℂ => ν (ball x r)) := by
  have hm : MeasurableSet {p : ℂ × ℂ | dist p.2 p.1 < r} :=
    isOpen_lt (continuous_snd.dist continuous_fst) continuous_const |>.measurableSet
  exact measurable_measure_prodMk_left hm

lemma measurable_rationalMaximal (ν : Measure ℂ) [SFinite ν] :
    Measurable (rationalMaximal ν) := by
  unfold rationalMaximal
  apply Measurable.iSup
  intro q
  apply Measurable.iSup
  intro _
  have hd : Measurable (fun x : ℂ => volume (ball x (q:ℝ))) := by
    simp only [Complex.volume_ball]
    exact measurable_const
  exact (measurable_ball_mass ν (q:ℝ)).div hd

/-- Truncating an input below half the testing height sharpens weak type by
charging only its large values. This is the interpolation mechanism. -/
lemma weak_split {ν η : Measure ℂ} [IsFiniteMeasure η] {a : ℝ} (ha : 0 < a)
    (hsplit : ∀ x r, 0 < r → ν (ball x r) ≤ η (ball x r)+
      ENNReal.ofReal (a/2)*volume (ball x r)) :
    volume {x | ENNReal.ofReal a < rationalMaximal ν x} ≤
      (25 / ENNReal.ofReal (a/2)) * η univ := by
  apply le_trans (measure_mono ?_) (weak_bound (by linarith : 0 < a/2))
  intro x hx
  change ENNReal.ofReal a < ⨆ (q : ℚ) (_ : 0 < q), ν (ball x q) / volume (ball x q) at hx
  obtain ⟨q,hh⟩ := lt_iSup_iff.mp hx
  obtain ⟨hq,hh⟩ := lt_iSup_iff.mp hh
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  have hh' := (ENNReal.lt_div_iff_mul_lt (Or.inl hv0) (Or.inl measure_ball_lt_top.ne)).mp hh
  refine ⟨q,hq',?_⟩
  by_contra h
  have hη : η (ball x (q:ℝ)) ≤ ENNReal.ofReal (a/2)*volume (ball x (q:ℝ)) := (lt_of_not_ge h).le
  have hfull := (hsplit x q hq').trans (add_le_add hη le_rfl)
  have hsum : ENNReal.ofReal (a/2)+ENNReal.ofReal (a/2) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_add (by linarith : 0 ≤ a/2) (by linarith : 0 ≤ a/2)]
    congr 1
    ring
  rw [← add_mul,hsum] at hfull
  exact (not_lt_of_ge hfull) hh'

lemma weak_truncated {f : ℂ → ℝ≥0∞} (hf : Measurable f)
    [IsFiniteMeasure (volume.withDensity f)] {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < rationalMaximal (volume.withDensity f) x} ≤
      (25 / ENNReal.ofReal (a/2)) *
        ∫⁻ x, {x | ENNReal.ofReal (a/2) < f x}.indicator f x := by
  let H := {x | ENNReal.ofReal (a/2) < f x}
  let η := volume.withDensity (H.indicator f)
  have hle : η ≤ volume.withDensity f := withDensity_mono (ae_of_all _ (indicator_le_self _ _))
  have : IsFiniteMeasure η := isFiniteMeasure_of_le _ hle
  have hweak := weak_split (ν := volume.withDensity f) (η := η) ha ?_
  · simpa only [η,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ] using hweak
  · intro x r _
    rw [withDensity_apply _ measurableSet_ball,show η = volume.withDensity (H.indicator f) from rfl,
      withDensity_apply _ measurableSet_ball]
    calc
      _ ≤ ∫⁻ y in ball x r, H.indicator f y+ENNReal.ofReal (a/2) := by
        apply lintegral_mono
        intro y
        dsimp only
        by_cases hy : y ∈ H
        · rw [indicator_of_mem hy]
          exact le_add_right le_rfl
        · rw [indicator_of_notMem hy,zero_add]
          exact le_of_not_gt hy
      _ = _ := by
        rw [lintegral_add_left (hf.indicator (measurableSet_lt measurable_const hf))]
        simp only [lintegral_const,Measure.restrict_apply_univ]
        rfl

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace DiskMaximalTools

lemma lintegral_rpow_Ioo {b s : ℝ} (hb : 0 ≤ b) (hs : -1 < s) :
    (∫⁻ t in Ioo 0 b, ENNReal.ofReal (t^s)) = ENNReal.ofReal (b^(s+1)/(s+1)) := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · simp [Real.zero_rpow (by linarith : s+1 ≠ 0)]
  · have hi : IntegrableOn (fun t : ℝ => t^s) (Ioo 0 b) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hb).mpr hs
    rw [← ofReal_integral_eq_lintegral_ofReal hi]
    · rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hb.le,
        integral_rpow (Or.inl hs)]
      simp [Real.zero_rpow (by linarith : s+1 ≠ 0)]
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
      exact Real.rpow_nonneg ht.1.le _

lemma truncation_layer_single {b p : ℝ} (hb : 0 ≤ b) (hp : 1 < p) :
    (∫⁻ t in Ioi 0, (if t < 2*b then ENNReal.ofReal b else 0)*ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal (2^(p-1)/(p-1))*ENNReal.ofReal (b^p) := by
  have heq : (fun t : ℝ => (if t < 2*b then ENNReal.ofReal b else 0)*ENNReal.ofReal (t^(p-2))) =
      (Iio (2*b)).indicator (fun t => ENNReal.ofReal b * ENNReal.ofReal (t^(p-2))) := by
    funext t
    by_cases ht : t < 2*b <;> simp [ht]
  rw [heq,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hi : Iio (2*b) ∩ Ioi (0:ℝ) = Ioo 0 (2*b) := by ext t; simp [and_comm]
  rw [hi,lintegral_const_mul'' _ (by fun_prop)]
  rw [lintegral_rpow_Ioo (by positivity : 0 ≤ 2*b) (by linarith : -1 < p-2)]
  have hpp : p-2+1 = p-1 := by ring
  rw [hpp]
  have h2 : 0 ≤ (2:ℝ)^(p-1)/(p-1) := div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
  rw [← ENNReal.ofReal_mul hb,← ENNReal.ofReal_mul h2]
  congr 1
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hb]
  have hp0 : 0 < p-1 := by linarith
  have hpow : b*b^(p-1) = b^p := by
    rcases eq_or_lt_of_le hb with rfl | hb
    · simp [Real.zero_rpow hp0.ne',Real.zero_rpow (by linarith : p ≠ 0)]
    · calc
        b*b^(p-1) = b^(1:ℝ)*b^(p-1) := by rw [Real.rpow_one]
        _ = b^(1+(p-1)) := (Real.rpow_add hb _ _).symm
        _ = b^p := by congr 1; ring
  calc
    b * (2^(p-1)*b^(p-1)/(p-1)) = (2^(p-1)/(p-1))*(b*b^(p-1)) := by ring
    _ = _ := by rw [hpow]

/-- Exact Tonelli computation behind strong maximal interpolation, for every
p > 1. The singularity at testing height zero is actually integrated. -/
theorem truncation_layer_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [SFinite μ] {f : α → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) :
    (∫⁻ t in Ioi 0,
      (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0 ∂μ)*ENNReal.ofReal (t^(p-2))) =
      ENNReal.ofReal (2^(p-1)/(p-1))*(∫⁻ x, ENNReal.ofReal ((f x)^p) ∂μ) := by
  have hm : Measurable (fun z : ℝ × α =>
      (if z.1 < 2*f z.2 then ENNReal.ofReal (f z.2) else 0)*ENNReal.ofReal (z.1^(p-2))) := by
    apply Measurable.mul
    · exact ((hf.comp measurable_snd).ennreal_ofReal).ite
        (measurableSet_lt measurable_fst ((hf.comp measurable_snd).const_mul 2)) measurable_const
    · exact (measurable_fst.pow_const _).ennreal_ofReal
  calc
    _ = ∫⁻ t in Ioi 0, ∫⁻ x,
        (if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2)) ∂μ := by
      apply lintegral_congr
      intro t
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ x, (∫⁻ t in Ioi 0,
        (if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ x, ENNReal.ofReal (2^(p-1)/(p-1))*ENNReal.ofReal ((f x)^p) ∂μ := by
      apply lintegral_congr
      intro x
      exact truncation_layer_single (hf0 x) hp
    _ = _ := lintegral_const_mul'' _ ((hf.pow_const _).ennreal_ofReal.aemeasurable)

end DiskMaximalTools

namespace DiskMaximalTools

lemma maximal_layer_coefficient {t p : ℝ} (ht : 0 < t) :
    (25 / ENNReal.ofReal (t/2))*ENNReal.ofReal (t^(p-1)) =
      ENNReal.ofReal 50*ENNReal.ofReal (t^(p-2)) := by
  rw [← show ENNReal.ofReal (25:ℝ) = 25 by norm_num,
    ← ENNReal.ofReal_div_of_pos (by linarith : 0 < t/2),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (25:ℝ)/(t/2)),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 50)]
  congr 1
  have hpow : t^(p-1) = t*t^(p-2) := by
    calc
      _ = t^(1+(p-2)) := by congr 1; ring
      _ = t^(1:ℝ)*t^(p-2) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hpow]
  field_simp
  ring

/-- A full strong p estimate from Vitali, truncation and Tonelli. No maximal
inequality is supplied as an assumption. The real representative is controlled
even before a separate almost-everywhere finiteness argument. -/
theorem strong_rationalMaximal {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) [IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))]
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, ENNReal.ofReal ((rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x))) x).toReal^p)) ≤
      ENNReal.ofReal (50*p*2^(p-1)/(p-1)) * (∫⁻ x, ENNReal.ofReal ((f x)^p)) := by
  let M := rationalMaximal (volume.withDensity (fun x => ENNReal.ofReal (f x)))
  have hM : Measurable M := measurable_rationalMaximal _
  have htail (t : ℝ) (ht : 0 < t) : volume {x | t < (M x).toReal} ≤
      (25/ENNReal.ofReal (t/2)) * ∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0 := by
    have hsub : {x | t < (M x).toReal} ⊆ {x | ENNReal.ofReal t < M x} := by
      intro x hx
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mpr hx |>.trans_le ENNReal.ofReal_toReal_le
    apply le_trans (measure_mono hsub)
    have hweak := weak_truncated hf.ennreal_ofReal ht
    apply hweak.trans_eq
    congr 1
    apply lintegral_congr
    intro x
    have heq : ENNReal.ofReal (t/2) < ENNReal.ofReal (f x) ↔ t < 2*f x := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith : 0 ≤ t/2)]
      constructor <;> intro h <;> linarith
    simp only [Set.indicator,Set.mem_ofPred_eq,heq]
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    hM.ennreal_toReal.aemeasurable (by linarith : 0 < p)]
  have hlayer : (∫⁻ t in Ioi 0, volume {x | t < (M x).toReal}*ENNReal.ofReal (t^(p-1))) ≤
      ENNReal.ofReal 50 * (∫⁻ t in Ioi 0,
        (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) := by
    calc
      _ ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal 50 *
          ((∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2))) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        calc
          _ ≤ ((25/ENNReal.ofReal (t/2)) * ∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*
              ENNReal.ofReal (t^(p-1)) := by gcongr; exact htail t ht
          _ = _ := by
            rw [mul_right_comm, maximal_layer_coefficient ht]
            ring
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal p*(ENNReal.ofReal 50 * (∫⁻ t in Ioi 0,
        (∫⁻ x, if t < 2*f x then ENNReal.ofReal (f x) else 0)*ENNReal.ofReal (t^(p-2)))) := by
      gcongr
    _ = _ := by
      rw [truncation_layer_integral hf hf0 hp]
      have hc : ENNReal.ofReal p*(ENNReal.ofReal 50 * ENNReal.ofReal (2^(p-1)/(p-1))) =
          ENNReal.ofReal (50*p*2^(p-1)/(p-1)) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 50),
          ← ENNReal.ofReal_mul (by linarith : 0 ≤ p)]
        congr 1
        ring
      simpa only [mul_assoc] using congrArg
        (fun c => c*(∫⁻ x, ENNReal.ofReal ((f x)^p))) hc

end DiskMaximalTools

namespace DiskMaximalTools

lemma disk_average_le_rationalMaximal_exact (ν : Measure ℂ) (x : ℂ) {r : ℝ} (hr : 0 < r) :
    ν (ball x r) / volume (ball x r) ≤ rationalMaximal ν x := by
  let I := {q : ℚ // 0 < q ∧ (q:ℝ) < r}
  have hdir : Directed (· ⊆ ·) (fun q : I => ball x (q:ℚ)) := by
    intro i j
    refine ⟨⟨max i.val j.val,?_,?_⟩,?_,?_⟩
    · exact lt_max_of_lt_left i.property.1
    · exact_mod_cast max_lt i.property.2 j.property.2
    · exact ball_subset_ball (by exact_mod_cast le_max_left i.val j.val)
    · exact ball_subset_ball (by exact_mod_cast le_max_right i.val j.val)
  have heq : (⋃ q : I, ball x (q:ℚ)) = ball x r := by
    ext y
    constructor
    · intro hy
      obtain ⟨q,hq⟩ := mem_iUnion.mp hy
      exact (ball_subset_ball q.property.2.le) hq
    · intro hy
      have hd : dist y x < r := hy
      obtain ⟨q,hq0,hqr⟩ := exists_rat_btwn (show max 0 (dist y x) < r by exact max_lt hr hd)
      have hq : 0 < (q:ℝ) := lt_of_le_of_lt (le_max_left _ _) hq0
      have hqRat : (0:ℚ) < q := by exact_mod_cast hq
      refine mem_iUnion.mpr ⟨⟨q,hqRat,hqr⟩,?_⟩
      exact lt_of_le_of_lt (le_max_right _ _) hq0
  have hv0 : volume (ball x r) ≠ 0 := by
    rw [volume_disk_real _ hr.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hr)))
  apply (ENNReal.div_le_iff hv0 measure_ball_lt_top.ne).mpr
  rw [← heq,hdir.measure_iUnion]
  apply iSup_le
  intro q
  have hq0 : 0 < (q.val:ℝ) := by exact_mod_cast q.property.1
  have hqv : volume (ball x (q.val:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq0.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq0)))
  have hav : ν (ball x (q.val:ℝ)) / volume (ball x (q.val:ℝ)) ≤ rationalMaximal ν x :=
    le_iSup_of_le q.val (le_iSup_of_le q.property.1 le_rfl)
  calc
    _ ≤ rationalMaximal ν x * volume (ball x (q.val:ℝ)) :=
      (ENNReal.div_le_iff hqv measure_ball_lt_top.ne).mp hav
    _ ≤ _ := by
      gcongr
      exact subset_iUnion (fun q : I => ball x (q:ℚ)) q

lemma rationalMaximal_le_of_density_le {f : ℂ → ℝ≥0∞} {B : ℝ≥0∞} (hf : ∀ x, f x ≤ B) (x : ℂ) :
    rationalMaximal (volume.withDensity f) x ≤ B := by
  unfold rationalMaximal
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hv0 : volume (ball x (q:ℝ)) ≠ 0 := by
    rw [volume_disk_real _ hq'.le]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Real.pi_pos (sq_pos_of_pos hq')))
  apply (ENNReal.div_le_iff hv0 measure_ball_lt_top.ne).mpr
  rw [withDensity_apply _ measurableSet_ball]
  calc
    _ ≤ ∫⁻ y in ball x (q:ℝ), B := lintegral_mono hf
    _ = _ := by simp

end DiskMaximalTools

open MeasureTheory Set
open scoped ENNReal NNReal
end
end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_BoundedMaximalL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Vitali/interpolation estimate, specialized to bounded,
integrable planar inputs. The representative dominates every ball average. -/
open Set Function Filter MeasureTheory Metric DiskMaximalTools
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem bounded_maximal_L2 {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f) (hf2 : MemLp f 2 volume)
    {B : ℝ} (hB : ∀ x, f x ≤ B) :
    ∃ m : ℂ → ℝ, Measurable m ∧ (∀ x, 0 ≤ m x) ∧ MemLp m 2 volume ∧
      (∫ x, m x^2) ≤ 200*(∫ x, f x^2) ∧
      (∀ x r, 0 < r → (∫ y in ball x r, f y) ≤ volume.real (ball x r)*m x) ∧
      ∀ x, ENNReal.ofReal (m x) = rationalMaximal (volume.withDensity (fun y => ENNReal.ofReal (f y))) x := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hfin : (∫⁻ x, ENNReal.ofReal (f x)) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0)).mp hfi.hasFiniteIntegral
  have : IsFiniteMeasure ν := ⟨by
    change volume.withDensity (fun x => ENNReal.ofReal (f x)) univ < ∞
    simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hfin⟩
  have hbound (x : ℂ) : rationalMaximal ν x ≤ ENNReal.ofReal B :=
    rationalMaximal_le_of_density_le (fun y => ENNReal.ofReal_le_ofReal (hB y)) x
  have hne (x : ℂ) : rationalMaximal ν x ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound x)
  let m := fun x => (rationalMaximal ν x).toReal
  have hm : Measurable m := (measurable_rationalMaximal ν).ennreal_toReal
  have hm0 (x : ℂ) : 0 ≤ m x := ENNReal.toReal_nonneg
  have hme (x : ℂ) : ENNReal.ofReal (m x) = rationalMaximal ν x :=
    ENNReal.ofReal_toReal (hne x)
  have hs := strong_rationalMaximal hf hf0 (p := 2) (by norm_num)
  norm_num only [Real.rpow_two, sub_self, sub_zero, Real.rpow_one, mul_one,
    div_one, Nat.cast_ofNat] at hs
  change (∫⁻ x, ENNReal.ofReal (m x^2)) ≤ ENNReal.ofReal (200:ℝ) *
    (∫⁻ x, ENNReal.ofReal (f x^2)) at hs
  have hfi2 := hf2.integrable_sq
  have he : (∫⁻ x, ENNReal.ofReal (f x^2)) = ENNReal.ofReal (∫ x, f x^2) :=
    (ofReal_integral_eq_lintegral_ofReal hfi2 (ae_of_all _ (fun x => sq_nonneg (f x)))).symm
  rw [he, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 200)] at hs
  have hmi : Integrable (fun x => m x^2) :=
    ⟨(hm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => sq_nonneg (m x)))).mpr
        (hs.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨m, hm, hm0, (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hmi, ?_, ?_, hme⟩
  · rw [← ofReal_integral_eq_lintegral_ofReal hmi (ae_of_all _ (fun x => sq_nonneg (m x)))] at hs
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num)
      (integral_nonneg (fun x => sq_nonneg (f x))))).mp hs
  · intro x r hr
    have hav := disk_average_le_rationalMaximal_exact ν x hr
    have hv : volume (ball x r) ≠ 0 := measure_ball_pos volume x hr |>.ne'
    have hh := (ENNReal.div_le_iff hv measure_ball_lt_top.ne).mp hav
    have hint : IntegrableOn f (ball x r) volume := hfi.integrableOn
    have hi : ENNReal.ofReal (∫ y in ball x r, f y) = ν (ball x r) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0),
        withDensity_apply _ measurableSet_ball]
    rw [← hme x, ← hi] at hh
    have hvol : ENNReal.ofReal (volume.real (ball x r)) = volume (ball x r) :=
      ENNReal.ofReal_toReal measure_ball_lt_top.ne
    rw [← hvol, ← ENNReal.ofReal_mul (hm0 x)] at hh
    have := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (hm0 x) measureReal_nonneg)).mp hh
    simpa only [mul_comm] using this

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_MaximalTruncations
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounded compactly supported increasing approximations to a nonnegative
L² function. Each fixed ball integral converges to the original integral. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma measurable_maximalInputTruncation {f : ℂ → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (maximalInputTruncation f n) :=
  (hf.min measurable_const).indicator isClosed_closedBall.measurableSet

lemma maximalInputTruncation_nonneg {f : ℂ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (n : ℕ) (x : ℂ) :
    0 ≤ maximalInputTruncation f n x :=
  indicator_nonneg (fun x _ => le_min (hf0 x) (Nat.cast_nonneg n)) x

lemma maximalInputTruncation_le {f : ℂ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (n : ℕ) (x : ℂ) :
    maximalInputTruncation f n x ≤ f x := by
  by_cases hx : x ∈ closedBall 0 (n : ℝ)
  · simpa only [maximalInputTruncation, indicator_of_mem hx] using min_le_left (f x) (n : ℝ)
  · simpa only [maximalInputTruncation, indicator_of_notMem hx] using hf0 x

lemma maximalInputTruncation_le_bound {f : ℂ → ℝ} (n : ℕ) (x : ℂ) :
    maximalInputTruncation f n x ≤ (n : ℝ) := by
  by_cases hx : x ∈ closedBall 0 (n : ℝ)
  · simpa only [maximalInputTruncation, indicator_of_mem hx] using min_le_right (f x) (n : ℝ)
  · simpa only [maximalInputTruncation, indicator_of_notMem hx] using Nat.cast_nonneg n

lemma maximalInputTruncation_mono {f : ℂ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (x : ℂ) :
    Monotone (fun n => maximalInputTruncation f n x) := by
  intro i j hij
  by_cases hx : x ∈ closedBall 0 (i : ℝ)
  · have hxj : x ∈ closedBall 0 (j : ℝ) := closedBall_subset_closedBall (Nat.cast_le.mpr hij) hx
    simp only [maximalInputTruncation, indicator_of_mem hx, indicator_of_mem hxj]
    exact min_le_min_left _ (Nat.cast_le.mpr hij)
  · simpa only [maximalInputTruncation, indicator_of_notMem hx] using
      maximalInputTruncation_nonneg hf0 j x

lemma maximalInputTruncation_eventually_eq (f : ℂ → ℝ) (x : ℂ) :
    ∀ᶠ n : ℕ in atTop, maximalInputTruncation f n x = f x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max ‖x‖ (f x))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hb : max ‖x‖ (f x) < (n : ℝ) := hN.trans_le (Nat.cast_le.mpr hn)
  have hx : x ∈ closedBall 0 (n : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using (le_max_left ‖x‖ (f x)).trans hb.le
  rw [maximalInputTruncation, indicator_of_mem hx,
    min_eq_left ((le_max_right ‖x‖ (f x)).trans hb.le)]

lemma maximalInputTruncation_memLp {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf2 : MemLp f 2 volume) (n : ℕ) :
    MemLp (maximalInputTruncation f n) 2 volume := by
  apply hf2.mono' (measurable_maximalInputTruncation hf n).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (maximalInputTruncation_nonneg hf0 n x)]
    exact maximalInputTruncation_le hf0 n x)

lemma maximalInputTruncation_integrable {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf2 : MemLp f 2 volume) (n : ℕ) :
    Integrable (maximalInputTruncation f n) := by
  have hlocal := (hf2.locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) (n : ℝ))
  have hmask : Integrable ((closedBall 0 (n : ℝ)).indicator f) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr hlocal
  apply hmask.mono_nonneg (measurable_maximalInputTruncation hf n).aestronglyMeasurable
    (ae_of_all _ (maximalInputTruncation_nonneg hf0 n))
  apply ae_of_all
  intro x
  by_cases hx : x ∈ closedBall 0 (n : ℝ)
  · rw [indicator_of_mem hx]
    exact maximalInputTruncation_le hf0 n x
  · simp only [maximalInputTruncation, indicator_of_notMem hx]
    exact le_rfl

lemma maximalInputTruncation_energy_le {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf2 : MemLp f 2 volume) (n : ℕ) :
    (∫ x, maximalInputTruncation f n x^2) ≤ ∫ x, f x^2 := by
  apply integral_mono (maximalInputTruncation_memLp hf hf0 hf2 n).integrable_sq hf2.integrable_sq
  intro x
  exact pow_le_pow_left₀ (maximalInputTruncation_nonneg hf0 n x)
    (maximalInputTruncation_le hf0 n x) 2

lemma tendsto_integral_maximalInputTruncation {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf2 : MemLp f 2 volume) (x : ℂ) (r : ℝ) :
    Tendsto (fun n => ∫ y in ball x r, maximalInputTruncation f n y)
      atTop (𝓝 (∫ y in ball x r, f y)) := by
  have hlocal := (hf2.locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall x r)
  apply tendsto_integral_of_dominated_convergence f
    (fun n => (measurable_maximalInputTruncation hf n).aestronglyMeasurable)
    (hlocal.mono_set ball_subset_closedBall)
  · intro n
    exact ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (maximalInputTruncation_nonneg hf0 n y)]
      exact maximalInputTruncation_le hf0 n y)
  · apply ae_of_all
    intro y
    have he : (fun n => maximalInputTruncation f n y) =ᶠ[atTop] (fun _ => f y) :=
      maximalInputTruncation_eventually_eq f y
    exact tendsto_const_nhds.congr' he.symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_NonnegativeMaximalL2
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pass the bounded maximal estimate through increasing compact truncations.
The finite L² limit dominates every original ball integral almost everywhere. -/
open Set Function Filter MeasureTheory Metric DiskMaximalTools
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

theorem nonnegative_maximal_L2 {f : ℂ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf2 : MemLp f 2 volume) :
    ∃ m : ℂ → ℝ, Measurable m ∧ (∀ x, 0 ≤ m x) ∧ MemLp m 2 volume ∧
      (∫ x, m x^2) ≤ 200*(∫ x, f x^2) ∧
      ∀ r : ℝ, 0 < r → ∀ᵐ x ∂volume,
        (∫ y in ball x r, f y) ≤ volume.real (ball x r)*m x := by
  have hb (n : ℕ) := bounded_maximal_L2 (measurable_maximalInputTruncation hf n)
    (maximalInputTruncation_nonneg hf0 n) (maximalInputTruncation_integrable hf hf0 hf2 n)
    (maximalInputTruncation_memLp hf hf0 hf2 n) (maximalInputTruncation_le_bound (f := f) n)
  choose m hm hm0 hm2 hE hav hme using hb
  have hmono (x : ℂ) : Monotone (fun n => m n x) := by
    intro i j hij
    have hν : volume.withDensity (fun y => ENNReal.ofReal (maximalInputTruncation f i y)) ≤
        volume.withDensity (fun y => ENNReal.ofReal (maximalInputTruncation f j y)) :=
      withDensity_mono (ae_of_all _ (fun y =>
        ENNReal.ofReal_le_ofReal (maximalInputTruncation_mono hf0 y hij)))
    have hle : ENNReal.ofReal (m i x) ≤ ENNReal.ofReal (m j x) := by
      rw [hme i x, hme j x]
      unfold rationalMaximal
      apply iSup_mono
      intro q
      apply iSup_mono
      intro _
      exact ENNReal.div_le_div_right (hν (ball x (q : ℝ))) _
    exact (ENNReal.ofReal_le_ofReal_iff (hm0 j x)).mp hle
  have hB : 0 ≤ 200*(∫ x, f x^2) := mul_nonneg (by norm_num)
    (integral_nonneg (fun x => sq_nonneg (f x)))
  obtain ⟨P, hP, hP0, hP2, hPE, hlim⟩ := exists_monotone_L2_limit hm hm2 hm0 hmono hB
    (fun n => (hE n).trans (mul_le_mul_of_nonneg_left
      (maximalInputTruncation_energy_le hf hf0 hf2 n) (by norm_num)))
  refine ⟨P, hP, hP0, hP2, hPE, ?_⟩
  intro r hr
  filter_upwards [hlim] with x hx
  apply le_of_tendsto (tendsto_integral_maximalInputTruncation hf hf0 hf2 x r)
  exact Eventually.of_forall (fun n => (hav n x r hr).trans
    (mul_le_mul_of_nonneg_left (hx.2 n) measureReal_nonneg))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarMaximalProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact planar L² maximal input, including a finite nonnegative
representative and the average bound for every positive fixed radius. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

theorem planarMaximalL2 : PlanarMaximalL2 := by
  refine ⟨20, by norm_num, ?_⟩
  intro g hg
  let f : ℂ → ℝ := hg.aestronglyMeasurable.mk g
  have hf : Measurable f := hg.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have heq : g =ᵐ[volume] f := hg.aestronglyMeasurable.ae_eq_mk
  have hf2 : MemLp f 2 volume := hg.ae_eq heq
  obtain ⟨m, hm, hm0, hm2, hE, hav⟩ := nonnegative_maximal_L2 hf.norm
    (fun x => norm_nonneg (f x)) hf2.norm
  have hsq : (∫ x, ‖f x‖^2) = ∫ x, g x^2 := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    rw [← hx, Real.norm_eq_abs, sq_abs]
  refine ⟨m, hm, hm0, hm2, ?_, ?_⟩
  · rw [hsq] at hE
    exact hE.trans (mul_le_mul_of_nonneg_right (by norm_num) (integral_nonneg fun x => sq_nonneg (g x)))
  · intro r hr
    have hev (x : ℂ) : (∫ y in ball x r, ‖g y‖) = ∫ y in ball x r, ‖f y‖ :=
      integral_congr_ae (heq.restrict (s := ball x r) |>.fun_comp norm)
    filter_upwards [hav r hr] with x hx
    rwa [hev x]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Theorems
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle-domain uniformization from finite Jordan models constructed by invariant
Beltrami reflection, and rigidity under conformal removability. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

local instance instBorelSpaceSphere_81_r26ada9_1 : BorelSpace Sphere := ⟨rfl⟩
theorem circleDomainRemovabilityRigidity_of_remaining_published_inputs
    (hfinite : FiniteCircleUniformization)
    : CircleDomainRemovabilityRigidity := by
  have hsch : PlanarSchoenflies := planarSchoenflies
  have hcompact : SmoothCompactMetricSphereUniformization := smoothCompactMetricSphereUniformization
  exact circleDomainRemovabilityRigidity_of_scalar_solver planarMaximalL2 principalConductivityScalarSolver principalRealBeltrami planarSobolevCoarea (unitDiskAlternatingContinua hsch)
    planarLipschitzFiberCoarea weightedPlanarScalarCoarea finiteTorusAnalyticMeasurability smoothPlanarSard hsch (unitDiskCrosscutSeparation hsch) (smoothRegularJordanCollars unorientedFiniteCircleGreenFormula) borelPathRelationSelection unorientedFiniteCircleGreenFormula (exteriorCoefficientAreaTheorem hsch unorientedFiniteCircleGreenFormula) hcompact (finiteCircleUniformization_jordanModels hfinite)
    montelExhaustion hurwitzUnivalentLimit hurwitzZeroFreeLimit (by
      intro C hC hLC
      let : CompactSpace C := isCompact_iff_compactSpace.mp hC
      let : LocallyConnectedSpace C := hLC
      exact hasSimpleArcsInConnectedOpens_compact_metric C) (by intros; exact standardBorelProbabilityLaws _) (polishProbabilityLaws _) (by intros; exact measureImageDuality _ _) (by intros; exact measurePlanLifting _ _) (exteriorOmittedAreaTheorem hsch unorientedFiniteCircleGreenFormula)

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem koebeCircleDomainConjecture
    : KoebeCircleDomainConjecture := by
  let : MeasurableSpace C(PathTime, Sphere) := borel _
  let : BorelSpace C(PathTime, Sphere) := ⟨rfl⟩
  have hsch : PlanarSchoenflies := planarSchoenflies
  have hcompact : SmoothCompactMetricSphereUniformization := smoothCompactMetricSphereUniformization
  exact koebeCircleDomainConjecture_of_constructed_quotient (unitDiskAlternatingContinua hsch) planarLipschitzFiberCoarea weightedPlanarScalarCoarea finiteTorusAnalyticMeasurability
    smoothPlanarSard hsch (unitDiskCrosscutSeparation hsch) (smoothRegularJordanCollars unorientedFiniteCircleGreenFormula) borelPathRelationSelection unorientedFiniteCircleGreenFormula (exteriorCoefficientAreaTheorem hsch unorientedFiniteCircleGreenFormula) hcompact finiteJordanModelUniformization montelExhaustion
    hurwitzUnivalentLimit hurwitzZeroFreeLimit (by
      intro C hC hLC
      let : CompactSpace C := isCompact_iff_compactSpace.mp hC
      let : LocallyConnectedSpace C := hLC
      exact hasSimpleArcsInConnectedOpens_compact_metric C) (by intros; exact standardBorelProbabilityLaws _) (polishProbabilityLaws _) (by intros; exact measureImageDuality _ _) (by intros; exact measurePlanLifting _ _)


/- The full published finite-circle existence statement follows from
 the unconditional Koebe theorem; the proof above only used the constructed
 finite Jordan models. -/
omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem finiteCircleUniformization : FiniteCircleUniformization := by
  intro U hU hconn _ _
  exact koebeCircleDomainConjecture U hU hconn

omit [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)] in
theorem circleDomainRemovabilityRigidity : CircleDomainRemovabilityRigidity := by
  let : MeasurableSpace C(PathTime, Sphere) := borel _
  let : BorelSpace C(PathTime, Sphere) := ⟨rfl⟩
  exact circleDomainRemovabilityRigidity_of_remaining_published_inputs finiteCircleUniformization

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circle-domain uniformization and rigidity under conformal removability. -/
open Set CircleDomainRigidity
noncomputable section
namespace Problem047

theorem removability_implies_rigidity_oai :
    ∀ (U V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain U → IsCircleDomain V →
      IsConformallyRemovable (frontier U) → IsConformalEquivalence f U V →
      ∃ M : Mobius, ∀ p ∈ U, f p = M • p :=
  CircleDomainRigidity.circleDomainRemovabilityRigidity

end Problem047

end

end OAI
end

theorem solution : type_of% @OAI.Problem047.removability_implies_rigidity_oai := @OAI.Problem047.removability_implies_rigidity_oai
