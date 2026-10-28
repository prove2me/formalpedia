-- Prove2me | solution 1 for OAI.PlaneFiveColor.Spectral.exists_terminal_factor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:15:45.717117+00:00
-- url     : https://prove2.me/submissions/a72714af-a661-4239-af7c-9b2a86d9506f

import Mathlib
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_PlaneFiveColor_Spectral_ambient_uniform_precision_contradiction
import Theorems.Thm_OAI_PlaneFiveColor_Spectral_finite_uniform_precision_contradiction

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Centers
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace EuclideanFiveColor.Location

theorem center_minimizes (μ : ProbabilityMeasure ℂ) (s : ℂ) :
    objective (μ : Measure ℂ) (center μ) ≤ objective (μ : Measure ℂ) s :=
  (exists_unique_minimizer (μ : Measure ℂ)).choose_spec.1 s

theorem center_unique (μ : ProbabilityMeasure ℂ) {z : ℂ}
    (hz : ∀ t, objective (μ : Measure ℂ) z ≤ objective (μ : Measure ℂ) t) :
    z = center μ := (exists_unique_minimizer (μ : Measure ℂ)).choose_spec.2 z hz

theorem measurable_objective (s : ℂ) :
    Measurable (fun μ : ProbabilityMeasure ℂ => objective (μ : Measure ℂ) s) :=
  ((continuous_kernel s).stronglyMeasurable.integral_kernel
    (κ := universalKernel)).measurable

theorem denseSeq_inf_eq_min {X : Type*} [TopologicalSpace X] [TopologicalSpace.SeparableSpace X]
    [Nonempty X] (f : X → ℝ) (hf : Continuous f) (x : X)
    (hx : ∀ y, f x ≤ f y) : (⨅ n, f (TopologicalSpace.denseSeq X n)) = f x := by
  have hb : BddBelow (Set.range (fun n => f (TopologicalSpace.denseSeq X n))) :=
    ⟨f x, by rintro _ ⟨n, rfl⟩; exact hx _⟩
  apply le_antisymm
  · exact (TopologicalSpace.denseRange_denseSeq X).induction_on
      (p := fun y => (⨅ n, f (TopologicalSpace.denseSeq X n)) ≤ f y) x
      (isClosed_le continuous_const hf) (fun n => ciInf_le hb n)
  · exact le_ciInf (fun n => hx _)

theorem measurable_minValue : Measurable minValue :=
  Measurable.iInf fun _n => measurable_objective _

theorem minValue_eq (μ : ProbabilityMeasure ℂ) :
    minValue μ = objective (μ : Measure ℂ) (center μ) :=
  denseSeq_inf_eq_min _ (continuous_objective _) _ (center_minimizes μ)

theorem exists_min_on_closed (μ : ProbabilityMeasure ℂ) {C : Set ℂ}
    (hC : IsClosed C) (hCn : C.Nonempty) :
    ∃ z ∈ C, ∀ t ∈ C, objective (μ : Measure ℂ) z ≤ objective (μ : Measure ℂ) t := by
  obtain ⟨x, hx⟩ := hCn
  apply (continuous_objective (μ : Measure ℂ)).continuousOn.exists_isMinOn' hC hx
  apply Filter.Eventually.filter_mono inf_le_left
  exact (objective_coercive (μ : Measure ℂ)).eventually
    (eventually_ge_atTop (objective (μ : Measure ℂ) x))

theorem measurable_center : Measurable center := by
  classical
  apply measurable_of_isClosed
  intro C hC
  by_cases hne : C.Nonempty
  · let : Nonempty C := hne.to_subtype
    let mC (μ : ProbabilityMeasure ℂ) : ℝ :=
      ⨅ n, objective (μ : Measure ℂ) (TopologicalSpace.denseSeq C n).val
    have hmC : Measurable mC := Measurable.iInf fun _n => measurable_objective _
    have he : center ⁻¹' C = {μ | mC μ = minValue μ} := by
      ext μ
      obtain ⟨z, hzC, hz⟩ := exists_min_on_closed μ hC hne
      have hm : mC μ = objective (μ : Measure ℂ) z :=
        denseSeq_inf_eq_min (fun t : C => objective (μ : Measure ℂ) t.val)
          ((continuous_objective _).comp continuous_subtype_val) ⟨z, hzC⟩
          (fun t => hz t.val t.property)
      rw [Set.mem_preimage, Set.mem_ofPred_eq, hm, minValue_eq]
      constructor
      · intro h
        exact le_antisymm (hz _ h) (center_minimizes μ z)
      · intro h
        have hzm : ∀ t, objective (μ : Measure ℂ) z ≤ objective (μ : Measure ℂ) t :=
          fun t => h.trans_le (center_minimizes μ t)
        rwa [center_unique μ hzm] at hzC
    rw [he]
    exact measurableSet_eq_fun hmC measurable_minValue
  · have he : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [he]

theorem kernel_translate (s t v : ℂ) :
    kernel (s + v) (t + v) = kernel s t - kernel (-v) t := by
  have h₁ : s + v - (t + v) = s - t := by abel
  have h₂ : -(t + v) = -v - t := by abel
  simp only [kernel, h₁, h₂]
  ring

theorem objective_translate (μ : ProbabilityMeasure ℂ) (s v : ℂ) :
    objective (Measure.map (fun t => t + v) (μ : Measure ℂ)) (s + v) =
      objective (μ : Measure ℂ) s - objective (μ : Measure ℂ) (-v) := by
  have hm : AEMeasurable (fun t : ℂ => t + v) (μ : Measure ℂ) :=
    (continuous_id.add_const v).aemeasurable
  rw [objective, integral_map hm (continuous_kernel _).aestronglyMeasurable]
  simp only [kernel_translate]
  exact integral_sub (integrable_kernel _ _) (integrable_kernel _ _)

theorem center_translate (μ : ProbabilityMeasure ℂ) (v : ℂ) :
    center (μ.map (measurable_add_const v).aemeasurable) = center μ + v := by
  apply Eq.symm
  apply center_unique
  intro t
  have he : t = (t - v) + v := by abel
  change objective (Measure.map (fun t : ℂ => t + v) (μ : Measure ℂ)) (center μ + v) ≤
    objective (Measure.map (fun t : ℂ => t + v) (μ : Measure ℂ)) t
  rw [objective_translate, he, objective_translate]
  exact sub_le_sub_right (center_minimizes μ (t - v)) _

theorem kernel_orthogonal (O : ℂ ≃ₗᵢ[ℝ] ℂ) (s t : ℂ) :
    kernel (O s) (O t) = kernel s t := by
  simp only [kernel_formula, ← O.map_sub, O.norm_map]

theorem objective_orthogonal (μ : ProbabilityMeasure ℂ) (O : ℂ ≃ₗᵢ[ℝ] ℂ) (s : ℂ) :
    objective (Measure.map O (μ : Measure ℂ)) (O s) = objective (μ : Measure ℂ) s := by
  rw [objective, integral_map O.continuous.aemeasurable
    (continuous_kernel _).aestronglyMeasurable]
  simp only [kernel_orthogonal, objective]

theorem center_orthogonal (μ : ProbabilityMeasure ℂ) (O : ℂ ≃ₗᵢ[ℝ] ℂ) :
    center (μ.map O.continuous.measurable.aemeasurable) = O (center μ) := by
  apply Eq.symm
  apply center_unique
  intro t
  obtain ⟨s, rfl⟩ := O.surjective t
  rw [ProbabilityMeasure.toMeasure_map, objective_orthogonal, objective_orthogonal]
  exact center_minimizes μ s

end EuclideanFiveColor.Location

namespace EuclideanFiveColor.CosetCenter
open ProbabilityTheory

variable {G : Type*} [CommGroup G] [MeasurableSpace G]

namespace Embedding

variable (e : Embedding G)

theorem j_injective : Function.Injective e.j := e.measurableEmbedding.injective

theorem measurable_j : Measurable e.j := e.measurableEmbedding.measurable

theorem mem_ordinary_iff (x : G) : x ∈ e.ordinary ↔ ∃ z : ℂ, e.j z = x := Iff.rfl

theorem measurableSet_ordinary : MeasurableSet (e.ordinary : Set G) :=
  e.measurableEmbedding.measurableSet_range

@[simp] theorem coordinate_j (z : ℂ) : e.coordinate (e.j z) = z :=
  e.j_injective.extend_apply id (fun _ => 0) z

theorem j_coordinate {x : G} (hx : x ∈ e.ordinary) : e.j (e.coordinate x) = x := by
  obtain ⟨z, rfl⟩ := (e.mem_ordinary_iff x).mp hx
  simp

variable [MeasurableMul₂ G] [MeasurableInv G]

theorem measurableSet_coset (z : G) : MeasurableSet (e.coset z) :=
  e.measurableSet_ordinary.preimage (measurable_id.div_const z)

theorem frequencyMeasure_apply (μ : Measure G) (z : G) {s : Set ℂ}
    (hs : MeasurableSet s) :
    e.frequencyMeasure μ z s = μ {d | d / z ∈ e.ordinary ∧ e.coordinate (d / z) ∈ s} := by
  rw [frequencyMeasure, Measure.map_apply
    (show Measurable (fun d : G => e.coordinate (d / z)) from
      e.measurable_coordinate.comp (measurable_id.div_const z)) hs,
    Measure.restrict_apply (show MeasurableSet ((fun d : G => e.coordinate (d / z)) ⁻¹' s) from
      (e.measurable_coordinate.comp (measurable_id.div_const z)) hs)]
  congr 1
  ext d
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, coset]
  exact and_comm

@[simp] theorem frequencyMeasure_univ (μ : Measure G) (z : G) :
    e.frequencyMeasure μ z Set.univ = μ (e.coset z) := by
  rw [e.frequencyMeasure_apply μ z MeasurableSet.univ]
  congr 1
  ext d
  simp [coset]

theorem measurable_frequencyMeasure :
    Measurable (fun p : ProbabilityMeasure G × G => e.frequencyMeasure (p.1 : Measure G) p.2) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm : Measurable (fun p : (ProbabilityMeasure G × G) × G =>
      if p.2 / p.1.2 ∈ e.ordinary ∧ e.coordinate (p.2 / p.1.2) ∈ s
      then (1 : ℝ≥0∞) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact (e.measurableSet_ordinary.preimage
      (measurable_snd.div (measurable_snd.comp measurable_fst))).inter
      (hs.preimage (e.measurable_coordinate.comp
        (measurable_snd.div (measurable_snd.comp measurable_fst))))
  have h := hm.lintegral_kernel_prod_right' (κ := parameterKernel (G := G))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  rw [e.frequencyMeasure_apply _ _ hs]
  have hset : MeasurableSet {d : G | d / p.2 ∈ e.ordinary ∧
      e.coordinate (d / p.2) ∈ s} :=
    (e.measurableSet_ordinary.preimage (measurable_id.div_const p.2)).inter
      (hs.preimage (e.measurable_coordinate.comp (measurable_id.div_const p.2)))
  rw [show parameterKernel p = (p.1 : Measure G) from rfl]
  simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using
    (lintegral_indicator_one (μ := (p.1 : Measure G)) hset).symm

theorem measurable_mass : Measurable (fun p : ProbabilityMeasure G × G =>
    (p.1 : Measure G) (e.coset p.2)) := by
  have h : Measurable (fun p : ProbabilityMeasure G × G =>
      e.frequencyMeasure (p.1 : Measure G) p.2 Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp e.measurable_frequencyMeasure
  simp only [frequencyMeasure_univ] at h
  exact h

theorem frequencyLaw_measure (μ : ProbabilityMeasure G) (z : G) :
    (e.frequencyLaw μ z : Measure ℂ) =
      if (μ : Measure G) (e.coset z) = 0 then Measure.dirac 0 else
      ((μ : Measure G) (e.coset z))⁻¹ • e.frequencyMeasure μ z := by
  split_ifs with h
  · simp [frequencyLaw, h]
  · simp [frequencyLaw, h, ProbabilityTheory.cond, frequencyMeasure]

theorem measurable_frequencyLaw :
    Measurable (fun p : ProbabilityMeasure G × G => e.frequencyLaw p.1 p.2) := by
  have hm : Measurable (fun p : ProbabilityMeasure G × G =>
      (e.frequencyLaw p.1 p.2 : Measure ℂ)) := by
    simp_rw [frequencyLaw_measure]
    apply Measurable.ite (e.measurable_mass (measurableSet_singleton 0)) measurable_const
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    exact e.measurable_mass.inv.mul ((Measure.measurable_coe hs).comp e.measurable_frequencyMeasure)
  exact hm.subtype_mk

theorem coset_mul_j (z : G) (v : ℂ) : e.coset (z * e.j v) = e.coset z := by
  ext d
  have hj : e.j v ∈ e.ordinary := ⟨_, rfl⟩
  constructor
  · intro h
    change d / z ∈ e.ordinary
    convert e.ordinary.mul_mem h hj using 1
    all_goals try with_reducible_and_instances rfl
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  · intro h
    change d / (z * e.j v) ∈ e.ordinary
    convert e.ordinary.div_mem h hj using 1
    all_goals try with_reducible_and_instances rfl
    simp [div_eq_mul_inv, mul_assoc, mul_comm]

theorem coordinate_div_j {d : G} (hd : d ∈ e.ordinary) (v : ℂ) :
    e.coordinate (d / e.j v) = e.coordinate d - v := by
  rw [← e.j_coordinate hd, ← e.j_sub, e.coordinate_j, e.coordinate_j]

theorem frequencyMeasure_shift (μ : Measure G) (z : G) (v : ℂ) :
    e.frequencyMeasure μ (z * e.j v) =
      (e.frequencyMeasure μ z).map (fun t => t + -v) := by
  rw [frequencyMeasure, frequencyMeasure, e.coset_mul_j,
    Measure.map_map (show Measurable (fun t : ℂ => t + -v) from
      measurable_id.add_const (-v))
      (show Measurable (fun d : G => e.coordinate (d / z)) from
        e.measurable_coordinate.comp (measurable_id.div_const z))]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (e.measurableSet_coset z)] with d hd
  change e.coordinate (d / (z * e.j v)) = e.coordinate (d / z) + -v
  rw [div_mul_eq_div_div, e.coordinate_div_j hd, sub_eq_add_neg]

theorem frequencyLaw_shift (μ : ProbabilityMeasure G) (z : G) (v : ℂ)
    (h : (μ : Measure G) (e.coset z) ≠ 0) :
    e.frequencyLaw μ (z * e.j v) =
      (e.frequencyLaw μ z).map (measurable_add_const (-v)).aemeasurable := by
  apply Subtype.ext
  change (e.frequencyLaw μ (z * e.j v) : Measure ℂ) =
    Measure.map (fun t => t + -v) (e.frequencyLaw μ z : Measure ℂ)
  rw [e.frequencyLaw_measure, e.frequencyLaw_measure, e.coset_mul_j]
  simp only [ite_eq_right h]
  rw [Measure.map_smul ((μ : Measure G) (e.coset z))⁻¹ _ (fun point : ℂ => point + -v),
    ← e.frequencyMeasure_shift]

theorem measurable_center :
    Measurable (fun p : ProbabilityMeasure G × G => e.center p.1 p.2) :=
  measurable_snd.mul (e.measurable_j.comp
    (Location.measurable_center.comp e.measurable_frequencyLaw))

theorem center_mem_coset (μ : ProbabilityMeasure G) (z : G) :
    e.center μ z ∈ e.coset z := by
  change z * e.j _ / z ∈ e.ordinary
  rw [mul_div_cancel_left]
  exact ⟨_, rfl⟩

theorem center_mul_j (μ : ProbabilityMeasure G) (z : G) (v : ℂ)
    (h : (μ : Measure G) (e.coset z) ≠ 0) :
    e.center μ (z * e.j v) = e.center μ z := by
  rw [center, e.frequencyLaw_shift μ z v h, Location.center_translate, e.j_add,
    e.j_neg, center]
  simp [mul_assoc, mul_comm]

theorem center_eq_of_mem_coset (μ : ProbabilityMeasure G) {z z' : G}
    (hz : (μ : Measure G) (e.coset z) ≠ 0) (hz' : z' ∈ e.coset z) :
    e.center μ z' = e.center μ z := by
  obtain ⟨v, hv⟩ := (e.mem_ordinary_iff (z' / z)).mp hz'
  have he : z' = z * e.j v := by rw [hv]; simp [div_eq_mul_inv]
  rw [he]
  exact e.center_mul_j μ z v hz

theorem quotient_center (μ : ProbabilityMeasure G) (z : G) :
    (QuotientGroup.mk (e.center μ z) : G ⧸ e.ordinary) = QuotientGroup.mk z :=
  QuotientGroup.eq_iff_div_mem.mpr (e.center_mem_coset μ z)

theorem center_eq_iff (μ : ProbabilityMeasure G) {z z' : G}
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    e.center μ z' = e.center μ z ↔ z' ∈ e.coset z := by
  constructor
  · intro h
    change z' / z ∈ e.ordinary
    apply QuotientGroup.eq_iff_div_mem.mp
    rw [← e.quotient_center μ z', ← e.quotient_center μ z, h]
  · exact e.center_eq_of_mem_coset μ hz

theorem center_mem_ordinary_iff (μ : ProbabilityMeasure G) (z : G) :
    e.center μ z ∈ e.ordinary ↔ z ∈ e.ordinary := by
  rw [← QuotientGroup.eq_one_iff, e.quotient_center, QuotientGroup.eq_one_iff]

theorem preimage_center_singleton (μ : ProbabilityMeasure G) {z : G}
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    (e.center μ) ⁻¹' {e.center μ z} = e.coset z := by
  ext z'
  exact e.center_eq_iff μ hz

theorem measurable_center_fixed (μ : ProbabilityMeasure G) : Measurable (e.center μ) :=
  e.measurable_center.comp (measurable_const.prodMk measurable_id)

variable (T : G ≃* G) (O : ℂ ≃ₗᵢ[ℝ] ℂ)
  (hT : Measurable T) (he : ∀ t : ℂ, T (e.j t) = e.j (O t))

include he

theorem equiv_mem_ordinary_iff (d : G) : T d ∈ e.ordinary ↔ d ∈ e.ordinary := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨Multiplicative.ofAdd (O.symm (Multiplicative.toAdd t)), ?_⟩
    change e.j (O.symm _) = d
    apply T.injective
    rw [he, O.apply_symm_apply]
    exact ht
  · rintro ⟨t, rfl⟩
    exact (e.mem_ordinary_iff _).mpr ⟨O (Multiplicative.toAdd t), (he _).symm⟩

theorem preimage_coset_equiv (z : G) : T ⁻¹' e.coset (T z) = e.coset z := by
  ext d
  change T d / T z ∈ e.ordinary ↔ d / z ∈ e.ordinary
  rw [← T.map_div]
  exact e.equiv_mem_ordinary_iff T O he _

theorem coordinate_equiv {d : G} (hd : d ∈ e.ordinary) :
    e.coordinate (T d) = O (e.coordinate d) := by
  obtain ⟨t, rfl⟩ := (e.mem_ordinary_iff d).mp hd
  rw [he, e.coordinate_j, e.coordinate_j]

include hT in
theorem frequencyMeasure_equiv (μ : Measure G) (z : G) :
    e.frequencyMeasure (μ.map T) (T z) = (e.frequencyMeasure μ z).map O := by
  rw [frequencyMeasure, Measure.restrict_map hT (e.measurableSet_coset _),
    e.preimage_coset_equiv T O he,
    Measure.map_map (show Measurable (fun d : G => e.coordinate (d / T z)) from
      e.measurable_coordinate.comp (measurable_id.div_const (T z))) hT,
    frequencyMeasure,
    Measure.map_map O.continuous.measurable
      (show Measurable (fun d : G => e.coordinate (d / z)) from
        e.measurable_coordinate.comp (measurable_id.div_const z))]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (e.measurableSet_coset z)] with d hd
  change e.coordinate (T d / T z) = O (e.coordinate (d / z))
  rw [← T.map_div]
  exact e.coordinate_equiv T O he hd

include hT in
theorem frequencyLaw_equiv (μ : ProbabilityMeasure G) (z : G)
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    e.frequencyLaw (μ.map hT.aemeasurable) (T z) =
      (e.frequencyLaw μ z).map O.continuous.measurable.aemeasurable := by
  apply Subtype.ext
  change (e.frequencyLaw (μ.map hT.aemeasurable) (T z) : Measure ℂ) =
    Measure.map O (e.frequencyLaw μ z : Measure ℂ)
  rw [e.frequencyLaw_measure, e.frequencyLaw_measure, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hT (e.measurableSet_coset _), e.preimage_coset_equiv T O he,
    ]
  simp only [ite_eq_right hz]
  rw [Measure.map_smul,
    e.frequencyMeasure_equiv T O hT he]

include hT in
theorem center_equivariant (μ : ProbabilityMeasure G) (z : G)
    (hz : (μ : Measure G) (e.coset z) ≠ 0) :
    e.center (μ.map hT.aemeasurable) (T z) = T (e.center μ z) := by
  rw [center, e.frequencyLaw_equiv T O hT he μ z hz, Location.center_orthogonal,
    center, T.map_mul, he]

end Embedding
end EuclideanFiveColor.CosetCenter

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Basic
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.K_countable _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualPolishSpace _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral

/-- The group-theoretic step behind the zero-mass coset argument. -/
theorem finite_image_trivial {G H : Type*} [Group G] [Group H] [Finite H]
    [RootableBy G ℕ] (f : G →* H) (g : G) : f g = 1 := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨x, hx⟩ := RootableBy.surjective_pow G ℕ (Fintype.card_ne_zero : Fintype.card H ≠ 0) g
  rw [← hx, map_pow, pow_card_eq_one]

/-- A divisible group cannot act nontrivially on a finite orbit. -/
theorem fixed_of_finite_orbit {G X : Type*} [Group G] [MulAction G X]
    [RootableBy G ℕ] (x : X) (hf : (MulAction.orbit G x).Finite) (g : G) :
    g • x = x := by
  let := hf.fintype
  have h := finite_image_trivial (MulAction.toPermHom G (MulAction.orbit G x)) g
  have h' := congrArg (fun p : Equiv.Perm (MulAction.orbit G x) =>
    (p ⟨x, MulAction.mem_orbit_self x⟩).val) h
  exact h'

theorem scalar_mem_C_iff {a : E} (ha : a ≠ 0) (d : D) : scalar a d ∈ C ↔ d ∈ C := by
  constructor
  · intro h
    have h' := scalar_mem_C a⁻¹ h
    simpa [ha] using h'
  · exact scalar_mem_C a

/-- Positive fibers of an equivariant partition have finite orbit. This uses
only finite measure and measurability of the fibers, not a measurable quotient. -/
theorem fixed_of_positive_fiber {G X Y : Type*} [Group G] [RootableBy G ℕ]
    [MulAction G X] [MulAction G Y] [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (π : X → Y) (heq : ∀ (g : G) (x : X), π (g • x) = g • π x)
    (hmeas : ∀ y, MeasurableSet (π ⁻¹' {y}))
    (hinv : ∀ g : G, MeasureTheory.MeasurePreserving (fun x : X => g • x) μ μ)
    (y : Y) (hpos : 0 < μ (π ⁻¹' {y})) (g : G) : g • y = y := by
  classical
  let A (z : MulAction.orbit G y) : Set X := π ⁻¹' {z.val}
  have hm (z : MulAction.orbit G y) : μ (A z) = μ (π ⁻¹' {y}) := by
    obtain ⟨g, hg⟩ := z.property
    have hs : (fun x : X => g • x) ⁻¹' A z = π ⁻¹' {y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, A, heq, ← hg]
      constructor
      · intro h
        have h' := congrArg (fun z : Y => g⁻¹ • z) h
        simpa only [inv_smul_smul] using h'
      · exact congrArg (fun z : Y => g • z)
    rw [← (hinv g).measure_preimage ((hmeas z.val).nullMeasurableSet), hs]
  have hd : Pairwise (Function.onFun Disjoint A) := by
    intro z w hzw
    change Disjoint (A z) (A w)
    rw [Set.disjoint_left]
    intro x hz hw
    exact hzw (Subtype.ext (hz.symm.trans hw))
  have hf := MeasureTheory.Measure.finite_const_le_meas_of_disjoint_iUnion μ hpos (As := A)
    (fun z => hmeas z.val) hd (MeasureTheory.measure_ne_top μ _)
  have hu : {z : MulAction.orbit G y | μ (π ⁻¹' {y}) ≤ μ (A z)} = Set.univ := by
    ext z
    simp [hm]
  rw [hu] at hf
  let := Set.finite_univ_iff.mp hf
  exact fixed_of_finite_orbit y (Set.toFinite _) g

theorem measurableSet_coset (q : Cosets) :
    MeasurableSet ((QuotientGroup.mk : D → Cosets) ⁻¹' {q}) := by
  induction q using QuotientGroup.induction_on with
  | H d =>
    have h : (QuotientGroup.mk : D → Cosets) ⁻¹' {QuotientGroup.mk d} =
        (fun x => x / d) ⁻¹' (C : Set D) := by
      ext x
      exact QuotientGroup.eq_iff_div_mem
    rw [h]
    exact measurableSet_C.preimage (continuous_id.div_const d).measurable

theorem coset_fixed_minusOne (q : Cosets) (h : minusOne • q = q) : q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H d =>
    change QuotientGroup.mk (scalar (-1) d) = QuotientGroup.mk d at h
    have hm : scalar ((-1 : E) - 1) d ∈ C := by
      rw [scalar_sub, scalar_one]
      exact QuotientGroup.eq_iff_div_mem.mp h
    exact (QuotientGroup.eq_one_iff d).mpr ((scalar_mem_C_iff (by norm_num) d).mp hm)

theorem wild_coset_null (ν : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsWild ν) (q : Cosets) :
    ν ((QuotientGroup.mk : D → Cosets) ⁻¹' {q}) = 0 := by
  by_contra hn
  have hp : 0 < ν ((QuotientGroup.mk : D → Cosets) ⁻¹' {q}) := pos_iff_ne_zero.mpr hn
  have hfix := fixed_of_positive_fiber ν (QuotientGroup.mk : D → Cosets)
    quotient_equivariant measurableSet_coset hν.1 q hp minusOne
  have hq := coset_fixed_minusOne q hfix
  subst q
  have hs : (QuotientGroup.mk : D → Cosets) ⁻¹' {1} = C := by
    ext d
    exact QuotientGroup.eq_one_iff d
  rw [hs, hν.2] at hn
  exact hn rfl

theorem wild_div_mem_null (ν : MeasureTheory.Measure D) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsWild ν) (d : D) : ν {x | x / d ∈ C} = 0 := by
  convert wild_coset_null ν hν (QuotientGroup.mk d) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  exact (QuotientGroup.eq_iff_div_mem (N := C) (x := x) (y := d)).symm

theorem wild_independent_difference (ν : MeasureTheory.Measure D)
    [MeasureTheory.IsProbabilityMeasure ν] (hν : IsWild ν) :
    (ν.prod ν) {p : D × D | p.1 / p.2 ∈ C} = 0 := by
  have hm : MeasurableSet {p : D × D | p.1 / p.2 ∈ C} :=
    measurableSet_C.preimage (continuous_fst.div' continuous_snd).measurable
  rw [MeasureTheory.Measure.prod_apply_symm hm]
  have h (d : D) : ν ((fun x => (x, d)) ⁻¹' {p : D × D | p.1 / p.2 ∈ C}) = 0 :=
    wild_div_mem_null ν hν d
  simp_rw [h]
  simp

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_RelativeCenters
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.K_countable _root_.OAI.PlaneFiveColor.Spectral.dualPolishSpace _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

open MeasureTheory
open scoped ENNReal

namespace EuclideanFiveColor.UniformFibers

variable {X Q : Type*} [MeasurableSpace X]

 theorem finite_uniform_fibers (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Q) (hm : ∀ y : Q, MeasurableSet (q ⁻¹' {y}))
    {a : ℝ≥0∞} (ha : 0 < a)
    (hs : ∀ᵐ x ∂μ, μ (q ⁻¹' {q x}) = a) :
    ∃ S : Finset Q, S.Nonempty ∧
      (∀ y ∈ S, μ (q ⁻¹' {y}) = a) ∧
      (∀ᵐ x ∂μ, q x ∈ S) ∧ (S.card : ℝ≥0∞) * a = 1 := by
  classical
  have hd : Pairwise (Function.onFun Disjoint (fun y : Q => q ⁻¹' {y})) := by
    intro y z hyz
    change Disjoint (q ⁻¹' {y}) (q ⁻¹' {z})
    rw [Set.disjoint_left]
    intro x hx hy
    exact hyz (hx.symm.trans hy)
  have hf := Measure.finite_const_le_meas_of_disjoint_iUnion μ ha hm hd (measure_ne_top μ _)
  have hf' : {y : Q | μ (q ⁻¹' {y}) = a}.Finite :=
    hf.subset (fun _ h => le_of_eq h.symm)
  let S := hf'.toFinset
  have hS (y : Q) : y ∈ S ↔ μ (q ⁻¹' {y}) = a := hf'.mem_toFinset
  have hsample : ∀ᵐ x ∂μ, q x ∈ S := hs.mono fun x hx => (hS _).mpr hx
  have hcover : (⋃ y ∈ S, q ⁻¹' {y}) =ᵐ[μ] Set.univ := by
    filter_upwards [hsample] with x hx
    have hmem : x ∈ ⋃ y ∈ S, q ⁻¹' {y} :=
      Set.mem_iUnion.mpr ⟨q x, Set.mem_iUnion.mpr ⟨hx, rfl⟩⟩
    exact propext (iff_of_true hmem (Set.mem_univ x))
  have hsum : (S.card : ℝ≥0∞) * a = 1 := by
    have h := measure_congr hcover
    rw [measure_biUnion_finset (fun _ _ _ _ h => hd h) (fun y _ => hm y),
      measure_univ] at h
    calc
      (S.card : ℝ≥0∞) * a = ∑ _y ∈ S, a := by simp
      _ = ∑ y ∈ S, μ (q ⁻¹' {y}) := Finset.sum_congr rfl fun y hy => ((hS y).mp hy).symm
      _ = 1 := h
  refine ⟨S, ?_, (fun y hy => (hS y).mp hy), hsample, hsum⟩
  by_contra h
  have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simp [hS0] at hsum

end EuclideanFiveColor.UniformFibers

namespace EuclideanFiveColor.CosetCenter.Embedding
open MeasureTheory
open scoped ENNReal
variable {G : Type*} [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSingletonClass G]
  (e : CosetCenter.Embedding G)

/-- The conditional center law has finitely many, equally weighted atoms.
The original cosets need not form a standard Borel quotient. -/
theorem finite_uniform_centers (μ : ProbabilityMeasure G) {a : ℝ≥0∞}
    (ha : 0 < a) (hs : ∀ᵐ z ∂(μ : Measure G), (μ : Measure G) (e.coset z) = a) :
    ∃ S : Finset G, S.Nonempty ∧
      (∀ b ∈ S, (μ : Measure G) ((e.center μ) ⁻¹' {b}) = a) ∧
      (∀ᵐ z ∂(μ : Measure G), e.center μ z ∈ S) ∧
      (S.card : ℝ≥0∞) * a = 1 := by
  apply UniformFibers.finite_uniform_fibers (μ : Measure G) (e.center μ)
    (fun b => e.measurable_center_fixed μ (measurableSet_singleton b)) ha
  filter_upwards [hs] with z hz
  rw [e.preimage_center_singleton μ (by rw [hz]; exact ha.ne'), hz]

end EuclideanFiveColor.CosetCenter.Embedding

namespace EuclideanFiveColor.ErgodicSupport
open MeasureTheory Filter
variable {K X V : Type*} [SMul K X] [MeasurableSpace X]
  {μ : Measure X} [ErgodicSMul K X μ] [MeasurableSpace V]
  [MeasurableSpace.CountablySeparated V] [Nonempty V]

/-- The invariant-function consequence of group-action ergodicity,
with an individual almost-everywhere identity for each group element. -/
theorem ae_eq_const_of_invariant {f : X → V} (hf : Measurable f)
    (hi : ∀ k : K, ∀ᵐ x ∂μ, f (k • x) = f x) :
    ∃ v : V, f =ᵐ[μ] (fun _ => v) := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro A hA
  have h := ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq (G := K)
    (hf hA) (fun k => (hi k).mono (fun x hx => by
      exact propext (show f (k • x) ∈ A ↔ f x ∈ A by rw [hx])))
  exact eventuallyConst_set.mp h

end EuclideanFiveColor.ErgodicSupport

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.KernelSupport

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

lemma compProd_map_base (ν : Measure Y) [SFinite ν] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] (R : Y ≃ᵐ Y) :
    (ν.map R) ⊗ₘ (κ.comap R.symm R.symm.measurable) =
      (ν ⊗ₘ κ).map (Prod.map R id) := by
  ext s hs
  rw [Measure.compProd_apply hs,
    Measure.map_apply (R.measurable.prodMap measurable_id) hs,
    Measure.compProd_apply ((R.measurable.prodMap measurable_id) hs),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) R.measurable]
  apply lintegral_congr
  intro y
  simp only [Kernel.comap_apply, R.symm_apply_apply]
  rfl

lemma condDistrib_comp_equiv [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Z) (p : X → Y) (hf : Measurable f) (hp : Measurable p)
    (R : Y ≃ᵐ Y) :
    condDistrib f (R ∘ p) μ =ᵐ[μ.map (R ∘ p)]
      (condDistrib f p μ).comap R.symm R.symm.measurable := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (R.measurable.comp hp) hf
  rw [← Measure.map_map R.measurable hp, compProd_map_base,
    compProd_map_condDistrib hf.aemeasurable,
    Measure.map_map (R.measurable.prodMap measurable_id) (hp.prodMk hf)]
  rfl

/-- Changing both coordinates of a conditional law by invertible measurable
maps commutes with conditional sampling. -/
lemma condDistrib_equivariant [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → Z) (p : X → Y) (hf : Measurable f) (hp : Measurable p)
    (S : X ≃ᵐ X) (R : Y ≃ᵐ Y) (T : Z → Z) (hT : Measurable T)
    (hS : MeasurePreserving S μ μ)
    (hRp : p ∘ S =ᵐ[μ] R ∘ p) (hTf : f ∘ S =ᵐ[μ] T ∘ f) :
    ∀ᵐ y ∂μ.map p, condDistrib f p μ (R y) = (condDistrib f p μ y).map T := by
  have hR : (μ.map p).map R = μ.map p := by
    rw [Measure.map_map R.measurable hp, ← Measure.map_congr hRp,
      ← Measure.map_map hp S.measurable, hS.map_eq]
  have hRS : μ.map (p ∘ S) = μ.map p := by
    rw [← Measure.map_map hp S.measurable, hS.map_eq]
  have hm := condDistrib_map (X := p) (Y := f) (ν := μ) (f := S)
    (hp.aemeasurable) (hf.aemeasurable) S.measurable.aemeasurable
  simp only [hS.map_eq, hRS] at hm
  rw [condDistrib_congr hTf hRp] at hm
  have hc := condDistrib_comp_equiv μ (T ∘ f) p (hT.comp hf) hp R
  have hh : μ.map (R ∘ p) = μ.map p := by
    rw [← Measure.map_map R.measurable hp, hR]
  rw [hh] at hc
  have he := condDistrib_comp (μ := μ) (mβ := inferInstance) p hf.aemeasurable hT
  have hcomp : ∀ᵐ y ∂μ.map p,
      condDistrib f p μ y = (condDistrib f p μ (R.symm y)).map T := by
    have he' : ∀ᵐ y ∂μ.map p,
        condDistrib (T ∘ f) p μ (R.symm y) =
          (condDistrib f p μ (R.symm y)).map T := by
      have hRinv : MeasurePreserving R.symm (μ.map p) (μ.map p) := by
        refine ⟨R.symm.measurable, ?_⟩
        calc
          (μ.map p).map R.symm = ((μ.map p).map R).map R.symm := by rw [hR]
          _ = μ.map p := R.map_symm_map
      exact hRinv.quasiMeasurePreserving.ae <| he.mono fun y hy => by
        simpa only [Kernel.map_apply _ hT] using hy
    filter_upwards [hm, hc, he'] with y h₁ h₂ h₃
    simpa only [Kernel.comap_apply] using h₁.trans (h₂.trans h₃)
  have hRpres : MeasurePreserving R (μ.map p) (μ.map p) := ⟨R.measurable, hR⟩
  have hfinal := hRpres.quasiMeasurePreserving.ae hcomp
  filter_upwards [hfinal] with y hy
  simpa only [R.symm_apply_apply] using hy

end EuclideanFiveColor.KernelSupport

namespace EuclideanFiveColor.RelativeCenters
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Y G : Type*} [MeasurableSpace Y] [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]
  (e : CosetCenter.Embedding G)

omit [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma measurable_probabilityKernel (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measurable (probabilityKernel κ) := κ.measurable.subtype_mk

lemma measurable_cosetMass (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measurable (cosetMass e κ) :=
  e.measurable_mass.comp ((measurable_probabilityKernel κ).comp measurable_fst |>.prodMk
    measurable_snd)

lemma differenceLaw_ordinary (ν : Measure Y) [SFinite ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] :
    differenceLaw ν κ e.ordinary = ∫⁻ p : Y × G, cosetMass e κ p ∂ν ⊗ₘ κ := by
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) :=
    measurable_fst.div measurable_snd
  rw [differenceLaw, Measure.map_apply hdiv
    e.measurableSet_ordinary,
    Measure.bind_apply (hdiv e.measurableSet_ordinary)
      (κ ×ₖ κ).aemeasurable,
    Measure.lintegral_compProd (measurable_cosetMass e κ)]
  apply lintegral_congr
  intro y
  rw [Kernel.prod_apply,
    Measure.prod_apply_symm (hdiv e.measurableSet_ordinary)]
  rfl

variable {X : Type*} [MeasurableSpace X]

lemma sampledMass_integral [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    differenceLaw (μ.map p) (condDistrib d p μ) e.ordinary =
      ∫⁻ x, cosetMass e (condDistrib d p μ) (p x, d x) ∂μ := by
  rw [differenceLaw_ordinary, compProd_map_condDistrib hd.aemeasurable,
    lintegral_map (measurable_cosetMass e _) (hp.prodMk hd)]

/-- Positive relative mass and ergodicity force a fixed positive mass for almost
all sampled cosets. The finite-center conclusion follows without a quotient
measurable space for the ordinary-character subgroup. -/
theorem positive_mass_finite_centers [StandardBorelSpace G]
    [MeasurableSingletonClass G]
    {K : Type*} [SMul K X]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hi : ∀ k : K, ∀ᵐ x ∂μ,
      cosetMass e (condDistrib d p μ) (p (k • x), d (k • x)) =
        cosetMass e (condDistrib d p μ) (p x, d x))
    (hpos : 0 < differenceLaw (μ.map p) (condDistrib d p μ) e.ordinary) :
    ∃ a : ℝ≥0∞, 0 < a ∧
      (∀ᵐ x ∂μ, cosetMass e (condDistrib d p μ) (p x, d x) = a) ∧
      ∀ᵐ y ∂μ.map p, ∃ S : Finset G, S.Nonempty ∧
        (∀ b ∈ S, condDistrib d p μ y
          ((e.center (probabilityKernel (condDistrib d p μ) y)) ⁻¹' {b}) = a) ∧
        (∀ᵐ z ∂condDistrib d p μ y,
          e.center (probabilityKernel (condDistrib d p μ) y) z ∈ S) ∧
        (S.card : ℝ≥0∞) * a = 1 := by
  have hm : Measurable (fun x => cosetMass e (condDistrib d p μ) (p x, d x)) :=
    (measurable_cosetMass e (condDistrib d p μ)).comp (hp.prodMk hd)
  obtain ⟨a, ha⟩ := ErgodicSupport.ae_eq_const_of_invariant hm hi
  have hapos : 0 < a := by
    rw [sampledMass_integral e μ d p hd hp, lintegral_congr_ae ha] at hpos
    simpa using hpos
  refine ⟨a, hapos, ha, ?_⟩
  have hpair : ∀ᵐ q ∂(μ.map p) ⊗ₘ condDistrib d p μ,
      cosetMass e (condDistrib d p μ) q = a := by
    rw [compProd_map_condDistrib hd.aemeasurable]
    exact (ae_map_iff (hp.prodMk hd).aemeasurable
      (measurableSet_eq_fun (measurable_cosetMass e _) measurable_const)).mpr ha
  have hany := Measure.ae_ae_of_ae_compProd hpair
  filter_upwards [hany] with y hy
  exact e.finite_uniform_centers (probabilityKernel (condDistrib d p μ) y) hapos hy

section Actions
variable {K : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MulDistribMulAction K G]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K G]
  [StandardBorelSpace G]

lemma sampledMass_invariant
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hC : ∀ (k : K) (z : G), k • z ∈ e.ordinary ↔ z ∈ e.ordinary)
    (k : K) :
    ∀ᵐ x ∂μ,
      cosetMass e (condDistrib d p μ) (p (k • x), d (k • x)) =
        cosetMass e (condDistrib d p μ) (p x, d x) := by
  have heq := KernelSupport.condDistrib_equivariant μ d p hd hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun z : G => k • z)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hde k)
  have hxeq := ae_of_ae_map hp.aemeasurable heq
  filter_upwards [hxeq, hde k, hpe k] with x hx hd' hp'
  change condDistrib d p μ (p (k • x)) (e.coset (d (k • x))) =
    condDistrib d p μ (p x) (e.coset (d x))
  change condDistrib d p μ (k • p x) = _ at hx
  rw [hp', hd', hx, Measure.map_apply (measurable_const_smul k) (e.measurableSet_coset _)]
  congr 1
  ext z
  change k • z / k • d x ∈ e.ordinary ↔ z / d x ∈ e.ordinary
  rw [← smul_div']
  exact hC k _

end Actions

lemma measurable_centerMap [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    Measurable (centerMap e μ d p) :=
  e.measurable_center.comp (((measurable_probabilityKernel _).comp hp).prodMk hd)

lemma centerMap_mem_ordinary_iff [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ] (d : X → G) (p : X → Y) (x : X) :
    centerMap e μ d p x ∈ e.ordinary ↔ d x ∈ e.ordinary :=
  e.center_mem_ordinary_iff _ _

lemma centerMap_law_ordinary [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    (μ.map (centerMap e μ d p)) e.ordinary = (μ.map d) e.ordinary := by
  rw [Measure.map_apply (measurable_centerMap e μ d p hd hp) e.measurableSet_ordinary,
    Measure.map_apply hd e.measurableSet_ordinary]
  congr 1
  ext x
  exact centerMap_mem_ordinary_iff e μ d p x

section CenterActions
variable {K : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MulDistribMulAction K G]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K G]
  [StandardBorelSpace G]

lemma centerMap_equivariant
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (O : K → ℂ ≃ₗᵢ[ℝ] ℂ)
    (he : ∀ (k : K) (t : ℂ), k • e.j t = e.j (O k t))
    (ha : ∀ᵐ x ∂μ, cosetMass e (condDistrib d p μ) (p x, d x) ≠ 0)
    (k : K) :
    ∀ᵐ x ∂μ, centerMap e μ d p (k • x) = k • centerMap e μ d p x := by
  have hk := KernelSupport.condDistrib_equivariant μ d p hd hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun z : G => k • z)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hde k)
  have hxk := ae_of_ae_map hp.aemeasurable hk
  filter_upwards [hxk, hde k, hpe k, ha] with x hx hd' hp' ha'
  have hprob : probabilityKernel (condDistrib d p μ) (k • p x) =
      (probabilityKernel (condDistrib d p μ) (p x)).map
        (measurable_const_smul k).aemeasurable := by
    apply Subtype.ext
    exact hx
  change e.center (probabilityKernel (condDistrib d p μ) (p (k • x))) (d (k • x)) = _
  rw [hp', hd', hprob]
  exact e.center_equivariant (MulDistribMulAction.toMulEquiv G k) (O k)
    (measurable_const_smul k) (he k) _ _ ha'

end CenterActions

section ConditionalLaw
variable {H : Type*} [MeasurableSpace H]

omit [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma dependentMapKernel_apply (κ : Kernel Y G) [IsMarkovKernel κ]
    (f : Y × G → H) (hf : Measurable f) (y : Y) :
    ((Kernel.id ×ₖ κ).map f) y = (κ y).map (fun z => f (y, z)) := by
  rw [Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

omit [CommGroup G] [MeasurableMul₂ G] [MeasurableInv G] in
lemma compProd_dependentMap (ν : Measure Y) [SFinite ν]
    (κ : Kernel Y G) [IsMarkovKernel κ]
    (f : Y × G → H) (hf : Measurable f) :
    ν ⊗ₘ ((Kernel.id ×ₖ κ).map f) =
      (ν ⊗ₘ κ).map (fun q : Y × G => (q.1, f q)) := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply (measurable_fst.prodMk hf) hs,
    Measure.compProd_apply ((measurable_fst.prodMk hf) hs)]
  apply lintegral_congr
  intro y
  have hfy : Measurable (fun z : G => f (y, z)) := hf.comp measurable_prodMk_left
  rw [dependentMapKernel_apply κ f hf y,
    Measure.map_apply hfy (measurable_prodMk_left hs)]
  rfl

lemma measurable_fiberCenter (κ : Kernel Y G) [IsMarkovKernel κ] :
    Measurable (fun q : Y × G => e.center (probabilityKernel κ q.1) q.2) :=
  e.measurable_center.comp (((measurable_probabilityKernel κ).comp measurable_fst).prodMk
    measurable_snd)

instance centerKernel_markov (κ : Kernel Y G) [IsMarkovKernel κ] :
    IsMarkovKernel (centerKernel e κ) :=
  Kernel.IsMarkovKernel.map _ (measurable_fiberCenter e κ)

lemma centerKernel_apply (κ : Kernel Y G) [IsMarkovKernel κ] (y : Y) :
    centerKernel e κ y = (κ y).map (e.center (probabilityKernel κ y)) :=
  dependentMapKernel_apply κ _ (measurable_fiberCenter e κ) y

lemma condDistrib_centerMap [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    condDistrib (centerMap e μ d p) p μ =ᵐ[μ.map p]
      centerKernel e (condDistrib d p μ) := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hp (measurable_centerMap e μ d p hd hp)
  rw [centerKernel, compProd_dependentMap (μ.map p) (condDistrib d p μ) _
    (measurable_fiberCenter e _), compProd_map_condDistrib hd.aemeasurable,
    Measure.map_map (measurable_fst.prodMk (measurable_fiberCenter e _)) (hp.prodMk hd)]
  rfl

end ConditionalLaw

lemma centerKernel_comp_map [StandardBorelSpace G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p) :
    centerKernel e (condDistrib d p μ) ∘ₘ (μ.map p) = μ.map (centerMap e μ d p) := by
  rw [← Measure.comp_congr (condDistrib_centerMap e μ d p hd hp)]
  exact condDistrib_comp_map hp.aemeasurable (measurable_centerMap e μ d p hd hp).aemeasurable

variable {K : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MulDistribMulAction K G]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K G]
  [StandardBorelSpace G] [MeasurableSingletonClass G]

theorem finite_center_reduction
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → G) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (O : K → ℂ ≃ₗᵢ[ℝ] ℂ)
    (he : ∀ (k : K) (t : ℂ), k • e.j t = e.j (O k t))
    (hwild : (μ.map d) e.ordinary = 0)
    (hpos : 0 < differenceLaw (μ.map p) (condDistrib d p μ) e.ordinary) :
    Measurable (centerMap e μ d p) ∧
    (∀ k : K, ∀ᵐ x ∂μ, centerMap e μ d p (k • x) = k • centerMap e μ d p x) ∧
    (μ.map (centerMap e μ d p)) e.ordinary = 0 ∧
    ∃ a : ℝ≥0∞, 0 < a ∧
      ∀ᵐ y ∂μ.map p, ∃ S : Finset G, S.Nonempty ∧
        (∀ b ∈ S, condDistrib (centerMap e μ d p) p μ y {b} = a) ∧
        (∀ᵐ b ∂condDistrib (centerMap e μ d p) p μ y, b ∈ S) ∧
        (S.card : ℝ≥0∞) * a = 1 ∧
        (∀ b ∈ S, b ∉ e.ordinary) := by
  have hC (k : K) (z : G) : k • z ∈ e.ordinary ↔ z ∈ e.ordinary :=
    e.equiv_mem_ordinary_iff (MulDistribMulAction.toMulEquiv G k) (O k) (he k) z
  obtain ⟨a, ha, hmass, hfib⟩ := positive_mass_finite_centers e μ d p hd hp
    (sampledMass_invariant e μ d p hd hp hde hpe hC) hpos
  have ha' : ∀ᵐ x ∂μ, cosetMass e (condDistrib d p μ) (p x, d x) ≠ 0 :=
    hmass.mono fun _ h => by rw [h]; exact ha.ne'
  have hbzero : (μ.map (centerMap e μ d p)) e.ordinary = 0 := by
    rw [centerMap_law_ordinary e μ d p hd hp, hwild]
  refine ⟨measurable_centerMap e μ d p hd hp,
    centerMap_equivariant e μ d p hd hp hde hpe O he ha', hbzero, a, ha, ?_⟩
  have hz : ∀ᵐ y ∂μ.map p, centerKernel e (condDistrib d p μ) y e.ordinary = 0 := by
    rw [← centerKernel_comp_map e μ d p hd hp,
      Measure.bind_apply e.measurableSet_ordinary (centerKernel e _).aemeasurable] at hbzero
    exact (lintegral_eq_zero_iff ((centerKernel e _).measurable_coe e.measurableSet_ordinary)).mp
      hbzero
  have hcd := condDistrib_centerMap e μ d p hd hp
  filter_upwards [hfib, hz, hcd] with y hy hyzero hycd
  obtain ⟨S, hS, hSa, hSm, hSc⟩ := hy
  have hSa' (b : G) (hb : b ∈ S) : centerKernel e (condDistrib d p μ) y {b} = a := by
    rw [centerKernel_apply, Measure.map_apply (e.measurable_center_fixed _)
      (measurableSet_singleton b)]
    exact hSa b hb
  refine ⟨S, hS, ?_, ?_, hSc, ?_⟩
  · intro b hb
    rw [hycd]
    exact hSa' b hb
  · rw [hycd, centerKernel_apply]
    exact (ae_map_iff (e.measurable_center_fixed _).aemeasurable S.measurableSet).mpr hSm
  · intro b hb hbC
    have hle : centerKernel e (condDistrib d p μ) y {b} ≤
        centerKernel e (condDistrib d p μ) y e.ordinary :=
      measure_mono (Set.singleton_subset_iff.mpr hbC)
    rw [hSa' b hb, hyzero] at hle
    exact (not_le_of_gt ha) hle

end EuclideanFiveColor.RelativeCenters

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor.RelativeCenters

theorem action_ordinaryEmbedding (u : K) (t : ℂ) :
    u • ordinaryEmbedding.j t = ordinaryEmbedding.j (frequencyRotation u t) :=
  scalar_j (kCoeff u) t

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction K X] [MulAction K Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

theorem wild_map_of_equivariant (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure K X μ] (b : X → D) (hb : Measurable b)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (hC : (μ.map b) C = 0) : IsWild (μ.map b) := by
  refine ⟨fun k => ⟨measurable_const_smul k, ?_⟩, hC⟩
  rw [Measure.map_map (measurable_const_smul k) hb]
  calc
    μ.map ((fun z : D => k • z) ∘ b) = μ.map (b ∘ (fun x : X => k • x)) :=
      Measure.map_congr ((hbe k).mono fun _ hx => hx.symm)
    _ = (μ.map (fun x : X => k • x)).map b :=
      (Measure.map_map hb (measurable_const_smul k)).symm
    _ = μ.map b := by rw [measurePreserving_smul k μ |>.map_eq]

theorem exact_finite_center_reduction
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → D) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hwild : IsWild (μ.map d))
    (hpos : 0 < differenceLaw (μ.map p) (condDistrib d p μ) C) :
    ∃ b : X → D, Measurable b ∧
      (∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x) ∧
      IsWild (μ.map b) ∧
      ∃ a : ℝ≥0∞, 0 < a ∧
        ∀ᵐ y ∂μ.map p, ∃ S : Finset D, S.Nonempty ∧
          (∀ c ∈ S, condDistrib b p μ y {c} = a) ∧
          (∀ᵐ c ∂condDistrib b p μ y, c ∈ S) ∧
          (S.card : ℝ≥0∞) * a = 1 ∧
          (∀ c ∈ S, c ∉ C) := by
  obtain ⟨hbm, hbe, hbw, hfin⟩ := finite_center_reduction ordinaryEmbedding μ d p hd hp
    hde hpe frequencyRotation action_ordinaryEmbedding hwild.2 hpos
  exact ⟨centerMap ordinaryEmbedding μ d p, hbm, hbe,
    wild_map_of_equivariant μ _ hbm hbe hbw, hfin⟩

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_PhaseEncoding
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators

open scoped BigOperators
open Polynomial
namespace EuclideanFiveColor.PhaseEncoding

section

theorem elem_eq_sum {m : ℕ} (z : Fin m → Circle) (n : ℕ) :
    elem z n = ∑ t ∈ (Finset.univ : Finset (Fin m)).powersetCard n,
      ∏ i ∈ t, (z i : ℂ) :=
  Finset.esymm_map_val _ _ n

theorem continuous_encoding {m : ℕ} : Continuous (encoding (m := m)) := by
  apply continuous_pi
  intro i
  simp only [encoding, elem_eq_sum]
  fun_prop

open scoped BigOperators

lemma measurable_fromPowers {Y : Type*} [MeasurableSpace Y] (p : Y → ℕ → ℂ)
    (hp : ∀ n, Measurable (fun y => p y n)) (n : ℕ) :
    Measurable (fun y => fromPowers (p y) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp only [fromPowers]; exact measurable_const
    | succ k =>
      simp only [fromPowers]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro i _
      exact (Measurable.const_mul (ih i i.isLt) _).mul (hp _)

lemma newton_elem {m : ℕ} (z : Fin m → Circle) (k : ℕ) :
    (k : ℂ) * elem z k = (-1) ^ (k + 1) *
      ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * elem z a.1 * (∑ i, (z i : ℂ) ^ a.2) := by
  have h := congrArg (MvPolynomial.aeval (fun i => (z i : ℂ)))
    (MvPolynomial.mul_esymm_eq_sum (Fin m) ℂ k)
  simpa only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X,
    elem, phases] using h

lemma filtered_antidiagonal_sum (f : ℕ → ℕ → ℂ) (k : ℕ) :
    (∑ a ∈ (Finset.HasAntidiagonal.antidiagonal (k+1)).filter (fun a => a.1 < k+1), f a.1 a.2) =
      ∑ i : Fin (k+1), f i (k+1-i) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f i (k+1-i)) (k+1), Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [lt_self_iff_false, ↓reduceIte, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

theorem fromPowers_eq_elem {m : ℕ} (z : Fin m → Circle) (n : ℕ) :
    fromPowers (fun k => ∑ i, (z i : ℂ) ^ k) n = elem z n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [fromPowers]
    | succ k =>
      rw [fromPowers]
      have hs : (∑ i : Fin (k+1), (-1 : ℂ)^(i : ℕ) *
          fromPowers (fun n => ∑ j, (z j : ℂ)^n) i * (∑ j, (z j : ℂ)^(k+1-i))) =
          ∑ i : Fin (k+1), (-1 : ℂ)^(i : ℕ) * elem z i *
            (∑ j, (z j : ℂ)^(k+1-i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ih i i.isLt]
      rw [hs, mul_assoc, ← filtered_antidiagonal_sum
        (fun i j => (-1 : ℂ)^i * elem z i * (∑ l, (z l : ℂ)^j)) k]
      have hn := newton_elem z (k+1)
      rw [Nat.cast_add, Nat.cast_one] at hn
      rw [← hn, inv_mul_cancel_left₀]
      exact_mod_cast (Nat.succ_ne_zero k)

end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Y G : Type*} [MeasurableSpace Y] [MeasurableSpace G]

theorem measurable_kernelEncoding (β : Kernel Y G) [IsMarkovKernel β]
    (χ : G → ℂ) (hχ : Measurable χ) (m : ℕ) :
    Measurable (kernelEncoding β χ m) := by
  apply Measurable.of_eval
  intro i
  apply measurable_fromPowers
  intro n
  exact (((hχ.pow_const n).stronglyMeasurable.integral_kernel).measurable).const_mul _

theorem moments_uniform_list [MeasurableSingletonClass G] (χ : G → ℂ) (m : ℕ) (hm : 0 < m) (g : Fin m → G)
    (μ : Measure G) (hμ : μ = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i))
    (n : ℕ) :
    (m : ℂ) * (∫ d, χ d ^ n ∂μ) = ∑ i, χ (g i) ^ n := by
  classical
  rw [hμ, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [← mul_assoc, mul_inv_cancel₀, one_mul]
    exact_mod_cast hm.ne'
  · intro i _
    exact integrable_dirac (by simp)

/-- On every uniform finite fiber, the formula is exactly the source's
 elementary-symmetric vector, including repetitions of equal phases. -/
theorem kernelEncoding_eq_encoding [MeasurableSingletonClass G] (β : Kernel Y G) (χ : G → Circle)
    (m : ℕ) (hm : 0 < m) (y : Y) (g : Fin m → G)
    (hβ : β y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i)) :
    kernelEncoding β (fun d => (χ d : ℂ)) m y = encoding (fun i => χ (g i)) := by
  have hp : (fun n => (m : ℂ) * ∫ d, (χ d : ℂ)^n ∂β y) =
      fun n => ∑ i, (χ (g i) : ℂ)^n := by
    funext n
    exact moments_uniform_list (fun d => (χ d : ℂ)) m hm g (β y) hβ n
  funext i
  change fromPowers _ (i.val+1) = elem _ (i.val+1)
  rw [hp]
  exact fromPowers_eq_elem (fun i => χ (g i)) (i.val+1)

end

/-- Boundedness of the exact phase encoding, from compactness of the phase torus. -/
theorem exists_encoding_bound (m : ℕ) :
    ∃ B : ℝ, ∀ z : Fin m → Circle, ‖encoding z‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_range (continuous_encoding (m := m))).isBounded.exists_norm_le
  exact ⟨B, fun z => hB _ ⟨z, rfl⟩⟩
end EuclideanFiveColor.PhaseEncoding

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_ConditionalSelection
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators

open MeasureTheory

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.ConditionalFiber
variable {X W G V : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace W] [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma comp_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) :
    (condDistrib id p μ) ∘ₘ μ.map p = μ := by
  simpa using condDistrib_comp_map hp.aemeasurable (measurable_id.aemeasurable (μ := μ))

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_fiber_of_ae (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, P x := by
  exact Measure.ae_ae_of_ae_comp (by rwa [comp_identity_fiber μ p hp])

lemma map_identity_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : AEMeasurable p μ) (b : X → G) (hb : Measurable b) :
    ∀ᵐ w ∂μ.map p, (condDistrib id p μ w).map b = condDistrib b p μ w := by
  filter_upwards [condDistrib_comp p
    (measurable_id.aemeasurable (μ := μ)) hb] with w hw
  simpa [Kernel.map_apply _ hb] using hw.symm

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma ae_in_own_fiber [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsFiniteMeasure μ] (p : X → W) (hp : Measurable p) :
    ∀ᵐ w ∂μ.map p, ∀ᵐ x ∂condDistrib id p μ w, p x = w := by
  filter_upwards [map_identity_fiber μ p hp.aemeasurable p hp,
    condDistrib_self p] with w hw hs
  have he : (condDistrib id p μ w).map p = Measure.dirac w := by
    rw [hw, hs]; rfl
  apply ae_of_ae_map (p := fun z : W => z = w) hp.aemeasurable
  rw [he]
  simp

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integral_fiber (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    ∫ w, (∫ x, f x ∂condDistrib id p μ w) ∂μ.map p = ∫ x, f x ∂μ := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  have he := Kernel.integral_comp hi
  simpa [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply,
    comp_identity_fiber μ p hp] using he.symm

omit [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G] in
lemma integrable_fiber_integral (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → W) (hp : Measurable p) (f : X → V) (hf : Integrable f μ) :
    Integrable (fun w => ∫ x, f x ∂condDistrib id p μ w) (μ.map p) := by
  have hi : Integrable f ((condDistrib id p μ) ∘ₘ μ.map p) := by
    rwa [comp_identity_fiber μ p hp]
  rw [Measure.comp_eq_comp_const_apply] at hi
  exact hi.integral_comp

end EuclideanFiveColor.ConditionalFiber

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_SmallArcs
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators

open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace EuclideanFiveColor.SmallArc
noncomputable section

lemma pow_sub_one_bound (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ n * ‖z - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z ^ (n+1) - 1 = z ^ n * (z - 1) + (z ^ n - 1) := by ring
    rw [he]
    calc
      _ ≤ ‖z ^ n * (z - 1)‖ + ‖z ^ n - 1‖ := norm_add_le _ _
      _ ≤ ‖z - 1‖ + n * ‖z - 1‖ := by
        simpa only [norm_mul, norm_pow, hz, one_pow, one_mul] using
          add_le_add_right ih ‖z - 1‖
      _ = _ := by push_cast; ring

lemma phaseSum_sub_bound (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) :
    ‖phaseSum z N - (N : ℂ)‖ ≤ (N : ℝ)^2 * ‖z-1‖ := by
  have he : phaseSum z N - (N : ℂ) = ∑ n ∈ Finset.range N, (z^n-1) := by
    simp [phaseSum, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖z^n-1‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, (N : ℝ) * ‖z-1‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact (pow_sub_one_bound z hz n).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hn).le)
          (norm_nonneg _))
    _ = _ := by simp; ring

lemma phaseSum_lower (z : ℂ) (hz : ‖z‖ = 1) {N : ℕ} (hN : 0 < N)
    (hd : ‖z-1‖ ≤ 1 / (2 * (N : ℝ))) : (N : ℝ) / 2 ≤ ‖phaseSum z N‖ := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb := phaseSum_sub_bound z hz N
  have he : (N : ℝ)^2 * ‖z-1‖ ≤ (N : ℝ)/2 := by
    have := mul_le_mul_of_nonneg_left hd (sq_nonneg (N : ℝ))
    calc
      _ ≤ (N : ℝ)^2 * (1 / (2 * (N : ℝ))) := this
      _ = _ := by field_simp
  have ht := norm_sub_norm_le (N : ℂ) (phaseSum z N)
  rw [norm_sub_rev] at ht
  have hn : ‖(N : ℂ)‖ = (N : ℝ) := by simp
  rw [hn] at ht
  linarith

lemma phase_energy (z : ℂ) (N : ℕ) :
    ‖phaseSum z N‖ ^ 2 = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (z^i * conj (z^j)).re := by
  calc
    _ = (phaseSum z N * conj (phaseSum z N)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    _ = _ := by
      simp only [phaseSum, map_sum, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      change Complex.reCLM (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, _) = _
      simp only [map_sum]
      rfl

lemma pow_mul_conj_pow (z : ℂ) (hz : ‖z‖ = 1) {i j : ℕ} (hji : j ≤ i) :
    z^i * conj (z^j) = z^(i-j) := by
  nth_rw 1 [← Nat.sub_add_cancel hji]
  rw [pow_add, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow,
    hz, one_pow, one_pow, Complex.ofReal_one, mul_one]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  (z : X → ℂ) (hz : Measurable z) (hu : ∀ x, ‖z x‖ = 1)

include hz hu
lemma integrable_pair (i j : ℕ) : Integrable (fun x => z x ^ i * conj (z x ^ j)) μ := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall (fun x => by simp [hu])

omit hz in
lemma pair_moment_bound {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ n, 0 < n → n < N → ‖∫ x, z x ^ n ∂μ‖ ≤ c)
    {i j : ℕ} (hi : i < N) (hj : j < N) :
    (∫ x, z x^i * conj (z x^j) ∂μ).re ≤ (if i=j then 1 else 0) + c := by
  by_cases he : i = j
  · subst j
    have he : (fun x => z x^i * conj (z x^i)) = fun _ => (1 : ℂ) := by
      funext x
      simpa using pow_mul_conj_pow (z x) (hu x) (le_refl i)
    rw [he, integral_const]
    simp [hc]
  · simp only [he, ↓reduceIte, zero_add]
    by_cases hji : j ≤ i
    · have he : (fun x => z x^i * conj (z x^j)) = fun x => z x^(i-j) := by
        funext x
        exact pow_mul_conj_pow (z x) (hu x) hji
      rw [he]
      exact (Complex.re_le_norm _).trans (hm (i-j) (by omega) (by omega))
    · have he : (fun x => z x^i * conj (z x^j)) =
          fun x => conj (z x^(j-i)) := by
        funext x
        rw [← pow_mul_conj_pow (z x) (hu x) (by omega : i ≤ j)]
        simp only [map_mul, starRingEnd_self_apply]
        exact mul_comm _ _
      rw [he, integral_conj]
      exact (Complex.re_le_norm _).trans (by simpa using hm (j-i) (by omega) (by omega))

lemma phase_energy_integral_bound {N : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ n, 0 < n → n < N → ‖∫ x, z x ^ n ∂μ‖ ≤ c) :
    (∫ x, ‖phaseSum (z x) N‖ ^ 2 ∂μ) ≤ N + (N : ℝ)^2 * c := by
  simp_rw [phase_energy]
  rw [integral_finsetSum]
  · calc
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (∫ x, z x^i * conj (z x^j) ∂μ).re := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j _
          exact (integral_re (integrable_pair μ z hz hu i j))
        · intro j _
          exact (integrable_pair μ z hz hu i j).re
      _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ((if i=j then (1 : ℝ) else 0) + c) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact pair_moment_bound μ z hu hc hm (Finset.mem_range.mp hi)
          (Finset.mem_range.mp hj)
      _ = _ := by
        rw [Finset.sum_congr rfl (fun i hi => by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left hi])]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  · intro i _
    exact integrable_finsetSum _ (fun j _ => (integrable_pair μ z hz hu i j).re)

lemma integrable_energy (N : ℕ) : Integrable (fun x => ‖phaseSum (z x) N‖^2) μ := by
  have h : ∀ x, ‖phaseSum (z x) N‖ ≤ N := by
    intro x
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖z x ^ n‖ := norm_sum_le _ _
      _ = N := by simp [hu]
  apply Integrable.of_bound (by unfold phaseSum; fun_prop) ((N : ℝ)^2)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h x) 2)

/-- A quantitative finite-moment bound for the small arc about 1. -/
theorem small_arc_bound {N : ℕ} (hN : 0 < N) {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ n, 0 < n → n < N → ‖∫ x, z x ^ n ∂μ‖ ≤ c) :
    μ.real {x | ‖z x-1‖ ≤ 1 / (2 * (N : ℝ))} ≤ 4 / N + 4*c := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : {x | ‖z x-1‖ ≤ 1 / (2 * (N : ℝ))} ⊆
      {x | (N : ℝ)^2 / 4 ≤ ‖phaseSum (z x) N‖ ^ 2} := by
    intro x hx
    have hh := phaseSum_lower (z x) (hu x) hN hx
    change (N : ℝ)^2 / 4 ≤ _
    nlinarith [norm_nonneg (phaseSum (z x) N)]
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖phaseSum (z x) N‖))
    (integrable_energy μ z hz hu N) ((N : ℝ)^2/4)
  have he := phase_energy_integral_bound μ z hz hu hc hm
  have hreal := measureReal_mono (μ := μ) hs
  have hm' : (N : ℝ)^2/4 * μ.real {x | ‖z x-1‖ ≤ 1 / (2 * (N : ℝ))} ≤
      N + (N : ℝ)^2*c :=
    (mul_le_mul_of_nonneg_left hreal (by positivity)).trans (hmark.trans he)
  calc
    _ ≤ (N + (N : ℝ)^2*c)/((N : ℝ)^2/4) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hm'])
    _ = _ := by field_simp

attribute [local instance] OAI.EuclideanFiveColor.SmallArc.instMeasurableSpaceCircle_solutions
local instance instBorelSpaceCircle_solutions : BorelSpace Circle := ⟨rfl⟩

omit [MeasurableSpace X] hz hu in
/-- The source's qualitative choice, with explicit constants. -/
theorem exists_small_arc_constants (m : ℕ) (hm : 0 < m) :
    ∃ (ρ c : ℝ) (N : ℕ), 0 < ρ ∧ 0 < c ∧ 0 < N ∧
      ∀ (ω : Measure Circle) [IsProbabilityMeasure ω],
      (∀ n, 0 < n → n ≤ N → ‖∫ w, (w : ℂ)^n ∂ω‖ < c) →
      ω.real {w | ‖(w : ℂ)-1‖ ≤ 4*ρ} < 1/(4*(m : ℝ)^2) := by
  let N := 64*m^2
  have hN : 0 < N := by dsimp [N]; positivity
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine ⟨1/(8*N), 1/N, N, by positivity, by positivity, hN, ?_⟩
  intro ω _ hω
  have hco : Continuous (fun w : Circle => (w : ℂ)) := continuous_subtype_val
  have hcm : Measurable (fun w : Circle => (w : ℂ)) := hco.measurable
  have hb := small_arc_bound ω (fun w : Circle => (w : ℂ))
    hcm Circle.norm_coe hN (by positivity : (0 : ℝ) ≤ 1/N)
    (fun n hn hnN => (hω n hn (le_of_lt hnN)).le)
  have hr : 4*(1/(8*(N : ℝ))) = 1/(2*N) := by ring
  rw [hr]
  apply hb.trans_lt
  have he : (N : ℝ) = 64*(m : ℝ)^2 := by dsimp [N]; push_cast; rfl
  rw [he]
  field_simp
  norm_num

end
end EuclideanFiveColor.SmallArc

/-! Fiberwise (possibly nonmeasurable) enumerations cause no measurability gap:
actual conditional samples lie in them by the measurable positive-atom event. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_ConditionalSpectrum
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.K_countable _root_.OAI.PlaneFiveColor.Spectral.dualMeasurableConstSMul _root_.OAI.PlaneFiveColor.Spectral.dualMulDistribAction _root_.OAI.PlaneFiveColor.Spectral.dualStandardBorelSpace _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory
open EuclideanFiveColor
open scoped BigOperators ComplexConjugate

lemma eval_smul_one (u : K) (d : D) : eval 1 (u • d) = eval (kCoeff u) d := by
  change eval (kCoeff u * 1) d = _
  rw [mul_one]

end

end PlaneFiveColor.Spectral

namespace EuclideanFiveColor.PhaseEncoding
open MeasureTheory ProbabilityTheory
variable {Y G : Type*} [MeasurableSpace Y] [MeasurableSpace G]
/-- Covariance of the *actual* Newton-symmetric conditional encoding. -/
theorem kernelEncoding_covariance (ν : Measure Y) (β : Kernel Y G)
    (R : Y → Y) (T : G → G) (hT : Measurable T)
    (χ : G → ℂ) (hχ : Measurable χ) (m : ℕ)
    (hβ : ∀ᵐ y ∂ν, β (R y) = (β y).map T) :
    ∀ᵐ y ∂ν, kernelEncoding β χ m (R y) = kernelEncoding β (χ ∘ T) m y := by
  filter_upwards [hβ] with y hy
  have he (n : ℕ) : (∫ d, χ d ^ n ∂β (R y)) = ∫ d, χ (T d)^n ∂β y := by
    rw [hy, integral_map hT.aemeasurable (hχ.pow_const n).aestronglyMeasurable]
  funext i
  simp only [kernelEncoding, he, Function.comp_def]
end EuclideanFiveColor.PhaseEncoding

namespace PlaneFiveColor.Spectral

open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators

variable {X Y W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

attribute [local instance] OAI.PlaneFiveColor.Spectral.instMeasurableSpaceCircle_solutions_2
omit [StandardBorelSpace Y] [Nonempty Y] in
theorem finite_uniform_successor_contradiction
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → Y) (q : Y → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q ∘ p))
      (condDistrib b (q ∘ p) μ)))
    (happrox : FiniteEncodingApproximation μ p q b m) : False := by
  obtain ⟨ρ, c, N, hρ, hc, hN, harc⟩ := SmallArc.exists_small_arc_constants m hm
  exact finite_uniform_precision_contradiction μ p q b hp hq hb m hm g hg hwild
    ρ c N hρ hc hN harc (happrox _ (by positivity))

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Approximation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.K_countable _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.UniformEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {G Y : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableSpace Y] [Nonempty G]

omit [Nonempty G] in
theorem list_of_uniform_atoms (κ : Measure G)
    (S : Finset G) (a : ℝ≥0∞) (hmass : ∀ d ∈ S, κ {d} = a)
    (hsupp : ∀ᵐ d ∂κ, d ∈ S) (hc : (S.card : ℝ≥0∞)*a=1) :
    ∃ g : Fin S.card → G, κ = (S.card : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) := by
  classical
  let e := S.equivFin
  let g : Fin S.card → G := fun i => (e.symm i).val
  have heq := Measure.ae_mem_finset_iff.mp hsupp
  have ha : a = (S.card : ℝ≥0∞)⁻¹ := by
    have hn : (S.card : ℝ≥0∞) ≠ 0 := by intro h; rw [h, zero_mul] at hc; exact zero_ne_one hc
    calc
      a = 1*a := by simp
      _ = ((S.card : ℝ≥0∞)⁻¹ * S.card)*a := by rw [ENNReal.inv_mul_cancel hn (by simp)]
      _ = (S.card : ℝ≥0∞)⁻¹ := by rw [mul_assoc, hc, mul_one]
  refine ⟨g, ?_⟩
  calc
    κ = ∑ d ∈ S, κ {d} • Measure.dirac d := heq
    _ = ∑ d ∈ S, (S.card : ℝ≥0∞)⁻¹ • Measure.dirac d :=
      Finset.sum_congr rfl (fun d hd => by rw [hmass d hd, ha])
    _ = (S.card : ℝ≥0∞)⁻¹ • ∑ d ∈ S, Measure.dirac d := Finset.smul_sum.symm
    _ = (S.card : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) := by
      congr 1
      rw [← Finset.sum_coe_sort S (fun d => Measure.dirac d)]
      exact (Equiv.sum_comp e.symm (fun d : S => Measure.dirac d.val)).symm

theorem constant_uniform_lists (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] (a : ℝ≥0∞) (ha : 0 < a)
    (hf : ∀ᵐ y ∂ν, ∃ S : Finset G, S.Nonempty ∧
      (∀ d ∈ S, κ y {d} = a) ∧ (∀ᵐ d ∂κ y, d ∈ S) ∧ (S.card : ℝ≥0∞)*a=1) :
    ∃ m : ℕ, 0 < m ∧ ∃ g : Y → Fin m → G,
      ∀ᵐ y ∂ν, κ y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i) := by
  classical
  obtain ⟨y₀, S₀, hS₀, _, _, hc₀⟩ := hf.exists
  let m := S₀.card
  have hm : 0 < m := Finset.card_pos.mpr hS₀
  have haT : a ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by exact_mod_cast hm.ne')] at hc₀
    exact ENNReal.top_ne_one hc₀
  have hlist : ∀ᵐ y ∂ν, ∃ g : Fin m → G,
      κ y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) := by
    filter_upwards [hf] with y hy
    obtain ⟨S, _hS, hSa, hSupp, hc⟩ := hy
    have hcard : S.card = m := by
      have hh : (S.card : ℝ≥0∞) = (m : ℝ≥0∞) :=
        (ENNReal.mul_right_inj ha.ne' haT).mp (by simpa only [mul_comm] using hc.trans hc₀.symm)
      exact_mod_cast hh
    obtain ⟨g, hg⟩ := list_of_uniform_atoms (κ y) S a hSa hSupp hc
    have hh : (∑ j : Fin S.card, Measure.dirac (g j)) =
        ∑ i : Fin m, Measure.dirac (g (Fin.cast hcard.symm i)) :=
      (Equiv.sum_comp (finCongr hcard.symm) (fun j => Measure.dirac (g j))).symm
    refine ⟨fun i => g (Fin.cast hcard.symm i), ?_⟩
    calc
      κ y = (S.card : ℝ≥0∞)⁻¹ • ∑ i : Fin m, Measure.dirac (g (Fin.cast hcard.symm i)) := hg.trans (congrArg ((S.card : ℝ≥0∞)⁻¹ • ·) hh)
      _ = _ := by congr 2; exact_mod_cast hcard
  let g : Y → Fin m → G := fun y => if h : ∃ g : Fin m → G,
      κ y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) then h.choose else fun _ => Classical.choice inferInstance
  refine ⟨m, hm, g, ?_⟩
  filter_upwards [hlist] with y hy
  simpa only [g, dite_eq_left hy] using hy.choose_spec

end EuclideanFiveColor.UniformEnumeration

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.DifferenceInvariant
variable {G Y : Type*} [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace Y]

lemma invariant (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ]
    (R : Y → Y) (hR : MeasurePreserving R ν ν)
    (T : G →* G) (hT : Measurable T)
    (he : ∀ᵐ y ∂ν, κ (R y) = (κ y).map T) :
    MeasurePreserving T (differenceLaw ν κ) (differenceLaw ν κ) := by
  have hprod : (((κ ×ₖ κ) ∘ₘ ν).map (Prod.map T T)) = ((κ ×ₖ κ) ∘ₘ ν) := by
    ext s hs
    rw [Measure.map_apply (hT.prodMap hT) hs,
      Measure.bind_apply ((hT.prodMap hT) hs) (κ ×ₖ κ).aemeasurable,
      Measure.bind_apply hs (κ ×ₖ κ).aemeasurable]
    calc
      (∫⁻ y, (κ ×ₖ κ) y ((Prod.map T T) ⁻¹' s) ∂ν) =
          ∫⁻ y, (κ ×ₖ κ) (R y) s ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [he] with y hy
        rw [Kernel.prod_apply, Kernel.prod_apply, hy,
          Measure.map_prod_map _ _ hT hT, Measure.map_apply (hT.prodMap hT) hs]
      _ = ∫⁻ y, (κ ×ₖ κ) y s ∂ν := hR.lintegral_comp (Kernel.measurable_coe _ hs)
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) := measurable_fst.div measurable_snd
  refine ⟨hT, ?_⟩
  rw [differenceLaw, Measure.map_map hT hdiv]
  calc
    (((κ ×ₖ κ) ∘ₘ ν).map (T ∘ (fun p : G × G => p.1 / p.2))) =
        ((κ ×ₖ κ) ∘ₘ ν).map ((fun p : G × G => p.1 / p.2) ∘ Prod.map T T) := by
      congr 1
      funext p
      exact map_div T p.1 p.2
    _ = (((κ ×ₖ κ) ∘ₘ ν).map (Prod.map T T)).map (fun p : G × G => p.1 / p.2) :=
      (Measure.map_map hdiv (hT.prodMap hT)).symm
    _ = _ := by rw [hprod]

end EuclideanFiveColor.DifferenceInvariant

/-! The scalar finite bounded-module approximation in (source-4), and its
finite-vector consequence. All functions are measurable bounded representatives. -/
namespace EuclideanFiveColor.CompactApproximation
open MeasureTheory
open scoped BigOperators
variable {K Y W : Type*} [SMul K Y] [MeasurableSpace Y] [MeasurableSpace W]

lemma pi_dist_sq_le_sum {I : Type*} [Fintype I] (a b : I → ℂ) :
    dist a b ^ 2 ≤ ∑ i, dist (a i) (b i)^2 := by
  have hs : 0 ≤ ∑ i, dist (a i) (b i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : dist a b ≤ Real.sqrt (∑ i, dist (a i) (b i)^2) := by
    rw [dist_eq_norm, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    change ‖a i - b i‖ ≤ _
    rw [← dist_eq_norm]
    apply (Real.le_sqrt (dist_nonneg) hs).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg (dist (a j) (b j))) (Finset.mem_univ i)
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ i, dist (a i) (b i)^2), dist_nonneg (x := a) (y := b)]

lemma vector_of_scalar (ν : Measure Y) [IsProbabilityMeasure ν]
    (q : Y → W) (hq : Measurable q) [MeasurableConstSMul K Y]
    (hs : Scalar (K := K) ν q) : Vector (K := K) ν q := by
  classical
  intro m H hH hHb ε hε
  let δ : ℝ := ε / (m+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hcoord (j : Fin m) : ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → ℂ),
      0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
      ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
        Integrable (fun y => dist (H (k • y) j) (∑ i, a (q y) i * Hf i y)^2) ν ∧
        (∫ y, dist (H (k • y) j) (∑ i, a (q y) i * Hf i y)^2 ∂ν) < δ^2 := by
    apply hs (fun y => H y j) ((measurable_pi_iff.mp hH) j) _ δ hδ
    obtain ⟨C, hC⟩ := hHb
    exact ⟨C, fun y => (norm_le_pi_norm (H y) j).trans (hC y)⟩
  choose r B C Hf hB hC hHm hHb hA using hcoord
  let I := (j : Fin m) × Fin (r j)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let V : I → Y → Fin m → ℂ := fun s y => Pi.single s.1 (Hf s.1 s.2 y)
  have hV (s : I) : Measurable (V s) := by
    apply Measurable.of_eval
    intro j
    by_cases h : s.1 = j
    · subst j
      simpa [V] using hHm s.1 s.2
    · simp only [V, Pi.single_apply, Ne.symm h, ite_false]
      exact measurable_const
  have hVnorm (s : I) (y : Y) : ‖V s y‖ ≤ ‖Hf s.1 s.2 y‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro j
    by_cases h : s.1 = j
    · subst j; simp [V]
    · simp [V, h]
  refine ⟨Fintype.card I, ∑ j, B j, ∑ j, C j, fun i => V (e i),
    Finset.sum_nonneg (fun j _ => hB j), Finset.sum_nonneg (fun j _ => hC j),
    fun i => hV (e i), ?_, ?_⟩
  · intro y
    change (∑ i, (fun s : I => ‖V s y‖) (e i)) ≤ _
    rw [Equiv.sum_comp e (fun s : I => ‖V s y‖)]
    calc
      ∑ s : I, ‖V s y‖ ≤ ∑ s : I, ‖Hf s.1 s.2 y‖ := Finset.sum_le_sum (fun s _ => hVnorm s y)
      _ = ∑ j, ∑ i, ‖Hf j i y‖ := Fintype.sum_sigma _
      _ ≤ ∑ j, C j := Finset.sum_le_sum (fun j _ => hHb j y)
  · intro k
    choose a ham hab hai hae using fun j => hA j k
    let a' : W → I → ℂ := fun w s => a s.1 w s.2
    have hap (w : W) : ‖fun i => a' w (e i)‖ ≤ ∑ j, B j := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => hB j))]
      intro i
      exact ((norm_le_pi_norm (a (e i).1 w) (e i).2).trans (hab (e i).1 w)).trans
        (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ _))
    have ham' : Measurable (fun w i => a' w (e i)) := by
      apply Measurable.of_eval
      intro i
      exact (measurable_pi_iff.mp (ham (e i).1)) (e i).2
    let A : Y → Fin m → ℂ := fun y => ∑ s : I, a' (q y) s • V s y
    have hAeq (y : Y) (j : Fin m) : A y j = ∑ i, a j (q y) i * Hf j i y := by
      change (∑ s : I, a' (q y) s • V s y) j = _
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Fintype.sum_sigma]
      simp [a', V, Pi.single_apply]
    have hAm : Measurable A := by
      apply Measurable.of_eval
      intro j
      simp_rw [hAeq]
      exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_iff.mp (ham j)) i |>.comp hq).mul (hHm j i))
    have hem : AEStronglyMeasurable (fun y => dist (H (k • y)) (A y)^2) ν :=
      ((hH.comp (measurable_const_smul k)).dist hAm |>.pow_const 2).aestronglyMeasurable
    have hsint : Integrable (fun y => ∑ j, dist (H (k • y) j) (A y j)^2) ν := by
      apply integrable_finsetSum
      intro j _
      simpa only [hAeq] using hai j
    have hbound (y : Y) : dist (H (k • y)) (A y)^2 ≤ ∑ j, dist (H (k • y) j) (A y j)^2 :=
      pi_dist_sq_le_sum _ _
    have hint : Integrable (fun y => dist (H (k • y)) (A y)^2) ν :=
      hsint.mono' hem (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (dist (H (k • y)) (A y)))] using hbound y))
    have hbudget : (∫ y, dist (H (k • y)) (A y)^2 ∂ν) < ε^2 := by
      calc
        _ ≤ ∫ y, ∑ j, dist (H (k • y) j) (A y j)^2 ∂ν := integral_mono hint hsint hbound
        _ = ∑ j, ∫ y, dist (H (k • y) j) (A y j)^2 ∂ν := integral_finsetSum _ (fun j _ => by simpa only [hAeq] using hai j)
        _ ≤ ∑ _j : Fin m, δ^2 := Finset.sum_le_sum (fun j _ => by simpa only [hAeq] using (hae j).le)
        _ = (m : ℝ) * δ^2 := by simp
        _ < ε^2 := by
          dsimp [δ]
          have hm : (0 : ℝ) < m+1 := by positivity
          rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (sq_pos_of_pos hm)]
          nlinarith [sq_nonneg (m : ℝ), sq_pos_of_pos hε]
    have hAe (y : Y) : (∑ i, a' (q y) (e i) • V (e i) y) = A y :=
      Equiv.sum_comp e (fun s => a' (q y) s • V s y)
    refine ⟨fun w i => a' w (e i), ham', hap, ?_, ?_⟩
    · simpa only [hAe] using hint
    · simpa only [hAe] using hbudget

end EuclideanFiveColor.CompactApproximation

namespace EuclideanFiveColor.KernelSupport
open MeasureTheory
variable {K X Y : Type*} [Group K] [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction K X] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y]
lemma factor_smul_preserving (μ : Measure X) [SMulInvariantMeasure K X μ]
    (p : X → Y) (hp : Measurable p)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) (k : K) :
    MeasurePreserving (fun y : Y => k • y) (μ.map p) (μ.map p) := by
  refine ⟨measurable_const_smul k, ?_⟩
  rw [Measure.map_map (measurable_const_smul k) hp]
  calc
    μ.map ((fun y : Y => k • y) ∘ p) = μ.map (p ∘ (fun x : X => k • x)) :=
      Measure.map_congr ((hpe k).mono fun _ hx => hx.symm)
    _ = (μ.map (fun x : X => k • x)).map p :=
      (Measure.map_map hp (measurable_const_smul k)).symm
    _ = μ.map p := by rw [measurePreserving_smul k μ |>.map_eq]
end EuclideanFiveColor.KernelSupport

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MulAction K X] [MulAction K Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

lemma relative_difference_invariant (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure K X μ] (b : X → D) (p : X → Y)
    (hb : Measurable b) (hp : Measurable p)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) (k : K) :
    MeasurePreserving (fun d : D => k • d)
      (DifferenceFourier.differenceLaw (μ.map p) (condDistrib b p μ))
      (DifferenceFourier.differenceLaw (μ.map p) (condDistrib b p μ)) := by
  have he := KernelSupport.condDistrib_equivariant μ b p hb hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun d : D => k • d)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hbe k)
  haveI : IsProbabilityMeasure (μ.map p) := Measure.isProbabilityMeasure_map hp.aemeasurable
  exact DifferenceInvariant.invariant (μ.map p) (condDistrib b p μ)
    (fun y : Y => k • y) (KernelSupport.factor_smul_preserving μ p hp hpe k)
    (scalarHom (kCoeff k)) (measurable_const_smul k) he

lemma finite_encoding_approximation_of_compact
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure K X μ]
    (p : X → Y) (q : Y → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hc : CompactApproximation.Scalar (K := K) (μ.map p) q) :
    FiniteEncodingApproximation μ p q b m := by
  classical
  let H₀ : Y → Fin m → ℂ := PhaseEncoding.kernelEncoding (condDistrib b p μ)
    (fun d => (eval 1 d : ℂ)) m
  have hH₀ : Measurable H₀ :=
    PhaseEncoding.measurable_kernelEncoding _ _ (measurable_eval_coe 1) m
  obtain ⟨A, hA⟩ := PhaseEncoding.exists_encoding_bound m
  have hHB : ∀ᵐ y ∂μ.map p, ‖H₀ y‖ ≤ max A 0 := by
    filter_upwards [hg] with y hy
    have he := PhaseEncoding.kernelEncoding_eq_encoding (condDistrib b p μ) (eval 1) m hm y (g y) hy
    change ‖PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval 1 d : ℂ)) m y‖ ≤ max A 0
    rw [he]
    exact (hA (fun i => eval 1 (g y i))).trans (le_max_left _ _)
  let H : Y → Fin m → ℂ := fun y => if ‖H₀ y‖ ≤ max A 0 then H₀ y else 0
  have hH : Measurable H := hH₀.piecewise (measurableSet_le hH₀.norm measurable_const) measurable_const
  have hHbound : ∀ y, ‖H y‖ ≤ max A 0 := by
    intro y
    by_cases hy : ‖H₀ y‖ ≤ max A 0
    · simpa only [H, ite_eq_left hy] using hy
    · simp only [H, ite_eq_right hy, norm_zero]
      exact le_max_right _ _
  haveI : IsProbabilityMeasure (μ.map p) := Measure.isProbabilityMeasure_map hp.aemeasurable
  have hHeq : H =ᵐ[μ.map p] H₀ := hHB.mono fun y hy => ite_eq_left hy
  have hv := CompactApproximation.vector_of_scalar (μ.map p) q hq hc
  intro γ hγ
  obtain ⟨r, B, C, Hf, hB, hC, _hHm, hHf, ha⟩ := hv m H hH ⟨max A 0, hHbound⟩ γ hγ
  refine ⟨r, B, C, Hf, hB, hC, hHf, ?_⟩
  intro k
  obtain ⟨a, _ham, hab, hai, hae⟩ := ha k
  have hker := KernelSupport.condDistrib_equivariant μ b p hb hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun d : D => k • d)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hbe k)
  have hcov := PhaseEncoding.kernelEncoding_covariance (μ.map p) (condDistrib b p μ)
    (fun y : Y => k • y) (fun d : D => k • d) (measurable_const_smul k)
    (fun d => (eval 1 d : ℂ)) (measurable_eval_coe 1) m hker
  have heq : ∀ᵐ y ∂μ.map p, H (k • y) =
      PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval (kCoeff k) d : ℂ)) m y := by
    filter_upwards [(KernelSupport.factor_smul_preserving μ p hp hpe k).quasiMeasurePreserving.ae hHeq,
      hcov] with y hy hc'
    exact hy.trans (by simpa only [Function.comp_def, eval_smul_one] using hc')
  have he : (fun y => dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2) =ᵐ[μ.map p]
      (fun y => dist (PhaseEncoding.kernelEncoding (condDistrib b p μ)
        (fun d => (eval (kCoeff k) d : ℂ)) m y) (∑ i, a (q y) i • Hf i y)^2) := by
    filter_upwards [heq] with y hy
    rw [hy]
  have hai' := hai.congr he
  refine ⟨a, hab, hai'.comp_measurable hp, ?_⟩
  rw [← integral_map hp.aemeasurable hai'.aestronglyMeasurable,
    ← integral_congr_ae he]
  exact hae

/-- The complete source successor implication. The predecessor assertion is
universal in the equivariant wild map, as required by the transfinite induction. -/
theorem relative_singularity_successor
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    [StandardBorelSpace W] [Nonempty W]
    [MulAction K W] [MeasurableConstSMul K W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → D) (p : X → Y) (q : Y → W)
    (hd : Measurable d) (hp : Measurable p) (hq : Measurable q)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hqe : ∀ k : K, ∀ᵐ y ∂μ.map p, q (k • y) = k • q y)
    (hwild : IsWild (μ.map d))
    (hc : CompactApproximation.Scalar (K := K) (μ.map p) q)
    (hprev : ∀ b : X → D, Measurable b →
      (∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x) → IsWild (μ.map b) →
      DifferenceFourier.differenceLaw (μ.map (q ∘ p)) (condDistrib b (q ∘ p) μ) C = 0) :
    DifferenceFourier.differenceLaw (μ.map p) (condDistrib d p μ) C = 0 := by
  by_contra hn
  have hpos : 0 < RelativeCenters.differenceLaw (μ.map p) (condDistrib d p μ) C :=
    pos_iff_ne_zero.mpr hn
  obtain ⟨b, hb, hbe, hbw, a, ha, hf⟩ := exact_finite_center_reduction μ d p hd hp hde hpe hwild hpos
  haveI : IsProbabilityMeasure (μ.map p) := Measure.isProbabilityMeasure_map hp.aemeasurable
  obtain ⟨m, hm, g, hg⟩ := UniformEnumeration.constant_uniform_lists (μ.map p)
    (condDistrib b p μ) a ha (hf.mono fun y ⟨S, hS, hSa, hSupp, hcS, _⟩ =>
      ⟨S, hS, hSa, hSupp, hcS⟩)
  have hcomp : ∀ k : K, ∀ᵐ x ∂μ, (q ∘ p) (k • x) = k • (q ∘ p) x := by
    intro k
    filter_upwards [hpe k, ae_of_ae_map hp.aemeasurable (hqe k)] with x hx hy
    simp only [Function.comp_def, hx, hy]
  have hpwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q ∘ p)) (condDistrib b (q ∘ p) μ)) :=
    ⟨relative_difference_invariant μ b (q ∘ p) hb (hq.comp hp) hbe hcomp,
      hprev b hb hbe hbw⟩
  exact finite_uniform_successor_contradiction μ p q b hp hq hb m hm g hg hpwild
    (finite_encoding_approximation_of_compact μ p q b hp hq hb hpe hbe m hm g hg hc)

end PlaneFiveColor.Spectral

namespace EuclideanFiveColor.CompactApproximation
open MeasureTheory
open scoped BigOperators
variable {K Y Z W : Type*} [SMul K Y] [SMul K Z]
  [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

lemma lift_at
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (p : Y → Z) (q : Z → W) (hp : Measurable p) (hq : Measurable q)
    [MeasurableConstSMul K Y] [MeasurableConstSMul K Z]
    (hpres : ∀ k : K, MeasurePreserving (fun y : Y => k • y) ν ν)
    (hpe : ∀ k : K, ∀ᵐ y ∂ν, p (k • y) = k • p y)
    (m : ℕ) (H : Y → Fin m → ℂ) (H₀ : Z → Fin m → ℂ)
    (hH : Measurable H) (hH₀ : Measurable H₀)
    (hB₀ : ∃ C : ℝ, ∀ z, ‖H₀ z‖ ≤ C)
    (ε : ℝ) (hε : 0 < ε)
    (hi : Integrable (fun y => dist (H y) (H₀ (p y))^2) ν)
    (he : (∫ y, dist (H y) (H₀ (p y))^2 ∂ν) < (ε/2)^2)
    (hc : Vector (K := K) (ν.map p) q) : At (K := K) ν (q ∘ p) m H ε := by
  classical
  obtain ⟨r, B, C, Hf, hB, hC, hHm, hHf, ha⟩ := hc m H₀ hH₀ hB₀ (ε/2) (by positivity)
  refine ⟨r, B, C, fun i => Hf i ∘ p, hB, hC, fun i => (hHm i).comp hp,
    fun y => hHf (p y), ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha k
  let F : Y → Fin m → ℂ := fun y => ∑ i, a (q (p y)) i • Hf i (p y)
  have hFm : Measurable F := by
    exact Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp (hq.comp hp)).smul ((hHm i).comp hp))
  let e₁ : Y → ℝ := fun y => dist (H (k • y)) (H₀ (k • p y))^2
  let e₂ : Y → ℝ := fun y => dist (H₀ (k • p y)) (F y)^2
  have heq : (fun y => dist (H (k • y)) (H₀ (p (k • y)))^2) =ᵐ[ν] e₁ :=
    (hpe k).mono fun y hy => by simp only [e₁, hy]
  have hi₁ : Integrable e₁ ν := ((hpres k).integrable_comp hi.aestronglyMeasurable |>.mpr hi).congr heq
  have he₁ : (∫ y, e₁ y ∂ν) < (ε/2)^2 := by
    have hm : AEStronglyMeasurable (fun y => dist (H y) (H₀ (p y))^2)
        (ν.map (fun y : Y => k • y)) := by
      rw [(hpres k).map_eq]
      exact hi.aestronglyMeasurable
    rw [← integral_congr_ae heq, ← integral_map (hpres k).measurable.aemeasurable hm,
      (hpres k).map_eq]
    exact he
  have hi₂ : Integrable e₂ ν := hai.comp_measurable hp
  have he₂ : (∫ y, e₂ y ∂ν) < (ε/2)^2 := by
    change (∫ y, dist (H₀ (k • p y)) (∑ i, a (q (p y)) i • Hf i (p y))^2 ∂ν) < _
    rw [← integral_map hp.aemeasurable hai.aestronglyMeasurable]
    exact hae
  have hmajor (y : Y) : dist (H (k • y)) (F y)^2 ≤ 2*(e₁ y + e₂ y) := by
    have ht := dist_triangle (H (k • y)) (H₀ (k • p y)) (F y)
    have hx := dist_nonneg (x := H (k • y)) (y := H₀ (k • p y))
    have hy := dist_nonneg (x := H₀ (k • p y)) (y := F y)
    have hz := dist_nonneg (x := H (k • y)) (y := F y)
    dsimp [e₁, e₂]
    nlinarith [sq_nonneg (dist (H (k • y)) (H₀ (k • p y)) - dist (H₀ (k • p y)) (F y))]
  have himaj : Integrable (fun y => 2*(e₁ y + e₂ y)) ν := (hi₁.add hi₂).const_mul 2
  have hint : Integrable (fun y => dist (H (k • y)) (F y)^2) ν :=
    himaj.mono' (((hH.comp (measurable_const_smul k)).dist hFm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor y)
  refine ⟨a, ham, hab, hint, ?_⟩
  calc
    (∫ y, dist (H (k • y)) (F y)^2 ∂ν) ≤ ∫ y, 2*(e₁ y + e₂ y) ∂ν :=
      integral_mono hint himaj hmajor
    _ = 2*((∫ y, e₁ y ∂ν) + ∫ y, e₂ y ∂ν) := by
      rw [integral_const_mul, integral_add hi₁ hi₂]
    _ < ε^2 := by nlinarith

end EuclideanFiveColor.CompactApproximation

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_ConditionalLimits
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.LabelModel.continuous_complete _root_.OAI.PlaneFiveColor.LabelModel.instCompactSpaceSpace _root_.OAI.PlaneFiveColor.LabelModel.instIsProbabilityMeasureSpaceMeasure _root_.OAI.PlaneFiveColor.Spectral.K_countable _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! Bounded finite-dimensional L² approximation at a generated limit factor.
The filtration is the pullback of an increasing sequence of earlier factors;
no martingale convergence theorem beyond Mathlib is assumed. -/
namespace EuclideanFiveColor.LimitDensity
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Y : Type*} [mY : MeasurableSpace Y]

lemma clip_bound {C : ℝ} (hC : 0 ≤ C) (t : ℝ) : |clip C t| ≤ C := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
lemma clip_eq {C t : ℝ} (ht : |t| ≤ C) : clip C t = t := by
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  simp only [clip, min_eq_right hu, max_eq_right hl]
lemma continuous_clip (C : ℝ) : Continuous (clip C) := by
  unfold clip
  fun_prop

/-- A bounded vector measurable for a generated join is an L² limit of
uniformly bounded functions measurable at finite stages. -/
theorem bounded_vector_approximation
    (ν : Measure Y) [IsProbabilityMeasure ν] (ℱ : Filtration ℕ mY)
    (m : ℕ) (H : Y → Fin m → ℂ) (hH : Measurable[⨆ n, ℱ n] H)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, ‖H y‖ ≤ C) :
    ∃ Hn : ℕ → Y → Fin m → ℂ,
      (∀ n, Measurable[ℱ n] (Hn n)) ∧
      (∀ n y, ‖Hn n y‖ ≤ 2*C) ∧
      (∀ n, Integrable (fun y => dist (H y) (Hn n y)^2) ν) ∧
      Tendsto (fun n => ∫ y, dist (H y) (Hn n y)^2 ∂ν) atTop (𝓝 0) := by
  classical
  have hle : (⨆ n, ℱ n) ≤ mY := iSup_le fun n => ℱ.le n
  have hHm : Measurable H := hH.mono hle le_rfl
  let R : Fin m → Y → ℝ := fun j y => (H y j).re
  let I : Fin m → Y → ℝ := fun j y => (H y j).im
  have hR (j : Fin m) : Measurable[⨆ n, ℱ n] (R j) := by
    let : MeasurableSpace Y := ⨆ n, ℱ n
    exact Complex.measurable_re.comp ((measurable_pi_iff.mp hH) j)
  have hI (j : Fin m) : Measurable[⨆ n, ℱ n] (I j) := by
    let : MeasurableSpace Y := ⨆ n, ℱ n
    exact Complex.measurable_im.comp ((measurable_pi_iff.mp hH) j)
  have hRB (j : Fin m) (y : Y) : |R j y| ≤ C :=
    (Complex.abs_re_le_norm _).trans ((norm_le_pi_norm (H y) j).trans (hbound y))
  have hIB (j : Fin m) (y : Y) : |I j y| ≤ C :=
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (H y) j).trans (hbound y))
  have hRi (j : Fin m) : Integrable (R j) ν :=
    Integrable.of_bound ((hR j).mono hle le_rfl).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hRB j y)
  have hIi (j : Fin m) : Integrable (I j) ν :=
    Integrable.of_bound ((hI j).mono hle le_rfl).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hIB j y)
  let Hn : ℕ → Y → Fin m → ℂ := fun n y j =>
    (clip C ((ν[R j | ℱ n]) y) : ℂ) + Complex.I * (clip C ((ν[I j | ℱ n]) y) : ℂ)
  have hHn (n : ℕ) : Measurable[ℱ n] (Hn n) := by
    let : MeasurableSpace Y := ℱ n
    apply Measurable.of_eval
    intro j
    exact ((Complex.measurable_ofReal.comp ((continuous_clip C).measurable.comp
      stronglyMeasurable_condExp.measurable))).add
      (measurable_const.mul (Complex.measurable_ofReal.comp ((continuous_clip C).measurable.comp
        stronglyMeasurable_condExp.measurable)))
  have hBn (n : ℕ) (y : Y) : ‖Hn n y‖ ≤ 2*C := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    calc
      ‖Hn n y j‖ ≤ ‖(clip C ((ν[R j | ℱ n]) y) : ℂ)‖ +
          ‖Complex.I * (clip C ((ν[I j | ℱ n]) y) : ℂ)‖ := norm_add_le _ _
      _ = |clip C ((ν[R j | ℱ n]) y)| + |clip C ((ν[I j | ℱ n]) y)| := by
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2*C := by linarith [clip_bound hC ((ν[R j | ℱ n]) y), clip_bound hC ((ν[I j | ℱ n]) y)]
  have hconv : ∀ᵐ y ∂ν, Tendsto (fun n => Hn n y) atTop (𝓝 (H y)) := by
    have hr (j : Fin m) := (hRi j).tendsto_ae_condExp (hR j).stronglyMeasurable
    have hi (j : Fin m) := (hIi j).tendsto_ae_condExp (hI j).stronglyMeasurable
    filter_upwards [ae_all_iff.mpr hr, ae_all_iff.mpr hi] with y hyr hyi
    apply tendsto_pi_nhds.mpr
    intro j
    have hr' := (continuous_clip C).continuousAt.tendsto.comp (hyr j)
    have hi' := (continuous_clip C).continuousAt.tendsto.comp (hyi j)
    rw [clip_eq (hRB j y)] at hr'
    rw [clip_eq (hIB j y)] at hi'
    have ht := (Complex.continuous_ofReal.continuousAt.tendsto.comp hr').add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hi').const_mul Complex.I)
    convert ht using 1
    · rfl
    · simp only [R, I, Complex.re_add_im, mul_comm Complex.I]
  have hdist (n : ℕ) (y : Y) : dist (H y) (Hn n y)^2 ≤ (3*C)^2 := by
    have hd : dist (H y) (Hn n y) ≤ 3*C :=
      (dist_le_norm_add_norm _ _).trans (by linarith [hbound y, hBn n y])
    exact pow_le_pow_left₀ dist_nonneg hd 2
  have hint (n : ℕ) : Integrable (fun y => dist (H y) (Hn n y)^2) ν :=
    Integrable.of_bound ((hHm.dist ((hHn n).mono (ℱ.le n) le_rfl)).pow_const 2).aestronglyMeasurable
      ((3*C)^2) (Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs, abs_sq] using hdist n y)
  refine ⟨Hn, hHn, hBn, hint, ?_⟩
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (f := fun _ : Y => (0 : ℝ)) (fun _ : Y => (3*C)^2)
    (fun n => (hint n).aestronglyMeasurable) (integrable_const _) (fun n =>
      Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, abs_sq] using hdist n y)
    (hconv.mono fun y hy => by
      have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => H y) atTop (𝓝 (H y))).dist hy).pow 2
      simpa only [dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht)

/-- At a generated limit factor, one earlier factor carries a bounded
finite-vector approximant, with a pointwise bounded measurable representative. -/
theorem generated_factor_approximation
    {Z : ℕ → Type*} [∀ n, MeasurableSpace (Z n)]
    (ν : Measure Y) [IsProbabilityMeasure ν] (p : ∀ n, Y → Z n)
    (hp : ∀ n, Measurable (p n))
    (hmono : Monotone (fun n => (inferInstance : MeasurableSpace (Z n)).comap (p n)))
    (hgen : (⨆ n, (inferInstance : MeasurableSpace (Z n)).comap (p n)) = mY)
    (m : ℕ) (H : Y → Fin m → ℂ) (hH : Measurable H)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, ‖H y‖ ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∃ H₀ : Z n → Fin m → ℂ, Measurable H₀ ∧ (∀ z, ‖H₀ z‖ ≤ 2*C) ∧
      Integrable (fun y => dist (H y) (H₀ (p n y))^2) ν ∧
      (∫ y, dist (H y) (H₀ (p n y))^2 ∂ν) < ε^2 := by
  classical
  let ℱ : Filtration ℕ mY := ⟨fun n => (inferInstance : MeasurableSpace (Z n)).comap (p n),
    hmono, fun n => (hp n).comap_le⟩
  have hHg : Measurable[⨆ n, ℱ n] H := by
    change Measurable[⨆ n, (inferInstance : MeasurableSpace (Z n)).comap (p n)] H
    rwa [hgen]
  obtain ⟨Hn, hHn, hBn, hint, hlim⟩ := bounded_vector_approximation ν ℱ m H hHg C hC hbound
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (sq_pos_of_pos hε))).exists
  obtain ⟨H', hH', heq⟩ := (hHn n).exists_eq_measurable_comp
  let H₀ : Z n → Fin m → ℂ := fun z => if ‖H' z‖ ≤ 2*C then H' z else 0
  have hH₀ : Measurable H₀ := hH'.piecewise (measurableSet_le hH'.norm measurable_const) measurable_const
  have hB₀ (z : Z n) : ‖H₀ z‖ ≤ 2*C := by
    by_cases hz : ‖H' z‖ ≤ 2*C
    · simpa only [H₀, ite_eq_left hz] using hz
    · simp only [H₀, ite_eq_right hz, norm_zero]; positivity
  have heq₀ (y : Y) : H₀ (p n y) = Hn n y := by
    have hy := congrFun heq y
    simp only [Function.comp_apply] at hy
    have hb : ‖H' (p n y)‖ ≤ 2*C := hy ▸ hBn n y
    simpa only [H₀, ite_eq_left hb] using hy.symm
  refine ⟨n, H₀, hH₀, hB₀, ?_, ?_⟩
  · simpa only [heq₀] using hint n
  · simpa only [heq₀] using hn

end EuclideanFiveColor.LimitDensity

namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MulAction K X] [MulAction K Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MulAction K X] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma bounded_phase_encoding
    (μ : Measure X) [IsProbabilityMeasure μ] (p : X → Y) (b : X → D)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i)) :
    ∃ H : Y → Fin m → ℂ, Measurable H ∧ (∃ A : ℝ, 0 ≤ A ∧ ∀ y, ‖H y‖ ≤ A) ∧
      H =ᵐ[μ.map p] PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval 1 d : ℂ)) m := by
  classical
  let H₀ : Y → Fin m → ℂ := PhaseEncoding.kernelEncoding (condDistrib b p μ)
    (fun d => (eval 1 d : ℂ)) m
  have hH₀ : Measurable H₀ :=
    PhaseEncoding.measurable_kernelEncoding _ _ (measurable_eval_coe 1) m
  obtain ⟨A, hA⟩ := PhaseEncoding.exists_encoding_bound m
  have hHB : ∀ᵐ y ∂μ.map p, ‖H₀ y‖ ≤ max A 0 := by
    filter_upwards [hg] with y hy
    have he := PhaseEncoding.kernelEncoding_eq_encoding (condDistrib b p μ) (eval 1) m hm y (g y) hy
    change ‖PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval 1 d : ℂ)) m y‖ ≤ max A 0
    rw [he]
    exact (hA (fun i => eval 1 (g y i))).trans (le_max_left _ _)
  let H : Y → Fin m → ℂ := fun y => if ‖H₀ y‖ ≤ max A 0 then H₀ y else 0
  have hH : Measurable H := hH₀.piecewise (measurableSet_le hH₀.norm measurable_const) measurable_const
  have hHbound : ∀ y, ‖H y‖ ≤ max A 0 := by
    intro y
    by_cases hy : ‖H₀ y‖ ≤ max A 0
    · simpa only [H, ite_eq_left hy] using hy
    · simp only [H, ite_eq_right hy, norm_zero]
      exact le_max_right _ _
  exact ⟨H, hH, ⟨max A 0, le_max_right _ _, hHbound⟩, hHB.mono fun y hy => ite_eq_left hy⟩

end

open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal

end PlaneFiveColor.Spectral

namespace EuclideanFiveColor.ConditionalBase
open MeasureTheory ProbabilityTheory
variable {X Y G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]
lemma condDistrib_given_const (μ : Measure X) [IsProbabilityMeasure μ]
    (b : X → G) (hb : Measurable b) (y₀ : Y) :
    condDistrib b (fun _ => y₀) μ y₀ = μ.map b := by
  have h := condDistrib_comp_map (μ := μ) (X := fun _ : X => y₀) measurable_const.aemeasurable hb.aemeasurable
  simpa only [Measure.map_const, measure_univ, one_smul,
    Measure.dirac_bind (condDistrib b (fun _ => y₀) μ).measurable] using h

lemma prod_given_const (μ : Measure X) [IsProbabilityMeasure μ]
    (b : X → G) (hb : Measurable b) (y₀ : Y) :
    ((condDistrib b (fun _ => y₀) μ ×ₖ condDistrib b (fun _ => y₀) μ) ∘ₘ μ.map (fun _ => y₀)) =
      (μ.map b).prod (μ.map b) := by
  rw [Measure.map_const, measure_univ, one_smul,
    Measure.dirac_bind (condDistrib b (fun _ => y₀) μ ×ₖ condDistrib b (fun _ => y₀) μ).measurable,
    Kernel.prod_apply, condDistrib_given_const μ b hb y₀]
end EuclideanFiveColor.ConditionalBase

namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory EuclideanFiveColor
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
lemma relative_singularity_base (μ : Measure X) [IsProbabilityMeasure μ]
    (b : X → D) (hb : Measurable b) (y₀ : Y) (hw : IsWild (μ.map b)) :
    DifferenceFourier.differenceLaw (μ.map (fun _ : X => y₀))
      (condDistrib b (fun _ : X => y₀) μ) C = 0 := by
  let : IsProbabilityMeasure (μ.map b) := Measure.isProbabilityMeasure_map (by fun_prop)
  rw [DifferenceFourier.differenceLaw, ConditionalBase.prod_given_const μ b hb y₀,
    Measure.map_apply (f := fun p : D × D => p.1 / p.2) (measurable_fst.div measurable_snd) measurableSet_C]
  exact wild_independent_difference (μ.map b) hw
end
open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal

end PlaneFiveColor.Spectral
namespace EuclideanFiveColor.CompactApproximation
open MeasureTheory
variable {K Y : Type*} [SMul K Y] [MeasurableSpace Y] [MeasurableConstSMul K Y]
lemma scalar_identity (ν : Measure Y) : Scalar (K := K) ν id := by
  intro H hH hB ε hε
  obtain ⟨B,hB⟩ := hB
  refine ⟨1, max 0 B, 1, fun _ _ => 1, le_max_left _ _, by norm_num,
    fun _ => measurable_const, fun _ => by simp, ?_⟩
  intro k
  refine ⟨fun y _ => H (k • y), Measurable.of_eval (fun _ => hH.comp (measurable_const_smul k)),
    fun y => ?_, ?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg (le_max_left _ _)]
    exact fun _ => (hB _).trans (le_max_right _ _)
  · simp
  · simpa using sq_pos_of_pos hε
end EuclideanFiveColor.CompactApproximation

namespace PlaneFiveColor.Spectral

section
open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [StandardBorelSpace W] [Nonempty W]
  [MulAction K X] [MulAction K Y] [MulAction K W]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K W]

omit [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace W] [Nonempty W]
  [StandardBorelSpace Y] [Nonempty Y] [MulAction K W] [MeasurableConstSMul K W] in
lemma ambient_encoding_of_at (μ : Measure X) [IsProbabilityMeasure μ]
    [ErgodicSMul K X μ] (p : X → Y) (q : X → W) (b : X → D)
    (hp : Measurable p) (hb : Measurable b)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (m : ℕ) (H : Y → Fin m → ℂ)
    (hHeq : H =ᵐ[μ.map p] PhaseEncoding.kernelEncoding (condDistrib b p μ)
      (fun d => (eval 1 d : ℂ)) m)
    (γ : ℝ) (ha : CompactApproximation.At (K := K) μ q m (H ∘ p) γ) :
    AmbientEncodingAt μ p q b m γ := by
  obtain ⟨r, B, C, Hf, hB, hC, _hHm, hHf, ha⟩ := ha
  refine ⟨r, B, C, Hf, hB, hC, hHf, ?_⟩
  intro k
  obtain ⟨a, _ham, hab, hai, hae⟩ := ha k
  have hker := KernelSupport.condDistrib_equivariant μ b p hb hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun d : D => k • d)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hbe k)
  have hcov := PhaseEncoding.kernelEncoding_covariance (μ.map p) (condDistrib b p μ)
    (fun y : Y => k • y) (fun d : D => k • d) (measurable_const_smul k)
    (fun d => (eval 1 d : ℂ)) (measurable_eval_coe 1) m hker
  have heq : ∀ᵐ x ∂μ, (H ∘ p) (k • x) =
      PhaseEncoding.kernelEncoding (condDistrib b p μ)
        (fun d => (eval (kCoeff k) d : ℂ)) m (p x) := by
    have he := (measurePreserving_smul k μ).quasiMeasurePreserving.ae
      (ae_of_ae_map hp.aemeasurable hHeq)
    filter_upwards [he, hpe k, ae_of_ae_map hp.aemeasurable hcov] with x hx hp' hc'
    dsimp only [Function.comp_apply]
    rw [hx, hp']
    simpa only [Function.comp_def, eval_smul_one] using hc'
  have he : (fun x => dist ((H ∘ p) (k • x)) (∑ i, a (q x) i • Hf i x)^2) =ᵐ[μ]
      (fun x => dist (PhaseEncoding.kernelEncoding (condDistrib b p μ)
        (fun d => (eval (kCoeff k) d : ℂ)) m (p x)) (∑ i, a (q x) i • Hf i x)^2) :=
    heq.mono fun x hx => by dsimp only at hx ⊢; rw [hx]
  exact ⟨a, hab, hai.congr he, by rw [← integral_congr_ae he]; exact hae⟩

omit [StandardBorelSpace Y] [Nonempty Y] in
/-- Relative singularity is closed under L² approximation by earlier factors,
with all comparisons made on the ambient probability space. This form avoids
choosing exactly commuting representatives at a countable tower join. -/
theorem relative_singularity_approximation
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → D) (p : X → Y) (hd : Measurable d) (hp : Measurable p)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hwild : IsWild (μ.map d))
    (ha : ∀ (m : ℕ) (H : Y → Fin m → ℂ), Measurable H →
      (∃ A : ℝ, ∀ y, ‖H y‖ ≤ A) → ∀ ε : ℝ, 0 < ε →
      ∃ q : X → W, Measurable q ∧
        (∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) ∧
        (∀ b : X → D, Measurable b →
          (∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x) → IsWild (μ.map b) →
          DifferenceFourier.differenceLaw (μ.map q) (condDistrib b q μ) C = 0) ∧
        ∃ H₀ : W → Fin m → ℂ, Measurable H₀ ∧ (∃ A : ℝ, ∀ w, ‖H₀ w‖ ≤ A) ∧
          Integrable (fun x => dist (H (p x)) (H₀ (q x))^2) μ ∧
          (∫ x, dist (H (p x)) (H₀ (q x))^2 ∂μ) < ε^2) :
    DifferenceFourier.differenceLaw (μ.map p) (condDistrib d p μ) C = 0 := by
  let : IsProbabilityMeasure (μ.map p) := Measure.isProbabilityMeasure_map (by fun_prop)
  by_contra hn
  have hpos : 0 < RelativeCenters.differenceLaw (μ.map p) (condDistrib d p μ) C :=
    pos_iff_ne_zero.mpr hn
  obtain ⟨b, hb, hbe, hbw, a, ha', hf⟩ := exact_finite_center_reduction μ d p hd hp hde hpe hwild hpos
  obtain ⟨m, hm, g, hg⟩ := UniformEnumeration.constant_uniform_lists (μ.map p)
    (condDistrib b p μ) a ha' (hf.mono fun y ⟨S, hS, hSa, hSupp, hcS, _⟩ =>
      ⟨S, hS, hSa, hSupp, hcS⟩)
  obtain ⟨ρ, c, N, hρ, hc, hN, harc⟩ := SmallArc.exists_small_arc_constants m hm
  let γ : ℝ := ((ρ^m/(m : ℝ))/100)/100
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨H, hH, ⟨A, _hA, hHB⟩, hHeq⟩ := bounded_phase_encoding μ p b m hm g hg
  obtain ⟨q, hq, hqe, hprev, H₀, hH₀, hH₀B, hi, he⟩ := ha m H hH ⟨A,hHB⟩ (γ/2) (by positivity)
  let : IsProbabilityMeasure (μ.map q) := Measure.isProbabilityMeasure_map (by fun_prop)
  have happ := CompactApproximation.lift_at μ q id hq measurable_id
    (fun k => measurePreserving_smul k μ) hqe m (H ∘ p) H₀ (hH.comp hp) hH₀ hH₀B γ hγ hi he
    (CompactApproximation.vector_of_scalar (μ.map q) id measurable_id
      (CompactApproximation.scalar_identity (K := K) (μ.map q)))
  have henc := ambient_encoding_of_at μ p q b hp hb hpe hbe m H hHeq γ happ
  have hpwild : IsWild (DifferenceFourier.differenceLaw (μ.map q) (condDistrib b q μ)) :=
    ⟨relative_difference_invariant μ b q hb hq hbe hqe, hprev b hb hbe hbw⟩
  exact ambient_uniform_precision_contradiction μ p q b hp hq hb m hm g hg
    hpwild ρ c N hρ hc hN harc henc

end
open MeasureTheory ProbabilityTheory EuclideanFiveColor
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MulAction K X] [MulAction K Y] [MulAction K W]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [MeasurableConstSMul K W]

lemma universalGood_of_factor [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (p : X → Y) (q : X → W) (r : W → Y)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hqe : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (he : p =ᵐ[μ] r ∘ q) (hg : UniversalGood μ q) : UniversalGood μ p := by
  intro d hd hde hw
  apply relative_singularity_approximation (W := W) μ d p hd hp hde hpe hw
  intro m H hH hB ε hε
  refine ⟨q, hq, hqe, hg, H ∘ r, hH.comp hr, ?_, ?_, ?_⟩
  · obtain ⟨B,hB⟩ := hB
    exact ⟨B, fun w => hB _⟩
  · apply (integrable_zero X ℝ μ).congr
    filter_upwards [he] with x hx
    simp only [hx, Function.comp_def, dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Pi.zero_apply]
  · have he0 : (fun x => dist (H (p x)) ((H ∘ r) (q x))^2) =ᵐ[μ] 0 := by
      filter_upwards [he] with x hx
      simp only [hx, Function.comp_def, dist_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Pi.zero_apply]
    rw [integral_congr_ae he0]
    simp only [Pi.zero_apply, integral_zero]
    exact sq_pos_of_pos hε

end PlaneFiveColor.Spectral

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Kernels
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.RelativeProduct.law_probability_add _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory

/-! Bounded integral kernels yield finite-module orbit approximation.
This implements the compact-tower construction without spectral projections:
approximate the invariant kernel by finite rectangles first. -/
namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma norm_integral_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℂ) (hf : Integrable f μ)
    (hf₂ : Integrable (fun x => ‖f x‖^2) μ) :
    ‖∫ x, f x ∂μ‖^2 ≤ ∫ x, ‖f x‖^2 ∂μ := by
  let a := ∫ x, ‖f x‖ ∂μ
  have ha : 0 ≤ a := integral_nonneg fun _ => norm_nonneg _
  have hvar : 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - a^2 := by
    have h : (0 : ℝ) ≤ ∫ x, (‖f x‖-a)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (‖f x‖-a))
    have he : (fun x => (‖f x‖-a)^2) = fun x => ‖f x‖^2 - (2*a)*‖f x‖ + a^2 := by
      funext x; ring
    rw [he, integral_add (f := fun x => ‖f x‖^2 - (2*a)*‖f x‖) (g := fun _ => a^2) (hf₂.sub (hf.norm.const_mul (2*a))) (integrable_const (a^2)),
      integral_sub (f := fun x => ‖f x‖^2) (g := fun x => (2*a)*‖f x‖) hf₂ (hf.norm.const_mul (2*a)), integral_const_mul] at h
    simp only [integral_const, probReal_univ, one_smul] at h
    change 0 ≤ (∫ x, ‖f x‖^2 ∂μ) - (2*a)*a + a^2 at h
    nlinarith
  have hn : ‖∫ x, f x ∂μ‖ ≤ a := norm_integral_le_integral_norm f
  nlinarith [norm_nonneg (∫ x, f x ∂μ)]

lemma measurable_fiberMean (κ : Kernel X Y) [IsSFiniteKernel κ]
    (F : X × Y → ℂ) (hF : Measurable F) : Measurable (fiberMean κ F) :=
  hF.stronglyMeasurable.integral_kernel_prod_right'.measurable

lemma fiberMean_bound (κ : Kernel X Y) [IsMarkovKernel κ]
    (F : X × Y → ℂ) (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (x : X) :
    ‖fiberMean κ F x‖ ≤ C := by
  simpa only [fiberMean, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := κ x)
      (Filter.Eventually.of_forall fun y => hC (x,y))

lemma fiberMean_l2_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Y) [IsMarkovKernel κ] (F : X × Y → ℂ)
    (hF : Measurable F) (C : ℝ) (hFC : ∀ z, ‖F z‖ ≤ C) :
    (∫ x, ‖fiberMean κ F x‖^2 ∂μ) ≤ ∫ z, ‖F z‖^2 ∂(μ ⊗ₘ κ) := by
  have hsq (z : X × Y) : ‖F z‖^2 ≤ C^2 := pow_le_pow_left₀ (norm_nonneg _) (hFC z) 2
  have hi : Integrable (fun z => ‖F z‖^2) (μ ⊗ₘ κ) :=
    Integrable.of_bound (hF.norm.pow_const 2).aestronglyMeasurable (C^2)
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_sq] using hsq z)
  rw [Measure.integral_compProd hi]
  apply integral_mono
  · exact Integrable.of_bound ((measurable_fiberMean κ F hF).norm.pow_const 2).aestronglyMeasurable
      (C^2) (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_sq] using
          pow_le_pow_left₀ (norm_nonneg _) (fiberMean_bound κ F C hFC x) 2)
  · have hm := (hF.norm.pow_const 2).stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
    exact Integrable.of_bound hm.aestronglyMeasurable (C^2) (Filter.Eventually.of_forall fun x => by
      have hb := norm_integral_le_of_norm_le_const (μ := κ x)
        (f := fun y => ‖F (x,y)‖^2) (C := C^2)
        (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs, abs_sq] using hsq (x,y))
      simpa only [probReal_univ, mul_one] using hb)

  · intro x
    apply norm_integral_sq
    · exact Integrable.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        C (Filter.Eventually.of_forall fun y => hFC (x,y))
    · exact Integrable.of_bound ((hF.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable
        (C^2) (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs, abs_sq] using hsq (x,y))

lemma kernel_apply_error_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Y) [IsMarkovKernel κ] (L P : X × Y → ℂ)
    (hL : Measurable L) (hP : Measurable P) (C : ℝ)
    (hLC : ∀ z, ‖L z‖ ≤ C) (hPC : ∀ z, ‖P z‖ ≤ C)
    (f : Y → ℂ) (hf : Measurable f) (hfB : ∀ y, ‖f y‖ ≤ 1) :
    (∫ x, ‖fiberMean κ (fun z => L z * f z.2) x -
      fiberMean κ (fun z => P z * f z.2) x‖^2 ∂μ) ≤
        ∫ z, ‖L z - P z‖^2 ∂(μ ⊗ₘ κ) := by
  have hLP (z : X × Y) : ‖L z - P z‖ ≤ 2*C :=
    (norm_sub_le _ _).trans (by linarith [hLC z, hPC z])
  have hF : Measurable (fun z : X × Y => (L z - P z) * f z.2) :=
    (hL.sub hP).mul (hf.comp measurable_snd)
  have hFB (z : X × Y) : ‖(L z - P z) * f z.2‖ ≤ 2*C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg _)).trans (by simpa using hLP z)
  have he (x : X) : fiberMean κ (fun z => L z * f z.2) x -
      fiberMean κ (fun z => P z * f z.2) x =
        fiberMean κ (fun z => (L z - P z) * f z.2) x := by
    dsimp [fiberMean]
    simp_rw [sub_mul]
    rw [integral_sub]
    · exact Integrable.of_bound ((hL.comp (measurable_const.prodMk measurable_id)).mul hf).aestronglyMeasurable
        C (Filter.Eventually.of_forall fun y => by
          rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (hfB y) (norm_nonneg _)).trans (by simpa using hLC (x,y)))
    · exact Integrable.of_bound ((hP.comp (measurable_const.prodMk measurable_id)).mul hf).aestronglyMeasurable
        C (Filter.Eventually.of_forall fun y => by
          rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (hfB y) (norm_nonneg _)).trans (by simpa using hPC (x,y)))
  simp_rw [he]
  apply (fiberMean_l2_bound μ κ _ hF (2*C) hFB).trans
  apply integral_mono
  · exact Integrable.of_bound (hF.norm.pow_const 2).aestronglyMeasurable ((2*C)^2)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) (hFB z) 2)
  · exact Integrable.of_bound ((hL.sub hP).norm.pow_const 2).aestronglyMeasurable ((2*C)^2)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) (hLP z) 2)
  · intro z
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg (L z - P z))

end EuclideanFiveColor.KernelCompact

/-! Bounded finite-dimensional L² approximation at a generated limit factor.
The filtration is the pullback of an increasing sequence of earlier factors;
no martingale convergence theorem beyond Mathlib is assumed. -/

namespace EuclideanFiveColor.RectangleDensity
open MeasureTheory
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X] [MeasurableSpace.CountablyGenerated Y]

lemma measurable_pairCode (n : ℕ) : Measurable (pairCode (X := X) (Y := Y) n) :=
  ((measurable_code n).comp measurable_fst).prodMk ((measurable_code n).comp measurable_snd)

lemma pairCode_mono : Monotone (fun n =>
    (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) := by
  intro n m hnm
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun z : Code m × Code m => (fun i : Fin n => z.1 (Fin.castLE hnm i), fun i : Fin n => z.2 (Fin.castLE hnm i)))
    (measurable_of_countable _)
  rfl

lemma pairCode_generates : (⨆ n,
    (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) =
      (inferInstance : MeasurableSpace (X × Y)) := by
  classical
  apply le_antisymm (iSup_le fun n => (measurable_pairCode n).comap_le)
  let m := ⨆ n, (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)
  have hp (n : ℕ) : Measurable[m] (pairCode (X := X) (Y := Y) n) :=
    (comap_measurable _).mono (by exact le_iSup (fun n =>
      (inferInstance : MeasurableSpace (Code n × Code n)).comap (pairCode (X := X) (Y := Y) n)) n) le_rfl
  have hx : @Measurable (X × Y) X m _ Prod.fst := by
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence X]
    apply measurable_generateFrom
    rintro _ ⟨n, rfl⟩
    have h : Measurable[m] (fun z : X × Y => (pairCode (X := X) (Y := Y) (n+1) z).1 ⟨n, by omega⟩) :=
      (measurable_pi_apply _).comp (measurable_fst.comp (hp (n+1)))
    have hs := h (measurableSet_singleton true)
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [pairCode, code]
  have hy : @Measurable (X × Y) Y m _ Prod.snd := by
    rw [← MeasurableSpace.generateFrom_natGeneratingSequence Y]
    apply measurable_generateFrom
    rintro _ ⟨n, rfl⟩
    have h : Measurable[m] (fun z : X × Y => (pairCode (X := X) (Y := Y) (n+1) z).2 ⟨n, by omega⟩) :=
      (measurable_pi_apply _).comp (measurable_snd.comp (hp (n+1)))
    have hs := h (measurableSet_singleton true)
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [pairCode, code]
  have hi := (hx.prodMk hy).comap_le
  have hfun : (fun z : X × Y => (z.1, z.2)) = id := rfl
  rw [hfun] at hi
  simpa only [MeasurableSpace.comap_id] using hi

/-- Bounded finite rectangle approximation for any probability coupling, not
only a product measure. The common sup bound is twice the original bound. -/
theorem bounded_rectangles (ν : Measure (X × Y)) [IsProbabilityMeasure ν]
    (L : X × Y → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Code n × Code n → ℂ),
      (∀ z, ‖a z‖ ≤ 2*C) ∧
      Integrable (fun z => ‖L z - a (pairCode n z)‖^2) ν ∧
      (∫ z, ‖L z - a (pairCode n z)‖^2 ∂ν) < ε^2 := by
  let H : X × Y → Fin 1 → ℂ := fun z _ => L z
  have hH : Measurable H := Measurable.of_eval fun _ => hL
  have hHB (z : X × Y) : ‖H z‖ ≤ C := by
    rw [pi_norm_le_iff_of_nonneg hC]; intro i; exact hLC z
  obtain ⟨n, H₀, _, hB, hi, he⟩ := LimitDensity.generated_factor_approximation ν
    (fun n => pairCode (X := X) (Y := Y) n) measurable_pairCode
    pairCode_mono pairCode_generates 1 H hH C hC hHB ε hε
  have hd (z : X × Y) : dist (H z) (H₀ (pairCode n z)) = ‖L z - H₀ (pairCode n z) 0‖ := by
    rw [dist_eq_norm]
    have heq : H z - H₀ (pairCode n z) = fun _ : Fin 1 => L z - H₀ (pairCode n z) 0 := by
      funext i
      have : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    rw [heq, pi_norm_const]
  refine ⟨n, fun z => H₀ z 0, fun z => (norm_le_pi_norm (H₀ z) 0).trans (hB z), ?_, ?_⟩
  · simpa only [hd] using hi
  · simpa only [hd] using he

end EuclideanFiveColor.RectangleDensity

namespace EuclideanFiveColor.KernelCompact

section
open MeasureTheory ProbabilityTheory RectangleDensity
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X]

/-- Uniform finite bounded-module approximation to the image of the bounded
unit ball under an integral kernel. This is the compactness step of the
relative compact-factor construction, with no spectral decomposition. -/
theorem bounded_range_approximation (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℕ) (B C₀ : ℝ) (Hf : Fin r → X → ℂ),
      0 ≤ B ∧ 0 ≤ C₀ ∧ (∀ i, Measurable (Hf i)) ∧ (∀ x, ∑ i, ‖Hf i x‖ ≤ C₀) ∧
      ∀ f : X → ℂ, Measurable f → (∀ x, ‖f x‖ ≤ 1) →
        ∃ a : Y → Fin r → ℂ, Measurable a ∧ (∀ y, ‖a y‖ ≤ B) ∧
          Integrable (fun x => dist (∫ x', L (x,x') * f x' ∂κ (q x))
            (∑ i, a (q x) i * Hf i x)^2) μ ∧
          (∫ x, dist (∫ x', L (x,x') * f x' ∂κ (q x))
            (∑ i, a (q x) i * Hf i x)^2 ∂μ) < ε^2 := by
  classical
  let κ₀ := κ.comap q hq
  obtain ⟨n, c, hB, _, he⟩ := bounded_rectangles (μ ⊗ₘ κ₀) L hL C hC hLC ε hε
  let r := Fintype.card (Code n)
  let e : Fin r ≃ Code n := (Fintype.equivFin (Code n)).symm
  let Hf : Fin r → X → ℂ := fun i x => if code X n x = e i then 1 else 0
  have hHf (i : Fin r) : Measurable (Hf i) :=
    measurable_const.piecewise ((measurable_code n) (measurableSet_singleton (e i))) measurable_const
  have hHfB (i : Fin r) (x : X) : ‖Hf i x‖ ≤ 1 := by
    dsimp only [Hf]
    split_ifs <;> norm_num
  have hsumB (x : X) : ∑ i, ‖Hf i x‖ ≤ r := by
    calc
      ∑ i, ‖Hf i x‖ ≤ ∑ _ : Fin r, (1 : ℝ) := Finset.sum_le_sum fun i _ => hHfB i x
      _ = r := by simp
  refine ⟨r, 2*C, r, Hf, by positivity, by positivity, hHf, hsumB, ?_⟩
  intro f hf hfB
  let a : Y → Fin r → ℂ := fun y i => ∫ x', c (e i, code X n x') * f x' ∂κ y
  have hm (i : Fin r) : Measurable (fun x' => c (e i, code X n x') * f x') :=
    ((measurable_of_countable c).comp (measurable_const.prodMk (measurable_code n))).mul hf
  have hbound (i : Fin r) (x' : X) : ‖c (e i, code X n x') * f x'‖ ≤ 2*C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB x') (norm_nonneg _)).trans (by simpa using hB (e i, code X n x'))
  have ha : Measurable a := by
    apply Measurable.of_eval
    intro i
    exact (hm i).stronglyMeasurable.integral_kernel.measurable
  have haB (y : Y) : ‖a y‖ ≤ 2*C := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    simpa only [a, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (μ := κ y) (Filter.Eventually.of_forall (hbound i))
  let P : X × X → ℂ := fun z => c (pairCode n z)
  have hP : Measurable P := (measurable_of_countable c).comp (measurable_pairCode n)
  have hPB (z : X × X) : ‖P z‖ ≤ 2*C := hB _
  have hs (x : X) : (∑ i, a (q x) i * Hf i x) = fiberMean κ₀ (fun z => P z * f z.2) x := by
    rw [Finset.sum_eq_single (e.symm (code X n x))]
    · simp [a, Hf, fiberMean, P, pairCode, κ₀]
    · intro b _ hb
      have hn : code X n x ≠ e b := by
        intro hz
        exact hb (e.injective (by simpa using hz.symm))
      simp [Hf, hn]
    · simp
  have hfm : Measurable (fiberMean κ₀ (fun z => L z * f z.2)) :=
    measurable_fiberMean κ₀ _ (hL.mul (hf.comp measurable_snd))
  have hgm : Measurable (fiberMean κ₀ (fun z => P z * f z.2)) :=
    measurable_fiberMean κ₀ _ (hP.mul (hf.comp measurable_snd))
  have hfb (x : X) : ‖fiberMean κ₀ (fun z => L z * f z.2) x‖ ≤ C := by
    apply fiberMean_bound
    intro z
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg _)).trans (by simpa using hLC z)
  have hgb (x : X) : ‖fiberMean κ₀ (fun z => P z * f z.2) x‖ ≤ 2*C := by
    apply fiberMean_bound
    intro z
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB z.2) (norm_nonneg _)).trans (by simpa using hPB z)
  have hdist : Integrable (fun x =>
      dist (fiberMean κ₀ (fun z => L z * f z.2) x) (fiberMean κ₀ (fun z => P z * f z.2) x)^2) μ :=
    Integrable.of_bound ((hfm.dist hgm).pow_const 2).aestronglyMeasurable ((3*C)^2)
      (Filter.Eventually.of_forall fun x => by
        have hd : dist (fiberMean κ₀ (fun z => L z * f z.2) x) (fiberMean κ₀ (fun z => P z * f z.2) x) ≤ 3*C :=
          (dist_le_norm_add_norm _ _).trans (by linarith [hfb x, hgb x])
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ dist_nonneg hd 2)
  refine ⟨a, ha, haB, ?_, ?_⟩
  · simpa only [hs, fiberMean, κ₀, Kernel.comap_apply] using hdist
  · simp_rw [hs, dist_eq_norm]
    change (∫ x, ‖fiberMean κ₀ (fun z => L z * f z.2) x - fiberMean κ₀ (fun z => P z * f z.2) x‖^2 ∂μ) < ε^2
    exact (kernel_apply_error_bound μ κ₀ L P hL hP (2*C)
      (fun z => (hLC z).trans (by linarith)) hPB f hf hfB).trans_lt he

end
section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MeasurableConstSMul K Y] in
lemma applyKernel_covariance (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    (hLcov : ∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z)
    (f : X → ℂ) (hfm : Measurable f) (k : K) :
    (fun x => applyKernel κ q L f (k • x)) =ᵐ[μ]
      applyKernel κ q L (fun x => f (k • x)) := by
  have hc : ∀ᵐ x ∂μ, κ (k • q x) = (κ (q x)).map (fun x => k • x) :=
    ae_of_ae_map (μ := μ) (p := fun y => κ (k • y) = (κ y).map (fun x => k • x))
      hq.aemeasurable (hκcov k)
  have hl₀ := Measure.ae_ae_of_ae_compProd (μ := μ) (κ := κ.comap q hq)
    (p := fun z => L (k • z.1, k • z.2) = L z) (hLcov k)
  have hl : ∀ᵐ x ∂μ, ∀ᵐ x' ∂κ (q x), L (k • x, k • x') = L (x,x') := by
    simpa only [Kernel.comap_apply] using hl₀
  filter_upwards [hqcov k, hc, hl] with x hqx hcx hlx
  dsimp [applyKernel]
  have hLf : Measurable (fun y => L (k • x,y) * f y) :=
    (hL.comp (measurable_const.prodMk measurable_id)).mul hfm
  rw [hqx, hcx, integral_map (measurable_const_smul k).aemeasurable hLf.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hlx] with x' hxx
  simp only [hxx]

end
section
open MeasureTheory ProbabilityTheory RectangleDensity
open scoped BigOperators
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated X]

lemma norm_sq_le_sub (z w : ℂ) : ‖z‖^2 ≤ ‖z-w‖^2 + 2*(z*star w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg w.re, sq_nonneg w.im]

/-- A nonzero bounded relative-product kernel has a nonzero image of a bounded
measurable function. Finite rectangle density replaces a spectral theorem. -/
theorem exists_nonzero_image (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C) (hne : ¬ L =ᵐ[μ ⊗ₘ κ.comap q hq] 0) :
    ∃ f : X → ℂ, Measurable f ∧ (∀ x, ‖f x‖ ≤ 1) ∧
      ¬ applyKernel κ q L f =ᵐ[μ] 0 := by
  classical
  by_contra h
  push Not at h
  let κ₀ := κ.comap q hq
  let ν := μ ⊗ₘ κ₀
  have hL₂ : Integrable (fun z => ‖L z‖^2) ν :=
    Integrable.of_bound (hL.norm.pow_const 2).aestronglyMeasurable (C^2)
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_sq] using pow_le_pow_left₀ (norm_nonneg _) (hLC z) 2)
  have hsmall : ∀ ε : ℝ, 0 < ε → (∫ z, ‖L z‖^2 ∂ν) < ε := by
    intro ε hε
    obtain ⟨n, c, hc, hi, he⟩ := bounded_rectangles ν L hL C hC hLC
      (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    rw [Real.sq_sqrt hε.le] at he
    let P : X × X → ℂ := fun z => c (pairCode n z)
    have hP : Measurable P := (measurable_of_countable c).comp (measurable_pairCode n)
    let d : ℝ := 2*C+1
    have hd : 0 < d := by dsimp [d]; positivity
    let f : Code n → X → ℂ := fun i x => star (c (i,code X n x)) / (d : ℂ)
    have hfm (i : Code n) : Measurable (f i) :=
      (Complex.continuous_conj.measurable.comp ((measurable_of_countable c).comp (measurable_const.prodMk (measurable_code n)))).div_const _
    have hfb (i : Code n) (x : X) : ‖f i x‖ ≤ 1 := by
      dsimp only [f]
      rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      apply (div_le_one hd).mpr
      exact (hc _).trans (by dsimp [d]; linarith)
    have hzero : ∀ᵐ x ∂μ, ∀ i : Code n, applyKernel κ q L (f i) x = 0 :=
      ae_all_iff.mpr fun i => h (f i) (hfm i) (hfb i)
    have hLP : Integrable (fun z => L z * star (P z)) ν :=
      Integrable.of_bound (hL.mul (Complex.continuous_conj.measurable.comp hP)).aestronglyMeasurable (C*(2*C))
        (Filter.Eventually.of_forall fun z => by
          rw [norm_mul, norm_star]
          exact mul_le_mul (hLC z) (hc _) (norm_nonneg _) hC)
    have hz : (∫ z, L z * star (P z) ∂ν) = 0 := by
      rw [Measure.integral_compProd hLP]
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with x hx
      have heq : (fun x' => L (x,x') * star (P (x,x'))) =
          fun x' => (L (x,x') * f (code X n x) x') * (d : ℂ) := by
        funext x'
        dsimp [P,pairCode,f]
        have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
        field_simp [hdc]
      rw [heq, integral_mul_const]
      change applyKernel κ q L (f (code X n x)) x * (d : ℂ) = 0
      rw [hx, zero_mul]
    have hr : (∫ z, RCLike.re (L z * star (P z)) ∂ν) = 0 := by
      rw [integral_re hLP, hz]; rfl
    have hb := integral_mono hL₂ (hi.add (hLP.re.const_mul 2))
      (fun z => norm_sq_le_sub (L z) (P z))
    dsimp only [Pi.add_apply] at hb
    rw [integral_add hi (hLP.re.const_mul 2), integral_const_mul, hr, mul_zero, add_zero] at hb
    exact hb.trans_lt he
  have hz : (∫ z, ‖L z‖^2 ∂ν) = 0 := by
    apply le_antisymm
    · exact le_of_forall_pos_le_add fun ε hε => le_of_lt (by simpa using hsmall ε hε)
    · exact integral_nonneg fun z => sq_nonneg _
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg ‖L z‖) hL₂).mp hz
  apply hne
  filter_upwards [hae] with z hz
  apply norm_eq_zero.mp
  exact sq_eq_zero_iff.mp hz

end

section
open MeasureTheory ProbabilityTheory Filter
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma measurable_applyKernel (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (hq : Measurable q) (L : X × X → ℂ) (hL : Measurable L)
    (f : X → ℂ) (hf : Measurable f) : Measurable (applyKernel κ q L f) :=
  measurable_fiberMean (κ.comap q hq) _ (hL.mul (hf.comp measurable_snd))

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma applyKernel_bound (κ : Kernel Y X) [IsMarkovKernel κ]
    (q : X → Y) (L : X × X → ℂ) (C : ℝ) (hLC : ∀ z, ‖L z‖ ≤ C)
    (f : X → ℂ) (hfB : ∀ x, ‖f x‖ ≤ 1) (x : X) : ‖applyKernel κ q L f x‖ ≤ C := by
  have hb (x' : X) : ‖L (x,x') * f x'‖ ≤ C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB _) (norm_nonneg _)).trans (by simpa using hLC (x,x'))
  change ‖∫ x', L (x,x') * f x' ∂κ (q x)‖ ≤ C
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := κ (q x)) (C := C) (Eventually.of_forall hb)

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma exists_invariant_set (ν : Measure (X × X))
    [SMulInvariantMeasure K (X × X) ν] (hn : ¬ ErgodicSMul K (X × X) ν) :
    ∃ s : Set (X × X), MeasurableSet s ∧
      (∀ k : K, (fun z : X × X => k • z) ⁻¹' s =ᵐ[ν] s) ∧
      ¬ EventuallyConst s (ae ν) := by
  classical
  by_contra! h
  apply hn
  exact ⟨fun hs hi => h _ hs hi⟩

omit [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma indicator_not_constant (ν : Measure (X × X)) (s : Set (X × X))
    (hn : ¬ EventuallyConst s (ae ν)) (c : ℂ) :
    ¬ s.indicator (fun _ => (1 : ℂ)) =ᵐ[ν] (fun _ => c) := by
  classical
  intro he
  apply hn
  change EventuallyConst s (ae ν)
  rw [eventuallyConst_set]
  by_cases hc : c = 0
  · right
    filter_upwards [he] with x hx
    simpa [hc] using hx
  · left
    filter_upwards [he] with x hx
    by_contra hxs
    simp only [Set.indicator_of_notMem hxs] at hx
    exact hc hx.symm

end
open MeasureTheory ProbabilityTheory Filter
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MeasurableConstSMul K Y] in
lemma row_constant (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hLC : ∀ z, ‖L z‖ ≤ C)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    (hLcov : ∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z) :
    (fun x => ∫ x', L (x,x') ∂κ (q x)) =ᵐ[μ]
      (fun _ => ∫ z, L z ∂μ ⊗ₘ κ.comap q hq) := by
  have hfm := measurable_applyKernel κ q hq L hL (fun _ => 1) measurable_const
  have hi : ∀ k : K, ∀ᵐ x ∂μ,
      applyKernel κ q L (fun _ => 1) (k • x) = applyKernel κ q L (fun _ => 1) x :=
    fun k => applyKernel_covariance μ κ q hq L hL hqcov hκcov hLcov _ measurable_const k
  obtain ⟨c, hc⟩ := ErgodicSupport.ae_eq_const_of_invariant hfm hi
  have hc' : (fun x => ∫ x', L (x,x') ∂κ (q x)) =ᵐ[μ] (fun _ => c) := by
    filter_upwards [hc] with x hx
    simpa only [applyKernel, mul_one] using hx
  have hLi : Integrable L (μ ⊗ₘ κ.comap q hq) :=
    Integrable.of_bound hL.aestronglyMeasurable C (Eventually.of_forall hLC)
  have he : (∫ z, L z ∂μ ⊗ₘ κ.comap q hq) = c := by
    rw [Measure.integral_compProd hLi]
    change (∫ x, (∫ x', L (x,x') ∂κ (q x)) ∂μ) = c
    rw [integral_congr_ae hc']
    simp
  simpa only [he] using hc'

omit [MeasurableConstSMul K Y] in
lemma centered_kernel (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (hswap : (μ ⊗ₘ κ.comap q hq).map Prod.swap = μ ⊗ₘ κ.comap q hq)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    [SMulInvariantMeasure K (X × X) (μ ⊗ₘ κ.comap q hq)]
    (hn : ¬ ErgodicSMul K (X × X) (μ ⊗ₘ κ.comap q hq)) :
    ∃ L : X × X → ℂ, Measurable L ∧ (∀ z, ‖L z‖ ≤ 2) ∧
      (∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z) ∧
      ¬ L =ᵐ[μ ⊗ₘ κ.comap q hq] 0 ∧
      (∀ᵐ x ∂μ, (∫ x', L (x,x') ∂κ (q x)) = 0) ∧
      (∀ᵐ x ∂μ, (∫ x', L (x',x) ∂κ (q x)) = 0) := by
  classical
  let ν := μ ⊗ₘ κ.comap q hq
  obtain ⟨s, hs, hscov, hsn⟩ := exists_invariant_set ν hn
  let F : X × X → ℂ := s.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hs
  have hFB (z : X × X) : ‖F z‖ ≤ 1 := by
    dsimp [F]; by_cases hz : z ∈ s <;> simp [hz]
  have hFi : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable 1 (Eventually.of_forall hFB)
  have hFc : ∀ k : K, ∀ᵐ z ∂ν, F (k • z.1,k • z.2) = F z := by
    intro k; filter_upwards [hscov k] with z hz
    change ((k • z.1,k • z.2) ∈ s) = (z ∈ s) at hz
    dsimp only [F]
    simp only [Set.indicator_apply, hz]
  let c : ℂ := ∫ z, F z ∂ν
  have hc : ‖c‖ ≤ 1 := by
    simpa [c] using norm_integral_le_of_norm_le_const (μ := ν) (f := F)
      (C := 1) (Eventually.of_forall hFB)
  let L : X × X → ℂ := fun z => F z - c
  have hLm : Measurable L := hF.sub measurable_const
  have hLB (z : X × X) : ‖L z‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hFB z])
  have hLc : ∀ k : K, ∀ᵐ z ∂ν, L (k • z.1,k • z.2) = L z := by
    intro k; filter_upwards [hFc k] with z hz using congrArg (fun w => w-c) hz
  have hLn : ¬ L =ᵐ[ν] 0 := by
    intro h
    apply indicator_not_constant ν s hsn c
    filter_upwards [h] with z hz
    exact sub_eq_zero.mp hz
  have hL0 : (∫ z, L z ∂ν) = 0 := by
    rw [integral_sub hFi (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, c, sub_self]
  have hr := row_constant μ κ q hq L hLm 2 hLB hqcov hκcov hLc
  have hswapP : MeasurePreserving Prod.swap ν ν := ⟨measurable_swap, hswap⟩
  have hLsc : ∀ k : K, ∀ᵐ z ∂ν, (L ∘ Prod.swap) (k • z.1,k • z.2) = (L ∘ Prod.swap) z := by
    intro k
    exact hswapP.quasiMeasurePreserving.ae (hLc k)
  have hc' := row_constant μ κ q hq (L ∘ Prod.swap) (hLm.comp measurable_swap) 2
    (fun z => hLB _) hqcov hκcov hLsc
  have hLs0 : (∫ z, (L ∘ Prod.swap) z ∂ν) = 0 := by
    change (∫ z, L (Prod.swap z) ∂ν) = 0
    rw [← integral_map measurable_swap.aemeasurable hLm.aestronglyMeasurable]
    exact (congrArg (fun ρ => ∫ z, L z ∂ρ) hswap).trans hL0
  refine ⟨L, hLm, hLB, hLc, hLn, ?_, ?_⟩
  · filter_upwards [hr] with x hx using hx.trans hL0
  · filter_upwards [hc'] with x hx using hx.trans hLs0

end EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]

lemma law_eq_mixture (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) :
    law μ q hq = ((condDistrib id q μ).prod (condDistrib id q μ)) ∘ₘ μ.map q := by
  let κ := condDistrib id q μ
  ext s hs
  rw [law, Measure.compProd_apply hs, Measure.bind_apply hs (Kernel.measurable _).aemeasurable]
  have he := ConditionalFiber.comp_identity_fiber μ q hq
  change κ ∘ₘ μ.map q = μ at he
  have hm : Measurable (fun x => (κ (q x)) (Prod.mk x ⁻¹' s)) :=
    Kernel.measurable_kernel_prodMk_left (κ := κ.comap q hq) hs
  change (∫⁻ x, κ (q x) (Prod.mk x ⁻¹' s) ∂μ) = _
  conv_lhs => rw [← he]
  rw [Measure.lintegral_bind (Kernel.measurable κ).aemeasurable hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ConditionalFiber.ae_in_own_fiber μ q hq] with y hy
  rw [Kernel.prod_apply, Measure.prod_apply hs]
  exact lintegral_congr_ae (hy.mono fun x hx => by change κ (q x) _ = _; rw [hx])

lemma law_swap (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) :
    (law μ q hq).map Prod.swap = law μ q hq := by
  rw [law_eq_mixture]
  rw [Measure.map_comp _ _ measurable_swap, Kernel.map_prod_swap]

end EuclideanFiveColor.RelativeProduct

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.RelativeProduct
open MeasureTheory ProbabilityTheory
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma conditional_covariance (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) (k : K) :
    ∀ᵐ y ∂μ.map q, condDistrib id q μ (k • y) =
      (condDistrib id q μ y).map (fun x => k • x) :=
  KernelSupport.condDistrib_equivariant μ id q measurable_id hq
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun x => k • x)
    (measurable_const_smul k) (hpres k) (hqcov k) (Filter.Eventually.of_forall fun _ => rfl)

lemma law_preserving (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) (k : K) :
    MeasurePreserving (fun z : X × X => (k • z.1,k • z.2)) (law μ q hq) (law μ q hq) := by
  let κ := condDistrib id q μ
  let ν := μ.map q
  have hS := measurable_const_smul (M := K) (α := X) k
  have hR := measurable_const_smul (M := K) (α := Y) k
  have hν : ν.map (fun y => k • y) = ν := by
    dsimp [ν]
    rw [Measure.map_map hR hq]
    calc
      _ = μ.map (q ∘ (fun x => k • x)) := Measure.map_congr (Filter.EventuallyEq.symm (hqcov k))
      _ = _ := by rw [← Measure.map_map hq hS, (hpres k).map_eq]
  have hc := conditional_covariance μ q hq hpres hqcov k
  refine ⟨hS.prodMap hS, ?_⟩
  change (law μ q hq).map (Prod.map (fun x => k • x) (fun x => k • x)) = _
  rw [law_eq_mixture, Measure.map_comp _ _ (hS.prodMap hS), ← Kernel.map_prod_map _ _ hS hS]
  change ((κ.map (fun x => k • x)).prod (κ.map (fun x => k • x))) ∘ₘ ν = _
  calc
    _ = ((κ.prod κ).comap (fun y => k • y) hR) ∘ₘ ν := by
      apply Measure.comp_congr
      filter_upwards [hc] with y hy
      simp only [Kernel.prod_apply, Kernel.map_apply _ hS, Kernel.comap_apply]
      rw [hy]
    _ = (κ.prod κ) ∘ₘ ν.map (fun y => k • y) := by
      ext s hs
      rw [Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        Measure.bind_apply hs (Kernel.measurable _).aemeasurable,
        lintegral_map ((κ.prod κ).measurable_coe hs) hR]
      rfl
    _ = (κ.prod κ) ∘ₘ ν := by rw [hν]

lemma law_invariant (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) :
    SMulInvariantMeasure K (X × X) (law μ q hq) := by
  constructor
  intro k s hs
  exact (law_preserving μ q hq hpres hqcov k).measure_preimage hs.nullMeasurableSet

end EuclideanFiveColor.RelativeProduct
namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory Filter ConditionalFiber
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]

lemma image_conditional_mean_zero (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hLC : ∀ z, ‖L z‖ ≤ C)
    (f : X → ℂ) (hfm : Measurable f) (hfB : ∀ x, ‖f x‖ ≤ 1)
    (hcol : ∀ᵐ x ∂μ, (∫ x', L (x',x) ∂condDistrib id q μ (q x)) = 0) :
    ∀ᵐ y ∂μ.map q, (∫ x, applyKernel (condDistrib id q μ) q L f x
      ∂condDistrib id q μ y) = 0 := by
  let κ := condDistrib id q μ
  filter_upwards [ae_in_own_fiber μ q hq, ae_fiber_of_ae μ q hq hcol] with y hy hcy
  have hLF : Measurable (fun z : X × X => L z * f z.2) := hL.mul (hfm.comp measurable_snd)
  have hLFB (z : X × X) : ‖L z * f z.2‖ ≤ C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hfB _) (norm_nonneg _)).trans (by simpa using hLC z)
  have hLFi : Integrable (fun z : X × X => L z * f z.2) ((κ y).prod (κ y)) :=
    Integrable.of_bound hLF.aestronglyMeasurable C (Eventually.of_forall hLFB)
  calc
    (∫ x, applyKernel κ q L f x ∂κ y) =
        ∫ x, (∫ x', L (x,x') * f x' ∂κ y) ∂κ y := by
      apply integral_congr_ae
      filter_upwards [hy] with x hx
      dsimp only [applyKernel]; rw [hx]
    _ = ∫ x', (∫ x, L (x,x') * f x' ∂κ y) ∂κ y := integral_integral_swap hLFi
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hy, hcy] with x' hx' hc'
      rw [integral_mul_const]
      change (∫ x, L (x,x') ∂κ (q x')) = 0 at hc'
      rw [hx'] at hc'
      change _ = 0
      rw [hc', zero_mul]

lemma nonzero_not_factorizable (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q) (H : X → ℂ)
    (hn : ¬ H =ᵐ[μ] 0)
    (hc : ∀ᵐ y ∂μ.map q, (∫ x, H x ∂condDistrib id q μ y) = 0) :
    ¬ ∃ b : Y → ℂ, Measurable b ∧ H =ᵐ[μ] b ∘ q := by
  rintro ⟨b, _hb, he⟩
  have hb0 : ∀ᵐ y ∂μ.map q, b y = 0 := by
    filter_upwards [hc, ae_in_own_fiber μ q hq, ae_fiber_of_ae μ q hq he] with y hy hqy hey
    have hh : H =ᵐ[condDistrib id q μ y] (fun _ => b y) := by
      filter_upwards [hqy, hey] with x hx hx'
      simpa only [Function.comp_apply, hx] using hx'
    rw [integral_congr_ae hh] at hy
    simpa using hy
  apply hn
  have he0 : ∀ᵐ x ∂μ, b (q x) = 0 := ae_of_ae_map (p := fun y => b y = 0) hq.aemeasurable hb0
  filter_upwards [he, he0] with x hx hx' using hx.trans hx'

end EuclideanFiveColor.KernelCompact

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Functions
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.CompactFunctions

section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

lemma compact_closed_preimage {μ : Measure X} [IsProbabilityMeasure μ]
    {q : X → Y} {H : X → ℂ} [MeasurableConstSMul K X]
    (hq : Measurable q) (hH : Measurable H) (hC : Compact (K := K) μ q H)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (t : Set ℂ) (ht : IsClosed t) :
    Compact (K := K) μ q ((H ⁻¹' t).indicator (fun _ => (1 : ℂ))) := by
  let δ : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  let f : ℕ → ℂ → ℂ := fun n z => ((thickenedIndicator (hδ n) t z : ℝ) : ℂ)
  have hf (n : ℕ) : LipschitzWith ((δ n).toNNReal⁻¹) (f n) := by
    have h := Complex.isometry_ofReal.lipschitz.comp
      (NNReal.isometry_coe.lipschitz.comp (lipschitzWith_thickenedIndicator (hδ n) t))
    simpa only [one_mul, Function.comp_def] using h
  have hfb (n : ℕ) (z : ℂ) : ‖f n z‖ ≤ 1 := by
    dsimp [f]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast thickenedIndicator_le_one (hδ n) t z
  have hfl (z : ℂ) : Tendsto (fun n => f n z) atTop (𝓝 (t.indicator (fun _ => (1 : ℂ)) z)) := by
    have hh := (tendsto_pi_nhds.mp (thickenedIndicator_tendsto_indicator_closure hδ
      tendsto_one_div_add_atTop_nhds_zero_nat t)) z
    rw [ht.closure_eq] at hh
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (NNReal.continuous_coe.continuousAt.tendsto.comp hh)
    have he : (((t.indicator (fun _ => (1 : NNReal)) z : NNReal) : ℝ) : ℂ) =
        t.indicator (fun _ => (1 : ℂ)) z := by
      by_cases hz : z ∈ t <;> simp [hz]
    change Tendsto (fun n => f n z) atTop (𝓝 _) at h
    rwa [he] at h
  have hiM : Measurable ((H ⁻¹' t).indicator (fun _ => (1 : ℂ))) :=
    measurable_const.indicator (hH ht.measurableSet)
  apply compact_of_bounded_pointwise_limit hq hiM
    (fun n => (hf n).continuous.measurable.comp hH)
    (fun n => compact_lipschitz hq hH hC (f n) _ (hf n)) hpres 1 (by norm_num)
  · intro x
    by_cases hx : H x ∈ t <;> simp [Set.indicator, hx]
  · intro n x
    exact hfb n (H x)
  · exact Filter.Eventually.of_forall fun x => by
      have he : (H ⁻¹' t).indicator (fun _ => (1 : ℂ)) x =
          t.indicator (fun _ => (1 : ℂ)) (H x) := by
        by_cases hx : H x ∈ t <;> simp [hx]
      simpa only [Function.comp_apply, he] using hfl (H x)

lemma compactSigma_le (μ : Measure X) [IsProbabilityMeasure μ] (q : X → Y)
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ) :
    compactSigma μ q hq hpres ≤ ‹MeasurableSpace X› := fun _ hs => hs.1

lemma measurable_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    {H : X → ℂ} (hm : Measurable H) (hc : Compact (K := K) μ q H) :
    @Measurable X ℂ (compactSigma μ q hq hpres) inferInstance H := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap H (borel ℂ) ≤ compactSigma μ q hq hpres
  rw [borel_eq_generateFrom_isClosed, MeasurableSpace.comap_generateFrom]
  apply MeasurableSpace.generateFrom_le
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨hm ht.measurableSet, compact_closed_preimage hq hm hc hpres t ht⟩

end
section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {K X Y : Type*} [SMul K X] [MeasurableSpace X] [MeasurableSpace Y]

lemma compact_simple {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (f : @SimpleFunc X (compactSigma μ q hq hpres) ℂ) :
    Compact (K := K) μ q f := by
  apply @SimpleFunc.induction X ℂ (compactSigma μ q hq hpres) _
    (fun f => Compact (K := K) μ q f) ?_ ?_ f
  · intro c s hs
    have hsm : MeasurableSet s := hs.1
    have hsc : Compact (K := K) μ q (s.indicator (fun _ => (1 : ℂ))) := hs.2
    have hh := compact_mul hq measurable_const (measurable_const.indicator hsm)
      1 (by norm_num) (indicator_one_bound s) (compact_const (K := K) μ q c) hsc
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  · intro f g _ hf hg
    exact compact_add hq ((@SimpleFunc.measurable X ℂ (compactSigma μ q hq hpres) _ f).mono (compactSigma_le μ q hq hpres) le_rfl)
      ((@SimpleFunc.measurable X ℂ (compactSigma μ q hq hpres) _ g).mono (compactSigma_le μ q hq hpres) le_rfl) hf hg

lemma compact_of_measurable_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    {H : X → ℂ} (hm : @Measurable X ℂ (compactSigma μ q hq hpres) inferInstance H)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖H x‖ ≤ C) :
    Compact (K := K) μ q H := by
  let F : ℕ → @SimpleFunc X (compactSigma μ q hq hpres) ℂ :=
    @SimpleFunc.approxOn ℂ X _ _ _ (compactSigma μ q hq hpres) H hm Set.univ 0 (Set.mem_univ 0) inferInstance
  have hHm : Measurable H := hm.mono (compactSigma_le μ q hq hpres) le_rfl
  have hFm (n : ℕ) : Measurable (F n) :=
    (@SimpleFunc.measurable X ℂ (compactSigma μ q hq hpres) _ (F n)).mono (compactSigma_le μ q hq hpres) le_rfl
  apply compact_of_bounded_pointwise_limit hq hHm hFm
    (fun n => compact_simple hq hpres (F n)) hpres (2*C) (by positivity)
  · intro x; have := hb x; linarith
  · intro n x
    exact (@SimpleFunc.norm_approxOn_zero_le X ℂ (compactSigma μ q hq hpres) _ _ _ H hm Set.univ (Set.mem_univ 0) inferInstance x n).trans (by linarith [hb x])
  · exact Filter.Eventually.of_forall fun x => @SimpleFunc.tendsto_approxOn ℂ X _ _ _ (compactSigma μ q hq hpres) H hm Set.univ 0
      (Set.mem_univ 0) inferInstance x (by simp)

lemma compact_base {μ : Measure X} {q : X → Y} [SMul K Y] [MeasurableConstSMul K Y]
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (b : Y → ℂ) (hbm : Measurable b) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, ‖b y‖ ≤ B) :
    Compact (K := K) μ q (b ∘ q) := by
  intro ε hε
  apply at_of_finite (I := Unit) B 1 (fun _ _ => 1) hB (by norm_num) (fun _ => measurable_const)
  · intro x; simp
  · intro k
    refine ⟨fun y _ => b (k • y), Measurable.of_eval (fun _ => hbm.comp (measurable_const_smul k)), ?_, ?_, ?_⟩
    · intro y; simpa using hb (k • y)
    · apply (integrable_zero X ℝ μ).congr
      filter_upwards [hqcov k] with x hx
      simp [Function.comp_apply, hx]
    · have he : (fun x => dist ((b ∘ q) (k • x)) (∑ _ : Unit, b (k • q x) * 1)^2) =ᵐ[μ]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [hqcov k] with x hx
        simp [Function.comp_apply, hx]
      rw [integral_congr_ae he, integral_zero]
      exact sq_pos_of_pos hε

end
section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {K X Y : Type*} [Monoid K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]

omit [MulAction K Y] in
lemma compact_shift {μ : Measure X} {q : X → Y} {H : X → ℂ}
    (hc : Compact (K := K) μ q H) (g : K) :
    Compact (K := K) μ q (fun x => H (g • x)) := by
  intro ε hε
  obtain ⟨r, B, C, Hf, hB, hC, hm, hb, ha⟩ := hc ε hε
  refine ⟨r, B, C, Hf, hB, hC, hm, hb, ?_⟩
  intro k
  simpa only [smul_smul] using ha (g*k)

omit [MulAction K Y] in
lemma measurable_shift_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ) (g : K) :
    @Measurable X X (compactSigma μ q hq hpres) (compactSigma μ q hq hpres) (fun x => g • x) := by
  intro s hs
  refine ⟨(measurable_const_smul g) hs.1, ?_⟩
  have hh := compact_shift hs.2 g
  have he : (fun x => (s.indicator (fun _ => (1 : ℂ))) (g • x)) =
      ((fun x : X => g • x) ⁻¹' s).indicator (fun _ => 1) := by
    funext x; by_cases hx : g • x ∈ s <;> simp [hx]
  rwa [he] at hh

lemma measurable_base_compactSigma {μ : Measure X} [IsProbabilityMeasure μ] {q : X → Y}
    [MeasurableConstSMul K X] [MeasurableConstSMul K Y] (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) :
    @Measurable X Y (compactSigma μ q hq hpres) inferInstance q := by
  intro s hs
  refine ⟨hq hs, ?_⟩
  have hh := compact_base hqcov (s.indicator (fun _ => (1 : ℂ)))
    (measurable_const.indicator hs) 1 (by norm_num) (indicator_one_bound s)
  have he : (s.indicator (fun _ => (1 : ℂ))) ∘ q =
      (q ⁻¹' s).indicator (fun _ => 1) := by
    funext x; by_cases hx : q x ∈ s <;> simp [Function.comp_apply, hx]
  rwa [he] at hh

end

/-! Bounded integral kernels yield finite-module orbit approximation.
This implements the compact-tower construction without spectral projections:
approximate the invariant kernel by finite rectangles first. -/
open MeasureTheory ProbabilityTheory ConditionalFiber
open scoped BigOperators
variable {K X Z Y : Type*} [SMul K X] [SMul K Z]
  [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Z]

/-- Conditional integration projects an ambient finite module to the actual
new factor, without sacrificing its uniform coefficient or basis bounds. -/
lemma compact_descend (μ : Measure X) [IsProbabilityMeasure μ]
    (π : X → Z) (hπ : Measurable π) (p : Z → Y) (hp : Measurable p)
    (hπcov : ∀ k : K, ∀ᵐ x ∂μ, π (k • x) = k • π x)
    (H : Z → ℂ) (hH : Measurable H) (D : ℝ) (_hD : 0 ≤ D)
    (hHD : ∀ z, ‖H z‖ ≤ D)
    (hc : Compact (K := K) μ (p ∘ π) (H ∘ π)) :
    Compact (K := K) (μ.map π) p H := by
  let κ := condDistrib id π μ
  let ν := μ.map π
  let : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hπ.aemeasurable
  intro ε hε
  obtain ⟨r, B, C, F, hB, hC, hFm, hFb, ha⟩ := hc ε hε
  have hFC (i : Fin r) (x : X) : ‖F i x‖ ≤ C :=
    (Finset.single_le_sum (fun j _ => norm_nonneg (F j x)) (Finset.mem_univ i)).trans (hFb x)
  have hFi (z : Z) (i : Fin r) : Integrable (F i) (κ z) :=
    Integrable.of_bound (hFm i).aestronglyMeasurable C (Filter.Eventually.of_forall (hFC i))
  let G : Fin r → Z → ℂ := fun i z => ∫ x, F i x ∂κ z
  have hGm (i : Fin r) : Measurable (G i) :=
    (hFm i).stronglyMeasurable.integral_kernel.measurable
  have hGb (z : Z) : ∑ i, ‖G i z‖ ≤ C := by
    calc
      ∑ i, ‖G i z‖ ≤ ∑ i, ∫ x, ‖F i x‖ ∂κ z :=
        Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _
      _ = ∫ x, ∑ i, ‖F i x‖ ∂κ z :=
        (integral_finsetSum _ (fun i _ => (hFi z i).norm)).symm
      _ ≤ ∫ _x, C ∂κ z := integral_mono
        (integrable_finsetSum _ (fun i _ => (hFi z i).norm)) (integrable_const C) hFb
      _ = C := by simp
  refine ⟨r, B, C, G, hB, hC, hGm, hGb, ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha k
  let E : X → ℂ := fun x => H (π (k • x)) - ∑ i, a (p (π x)) i * F i x
  have hEm : Measurable E := ((hH.comp hπ).comp (measurable_const_smul k)).sub
    (Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp (hp.comp hπ)).mul (hFm i)))
  have hEB (x : X) : ‖E x‖ ≤ D+B*C :=
    (norm_sub_le _ _).trans (add_le_add (hHD _) (module_bound _ _ hB (hab _) (hFb x)))
  have hEi (z : Z) : Integrable E (κ z) :=
    Integrable.of_bound hEm.aestronglyMeasurable (D+B*C) (Filter.Eventually.of_forall hEB)
  have hE₂i (z : Z) : Integrable (fun x => ‖E x‖^2) (κ z) :=
    Integrable.of_bound (hEm.norm.pow_const 2).aestronglyMeasurable ((D+B*C)^2)
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_sq] using
          pow_le_pow_left₀ (norm_nonneg _) (hEB x) 2)
  have hE₂μ : Integrable (fun x => ‖E x‖^2) μ := by
    simpa only [E, Function.comp_apply, dist_eq_norm] using hai
  have hEeq : ∀ᵐ z ∂ν, (∫ x, E x ∂κ z) = H (k • z) - ∑ i, a (p z) i * G i z := by
    filter_upwards [ae_in_own_fiber μ π hπ, ae_fiber_of_ae μ π hπ (hπcov k)] with z hz hc'
    have he : E =ᵐ[κ z] (fun x => H (k • z) - ∑ i, a (p z) i * F i x) := by
      filter_upwards [hz, hc'] with x hx hx'
      dsimp only [E]
      rw [hx', hx]
    rw [integral_congr_ae he, integral_sub (integrable_const _) (integrable_finsetSum _
      fun i _ => (hFi z i).const_mul _), integral_finsetSum _
      (fun i _ => (hFi z i).const_mul _)]
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul, G]
  have hdistm : Measurable (fun z => dist (H (k • z)) (∑ i, a (p z) i * G i z)^2) :=
    ((hH.comp (measurable_const_smul k)).dist
      (Finset.measurable_sum _ (fun i _ => (((measurable_pi_iff.mp ham) i).comp hp).mul (hGm i)))).pow_const 2
  have hdistB (z : Z) : dist (H (k • z)) (∑ i, a (p z) i * G i z)^2 ≤ (D+B*C)^2 := by
    apply pow_le_pow_left₀ dist_nonneg
    exact (dist_le_norm_add_norm _ _).trans
      (add_le_add (hHD _) (module_bound _ _ hB (hab _) (hGb z)))
  have hdisti : Integrable (fun z => dist (H (k • z)) (∑ i, a (p z) i * G i z)^2) ν :=
    Integrable.of_bound hdistm.aestronglyMeasurable ((D+B*C)^2)
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_sq] using hdistB z)
  refine ⟨a, ham, hab, hdisti, ?_⟩
  have hle : (∫ z, dist (H (k • z)) (∑ i, a (p z) i * G i z)^2 ∂ν) ≤
      ∫ z, (∫ x, ‖E x‖^2 ∂κ z) ∂ν := by
    apply integral_mono_ae hdisti (integrable_fiber_integral μ π hπ _ hE₂μ)
    filter_upwards [hEeq] with z hz
    rw [dist_eq_norm, ← hz]
    exact KernelCompact.norm_integral_sq (κ z) E (hEi z) (hE₂i z)
  rw [integral_fiber μ π hπ _ hE₂μ] at hle
  apply hle.trans_lt
  simpa only [E, Function.comp_apply, dist_eq_norm] using hae

end EuclideanFiveColor.CompactFunctions

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Factors
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.RelativeProduct.law_probability_add _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EuclideanFiveColor
open MeasureTheory

namespace OrbitSpace
variable {K : Type*}

lemma continuous_val : Continuous (val : OrbitSpace K → K → ℂ) :=
  (equiv K).homeomorph.continuous
lemma continuous_mk : Continuous (mk : (K → ℂ) → OrbitSpace K) :=
  (equiv K).homeomorph.symm.continuous
lemma measurable_val [Countable K] : Measurable (val : OrbitSpace K → K → ℂ) := continuous_val.measurable
lemma measurable_mk [Countable K] : Measurable (mk : (K → ℂ) → OrbitSpace K) := continuous_mk.measurable

instance instContinuousConstSMul [Monoid K] : ContinuousConstSMul K (OrbitSpace K) where
  continuous_const_smul k := continuous_mk.comp
    (continuous_pi fun l => (continuous_apply (l*k)).comp continuous_val)
instance instMeasurableConstSMul [Monoid K] : MeasurableConstSMul K (OrbitSpace K) where
  measurable_const_smul k := (continuous_const_smul k).measurable

end OrbitSpace

namespace OrbitFactor
variable {K X Y : Type*} [Monoid K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]

omit [MulAction K Y] [MeasurableSpace Y] in
lemma measurable_orbit [Countable K] [MeasurableConstSMul K X]
    {H : X → ℂ} (hH : Measurable H) : Measurable (orbit (K := K) H) :=
  OrbitSpace.measurable_mk.comp (Measurable.of_eval fun k => hH.comp (measurable_const_smul k))

omit [MulAction K Y] [MeasurableSpace X] [MeasurableSpace Y] in
lemma orbit_equivariant (H : X → ℂ) (k : K) (x : X) :
    orbit (K := K) H (k • x) = k • orbit H x := by
  ext l
  exact congrArg H (mul_smul l k x).symm

omit [MulAction K Y] in
lemma measurable_extend [Countable K] [MeasurableConstSMul K X]
    {q : X → Y} (hq : Measurable q) {H : X → ℂ} (hH : Measurable H) :
    Measurable (extend (K := K) q H) := hq.prodMk (measurable_orbit hH)

omit [MeasurableSpace Y] in
lemma extend_equivariant (μ : Measure X) {q : X → Y} (H : X → ℂ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) (k : K) :
    ∀ᵐ x ∂μ, extend (K := K) q H (k • x) = k • extend q H x := by
  filter_upwards [hqcov k] with x hx
  exact Prod.ext hx (orbit_equivariant H k x)

end OrbitFactor
end EuclideanFiveColor

namespace EuclideanFiveColor.OrbitFactor
open MeasureTheory ProbabilityTheory CompactFunctions
variable {K X Y : Type*} [Monoid K] [Countable K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] in
lemma measurable_extend_compactSigma (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (H : X → ℂ) (hH : Measurable H) (hc : Compact (K := K) μ q H) :
    @Measurable X (Y × OrbitSpace K) (compactSigma μ q hq hpres) inferInstance
      (extend (K := K) q H) := by
  have hHm := measurable_compactSigma hq hpres hH hc
  have hpm : @Measurable X (K → ℂ) (compactSigma μ q hq hpres) inferInstance
      (fun x k => H (k • x)) :=
    @Measurable.of_eval X K (fun _ => ℂ) (compactSigma μ q hq hpres) (fun _ => inferInstance) _ (fun k => hHm.comp (measurable_shift_compactSigma hq hpres k))
  exact (measurable_base_compactSigma hq hpres hqcov).prodMk
    (OrbitSpace.measurable_mk.comp hpm)

/-- The orbit factor generated by a compact scalar function is an actual
compact extension; the finite module is projected onto that factor. -/
lemma compact_orbit_extension (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (H : X → ℂ) (hH : Measurable H) (hc : Compact (K := K) μ q H)
    (F : Y × OrbitSpace K → ℂ) (hF : Measurable F)
    (D : ℝ) (hD : 0 ≤ D) (hFD : ∀ z, ‖F z‖ ≤ D) :
    Compact (K := K) (μ.map (extend (K := K) q H)) Prod.fst F := by
  let : MeasurableConstSMul K (Y × OrbitSpace K) := ⟨fun k =>
    ((measurable_const_smul k).comp measurable_fst).prodMk
      ((measurable_const_smul k).comp measurable_snd)⟩
  apply compact_descend μ (extend (K := K) q H) (measurable_extend hq hH)
    Prod.fst measurable_fst (extend_equivariant μ H hqcov) F hF D hD hFD
  change Compact (K := K) μ q (F ∘ extend (K := K) q H)
  exact compact_of_measurable_compactSigma hq hpres
    (hF.comp (measurable_extend_compactSigma μ q hq hpres hqcov H hH hc)) D hD
    (fun x => hFD _)

end EuclideanFiveColor.OrbitFactor
namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated X]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MeasurableConstSMul K Y] in
lemma compact_applyKernel (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    (hLcov : ∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z)
    (f : X → ℂ) (hfm : Measurable f) (hfB : ∀ x, ‖f x‖ ≤ 1) :
    CompactFunctions.Compact (K := K) μ q (applyKernel κ q L f) := by
  intro ε hε
  obtain ⟨r, B, C₀, Hf, hB, hC₀, hHm, hHb, ha⟩ :=
    bounded_range_approximation μ κ q hq L hL C hC hLC ε hε
  refine ⟨r, B, C₀, Hf, hB, hC₀, hHm, hHb, ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha (fun x => f (k • x))
    (hfm.comp (measurable_const_smul k)) (fun x => hfB (k • x))
  have he := applyKernel_covariance μ κ q hq L hL hqcov hκcov hLcov f hfm k
  have hd : (fun x => dist (applyKernel κ q L f (k • x))
      (∑ i, a (q x) i * Hf i x)^2) =ᵐ[μ]
      (fun x => dist (applyKernel κ q L (fun x => f (k • x)) x)
        (∑ i, a (q x) i * Hf i x)^2) := he.mono fun x hx => by dsimp only at hx ⊢; rw [hx]
  exact ⟨a, ham, hab, hai.congr hd.symm, by rw [integral_congr_ae hd]; exact hae⟩

end EuclideanFiveColor.KernelCompact
namespace EuclideanFiveColor.CompactTower
open MeasureTheory ProbabilityTheory KernelCompact CompactFunctions OrbitFactor
variable {K X Y : Type*} [Group K] [Countable K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

/-- The strict compact-successor step of the compact tower. The new coordinate
is constructed from a centered invariant conditional-product kernel. -/
theorem strict_compact_successor (μ : Measure X) [IsProbabilityMeasure μ]
    [ErgodicSMul K X μ] (q : X → Y) (hq : Measurable q)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hn : ¬ ErgodicSMul K (X × X) (RelativeProduct.law μ q hq)) :
    ∃ H : X → ℂ, Measurable H ∧ (∀ x, ‖H x‖ ≤ 2) ∧
      (¬ ∃ b : Y → ℂ, Measurable b ∧ H =ᵐ[μ] b ∘ q) ∧
      (∀ F : Y × OrbitSpace K → ℂ, Measurable F →
        (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
        Compact (K := K) (μ.map (extend (K := K) q H)) Prod.fst F) := by
  have hpres (k : K) := measurePreserving_smul k μ
  let κ := condDistrib id q μ
  let : SMulInvariantMeasure K (X × X) (μ ⊗ₘ κ.comap q hq) :=
    RelativeProduct.law_invariant μ q hq hpres hqcov
  have hκcov := RelativeProduct.conditional_covariance μ q hq hpres hqcov
  obtain ⟨L, hLm, hLB, hLcov, hLn, _hrow, hcol⟩ := centered_kernel μ κ q hq
    (RelativeProduct.law_swap μ q hq) hqcov hκcov hn
  obtain ⟨f, hfm, hfB, hfn⟩ := exists_nonzero_image μ κ q hq L hLm 2 (by norm_num) hLB hLn
  let H := applyKernel κ q L f
  have hHm : Measurable H := measurable_applyKernel κ q hq L hLm f hfm
  have hHc : Compact (K := K) μ q H := compact_applyKernel μ κ q hq L hLm 2
    (by norm_num) hLB hqcov hκcov hLcov f hfm hfB
  refine ⟨H, hHm, applyKernel_bound κ q L 2 hLB f hfB, ?_, ?_⟩
  · exact nonzero_not_factorizable μ q hq H hfn
      (image_conditional_mean_zero μ q hq L hLm 2 hLB f hfm hfB hcol)
  · intro F hF hFB
    obtain ⟨C,hC⟩ := hFB
    have hC0 : 0 ≤ C := (norm_nonneg (F (Classical.choice inferInstance))).trans (hC _)
    exact compact_orbit_extension μ q hq hpres hqcov H hHm hHc F hF C hC0 hC

end EuclideanFiveColor.CompactTower

namespace EuclideanFiveColor.FactorCode
open MeasureTheory
variable {K X Y : Type*} [Group K] [Countable K]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
  [MulAction K X] [MeasurableConstSMul K X]

lemma scalar_bound (y : Y) : ‖scalar Y y‖ ≤ 2 := by
  rw [scalar, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have := Real.neg_pi_div_two_lt_arctan (embeddingReal Y y)
    linarith [Real.pi_lt_four]
  · have := Real.arctan_lt_pi_div_two (embeddingReal Y y)
    linarith [Real.pi_lt_four]

lemma encode_measurable {p : X → Y} (hp : Measurable p) : Measurable (encode (K := K) p) :=
  OrbitFactor.measurable_orbit (scalar_measurable.comp hp)

omit [Countable K] [MeasurableSpace X] [MeasurableConstSMul K X] in
lemma encode_equivariant (p : X → Y) (k : K) (x : X) :
    encode (K := K) p (k • x) = k • encode (K := K) p x := OrbitFactor.orbit_equivariant _ _ _

variable [Nonempty Y]

lemma decode_measurable : Measurable (decode (K := K) (Y := Y)) :=
  scalar_embedding.measurable_invFun.comp ((measurable_pi_apply 1).comp OrbitSpace.measurable_val)

omit [Countable K] [MeasurableSpace X] [MeasurableConstSMul K X] in
lemma decode_encode (p : X → Y) (x : X) : decode (encode (K := K) p x) = p x := by
  dsimp only [decode, encode]
  rw [OrbitFactor.orbit_one]
  exact scalar_embedding.leftInverse_invFun _

omit [Nonempty Y] [MeasurableConstSMul K X] in
lemma encode_as_comp [MulAction K Y] [MeasurableConstSMul K Y]
    (μ : Measure X) (p : X → Y) (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) :
    ∀ᵐ x ∂μ, encode (K := K) p x = encode (K := K) (id : Y → Y) (p x) := by
  filter_upwards [ae_all_iff.mpr hpe] with x hx
  ext k
  exact congrArg (scalar Y) (hx k)

end EuclideanFiveColor.FactorCode
namespace EuclideanFiveColor.FactorLp
open MeasureTheory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace Y] [Nonempty Y]

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma isClosed (μ : Measure X) {p : X → Y} (hp : Measurable p) :
    IsClosed (space μ p : Set (Lp ℂ 2 μ)) :=
  isClosed_aestronglyMeasurable hp.comap_le

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma exists_rep (μ : Measure X) (p : X → Y) (f : Lp ℂ 2 μ) (hf : f ∈ space μ p) :
    ∃ g : Y → ℂ, Measurable g ∧ (f : X → ℂ) =ᵐ[μ] g ∘ p := by
  obtain ⟨h, hh, hfe⟩ := hf
  obtain ⟨g, hg, he⟩ := hh.measurable.exists_eq_measurable_comp (f := p)
  exact ⟨g, hg, by simpa only [he] using hfe⟩

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma mem_of_rep (μ : Measure X) (p : X → Y) (f : Lp ℂ 2 μ)
    (g : Y → ℂ) (hg : Measurable g) (he : (f : X → ℂ) =ᵐ[μ] g ∘ p) : f ∈ space μ p := by
  exact ⟨g ∘ p, (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable, he⟩

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma le_of_factor (μ : Measure X) (p : X → Y) (q : X → Z)
    (r : Z → Y) (hr : Measurable r) (he : p =ᵐ[μ] r ∘ q) : space μ p ≤ space μ q := by
  intro f hf
  obtain ⟨g, hg, hfe⟩ := exists_rep μ p f hf
  apply mem_of_rep μ q f (g ∘ r) (hg.comp hr)
  filter_upwards [hfe, he] with x hx he
  simpa only [Function.comp_apply, he] using hx

lemma factor_of_le (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → Y) (q : X → Z) (hp : Measurable p) (hle : space μ p ≤ space μ q) :
    ∃ r : Z → Y, Measurable r ∧ p =ᵐ[μ] r ∘ q := by
  let f := FactorCode.scalar Y ∘ p
  have hfm : Measurable f := FactorCode.scalar_measurable.comp hp
  have hf : MemLp f 2 μ := MemLp.of_bound hfm.aestronglyMeasurable 2
    (Filter.Eventually.of_forall fun x => FactorCode.scalar_bound (p x))
  have hmem : hf.toLp f ∈ space μ p := mem_of_rep μ p _ _ FactorCode.scalar_measurable hf.coeFn_toLp
  obtain ⟨g, hg, he⟩ := exists_rep μ q _ (hle hmem)
  refine ⟨FactorCode.scalar_embedding.invFun ∘ g,
    FactorCode.scalar_embedding.measurable_invFun.comp hg, ?_⟩
  filter_upwards [hf.coeFn_toLp, he] with x hx hex
  have hh : f x = g (q x) := hx.symm.trans hex
  change p x = FactorCode.scalar_embedding.invFun (g (q x))
  rw [← hh]
  exact (FactorCode.scalar_embedding.leftInverse_invFun (p x)).symm

end EuclideanFiveColor.FactorLp
namespace EuclideanFiveColor.CountableApprox
open MeasureTheory
variable {Y : Type*} [MeasurableSpace Y]

lemma truncate_measurable (n : ℕ) : Measurable (truncate (Y := Y) n) :=
  Measurable.of_eval fun i => measurable_pi_apply (i : ℕ)

lemma truncate_mono : Monotone (fun n => (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)) := by
  intro n m hnm
  rw [← measurable_iff_comap_le]
  have hm : Measurable[(inferInstance : MeasurableSpace (Fin m → Y)).comap (truncate m)]
      (truncate (Y := Y) m) := Measurable.of_comap_le le_rfl
  refine @Measurable.of_eval (ℕ → Y) (Fin n) (fun _ => Y)
    (MeasurableSpace.comap (truncate m) inferInstance) (fun _ => inferInstance) (truncate n) ?_
  intro i
  exact (measurable_pi_apply (⟨i, lt_of_lt_of_le i.isLt hnm⟩ : Fin m)).comp hm

lemma truncate_generate : (⨆ n, (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)) =
    (inferInstance : MeasurableSpace (ℕ → Y)) := by
  apply le_antisymm (iSup_le fun n => (truncate_measurable n).comap_le)
  have hm (n : ℕ) : Measurable[⨆ n, (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)]
      (truncate (Y := Y) n) := Measurable.of_comap_le (le_iSup (fun n => MeasurableSpace.comap (truncate (Y := Y) n) (inferInstance : MeasurableSpace (Fin n → Y))) n)
  have hi : Measurable[⨆ n, (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)]
      (id : (ℕ → Y) → (ℕ → Y)) := by
    refine @Measurable.of_eval (ℕ → Y) ℕ (fun _ => Y)
      (⨆ n, MeasurableSpace.comap (truncate n) (inferInstance : MeasurableSpace (Fin n → Y)))
      (fun _ => inferInstance) id ?_
    intro n
    exact (measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1))).comp (hm (n+1))
  simpa using hi.comap_le

lemma bounded_approximation (ν : Measure (ℕ → Y)) [IsProbabilityMeasure ν]
    (m : ℕ) (H : (ℕ → Y) → Fin m → ℂ) (hH : Measurable H)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ y, ‖H y‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∃ H₀ : (Fin n → Y) → Fin m → ℂ, Measurable H₀ ∧ (∀ y, ‖H₀ y‖ ≤ 2*C) ∧
      Integrable (fun y => dist (H y) (H₀ (truncate n y))^2) ν ∧
      (∫ y, dist (H y) (H₀ (truncate n y))^2 ∂ν) < ε^2 :=
  LimitDensity.generated_factor_approximation ν truncate truncate_measurable truncate_mono truncate_generate
    m H hH C hC hB ε hε

end EuclideanFiveColor.CountableApprox
namespace EuclideanFiveColor.ChainJoin
open MeasureTheory
variable {K X Y : Type*} [Group K] [Countable K]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MulAction K X] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma joint_measurable (q : ℕ → X → Y) (hq : ∀ n, Measurable (q n)) : Measurable (joint q) :=
  Measurable.of_eval hq

omit [Nonempty Y] [MulAction K Y] [MeasurableConstSMul K Y] in
lemma code_measurable (q : ℕ → X → Y) (hq : ∀ n, Measurable (q n)) : Measurable (code (K := K) q) :=
  FactorCode.encode_measurable (joint_measurable q hq)

omit [Countable K] [MeasurableSpace X] [Nonempty Y] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma code_equivariant (q : ℕ → X → Y) (k : K) (x : X) :
    code (K := K) q (k • x) = k • code q x := FactorCode.encode_equivariant _ _ _

omit [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma le_code (μ : Measure X) (q : ℕ → X → Y) (n : ℕ) :
    FactorLp.space μ (q n) ≤ FactorLp.space μ (code (K := K) q) := by
  apply FactorLp.le_of_factor μ (q n) (code q)
    (fun z => (FactorCode.decode (K := K) (Y := ℕ → Y) z) n)
    ((measurable_pi_apply n).comp FactorCode.decode_measurable)
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply, code]
    rw [FactorCode.decode_encode]
    rfl

omit [Countable K] [MeasurableSpace Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [Nonempty Y] [StandardBorelSpace Y] in
lemma joint_equivariant (μ : Measure X) (q : ℕ → X → Y)
    (hqe : ∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x) (k : K) :
    ∀ᵐ x ∂μ, joint q (k • x) = k • joint q x := by
  filter_upwards [ae_all_iff.mpr (fun n => hqe n k)] with x hx
  exact funext hx

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma finite_upper (μ : Measure X) (q : ℕ → X → Y)
    (hc : ∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
      FactorLp.space μ (q j) ≤ FactorLp.space μ (q i)) (n : ℕ) :
    ∃ j, ∀ i < n, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨j, hj⟩ := ih
    obtain hij | hji := hc j n
    · refine ⟨n, fun i hi => ?_⟩
      obtain hi | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
      · exact (hj i hi).trans hij
      · exact le_rfl
    · refine ⟨j, fun i hi => ?_⟩
      obtain hi | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
      · exact hj i hi
      · exact hji

omit [MeasurableConstSMul K X] in
lemma approximation (μ : Measure X) [IsProbabilityMeasure μ]
    (q : ℕ → X → Y) (hq : ∀ n, Measurable (q n))
    (hqe : ∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x)
    (hc : ∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
      FactorLp.space μ (q j) ≤ FactorLp.space μ (q i))
    (m : ℕ) (H : OrbitSpace K → Fin m → ℂ) (hH : Measurable H)
    (hB : ∃ C : ℝ, ∀ z, ‖H z‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ j, ∃ H₀ : Y → Fin m → ℂ, Measurable H₀ ∧ (∃ C : ℝ, ∀ y, ‖H₀ y‖ ≤ C) ∧
      Integrable (fun x => dist (H (code q x)) (H₀ (q j x))^2) μ ∧
      (∫ x, dist (H (code q x)) (H₀ (q j x))^2 ∂μ) < ε^2 := by
  classical
  obtain ⟨C, hC⟩ := hB
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  let J := joint q
  have hJ := joint_measurable q hq
  let E : (ℕ → Y) → OrbitSpace K := FactorCode.encode id
  haveI : IsProbabilityMeasure (μ.map J) := Measure.isProbabilityMeasure_map hJ.aemeasurable
  have hE : Measurable E := FactorCode.encode_measurable measurable_id
  obtain ⟨n, Hn, hHn, hHnB, hi, he⟩ := CountableApprox.bounded_approximation (μ.map J)
    m (H ∘ E) (hH.comp hE) C' hC' (fun y => (hC _).trans (le_max_left _ _)) ε hε
  obtain ⟨j, hj⟩ := finite_upper μ q hc n
  have hfac (i : Fin n) : ∃ r : Y → Y, Measurable r ∧ q i =ᵐ[μ] r ∘ q j :=
    FactorLp.factor_of_le μ (q i) (q j) (hq i) (hj i i.isLt)
  choose r hr hre using hfac
  let R : Y → Fin n → Y := fun y i => r i y
  have hR : Measurable R := Measurable.of_eval hr
  have hEq := FactorCode.encode_as_comp (K := K) μ J (joint_equivariant μ q hqe)
  have hEq' : (fun x => dist ((H ∘ E) (J x)) (Hn (CountableApprox.truncate n (J x)))^2) =ᵐ[μ]
      (fun x => dist (H (code q x)) ((Hn ∘ R) (q j x))^2) := by
    filter_upwards [hEq, ae_all_iff.mpr hre] with x hx hxr
    have hp : CountableApprox.truncate n (J x) = R (q j x) := funext hxr
    change dist (H (E (J x))) _ ^ 2 = _
    change code (K := K) q x = E (J x) at hx
    rw [← hx, hp]
    rfl
  refine ⟨j, Hn ∘ R, hHn.comp hR, ⟨2*C', fun y => hHnB _⟩, ?_, ?_⟩
  · exact (hi.comp_measurable hJ).congr hEq'
  · rw [← integral_congr_ae hEq', ← integral_map hJ.aemeasurable hi.aestronglyMeasurable]
    exact he

end EuclideanFiveColor.ChainJoin
namespace EuclideanFiveColor.SeparableZorn
open TopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SecondCountableTopology E]

lemma countable_cover (S : Set (Submodule ℂ E)) (hS : S.Nonempty) :
    ∃ p : ℕ → S, ∀ V : Submodule ℂ E, IsClosed (V : Set E) →
      (∀ n, (p n).val ≤ V) → ∀ U ∈ S, U ≤ V := by
  classical
  let D : Set E := {x | ∃ U ∈ S, x ∈ U}
  have : Nonempty D := by
    obtain ⟨U, hU⟩ := hS
    exact ⟨⟨0, U, hU, U.zero_mem⟩⟩
  obtain ⟨u, hu⟩ := exists_dense_seq D
  have hU (n : ℕ) : ∃ U : S, (u n).val ∈ U.val := by
    obtain ⟨U, hU, hx⟩ := (u n).property
    exact ⟨⟨U, hU⟩, hx⟩
  choose p hp using hU
  refine ⟨p, ?_⟩
  intro V hc hV U hUS x hx
  have hcl : IsClosed ((Subtype.val : D → E) ⁻¹' (V : Set E)) := hc.preimage continuous_subtype_val
  have hsub : Set.range u ⊆ (Subtype.val : D → E) ⁻¹' (V : Set E) := by
    rintro _ ⟨n, rfl⟩
    exact hV n (hp n)
  have hwhole := closure_minimal hsub hcl
  rw [hu.closure_range] at hwhole
  exact hwhole (Set.mem_univ (⟨x, U, hUS, hx⟩ : D))

lemma exists_maximal {A : Type*} [Preorder A] [Nonempty A]
    (F : A → Submodule ℂ E) (hF : ∀ a, IsClosed (F a : Set E))
    (hord : ∀ a b, a ≤ b ↔ F a ≤ F b)
    (hseq : ∀ p : ℕ → A, (∀ i j, p i ≤ p j ∨ p j ≤ p i) →
      ∃ a, ∀ i, p i ≤ a) : ∃ a : A, IsMax a := by
  classical
  apply zorn_le_nonempty
  intro c hc hne
  obtain ⟨p, hp⟩ := countable_cover (F '' c) (hne.image F)
  have hrep (n : ℕ) : ∃ a : c, F a = (p n).val := by
    obtain ⟨a, ha, he⟩ := (p n).property
    exact ⟨⟨a, ha⟩, he⟩
  choose a ha using hrep
  have haorder (i j : ℕ) : (a i).val ≤ (a j).val ∨ (a j).val ≤ (a i).val :=
    hc.total (a i).property (a j).property
  obtain ⟨b, hb⟩ := hseq (fun n => (a n).val) haorder
  refine ⟨b, ?_⟩
  intro d hd
  apply (hord d b).mpr
  exact hp (F b) (hF b) (fun n => by rw [← ha n]; exact (hord _ _).mp (hb n))
    (F d) ⟨d, hd, rfl⟩

end EuclideanFiveColor.SeparableZorn
namespace EuclideanFiveColor.CodedMax
open MeasureTheory
variable {K X : Type*} [Group K] [Countable K] [MeasurableSpace X]
  [MulAction K X] [MeasurableConstSMul K X]

lemma exists_maximal (μ : Measure X) [IsProbabilityMeasure μ] [StandardBorelSpace X]
    (Good : (X → OrbitSpace K) → Prop) (hbase : Nonempty (Model μ Good))
    (hjoin : ∀ q : ℕ → X → OrbitSpace K, (∀ n, Measurable (q n)) →
      (∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x) → (∀ n, Good (q n)) →
      (∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
        FactorLp.space μ (q j) ≤ FactorLp.space μ (q i)) → Good (ChainJoin.code q)) :
    ∃ a : Model μ Good, IsMax a := by
  have := hbase
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  apply SeparableZorn.exists_maximal (fun a : Model μ Good => FactorLp.space μ a.map)
    (fun a => FactorLp.isClosed μ a.measurable) (fun _ _ => Iff.rfl)
  intro p hc
  let q := fun n => (p n).map
  have hq (n : ℕ) := (p n).measurable
  have hqe (n : ℕ) := (p n).equivariant
  have hcg : Good (ChainJoin.code q) := hjoin q hq hqe (fun n => (p n).good) hc
  let a : Model μ Good := ⟨ChainJoin.code q, ChainJoin.code_measurable q hq,
    fun k => Filter.Eventually.of_forall (ChainJoin.code_equivariant q k), hcg⟩
  exact ⟨a, fun n => ChainJoin.le_code μ q n⟩

end EuclideanFiveColor.CodedMax

end

end OAI
end

section
-- module Solutions.OAIQ5_T4.CompactFactors_Stationary
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.RelativeProduct.law_probability_add _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.PlaneFiveColor.Spectral.rotAction _root_.OAI.PlaneFiveColor.Spectral.rotErgodic _root_.OAI.PlaneFiveColor.Spectral.rotInvariant _root_.OAI.PlaneFiveColor.Spectral.rotMeasurable _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory EuclideanFiveColor

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MulAction K X] [MeasurableConstSMul K X]

/-- An actual standard Borel factor with universal relative spectral
singularity and an ergodic conditional square. Maximality is countable,
inside the separable ambient L² space. -/
theorem exists_terminal_factor_oai (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ] :
    ∃ p : X → OrbitSpace K, ∃ hp : Measurable p,
      (∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) ∧ UniversalGood μ p ∧
      ErgodicSMul K (X × X) (RelativeProduct.law μ p hp) := by
  classical
  let z₀ : OrbitSpace K := ⟨fun _ => 0⟩
  have hbase : Nonempty (CodedMax.Model (K := K) μ (UniversalGood μ)) := by
    refine ⟨⟨fun _ => z₀, measurable_const, ?_, ?_⟩⟩
    · intro k
      exact Filter.Eventually.of_forall fun x => by ext l; rfl
    · intro d hd _hw hw
      exact relative_singularity_base μ d hd z₀ hw
  have hjoin : ∀ q : ℕ → X → OrbitSpace K, (∀ n, Measurable (q n)) →
      (∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x) →
      (∀ n, UniversalGood μ (q n)) →
      (∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
        FactorLp.space μ (q j) ≤ FactorLp.space μ (q i)) → UniversalGood μ (ChainJoin.code (K := K) q) := by
    intro q hq hqe hg hc d hd hde hw
    apply relative_singularity_approximation (W := OrbitSpace K) μ d (ChainJoin.code (K := K) q) hd
      (ChainJoin.code_measurable q hq) hde
      (fun k => Filter.Eventually.of_forall (ChainJoin.code_equivariant q k)) hw
    intro m H hH hB ε hε
    obtain ⟨j, H₀, hH₀, hB₀, hi, he⟩ := ChainJoin.approximation μ q hq hqe hc m H hH hB ε hε
    exact ⟨q j, hq j, hqe j, hg j, H₀, hH₀, hB₀, hi, he⟩
  obtain ⟨a, hamax⟩ := CodedMax.exists_maximal (K := K) μ (UniversalGood μ) hbase hjoin
  refine ⟨a.map, a.measurable, a.equivariant, a.good, ?_⟩
  by_contra hn
  obtain ⟨H, hH, hB, hnot, hc⟩ := CompactTower.strict_compact_successor μ a.map
    a.measurable a.equivariant hn
  let u := OrbitFactor.extend (K := K) a.map H
  have hum : Measurable u := OrbitFactor.measurable_extend a.measurable hH
  have hue (k : K) : ∀ᵐ x ∂μ, u (k • x) = k • u x :=
    OrbitFactor.extend_equivariant μ H a.equivariant k
  have hug : UniversalGood μ u := by
    intro d hd hde hw
    apply relative_singularity_successor μ d u Prod.fst hd hum measurable_fst hde hue
      (fun k => Filter.Eventually.of_forall fun y => rfl) hw hc
    exact a.good
  let v := FactorCode.encode (K := K) u
  have hvm : Measurable v := FactorCode.encode_measurable hum
  have hve (k : K) : ∀ᵐ x ∂μ, v (k • x) = k • v x :=
    Filter.Eventually.of_forall (FactorCode.encode_equivariant u k)
  have hvg : UniversalGood μ v := universalGood_of_factor μ v u
    (FactorCode.encode (K := K) (id : OrbitSpace K × OrbitSpace K → _)) hvm hum
    (FactorCode.encode_measurable measurable_id) hve hue (FactorCode.encode_as_comp μ u hue) hug
  let b : CodedMax.Model (K := K) μ (UniversalGood μ) := ⟨v, hvm, hve, hvg⟩
  have hab : a ≤ b := by
    apply FactorLp.le_of_factor μ a.map v
      (Prod.fst ∘ FactorCode.decode (K := K) (Y := OrbitSpace K × OrbitSpace K))
      (measurable_fst.comp FactorCode.decode_measurable)
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply, v]
      rw [FactorCode.decode_encode]
      rfl
  have hba : FactorLp.space μ v ≤ FactorLp.space μ a.map := hamax hab
  have hHlp : MemLp H 2 μ := MemLp.of_bound hH.aestronglyMeasurable 2
    (Filter.Eventually.of_forall hB)
  let J : OrbitSpace K → ℂ := fun z => (FactorCode.decode
    (K := K) (Y := OrbitSpace K × OrbitSpace K) z).2.val 1
  have hJ : Measurable J := (measurable_pi_apply 1).comp
    (OrbitSpace.measurable_val.comp (measurable_snd.comp FactorCode.decode_measurable))
  have hHv : hHlp.toLp H ∈ FactorLp.space μ v := by
    apply FactorLp.mem_of_rep μ v _ J hJ
    filter_upwards [hHlp.coeFn_toLp] with x hx
    rw [hx]
    dsimp only [Function.comp_apply, J, v]
    rw [FactorCode.decode_encode]
    exact (OrbitFactor.orbit_one H x).symm
  obtain ⟨g, hg, hhe⟩ := FactorLp.exists_rep μ a.map _ (hba hHv)
  exact hnot ⟨g, hg, hHlp.coeFn_toLp.symm.trans hhe⟩

end PlaneFiveColor.Spectral

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PlaneFiveColor.Spectral.exists_terminal_factor_oai.{u_1} := @OAI.PlaneFiveColor.Spectral.exists_terminal_factor_oai.{u_1}
