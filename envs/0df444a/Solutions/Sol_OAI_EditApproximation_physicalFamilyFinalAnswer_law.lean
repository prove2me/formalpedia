-- Prove2me | solution 1 for OAI.EditApproximation.physicalFamilyFinalAnswer_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:43:50.687718+00:00
-- url     : https://prove2.me/submissions/adbedb41-7b36-411a-81b8-a61f97d812bb

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Geometric
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_localCommonMemoAnswer_law
import Theorems.Thm_OAI_EditApproximation_physicalFamilyFinalAnswer_eq

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CommonArrayTrace
attribute [-instance] _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite array of fresh pass draws is equivalent to the sequential
common-source trace. The conversion has exactly the nested product law. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

variable {Seed Ω : Type}

 theorem commonTraceToArray_toTrace (n : ℕ) (input : Seed × (Fin n → Ω)) :
    commonTraceToArray n (commonArrayToTrace n input) = input := by
  induction n with
  | zero =>
    apply Prod.ext
    · rfl
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [commonArrayToTrace, commonTraceToArray, ih]
    apply Prod.ext
    · rfl
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

 theorem commonArrayToTrace_toArray (n : ℕ) (trace : CommonSeedTrace Seed (fun _ => Ω) n) :
    commonArrayToTrace n (commonTraceToArray n trace) = trace := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases trace with ⟨trace, last⟩
    simp only [commonArrayToTrace, commonTraceToArray, Fin.snoc_last, Fin.snoc_castSucc]
    exact Prod.ext (ih trace) rfl

section Law

variable [Fintype Seed] [Fintype Ω] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]
  (random : Measure Ω) [IsProbabilityMeasure random]

omit [Fintype Seed] [DecidableEq Seed] [MeasurableSingletonClass Seed]
  [MeasurableSingletonClass Ω] [IsProbabilityMeasure incoming] [IsProbabilityMeasure random] in
theorem commonArrayToTrace_atom (n : ℕ) (input : Seed × (Fin n → Ω)) :
    (commonTraceLaw (fun _ => random) incoming n) {commonArrayToTrace n input} =
      incoming {input.1} * ∏ i, random {input.2 i} := by
  induction n with
  | zero =>
    simp only [commonArrayToTrace, commonTraceLaw, Fin.prod_univ_zero, mul_one]
    rfl
  | succ n ih =>
    change ((commonTraceLaw (fun _ => random) incoming n).prod random)
      {(commonArrayToTrace n (input.1, fun i => input.2 i.castSucc), input.2 (Fin.last n))} = _
    rw [← Set.singleton_prod_singleton, Measure.prod_prod, ih, Fin.prod_univ_castSucc]
    exact mul_assoc _ _ _

end Law

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_CommonArrayFinal
attribute [-instance] _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A final independent draw may be stored as the last array row. These
maps expose the literal product law used by the scheduled seed passes. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

variable {Seed Ω Δ : Type}

 theorem commonArrayFinal_inverse (n : ℕ) (input : Seed × (Fin (n + 1) → Ω)) :
    commonFinalArray n (commonArrayFinal n input) = input := by
  unfold commonFinalArray commonArrayFinal
  rw [commonTraceToArray_toTrace]
  apply Prod.ext
  · rfl
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

 theorem commonFinalArray_inverse (n : ℕ) (input : CommonSeedTrace Seed (fun _ => Ω) n × Ω) :
    commonArrayFinal n (commonFinalArray n input) = input := by
  rcases input with ⟨trace, last⟩
  unfold commonFinalArray commonArrayFinal
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  exact Prod.ext (commonArrayToTrace_toArray n trace) rfl

section Law

variable [Fintype Seed] [Fintype Ω] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]
  (random : Measure Ω) [IsProbabilityMeasure random]

omit [DecidableEq Seed] [IsProbabilityMeasure incoming] in
theorem commonArrayFinal_law (n : ℕ) :
    (incoming.prod (Measure.pi fun _ : Fin (n + 1) => random)).map (commonArrayFinal (Ω := Ω) n) =
      (commonTraceLaw (fun _ => random) incoming n).prod random := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨trace, last⟩
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have hpre : commonArrayFinal (Ω := Ω) n ⁻¹' {(trace, last)} =
      {commonFinalArray n (trace, last)} := by
    ext input
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      rw [← h, commonArrayFinal_inverse]
    · rintro rfl
      exact commonFinalArray_inverse n (trace, last)
  rw [hpre]
  change (incoming.prod (Measure.pi fun _ : Fin (n + 1) => random))
    {((commonTraceToArray n trace).1, Fin.snoc (commonTraceToArray n trace).2 last)} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, Measure.pi_singleton,
    Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [← mul_assoc, ← commonArrayToTrace_atom incoming random n (commonTraceToArray n trace),
    commonArrayToTrace_toArray, ← Set.singleton_prod_singleton, Measure.prod_prod]

end Law

section MapLaw

variable [Fintype Seed] [Fintype Ω] [Fintype Δ] [DecidableEq Seed]
  [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Δ] [MeasurableSingletonClass Δ]
  (incoming : Measure Seed) [IsProbabilityMeasure incoming]
  (random : Measure Ω) [IsProbabilityMeasure random]

omit [Fintype Δ] [DecidableEq Seed] [MeasurableSingletonClass Δ]
  [IsProbabilityMeasure incoming] [IsProbabilityMeasure random] in
 theorem mapCommonTrace_law (f : Ω → Δ) (n : ℕ) :
    (commonTraceLaw (fun _ => random) incoming n).map (mapCommonTrace f n) =
      commonTraceLaw (fun _ => random.map f) incoming n := by
  induction n with
  | zero => exact Measure.map_id
  | succ n ih =>
    change ((commonTraceLaw (fun _ => random) incoming n).prod random).map
      (Prod.map (mapCommonTrace f n) f) = _
    rw [← Measure.map_prod_map _ _ (measurable_of_finite _) (measurable_of_finite _), ih]
    rfl

end MapLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteArrayMarginal
attribute [-instance] _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Law

variable {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

 theorem finite_init_last_law (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => μ).map
      (fun draw => ((fun i : Fin n => draw i.castSucc), draw (Fin.last n))) =
    (Measure.pi fun _ : Fin n => μ).prod μ := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨front, last⟩
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have hpre : (fun draw : Fin (n + 1) → Ω =>
      ((fun i : Fin n => draw i.castSucc), draw (Fin.last n))) ⁻¹' {(front, last)} =
      {Fin.snoc front last} := by
    ext draw
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨hp, hl⟩
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hl
      · simpa only [Fin.snoc_castSucc] using congrFun hp j
    · rintro rfl
      constructor
      · funext i; simp only [Fin.snoc_castSucc]
      · simp only [Fin.snoc_last]
  rw [hpre, Measure.pi_singleton, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, Measure.pi_singleton]

 theorem finite_init_law (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => μ).map
      (fun draw (i : Fin n) => draw i.castSucc) = Measure.pi fun _ : Fin n => μ := by
  have h := congrArg (fun law : Measure ((Fin n → Ω) × Ω) => law.map Prod.fst)
    (finite_init_last_law μ n)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _), Measure.map_fst_prod] at h
  simpa only [Function.comp_def, measure_univ, one_smul] using h

end Law

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarSource
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Each common array source is realized by scalar exact uniform draws.
Regrouping finite coordinates recovers the common source law; unused
coordinates belong only to the probability space. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem finite_pi_curry {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {X : (i : ι) → κ i → Type*} [∀ i j, MeasurableSpace (X i j)]
    (μ : ∀ i j, Measure (X i j)) [∀ i j, IsProbabilityMeasure (μ i j)] :
    (Measure.pi fun p : Sigma κ => μ p.1 p.2).map (fun draw i j => draw ⟨i, j⟩) =
      Measure.pi fun i => Measure.pi (μ i) := by
  have h := Measure.infinitePi_map_piCurry μ
  simp only [Measure.infinitePi_eq_pi, MeasurableEquiv.coe_piCurry] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

theorem finite_uniform_three_curry {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {κ₂ : (i : ι) → κ i → Type*} [∀ i j, Fintype (κ₂ i j)]
    (M : ℕ) [NeZero M] :
    (Measure.pi fun _ : Σ i, Σ j : κ i, κ₂ i j => (PMF.uniformOfFintype (Fin M)).toMeasure).map
      (fun draw i j k => draw ⟨i, j, k⟩) =
    Measure.pi fun i => Measure.pi fun j : κ i => Measure.pi fun _ : κ₂ i j =>
      (PMF.uniformOfFintype (Fin M)).toMeasure := by
  let μ := fun (i : ι) (_ : Σ j : κ i, κ₂ i j) => (PMF.uniformOfFintype (Fin M)).toMeasure
  have hfirst := finite_pi_curry μ
  have hsecond := Measure.pi_map_pi
    (μ := fun i => Measure.pi (μ i))
    (f := fun (i : ι) (draw : (Σ j : κ i, κ₂ i j) → Fin M) (j : κ i) (k : κ₂ i j) => draw ⟨j, k⟩)
    (fun _ => (measurable_of_finite _).aemeasurable)
  have heach (i : ι) := finite_pi_curry (fun (j : κ i) (_ : κ₂ i j) =>
    (PMF.uniformOfFintype (Fin M)).toMeasure)
  dsimp only [μ] at hsecond
  simp_rw [heach] at hsecond
  rw [← hfirst, Measure.map_map (by fun_prop) (by fun_prop)] at hsecond
  exact hsecond











section Laws

variable (M J N n exponent F Q R B : ℕ) [NeZero M]

 theorem physicalScalarCoordinatePack_law (key : PhysicalCommonKey M J N n exponent B) :
    (Measure.pi fun index : PhysicalScalarIndex M J N n exponent F Q R B key =>
      (PMF.uniformOfFintype (Fin (physicalScalarRange M J N n exponent F Q R B ⟨key, index⟩))).toMeasure).map
        (physicalScalarCoordinatePack M J N n exponent F Q R B key) =
      physicalCommonCoordinateLaw M J N n exponent F Q R B key := by
  cases key with
  | inl online => exact Measure.map_id
  | inr group => exact finite_uniform_three_curry M

 theorem physicalScalarPack_law :
    (physicalScalarLaw M J N n exponent F Q R B).map
        (physicalScalarPack M J N n exponent F Q R B) =
      physicalCommonLaw M J N n exponent F Q R B := by
  let μ := fun (key : PhysicalCommonKey M J N n exponent B)
      (index : PhysicalScalarIndex M J N n exponent F Q R B key) =>
    (PMF.uniformOfFintype (Fin (physicalScalarRange M J N n exponent F Q R B ⟨key, index⟩))).toMeasure
  have hfirst := finite_pi_curry μ
  have hsecond := Measure.pi_map_pi (μ := fun key => Measure.pi (μ key))
    (f := physicalScalarCoordinatePack M J N n exponent F Q R B)
    (fun _ => (measurable_of_finite _).aemeasurable)
  have heach := physicalScalarCoordinatePack_law M J N n exponent F Q R B
  dsimp only [μ] at hsecond
  simp_rw [heach] at hsecond
  rw [← hfirst, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at hsecond
  exact hsecond

end Laws

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarFamilyLaw
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regrouping the finite physical scalar source gives exactly one fresh
common draw for each pass and copy. This is equality of product laws,
not an assumption about the sampler. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

 theorem finite_pi_product_curry {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : κ → Type*} [∀ j, Fintype (X j)] [∀ j, MeasurableSpace (X j)]
    [∀ j, MeasurableSingletonClass (X j)] (μ : ∀ j, Measure (X j))
    [∀ j, IsProbabilityMeasure (μ j)] :
    (Measure.pi fun pair : ι × κ => μ pair.2).map (fun draw i j => draw (i, j)) =
      Measure.pi fun _ : ι => Measure.pi μ := by
  classical
  apply Measure.ext_of_singleton
  intro result
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hpre : (fun draw i j => draw (i, j)) ⁻¹' {result} =
      {fun pair : ι × κ => result pair.1 pair.2} := by
    ext draw
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext pair
      exact congrFun (congrFun h pair.1) pair.2
    · rintro rfl
      rfl
  rw [hpre]
  simp only [Measure.pi_singleton]
  simpa only [Finset.univ_product_univ] using
    (Finset.prod_product (Finset.univ : Finset ι) (Finset.univ : Finset κ)
      (fun pair => μ pair.2 {result pair.1 pair.2}))

section FamilyLaw

variable {α : Type*} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)

local notation "Key" => PhysicalScalarKey M J N target.length exponent F Q R (localOnlineMassBound M P H)
local notation "range" => physicalScalarRange M J N target.length exponent F Q R (localOnlineMassBound M P H)

 theorem physicalFamilyCurry_law :
    (physicalFamilyLaw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies).map
      (physicalFamilyCurry target N P F exponent H Q passes copies) =
    Measure.pi fun _ : Fin (passes + 1) => Measure.pi fun _ : Fin (copies + 1) =>
      physicalScalarLaw M J N target.length exponent F Q R (localOnlineMassBound M P H) := by
  let μ : ∀ key : Key, Measure (Fin (range key)) := fun key =>
    (PMF.uniformOfFintype (Fin (range key))).toMeasure
  have hfirst := finite_pi_product_curry (ι := Fin (passes + 1))
    (κ := Fin (copies + 1) × Key) (fun pair => μ pair.2)
  have hsecond := Measure.pi_map_pi
    (μ := fun _ : Fin (passes + 1) => Measure.pi fun pair : Fin (copies + 1) × Key => μ pair.2)
    (f := fun (_ : Fin (passes + 1)) draw (copy : Fin (copies + 1)) (key : Key) => draw (copy, key))
    (fun _ => (measurable_of_finite _).aemeasurable)
  have hrow := finite_pi_product_curry (ι := Fin (copies + 1)) μ
  have htarget : (Measure.pi fun _ : Fin (passes + 1) =>
      (Measure.pi fun pair : Fin (copies + 1) × Key => μ pair.2).map
        (fun draw copy key => draw (copy, key))) =
      Measure.pi fun _ : Fin (passes + 1) => Measure.pi fun _ : Fin (copies + 1) => Measure.pi μ := by
    simp only [hrow]
  rw [← hfirst, Measure.map_map (by fun_prop) (by fun_prop)] at hsecond
  exact hsecond.trans htarget

 theorem physicalFamilyPack_law :
    (physicalFamilyLaw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies).map
      (physicalFamilyPack target N P F exponent H Q passes copies) =
    Measure.pi fun _ : Fin (passes + 1) => Measure.pi fun _ : Fin (copies + 1) =>
      physicalCommonLaw M J N target.length exponent F Q R (localOnlineMassBound M P H) := by
  let pack := physicalScalarPack M J N target.length exponent F Q R (localOnlineMassBound M P H)
  have hrow := Measure.pi_map_pi
    (μ := fun _ : Fin (copies + 1) => physicalScalarLaw M J N target.length exponent F Q R (localOnlineMassBound M P H))
    (f := fun _ => pack) (fun _ => (measurable_of_finite _).aemeasurable)
  have hrow' : (Measure.pi fun _ : Fin (copies + 1) =>
      physicalScalarLaw M J N target.length exponent F Q R (localOnlineMassBound M P H)).map
      (fun row copy => pack (row copy)) =
      Measure.pi fun _ : Fin (copies + 1) =>
        physicalCommonLaw M J N target.length exponent F Q R (localOnlineMassBound M P H) := by
    exact hrow.trans (by simp only [pack, physicalScalarPack_law])
  have h := Measure.pi_map_pi
    (μ := fun _ : Fin (passes + 1) => Measure.pi fun _ : Fin (copies + 1) =>
      physicalScalarLaw M J N target.length exponent F Q R (localOnlineMassBound M P H))
    (f := fun _ row copy => pack (row copy)) (fun _ => (measurable_of_finite _).aemeasurable)
  rw [← physicalFamilyCurry_law target N P F exponent H Q passes copies,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h.trans (by simp only [hrow'])

end FamilyLaw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyTrace
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.rejectionRuntimeArrayLaw_probability _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal finite scalar family supplies the independent common
source trace and its final draw, after removing unused extra copies. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section SourceFamily

variable {Seed α : Type} {M J R : ℕ} [NeZero M]
  (target : List α) (N P F exponent H Q passes copies : ℕ)

local notation "Draw" => PhysicalCommonDraw M J N target.length exponent F Q R (localOnlineMassBound M P H)
local notation "Family" => PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
  target N P F exponent H Q passes copies
local notation "μ" => physicalCommonLaw M J N target.length exponent F Q R (localOnlineMassBound M P H)

variable [Fintype Seed] [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
  (incoming : Measure Seed)

 theorem physicalFamilyToTrace_law :
    (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)).map
      (physicalFamilyToTrace (Seed := Seed) target N P F exponent H Q passes copies) =
    (commonTraceLaw (fun _ => Measure.pi fun _ : Fin copies => μ) incoming passes).prod μ := by
  classical
  let : MeasurableSingletonClass Draw := inferInstance
  let : MeasurableSingletonClass (Fin (copies + 1) → Draw) := inferInstance
  let : MeasurableSingletonClass (Fin (passes + 1) → Fin (copies + 1) → Draw) := inferInstance
  let := commonSeedTraceFintype Seed (fun _ => Fin (copies + 1) → Draw) passes
  let := commonSeedTraceSingleton Seed (fun _ => Fin (copies + 1) → Draw) passes
  let rowLaw : Measure (Fin (copies + 1) → Draw) := Measure.pi fun _ => μ
  let trim : (Fin (copies + 1) → Draw) → (Fin copies → Draw) := fun row copy => row copy.castSucc
  let finish : (Fin (copies + 1) → Draw) → Draw := fun row => row 0
  let pack : Seed × Family → Seed × (Fin (passes + 1) → Fin (copies + 1) → Draw) :=
    Prod.map (id : Seed → Seed)
    (physicalFamilyPack target N P F exponent H Q passes copies)
  let finalMap := Prod.map (mapCommonTrace (Seed := Seed) trim passes) finish
  have hpack : (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies)).map pack =
      incoming.prod (Measure.pi fun _ : Fin (passes + 1) => rowLaw) := by
    dsimp only [pack, rowLaw]
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_of_finite _), Measure.map_id,
      physicalFamilyPack_law]
  have hrow : rowLaw.map trim = Measure.pi fun _ : Fin copies => μ :=
    finite_init_law μ copies
  have hlast : rowLaw.map finish = μ := by
    simpa only [measure_univ, Finset.prod_const_one, one_smul] using
      (Measure.pi_map_eval (fun _ : Fin (copies + 1) => μ) 0)
  have hmap : ((commonTraceLaw (fun _ => rowLaw) incoming passes).prod rowLaw).map finalMap =
      (commonTraceLaw (fun _ => Measure.pi fun _ : Fin copies => μ) incoming passes).prod μ := by
    dsimp only [finalMap]
    rw [← Measure.map_prod_map _ _ (measurable_of_finite _) (measurable_of_finite _),
      mapCommonTrace_law incoming rowLaw trim passes, hrow, hlast]
  have heq : physicalFamilyToTrace (Seed := Seed) target N P F exponent H Q passes copies =
      finalMap ∘ commonArrayFinal passes ∘ pack := rfl
  rw [heq, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), hpack,
    commonArrayFinal_law incoming rowLaw passes]
  exact hmap

end SourceFamily

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyOutput
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Output

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ) (hP : 0 < P)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N

 theorem physicalFamilyFinalAnswer_law_oai (hH : 0 < H) (incoming : Measure SeedState)
    [IsProbabilityMeasure incoming] (rootQ : TargetInterval target.length) :
    (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2))).map
        (physicalFamilyFinalAnswer source target N P T S H hP rootQ) =
    (localFinalProgramLaw (R := R) source target N P T S H incoming).map
        (localFinalProgramAnswer (R := R) source target N P T S H rootQ) := by
  classical
  let : MeasurableSingletonClass (PhysicalCommonDraw M J N target.length exponent ell
      (ell ^ 80) R (localOnlineMassBound M P H)) := inferInstance
  let := commonSeedTraceFintype SeedState
    (fun _ => LocalCommonDraw (M := M) (J := J) (R := R) target N P H) passes
  let := commonSeedTraceSingleton SeedState
    (fun _ => LocalCommonDraw (M := M) (J := J) (R := R) target N P H) passes
  have heq : physicalFamilyFinalAnswer (R := R) source target N P T S H hP rootQ =
      localCommonMemoAnswer (M := M) (J := J) (R := R) source target N P T S H hP hH rootQ ∘
        physicalFamilyToTrace target N P ell exponent H (ell ^ 80) passes (H ^ 2) := by
    funext input
    exact physicalFamilyFinalAnswer_eq source target N P T S H hP hH rootQ input
  have htrace : (incoming.prod (physicalFamilyLaw (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2))).map
      (physicalFamilyToTrace target N P ell exponent H (ell ^ 80) passes (H ^ 2)) =
      localCommonFinalLaw (M := M) (J := J) (R := R) target N P H incoming := by
    exact physicalFamilyToTrace_law (Seed := SeedState) (M := M) (J := J) (R := R)
      target N P ell exponent H (ell ^ 80) passes (H ^ 2) incoming
  rw [heq, ← Measure.map_map (measurable_of_finite _) (measurable_of_finite _), htrace]
  exact localCommonMemoAnswer_law source target N P T S H hP hH incoming rootQ

end Output

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.physicalFamilyFinalAnswer_law_oai := @OAI.EditApproximation.physicalFamilyFinalAnswer_law_oai
