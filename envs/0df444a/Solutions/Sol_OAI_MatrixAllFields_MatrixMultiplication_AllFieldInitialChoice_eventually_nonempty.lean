-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.eventually_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:54:24.150759+00:00
-- url     : https://prove2.me/submissions/7e60d878-2c18-4880-94d4-5e075b4cb4c3

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialOrbit_weighted_shape_fiber_count
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointOrdinaryPopulationSelection_eventually_exists_selection_of_word_support

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

theorem homogeneousEntropy_normalized {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∑ a, p a = 1) :
    homogeneousEntropy p = finiteEntropy p := by
  simp [homogeneousEntropy, hp]

end

end MatrixMultiplication.AllFieldParameters

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_PopulationCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldPopulationCounts

open scoped BigOperators

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem blockLength_pos (w : I → ℚ) {m : ℕ} (hm : 0 < m) :
    0 < blockLength w m := Nat.mul_pos hm (denominator_pos w)

end

end MatrixMultiplication.AllFieldPopulationCounts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationRates

open MatrixMultiplication.Foundation Filter JointPopulation
open scoped BigOperators Topology

theorem sideMass_total (p : Shape → ℝ) (s : Fin 3) :
    (∑ a, sideMass p s a) = ∑ u, p u := by
  unfold sideMass
  rw [Finset.sum_comm]
  simp

end MatrixMultiplication.JointPopulationRates






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointOrdinaryPopulationSelection
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section

namespace MatrixMultiplication.JointOrdinaryPopulationSelection

open MatrixMultiplication.Foundation JointPopulation JointPopulationRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {Hist : Type*} [Fintype Hist] [DecidableEq Hist]

theorem eventually_exists_selection
    (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (mass : Hist → ℝ)
    (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ) (c : Hist → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (hcountSupport : ∀ N h a, 0 < counts N h a →
      a.1.val + a.2.1.val + a.2.2.val = sum h)
    (hsupport : ∀ h (a : Shape),
      a.1.val + a.2.1.val + a.2.2.val = sum h → 0 < (p h).mass a)
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h)
    (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
      atTop (𝓝 (mass h * (p h).mass a)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop,
      ∃ (s : JointCoarseHashing.Sample (Position (counts N))
          (JointOrdinarySelection.hashLevel (selectionHashRate mass p ε) N))
        (G : Finset (Target (counts N))),
        G.card = ⌊Real.exp ((N : ℝ) * (entropyRate mass p - degreeRate mass p - ε))⌋₊ ∧
        (∀ e ∈ G, JointOrdinarySelection.Good
          (JointOrdinarySelection.hashLevel (selectionHashRate mass p ε) N)
          (JointOrdinarySelection.hashSet (selectionHashRate mass p ε) N)
          (ambientSet (counts N) sum) (triple (counts N) e) s) ∧
        (G : Set (Target (counts N))).Pairwise (fun e f =>
          ¬ JointCoarseHashing.SharesSide (triple (counts N) e) (triple (counts N) f)) :=
  eventually_exists_selection_of_word_support counts sum mass p u v w c
    hmass hcountSupport
    (Eventually.of_forall fun _ h word hw i => hsupport h (word i) (hw.1 i))
    hlog hcounts hε

end MatrixMultiplication.JointOrdinaryPopulationSelection

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_InitialEntropy
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropy

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation
open JointPopulationRates JointOrdinaryPopulationSelection
open scoped BigOperators

theorem placement_read_card : ∀ s w : Fin 3,
    Fintype.card {phi : Placement // phi.symm s = w} = 2 := by
  decide +kernel

theorem sum_placement_read (s : Fin 3) (f : Fin 3 → ℝ) :
    (∑ phi : Placement, f (phi.symm s)) = 2 * ∑ w, f w := by
  classical
  rw [← Fintype.sum_fiberwise' (fun phi : Placement => phi.symm s) f]
  simp only [Finset.sum_const, Finset.card_univ, placement_read_card,
    nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]

theorem sideMass_orderedInitialLaw (s : Fin 3) (k : Fin 17) :
    sideMass orderedInitialLaw.mass s k =
      ∑ p : PlacedInitial,
        if JointPopulation.shapeSide s (initialShapeCode p) = k
          then placedInitialLaw.mass p else 0 := by
  classical
  unfold sideMass orderedInitialLaw
  simp only [FiniteLaw.map_mass]
  calc
    _ = ∑ u : JointPopulation.Shape, ∑ p : PlacedInitial,
        if initialShapeCode p = u then
          if JointPopulation.shapeSide s u = k then placedInitialLaw.mass p else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : JointPopulation.shapeSide s u = k <;> simp [hu]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem orderedInitialLaw_sideMass (s : Fin 3) :
    sideMass orderedInitialLaw.mass s = nativeInitialMarginal := by
  classical
  funext k
  rw [sideMass_orderedInitialLaw, Fintype.sum_prod_type]
  unfold nativeInitialMarginal
  apply Finset.sum_congr rfl
  intro g _
  have hside (phi : Placement) :
      JointPopulation.shapeSide s (initialShapeCode (g, phi)) = k ↔
        sortedInitial.get g (phi.symm s) = k.val := by
    rw [← Fin.val_inj, initialShapeCode_side]
  simp only [hside, placedInitialLaw]
  calc
    _ = ∑ phi : Placement, ((initialLaw (sortedInitial.get g) : ℝ) / 6) *
        (if sortedInitial.get g (phi.symm s) = k.val then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro phi _
      split_ifs <;> ring
    _ = ((initialLaw (sortedInitial.get g) : ℝ) / 6) *
        (2 * ∑ w : Fin 3, if sortedInitial.get g w = k.val then 1 else 0) := by
      rw [← Finset.mul_sum,
        sum_placement_read s (fun w : Fin 3 =>
          if sortedInitial.get g w = k.val then 1 else 0)]
    _ = _ := by ring

theorem nativeInitialMarginal_total : ∑ k, nativeInitialMarginal k = 1 := by
  rw [← orderedInitialLaw_sideMass 0, sideMass_total, orderedInitialLaw.total]

theorem nativeH0_eq_finiteEntropy : nativeH0 = finiteEntropy nativeInitialMarginal :=
  homogeneousEntropy_normalized _ nativeInitialMarginal_total

theorem orderedInitialLaw_side_entropy (s : Fin 3) :
    finiteEntropy (sideMass orderedInitialLaw.mass s) = nativeH0 := by
  rw [orderedInitialLaw_sideMass, nativeH0_eq_finiteEntropy]

theorem population_cast_real {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : History K) :
    (population allocation dilation h : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        (amount allocation h : ℝ) := by
  exact_mod_cast population_cast allocation dilation h

theorem initialJointCounts_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) (u : JointPopulation.Shape) :
    (initialJointCounts allocation dilation j u : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) * orderedInitialLaw.mass u := by
  classical
  unfold initialJointCounts shapeCounts orderedInitialLaw
  simp only [FiniteLaw.map_mass, Nat.cast_sum, Finset.mul_sum,
    rootShape_eq_initialShapeCode]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : initialShapeCode p = u
  · simp only [hp, ite_true, if_true, population_cast_real, placedInitialLaw]
    congr 1
    simp only [amount, canonicalAmount, initialAmount, initialShape,
      Rat.cast_div, Rat.cast_ofNat]
  · simp [hp]

end MatrixMultiplication.AllFieldInitialEntropy

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InitialOrbit
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldInitialOrbit

open AllFieldParameters AllFieldHistory AllFieldInitialEntropy
open scoped BigOperators

theorem source_total (p : PlacedInitial) :
    (initialShapeCode p).1.val + (initialShapeCode p).2.1.val +
      (initialShapeCode p).2.2.val = 16 := by
  unfold initialShapeCode rootShape
  rw [encodePhysicalShape_total]
  exact (root_shape_spec _ (initialShape_mem _)).2

theorem decodeShape_injective : Function.Injective decodeShape := by
  intro u v h
  apply Prod.ext
  · exact Fin.ext (congrFun h 0)
  · apply Prod.ext
    · exact Fin.ext (congrFun h 1)
    · exact Fin.ext (congrFun h 2)

theorem decodeShape_mem_shapes (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    decodeShape u ∈ shapes 16 := by
  simp only [shapes, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨u.1.val, by omega, u.2.1.val, by omega, ?_⟩
  funext i
  fin_cases i
  · rfl
  · rfl
  · change 16 - u.1.val - u.2.1.val = u.2.2.val
    omega

theorem initialShapeCode_eq_iff (p : PlacedInitial) (u : JointPopulation.Shape) :
    initialShapeCode p = u ↔
      physicalShape p.2 (sortedInitial.get p.1) = decodeShape u := by
  have hdecode : decodeShape (initialShapeCode p) =
      physicalShape p.2 (sortedInitial.get p.1) := by
    funext i
    exact initialShapeCode_side p i
  rw [← hdecode]
  exact decodeShape_injective.eq_iff.symm

theorem weighted_fiber_count (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    (∑ p : PlacedInitial, if initialShapeCode p = u
      then initialMultiplicity (sortedInitial.get p.1) else 0) = 6 := by
  simp only [initialShapeCode_eq_iff]
  exact weighted_shape_fiber_count _ (decodeShape_mem_shapes u hu)

end MatrixMultiplication.AllFieldInitialOrbit

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_InitialFamily
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldInitialGibbs

open AllFieldParameters AllFieldHistory AllFieldInitialEntropy AllFieldInitialOrbit
open MatrixMultiplication.Foundation
open scoped BigOperators

theorem coordinateWeight_pos (k : Fin 17) : 0 < coordinateWeight k := by
  apply Rat.cast_pos.mpr
  apply weight_positive_of_argument_bound
  exact assigned_argument_bound _ tablea initial_table_arguments_bounded _

theorem orderedWeight_pos (u : JointPopulation.Shape) : 0 < orderedWeight u :=
  Finset.prod_pos (fun _ _ => coordinateWeight_pos _)

theorem initialNormalizer_pos : 0 < initialNormalizer := by
  apply Rat.cast_pos.mpr
  exact list_sum_map_positive _ _ (by decide +kernel)
    (fun s _ => initialWeight_positive s)

theorem orderedWeight_source (p : PlacedInitial) :
    orderedWeight (initialShapeCode p) =
      ∏ s : Fin 3, (weight (initialInteger (sortedInitial.get p.1 s)) : ℝ) := by
  simp only [orderedWeight, coordinateWeight, initialShapeCode_side]
  exact p.2.symm.prod_comp
    (fun s : Fin 3 => (weight (initialInteger (sortedInitial.get p.1 s)) : ℝ))

theorem initialWeight_source (p : PlacedInitial) :
    (initialWeight (sortedInitial.get p.1) : ℝ) =
      (initialMultiplicity (sortedInitial.get p.1) : ℝ) *
        orderedWeight (initialShapeCode p) := by
  rw [orderedWeight_source]
  simp only [initialWeight]
  push_cast
  rfl

theorem placedInitialLaw_mass (p : PlacedInitial) :
    placedInitialLaw.mass p =
      (initialMultiplicity (sortedInitial.get p.1) : ℝ) *
        orderedWeight (initialShapeCode p) / initialNormalizer / 6 := by
  change (initialLaw (sortedInitial.get p.1) : ℝ) / 6 = _
  rw [initialLaw, ite_eq_left (List.get_mem _ _), Rat.cast_div, initialWeight_source p]
  rfl

theorem orderedInitialLaw_mass (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    orderedInitialLaw.mass u = orderedWeight u / initialNormalizer := by
  classical
  have hcount : (∑ p : PlacedInitial,
      if initialShapeCode p = u then
        (initialMultiplicity (sortedInitial.get p.1) : ℝ) else 0) = 6 := by
    exact_mod_cast weighted_fiber_count u hu
  simp only [orderedInitialLaw, FiniteLaw.map_mass, placedInitialLaw_mass]
  calc
    _ = (∑ p : PlacedInitial, if initialShapeCode p = u then
          (initialMultiplicity (sortedInitial.get p.1) : ℝ) else 0) *
        (orderedWeight u / initialNormalizer / 6) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : initialShapeCode p = u
      · simp only [hp, ite_true, if_true]
        ring
      · simp only [hp, ite_false, if_false, zero_mul]
    _ = _ := by rw [hcount]; ring

theorem orderedInitialLaw_zero (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val ≠ 16) :
    orderedInitialLaw.mass u = 0 := by
  classical
  simp only [orderedInitialLaw, FiniteLaw.map_mass]
  apply Finset.sum_eq_zero
  intro p _
  apply ite_eq_right
  intro hp
  have ht := source_total p
  rw [hp] at ht
  exact hu ht

theorem orderedInitialLaw_positive (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    0 < orderedInitialLaw.mass u := by
  rw [orderedInitialLaw_mass u hu]
  exact div_pos (orderedWeight_pos u) initialNormalizer_pos

theorem orderedInitialLaw_support (u : JointPopulation.Shape)
    (hu : 0 < orderedInitialLaw.mass u) :
    u.1.val + u.2.1.val + u.2.2.val = 16 := by
  by_contra hn
  rw [orderedInitialLaw_zero u hn] at hu
  exact lt_irrefl _ hu

theorem log_orderedWeight (u : JointPopulation.Shape) :
    Real.log (orderedWeight u) =
      initialPotential (JointPopulation.shapeSide 0 u) +
        initialPotential (JointPopulation.shapeSide 1 u) +
        initialPotential (JointPopulation.shapeSide 2 u) := by
  rw [orderedWeight, Real.log_prod
    (fun s _ => ne_of_gt (coordinateWeight_pos (JointPopulation.shapeSide s u)))]
  simp only [Fin.sum_univ_three, initialPotential]

theorem orderedInitialLaw_log (u : JointPopulation.Shape)
    (hu : 0 < orderedInitialLaw.mass u) :
    Real.log (orderedInitialLaw.mass u) =
      initialPotential (JointPopulation.shapeSide 0 u) +
        initialPotential (JointPopulation.shapeSide 1 u) +
        initialPotential (JointPopulation.shapeSide 2 u) - initialLogNormalizer := by
  rw [orderedInitialLaw_mass u (orderedInitialLaw_support u hu),
    Real.log_div (ne_of_gt (orderedWeight_pos u)) (ne_of_gt initialNormalizer_pos),
    log_orderedWeight]
  rfl

end MatrixMultiplication.AllFieldInitialGibbs

namespace MatrixMultiplication.AllFieldInitialFamily

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldFiniteFamily
open AllFieldInitialEntropy JointOrdinaryPopulationSelection Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {K : ℕ} (allocation : Allocation)

theorem grid_pos : 0 < grid (K := K) allocation :=
  AllFieldPopulationCounts.blockLength_pos (amount (K := K) allocation) (by decide)

theorem populationLength_eq_mul_grid (dilation : ℕ) :
    populationLength (K := K) allocation dilation = dilation * grid (K := K) allocation := by
  simp only [grid, populationLength, AllFieldPopulationCounts.blockLength, one_mul]

theorem initialJointCounts_dilation_ratio {dilation : ℕ} (hd : 0 < dilation)
    (j : Fin K) (u : JointPopulation.Shape) :
    (initialJointCounts allocation dilation j u : ℝ) / (dilation : ℝ) =
      (grid (K := K) allocation : ℝ) * orderedInitialLaw.mass u := by
  rw [initialJointCounts_cast, populationLength_eq_mul_grid, Nat.cast_mul, mul_assoc]
  have hd' : (dilation : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  exact mul_div_cancel_left₀ _ hd'

theorem initialJointCounts_dilation_rate (j : Fin K) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ =>
      (initialJointCounts allocation dilation j u : ℝ) / (dilation : ℝ)) atTop
      (𝓝 ((grid (K := K) allocation : ℝ) * orderedInitialLaw.mass u)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with dilation hd
  exact (initialJointCounts_dilation_ratio allocation hd j u).symm

theorem native_dilation_capacity :
    entropyRate (fun _ : Fin K => (grid (K := K) allocation : ℝ))
      (fun _ => orderedInitialLaw) -
    degreeRate (fun _ : Fin K => (grid (K := K) allocation : ℝ))
      (fun _ => orderedInitialLaw) =
      (grid (K := K) allocation : ℝ) * ((K : ℝ) * nativeH0) := by
  simp only [entropyRate, degreeRate, sideDegreeRate, orderedInitialLaw_side_entropy,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, max_self]
  ring

theorem selection_exponent (ε : ℝ) (dilation : ℕ) :
    (dilation : ℝ) *
        (entropyRate (fun _ : Fin K => (grid (K := K) allocation : ℝ))
            (fun _ => orderedInitialLaw) -
          degreeRate (fun _ : Fin K => (grid (K := K) allocation : ℝ))
            (fun _ => orderedInitialLaw) - (grid (K := K) allocation : ℝ) * ε) =
      (populationLength (K := K) allocation dilation : ℝ) * ((K : ℝ) * nativeH0 - ε) := by
  rw [native_dilation_capacity, populationLength_eq_mul_grid, Nat.cast_mul]
  ring

theorem eventually_exists_execution_with_width (F : Type*) [Field F]
    (residentWidth : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ dilation in atTop,
      ∃ (s : Sample (K := K) allocation ε dilation)
        (G : Finset (JointPopulation.Target (initialJointCounts (K := K) allocation dilation))),
        G.card = ⌊Real.exp ((populationLength (K := K) allocation dilation : ℝ) *
          ((K : ℝ) * nativeH0 - ε))⌋₊ ∧
        (∀ e ∈ G, Good allocation ε dilation s e) ∧
        ∃ E : Execution (cwSource F K (populationLength (K := K) allocation dilation))
            (Tensor.directSum (fun _ : AllFieldInitialHash.SelectedTargets
                (initialJointCounts (K := K) allocation dilation) G =>
              stateTensor F (K := K) allocation dilation residentWidth 0)),
          Fintype.card E.Copies = 1 := by
  have hslack : 0 < (grid (K := K) allocation : ℝ) * ε :=
    mul_pos (by exact_mod_cast grid_pos (K := K) allocation) hε
  have hselection := JointOrdinaryPopulationSelection.eventually_exists_selection
    (fun dilation => initialJointCounts (K := K) allocation dilation) (fun _ => 16)
    (fun _ : Fin K => (grid (K := K) allocation : ℝ)) (fun _ => orderedInitialLaw)
    (fun _ => AllFieldInitialGibbs.initialPotential)
    (fun _ => AllFieldInitialGibbs.initialPotential)
    (fun _ => AllFieldInitialGibbs.initialPotential)
    (fun _ => AllFieldInitialGibbs.initialLogNormalizer)
    (fun _ => Nat.cast_nonneg _)
    (fun dilation => initialJointCounts_support allocation dilation)
    (fun _ => AllFieldInitialGibbs.orderedInitialLaw_positive)
    (fun _ => AllFieldInitialGibbs.orderedInitialLaw_log)
    (initialJointCounts_dilation_rate allocation) hslack
  filter_upwards [hselection] with dilation hd
  obtain ⟨s, G, hcard, hgood, _hpairwise⟩ := hd
  rw [selection_exponent allocation ε dilation] at hcard
  exact ⟨s, G, hcard, hgood,
    executionWithWidth allocation F ε residentWidth dilation s G hgood,
    executionWithWidth_copies allocation F ε residentWidth dilation s G hgood⟩

end MatrixMultiplication.AllFieldInitialFamily

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_ConstructionLabels
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldConstructionRates

open MatrixMultiplication.Foundation AllFieldHistory AllFieldScheduledYield
open AllFieldActiveLaws Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

theorem initialCount_eq (allocation : Allocation) (δ : ℝ) (m : ℕ) :
    initialCount (K := K) allocation δ m =
      ⌊Real.exp ((m : ℝ) * ((populationLength (K := K) allocation 1 : ℝ) *
        ((K : ℝ) * AllFieldInitialEntropy.nativeH0) - δ))⌋₊ := rfl

end MatrixMultiplication.AllFieldConstructionRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_OrderedLimits
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialChoice

open MatrixMultiplication.Foundation AllFieldHistory AllFieldFiniteFamily Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

theorem initial_count_eq (allocation : Allocation) (m : ℕ) (δ : ℝ) :
    ⌊Real.exp ((populationLength (K := K) allocation m : ℝ) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0 -
        δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)))⌋₊ =
      AllFieldConstructionRates.initialCount (K := K) allocation δ m := by
  rw [AllFieldConstructionRates.initialCount_eq,
    AllFieldInitialFamily.populationLength_eq_mul_grid, Nat.cast_mul]
  congr 2
  change ((m : ℝ) * (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0 -
        δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ)) =
    (m : ℝ) * ((AllFieldInitialFamily.grid (K := K) allocation : ℝ) *
      ((K : ℝ) * AllFieldInitialEntropy.nativeH0) - δ)
  have hD : (AllFieldInitialFamily.grid (K := K) allocation : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (AllFieldInitialFamily.grid_pos allocation).ne'
  field_simp [hD]

theorem eventually_nonempty_oai (allocation : Allocation) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, Nonempty (Choice (K := K) allocation m δ) := by
  have hs : 0 < δ / (AllFieldInitialFamily.grid (K := K) allocation : ℝ) :=
    div_pos hδ (Nat.cast_pos.mpr (AllFieldInitialFamily.grid_pos allocation))
  have h := AllFieldInitialFamily.eventually_exists_execution_with_width
    (K := K) allocation ℚ 0 hs
  filter_upwards [h] with m hm
  obtain ⟨sample, selected, hcard, hgood, _execution⟩ := hm
  exact ⟨{
    sample := sample
    selected := selected
    card_selected := hcard.trans (initial_count_eq allocation m δ)
    good := hgood }⟩

end MatrixMultiplication.AllFieldInitialChoice

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.eventually_nonempty_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.eventually_nonempty_oai
