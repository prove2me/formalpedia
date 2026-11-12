-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldScheduledPositivity.nativeH0_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:48:45.490312+00:00
-- url     : https://prove2.me/submissions/81a55dc4-ea35-44a4-bc34-0345bdad87bd

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialOrbit_initialShapeCode_eq_iff
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialOrbit_weighted_shape_fiber_count

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

theorem mass_le_map_mass (p : FiniteLaw A) (f : A → B) (a : A) :
    p.mass a ≤ (p.map f).mass (f a) := by
  classical
  rw [map_mass]
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset A))
    (f := fun a' => if f a' = f a then p.mass a' else 0)
    (fun a' _ => by
      split_ifs
      · exact p.nonneg a'
      · exact le_rfl)
    (Finset.mem_univ a)
  simpa using h

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

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

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

theorem entropyTerm_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ entropyTerm p :=
  Real.negMulLog_nonneg hp₀ hp₁

namespace FiniteLaw

variable {A : Type*} [Fintype A]

theorem mass_le_one (p : FiniteLaw A) (a : A) : p.mass a ≤ 1 := by
  calc
    p.mass a ≤ ∑ b, p.mass b :=
      Finset.single_le_sum (fun b _hb => p.nonneg b) (Finset.mem_univ a)
    _ = 1 := p.total

end FiniteLaw
end MatrixMultiplication.Foundation

end
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
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_InitialEntropy
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
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
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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

theorem orderedInitialLaw_positive (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    0 < orderedInitialLaw.mass u := by
  rw [orderedInitialLaw_mass u hu]
  exact div_pos (orderedWeight_pos u) initialNormalizer_pos

end MatrixMultiplication.AllFieldInitialGibbs

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_ScheduledPositivity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldScheduledPositivity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldInitialEntropy AllFieldNativeCapacity AllFieldScheduledYield Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

theorem nativeH0_pos_oai : 0 < nativeH0 := by
  let p := orderedInitialLaw.map (JointPopulation.shapeSide 0)
  have hzero : 0 < p.mass 0 := by
    have hp := AllFieldInitialGibbs.orderedInitialLaw_positive
      ((0 : Fin 17), (0 : Fin 17), (16 : Fin 17)) (by decide)
    exact hp.trans_le (orderedInitialLaw.mass_le_map_mass
      (JointPopulation.shapeSide 0) ((0 : Fin 17), (0 : Fin 17), (16 : Fin 17)))
  have hone : 0 < p.mass 1 := by
    have hp := AllFieldInitialGibbs.orderedInitialLaw_positive
      ((1 : Fin 17), (0 : Fin 17), (15 : Fin 17)) (by decide)
    exact hp.trans_le (orderedInitialLaw.mass_le_map_mass
      (JointPopulation.shapeSide 0) ((1 : Fin 17), (0 : Fin 17), (15 : Fin 17)))
  have hpair : p.mass 0 + p.mass 1 ≤ 1 := by
    have hs : (∑ k ∈ ({0, 1} : Finset (Fin 17)), p.mass k) ≤
        ∑ k : Fin 17, p.mass k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => p.nonneg k)
    simpa [p.total] using hs
  have hterm : 0 < entropyTerm (p.mass 0) :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos hzero) (Real.log_neg hzero (by linarith))
  have hentropy : 0 < finiteEntropy p.mass := hterm.trans_le
    (Finset.single_le_sum
      (fun k _ => entropyTerm_nonneg (p.nonneg k) (p.mass_le_one k))
      (Finset.mem_univ 0))
  rw [← orderedInitialLaw_side_entropy 0]
  have hm : p.mass = JointPopulationRates.sideMass orderedInitialLaw.mass 0 := by
    funext k
    simp only [p, FiniteLaw.map_mass, JointPopulationRates.sideMass]
  rw [← hm]
  exact hentropy

end MatrixMultiplication.AllFieldScheduledPositivity

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldScheduledPositivity.nativeH0_pos_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldScheduledPositivity.nativeH0_pos_oai
