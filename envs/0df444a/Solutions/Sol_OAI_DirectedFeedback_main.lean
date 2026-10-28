-- Prove2me | solution 1 for OAI.DirectedFeedback.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:18:14.663745+00:00
-- url     : https://prove2.me/submissions/d6ca53b5-8c43-44c4-b905-1f41b4436970

import Mathlib
import Definitions.Def_DirectedFeedback
import Definitions.Def_OAIQ085D030
import Theorems.Thm_OAI_DFVSGames_theorem11

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_CellCount
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DFVSGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.FullGame.edge_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.SourceInstance.edge_nonempty _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical

noncomputable section
open scoped Classical

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped BigOperators

namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {I J : Type*} [Fintype I] [Fintype J]

theorem expectation_uniform_eq_expect [Nonempty I] (f : I → ℝ) :
    (uniform I).expectation f = 𝔼 i, f i := by
  rw [expectation_uniform, Fintype.expect_eq_sum_div_card]

theorem table_uniform {Q A : Type*} [Fintype Q] [Fintype A]
    [DecidableEq Q] [Nonempty A] :
    table (fun _ : Q => uniform A) = uniform (Q → A) := by
  apply eq_of_weight_eq
  intro x
  simp [table, uniform, Nat.cast_pow, one_div]

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Probability
open DirectedFeedback.SourceProbability FiniteDistribution

theorem andCoin_true (k : ℕ) : (andCoin k).weight true = (2 : ℝ)⁻¹ ^ k := by
  have heq (x : Fin k → Bool) : andBit x = true ↔ x = fun _ => true := by
    simp [andBit, funext_iff]
  simp [andCoin, pushforward, heq, uniform, Nat.cast_pow, inv_pow]

theorem andCoin_false (k : ℕ) : (andCoin k).weight false = 1 - (2 : ℝ)⁻¹ ^ k := by
  have h := (andCoin k).normalized
  rw [Fintype.sum_bool, andCoin_true] at h
  linarith

theorem blockAnd_expectation {I : Type*} [Fintype I] [DecidableEq I] (k : ℕ)
    (f : (I → Bool) → ℝ) :
    (𝔼 x : I → Fin k → Bool, f (blockAnd x)) = (dyadicLaw I k).expectation f := by
  rw [← expectation_uniform_eq_expect]
  rw [← table_uniform, ← expectation_pushforward]
  unfold blockAnd
  rw [table_pushforward]
  rfl

end DirectedFeedback.Probability

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Bias
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution
variable {Ω : Type*} [Fintype Ω]

theorem support_nonempty (μ : FiniteDistribution Ω) : Nonempty μ.Support := by
  by_contra h
  have hz : ∀ x, μ.weight x = 0 := by
    intro x
    exact le_antisymm (not_lt.mp (fun hx => h ⟨⟨x,hx⟩⟩)) (μ.nonnegative x)
  have := μ.normalized
  simp [hz] at this

end DirectedFeedback.SourceProbability.FiniteDistribution

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_FailureEvent
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DFVSGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
namespace DirectedFeedback.JuntaSupport

open scoped BigOperators
open Finset

theorem walsh_symm {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x = walsh x s := by
  simp [walsh, Bool.and_comm]

theorem coordinate_orthogonality (s t : Bool) :
    (∑ x : Bool, bitSign (s && x) * bitSign (t && x)) =
      if s = t then 2 else 0 := by
  cases s <;> cases t <;> norm_num [bitSign, Fintype.sum_bool]

theorem walsh_sum_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (∑ x, walsh s x * walsh t x) =
      if s = t then (Fintype.card (Cube I) : ℝ) else 0 := by
  classical
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    bitSign (s i && b) * bitSign (t i && b))]
  simp only [coordinate_orthogonality]
  by_cases h : s = t
  · subst t
    simp []
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

theorem walsh_orthogonality {I : Type*} [Fintype I] [DecidableEq I]
    (s t : Cube I) :
    (𝔼 x, walsh s x * walsh t x) = if s = t then 1 else 0 := by
  classical
  rw [Fintype.expect_eq_sum_div_card, walsh_sum_orthogonality]
  split_ifs <;> simp

theorem walsh_inversion {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) (x : Cube I) :
    (∑ s, coefficient f s * walsh s x) = f x := by
  classical
  unfold coefficient
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have h (y : Cube I) :
      (∑ s, (f y * walsh s y) * walsh s x) =
        f y * (if y = x then (Fintype.card (Cube I) : ℝ) else 0) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    simp_rw [walsh_symm (x := y), walsh_symm (x := x)]
    exact walsh_sum_orthogonality y x
  simp_rw [h]
  rw [Fintype.expect_eq_sum_div_card]
  simp

theorem walsh_inner {I : Type*} [Fintype I] [DecidableEq I] (f g : Cube I → ℝ) :
    (∑ s, coefficient f s * coefficient g s) = 𝔼 x, f x * g x := by
  classical
  unfold coefficient
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  have h : (∑ s, (𝔼 y, f y * walsh s y) * (g x * walsh s x)) =
      g x * (∑ s, coefficient f s * walsh s x) := by
    simp only [Finset.mul_sum, coefficient]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h, walsh_inversion]
  ring

theorem walsh_parseval {I : Type*} [Fintype I] [DecidableEq I] (f : Cube I → ℝ) :
    (∑ s, coefficient f s ^ 2) = 𝔼 x, f x ^ 2 := by
  simpa [pow_two] using walsh_inner f f

end DirectedFeedback.JuntaSupport

namespace DFVSMaxCut.BooleanFourthMoment
open scoped BigOperators
open Finset DirectedFeedback.JuntaSupport

 theorem sum_cube_succ {n : ℕ} (F : Cube (Fin (n + 1)) → ℝ) :
    ∑ x, F x = ∑ b : Bool, ∑ y : Cube (Fin n), F (Fin.cons b y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
  exact Fintype.sum_prod_type _

 theorem expect_cube_succ {n : ℕ} (F : Cube (Fin (n + 1)) → ℝ) :
    (𝔼 x, F x) = 𝔼 b : Bool, 𝔼 y : Cube (Fin n), F (Fin.cons b y) := by
  calc
    _ = 𝔼 p : Bool × Cube (Fin n), F (Fin.cons p.1 p.2) :=
      (Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) _ F (fun _ => rfl)).symm
    _ = _ := by rw [← Finset.univ_product_univ, Finset.expect_product]

 theorem expect_bool (F : Bool → ℝ) : (𝔼 b, F b) = (F false + F true) / 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp [add_comm]

 theorem energy_nonneg {I : Type*} [Fintype I] [DecidableEq I] (c : Cube I → ℝ) :
    0 ≤ energy c := by
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg _ (sq_nonneg _)
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> norm_num

 theorem walsh_cons {n : ℕ} (s x : Cube (Fin n)) (a b : Bool) :
    walsh (Fin.cons a s) (Fin.cons b x) = (if a then bitSign b else 1) * walsh s x := by
  cases a <;> simp [walsh, Fin.prod_univ_succ, bitSign]

 theorem polynomial_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) (x : Cube (Fin n)) (b : Bool) :
    polynomial c (Fin.cons b x) = polynomial (fun s => c (Fin.cons false s)) x +
      bitSign b * polynomial (fun s => c (Fin.cons true s)) x := by
  unfold polynomial
  rw [sum_cube_succ, Fintype.sum_bool]
  simp only [walsh_cons, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

 theorem energy_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) :
    energy c = energy (fun s => c (Fin.cons false s)) +
      3 * energy (fun s => c (Fin.cons true s)) := by
  unfold energy
  rw [sum_cube_succ, Fintype.sum_bool]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte,
    one_mul, mul_assoc]
  rw [← Finset.mul_sum]
  ring

 theorem fourth_moment_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) :
    (𝔼 x, polynomial c x ^ 4) =
      (𝔼 x, polynomial (fun s => c (Fin.cons false s)) x ^ 4) +
      6 * (𝔼 x, polynomial (fun s => c (Fin.cons false s)) x ^ 2 *
        polynomial (fun s => c (Fin.cons true s)) x ^ 2) +
      (𝔼 x, polynomial (fun s => c (Fin.cons true s)) x ^ 4) := by
  rw [expect_cube_succ, Finset.expect_comm]
  simp_rw [expect_bool]
  simp only [polynomial_cons, bitSign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
  simp_rw [show ∀ a b : ℝ, ((a + b) ^ 4 + (a + -b) ^ 4) / 2 = a ^ 4 + 6 * (a ^ 2 * b ^ 2) + b ^ 4 by
    intro a b; ring]
  rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect]

 theorem fourth_moment_bound (n : ℕ) (c : Cube (Fin n) → ℝ) :
    (𝔼 x, polynomial c x ^ 4) ≤ energy c ^ 2 := by
  induction n with
  | zero => simp [polynomial, energy, walsh]; exact le_of_eq (by ring)
  | succ n ih =>
    let c₀ : Cube (Fin n) → ℝ := fun s => c (Fin.cons false s)
    let c₁ : Cube (Fin n) → ℝ := fun s => c (Fin.cons true s)
    have h₀ := ih c₀
    have h₁ := ih c₁
    have he₀ := energy_nonneg c₀
    have he₁ := energy_nonneg c₁
    have hm₀ : 0 ≤ 𝔼 x, polynomial c₀ x ^ 4 := by positivity
    have hm₁ : 0 ≤ 𝔼 x, polynomial c₁ x ^ 4 := by positivity
    have hc := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
      (fun x => polynomial c₀ x ^ 2) (fun x => polynomial c₁ x ^ 2)
    simp only [← pow_mul, Nat.reduceMul] at hc
    have hc' : (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) ^ 2 ≤
        (energy c₀ * energy c₁) ^ 2 := by
      calc _ ≤ _ := hc
           _ ≤ energy c₀ ^ 2 * energy c₁ ^ 2 := mul_le_mul h₀ h₁ hm₁ (sq_nonneg _)
           _ = _ := by ring
    have hc'' : (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) ≤ energy c₀ * energy c₁ :=
      (sq_le_sq₀ (by positivity) (mul_nonneg he₀ he₁)).mp hc'
    rw [fourth_moment_cons, energy_cons]
    change (𝔼 x, polynomial c₀ x ^ 4) +
      6 * (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) +
      (𝔼 x, polynomial c₁ x ^ 4) ≤ (energy c₀ + 3 * energy c₁) ^ 2
    nlinarith [sq_nonneg (energy c₁)]

 theorem weight_eq_degree {I : Type*} [Fintype I] [DecidableEq I] (s : Cube I) :
    (∏ i, if s i then (3 : ℝ) else 1) = 3 ^ Analytic.degree s := by
  simp [Finset.prod_ite, Analytic.degree]

 theorem energy_truncated {I : Type*} [Fintype I] [DecidableEq I]
    (K : ℕ) (c : Cube I → ℝ) (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    energy c ≤ 3 ^ K * ∑ s, c s ^ 2 := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [weight_eq_degree]
  by_cases hs : Analytic.degree s ≤ K
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hs) (sq_nonneg _)
  · rw [hc s (lt_of_not_ge hs)]; simp

 theorem coefficient_polynomial {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (a : Cube I) : coefficient (polynomial c) a = c a := by
  unfold coefficient polynomial
  simp only [Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_expect, walsh_orthogonality]
  simp

 theorem polynomial_second_moment {I : Type*} [Fintype I] [DecidableEq I] (c : Cube I → ℝ) :
    (𝔼 x, polynomial c x ^ 2) = ∑ s, c s ^ 2 := by
  rw [← walsh_parseval]
  simp only [coefficient_polynomial]

 theorem degree_fourth_moment_bound {n K : ℕ} (c : Cube (Fin n) → ℝ)
    (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    (𝔼 x, polynomial c x ^ 4) ≤ (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 := by
  rw [polynomial_second_moment]
  exact (fourth_moment_bound n c).trans
    ((sq_le_sq₀ (energy_nonneg c) (by positivity)).mpr (energy_truncated K c hc))

 theorem walsh_flip {I : Type*} [Fintype I] [DecidableEq I]
    (s x : Cube I) (i : I) :
    walsh s (Function.update x i (!x i)) = (if s i then -1 else 1) * walsh s x := by
  classical
  have hp (j : I) : bitSign (s j && Function.update x i (!x i) j) =
      (if j = i then (if s i then (-1 : ℝ) else 1) else 1) * bitSign (s j && x j) := by
    by_cases h : j = i
    · subst j; cases s i <;> cases x i <;> simp [bitSign]
    · simp [h]
  simp only [walsh, hp, Finset.prod_mul_distrib]
  simp

 theorem polynomial_diff {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (i : I) :
    discreteDiff (polynomial c) i = polynomial (fun s => if s i then c s else 0) := by
  funext x
  simp only [discreteDiff, polynomial, walsh_flip, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  cases s i <;> simp

 theorem total_diff_second {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) :
    (∑ i, 𝔼 x, discreteDiff (polynomial c) i x ^ 2) =
      ∑ s, (Analytic.degree s : ℝ) * c s ^ 2 := by
  simp only [polynomial_diff, polynomial_second_moment]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [ite_pow, zero_pow (by omega : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp [Analytic.degree]

end DFVSMaxCut.BooleanFourthMoment

namespace DirectedFeedback.Junta
open scoped BigOperators
open Finset DirectedFeedback.JuntaSupport DFVSMaxCut.BooleanFourthMoment
open DFVSMaxCut.Analytic

theorem polynomial_coefficients {n : ℕ} (f : Cube (Fin n) → ℝ) :
    polynomial (coefficient f) = f := by
  funext x
  exact walsh_inversion f x

theorem influence_nonneg {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n) :
    0 ≤ influence f i := by unfold influence; positivity

theorem influence_eq_diff {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n) :
    influence f i = 4 * (𝔼 x, discreteDiff f i x ^ 2) := by
  rw [Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro x _
  unfold discreteDiff
  ring

theorem totalInfluence_spectral {n : ℕ} (f : Cube (Fin n) → ℝ) :
    totalInfluence f = 4 * ∑ s, (degree s : ℝ) * coefficient f s ^ 2 := by
  unfold totalInfluence
  simp_rw [influence_eq_diff]
  rw [← Finset.mul_sum]
  conv_lhs => rw [← polynomial_coefficients f]
  rw [total_diff_second]

theorem spectral_tail {n : ℕ} (f : Cube (Fin n) → ℝ) (K : ℕ) :
    4 * (K + 1 : ℝ) *
      (∑ s ∈ Finset.univ.filter (fun s => K < degree s), coefficient f s ^ 2) ≤
      totalInfluence f := by
  rw [totalInfluence_spectral, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ s ∈ Finset.univ.filter (fun s => K < degree s),
          (degree s : ℝ) * coefficient f s ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_filter.mp hs).2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

theorem pivotal_sq {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n)
    (x : Cube (Fin n)) : pivotal f i x ^ 2 = pivotal f i x := by
  unfold pivotal
  split_ifs <;> norm_num

theorem diff_mul_pivotal {n : ℕ} (f : Cube (Fin n) → ℝ) (i : Fin n)
    (x : Cube (Fin n)) : discreteDiff f i x * pivotal f i x = discreteDiff f i x := by
  unfold pivotal discreteDiff
  split_ifs with h
  · simp [h]
  · ring

theorem pivotal_eq_difference_sq {n : ℕ} (f : Cube (Fin n) → ℝ) (hf : IsBoolean f)
    (i : Fin n) (x : Cube (Fin n)) :
    pivotal f i x = (f x - f (Function.update x i (!x i))) ^ 2 := by
  unfold pivotal
  rcases hf x with h | h <;>
    rcases hf (Function.update x i (!x i)) with h' | h' <;> simp [h, h']

theorem expect_pivotal {n : ℕ} (f : Cube (Fin n) → ℝ) (hf : IsBoolean f) (i : Fin n) :
    (𝔼 x, pivotal f i x) = influence f i := by
  unfold influence
  simp only [pivotal_eq_difference_sq f hf]

theorem coefficient_discreteDiff {n : ℕ} (f : Cube (Fin n) → ℝ)
    (i : Fin n) (s : Cube (Fin n)) :
    coefficient (discreteDiff f i) s = if s i then coefficient f s else 0 := by
  conv_lhs => rw [← polynomial_coefficients f]
  rw [polynomial_diff, coefficient_polynomial]

theorem inner_lowDiff {n : ℕ} (f : Cube (Fin n) → ℝ) (K : ℕ) (i : Fin n) :
    (𝔼 x, discreteDiff f i x * lowDiff f K i x) =
      (𝔼 x, lowDiff f K i x ^ 2) := by
  rw [← walsh_inner]
  simp only [lowDiff, coefficient_polynomial, coefficient_discreteDiff,
    polynomial_second_moment]
  apply Finset.sum_congr rfl
  intro s _
  unfold lowDiffCoeff
  by_cases hs : s i = true <;> by_cases hk : degree s ≤ K <;> simp [hs, hk, pow_two]

theorem lowDiff_fourth {n : ℕ} (f : Cube (Fin n) → ℝ) (K : ℕ) (i : Fin n) :
    (𝔼 x, lowDiff f K i x ^ 4) ≤
      (3 ^ K * (𝔼 x, lowDiff f K i x ^ 2)) ^ 2 := by
  apply degree_fourth_moment_bound
  intro s hs
  simp [lowDiffCoeff, not_le.mpr hs]

theorem lowDiff_energy_le {n : ℕ} (f : Cube (Fin n) → ℝ) (hf : IsBoolean f)
    (K : ℕ) (i : Fin n) (τ : ℝ) (hτ : 0 ≤ τ) (hsmall : influence f i ≤ τ ^ 2) :
    (𝔼 x, lowDiff f K i x ^ 2) ≤ 3 ^ K * τ * influence f i / 4 := by
  let s := (𝔼 x, lowDiff f K i x ^ 2)
  let X := (𝔼 x, pivotal f i x * lowDiff f K i x ^ 2)
  let I := influence f i
  let a : ℝ := 3 ^ K
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hI0 : 0 ≤ I := influence_nonneg f i
  have hX : 0 ≤ X := by
    apply Finset.expect_nonneg
    intro x _
    apply mul_nonneg _ (sq_nonneg _)
    unfold pivotal
    split_ifs <;> norm_num
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hc₁ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (discreteDiff f i) (fun x => pivotal f i x * lowDiff f K i x)
  have hinner : (𝔼 x, discreteDiff f i x *
      (pivotal f i x * lowDiff f K i x)) = s := by
    simp only [← mul_assoc, diff_mul_pivotal, inner_lowDiff]
    rfl
  have hprod : (𝔼 x, (pivotal f i x * lowDiff f K i x) ^ 2) = X := by
    simp only [mul_pow, pivotal_sq]
    rfl
  rw [hinner, hprod] at hc₁
  have hIdiff : (𝔼 x, discreteDiff f i x ^ 2) = I / 4 := by
    have hh := influence_eq_diff f i
    dsimp [I]
    linarith
  rw [hIdiff] at hc₁
  have hc₂ := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (pivotal f i) (fun x => lowDiff f K i x ^ 2)
  simp only [pivotal_sq, expect_pivotal f hf, ← pow_mul, Nat.reduceMul] at hc₂
  have hc₂' : X ^ 2 ≤ I * (a * s) ^ 2 := by
    exact hc₂.trans (mul_le_mul_of_nonneg_left (lowDiff_fourth f K i) hI0)
  by_cases hs : s = 0
  · change s ≤ a * τ * I / 4
    rw [hs]
    positivity
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
  have hsq : s ^ 4 ≤ (I / 4) ^ 2 * (I * (a * s) ^ 2) := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ ≤ (I / 4 * X) ^ 2 :=
        (sq_le_sq₀ (sq_nonneg _) (by positivity)).mpr hc₁
      _ = (I / 4) ^ 2 * X ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc₂' (sq_nonneg _)
  have hcancel : s ^ 2 ≤ a ^ 2 * I ^ 3 / 16 := by
    apply (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hspos)).mp
    nlinarith only [hsq]
  have hsmall' : a ^ 2 * I ^ 3 / 16 ≤ (a * τ * I / 4) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ a ^ 2 * I ^ 2 / 16)
    dsimp [I] at *
    nlinarith only [hh]
  exact (sq_le_sq₀ hs0 (by positivity)).mp (hcancel.trans hsmall')

theorem walsh_eq_on_support {n : ℕ} (s x y : Cube (Fin n))
    (hxy : ∀ i ∈ support s, x i = y i) : walsh s x = walsh s y := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : s i = true
  · rw [hxy i (by simp [support, hi])]
  · simp [Bool.eq_false_of_not_eq_true hi]

theorem project_onCoordinates {n : ℕ} (J : Finset (Fin n)) (f : Cube (Fin n) → ℝ) :
    OnCoordinates J (project J f) := by
  intro x y hxy
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : support s ⊆ J
  · rw [walsh_eq_on_support s x y (fun i hi => hxy i (hs hi))]
  · simp [projectCoeff, hs]

theorem coefficient_sub {n : ℕ} (f g : Cube (Fin n) → ℝ) (s : Cube (Fin n)) :
    coefficient (fun x => f x - g x) s = coefficient f s - coefficient g s := by
  unfold coefficient
  simp only [sub_mul, Finset.expect_sub_distrib]

theorem project_squared_error {n : ℕ} (J : Finset (Fin n)) (f : Cube (Fin n) → ℝ) :
    (𝔼 x, (f x - project J f x) ^ 2) =
      ∑ s, if support s ⊆ J then 0 else coefficient f s ^ 2 := by
  rw [← walsh_parseval]
  simp only [coefficient_sub, project, coefficient_polynomial]
  apply Finset.sum_congr rfl
  intro s _
  unfold projectCoeff
  split_ifs <;> simp

theorem project_squared_error_le {n : ℕ} (J : Finset (Fin n))
    (f : Cube (Fin n) → ℝ) (K : ℕ) :
    (𝔼 x, (f x - project J f x) ^ 2) ≤
      (∑ s ∈ Finset.univ.filter (fun s => K < degree s), coefficient f s ^ 2) +
      ∑ i ∈ Finset.univ \ J, (𝔼 x, lowDiff f K i x ^ 2) := by
  rw [project_squared_error]
  simp only [lowDiff, polynomial_second_moment]
  rw [Finset.sum_filter, Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : support s ⊆ J
  · rw [ite_eq_left hs]
    positivity
  · rw [ite_eq_right hs]
    by_cases hk : K < degree s
    · rw [ite_eq_left hk]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    · rw [ite_eq_right hk, zero_add]
      obtain ⟨i, hi, hiJ⟩ := Finset.not_subset.mp hs
      have his : s i = true := (Finset.mem_filter.mp hi).2
      have hiout : i ∈ Finset.univ \ J := by simp [hiJ]
      have hterm : lowDiffCoeff f K i s = coefficient f s := by
        simp [lowDiffCoeff, his, Nat.le_of_not_gt hk]
      rw [← hterm]
      exact Finset.single_le_sum (fun i _ => sq_nonneg (lowDiffCoeff f K i s)) hiout

theorem highInfluences_card_bound {n : ℕ} (f : Cube (Fin n) → ℝ) (τ : ℝ) :
    (highInfluences f τ).card * τ ^ 2 ≤ totalInfluence f := by
  calc
    _ = ∑ i ∈ highInfluences f τ, τ ^ 2 := by simp
    _ ≤ ∑ i ∈ highInfluences f τ, influence f i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
      influence_nonneg f i

theorem lowDiff_sum_outside {n : ℕ} (f : Cube (Fin n) → ℝ) (hf : IsBoolean f)
    (K : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ i ∈ Finset.univ \ highInfluences f τ, (𝔼 x, lowDiff f K i x ^ 2)) ≤
      3 ^ K * τ * totalInfluence f / 4 := by
  calc
    _ ≤ ∑ i ∈ Finset.univ \ highInfluences f τ, 3 ^ K * τ * influence f i / 4 := by
      apply Finset.sum_le_sum
      intro i hi
      apply lowDiff_energy_le f hf K i τ hτ
      have hnot := (Finset.mem_sdiff.mp hi).2
      simpa only [highInfluences, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hnot
    _ ≤ ∑ i, 3 ^ K * τ * influence f i / 4 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset.trans (Finset.subset_univ _))
        (fun i _ _ => by have := influence_nonneg f i; positivity)
    _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]; rfl

end DirectedFeedback.Junta
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_RoundBoolean
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DFVSGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.FullGame.edge_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.SourceInstance.edge_nonempty _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
namespace DirectedFeedback.Junta
open scoped BigOperators
open Finset DirectedFeedback.JuntaSupport DFVSMaxCut.BooleanFourthMoment
open DFVSMaxCut.Analytic

theorem roundBoolean_isBoolean {n : ℕ} (p : Cube (Fin n) → ℝ) :
    IsBoolean (roundBoolean p) := by
  intro x
  unfold roundBoolean
  split_ifs <;> simp

theorem roundBoolean_onCoordinates {n : ℕ} (J : Finset (Fin n))
    (p : Cube (Fin n) → ℝ) (hp : OnCoordinates J p) : OnCoordinates J (roundBoolean p) := by
  intro x y h
  unfold roundBoolean
  rw [hp x y h]

theorem rounding_error_le {n : ℕ} (f p : Cube (Fin n) → ℝ) (hf : IsBoolean f) :
    error f (roundBoolean p) ≤ 4 * (𝔼 x, (f x - p x) ^ 2) := by
  unfold error
  rw [Finset.mul_expect]
  apply Finset.expect_le_expect
  intro x _
  by_cases heq : f x = roundBoolean p x
  · rw [ite_eq_left heq]
    positivity
  · rw [ite_eq_right heq]
    rcases hf x with hf0 | hf1
    · have hp : (1 : ℝ) / 2 ≤ p x := by
        by_contra h
        exact heq (by rw [hf0]; unfold roundBoolean; rw [ite_eq_right h])
      rw [hf0]
      nlinarith [sq_nonneg (p x - 1 / 2)]
    · have hp : p x < (1 : ℝ) / 2 := by
        by_contra h
        exact heq (by rw [hf1]; unfold roundBoolean; rw [ite_eq_left (le_of_not_gt h)])
      rw [hf1]
      nlinarith [sq_nonneg (p x - 1 / 2)]

theorem friedgut_uniform (b α : ℝ) (hb : 0 ≤ b) (hα : 0 < α) :
    ∃ Jmax : ℕ, ∀ (n : ℕ) (f : Cube (Fin n) → ℝ),
      IsBoolean f → totalInfluence f ≤ b →
      ∃ J : Finset (Fin n), J.card ≤ Jmax ∧
        ∃ g : Cube (Fin n) → ℝ, IsBoolean g ∧ OnCoordinates J g ∧ error f g ≤ α := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * b / α)
  have hKpos : (0 : ℝ) < K + 1 := by positivity
  have hKb : 2 * b ≤ (K + 1 : ℝ) * α := by
    have := (div_lt_iff₀ hα).mp hK
    nlinarith
  let τ : ℝ := α / (2 * 3 ^ K * (b + 1))
  have hb1 : 0 < b + 1 := by linarith
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτid : (3 : ℝ) ^ K * τ * (b + 1) = α / 2 := by
    dsimp [τ]
    field_simp
  have hτb : (3 : ℝ) ^ K * τ * b ≤ α / 2 := by
    rw [← hτid]
    exact mul_le_mul_of_nonneg_left (by linarith : b ≤ b + 1) (by positivity)
  refine ⟨Nat.ceil (b / τ ^ 2), ?_⟩
  intro n f hf hIf
  let J := highInfluences f τ
  have hcard : (J.card : ℝ) ≤ b / τ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
    exact (highInfluences_card_bound f τ).trans hIf
  refine ⟨J, ?_, roundBoolean (project J f), roundBoolean_isBoolean _,
    roundBoolean_onCoordinates J _ (project_onCoordinates J f), ?_⟩
  · exact_mod_cast hcard.trans (Nat.le_ceil _)
  · have htail := (spectral_tail f K).trans hIf
    have htail' : 8 *
        (∑ s ∈ Finset.univ.filter (fun s => K < degree s), coefficient f s ^ 2) ≤ α := by
      apply (mul_le_mul_iff_of_pos_left hKpos).mp
      nlinarith
    have hlow := lowDiff_sum_outside f hf K τ hτ.le
    have hlow' : 8 * (∑ i ∈ Finset.univ \ J, (𝔼 x, lowDiff f K i x ^ 2)) ≤ α := by
      have hh := mul_le_mul_of_nonneg_left hIf (by positivity : 0 ≤ (3 : ℝ) ^ K * τ)
      dsimp [J]
      nlinarith
    have hproject := project_squared_error_le J f K
    have hround := rounding_error_le f (project J f) hf
    linarith

theorem cubeEquiv_update {I J : Type*} [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (x : I → Bool) (i : I) (a : Bool) :
    cubeEquiv e (Function.update x i a) = Function.update (cubeEquiv e x) (e i) a := by
  funext j
  by_cases hj : j = e i
  · subst j; simp [cubeEquiv]
  · have hji : e.symm j ≠ i := by
      intro heq
      apply hj
      simpa using congrArg e heq
    simp [cubeEquiv, hj, hji]

theorem cubeInfluence_reindex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (f : (J → Bool) → ℝ) (i : I) :
    cubeInfluence (fun x => f (cubeEquiv e x)) i = cubeInfluence f (e i) := by
  apply Fintype.expect_equiv (cubeEquiv e)
  intro x
  simp only [cubeEquiv_update]
  simp [cubeEquiv]

theorem friedgut_finite (b α : ℝ) (hb : 0 ≤ b) (hα : 0 < α) :
    ∃ Jmax : ℕ, ∀ (I : Type) [Fintype I] [DecidableEq I]
      (f : (I → Bool) → ℝ),
      (∀ x, f x = 0 ∨ f x = 1) → (∑ i, cubeInfluence f i) ≤ b →
      ∃ J : Finset I, J.card ≤ Jmax ∧
        ∃ g : (I → Bool) → ℝ, (∀ x, g x = 0 ∨ g x = 1) ∧
          DependsOn J g ∧ cubeError f g ≤ α := by
  obtain ⟨Jmax, hJmax⟩ := friedgut_uniform b α hb hα
  refine ⟨Jmax, ?_⟩
  intro I _ _ f hf hIf
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f' : Cube (Fin (Fintype.card I)) → ℝ := fun x => f (cubeEquiv e x)
  have htrans : totalInfluence f' = ∑ i, cubeInfluence f i := by
    unfold totalInfluence
    change (∑ i, cubeInfluence (fun x => f (cubeEquiv e x)) i) = _
    simp_rw [cubeInfluence_reindex]
    exact e.sum_comp (cubeInfluence f)
  obtain ⟨J, hcard, g, hg, hdep, herr⟩ :=
    hJmax (Fintype.card I) f' (fun x => hf _) (htrans ▸ hIf)
  refine ⟨J.map e.toEmbedding, by simpa using hcard,
    (fun x => g (cubeEquiv e.symm x)), (fun x => hg _), ?_, ?_⟩
  · intro x y h
    apply hdep
    intro i hi
    exact h (e i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
  · have heq : cubeError f (fun x => g (cubeEquiv e.symm x)) = error f' g := by
      unfold cubeError error
      apply Fintype.expect_equiv (cubeEquiv e.symm)
      intro x
      have hx : cubeEquiv e (cubeEquiv e.symm x) = x := by funext i; simp [cubeEquiv]
      change (if f x = g (cubeEquiv e.symm x) then (0 : ℝ) else 1) =
        (if f (cubeEquiv e (cubeEquiv e.symm x)) = g (cubeEquiv e.symm x) then 0 else 1)
      rw [hx]
    exact heq ▸ herr

end DirectedFeedback.Junta

namespace DirectedFeedback.Junta
open DirectedFeedback.SourceProbability FiniteDistribution
open DirectedFeedback.Probability

variable {I : Type} [Fintype I] [DecidableEq I]

theorem expect_merge (J : Finset I) (h : (I → Bool) → ℝ) :
    (𝔼 x, 𝔼 y, h (merge J x y)) = 𝔼 x, h x := by
  calc
    _ = 𝔼 p : (I → Bool) × (I → Bool), h (merge J p.1 p.2) := by
      rw [← Finset.expect_product']; simp
    _ = 𝔼 p : (I → Bool) × (I → Bool), h p.1 := by
      exact (Fintype.expect_equiv (swapOutside J) (fun p => h p.1)
        (fun p => h (merge J p.1 p.2)) (by
          intro p
          congr 1
          funext i
          by_cases hi : i ∈ J <;> simp [swapOutside, merge, hi])).symm
    _ = _ := by rw [← Finset.univ_product_univ, Finset.expect_product]; simp

theorem disagree_triangle (a b c : ℝ) : disagree a c ≤ disagree a b + disagree b c := by
  by_cases hab : a = b
  · subst b; simp [disagree]
  by_cases hbc : b = c
  · subst c; simp [disagree]
  simp only [disagree, ite_eq_right hab, ite_eq_right hbc]
  split_ifs <;> norm_num

theorem restriction_approximation (J : Finset I) (f h : (I → Bool) → ℝ)
    (hh : DependsOn J h) :
    ∃ y, cubeError f (fun x => f (merge J x y)) ≤ 2 * cubeError f h := by
  have hdep (x y : I → Bool) : h x = h (merge J x y) := by
    apply hh
    intro i hi
    simp [merge, hi]
  have hbound : (𝔼 y, cubeError f (fun x => f (merge J x y))) ≤ 2 * cubeError f h := by
    unfold cubeError
    change (𝔼 y, 𝔼 x, disagree (f x) (f (merge J x y))) ≤ _
    calc
      _ ≤ 𝔼 y, 𝔼 x, (disagree (f x) (h x) + disagree (f (merge J x y)) (h (merge J x y))) := by
        apply Finset.expect_le_expect
        intro y _
        apply Finset.expect_le_expect
        intro x _
        have ht := disagree_triangle (f x) (h x) (f (merge J x y))
        simpa [hdep x y, disagree, eq_comm] using ht
      _ = (𝔼 x, disagree (f x) (h x)) + (𝔼 y, 𝔼 x,
          disagree (f (merge J x y)) (h (merge J x y))) := by
        simp_rw [Finset.expect_add_distrib]
        simp
      _ = _ := by
        rw [Finset.expect_comm]
        rw [expect_merge J (fun z => disagree (f z) (h z))]
        change cubeError f h + cubeError f h = 2 * cubeError f h
        ring
  obtain ⟨y, _, hy⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty hbound
  exact ⟨y, hy⟩

end DirectedFeedback.Junta

namespace DirectedFeedback.Junta
open DirectedFeedback.SourceProbability FiniteDistribution
open DirectedFeedback.Probability
variable {I : Type} [Fintype I] [DecidableEq I]

theorem flatAnd_expectation (k : ℕ) (f : (I → Bool) → ℝ) :
    (𝔼 x : I × Fin k → Bool, f (flatAnd x)) = (dyadicLaw I k).expectation f := by
  rw [← blockAnd_expectation]
  apply Fintype.expect_equiv (Equiv.curry I (Fin k) Bool)
  intro x
  rfl

omit [Fintype I] in
theorem flatAnd_update_other {k : ℕ} (x : I × Fin k → Bool) (q : I × Fin k)
    (i : I) (hi : i ≠ q.1) :
    flatAnd (Function.update x q (!x q)) i = flatAnd x i := by
  unfold flatAnd
  congr 1
  funext a
  have hia : (i, a) ≠ q := fun h => hi (congrArg Prod.fst h)
  simp [hia]

omit [Fintype I] in
theorem flatAnd_update_cases {k : ℕ} (x : I × Fin k → Bool) (q : I × Fin k) :
    flatAnd (Function.update x q (!x q)) = flatAnd x ∨
    flatAnd (Function.update x q (!x q)) =
      Function.update (flatAnd x) q.1 (!(flatAnd x q.1)) := by
  by_cases h : flatAnd (Function.update x q (!x q)) q.1 = flatAnd x q.1
  · left
    funext i
    by_cases hi : i = q.1
    · simpa [hi] using h
    · exact flatAnd_update_other x q i hi
  · right
    funext i
    by_cases hi : i = q.1
    · subst i
      simp only [Function.update_self]
      cases ha : flatAnd (Function.update x q (!x q)) q.1 <;>
        cases hb : flatAnd x q.1 <;> simp_all
    · rw [Function.update_of_ne hi]
      exact flatAnd_update_other x q i hi

theorem flatAnd_influence_le (k : ℕ) (f : (I → Bool) → ℝ) (q : I × Fin k) :
    cubeInfluence (fun x => f (flatAnd x)) q ≤ biasedInfluence k f q.1 := by
  unfold cubeInfluence biasedInfluence
  rw [← flatAnd_expectation k]
  apply Finset.expect_le_expect
  intro x _
  dsimp only
  obtain h | h := flatAnd_update_cases x q
  · simp only [h, sub_self, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  · rw [h]

theorem flatAnd_totalInfluence_le (k : ℕ) (f : (I → Bool) → ℝ) :
    (∑ q : I × Fin k, cubeInfluence (fun x => f (flatAnd x)) q) ≤
      k * ∑ i, biasedInfluence k f i := by
  calc
    _ ≤ ∑ q : I × Fin k, biasedInfluence k f q.1 :=
      Finset.sum_le_sum (fun q _ => flatAnd_influence_le k f q)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [← Finset.mul_sum]

theorem friedgut_dyadic (k : ℕ) (b α : ℝ) (hb : 0 ≤ b) (hα : 0 < α) :
    ∃ Jmax : ℕ, ∀ (I : Type) [Fintype I] [DecidableEq I] (f : (I → Bool) → ℝ),
      (∀ x, f x = 0 ∨ f x = 1) → (∑ i, biasedInfluence k f i) ≤ b →
      ∃ J : Finset I, J.card ≤ Jmax ∧ ∃ g : (I → Bool) → ℝ,
        (∀ x, g x = 0 ∨ g x = 1) ∧ DependsOn J g ∧
          (dyadicLaw I k).expectation (fun x => disagree (f x) (g x)) ≤ α := by
  obtain ⟨Jmax, hJmax⟩ := friedgut_finite (k * b) (α / 2) (mul_nonneg (Nat.cast_nonneg _) hb)
    (by positivity)
  refine ⟨Jmax, ?_⟩
  intro I _ _ f hf hIf
  let F : (I × Fin k → Bool) → ℝ := fun x => f (flatAnd x)
  have hIF : (∑ q, cubeInfluence F q) ≤ k * b :=
    (flatAnd_totalInfluence_le k f).trans (mul_le_mul_of_nonneg_left hIf (Nat.cast_nonneg _))
  obtain ⟨L, hL, H, _, hH, herror⟩ := hJmax (I × Fin k) F (fun x => hf _) hIF
  let J : Finset I := L.image Prod.fst
  let K : Finset (I × Fin k) := Finset.univ.filter (fun q => q.1 ∈ J)
  have hHK : DependsOn K H := by
    intro x y hxy
    apply hH
    intro q hq
    apply hxy
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  obtain ⟨y, hy⟩ := restriction_approximation K F H hHK
  let g : (I → Bool) → ℝ := fun z => f (merge J z (flatAnd y))
  have hmerge (x : I × Fin k → Bool) :
      flatAnd (merge K x y) = merge J (flatAnd x) (flatAnd y) := by
    funext i
    by_cases hi : i ∈ J <;> simp [flatAnd, merge, K, hi]
  refine ⟨J, (Finset.card_image_le).trans hL, g, (fun x => hf _), ?_, ?_⟩
  · intro x z hxz
    apply congrArg f
    funext i
    by_cases hi : i ∈ J
    · simp [merge, hi, hxz i hi]
    · simp [merge, hi]
  · have heq : cubeError F (fun x => F (merge K x y)) =
        (dyadicLaw I k).expectation (fun z => disagree (f z) (g z)) := by
      unfold cubeError
      change (𝔼 x, disagree (F x) (F (merge K x y))) = _
      simp only [F, hmerge]
      exact flatAnd_expectation k (fun z => disagree (f z) (g z))
    rw [heq] at hy
    linarith

end DirectedFeedback.Junta

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution
open DirectedFeedback.Probability
variable {I : Type} [Fintype I] [DecidableEq I]

theorem bitValue_boolean (b : Bool) : bitValue b = 0 ∨ bitValue b = 1 := by
  cases b <;> simp [bitValue]

theorem dyadic_coin (k : ℕ) :
    andCoin k = coin ((2 : ℝ)⁻¹ ^ k) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) := by
  apply eq_of_weight_eq
  intro b
  cases b
  · exact andCoin_false k
  · exact andCoin_true k

theorem dyadic_law (k : ℕ) :
    dyadicLaw I k = law ((2 : ℝ)⁻¹ ^ k) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num)) := by
  simp only [dyadicLaw, law, dyadic_coin]

omit [Fintype I] in
theorem update_insertBit (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool) :
    Function.update (insertBit j b x) j (!b) = insertBit j (!b) x := by
  funext i
  by_cases hi : i = j
  · subst i; simp
  · simp [insertBit, hi]

theorem prod_insertBit (p : ℝ) (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool) :
    (∏ i, atom p (insertBit j b x i)) = atom p b * ∏ i : {i : I // i ≠ j}, atom p (x i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  rw [insertBit_self, prod_except]
  simp only [insertBit_other]

omit [Fintype I] in
theorem flip_square (f : (I → Bool) → Bool) (hf : Monotone f)
    (j : I) (b : Bool) (x : {i : I // i ≠ j} → Bool) :
    (bitValue (f (insertBit j b x)) -
      bitValue (f (Function.update (insertBit j b x) j (!(insertBit j b x j)))))^2 =
      discreteDerivative f j x := by
  rw [insertBit_self, update_insertBit, discreteDerivative_eq_indicator f hf]
  have hm : f (insertBit j false x) ≤ f (insertBit j true x) := by
    apply hf
    intro i
    by_cases hi : i = j
    · subst i; simp
    · simp [insertBit, hi]
  cases b <;> cases h0 : f (insertBit j false x) <;> cases h1 : f (insertBit j true x) <;>
    simp_all [bitValue, pivotalEvent, Bool.le_iff_imp]

theorem biasedInfluence_eq (k : ℕ) (f : (I → Bool) → Bool) (hf : Monotone f) (j : I) :
    Junta.biasedInfluence k (fun x => bitValue (f x)) j =
      ∑ x : {i : I // i ≠ j} → Bool,
        (∏ i, atom ((2 : ℝ)⁻¹^k) (x i)) * discreteDerivative f j x := by
  unfold Junta.biasedInfluence
  rw [dyadic_law]
  change (∑ x, (∏ i, atom ((2 : ℝ)⁻¹^k) (x i)) *
    (bitValue (f x) - bitValue (f (Function.update x j (!(x j)))))^2) = _
  rw [sum_split j]
  apply Finset.sum_congr rfl
  intro x _
  rw [prod_insertBit, prod_insertBit, flip_square f hf, flip_square f hf]
  simp only [atom, Bool.false_eq_true, ↓reduceIte]
  ring

theorem dyadic_influences_le_budget (k : ℕ) (f : (I → Bool) → Bool) (hf : Monotone f) :
    (∑ j, Junta.biasedInfluence k (fun x => bitValue (f x)) j) ≤ budget f := by
  simp_rw [biasedInfluence_eq k f hf]
  exact influence_le_budget f hf _ (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

theorem boolean_dyadic_junta (k : ℕ) (B γ : ℝ) (hB : 0 ≤ B) (hγ : 0 < γ) :
    ∃ Jmax : ℕ, ∀ (I : Type) [Fintype I] [DecidableEq I] (f : (I → Bool) → Bool),
      Monotone f → budget f ≤ B →
      ∃ J : Finset I, J.card ≤ Jmax ∧ ∃ g : (I → Bool) → Bool,
        (∀ x y, (∀ i ∈ J, x i = y i) → g x = g y) ∧
          (law ((2 : ℝ)⁻¹^k) (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))).probability
            (fun x => decide (f x ≠ g x)) ≤ γ := by
  obtain ⟨Jmax, hJmax⟩ := Junta.friedgut_dyadic k B γ hB hγ
  refine ⟨Jmax, ?_⟩
  intro I _ _ f hf hbf
  obtain ⟨J,hJ,g,hg,hdep,herr⟩ := hJmax I (fun x => bitValue (f x))
    (fun x => bitValue_boolean (f x)) ((dyadic_influences_le_budget k f hf).trans hbf)
  let g' : (I → Bool) → Bool := fun x => decide (g x = 1)
  refine ⟨J,hJ,g',?_,?_⟩
  · intro x y hxy
    simp only [g', hdep x y hxy]
  · rw [probability_eq_expectation, ← dyadic_law]
    convert herr using 1
    all_goals try with_reducible_and_instances rfl
    apply expectation_congr
    intro x
    obtain hx | hx := hg x <;> cases hfx : f x <;>
      simp [g', Junta.disagree, bitValue, hx]

end DirectedFeedback.Pivotal

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Pivotal
open DirectedFeedback.SourceProbability FiniteDistribution

theorem uniform_dyadic_junta (M : ℕ) (B γ : ℝ) (hB : 0 ≤ B) (hγ : 0 < γ) :
    ∃ Jmax : ℕ, 1 ≤ Jmax ∧ DyadicJuntaBound M B γ Jmax := by
  have h := fun k : Fin (M+2) => boolean_dyadic_junta k.val B γ hB hγ
  choose J hJ using h
  refine ⟨1 + ∑ k, J k, by omega, ?_⟩
  intro k I _ _ f hf hb
  obtain ⟨S,hS,g,hg,herr⟩ := hJ k I f hf hb
  refine ⟨S, ?_,g,hg,herr⟩
  have hh : J k ≤ ∑ j : Fin (M+2), J j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  omega

end DirectedFeedback.Pivotal

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_PrefixBit
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.DFVSGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.DFVSGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.FullGame.edge_nonempty _root_.OAI.DirectedFeedback.FullGame.vertex_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty _root_.OAI.DirectedFeedback.SourceInstance.edge_nonempty _root_.OAI.DirectedFeedback.SourceInstance.label_nonempty _root_.OAI.DirectedFeedback.StackDSL.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

theorem end_homogeneous {C : Type*} [Fintype C] [Nonempty C] (r : ℕ)
    (R : ℕ → ℕ) (hR : ∀ k, ∀ (s : Finset ℕ), R k ≤ s.card →
      ∀ color : Finset ℕ → C, ∃ h ⊆ s, h.card = k ∧ Homogeneous r color h) :
    ∀ k, ∃ N, ∀ (s : Finset ℕ), N ≤ s.card → ∀ color : Finset ℕ → C,
      ∃ h ⊆ s, h.card = k ∧ ∃ tag : ℕ → C,
        ∀ t ⊆ h, t.card = r + 1 → ∀ a ∈ t,
          (∀ b ∈ t, a ≤ b) → color t = tag a := by
  classical
  intro k
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    intro s _ color
    refine ⟨∅, Finset.empty_subset _, rfl, (fun _ => color ∅), ?_⟩
    intro t ht hcard a ha _
    have : t = ∅ := Finset.subset_empty.mp ht
    simp [this] at ha
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨R N + 1, ?_⟩
    intro s hs color
    have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
    let v := s.min' hsne
    have hv : v ∈ s := Finset.min'_mem _ _
    have hrest : R N ≤ (s.erase v).card := by
      rw [Finset.card_erase_of_mem hv]
      omega
    obtain ⟨B, hBs, hBcard, c, hc⟩ := hR N (s.erase v) hrest (fun t => color (insert v t))
    obtain ⟨H, hHB, hHcard, tag, htag⟩ := hN B hBcard.ge color
    have hvH : v ∉ H := fun h => (Finset.mem_erase.mp (hBs (hHB h))).1 rfl
    have hvmin : ∀ a ∈ B, v < a := by
      intro a ha
      have hsa := Finset.mem_erase.mp (hBs ha)
      exact lt_of_le_of_ne (Finset.min'_le _ _ hsa.2) hsa.1.symm
    refine ⟨insert v H, Finset.insert_subset hv (hHB.trans (hBs.trans (Finset.erase_subset _ _))),
      by simp [hvH, hHcard], (fun a => if a = v then c else tag a), ?_⟩
    intro t ht hcard a ha hamin
    by_cases hvt : v ∈ t
    · have hat : a = v := by
        apply Nat.le_antisymm (hamin v hvt)
        rcases Finset.mem_insert.mp (ht ha) with hav | haH
        · exact hav ▸ le_rfl
        · exact (hvmin a (hHB haH)).le
      subst a
      have het : t.erase v ⊆ B := by
        intro a ha
        rcases Finset.mem_insert.mp (ht (Finset.mem_erase.mp ha).2) with hav | haH
        · exact False.elim ((Finset.mem_erase.mp ha).1 hav)
        · exact hHB haH
      have hecard : (t.erase v).card = r := by
        rw [Finset.card_erase_of_mem hvt, hcard]
        omega
      have h := hc (t.erase v) het hecard
      simpa [Finset.insert_erase hvt] using h
    · have htH : t ⊆ H := by
        intro b hb
        rcases Finset.mem_insert.mp (ht hb) with hbv | hbH
        · exact False.elim (hvt (hbv ▸ hb))
        · exact hbH
      have hav : a ≠ v := fun he => hvt (he ▸ ha)
      simp only [ite_eq_right hav]
      exact htag t htH hcard a ha hamin

theorem finite_ramsey {C : Type*} [Fintype C] [Nonempty C] :
    ∀ r k : ℕ, ∃ N ≥ k, ∀ (s : Finset ℕ), N ≤ s.card →
      ∀ color : Finset ℕ → C, ∃ h ⊆ s, h.card = k ∧ Homogeneous r color h := by
  classical
  intro r
  induction r with
  | zero =>
    intro k
    refine ⟨k, le_rfl, ?_⟩
    intro s hs color
    obtain ⟨h, hhs, hh⟩ := Finset.exists_subset_card_eq hs
    refine ⟨h, hhs, hh, color ∅, ?_⟩
    intro t _ ht
    rw [Finset.card_eq_zero.mp ht]
  | succ r ih =>
    choose R hRk hR using ih
    intro k
    obtain ⟨N, hN⟩ := end_homogeneous r R hR (Fintype.card C * k)
    refine ⟨max N k, le_max_right _ _, ?_⟩
    intro s hs color
    obtain ⟨H, hHs, hHcard, tag, htag⟩ := hN s ((le_max_left _ _).trans hs) color
    obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := H) (t := (Finset.univ : Finset C)) (f := tag)
      (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty
      (by simpa using hHcard.ge : Fintype.card C * k ≤ H.card)
    obtain ⟨h, hsub, hcard⟩ := Finset.exists_subset_card_eq hc
    refine ⟨h, hsub.trans (Finset.filter_subset _ _ |>.trans hHs), hcard, c, ?_⟩
    intro t ht htcard
    have htne : t.Nonempty := Finset.card_pos.mp (by omega)
    let a := t.min' htne
    have ha : a ∈ t := Finset.min'_mem _ _
    have ha' := Finset.mem_filter.mp (hsub (ht ha))
    rw [htag t (ht.trans (hsub.trans (Finset.filter_subset _ _))) htcard a ha
      (fun b hb => Finset.min'_le _ _ hb), ha'.2]

end DirectedFeedback.Ranks

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

variable {I J : Type*} [Fintype I] [Fintype J]

theorem payoff_left (a : I → J → ℝ) (x x' : I → ℝ) (y : J → ℝ) (r s : ℝ) :
    payoff a (r • x + s • x') y = r * payoff a x y + s * payoff a x' y := by
  simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem payoff_right (a : I → J → ℝ) (x : I → ℝ) (y y' : J → ℝ) (r s : ℝ) :
    payoff a x (r • y + s • y') = r * payoff a x y + s * payoff a x y' := by
  simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem single_mem_probabilitySimplex {Index : Type*} [Fintype Index] [DecidableEq Index]
    (index : Index) : Pi.single index 1 ∈ probabilitySimplex Index :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ => le_rfl⟩, by simp⟩

theorem convex_probabilitySimplex (Index : Type*) [Fintype Index] :
    Convex ℝ (probabilitySimplex Index) := by
  intro left hleft right hright weightLeft weightRight hweightLeft hweightRight hsum
  refine ⟨fun index => ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hweightLeft (hleft.1 index))
      (mul_nonneg hweightRight (hright.1 index))
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
      hleft.2, hright.2, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

theorem isCompact_probabilitySimplex (Index : Type*) [Fintype Index] :
    IsCompact (probabilitySimplex Index) := by
  have hform : probabilitySimplex Index =
      (⋂ index : Index, {weights : Index → ℝ | 0 ≤ weights index}) ∩
        {weights | ∑ index, weights index = 1} := by
    ext weights
    simp only [probabilitySimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  apply IsCompact.of_isClosed_subset (s := Set.Icc (0 : Index → ℝ) 1) isCompact_Icc
  · rw [hform]
    exact (isClosed_iInter fun index =>
      isClosed_le continuous_const (continuous_apply index)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  · intro weights hweights
    refine ⟨hweights.1, fun index => ?_⟩
    change weights index ≤ 1
    rw [← hweights.2]
    exact Finset.single_le_sum (fun other _ => hweights.1 other) (Finset.mem_univ index)

theorem finite_minimax [Nonempty I] [Nonempty J] (a : I → J → ℝ) (δ : ℝ)
    (hresponse : ∀ y ∈ probabilitySimplex J, ∃ i, (∑ j, y j * a i j) ≤ δ) :
    ∃ x ∈ probabilitySimplex I, ∀ j, (∑ i, x i * a i j) ≤ δ := by
  classical
  have hI : (probabilitySimplex I).Nonempty := ⟨Pi.single (Classical.arbitrary I) 1,
    single_mem_probabilitySimplex _⟩
  have hJ : (probabilitySimplex J).Nonempty := ⟨Pi.single (Classical.arbitrary J) 1,
    single_mem_probabilitySimplex _⟩
  have hleft (y : J → ℝ) : Continuous (fun x : I → ℝ => payoff a x y) := by
    unfold payoff
    fun_prop
  have hright (x : I → ℝ) : Continuous (fun y : J → ℝ => payoff a x y) := by
    unfold payoff
    fun_prop
  have hcLeft (y : J → ℝ) : ConvexOn ℝ (probabilitySimplex I) (fun x => payoff a x y) := by
    refine ⟨convex_probabilitySimplex _, ?_⟩
    intro x _ x' _ r s _ _ _
    exact (payoff_left a x x' y r s).le
  have hcRight (x : I → ℝ) : ConcaveOn ℝ (probabilitySimplex J) (fun y => payoff a x y) := by
    refine ⟨convex_probabilitySimplex _, ?_⟩
    intro y _ y' _ r s _ _ _
    exact (payoff_right a x y y' r s).ge
  obtain ⟨x, hx, y, hy, hxy⟩ := Sion.exists_isSaddlePointOn hI (convex_probabilitySimplex _)
    (isCompact_probabilitySimplex _) (fun y _ => (hleft y).continuousOn.lowerSemicontinuousOn)
    (fun y _ => (hcLeft y).quasiconvexOn) (convex_probabilitySimplex _) hJ
    (isCompact_probabilitySimplex _) (fun x _ => (hright x).continuousOn.upperSemicontinuousOn)
    (fun x _ => (hcRight x).quasiconcaveOn)
  obtain ⟨i, hi⟩ := hresponse y hy
  refine ⟨x, hx, ?_⟩
  intro j
  have hsaddle := hxy (Pi.single i 1) (single_mem_probabilitySimplex _)
    (Pi.single j 1) (single_mem_probabilitySimplex _)
  have hpureLeft : payoff a (Pi.single i 1) y = ∑ j, y j * a i j := by
    simp [payoff, Pi.single_apply, ite_mul]
  have hpureRight : payoff a x (Pi.single j 1) = ∑ i, x i * a i j := by
    simp [payoff, Pi.single_apply, mul_ite, ite_mul]
  rw [hpureLeft, hpureRight] at hsaddle
  exact hsaddle.trans hi

theorem rational_simplex_approximation [Nonempty I] (x : I → ℝ)
    (hx : x ∈ probabilitySimplex I) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : I → ℚ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      (∑ i, |(q i : ℝ) - x i|) < ε := by
  classical
  let n : ℝ := Fintype.card I
  have hn : 0 < n := by
    change 0 < (Fintype.card I : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  let d := ε / (2 * n)
  have hd : 0 < d := by dsimp [d]; positivity
  have hex (i : I) : ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ x i ∧ x i - q < d := by
    by_cases hxi : x i = 0
    · exact ⟨0, le_rfl, by simp [hxi], by simpa [hxi] using hd⟩
    have hp : 0 < x i := lt_of_le_of_ne (hx.1 i) (Ne.symm hxi)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (x i - d) < x i by
      exact max_lt hp (by linarith))
    refine ⟨q, ?_, hq2.le, ?_⟩
    · exact_mod_cast (le_max_left _ _).trans hq1.le
    · have hh := (le_max_right _ _).trans_lt hq1
      linarith
  choose q hqnonneg hqle hqerr using hex
  let deficit : ℚ := 1 - ∑ i, q i
  have hdef : 0 ≤ deficit := by
    have hsum : (∑ i, (q i : ℝ)) ≤ 1 := by
      rw [← hx.2]
      exact Finset.sum_le_sum (fun i _ => hqle i)
    dsimp [deficit]
    exact_mod_cast (sub_nonneg.mpr hsum)
  have herr : (deficit : ℝ) < ε / 2 := by
    have hh := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hqerr i)
    have hdid : (∑ _i : I, d) = ε / 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change n * (ε / (2 * n)) = ε / 2
      field_simp
    rw [Finset.sum_sub_distrib, hx.2, hdid] at hh
    simpa [deficit] using hh
  let i₀ : I := Classical.arbitrary I
  let q' : I → ℚ := fun i => q i + if i = i₀ then deficit else 0
  refine ⟨q', (fun i => add_nonneg (hqnonneg i) (by split_ifs <;> positivity)), ?_, ?_⟩
  · simp [q', Finset.sum_add_distrib, deficit]
  · calc
      (∑ i, |(q' i : ℝ) - x i|) ≤
          ∑ i, ((x i - (q i : ℝ)) + if i = i₀ then (deficit : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [q']
        push_cast
        split_ifs with hi
        · have ht := abs_add_le ((q i : ℝ) - x i) (deficit : ℝ)
          rw [abs_of_nonpos (sub_nonpos.mpr (hqle i)),
            abs_of_nonneg (show (0 : ℝ) ≤ (deficit : ℝ) by exact_mod_cast hdef)] at ht
          calc
            |(q i : ℝ) + (deficit : ℝ) - x i| =
                |((q i : ℝ) - x i) + (deficit : ℝ)| := by congr 1; ring
            _ ≤ -((q i : ℝ) - x i) + (deficit : ℝ) := ht
            _ = _ := by ring
        · rw [Rat.cast_zero, add_zero, add_zero, abs_of_nonpos (sub_nonpos.mpr (hqle i))]
          linarith
      _ = 2 * deficit := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hx.2]
        simp [deficit]
        ring
      _ < ε := by linarith

end DirectedFeedback.Ranks

noncomputable section
open scoped BigOperators
namespace DirectedFeedback.Ranks

theorem triple_nonempty {L : ℕ} (hL : 3 ≤ L) : Nonempty (Triple L) := by
  classical
  refine ⟨⟨Finset.univ.image (Fin.castLE hL), ?_⟩⟩
  rw [Finset.card_image_of_injective _ (Fin.castLE_injective hL)]
  simp

theorem rankPayoff_abs {L N : ℕ} (ψ : Increasing L N) (t : RankTest L N) :
    |rankPayoff ψ t| ≤ 1 := by
  unfold rankPayoff
  split_ifs <;> norm_num

theorem bucket_close (b : ℕ) (hb : 0 < b) (x y : ℝ) (_hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ⌊(b : ℝ) * x⌋₊ = ⌊(b : ℝ) * y⌋₊) : x - y ≤ 1 / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h1 := Nat.lt_floor_add_one ((b : ℝ) * x)
  have h2 := Nat.floor_le (mul_nonneg hb'.le hy)
  rw [h] at h1
  apply (le_div_iff₀ hb').mpr
  nlinarith

theorem rank_spreading (L : ℕ) (hL : 3 ≤ L) (η : ℝ) (hη : 0 < η) :
    ∃ N ≥ L, ∃ μ : Increasing L N → ℚ,
      (∀ ψ, 0 ≤ μ ψ) ∧ (∑ ψ, μ ψ = 1) ∧
      ∀ I I' : Triple L, ∀ A : Finset (Finset (Fin N)),
        |(∑ ψ, (μ ψ : ℝ) * if I.val.image ψ.val ∈ A then 1 else 0) -
          (∑ ψ, (μ ψ : ℝ) * if I'.val.image ψ.val ∈ A then 1 else 0)| ≤ η := by
  classical
  let : Nonempty (Triple L) := triple_nonempty hL
  let P := Triple L × Triple L
  let c : ℝ := Fintype.card P
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card P)
  obtain ⟨b₀, hb₀⟩ := exists_nat_one_div_lt (show 0 < η / (4 * c) by positivity)
  let b := b₀ + 1
  have hb : 0 < b := Nat.succ_pos _
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hcb : c * (1 / (b : ℝ)) < η / 4 := by
    have hh := mul_lt_mul_of_pos_left hb₀ hc
    have heq : c * (η / (4 * c)) = η / 4 := by field_simp
    simpa [b, heq] using hh
  obtain ⟨N, hNL, hN⟩ := finite_ramsey (C := P → Fin (b + 1)) 3 L
  let : Nonempty (Increasing L N) := ⟨⟨Fin.castLE hNL, fun _ _ h => h⟩⟩
  have hresponse : ∀ τ ∈ probabilitySimplex (RankTest L N), ∃ ψ : Increasing L N,
      (∑ t, τ t * rankPayoff ψ t) ≤ η / 4 := by
    intro τ hτ
    let q (p : P) (Z : Finset (Fin N)) : ℝ :=
      ∑ A : Finset (Finset (Fin N)), τ (p, A) * if Z ∈ A then 1 else 0
    have hq0 (p : P) (Z : Finset (Fin N)) : 0 ≤ q p Z := by
      apply Finset.sum_nonneg
      intro A _
      split_ifs <;> simp [hτ.1 (p, A)]
    have hq1 (p : P) (Z : Finset (Fin N)) : q p Z ≤ 1 := by
      calc
        q p Z ≤ ∑ A : Finset (Finset (Fin N)), τ (p, A) := by
          apply Finset.sum_le_sum
          intro A _
          split_ifs <;> simp [hτ.1 (p, A)]
        _ ≤ ∑ p' : P, ∑ A : Finset (Finset (Fin N)), τ (p', A) := by
          exact Finset.single_le_sum (fun p' _ => Finset.sum_nonneg (fun A _ => hτ.1 (p', A)))
            (Finset.mem_univ p)
        _ = 1 := by
          have hh := hτ.2
          rw [Fintype.sum_prod_type] at hh
          exact hh
    let color (s : Finset ℕ) (p : P) : Fin (b + 1) :=
      ⟨⌊(b : ℝ) * q p (toFinite N s)⌋₊, by
        have hh := Nat.floor_mono (mul_le_mul_of_nonneg_left (hq1 p (toFinite N s)) hb'.le)
        simp only [mul_one, Nat.floor_natCast] at hh
        omega⟩
    obtain ⟨H, hHN, hHcard, tag, htag⟩ := hN (Finset.range N) (by simp) color
    let ψ₀ : Fin L → Fin N := fun i =>
      ⟨H.orderEmbOfFin hHcard i, Finset.mem_range.mp (hHN (H.orderEmbOfFin_mem hHcard i))⟩
    have hψ : StrictMono ψ₀ := fun i j hij => (H.orderEmbOfFin hHcard).strictMono hij
    let ψ : Increasing L N := ⟨ψ₀, hψ⟩
    have hmono (I : Triple L) : color ((I.val.image ψ.val).image Fin.val) = tag := by
      apply htag
      · intro a ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact H.orderEmbOfFin_mem hHcard i
      · rw [Finset.card_image_of_injective _ Fin.val_injective,
          Finset.card_image_of_injective _ hψ.injective]
        exact I.property
    have hclose (p : P) : q p (p.1.val.image ψ.val) - q p (p.2.val.image ψ.val) ≤ 1 / b := by
      apply bucket_close b hb _ _ (hq0 _ _) (hq0 _ _)
      have heq := congrArg (fun f => (f p).val) ((hmono p.1).trans (hmono p.2).symm)
      simpa only [color, toFinite_image] using heq
    refine ⟨ψ, ?_⟩
    calc
      (∑ t, τ t * rankPayoff ψ t) =
          ∑ p : P, (q p (p.1.val.image ψ.val) - q p (p.2.val.image ψ.val)) := by
        rw [Fintype.sum_prod_type]
        simp only [rankPayoff, mul_sub, Finset.sum_sub_distrib, q]
        rfl
      _ ≤ ∑ _p : P, (1 / (b : ℝ)) := Finset.sum_le_sum (fun p _ => hclose p)
      _ = c * (1 / (b : ℝ)) := by simp [c]
      _ ≤ η / 4 := hcb.le
  obtain ⟨x, hx, hxbound⟩ := finite_minimax rankPayoff (η / 4) hresponse
  obtain ⟨μ, hμ0, hμ1, hμerr⟩ := rational_simplex_approximation x hx (η / 2) (by positivity)
  have hμbound (t : RankTest L N) : (∑ ψ, (μ ψ : ℝ) * rankPayoff ψ t) < η := by
    have hle : (∑ ψ, (μ ψ : ℝ) * rankPayoff ψ t) ≤
        (∑ ψ, x ψ * rankPayoff ψ t) + ∑ ψ, |(μ ψ : ℝ) - x ψ| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro ψ _
      have hh : ((μ ψ : ℝ) - x ψ) * rankPayoff ψ t ≤ |(μ ψ : ℝ) - x ψ| := by
        calc
          _ ≤ |((μ ψ : ℝ) - x ψ) * rankPayoff ψ t| := le_abs_self _
          _ = |(μ ψ : ℝ) - x ψ| * |rankPayoff ψ t| := abs_mul _ _
          _ ≤ |(μ ψ : ℝ) - x ψ| * 1 :=
            mul_le_mul_of_nonneg_left (rankPayoff_abs ψ t) (abs_nonneg _)
          _ = _ := mul_one _
      linarith
    have hh := hxbound t
    linarith
  refine ⟨N, hNL, μ, hμ0, hμ1, ?_⟩
  intro I I' A
  have h1 := hμbound ((I, I'), A)
  have h2 := hμbound ((I', I), A)
  simp only [rankPayoff, mul_sub, Finset.sum_sub_distrib] at h1 h2
  exact abs_le.mpr ⟨by linarith, h1.le⟩

end DirectedFeedback.Ranks
open scoped Classical
namespace DirectedFeedback.Ranks
open DirectedFeedback.SourceProbability
open DirectedFeedback.SourceProbability.FiniteDistribution

theorem exists_spreading_law (L : ℕ) (hL : 3 ≤ L) (η : ℝ) (hη : 0 < η) :
    ∃ N ≥ L, ∃ μ : FiniteDistribution (Increasing L N), Spreads μ η ∧
      ∀ ψ, ∃ q : ℚ, μ.weight ψ = q := by
  obtain ⟨N, hNL, q, hq0, hq1, hq⟩ := rank_spreading L hL η hη
  let μ : FiniteDistribution (Increasing L N) :=
    ⟨fun ψ => q ψ, fun ψ => by exact_mod_cast hq0 ψ, by exact_mod_cast hq1⟩
  refine ⟨N, hNL, μ, ?_, fun ψ => ⟨q ψ, rfl⟩⟩
  intro I I' A
  convert hq I I' A using 1
  all_goals try with_reducible_and_instances rfl
  simp only [probability, μ, decide_eq_true_eq, mul_ite, mul_one, mul_zero]

end DirectedFeedback.Ranks

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_LastBias
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Hastad.SourceDescriptorEmission.localInputDecidableEq _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open DirectedFeedback.SourceProbability
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open scoped Classical
noncomputable section
open scoped Classical BigOperators
noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open Pivotal

theorem exists_parameters (D : ℕ) : Nonempty (Parameters D) := by
  let M := 128*(D+1)
  let H : ℝ := 8*((D:ℝ)+1)
  let p := lastBias M
  let γ := p/1000
  have hM : (0:ℝ) < M := by dsimp [M]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hp : 0 < p := by dsimp [p, lastBias]; positivity
  have hg : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨T, hT⟩ := exists_nat_gt (8*M*(H*M)/p)
  have hT0 : 0 < T := by
    have ht : (0:ℝ) < T := lt_of_le_of_lt (by positivity) hT
    exact_mod_cast ht
  have hprefix : H * (M * Real.exp (-(p*T/(8*M)))) ≤ 1 := by
    have harg : H*M ≤ p*T/(8*M) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have hh := (div_lt_iff₀ hp).mp hT
      nlinarith
    calc
      _ = (H*M)/Real.exp (p*T/(8*M)) := by rw [Real.exp_neg]; ring
      _ ≤ 1 := (div_le_one (Real.exp_pos _)).mpr
        (harg.trans (by linarith [Real.add_one_le_exp (p*T/(8*M))]))
  obtain ⟨K, hK⟩ := exists_nat_gt (max 0 ((M:ℝ)*2^T*D/γ))
  have hK0 : (0:ℝ) < K := lt_of_le_of_lt (le_max_left _ _) hK
  have hKnat : 0 < K := by exact_mod_cast hK0
  have hcomparison : (M:ℝ)*2^T*D/K ≤ γ := by
    apply (div_le_iff₀ hK0).mpr
    have hh := (div_lt_iff₀ hg).mp (lt_of_le_of_lt (le_max_right _ _) hK)
    linarith
  obtain ⟨J,hJ,hjunta⟩ := uniform_dyadic_junta M (((D:ℝ)+1)/γ) γ (by positivity) hg
  have hJ0 : (0:ℝ) < J := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  let t : ℝ := min (1/4) (min (1/K) (γ/(J:ℝ)^2))
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨θ,hθ0,hθ⟩ := exists_rat_btwn ht
  have hθnat : (0:ℚ) < θ := by exact_mod_cast hθ0
  have ht1 : (θ:ℝ) < 1/4 := hθ.trans_le (min_le_left _ _)
  have htK : (θ:ℝ) < 1/(K:ℝ) := hθ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htJ : (θ:ℝ) < γ/(J:ℝ)^2 := hθ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨⟨M,T,K,J,rfl,hT0,hKnat,hJ,θ,hθnat,by linarith,hprefix,hcomparison,hjunta,?_,?_⟩⟩
  · have hh := (lt_div_iff₀ hK0).mp htK
    nlinarith
  · exact ((lt_div_iff₀ (sq_pos_of_pos hJ0)).mp htJ).le

end DirectedFeedback.Construction

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal Ranks

theorem exists_rankParameters {D : ℕ} (P : Parameters D) (X : Type)
    [Fintype X] [Nonempty X] : Nonempty (RankParameters P X) := by
  let m : ℝ := Fintype.card X
  let ρ := min (lastBias P.M/1000) (1/m)
  let L := rankLength X P.T
  let η := ρ / (3*(L:ℝ)^3*2^((Fintype.card X)^P.T))
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  have hρ : 0 < ρ := lt_min P.gamma_pos (div_pos (by norm_num) hm)
  have hL : 3 ≤ L := by dsimp [L, rankLength]; omega
  have hLc : (0:ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N,_,μ,hs,hr⟩ := exists_spreading_law L hL η hη
  refine ⟨⟨N,μ,η,ρ,hη,hρ.le,min_le_left _ _,?_,?_,hs,hr⟩⟩
  · have hh := min_le_right (lastBias P.M/1000) (1/m)
    have hb := (le_div_iff₀ hm).mp hh
    dsimp [m] at hb ⊢
    nlinarith
  · dsimp only [η]
    have hden : (3:ℝ)*(L:ℝ)^3*2^((Fintype.card X)^P.T) ≠ 0 := by positivity
    field_simp
    ring_nf
    rfl

end DirectedFeedback.Construction
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Rational
attribute [-instance] _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open scoped Classical BigOperators
open scoped Classical
open scoped Classical
open scoped Classical BigOperators
open scoped BigOperators
open scoped BigOperators
open DirectedFeedback.SourceProbability
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped Classical BigOperators

open scoped Classical BigOperators
namespace DirectedFeedback

namespace Rational

theorem nat (n : ℕ) : Rational (n:ℝ) := ⟨n,by simp⟩
theorem zero : Rational 0 := ⟨0,by simp⟩
theorem one : Rational 1 := ⟨1,by simp⟩
theorem sub {x y : ℝ} (hx : Rational x) (hy : Rational y) : Rational (x-y) := by
  obtain ⟨a,rfl⟩ := hx; obtain ⟨b,rfl⟩ := hy
  exact ⟨a-b,by simp⟩
theorem mul {x y : ℝ} (hx : Rational x) (hy : Rational y) : Rational (x*y) := by
  obtain ⟨a,rfl⟩ := hx; obtain ⟨b,rfl⟩ := hy
  exact ⟨a*b,by simp⟩
theorem inv {x : ℝ} (hx : Rational x) : Rational x⁻¹ := by
  obtain ⟨a,rfl⟩ := hx
  exact ⟨a⁻¹,by simp⟩
theorem div {x y : ℝ} (hx : Rational x) (hy : Rational y) : Rational (x/y) := by
  simpa only [div_eq_mul_inv] using hx.mul hy.inv
theorem pow {x : ℝ} (hx : Rational x) (n : ℕ) : Rational (x^n) := by
  obtain ⟨a,rfl⟩ := hx
  exact ⟨a^n,by simp⟩
theorem prod {I : Type*} (s : Finset I) (f : I → ℝ) (h : ∀ i ∈ s, Rational (f i)) :
    Rational (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (by simp)).mul (ih (fun i hi => h i (by simp [hi])))
end Rational
end DirectedFeedback

namespace DirectedFeedback.SourceProbability.FiniteDistribution
open DirectedFeedback
variable {I J : Type*} [Fintype I] [Fintype J]

theorem RationalMass.uniform [Nonempty I] : RationalMass (uniform I) :=
  fun _ => Rational.one.div (Rational.nat _)

theorem RationalMass.product {μ : FiniteDistribution I} {ν : FiniteDistribution J}
    (hμ : μ.RationalMass) (hν : ν.RationalMass) : (μ.product ν).RationalMass :=
  fun x => (hμ x.1).mul (hν x.2)

theorem RationalMass.sigma {F : I → Type*} [∀ i, Fintype (F i)]
    {μ : FiniteDistribution I} {ν : ∀ i, FiniteDistribution (F i)}
    (hμ : μ.RationalMass) (hν : ∀ i, (ν i).RationalMass) : (μ.sigma ν).RationalMass :=
  fun x => (hμ x.1).mul (hν x.1 x.2)

theorem RationalMass.iid {μ : FiniteDistribution I} (hμ : μ.RationalMass) (n : ℕ) :
    (μ.iid n).RationalMass := by
  intro x
  change Rational (∏ i : Fin n, μ.weight (x i))
  exact Rational.prod _ _ (fun i _ => hμ (x i))

theorem RationalMass.table {μ : I → FiniteDistribution J}
    (hμ : ∀ i, (μ i).RationalMass) : (table μ).RationalMass :=
  fun x => Rational.prod _ _ (fun i _ => hμ i (x i))

end DirectedFeedback.SourceProbability.FiniteDistribution

namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : ℕ} [NeZero M] [NeZero T]

omit [NeZero M] [NeZero T] [Nonempty X] in
theorem subsetLaw_rational (i : Fin M) : (subsetLaw (X:=X) i).RationalMass := by
  apply RationalMass.table
  intro _ b
  change Rational (if b then bias i else 1-bias i)
  have hp : Rational (bias i) := (Rational.nat 2).inv.pow _
  split_ifs
  · exact hp
  · exact Rational.one.sub hp

end DirectedFeedback.Construction

open scoped Classical BigOperators

open scoped Classical BigOperators
namespace DirectedFeedback.Construction
open DirectedFeedback.SourceProbability FiniteDistribution
open RankGraph Prefix PrefixExperiment Games Pivotal Ranks
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {D : ℕ} (P : Parameters D) (R : RankParameters P X)
  (G : Game U V E X Y) (hG : G.edgeLaw.RationalMass)

instance parameterized_output_nonempty : Nonempty (OutputVertex (M := P.M) G R.law) := by
  obtain ⟨w⟩ := (fullLaw (M := P.M) G R.law).support_nonempty
  exact ⟨.inr (.inl (.inl w))⟩

end DirectedFeedback.Construction

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_AllGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.SourceProbability.FiniteDistribution

theorem fixed_denominator {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ x, Rational (w x)) (hn : ∀ x, 0 ≤ w x) :
    ∃ C : Nat, 0 < C ∧ ∃ c : Ω → Nat, ∀ x, (C:ℝ)*w x=c x := by
  choose q hq using hw
  let C := ∏ x, (q x).den
  have hC : 0 < C := Finset.prod_pos (fun x _ => (q x).den_pos)
  have hd (x : Ω) : (q x).den ∣ C := Finset.dvd_prod_of_mem _ (Finset.mem_univ x)
  choose k hk using hd
  refine ⟨C,hC,fun x => (q x).num.toNat*k x,?_⟩
  intro x
  have hnum : 0 ≤ (q x).num := Rat.num_nonneg.mpr (by exact_mod_cast hq x ▸ hn x)
  rw [hq x,Rat.cast_def,hk x,Nat.cast_mul,Nat.cast_mul]
  have hden : ((q x).den:ℝ) ≠ 0 := by exact_mod_cast (q x).den_ne_zero
  have hh : (((q x).num.toNat:Nat):ℝ)=((q x).num:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  rw [hh]
  field_simp

end DirectedFeedback.SourceProbability.FiniteDistribution

end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_PacketLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback.PacketSeeds
open SourceProbability FiniteDistribution Construction PrefixExperiment Games
variable {U V E X Y : Type} [Fintype U] [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
variable {M T N : Nat} [NeZero M] [NeZero T]
variable (ψLaw : FiniteDistribution (Emb (rankLength X T) N))

theorem mass_nonnegative (H K : Nat) (s : Seed X Y M T N) : 0 ≤ mass ψLaw H K s := by
  rcases s with s | (s | (s | s)) <;> exact mul_nonneg (Nat.cast_nonneg _) (FiniteDistribution.nonnegative _ _)

omit [Nonempty X] in
theorem slot_rational : (slotLaw (X:=X) (M:=M)).RationalMass :=
  RationalMass.uniform.sigma (fun i => Construction.subsetLaw_rational i)

omit [Nonempty X] in
theorem common_rational (hψ : ψLaw.RationalMass) : (commonLaw (M:=M) ψLaw).RationalMass :=
  hψ.product (RationalMass.uniform.sigma (fun _ => slot_rational.iid _))

omit [Nonempty Y] in
theorem localCompare_rational (t : Nat) : (localCompareLaw (Y:=Y) (M:=M) t).RationalMass := by
  apply RationalMass.uniform.sigma
  intro i
  apply RationalMass.uniform.product
  apply RationalMass.table
  intro _ b
  obtain ⟨⟨b₁,b₂⟩,b₃⟩ := b
  have hp : Rational (bias i) := (Rational.nat 2).inv.pow _
  have h1 := Rational.one.sub hp
  cases b₁ <;> cases b₂ <;> cases b₃ <;>
    first | exact Rational.one.sub ((Rational.nat 2).mul hp)
          | exact hp.pow 2 | exact hp.mul h1 | exact Rational.zero

theorem mass_rational (hψ : ψLaw.RationalMass) (H K : Nat) (s : Seed X Y M T N) :
    Rational (mass ψLaw H K s) := by
  rcases s with s | (s | (s | s))
  · exact (Rational.nat H).mul ((hψ.product (slot_rational.iid T)) s)
  · exact (Rational.nat _).mul (((common_rational ψLaw hψ).product
        (RationalMass.uniform.sigma (fun _ => RationalMass.uniform))) s)
  · exact (Rational.nat _).mul (((common_rational ψLaw hψ).product
        (RationalMass.uniform.sigma (fun _ => RationalMass.uniform))) s)
  · exact (Rational.nat K).mul (((common_rational ψLaw hψ).sigma
        (fun d => localCompare_rational d.2.1.val)) s)

theorem denominator (hψ : ψLaw.RationalMass) (H K : Nat) :
    ∃ C : Nat, 0<C ∧ ∃ c : Seed X Y M T N → Nat, ∀ s, (C:ℝ)*mass ψLaw H K s=c s :=
  fixed_denominator _ (mass_rational ψLaw hψ H K) (mass_nonnegative ψLaw H K)

end DirectedFeedback.PacketSeeds

end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators
namespace DirectedFeedback
open Construction Games PacketSeeds SourceProbability FiniteDistribution RankGraph
open DFVSGames.Foundations DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity
open DFVSGames.Explicit.MachineOutputContract

theorem rankSize_pos {D : Nat} (P : Parameters D) (X : Type) [Fintype X]
    (R : RankParameters P X) : 0<R.N := by
  obtain ⟨ψ⟩ := R.law.support_nonempty
  have hL : 0 < rankLength X P.T := by unfold rankLength; omega
  exact (ψ.val.val ⟨0,hL⟩).isLt |> (fun h => lt_of_le_of_lt (Nat.zero_le _) h)

theorem main_oai : MainStatement := by
  intro A _ language hNP
  obtain ⟨V,hV⟩ := hNP
  obtain ⟨D,hD⟩ := exists_nat_ge (4*A)
  obtain ⟨P⟩ := exists_parameters D
  obtain ⟨S⟩ := DFVSGames.theorem11 P.theta P.theta
    (by exact_mod_cast P.theta_pos) P.theta_half (by exact_mod_cast P.theta_pos) P.theta_half
  let : NeZero S.alphabet := ⟨by have := S.alphabetAtLeastTwo; omega⟩
  obtain ⟨R⟩ := exists_rankParameters P (RawFamily.X S.alphabet)
  let : NeZero R.N := ⟨ne_of_gt (rankSize_pos P _ R)⟩
  obtain ⟨C,hC,c,hc⟩ := PacketSeeds.denominator (Y:=RawFamily.Y S.alphabet) (M:=P.M)
    R.law R.rational (8*(D+1)) P.K
  exact ⟨RawFamily.reduction P S R C c hC hc A hD language V hV⟩

end DirectedFeedback

end
end

end OAI
end

theorem solution : type_of% @OAI.DirectedFeedback.main_oai := @OAI.DirectedFeedback.main_oai
