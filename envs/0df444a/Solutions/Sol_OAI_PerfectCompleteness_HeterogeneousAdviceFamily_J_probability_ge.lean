-- Prove2me | solution 1 for OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:40.399166+00:00
-- url     : https://prove2.me/submissions/55ba3d47-c08a-46a3-9b78-1ea4af835442

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P008
import Definitions.Def_OAIQ252P011
import Theorems.Thm_OAI_PerfectCompleteness_MatrixInverse_noiseEnergy_le_of_global

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BilinearGramCompressionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixSlice

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

theorem expect_translate_eq_slice [Finite E] [Finite C]
    (W : Submodule F2 E) (C' : Submodule F2 C) (T : E →ₗ[F2] C)
    (f : (E →ₗ[F2] C) → ℝ) :
    (𝔼 A : Parameter W C', f (translate W C' T A)) =
      𝔼 X : Slice W C' T, f X.val :=
  Fintype.expect_equiv (parameterEquivSlice W C' T) _ _ (fun _ => rfl)

theorem expect_restrict_eq_slice [Finite E] [Finite C]
    (W : Submodule F2 E) (C' : Submodule F2 C) (T : E →ₗ[F2] C)
    (f : (E →ₗ[F2] C) → ℝ) :
    (𝔼 A : Parameter W C', restrict f W C' T A) =
      𝔼 X : Slice W C' T, f X.val :=
  expect_translate_eq_slice W C' T f

theorem column_count_le_order (W : Submodule F2 E) (C' : Submodule F2 C) :
    Module.finrank F2 W ≤ order W C' := Nat.le_add_right _ _

theorem row_count_le_order (W : Submodule F2 E) (C' : Submodule F2 C) :
    Module.finrank F2 (C ⧸ C') ≤ order W C' := Nat.le_add_left _ _

end
end PerfectCompleteness.MatrixSlice

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual binary matrix and linear-map parity used in Lemma 5.3. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixParity

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped Matrix BigOperators Classical

section LinearMaps

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

/-- The exact number of binary linear maps, supplying the count in (5.20).
Taking `E` to be the subspace `W` counts precisely maps whose image lies in `W`. -/
theorem card_linearMaps [FiniteDimensional F2 E] [FiniteDimensional F2 C]
    [Fintype (C →ₗ[F2] E)] :
    Fintype.card (C →ₗ[F2] E) =
      2 ^ (Module.finrank F2 C * Module.finrank F2 E) := by
  classical
  let bC := Module.finBasis F2 C
  let bE := Module.finBasis F2 E
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (LinearMap.toMatrix bC bE).toEquiv]
  change Nat.card (Fin (Module.finrank F2 E) → Fin (Module.finrank F2 C) → F2) = _
  rw [Nat.card_fun, Nat.card_fun]
  simp [F2, Integration.BinaryLinear.F2, Nat.card_eq_fintype_card, ← pow_mul,
    Nat.mul_comm]

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixParity

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A13IndexLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The real-valued finite-probability steps at the end of Appendix A.5.

The results here prove normalized Cauchy--Schwarz/Hölder consequences and
Boolean moment identities. They do not introduce Proposition A.5 or Lemma A.6
as axioms, and do not identify a conditional estimate with Theorem 2.3.
-/

namespace UniqueGamesTheorem.Appendix.LevelInequality

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem boolean_positive_moment {f : α → ℝ} (hf : IsBoolean f)
    (k : ℕ) (hk : 0 < k) : (𝔼 x, f x ^ k) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  rcases hf x with h | h <;> simp [h, Nat.ne_of_gt hk]

theorem boolean_squared_norm_eq_density {f : α → ℝ} (hf : IsBoolean f) :
    (𝔼 x, f x ^ 2) = 𝔼 x, f x :=
  boolean_positive_moment hf 2 (by decide)

end UniqueGamesTheorem.Appendix.LevelInequality

noncomputable section

namespace UniqueGamesTheorem.Appendix.LevelInequality

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier

section ActualLinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Finite E] [Finite F]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem boolean_restriction (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    IsBoolean (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) := by
  intro N
  exact hf (UniqueGamesTheorem.Fourier.MatrixRestrictions.translate A B T N)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- On Boolean functions the restriction-global norm bound is exactly the
restriction-density hypothesis in Theorem 2.3. -/
theorem boolean_global_iff_density (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (d : ℕ) (η : ℝ) :
    IsRestrictionGlobal f d η ↔
      ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
        UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
          (𝔼 N, UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T N) ≤ η := by
  unfold IsRestrictionGlobal
  simp_rw [boolean_squared_norm_eq_density (boolean_restriction f hf _ _ _)]

end ActualLinearMaps

end UniqueGamesTheorem.Appendix.LevelInequality

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GlobalityLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixLevelBridge

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.LevelInequality

theorem levelCutoffConstant_nonneg (r : Nat) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    0 ≤ levelCutoffConstant r ρ := by
  unfold levelCutoffConstant
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact hρ
  · exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (Real.rpow_nonneg hρ _)

end UniqueGamesTheorem.Fourier.MatrixLevelBridge

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixInverse
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixNoise UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.LevelInequality UniqueGamesTheorem.Appendix.RankLevelFilter

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem exists_dense_restriction_of_family {Y : Type*} [Fintype Y]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (f : Y → (E →ₗ[F2] F) → ℝ) (hf : ∀ y, IsBoolean (f y))
    (hmass : (∑ y, 𝔼 X, f y X ^ 2) ≤ 1)
    (hretention : η ≤ ∑ y, noiseEnergy (f y)) :
    ∃ (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F),
      order W C' ≤ r ∧ ρ < (𝔼 N, restrict (f y) W C' T N) := by
  by_contra hnone
  have hg (y : Y) : IsRestrictionGlobal (f y) r ρ := by
    apply (boolean_global_iff_density (f y) (hf y) r ρ).mpr
    intro W C' T horder
    apply le_of_not_gt
    intro hdense
    exact hnone ⟨y, W, C', T, horder, hdense⟩
  have hbound : (∑ y, noiseEnergy (f y)) ≤
      (levelCutoffConstant r ρ + node (r + 1)) * (∑ y, 𝔼 X, f y X ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => noiseEnergy_le_of_global r ρ hρ hρ1 (f y) (hf y) (hg y)
  have hnonneg : 0 ≤ levelCutoffConstant r ρ + node (r + 1) :=
    add_nonneg (levelCutoffConstant_nonneg r ρ hρ.le) (node_pos _).le
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_left hmass hnonneg)
  simp only [mul_one] at hbound'
  exact (not_lt_of_ge (hretention.trans hbound')) hconstants

end
end PerfectCompleteness.MatrixInverse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DummyEliminationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.NonzeroAverage

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem card_subtype_ne_real (a : A) :
    (Fintype.card {x : A // x ≠ a} : ℝ) = (Fintype.card A : ℝ) - 1 := by
  have h : (Fintype.card A : ℝ) =
      1 + (Fintype.card {x : A // x ≠ a} : ℝ) := by
    simpa using Fintype.sum_eq_add_sum_subtype_ne (fun _ : A => (1 : ℝ)) a
  linarith

theorem card_mul_expect_eq (g : A → ℝ) (a : A) :
    (Fintype.card A : ℝ) * (𝔼 x, g x) =
      g a + (Fintype.card {x : A // x ≠ a} : ℝ) *
        (𝔼 x : {x : A // x ≠ a}, g x.1) := by
  rw [Fintype.card_mul_expect, Fintype.card_mul_expect]
  exact Fintype.sum_eq_add_sum_subtype_ne g a

theorem card_mul_expect_eq_sub_one (g : A → ℝ) (a : A) :
    (Fintype.card A : ℝ) * (𝔼 x, g x) =
      g a + ((Fintype.card A : ℝ) - 1) *
        (𝔼 x : {x : A // x ≠ a}, g x.1) := by
  rw [← card_subtype_ne_real a]
  exact card_mul_expect_eq g a

theorem expect_subtype_ne_le_expect_of_expect_le (g : A → ℝ) (a : A)
    (h : (𝔼 x : {x : A // x ≠ a}, g x.1) ≤ g a) :
    (𝔼 x : {x : A // x ≠ a}, g x.1) ≤ (𝔼 x, g x) := by
  let : Nonempty A := ⟨a⟩
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hcard).mp
  have hid := card_mul_expect_eq_sub_one g a
  nlinarith

theorem expect_subtype_ne_le_expect [Nontrivial A] (g : A → ℝ) (a : A)
    (h : ∀ x, g x ≤ g a) :
    (𝔼 x : {x : A // x ≠ a}, g x.1) ≤ (𝔼 x, g x) := by
  obtain ⟨b, hb⟩ := exists_ne a
  let : Nonempty {x : A // x ≠ a} := ⟨⟨b, hb⟩⟩
  apply expect_subtype_ne_le_expect_of_expect_le g a
  exact Finset.expect_le Finset.univ_nonempty (fun x _ => h x.1)

theorem nonzero_expect_le_expect [Zero A] [Nontrivial A] (g : A → ℝ)
    (h : ∀ x, g x ≤ g 0) :
    (𝔼 x : {x : A // x ≠ (0 : A)}, g x.1) ≤ (𝔼 x, g x) :=
  expect_subtype_ne_le_expect g 0 h

end PerfectCompleteness.NonzeroAverage

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PartialTableInverse
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PartialTableInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixNoise
open UniqueGamesTheorem.Fourier.MatrixRestrictions UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.LevelInequality UniqueGamesTheorem.Appendix.RankLevelFilter
open PerfectCompleteness.MatrixInverse

variable {Ω Y : Type*} [Fintype Y]

omit [Fintype Y] in
theorem indicator_boolean (f : Ω → Option Y) (y : Y) : IsBoolean (indicator f y) := by
  intro X
  unfold indicator
  split_ifs <;> simp

theorem sum_indicator_sq_le (f : Ω → Option Y) (X : Ω) :
    (∑ y, indicator f y X ^ 2) ≤ 1 := by
  cases h : f X <;> simp [indicator, h, eq_comm]

theorem definedEquality_eq_sum (f : Ω → Option Y) (X X' : Ω) :
    definedEquality f X X' = ∑ y, indicator f y X * indicator f y X' := by
  cases h : f X <;> cases h' : f X' <;>
    simp [definedEquality, indicator, h, h', mul_ite, eq_comm]

omit [Fintype Y] in
theorem definedEquality_le_self (f : Ω → Option Y) (X X' : Ω) :
    definedEquality f X X' ≤ definedEquality f X X := by
  unfold definedEquality
  split_ifs with h h' h'
  · exact le_rfl
  · obtain ⟨y, hy, _⟩ := h
    exact (h' ⟨y, hy, hy⟩).elim
  · norm_num
  · exact le_rfl

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem uniform_operator_eq_average (g : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator (fun _ : F => (Fintype.card F : ℝ)⁻¹) g X =
      𝔼 a : F, 𝔼 h : E →ₗ[F2] F2, g (X + h.smulRight a) := by
  unfold linearRealNoiseOperator
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (F →ₗ[F2] E)] in
theorem noiseEnergy_eq_average (g : (E →ₗ[F2] F) → ℝ) :
    noiseEnergy g =
      𝔼 X, 𝔼 a : F, 𝔼 h : E →ₗ[F2] F2, g X * g (X + h.smulRight a) := by
  unfold noiseEnergy
  simp_rw [uniform_operator_eq_average, Finset.mul_expect]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (F →ₗ[F2] E)] in
theorem allAgreement_eq_sum (f : (E →ₗ[F2] F) → Option Y) :
    allAgreement f = ∑ y, noiseEnergy (indicator f y) := by
  unfold allAgreement stepAgreement
  rw [Finset.expect_comm]
  simp_rw [definedEquality_eq_sum, Finset.expect_sum_comm, ← noiseEnergy_eq_average]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype F] [Fintype (E →ₗ[F2] F2)] [Fintype (F →ₗ[F2] E)] in
theorem indicator_mass_le_one (f : (E →ₗ[F2] F) → Option Y) :
    (∑ y, 𝔼 X, indicator f y X ^ 2) ≤ 1 := by
  rw [← Finset.expect_sum_comm]
  calc
    _ ≤ 𝔼 _X : E →ₗ[F2] F, (1 : ℝ) :=
      Finset.expect_le_expect fun X _ => sum_indicator_sq_le f X
    _ = 1 := Fintype.expect_const _

theorem exists_dense_slice_all (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (f : (E →ₗ[F2] F) → Option Y) (hagreement : η ≤ allAgreement f) :
    ∃ (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F),
      order W C' ≤ r ∧ ρ < (𝔼 N, restrict (indicator f y) W C' T N) := by
  apply exists_dense_restriction_of_family r ρ η hρ hρ1 hconstants (indicator f)
    (indicator_boolean f) (indicator_mass_le_one f)
  rwa [← allAgreement_eq_sum]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype F] [Fintype (F →ₗ[F2] E)] [Fintype Y] in
theorem stepAgreement_le_zero (f : (E →ₗ[F2] F) → Option Y) (a : F) :
    stepAgreement f a ≤ stepAgreement f 0 := by
  apply Finset.expect_le_expect
  intro X _
  apply Finset.expect_le_expect
  intro h _
  simpa using definedEquality_le_self f X (X + h.smulRight a)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (F →ₗ[F2] E)] [Fintype Y] in
theorem nonzeroAgreement_le_all [Nontrivial F]
    (f : (E →ₗ[F2] F) → Option Y) :
    nonzeroAgreement f ≤ allAgreement f :=
  PerfectCompleteness.NonzeroAverage.nonzero_expect_le_expect
    (stepAgreement f) (stepAgreement_le_zero f)

theorem exists_dense_slice_nonzero [Nontrivial F]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (f : (E →ₗ[F2] F) → Option Y) (hagreement : η ≤ nonzeroAgreement f) :
    ∃ (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F),
      order W C' ≤ r ∧ ρ < (𝔼 N, restrict (indicator f y) W C' T N) :=
  exists_dense_slice_all r ρ η hρ hρ1 hconstants f
    (hagreement.trans (nonzeroAgreement_le_all f))

end
end PerfectCompleteness.PartialTableInverse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixErasure
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixErasure

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open PerfectCompleteness.PartialTableInverse

variable {Ω Y : Type*}

theorem indicator_erase_le (f : Ω → Option Y) (T : Ω → Prop) (y : Y) (X : Ω) :
    indicator (erase f T) y X ≤ indicator f y X := by
  by_cases hX : T X
  · simp only [indicator, erase, ite_eq_left hX, reduceCtorEq, ite_false, if_false]
    split_ifs <;> norm_num
  · simp [indicator, erase, hX]

theorem definedEquality_erase (f : Ω → Option Y) (T : Ω → Prop) (X X' : Ω) :
    definedEquality (erase f T) X X' =
      if T X ∨ T X' then 0 else definedEquality f X X' := by
  by_cases hX : T X <;> by_cases hX' : T X' <;>
    simp [definedEquality, erase, hX, hX']

theorem definedEquality_le_one (f : Ω → Option Y) (X X' : Ω) :
    definedEquality f X X' ≤ 1 := by
  unfold definedEquality
  split_ifs <;> norm_num

theorem definedEquality_le_erase_add (f : Ω → Option Y) (T : Ω → Prop) (X X' : Ω) :
    definedEquality f X X' ≤ definedEquality (erase f T) X X' +
      (if T X then (1 : ℝ) else 0) + (if T X' then (1 : ℝ) else 0) := by
  have hbound := definedEquality_le_one f X X'
  by_cases hX : T X <;> by_cases hX' : T X' <;>
    simp [definedEquality_erase, hX, hX'] <;> linarith

theorem expect_add_right [AddGroup Ω] [Fintype Ω] (g : Ω → ℝ) (v : Ω) :
    (𝔼 X, g (X + v)) = (𝔼 X, g X) :=
  Fintype.expect_equiv (Equiv.addRight v) _ _ (fun _ => rfl)

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [Fintype F] [Fintype (E →ₗ[F2] F2)] [Fintype (E →ₗ[F2] F)]

omit [Fintype F] in
theorem step_second_marginal (g : (E →ₗ[F2] F) → ℝ) (a : F) :
    (𝔼 X, 𝔼 h : E →ₗ[F2] F2, g (X + h.smulRight a)) = (𝔼 X, g X) := by
  rw [Finset.expect_comm]
  simp_rw [expect_add_right]
  exact Fintype.expect_const _

omit [Fintype F] in
theorem stepAgreement_erase_bound (f : (E →ₗ[F2] F) → Option Y)
    (T : (E →ₗ[F2] F) → Prop) (a : F) :
    stepAgreement f a ≤ stepAgreement (erase f T) a + 2 * uniformMass T := by
  have havg : stepAgreement f a ≤
      𝔼 X, 𝔼 h : E →ₗ[F2] F2,
        (definedEquality (erase f T) X (X + h.smulRight a) +
          (if T X then (1 : ℝ) else 0) +
          (if T (X + h.smulRight a) then (1 : ℝ) else 0)) := by
    apply Finset.expect_le_expect
    intro X _
    apply Finset.expect_le_expect
    intro h _
    exact definedEquality_le_erase_add f T X (X + h.smulRight a)
  simp_rw [Finset.expect_add_distrib, Fintype.expect_const] at havg
  rw [step_second_marginal (fun X => if T X then (1 : ℝ) else 0) a] at havg
  change stepAgreement f a ≤
    stepAgreement (erase f T) a + uniformMass T + uniformMass T at havg
  linarith

theorem nonzeroAgreement_erase [Nontrivial F] (f : (E →ₗ[F2] F) → Option Y)
    (T : (E →ₗ[F2] F) → Prop) :
    nonzeroAgreement f - 2 * uniformMass T ≤ nonzeroAgreement (erase f T) := by
  obtain ⟨a, ha⟩ := exists_ne (0 : F)
  let : Nonempty {a : F // a ≠ 0} := ⟨⟨a, ha⟩⟩
  have havg : nonzeroAgreement f ≤
      𝔼 a : {a : F // a ≠ 0}, (stepAgreement (erase f T) a.val + 2 * uniformMass T) := by
    unfold nonzeroAgreement
    apply Finset.expect_le_expect
    intro a _
    exact stepAgreement_erase_bound f T a.val
  simp only [Finset.expect_add_distrib, Fintype.expect_const] at havg
  change nonzeroAgreement f ≤ nonzeroAgreement (erase f T) + 2 * uniformMass T at havg
  linarith

end
end PerfectCompleteness.MatrixErasure

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

theorem probability_inter_eq_mul_conditional (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given) :
    μ.probability (fun x => given x && event x) =
      μ.probability given * (μ.condition given positive).probability event := by
  have h := (eq_div_iff (ne_of_gt positive)).mp
    (μ.probability_condition given event positive)
  simpa only [mul_comm] using h.symm

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RecursiveSpaceEquivLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.RowAdvice

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

theorem pad_injective {d r : Nat} (h : d ≤ r) : Function.Injective (pad h) := by
  intro v w hvw
  funext i
  have hi := congrFun hvw (⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩ : Fin r)
  simpa only [pad_low] using hi

variable {E C R : Type*}
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

theorem paddedRowMap_apply_eq_iff [FiniteDimensional F2 C]
    (r : Nat) (C' : Submodule F2 C) (h : Module.finrank F2 (C ⧸ C') ≤ r)
    (x y : C) :
    paddedRowMap r C' h x = paddedRowMap r C' h y ↔ C'.mkQ x = C'.mkQ y := by
  constructor
  · intro hxy
    apply (Module.finBasis F2 (C ⧸ C')).equivFun.injective
    exact pad_injective h hxy
  · intro hxy
    change pad h ((Module.finBasis F2 (C ⧸ C')).equivFun (C'.mkQ x)) =
      pad h ((Module.finBasis F2 (C ⧸ C')).equivFun (C'.mkQ y))
    rw [hxy]

theorem ker_paddedRowMap [FiniteDimensional F2 C]
    (r : Nat) (C' : Submodule F2 C) (h : Module.finrank F2 (C ⧸ C') ≤ r) :
    LinearMap.ker (paddedRowMap r C' h) = C' := by
  ext x
  change paddedRowMap r C' h x = 0 ↔ x ∈ C'
  calc
    paddedRowMap r C' h x = 0 ↔
        paddedRowMap r C' h x = paddedRowMap r C' h 0 := by rw [map_zero]
    _ ↔ C'.mkQ x = C'.mkQ 0 := paddedRowMap_apply_eq_iff r C' h x 0
    _ ↔ x ∈ C' := by
      rw [map_zero]
      exact Submodule.Quotient.mk_eq_zero C'

theorem card_rowMaps [FiniteDimensional F2 C] (r : Nat)
    [Fintype (C →ₗ[F2] (Fin r → F2))] :
    Fintype.card (C →ₗ[F2] (Fin r → F2)) = 2 ^ (r * Module.finrank F2 C) := by
  simpa only [Module.finrank_fin_fun, Nat.mul_comm] using
    (UniqueGamesTheorem.Fourier.MatrixParity.card_linearMaps (C := C) (E := Fin r → F2))

end
end PerfectCompleteness.RowAdvice

end

section

namespace PerfectCompleteness.SliceMass

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions (Parameter)
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.MatrixSlice

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

section Finite

variable [Finite E] [Finite C]
  [FiniteDimensional F2 E] [FiniteDimensional F2 C]

theorem card_slice (W : Submodule F2 E) (C' : Submodule F2 C)
    (T : E →ₗ[F2] C) :
    Fintype.card (Slice W C' T) =
      2 ^ (Module.finrank F2 (E ⧸ W) * Module.finrank F2 C') := by
  rw [← Fintype.card_congr (parameterEquivSlice W C' T)]
  rw [Module.card_eq_pow_finrank (K := F2) (V := Parameter W C')]
  rw [show Fintype.card F2 = 2 by decide]
  change 2 ^ Module.finrank F2 ((E ⧸ W) →ₗ[F2] C') = _
  rw [Module.finrank_linearMap]

theorem card_rowFiber (C' : Submodule F2 C) (T : E →ₗ[F2] C) :
    Fintype.card (Slice (⊥ : Submodule F2 E) C' T) =
      2 ^ (Module.finrank F2 E * Module.finrank F2 C') := by
  rw [card_slice]
  have hdim := (⊥ : Submodule F2 E).finrank_quotient_add_finrank
  simp only [finrank_bot, add_zero] at hdim
  rw [hdim]

theorem card_rowFiber_eq_card_slice_mul (W : Submodule F2 E)
    (C' : Submodule F2 C) (T : E →ₗ[F2] C) :
    Fintype.card (Slice (⊥ : Submodule F2 E) C' T) =
      Fintype.card (Slice W C' T) *
        2 ^ (Module.finrank F2 W * Module.finrank F2 C') := by
  rw [card_rowFiber, card_slice, ← pow_add, ← Nat.add_mul,
    W.finrank_quotient_add_finrank]

theorem card_ratio (W : Submodule F2 E) (C' : Submodule F2 C)
    (T : E →ₗ[F2] C) :
    (Fintype.card (Slice W C' T) : ℝ) /
        Fintype.card (Slice (⊥ : Submodule F2 E) C' T) =
      1 / (2 : ℝ) ^ (Module.finrank F2 W * Module.finrank F2 C') := by
  rw [card_rowFiber_eq_card_slice_mul W C' T, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  have hcard : (Fintype.card (Slice W C' T) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [div_mul_eq_div_div, div_self hcard]

theorem probability_columnConstraint (W : Submodule F2 E)
    (C' : Submodule F2 C) (T : E →ₗ[F2] C) :
    (FiniteDistribution.uniform (Slice (⊥ : Submodule F2 E) C' T)).probability
        (fun X => decide (X.val.domRestrict W = T.domRestrict W)) =
      1 / (2 : ℝ) ^ (Module.finrank F2 W * Module.finrank F2 C') := by
  let event : Slice (⊥ : Submodule F2 E) C' T → Prop :=
    fun X => X.val.domRestrict W = T.domRestrict W
  calc
    _ = (FiniteDistribution.uniform (Slice (⊥ : Submodule F2 E) C' T)).expectation
        (fun X => if event X then (1 : ℝ) else 0) := by
      unfold FiniteDistribution.probability FiniteDistribution.expectation
      apply Finset.sum_congr rfl
      intro X _
      by_cases hX : event X <;> simp [event] at hX ⊢
    _ = (∑ X, if event X then (1 : ℝ) else 0) /
        (Fintype.card (Slice (⊥ : Submodule F2 E) C' T) : ℝ) :=
      FiniteDistribution.expectation_uniform _
    _ = (Fintype.card {X // event X} : ℝ) /
        (Fintype.card (Slice (⊥ : Submodule F2 E) C' T) : ℝ) := by
      simp only [Fintype.card_subtype, Finset.sum_boole]
    _ = (Fintype.card (Slice W C' T) : ℝ) /
        (Fintype.card (Slice (⊥ : Submodule F2 E) C' T) : ℝ) := by
      rw [Fintype.card_congr (columnEventEquivSlice W C' T)]
    _ = _ := card_ratio W C' T

theorem probability_columnConstraint_ge (W : Submodule F2 E)
    (C' : Submodule F2 C) (T : E →ₗ[F2] C) :
    1 / (2 : ℝ) ^ (Module.finrank F2 W * Module.finrank F2 C) ≤
      (FiniteDistribution.uniform (Slice (⊥ : Submodule F2 E) C' T)).probability
        (fun X => decide (X.val.domRestrict W = T.domRestrict W)) := by
  rw [probability_columnConstraint]
  apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
  exact pow_le_pow_right₀ (by norm_num)
    (Nat.mul_le_mul_left _ C'.finrank_le)

theorem probability_columnConstraint_ge_of_finrank_le
    (W : Submodule F2 E) (C' : Submodule F2 C) (T : E →ₗ[F2] C)
    (r : Nat) (hW : Module.finrank F2 W ≤ r) :
    1 / (2 : ℝ) ^ (r * Module.finrank F2 C) ≤
      (FiniteDistribution.uniform (Slice (⊥ : Submodule F2 E) C' T)).probability
        (fun X => decide (X.val.domRestrict W = T.domRestrict W)) := by
  apply le_trans _ (probability_columnConstraint_ge W C' T)
  apply one_div_le_one_div_of_le (pow_pos (by norm_num) _)
  exact pow_le_pow_right₀ (by norm_num)
    (Nat.mul_le_mul_right _ hW)

end Finite
end
end PerfectCompleteness.SliceMass

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ManyGoodRowsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ManyGoodRows

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open PerfectCompleteness.PartialTableInverse PerfectCompleteness.MatrixErasure

attribute [local instance] linearMapFintype

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem GoodRow.mono {f g : (E →ₗ[F2] F) → Option Y} {r : Nat} {ρ : ℝ}
    {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}
    (h : GoodRow f r ρ A U)
    (hfg : ∀ y X, indicator f y X ≤ indicator g y X) : GoodRow g r ρ A U := by
  obtain ⟨W, T, y, hW, hU, hdensity⟩ := h
  refine ⟨W, T, y, hW, hU, hdensity.trans ?_⟩
  exact Finset.expect_le_expect fun X _ => hfg y X.val

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem isGoodPoint_of_witness {f : (E →ₗ[F2] F) → Option Y} {r : Nat} {ρ : ℝ}
    {W : Submodule F2 E} {A : RowMap F r} {T : E →ₗ[F2] F}
    (hgood : GoodRow f r ρ A (A.comp T))
    (X : MatrixSlice.Slice W (LinearMap.ker A) T) : IsGoodPoint f r ρ X.val := by
  refine ⟨A, ?_⟩
  rw [RowAdvice.slice_row_eq W A T X]
  exact hgood

omit [FiniteDimensional F2 E] [Fintype Y] in
theorem dense_restriction_rowMap (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ)
    (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F)
    (horder : order W C' ≤ r)
    (hdensity : ρ < (𝔼 N, restrict (indicator f y) W C' T N)) :
    ∃ A : RowMap F r,
      Module.finrank F2 W ≤ r ∧
      ρ < (𝔼 X : MatrixSlice.Slice W (LinearMap.ker A) T, indicator f y X.val) := by
  let hcodim := (MatrixSlice.row_count_le_order W C').trans horder
  let A := RowAdvice.paddedRowMap r C' hcodim
  have hker : LinearMap.ker A = C' := RowAdvice.ker_paddedRowMap r C' hcodim
  refine ⟨A, (MatrixSlice.column_count_le_order W C').trans horder, ?_⟩
  rw [hker]
  rwa [MatrixSlice.expect_restrict_eq_slice] at hdensity

theorem goodMass_ge [Nontrivial F]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (f : (E →ₗ[F2] F) → Option Y) (hagreement : η ≤ nonzeroAgreement f) :
    η / 4 ≤ goodMass f r ρ := by
  by_contra hsmall
  have hsmall' : goodMass f r ρ < η / 4 := lt_of_not_ge hsmall
  let erased := erase f (IsGoodPoint f r ρ)
  have herasure := nonzeroAgreement_erase f (IsGoodPoint f r ρ)
  have hremaining : η / 2 ≤ nonzeroAgreement erased := by
    change nonzeroAgreement f - 2 * goodMass f r ρ ≤ nonzeroAgreement erased at herasure
    linarith
  obtain ⟨y, W, C', T, horder, hdense⟩ :=
    exists_dense_slice_nonzero r ρ (η / 2) hρ hρ1 hconstants erased hremaining
  obtain ⟨A, hW, hdense'⟩ := dense_restriction_rowMap erased r ρ y W C' T horder hdense
  have hgoodErased : GoodRow erased r ρ A (A.comp T) :=
    ⟨W, T, y, hW, rfl, hdense'.le⟩
  have hgood : GoodRow f r ρ A (A.comp T) :=
    GoodRow.mono hgoodErased (indicator_erase_le f (IsGoodPoint f r ρ))
  have hzero : (𝔼 X : MatrixSlice.Slice W (LinearMap.ker A) T,
      indicator erased y X.val) = 0 := by
    apply Finset.expect_eq_zero
    intro X _
    have hX : IsGoodPoint f r ρ X.val := isGoodPoint_of_witness hgood X
    simp [indicator, erased, erase_eq_none_of f (IsGoodPoint f r ρ) hX]
  rw [hzero] at hdense'
  exact (not_lt_of_ge hρ.le) hdense'

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem goodMass_le_card_mul_adviceMass
    (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) :
    goodMass f r ρ ≤ (Fintype.card (RowMap F r) : ℝ) * adviceMass f r ρ := by
  unfold goodMass uniformMass adviceMass
  rw [Fintype.card_mul_expect, ← Finset.expect_sum_comm]
  apply Finset.expect_le_expect
  intro X _
  by_cases hX : IsGoodPoint f r ρ X
  · rw [ite_eq_left hX]
    obtain ⟨A, hA⟩ := hX
    calc
      (1 : ℝ) = (if GoodRow f r ρ A (A.comp X) then 1 else 0) := by rw [ite_eq_left hA]
      _ ≤ ∑ B : RowMap F r, if GoodRow f r ρ B (B.comp X) then (1 : ℝ) else 0 := by
        apply Finset.single_le_sum
          (f := fun B : RowMap F r =>
            if GoodRow f r ρ B (B.comp X) then (1 : ℝ) else 0)
          (s := Finset.univ) (a := A)
        · intro B _
          split_ifs <;> norm_num
        · exact Finset.mem_univ A
  · rw [ite_eq_right hX]
    apply Finset.sum_nonneg
    intro A _
    split_ifs <;> norm_num

theorem adviceMass_ge [Nontrivial F]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (f : (E →ₗ[F2] F) → Option Y) (hagreement : η ≤ nonzeroAgreement f) :
    (η / 4) / (2 : ℝ) ^ (r * Module.finrank F2 F) ≤ adviceMass f r ρ := by
  have hmass := (goodMass_ge r ρ η hρ hρ1 hconstants f hagreement).trans
    (goodMass_le_card_mul_adviceMass f r ρ)
  have hcard : (Fintype.card (RowMap F r) : ℝ) =
      (2 : ℝ) ^ (r * Module.finrank F2 F) := by
    exact_mod_cast RowAdvice.card_rowMaps (C := F) r
  rw [hcard] at hmass
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  simpa only [mul_comm] using hmass

end
end PerfectCompleteness.ManyGoodRows



namespace PerfectCompleteness.FamilyGoodRows

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open PerfectCompleteness.PartialTableInverse PerfectCompleteness.MatrixErasure
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {P : Type*} [Fintype P]

theorem expectation_le_threshold_add_probability (μ : FiniteDistribution P)
    (g : P → ℝ) (η : ℝ) (hη : 0 ≤ η) (hg : ∀ p, g p ≤ 1) :
    μ.expectation g ≤ η + μ.probability (fun p => decide (η ≤ g p)) := by
  have hpoint : ∀ p, g p ≤ η + (if η ≤ g p then (1 : ℝ) else 0) := by
    intro p
    by_cases hp : η ≤ g p
    · rw [ite_eq_left hp]
      linarith [hg p]
    · rw [ite_eq_right hp, add_zero]
      exact (lt_of_not_ge hp).le
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) =>
    mul_le_mul_of_nonneg_left (hpoint p) (μ.nonnegative p))
  simpa only [FiniteDistribution.expectation, FiniteDistribution.probability,
    mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    ← Finset.sum_mul, μ.normalized, one_mul, decide_eq_true_eq] using hsum

theorem threshold_probability_ge (μ : FiniteDistribution P) (g : P → ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hg : ∀ p, g p ≤ 1)
    (hmean : 2 * η ≤ μ.expectation g) :
    η ≤ μ.probability (fun p => decide (η ≤ g p)) := by
  have h := expectation_le_threshold_add_probability μ g η hη hg
  linarith

theorem probability_mul_le_expectation (μ : FiniteDistribution P)
    (S : P → Prop) (g : P → ℝ) (c : ℝ)
    (hnonneg : ∀ p, 0 ≤ g p) (hgood : ∀ p, S p → c ≤ g p) :
    μ.probability (fun p => decide (S p)) * c ≤ μ.expectation g := by
  calc
    _ = μ.expectation (fun p => if S p then c else 0) := by
      simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
        decide_eq_true_eq, Finset.sum_mul, ite_mul, mul_ite, zero_mul, mul_zero]
    _ ≤ μ.expectation g := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (μ.nonnegative p)
      by_cases hp : S p
      · simpa only [ite_eq_left hp] using hgood p hp
      · simpa only [ite_eq_right hp] using hnonneg p

section TableBounds

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem nonzeroAgreement_le_one [Nontrivial F]
    (f : (E →ₗ[F2] F) → Option Y) : nonzeroAgreement f ≤ 1 := by
  obtain ⟨a, ha⟩ := exists_ne (0 : F)
  let : Nonempty {a : F // a ≠ 0} := ⟨⟨a, ha⟩⟩
  unfold nonzeroAgreement stepAgreement
  apply Finset.expect_le Finset.univ_nonempty
  intro a _
  apply Finset.expect_le Finset.univ_nonempty
  intro X _
  apply Finset.expect_le Finset.univ_nonempty
  intro h _
  exact definedEquality_le_one f X (X + h.smulRight a.val)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem adviceMass_nonneg (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) :
    0 ≤ adviceMass f r ρ := by
  unfold adviceMass
  apply Finset.expect_nonneg
  intro A _
  apply Finset.expect_nonneg
  intro X _
  split_ifs <;> norm_num

end TableBounds


end
end PerfectCompleteness.FamilyGoodRows



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_TupleIndexEmitterLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.UsefulMark

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω P : Type*} [Fintype Ω] [Fintype P]

theorem probability_eq_sum_fibers (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : Ω → Bool) : μ.probability event = ∑ z, lowerFiberMass μ p event z := by
  unfold lowerFiberMass FiniteDistribution.probability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases he : event x <;> simp [he, eq_comm]

end
end PerfectCompleteness.UsefulMark



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerReplayTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UniformConditioning

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [Nonempty Ω] [Nonempty Γ]

theorem uniform_transport (e : Ω ≃ Γ) :
    (FiniteDistribution.uniform Ω).transport e = FiniteDistribution.uniform Γ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change 1 / (Fintype.card Ω : ℝ) = 1 / (Fintype.card Γ : ℝ)
  rw [Fintype.card_congr e]

theorem uniform_probability_equiv (e : Ω ≃ Γ) (event : Γ → Bool) :
    (FiniteDistribution.uniform Ω).probability (fun x => event (e x)) =
      (FiniteDistribution.uniform Γ).probability event := by
  rw [← uniform_transport e, FiniteDistribution.probability_transport]

theorem uniform_probability (T : Ω → Prop) :
    (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)) =
      (Fintype.card {x : Ω // T x} : ℝ) / (Fintype.card Ω : ℝ) := by
  calc
    _ = (∑ x : Ω, if T x then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) := by
      change (∑ x : Ω, if decide (T x) then 1 / (Fintype.card Ω : ℝ) else 0) = _
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : T x <;> simp [hx]
    _ = _ := by simp only [Fintype.card_subtype, Finset.sum_boole]

theorem uniform_probability_pos (T : Ω → Prop) [Nonempty {x : Ω // T x}] :
    0 < (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)) := by
  rw [uniform_probability]
  exact div_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)

omit [Nonempty Ω] in
theorem uniform_subtype_pushforward_weight (T : Ω → Prop)
    [Nonempty {x : Ω // T x}] (x : Ω) :
    ((FiniteDistribution.uniform {x : Ω // T x}).pushforward Subtype.val).weight x =
      if T x then 1 / (Fintype.card {x : Ω // T x} : ℝ) else 0 := by
  change (∑ y : {x : Ω // T x},
    if y.val = x then 1 / (Fintype.card {x : Ω // T x} : ℝ) else 0) = _
  by_cases hx : T x
  · rw [ite_eq_left hx]
    rw [Finset.sum_eq_single (⟨x, hx⟩ : {x : Ω // T x})]
    · simp
    · intro y _ hy
      have hne : y.val ≠ x := fun heq => hy (Subtype.ext heq)
      simp [hne]
    · simp
  · rw [ite_eq_right hx]
    apply Finset.sum_eq_zero
    intro y _
    have hne : y.val ≠ x := fun heq => hx (heq ▸ y.property)
    simp [hne]

theorem condition_uniform (T : Ω → Prop) [Nonempty {x : Ω // T x}]
    (positive : 0 < (FiniteDistribution.uniform Ω).probability (fun x => decide (T x))) :
    (FiniteDistribution.uniform Ω).condition (fun x => decide (T x)) positive =
      (FiniteDistribution.uniform {x : Ω // T x}).pushforward Subtype.val := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  rw [uniform_subtype_pushforward_weight]
  change (if decide (T x) then
    (1 / (Fintype.card Ω : ℝ)) /
      (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)) else 0) = _
  rw [uniform_probability]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hx : T x
  · simpa [hx] using
      div_div_div_cancel_right₀ hcard (1 : ℝ) (Fintype.card {x : Ω // T x} : ℝ)
  · simp [hx]

theorem probability_condition_uniform (T : Ω → Prop) [Nonempty {x : Ω // T x}]
    (positive : 0 < (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)))
    (event : Ω → Bool) :
    ((FiniteDistribution.uniform Ω).condition (fun x => decide (T x)) positive).probability
        event =
      (FiniteDistribution.uniform {x : Ω // T x}).probability (fun x => event x.val) := by
  rw [condition_uniform, FiniteDistribution.probability_pushforward]

end
end PerfectCompleteness.UniformConditioning

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_GoodRowSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.GoodRowSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

omit [Fintype Y] in
theorem witness_column_probability {f : (E →ₗ[F2] F) → Option Y}
    {r : Nat} {ρ : ℝ} {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}
    (w : Witness f r ρ A U) :
    letI : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
    1 / (2 : ℝ) ^ (r * Module.finrank F2 F) ≤
      (FiniteDistribution.uniform (RowFiber A U)).probability
        (fun X => decide (X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace)) := by
  let : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
  have h := SliceMass.probability_columnConstraint_ge_of_finrank_le
    w.columnSpace (LinearMap.ker A) w.base r w.column_count
  have he := UniformConditioning.uniform_probability_equiv
    (rowFiberEquiv A U w.base w.row_value)
    (fun X : RowFiber A U =>
      decide (X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace))
  apply h.trans_eq
  refine Eq.trans ?_ he
  congr 1
  funext X
  exact decide_eq_decide.mpr Iff.rfl

end
end PerfectCompleteness.GoodRowSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GoodAdviceEventsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.GoodAdviceEvents

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open PerfectCompleteness.ManyGoodRows PerfectCompleteness.GoodRowSampling

attribute [local instance] linearMapFintype

section FiniteLaws

variable {Ω P : Type*} [Fintype Ω] [Fintype P] [Nonempty Ω]

omit [Fintype P] [Nonempty Ω] in
theorem adapted_fiber_probability (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : P → Ω → Bool) (z : P) :
    UsefulMark.lowerFiberMass μ p (fun x => event (p x) x) z =
      μ.probability (fun x => decide (p x = z) && event z x) := by
  unfold UsefulMark.lowerFiberMass
  congr 1
  funext x
  by_cases hx : p x = z <;> simp [hx]

omit [Fintype P] in
theorem adapted_uniform_fiber_probability (p : Ω → P)
    (event : P → Ω → Bool) (z : P) [Nonempty {x : Ω // p x = z}] :
    UsefulMark.lowerFiberMass (FiniteDistribution.uniform Ω) p
        (fun x => event (p x) x) z =
      (FiniteDistribution.uniform Ω).probability (fun x => decide (p x = z)) *
        (FiniteDistribution.uniform {x : Ω // p x = z}).probability
          (fun x => event z x.val) := by
  rw [adapted_fiber_probability]
  rw [FiniteDistribution.probability_inter_eq_mul_conditional _ _ _
    (UniformConditioning.uniform_probability_pos (fun x => p x = z))]
  rw [UniformConditioning.probability_condition_uniform]

omit [Fintype P] [Nonempty Ω] in
theorem adapted_fiber_probability_zero (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : P → Ω → Bool) (z : P) (h : ∀ x, event z x = false) :
    UsefulMark.lowerFiberMass μ p (fun x => event (p x) x) z = 0 := by
  rw [adapted_fiber_probability]
  simp only [h, Bool.and_false, FiniteDistribution.probability_false]

theorem uniform_probability_eq_expect (event : Ω → Bool) :
    (FiniteDistribution.uniform Ω).probability event =
      𝔼 x : Ω, if event x then (1 : ℝ) else 0 := by
  have h : (FiniteDistribution.uniform Ω).probability event =
      (FiniteDistribution.uniform Ω).expectation
        (fun x => if event x then (1 : ℝ) else 0) := by
    simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
      mul_ite, mul_one, mul_zero]
  rw [h, FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

omit [Nonempty Ω] in
theorem product_probability {Γ : Type*} [Fintype Γ]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) (event : Ω × Γ → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun x => ν.probability (fun y => event (x, y))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

end FiniteLaws

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

omit [Fintype Y] in
theorem J_probability_fixed_row (f : (E →ₗ[F2] F) → Option Y)
    (r : Nat) (ρ : ℝ) (A : RowMap F r) :
    (1 / (2 : ℝ) ^ (r * Module.finrank F2 F)) *
        (FiniteDistribution.uniform (E →ₗ[F2] F)).probability
          (fun X => decide (GoodRow f r ρ A (A.comp X))) ≤
      (FiniteDistribution.uniform (E →ₗ[F2] F)).probability
        (fun X => J f r ρ (A, X)) := by
  let μ := FiniteDistribution.uniform (E →ₗ[F2] F)
  let p : (E →ₗ[F2] F) → (E →ₗ[F2] (Fin r → F2)) := fun X => A.comp X
  rw [UsefulMark.probability_eq_sum_fibers μ p,
    UsefulMark.probability_eq_sum_fibers μ p, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro U _
  by_cases hgood : GoodRow f r ρ A U
  · let w := selectWitness f r ρ A U hgood
    let : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
    have hG : UsefulMark.lowerFiberMass μ p
        (fun X => decide (GoodRow f r ρ A (A.comp X))) U =
        μ.probability (fun X => @decide (A.comp X = U) (Classical.propDecidable _)) := by
      rw [adapted_fiber_probability μ p
        (fun V _X => decide (GoodRow f r ρ A V)) U]
      simp only [hgood, decide_true, Bool.and_true]
      rfl
    have hJ : UsefulMark.lowerFiberMass μ p (fun X => J f r ρ (A, X)) U =
        μ.probability (fun X => @decide (A.comp X = U) (Classical.propDecidable _)) *
          (FiniteDistribution.uniform (RowFiber A U)).probability
            (fun X => decide (X.val.domRestrict w.columnSpace =
              w.base.domRestrict w.columnSpace)) := by
      change UsefulMark.lowerFiberMass (FiniteDistribution.uniform (E →ₗ[F2] F)) p
        (fun X => selectedColumn f r ρ A (p X) X) U = _
      refine (adapted_uniform_fiber_probability p (selectedColumn f r ρ A) U).trans ?_
      simp only [selectedColumn, dite_eq_left hgood]
      congr!
    rw [hG, hJ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (witness_column_probability w) (μ.probability_nonnegative _)
  · have hG : UsefulMark.lowerFiberMass μ p
        (fun X => decide (GoodRow f r ρ A (A.comp X))) U = 0 :=
      adapted_fiber_probability_zero μ p
        (fun V _X => decide (GoodRow f r ρ A V)) U (by intro X; simp [hgood])
    rw [hG, mul_zero]
    exact μ.probability_nonnegative _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem good_probability_eq_adviceMass (f : (E →ₗ[F2] F) → Option Y)
    (r : Nat) (ρ : ℝ) :
    (law E F r).probability
        (fun s => decide (GoodRow f r ρ s.1 (s.1.comp s.2))) = adviceMass f r ρ := by
  simp only [law, product_probability, uniform_probability_eq_expect,
    FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card,
    adviceMass, decide_eq_true_eq]

omit [Fintype Y] in
theorem J_probability_ge (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) :
    adviceMass f r ρ / (2 : ℝ) ^ (r * Module.finrank F2 F) ≤
      (law E F r).probability (J f r ρ) := by
  calc
    _ = (1 / (2 : ℝ) ^ (r * Module.finrank F2 F)) *
        (law E F r).probability
          (fun s => decide (GoodRow f r ρ s.1 (s.1.comp s.2))) := by
      rw [good_probability_eq_adviceMass]
      ring
    _ ≤ _ := by
      simp only [law, product_probability, FiniteDistribution.expectation, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro A _
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
        (J_probability_fixed_row f r ρ A)
        ((FiniteDistribution.uniform (RowMap F r)).nonnegative A)

end
end PerfectCompleteness.GoodAdviceEvents



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HeterogeneousAdviceFamily
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HeterogeneousAdviceFamily

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {P : Type*} [Fintype P] {E F Y : P → Type*}
  [∀ p, AddCommGroup (E p)] [∀ p, Module F2 (E p)]
  [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module F2 (F p)]
  [∀ p, FiniteDimensional F2 (F p)] [∀ p, Fintype (F p)]
  [∀ p, Fintype (Y p)]

omit [∀ p, FiniteDimensional F2 (E p)] [∀ p, FiniteDimensional F2 (F p)]
  [∀ p, Fintype (Y p)] in
theorem J_probability_eq_mean (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    (law (E := E) (F := F) μ r).probability (J f r ρ) =
      μ.expectation (fun p =>
        (GoodAdviceEvents.law (E p) (F p) r).probability (GoodAdviceEvents.J (f p) r ρ)) :=
  CompletionSoundness.sigmaLaw_probability μ
    (fun p => GoodAdviceEvents.law (E p) (F p) r) (J f r ρ)

private theorem div_pow_le {a : ℝ} (ha : 0 ≤ a) {i j : Nat} (hij : i ≤ j) :
    a / (2 : ℝ) ^ j ≤ a / (2 : ℝ) ^ i := by
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left
      (one_div_pow_le_one_div_pow_of_le (by norm_num : (1 : ℝ) ≤ 2) hij) ha

omit [∀ p, Fintype (Y p)] in
theorem J_probability_ge_mean_advice (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r ℓ : Nat)
    (hdim : ∀ p, Module.finrank F2 (F p) ≤ ℓ) (ρ : ℝ) :
    μ.expectation (fun p => adviceMass (f p) r ρ) / (2 : ℝ) ^ (r * ℓ) ≤
      (law (E := E) (F := F) μ r).probability (J f r ρ) := by
  have hpoint (p : P) :
      adviceMass (f p) r ρ / (2 : ℝ) ^ (r * ℓ) ≤
        (GoodAdviceEvents.law (E p) (F p) r).probability (GoodAdviceEvents.J (f p) r ρ) :=
    (div_pow_le (FamilyGoodRows.adviceMass_nonneg (f p) r ρ)
      (Nat.mul_le_mul_left r (hdim p))).trans (GoodAdviceEvents.J_probability_ge (f p) r ρ)
  rw [J_probability_eq_mean]
  simp only [FiniteDistribution.expectation, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  simpa only [div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left (hpoint p) (μ.nonnegative p)

variable [∀ p, Nontrivial (F p)]

theorem mean_adviceMass_ge (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r ℓ : Nat)
    (hdim : ∀ p, Module.finrank F2 (F p) ≤ ℓ)
    (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ μ.expectation (fun p => PartialTableInverse.nonzeroAgreement (f p))) :
    (η ^ 2 / 4) / (2 : ℝ) ^ (r * ℓ) ≤
      μ.expectation (fun p => adviceMass (f p) r ρ) := by
  let c : ℝ := (η / 4) / (2 : ℝ) ^ (r * ℓ)
  have hc : 0 ≤ c :=
    div_nonneg (div_nonneg hη.le (by norm_num : (0 : ℝ) ≤ 4)) (by positivity)
  have hmass : η ≤ μ.probability
      (fun p => decide (η ≤ PartialTableInverse.nonzeroAgreement (f p))) :=
    FamilyGoodRows.threshold_probability_ge μ
      (fun p => PartialTableInverse.nonzeroAgreement (f p)) η hη.le
      (fun p => FamilyGoodRows.nonzeroAgreement_le_one (f p)) hmean
  have hweighted :
      μ.probability (fun p => decide (η ≤ PartialTableInverse.nonzeroAgreement (f p))) * c ≤
        μ.expectation (fun p => adviceMass (f p) r ρ) := by
    apply FamilyGoodRows.probability_mul_le_expectation μ
      (fun p => η ≤ PartialTableInverse.nonzeroAgreement (f p))
      (fun p => adviceMass (f p) r ρ) c
    · intro p
      exact FamilyGoodRows.adviceMass_nonneg (f p) r ρ
    · intro p hp
      exact (div_pow_le (div_nonneg hη.le (by norm_num : (0 : ℝ) ≤ 4))
        (Nat.mul_le_mul_left r (hdim p))).trans
          (ManyGoodRows.adviceMass_ge r ρ η hρ hρ1 hconstants (f p) hp)
  calc
    (η ^ 2 / 4) / (2 : ℝ) ^ (r * ℓ) = η * c := by
      dsimp [c]
      ring
    _ ≤ μ.probability (fun p => decide (η ≤ PartialTableInverse.nonzeroAgreement (f p))) * c :=
      mul_le_mul_of_nonneg_right hmass hc
    _ ≤ μ.expectation (fun p => adviceMass (f p) r ρ) := hweighted

theorem J_probability_ge_oai (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r ℓ : Nat)
    (hdim : ∀ p, Module.finrank F2 (F p) ≤ ℓ)
    (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ μ.expectation (fun p => PartialTableInverse.nonzeroAgreement (f p))) :
    (η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2 ≤
      (law (E := E) (F := F) μ r).probability (J f r ρ) := by
  calc
    _ = ((η ^ 2 / 4) / (2 : ℝ) ^ (r * ℓ)) / (2 : ℝ) ^ (r * ℓ) := by ring
    _ ≤ μ.expectation (fun p => adviceMass (f p) r ρ) / (2 : ℝ) ^ (r * ℓ) :=
      div_le_div_of_nonneg_right
        (mean_adviceMass_ge μ f r ℓ hdim ρ η hη hρ hρ1 hconstants hmean) (by positivity)
    _ ≤ _ := J_probability_ge_mean_advice μ f r ℓ hdim ρ

end
end PerfectCompleteness.HeterogeneousAdviceFamily

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge_oai.{u_1, u_2, u_3, u_4} := @OAI.PerfectCompleteness.HeterogeneousAdviceFamily.J_probability_ge_oai.{u_1, u_2, u_3, u_4}
