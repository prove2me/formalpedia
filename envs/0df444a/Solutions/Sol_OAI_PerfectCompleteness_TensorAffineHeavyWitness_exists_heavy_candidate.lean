-- Prove2me | solution 1 for OAI.PerfectCompleteness.TensorAffineHeavyWitness.exists_heavy_candidate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:16:23.75097+00:00
-- url     : https://prove2.me/submissions/b95f57e8-0e68-4af2-a6dd-72a0c7798296

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
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
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
import Mathlib.LinearAlgebra.TensorProduct.Associator
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
import Definitions.Def_OAIQ252P015

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BilinearGramCompressionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TensorCosetEvaluation

noncomputable section

open scoped TensorProduct

section GeneralField

variable {𝕜 U H : Type*} [Field 𝕜]
  [AddCommGroup U] [Module 𝕜 U] [AddCommGroup H] [Module 𝕜 H]

theorem scalarRestriction_mem_of_vanishes
    (Q : Submodule 𝕜 (Module.Dual 𝕜 H)) [FiniteDimensional 𝕜 Q]
    (Ψ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (hΨ : ∀ u h, h ∈ Q.dualCoannihilator → Ψ (u ⊗ₜ[𝕜] h) = 0) (u : U) :
    scalarRestriction Ψ u ∈ Q := by
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Q)]
  apply (Submodule.mem_dualAnnihilator _).mpr
  intro h hh
  exact hΨ u h hh

end GeneralField

section Binary

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {K H : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H]

theorem annihilator_iff_restriction_zero (W : Submodule F2 K) (σ : Module.Dual F2 K) :
    σ ∈ W.dualAnnihilator ↔ σ.comp W.subtype = 0 := Iff.rfl

theorem card_annihilatingCharacters [FiniteDimensional F2 K] (W : Submodule F2 K) :
    Nat.card W.dualAnnihilator =
      2 ^ (Module.finrank F2 K - Module.finrank F2 W) := by
  have hdim : Module.finrank F2 W.dualAnnihilator =
      Module.finrank F2 K - Module.finrank F2 W :=
    Nat.eq_sub_of_add_eq' (Subspace.finrank_add_finrank_dualAnnihilator_eq W)
  rw [Module.natCard_eq_pow_finrank (K := F2), hdim]
  rw [show Nat.card F2 = 2 from Nat.card_zmod 2]

end Binary
end
end PerfectCompleteness.TensorCosetEvaluation

end

section

namespace PerfectCompleteness.TensorRestriction

noncomputable section

open scoped TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {W H : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup H] [Module F2 H] [FiniteDimensional F2 H]

theorem restrictionMap_surjective (Q : Submodule F2 (Module.Dual F2 H)) :
    Function.Surjective (restrictionMap (W := W) Q) := by
  intro f
  obtain ⟨g, hg⟩ := f.exists_extend
  refine ⟨tensorEquivHom.symm g, ?_⟩
  change (tensorEquivHom (tensorEquivHom.symm g)).comp Q.subtype = f
  rw [LinearEquiv.apply_symm_apply]
  exact hg

theorem restrictionMap_tmul_eq_zero (Q : Submodule F2 (Module.Dual F2 H))
    (w : W) (h : H) (hh : h ∈ Q.dualCoannihilator) :
    restrictionMap Q (w ⊗ₜ[F2] h) = 0 := by
  apply LinearMap.ext
  intro q
  rw [restrictionMap_tmul]
  have hq : q.val h = 0 := (Submodule.mem_dualCoannihilator h).mp hh q.val q.property
  rw [hq, zero_smul, LinearMap.zero_apply]

theorem dualImage_vanishes (Q : Submodule F2 (Module.Dual F2 H))
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ∈ dualImage (W := W) Q)
    (w : W) (h : H) (hh : h ∈ Q.dualCoannihilator) :
    Φ (w ⊗ₜ[F2] h) = 0 := by
  obtain ⟨f, rfl⟩ := hΦ
  change f (restrictionMap Q (w ⊗ₜ[F2] h)) = 0
  rw [restrictionMap_tmul_eq_zero Q w h hh, map_zero]

end
end PerfectCompleteness.TensorRestriction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RecursiveSpaceEquivLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SmallBias

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Foundations.Information

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem expectation_mono (μ : FiniteDistribution Ω) {a b : Ω → ℝ}
    (h : ∀ x, a x ≤ b x) : μ.expectation a ≤ μ.expectation b := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

theorem expectation_sum (μ : FiniteDistribution Ω) (a : I → Ω → ℝ) :
    μ.expectation (fun x => ∑ i, a i x) = ∑ i, μ.expectation (a i) := by
  simp only [FiniteDistribution.expectation, Finset.mul_sum]
  exact Finset.sum_comm

end

end PerfectCompleteness.SmallBias

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DualQuotientRowsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.bitSign_toBool _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.SmallBiasSlice

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.SmallBias

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem maskChar_kernel (v t : I → Bool) :
    (∑ s : I → Bool, maskChar s v * maskChar s t) =
      if v = t then (Fintype.card (I → Bool) : ℝ) else 0 := by
  classical
  calc
    _ = ∑ s : I → Bool, ∏ i,
        ((if s i then bitSign (v i) else 1) *
         (if s i then bitSign (t i) else 1)) := by
      simp only [maskChar, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool,
        ((if b then bitSign (v i) else 1) *
         (if b then bitSign (t i) else 1)) :=
      (Fintype.prod_sum (fun (i : I) (b : Bool) =>
        (if b then bitSign (v i) else 1) * (if b then bitSign (t i) else 1))).symm
    _ = ∏ i, (if v i = t i then (2 : ℝ) else 0) := by
      apply Finset.prod_congr rfl
      intro i _
      cases v i <;> cases t i <;> norm_num [Fintype.sum_bool, bitSign]
    _ = _ := by
      rw [Fintype.prod_ite_zero]
      by_cases h : v = t
      · subst t
        simp
      · have h' : ¬ ∀ i, v i = t i := fun h' => h (funext h')
        simp [h, h']

theorem expectation_const_mul (μ : FiniteDistribution Ω) (c : ℝ) (g : Ω → ℝ) :
    μ.expectation (fun x => c * g x) = c * μ.expectation g := by
  unfold FiniteDistribution.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem slice_expansion (μ : FiniteDistribution Ω) (A : Ω → I → Bool)
    (t : I → Bool) (g : Ω → ℝ) :
    (Fintype.card (I → Bool) : ℝ) * sliceNumerator μ A t g =
      ∑ s : I → Bool, maskChar s t *
        μ.expectation (fun x => g x * maskChar s (A x)) := by
  classical
  have hpoint : ∀ x, (Fintype.card (I → Bool) : ℝ) *
      (if A x = t then g x else 0) =
      ∑ s : I → Bool, maskChar s t * (g x * maskChar s (A x)) := by
    intro x
    calc
      _ = g x * (if t = A x then (Fintype.card (I → Bool) : ℝ) else 0) := by
        by_cases hx : A x = t
        · simp [hx, mul_comm]
        · simp [hx, Ne.symm hx]
      _ = g x * ∑ s : I → Bool, maskChar s t * maskChar s (A x) := by
        rw [maskChar_kernel]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
  calc
    _ = μ.expectation (fun x => (Fintype.card (I → Bool) : ℝ) *
        (if A x = t then g x else 0)) :=
      (expectation_const_mul μ _ _).symm
    _ = μ.expectation (fun x => ∑ s : I → Bool,
        maskChar s t * (g x * maskChar s (A x))) := by simp only [hpoint]
    _ = _ := by
      rw [expectation_sum]
      apply Finset.sum_congr rfl
      intro s _
      exact expectation_const_mul μ _ _

theorem sliceMass_lower (μ : FiniteDistribution Ω) (A : Ω → I → Bool)
    (t : I → Bool) (biasBound : ℝ) (hb : 0 ≤ biasBound)
    (hbiased : ∀ s : I → Bool, s ≠ (fun _ => false) →
      |μ.expectation (fun x => maskChar s (A x))| ≤ biasBound) :
    1 / (Fintype.card (I → Bool) : ℝ) - biasBound ≤ sliceMass μ A t := by
  classical
  have hterm : ∀ s : I → Bool,
      (if s = (fun _ => false) then (1 : ℝ) else 0) - biasBound ≤
      maskChar s t * μ.expectation (fun x => maskChar s (A x)) := by
    intro s
    by_cases hs : s = (fun _ => false)
    · subst s
      simp only [ite_true, if_true, maskChar_zero, expectation_const, one_mul]
      linarith
    · have ha : |maskChar s t * μ.expectation (fun x => maskChar s (A x))| ≤
          biasBound := by
        rw [abs_mul, abs_maskChar, one_mul]
        exact hbiased s hs
      simpa only [ite_eq_right hs, zero_sub] using (abs_le.mp ha).1
  have hsum := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (I → Bool))) =>
    hterm s)
  have hexp := slice_expansion μ A t (fun _ => 1)
  simp only [one_mul] at hexp
  have hN : (0 : ℝ) < Fintype.card (I → Bool) :=
    Nat.cast_pos.mpr Fintype.card_pos
  apply le_of_mul_le_mul_left (a := (Fintype.card (I → Bool) : ℝ)) _ hN
  calc
    _ = 1 - (Fintype.card (I → Bool) : ℝ) * biasBound := by
      field_simp [hN.ne']
    _ ≤ ∑ s : I → Bool, maskChar s t *
        μ.expectation (fun x => maskChar s (A x)) := by
      simpa [Finset.sum_sub_distrib] using hsum
    _ = _ := hexp.symm

theorem slice_coefficient_witness (μ : FiniteDistribution Ω) (A : Ω → I → Bool)
    (t : I → Bool) (g : Ω → ℝ) (threshold : ℝ)
    (hlarge : threshold ≤ |sliceNumerator μ A t g|) :
    ∃ s : I → Bool,
      threshold ≤ |μ.expectation (fun x => g x * maskChar s (A x))| := by
  classical
  have hN : (0 : ℝ) ≤ Fintype.card (I → Bool) := Nat.cast_nonneg _
  have hsum : (∑ _s : I → Bool, threshold) ≤
      ∑ s : I → Bool, |μ.expectation (fun x => g x * maskChar s (A x))| := by
    calc
      _ = (Fintype.card (I → Bool) : ℝ) * threshold := by simp
      _ ≤ (Fintype.card (I → Bool) : ℝ) * |sliceNumerator μ A t g| :=
        mul_le_mul_of_nonneg_left hlarge hN
      _ = |∑ s : I → Bool, maskChar s t *
          μ.expectation (fun x => g x * maskChar s (A x))| := by
        rw [← slice_expansion, abs_mul, abs_of_nonneg hN]
      _ ≤ ∑ s : I → Bool, |maskChar s t *
          μ.expectation (fun x => g x * maskChar s (A x))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, abs_maskChar, one_mul]
  obtain ⟨s, _, hs⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨s, hs⟩


variable {F : Type*} [AddCommMonoid F]

omit [Fintype Ω] [DecidableEq I] in
theorem character_rowCombination (χ : F → Ω → ℝ)
    (hzero : ∀ x, χ 0 x = 1)
    (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (rows : I → F) (A : Ω → I → Bool)
    (hrows : ∀ i x, χ (rows i) x = bitSign (A x i)) (s : I → Bool) (x : Ω) :
    χ (rowCombination rows s) x = maskChar s (A x) := by
  classical
  have hsum : ∀ u : Finset I,
      χ (∑ i ∈ u, if s i then rows i else 0) x =
        ∏ i ∈ u, χ (if s i then rows i else 0) x := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp [hzero]
    | @insert i u hi ih => simp [hi, hadd, ih]
  rw [rowCombination, hsum]
  unfold maskChar
  apply Finset.prod_congr rfl
  intro i _
  cases s i <;> simp [hzero, hrows]

theorem coset_coefficient_witness (μ : FiniteDistribution Ω)
    (χ : F → Ω → ℝ) (hzero : ∀ x, χ 0 x = 1)
    (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (rows : I → F) (A : Ω → I → Bool)
    (hrows : ∀ i x, χ (rows i) x = bitSign (A x i))
    (t : I → Bool) (g : Ω → ℝ) (base : F) (threshold : ℝ)
    (hlarge : threshold ≤ |sliceNumerator μ A t (fun x => g x * χ base x)|) :
    ∃ s : I → Bool, threshold ≤
      |μ.expectation (fun x => g x * χ (base + rowCombination rows s) x)| := by
  obtain ⟨s, hs⟩ := slice_coefficient_witness μ A t (fun x => g x * χ base x)
    threshold hlarge
  refine ⟨s, ?_⟩
  simpa only [hadd, character_rowCombination χ hzero hadd rows A hrows, mul_assoc] using hs

theorem affine_coset_heavy_witness [Fintype F] (μ : FiniteDistribution Ω)
    (χ : F → Ω → ℝ) (hzero : ∀ x, χ 0 x = 1)
    (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (rows : I → F) (A : Ω → I → Bool)
    (hrows : ∀ i x, χ (rows i) x = bitSign (A x i))
    (hindependent : Function.Injective (rowCombination rows))
    (t : I → Bool) (g : Ω → ℝ) (base : F)
    (rho h0 biasBound : ℝ) (hrho : 0 < rho) (hh0 : 0 < h0)
    (hsize : h0 ≤ 1 / (Fintype.card (I → Bool) : ℝ))
    (hb : 0 ≤ biasBound) (hbsmall : biasBound ≤ h0 / 2)
    (hbias : ∀ a : F, a ≠ 0 → |μ.expectation (χ a)| ≤ biasBound)
    (hconditional : rho / 2 ≤
      |sliceNumerator μ A t (fun x => g x * χ base x) / sliceMass μ A t|) :
    ∃ s : I → Bool,
      base + rowCombination rows s ∈ heavySet μ χ g (rho * h0 / 4) := by
  classical
  have hmaskbias : ∀ s : I → Bool, s ≠ (fun _ => false) →
      |μ.expectation (fun x => maskChar s (A x))| ≤ biasBound := by
    intro s hs
    have hne : rowCombination rows s ≠ 0 := by
      intro hz
      apply hs
      apply hindependent
      simpa using hz
    have h := hbias (rowCombination rows s) hne
    change |μ.expectation (fun x => χ (rowCombination rows s) x)| ≤ biasBound at h
    simpa only [character_rowCombination χ hzero hadd rows A hrows] using h
  have hmass : h0 / 2 ≤ sliceMass μ A t := by
    have h := sliceMass_lower μ A t biasBound hb hmaskbias
    linarith
  have hmasspos : 0 < sliceMass μ A t := by linarith
  have hcond := hconditional
  rw [abs_div, abs_of_pos hmasspos] at hcond
  have hnum := (le_div_iff₀ hmasspos).1 hcond
  have hthreshold : rho * h0 / 4 ≤
      |sliceNumerator μ A t (fun x => g x * χ base x)| := by
    have hmul := mul_le_mul_of_nonneg_left hmass (show 0 ≤ rho / 2 by linarith)
    nlinarith
  obtain ⟨s, hs⟩ := coset_coefficient_witness μ χ hzero hadd rows A hrows t g base
    (rho * h0 / 4) hthreshold
  refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩


end

end PerfectCompleteness.SmallBiasSlice

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_OutputCharacters
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.bitSign_toBool _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OutputCharacters

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.SmallBias
open PerfectCompleteness.SmallBiasSlice

noncomputable section

variable {Ω I J : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

omit [DecidableEq I] in
theorem sliceNumerator_const_mul (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (c : ℝ) (g : Ω → ℝ) :
    sliceNumerator μ A t (fun x => c * g x) = c * sliceNumerator μ A t g := by
  unfold sliceNumerator
  calc
    _ = μ.expectation (fun x => c * (if A x = t then g x else 0)) := by
      congr 1
      funext x
      by_cases hx : A x = t <;> simp [hx]
    _ = _ := expectation_const_mul μ c _

omit [DecidableEq I] in
theorem abs_sliceNumerator_le_mass (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (g : Ω → ℝ)
    (hg : ∀ x, |g x| ≤ 1) :
    |sliceNumerator μ A t g| ≤ sliceMass μ A t := by
  classical
  apply abs_le.mpr
  constructor
  · have h := expectation_mono μ
        (a := fun x => -(if A x = t then (1 : ℝ) else 0))
        (b := fun x => if A x = t then g x else 0) (by
          intro x
          by_cases hx : A x = t
          · simpa only [ite_eq_left hx] using (abs_le.mp (hg x)).1
          · simp only [ite_eq_right hx, neg_zero, le_refl])
    simpa only [expectation_neg, sliceMass, sliceNumerator] using h
  · change μ.expectation (fun x => if A x = t then g x else 0) ≤
        μ.expectation (fun x => if A x = t then (1 : ℝ) else 0)
    apply expectation_mono μ
    intro x
    by_cases hx : A x = t
    · simpa only [ite_eq_left hx] using (abs_le.mp (hg x)).2
    · simp only [ite_eq_right hx, le_refl]

omit [DecidableEq I] in
theorem abs_sliceCorrelation_le_one (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (g : Ω → ℝ)
    (hmass : 0 < sliceMass μ A t) (hg : ∀ x, |g x| ≤ 1) :
    |sliceCorrelation μ A t g| ≤ 1 := by
  unfold sliceCorrelation
  rw [abs_div, abs_of_pos hmass]
  exact (div_le_one hmass).2 (abs_sliceNumerator_le_mass μ A t g hg)

omit [DecidableEq I] in
theorem sliced_output_kernel (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (G T : Ω → J → Bool) :
    (∑ s : J → Bool, sliceNumerator μ A t
      (fun x => maskChar s (G x) * maskChar s (T x))) =
      (Fintype.card (J → Bool) : ℝ) * sliceNumerator μ A t
        (fun x => if G x = T x then (1 : ℝ) else 0) := by
  classical
  have hpoint : ∀ x,
      (∑ s : J → Bool, if A x = t then
        maskChar s (G x) * maskChar s (T x) else 0) =
      (Fintype.card (J → Bool) : ℝ) *
        (if A x = t then (if G x = T x then (1 : ℝ) else 0) else 0) := by
    intro x
    by_cases hx : A x = t
    · simp only [ite_eq_left hx]
      rw [maskChar_kernel]
      by_cases heq : G x = T x <;> simp [heq]
    · simp [hx]
  calc
    _ = μ.expectation (fun x => ∑ s : J → Bool, if A x = t then
        maskChar s (G x) * maskChar s (T x) else 0) :=
      (expectation_sum μ (fun s x => if A x = t then
        maskChar s (G x) * maskChar s (T x) else 0)).symm
    _ = μ.expectation (fun x => (Fintype.card (J → Bool) : ℝ) *
        (if A x = t then (if G x = T x then (1 : ℝ) else 0) else 0)) := by
      simp only [hpoint]
    _ = _ := expectation_const_mul μ _ _

omit [DecidableEq I] in
theorem sum_output_correlations (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (G T : Ω → J → Bool) :
    (∑ s : J → Bool, sliceCorrelation μ A t
      (fun x => maskChar s (G x) * maskChar s (T x))) =
      (Fintype.card (J → Bool) : ℝ) * conditionalEquality μ A t G T := by
  simp only [sliceCorrelation, conditionalEquality]
  rw [← Finset.sum_div, sliced_output_kernel]
  ring

theorem exists_large_outside {K : Type*} [Fintype K] [Nonempty K]
    (bad : Finset K) (c : K → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hc : ∀ j, |c j| ≤ 1)
    (hbad : (bad.card : ℝ) < (Fintype.card K : ℝ) * rho / 8)
    (htotal : (Fintype.card K : ℝ) * rho ≤ ∑ j, c j) :
    ∃ j, j ∉ bad ∧ rho / 2 ≤ |c j| := by
  classical
  by_contra h
  have hsmall : ∀ j, j ∉ bad → |c j| < rho / 2 := by
    intro j hj
    exact lt_of_not_ge (fun hh => h ⟨j, hj, hh⟩)
  have hterm : ∀ j, c j ≤ (if j ∈ bad then (1 : ℝ) else 0) + rho / 2 := by
    intro j
    by_cases hj : j ∈ bad
    · have hb := (abs_le.mp (hc j)).2
      simp only [ite_eq_left hj]
      linarith
    · have hs := (le_abs_self (c j)).trans (hsmall j hj).le
      simpa only [ite_eq_right hj, zero_add] using hs
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset K)) => hterm j)
  have hsum' : (∑ j, c j) ≤
      (bad.card : ℝ) + (Fintype.card K : ℝ) * (rho / 2) := by
    simpa [Finset.sum_add_distrib] using hsum
  have hN : (0 : ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hNrho : 0 < (Fintype.card K : ℝ) * rho := mul_pos hN hrho
  nlinarith

omit [DecidableEq I] in
theorem equality_implies_nonbad_correlation (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool) (G T : Ω → J → Bool)
    (bad : Finset (J → Bool)) (rho : ℝ) (hrho : 0 < rho)
    (hmass : 0 < sliceMass μ A t)
    (hbad : (bad.card : ℝ) / (Fintype.card (J → Bool) : ℝ) < rho / 8)
    (hequality : rho ≤ conditionalEquality μ A t G T) :
    ∃ s : J → Bool, s ∉ bad ∧ rho / 2 ≤
      |sliceCorrelation μ A t (fun x => maskChar s (G x) * maskChar s (T x))| := by
  have hN : (0 : ℝ) < Fintype.card (J → Bool) := Nat.cast_pos.mpr Fintype.card_pos
  apply exists_large_outside bad _ rho hrho
  · intro s
    apply abs_sliceCorrelation_le_one μ A t _ hmass
    intro x
    simp only [abs_mul, abs_maskChar, one_mul, le_refl]
  · have h := (div_lt_iff₀ hN).1 hbad
    nlinarith
  · rw [sum_output_correlations]
    exact mul_le_mul_of_nonneg_left hequality hN.le

omit [DecidableEq I] [DecidableEq J] in
theorem abs_conditional_sign_transport (μ : FiniteDistribution Ω)
    (A : Ω → I → Bool) (t : I → Bool)
    (G T : Ω → J → Bool) (s : J → Bool)
    (φ : Ω → ℝ) (sign : ℝ) (hsign : |sign| = 1)
    (hT : ∀ x, maskChar s (T x) = sign * φ x) :
    |sliceCorrelation μ A t (fun x => maskChar s (G x) * maskChar s (T x))| =
      |sliceCorrelation μ A t (fun x => maskChar s (G x) * φ x)| := by
  have hfun : (fun x => maskChar s (G x) * maskChar s (T x)) =
      (fun x => sign * (maskChar s (G x) * φ x)) := by
    funext x
    rw [hT]
    ring
  unfold sliceCorrelation
  rw [hfun, sliceNumerator_const_mul]
  simp only [abs_div, abs_mul, hsign, one_mul]


variable {F : Type*} [AddCommMonoid F] [Fintype F]

theorem equality_implies_affine_heavy_witness (μ : FiniteDistribution Ω)
    (χ : F → Ω → ℝ) (hzero : ∀ x, χ 0 x = 1)
    (hadd : ∀ a b x, χ (a + b) x = χ a x * χ b x)
    (rows : I → F) (A : Ω → I → Bool)
    (hrows : ∀ i x, χ (rows i) x = bitSign (A x i))
    (hindependent : Function.Injective (rowCombination rows))
    (t : I → Bool) (G T : Ω → J → Bool)
    (base : (J → Bool) → F) (sign : (J → Bool) → ℝ)
    (hsign : ∀ s, |sign s| = 1)
    (htarget : ∀ s x, maskChar s (T x) = sign s * χ (base s) x)
    (bad : Finset (J → Bool)) (rho h0 biasBound : ℝ)
    (hrho : 0 < rho) (hh0 : 0 < h0)
    (hsize : h0 ≤ 1 / (Fintype.card (I → Bool) : ℝ))
    (hb : 0 ≤ biasBound) (hbsmall : biasBound ≤ h0 / 2)
    (hbias : ∀ a : F, a ≠ 0 → |μ.expectation (χ a)| ≤ biasBound)
    (hbad : (bad.card : ℝ) / (Fintype.card (J → Bool) : ℝ) < rho / 8)
    (hequality : rho ≤ conditionalEquality μ A t G T) :
    ∃ s : J → Bool, s ∉ bad ∧ ∃ mask : I → Bool,
      base s + rowCombination rows mask ∈
        heavySet μ χ (fun x => maskChar s (G x)) (rho * h0 / 4) := by
  have hmaskbias : ∀ mask : I → Bool, mask ≠ (fun _ => false) →
      |μ.expectation (fun x => maskChar mask (A x))| ≤ biasBound := by
    intro mask hmask
    have hne : rowCombination rows mask ≠ 0 := by
      intro hz
      apply hmask
      apply hindependent
      simpa using hz
    have h := hbias (rowCombination rows mask) hne
    change |μ.expectation (fun x => χ (rowCombination rows mask) x)| ≤ biasBound at h
    simpa only [character_rowCombination χ hzero hadd rows A hrows] using h
  have hmass : 0 < sliceMass μ A t := by
    have h := sliceMass_lower μ A t biasBound hb hmaskbias
    linarith
  obtain ⟨s, hsbad, hcorr⟩ :=
    equality_implies_nonbad_correlation μ A t G T bad rho hrho hmass hbad hequality
  rw [abs_conditional_sign_transport μ A t G T s (χ (base s)) (sign s)
    (hsign s) (htarget s)] at hcorr
  refine ⟨s, hsbad, ?_⟩
  exact affine_coset_heavy_witness μ χ hzero hadd rows A hrows hindependent t
    (fun x => maskChar s (G x)) (base s) rho h0 biasBound hrho hh0 hsize hb hbsmall
    hbias hcorr


end

end PerfectCompleteness.OutputCharacters

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryDualCoordinates
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineLinearHeavyWitness.card_badMasks _root_.OAI.PerfectCompleteness.AffineLinearHeavyWitness.mem_badMasks _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BinaryDualCoordinates

open scoped BigOperators
open QuarterBalance (F2)
open SmallBiasSlice

noncomputable section

theorem toBool_injective : Function.Injective toBool := by
  intro a b h
  simpa using congrArg ofBool h

theorem ofBool_injective : Function.Injective ofBool := by
  intro a b h
  simpa using congrArg toBool h

variable {I V : Type*} [Fintype I] [AddCommGroup V] [Module F2 V]

theorem coordinates_injective (b : Module.Basis I F2 V) :
    Function.Injective (coordinates b) := by
  intro x y h
  apply b.equivFun.injective
  funext i
  have hi := toBool_injective (congrFun h i)
  simpa only [Module.Basis.equivFun_apply, Module.Basis.coord_apply] using hi

theorem frequency_injective (b : Module.Basis I F2 V) :
    Function.Injective (frequency b) := by
  intro s t h
  funext i
  apply ofBool_injective
  simpa using congrArg (fun f : Module.Dual F2 V => f (b i)) h

theorem character_add (f g : Module.Dual F2 V) (x : V) :
    character (f + g) x = character f x * character g x := by
  simp only [character, LinearMap.add_apply, QuarterBalance.sign_add]

theorem character_frequency (b : Module.Basis I F2 V)
    (s : I → Bool) (x : V) :
    character (frequency b s) x = maskChar s (coordinates b x) := by
  classical
  apply character_rowCombination character character_zero character_add
    (fun i => b.coord i) (coordinates b)
  intro i y
  exact (bitSign_toBool (b.coord i y)).symm

variable {U : Type*} [AddCommGroup U] [Module F2 U]

theorem equations_eq_iff (b : Module.Basis I F2 V) (R : U →ₗ[F2] V)
    (x : U) (target : V) :
    equations b R x = coordinates b target ↔ R x = target :=
  ⟨fun h => coordinates_injective b h, fun h => congrArg (coordinates b) h⟩

omit [Fintype I] in
theorem character_equationRows (b : Module.Basis I F2 V)
    (R : U →ₗ[F2] V) (i : I) (x : U) :
    character (equationRows b R i) x = bitSign (equations b R x i) :=
  (bitSign_toBool _).symm

theorem rowCombination_equationRows (b : Module.Basis I F2 V)
    (R : U →ₗ[F2] V) (s : I → Bool) :
    rowCombination (equationRows b R) s = (frequency b s).comp R := by
  classical
  ext x
  simp only [equationRows, frequency, rowCombination, LinearMap.comp_apply,
    LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases s i <;> simp

theorem equationRows_independent (b : Module.Basis I F2 V)
    (R : U →ₗ[F2] V) (hR : Function.Surjective R) :
    Function.Injective (rowCombination (equationRows b R)) := by
  intro s t h
  apply frequency_injective b
  ext v
  obtain ⟨x, rfl⟩ := hR v
  rw [rowCombination_equationRows, rowCombination_equationRows] at h
  exact congrArg (fun f : Module.Dual F2 U => f x) h

theorem rowCombination_mem_dualRange (b : Module.Basis I F2 V)
    (R : U →ₗ[F2] V) (s : I → Bool) :
    rowCombination (equationRows b R) s ∈ LinearMap.range R.dualMap := by
  refine ⟨frequency b s, ?_⟩
  exact (rowCombination_equationRows b R s).symm

theorem character_affine_target (b : Module.Basis I F2 V)
    (T : U →ₗ[F2] V) (offset : V) (s : I → Bool) (x : U) :
    maskChar s (coordinates b (offset + T x)) =
      character (frequency b s) offset * character ((frequency b s).comp T) x := by
  rw [← character_frequency]
  simp only [character, map_add, LinearMap.comp_apply, QuarterBalance.sign_add]

end
end PerfectCompleteness.BinaryDualCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_AffineLinearHeavyWitness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.AffineLinearHeavyWitness

open scoped BigOperators
open QuarterBalance (F2)
open BinaryDualCoordinates
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {U V K I J : Type*}
  [AddCommGroup U] [Module F2 U] [Fintype U]
  [AddCommGroup V] [Module F2 V]
  [AddCommGroup K] [Module F2 K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem conditionalEquality_coordinates (μ : FiniteDistribution U)
    (b : Module.Basis I F2 V) (c : Module.Basis J F2 K)
    (R : U →ₗ[F2] V) (target : V) (G : U → K)
    (T : U →ₗ[F2] K) (offset : K) :
    OutputCharacters.conditionalEquality μ (equations b R) (coordinates b target)
      (fun x => coordinates c (G x)) (fun x => coordinates c (offset + T x)) =
      conditionalMatch μ R target G T offset := by
  classical
  simp only [OutputCharacters.conditionalEquality, OutputCharacters.sliceCorrelation,
    SmallBiasSlice.sliceNumerator, SmallBiasSlice.sliceMass, conditionalMatch,
    equations_eq_iff, (coordinates_injective c).eq_iff]

theorem exists_heavy_in_dual_coset [Fintype (Module.Dual F2 U)]
    [Fintype (Module.Dual F2 K)]
    (μ : FiniteDistribution U)
    (b : Module.Basis I F2 V) (c : Module.Basis J F2 K)
    (R : U →ₗ[F2] V) (hR : Function.Surjective R) (target : V)
    (G : U → K) (T : U →ₗ[F2] K) (offset : K)
    (bad : Finset (Module.Dual F2 K)) (rho h0 biasBound : ℝ)
    (hrho : 0 < rho) (hh0 : 0 < h0)
    (hsize : h0 ≤ 1 / (Fintype.card (I → Bool) : ℝ))
    (hb : 0 ≤ biasBound) (hbsmall : biasBound ≤ h0 / 2)
    (hbias : ∀ f : Module.Dual F2 U, f ≠ 0 →
      |μ.expectation (character f)| ≤ biasBound)
    (hbad : (bad.card : ℝ) / (Fintype.card (Module.Dual F2 K) : ℝ) < rho / 8)
    (hmatch : rho ≤ conditionalMatch μ R target G T offset) :
    ∃ σ : Module.Dual F2 K, σ ∉ bad ∧
      ∃ ψ ∈ LinearMap.range R.dualMap,
        σ.comp T + ψ ∈ SmallBias.heavySet μ character
          (fun x => character σ (G x)) (rho * h0 / 4) := by
  classical
  have hcard : Fintype.card (J → Bool) = Fintype.card (Module.Dual F2 K) :=
    Fintype.card_congr (frequencyEquiv c)
  have hbad' : ((badMasks c bad).card : ℝ) /
      (Fintype.card (J → Bool) : ℝ) < rho / 8 := by
    simpa only [card_badMasks, hcard] using hbad
  have hmatch' : rho ≤ OutputCharacters.conditionalEquality μ (equations b R)
      (coordinates b target) (fun x => coordinates c (G x))
      (fun x => coordinates c (offset + T x)) := by
    rwa [conditionalEquality_coordinates]
  obtain ⟨s, hs, mask, hmask⟩ :=
    OutputCharacters.equality_implies_affine_heavy_witness μ
      character character_zero character_add (equationRows b R) (equations b R)
      (character_equationRows b R) (equationRows_independent b R hR)
      (coordinates b target) (fun x => coordinates c (G x))
      (fun x => coordinates c (offset + T x))
      (fun s => (frequency c s).comp T) (fun s => character (frequency c s) offset)
      (fun s => abs_character _ _) (character_affine_target c T offset)
      (badMasks c bad) rho h0 biasBound hrho hh0 hsize hb hbsmall hbias hbad' hmatch'
  refine ⟨frequency c s, (mem_badMasks c bad s).not.mp hs,
    SmallBiasSlice.rowCombination (equationRows b R) mask,
    rowCombination_mem_dualRange b R mask, ?_⟩
  simpa only [← character_frequency] using hmask

end
end PerfectCompleteness.AffineLinearHeavyWitness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.TensorTargetCharacter

noncomputable section

open scoped TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open TensorCosetEvaluation (pureFrequency)

variable {ℓ : Nat} {H : Type*} [AddCommGroup H] [Module F2 H]

theorem comp_tensorOutputLinear (W : Submodule F2 (Fin ℓ → F2))
    (σ : Module.Dual F2 (Fin ℓ → F2)) (z : Module.Dual F2 H) :
    σ.comp (TensorBucketEvaluation.tensorOutputLinear W z) =
      pureFrequency (σ.comp W.subtype) z := by
  apply TensorProduct.ext'
  intro w h
  change σ (TensorBucketEvaluation.tensorOutput W z (w ⊗ₜ[F2] h)) =
    pureFrequency (σ.comp W.subtype) z (w ⊗ₜ[F2] h)
  rw [TensorBucketEvaluation.tensorOutput_tmul,
    TensorCosetEvaluation.pureFrequency_tmul, map_smul]
  change z h * σ w.val = σ w.val * z h
  exact mul_comm _ _

end
end PerfectCompleteness.TensorTargetCharacter

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OutputAnnihilator
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OutputAnnihilator

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {K : Type*} [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 K] [Fintype (Module.Dual F2 K)]

omit [FiniteDimensional F2 K] in
theorem not_mem_bad_iff (W : Submodule F2 K) (σ : Module.Dual F2 K) :
    σ ∉ bad W ↔ σ.comp W.subtype ≠ 0 := by
  rw [mem_bad, TensorCosetEvaluation.annihilator_iff_restriction_zero]

theorem card_bad (W : Submodule F2 K) :
    (bad W).card = 2 ^ (Module.finrank F2 K - Module.finrank F2 W) := by
  calc
    _ = Fintype.card W.dualAnnihilator := by
      rw [Fintype.card_subtype]
      rfl
    _ = Nat.card W.dualAnnihilator := Fintype.card_eq_nat_card
    _ = _ := TensorCosetEvaluation.card_annihilatingCharacters W

omit [FiniteDimensional F2 K] in
theorem card_dual : Fintype.card (Module.Dual F2 K) = 2 ^ Module.finrank F2 K := by
  rw [Module.card_eq_pow_finrank (K := F2), Subspace.dual_finrank_eq]
  rw [show Fintype.card F2 = 2 by decide]

theorem card_dual_eq_bad_mul (W : Submodule F2 K) :
    Fintype.card (Module.Dual F2 K) = (bad W).card * 2 ^ Module.finrank F2 W := by
  rw [card_dual, card_bad, ← pow_add, Nat.sub_add_cancel W.finrank_le]

theorem bad_fraction (W : Submodule F2 K) :
    ((bad W).card : ℝ) / Fintype.card (Module.Dual F2 K) =
      1 / (2 : ℝ) ^ Module.finrank F2 W := by
  have hbad : ((bad W).card : ℝ) ≠ 0 := by
    rw [card_bad]
    positivity
  rw [card_dual_eq_bad_mul W, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    div_mul_eq_div_div, div_self hbad]

end
end PerfectCompleteness.OutputAnnihilator

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorAffineHeavyWitness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TensorAffineHeavyWitness

open scoped TensorProduct Classical
open QuarterBalance (F2)
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {ℓ : Nat} {H : Type*} [AddCommGroup H] [Module F2 H]
  [Finite H] [FiniteDimensional F2 H]

attribute [local instance] OAI.PerfectCompleteness.TensorAffineHeavyWitness.dualFintype
theorem exists_heavy_candidate_oai (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution (W ⊗[F2] H)) (G : (W ⊗[F2] H) → (Fin ℓ → F2))
    (ρ h₀ biasBound : ℝ) (hρ : 0 < ρ) (hh₀ : 0 < h₀) (hbiasBound : 0 ≤ biasBound)
    (hsmall : biasBound ≤ h₀ / 2)
    (hbias : ∀ Φ : Module.Dual F2 (W ⊗[F2] H), Φ ≠ 0 →
      |μ.expectation (fun X => QuarterBalance.sign (Φ X))| ≤ biasBound)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 W < ρ / 8)
    (Q : Submodule F2 (Module.Dual F2 H))
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2 (Q →ₗ[F2] W))
    (target : Q →ₗ[F2] W) (z : Module.Dual F2 H) (offset : Fin ℓ → F2)
    (hmatch : ρ ≤ conditionalMatch W μ G Q target z offset) :
    ∃ σ : Module.Dual F2 (Fin ℓ → F2), σ.comp W.subtype ≠ 0 ∧
      ∃ Φ ∈ heavyList W μ G (ρ * h₀ / 4) σ,
        ∀ w : W, σ w = 1 → TensorCosetEvaluation.scalarRestriction Φ w - z ∈ Q := by
  let : Module.Free F2 (Q →ₗ[F2] W) := Module.Free.of_divisionRing F2 (Q →ₗ[F2] W)
  let : Fintype (Module.Dual F2 (W ⊗[F2] H)) :=
    Fintype.ofInjective (fun functional : Module.Dual F2 (W ⊗[F2] H) =>
      (functional : (W ⊗[F2] H) → F2)) DFunLike.coe_injective
  let b := Module.finBasis F2 (Q →ₗ[F2] W)
  let c := Module.finBasis F2 (Fin ℓ → F2)
  have hsize' : h₀ ≤ 1 / (Fintype.card
      (Fin (Module.finrank F2 (Q →ₗ[F2] W)) → Bool) : ℝ) := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat] using hsize
  have hbad : ((OutputAnnihilator.bad W).card : ℝ) /
      Fintype.card (Module.Dual F2 (Fin ℓ → F2)) < ρ / 8 := by
    rw [OutputAnnihilator.bad_fraction]
    exact hexcluded
  unfold conditionalMatch at hmatch
  have candidateBasis :=
    AffineLinearHeavyWitness.exists_heavy_in_dual_coset
      (U := W ⊗[F2] H) (V := Q →ₗ[F2] W) (K := Fin ℓ → F2) μ b c
  have candidateRestriction := candidateBasis
      (TensorRestriction.restrictionMap Q)
      (TensorRestriction.restrictionMap_surjective (W := W) Q)
  have candidateData := candidateRestriction
      target G (TensorBucketEvaluation.tensorOutputLinear W z) offset
      (OutputAnnihilator.bad W) ρ h₀ biasBound
  have candidateBounds := candidateData hρ hh₀ hsize' hbiasBound hsmall hbias hbad
  have candidateWitness := candidateBounds hmatch
  obtain ⟨σ, hσ, ψ, hψ, hheavy⟩ := candidateWitness
  refine ⟨σ, (OutputAnnihilator.not_mem_bad_iff W σ).mp hσ,
    σ.comp (TensorBucketEvaluation.tensorOutputLinear W z) + ψ, ?_, ?_⟩
  · simp only [heavyList, OwnLawHeavyList.heavyList, SmallBias.heavySet,
      Finset.mem_filter, Finset.mem_univ, true_and] at hheavy ⊢
    simpa only [OwnLawHeavyList.character, BinaryDualCoordinates.character] using hheavy
  · intro w hw
    have hψ' : TensorCosetEvaluation.scalarRestriction ψ w ∈ Q :=
      TensorCosetEvaluation.scalarRestriction_mem_of_vanishes Q ψ
        (TensorRestriction.dualImage_vanishes Q ψ hψ) w
    rw [TensorTargetCharacter.comp_tensorOutputLinear,
      TensorCosetEvaluation.scalarRestriction_add,
      TensorCosetEvaluation.scalarRestriction_pure]
    have hw' : (σ.comp W.subtype) w = 1 := hw
    rw [hw', one_smul, add_sub_cancel_left]
    exact hψ'

end
end PerfectCompleteness.TensorAffineHeavyWitness

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PerfectCompleteness.TensorAffineHeavyWitness.exists_heavy_candidate_oai.{u_1} := @OAI.PerfectCompleteness.TensorAffineHeavyWitness.exists_heavy_candidate_oai.{u_1}
