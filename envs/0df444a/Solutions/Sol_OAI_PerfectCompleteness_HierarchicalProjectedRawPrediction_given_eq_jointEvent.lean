-- Prove2me | solution 1 for OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.given_eq_jointEvent
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:27.546216+00:00
-- url     : https://prove2.me/submissions/d207a097-d61e-4aac-b7fa-4e97b03a029a

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
import Mathlib.Algebra.BigOperators.Module
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
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
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
import Definitions.Def_OAIQ252P017

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PartitionsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedColumnSlice

noncomputable section

variable {𝕜 H H' W : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup H'] [Module 𝕜 H']
  [AddCommGroup W] [Module 𝕜 W]
  (i : H' →ₗ[𝕜] H) (Z : Submodule 𝕜 (Module.Dual 𝕜 H))

theorem restrictionZ_surjective : Function.Surjective (restrictionZ i Z) := by
  intro q
  obtain ⟨z, hz, heq⟩ := Submodule.mem_map.mp q.property
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  exact heq

end
end PerfectCompleteness.ProjectedColumnSlice

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BucketSampler

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {Ω H : Type*} [AddCommGroup H] [Module F2 H]

theorem linearMap_evaluate (ℓ : Nat) (eval : Ω → H) (t : Tape ℓ Ω)
    (q : H →ₗ[F2] F2) (i : Fin ℓ) :
    q (evaluate ℓ eval t i) = ∑ v : Direction ℓ, v.val i * q (eval (t v)) := by
  simp only [evaluate, map_sum, map_smul, smul_eq_mul]


open PointwiseSpaces RecursiveSpaces DescendantSpaces

universe u

end
end PerfectCompleteness.BucketSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TensorBucketEvaluation

open scoped BigOperators TensorProduct Classical

noncomputable section

variable {ℓ : Nat} {Ω H : Type*} [AddCommGroup H] [Module F2 H]

theorem tensorOutput_hiddenSum (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (eval : Ω → H)
    (ω : HiddenBucketBias.HiddenTape W Ω) :
    tensorOutput W q (HiddenBucketBias.hiddenSum W eval ω) =
      ∑ v : HiddenBucketBias.HiddenDirection W, q (eval (ω v)) • v.val.val := by
  change tensorOutputLinear W q
    (∑ v : HiddenBucketBias.HiddenDirection W,
      HiddenBucketBias.directionIn W v ⊗ₜ[F2] eval (ω v)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact tensorOutput_tmul W q (HiddenBucketBias.directionIn W v) (eval (ω v))

theorem evaluate_eq_direction_sum (q : Module.Dual F2 H)
    (eval : Ω → H) (t : BucketSampler.Tape ℓ Ω) :
    (fun i => q (BucketSampler.evaluate ℓ eval t i)) =
      ∑ v : BucketSampler.Direction ℓ, q (eval (t v)) • v.val := by
  funext i
  rw [BucketSampler.linearMap_evaluate]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro v _
  exact mul_comm _ _

theorem evaluate_split (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (eval : Ω → H) (t : BucketSampler.Tape ℓ Ω) :
    (fun i => q (BucketSampler.evaluate ℓ eval t i)) =
      visibleOutput W q eval (fun v => t v.val) +
        tensorOutput W q
          (HiddenBucketBias.hiddenSum W eval (fun v => t v.val)) := by
  rw [evaluate_eq_direction_sum, tensorOutput_hiddenSum]
  exact (Fintype.sum_subtype_add_sum_subtype
    (fun v : BucketSampler.Direction ℓ => v.val ∈ W)
    (fun v => q (eval (t v)) • v.val)).symm.trans (add_comm _ _)

theorem evaluate_splitTape (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (eval : Ω → H) (t : BucketSampler.Tape ℓ Ω) :
    (fun i => q (BucketSampler.evaluate ℓ eval t i)) =
      visibleOutput W q eval (HiddenBucketBias.splitTape W Ω t).2 +
        tensorOutput W q
          (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω t).1) :=
  evaluate_split W q eval t

end

end PerfectCompleteness.TensorBucketEvaluation



namespace PerfectCompleteness.TensorProjectedSlice

noncomputable section

open scoped TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {K H H' : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H']
  (i : H' →ₗ[F2] H) (W : Submodule F2 K)

variable (Z : Submodule F2 (Module.Dual F2 H))

theorem compatible_iff_restrictionMap_eq
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (T₀ : W ⊗[F2] H') (h₀ : Compatible i W Z X₀ v T₀)
    (T : W ⊗[F2] H') :
    Compatible i W Z X₀ v T ↔
      TensorRestriction.restrictionMap (ProjectedColumnSlice.projectedColumns i Z) T =
        targetAt i W Z T₀ := by
  constructor
  · intro hT
    apply LinearMap.ext
    intro q
    obtain ⟨z, rfl⟩ := ProjectedColumnSlice.restrictionZ_surjective i Z q
    apply Subtype.ext
    have hTz := LinearMap.congr_fun hT z
    have h₀z := LinearMap.congr_fun h₀ z
    change X₀ z.val + (TensorRestriction.tensorEquivHom T (i.dualMap z.val) : K) =
      v z at hTz
    change X₀ z.val + (TensorRestriction.tensorEquivHom T₀ (i.dualMap z.val) : K) =
      v z at h₀z
    exact add_left_cancel (hTz.trans h₀z.symm)
  · intro hT
    apply LinearMap.ext
    intro z
    have hz := LinearMap.congr_fun hT (ProjectedColumnSlice.restrictionZ i Z z)
    change TensorRestriction.tensorEquivHom T (i.dualMap z.val) =
      TensorRestriction.tensorEquivHom T₀ (i.dualMap z.val) at hz
    change X₀ z.val + (TensorRestriction.tensorEquivHom T (i.dualMap z.val) : K) = v z
    rw [hz]
    exact LinearMap.congr_fun h₀ z

theorem columnEquations_iff_inducedTarget
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (v : Z →ₗ[F2] K)
    (hne : ∃ T : W ⊗[F2] H', Compatible i W Z X₀ v T)
    (T : W ⊗[F2] H') :
    (totalMatrix i W X₀ T).domRestrict Z = v ↔
      TensorRestriction.restrictionMap (ProjectedColumnSlice.projectedColumns i Z) T =
        inducedTarget i W Z X₀ v hne :=
  compatible_iff_restrictionMap_eq i W Z X₀ v
    (Classical.choose hne) (Classical.choose_spec hne) T


variable {ℓ : Nat} (R : Submodule F2 (Fin ℓ → F2))

theorem includedEvaluation_eq_tensorOutputLinear (q : Module.Dual F2 H') :
    R.subtype.comp ((LinearMap.applyₗ (R := F2) q).comp
      (TensorRestriction.tensorEquivHom (W := R) (H := H')).toLinearMap) =
      TensorBucketEvaluation.tensorOutputLinear R q := by
  apply TensorProduct.ext'
  intro w h
  change (TensorRestriction.tensorEquivHom (w ⊗ₜ[F2] h) q : Fin ℓ → F2) =
    TensorBucketEvaluation.tensorOutput R q (w ⊗ₜ[F2] h)
  rw [TensorRestriction.tensorEquivHom_tmul, TensorBucketEvaluation.tensorOutput_tmul]
  rfl

theorem includedEvaluation_eq_tensorOutput (q : Module.Dual F2 H')
    (T : R ⊗[F2] H') :
    (TensorRestriction.tensorEquivHom T q : Fin ℓ → F2) =
      TensorBucketEvaluation.tensorOutput R q T :=
  LinearMap.congr_fun (includedEvaluation_eq_tensorOutputLinear R q) T

end
end PerfectCompleteness.TensorProjectedSlice



namespace PerfectCompleteness.HierarchicalTensorMatrix

noncomputable section

open scoped BigOperators TensorProduct Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (W : Submodule F2 (Block rows upper))

theorem visibleMatrix_apply
    (known : HiddenBucketBias.VisibleDirection W → NodeEmbedding.NodeH slots upper)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    visibleMatrix slots upper W known q =
      ∑ v : HiddenBucketBias.VisibleDirection W,
        (q.comp (NodeEmbedding.embed slots upper)) (known v) • v.val.val := by
  simp only [visibleMatrix, LinearMap.sum_apply, LinearMap.smulRight_apply]
  rfl

end
end PerfectCompleteness.HierarchicalTensorMatrix



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorRowAdviceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.TensorSelectedSlice

noncomputable section

open scoped Classical TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {K H H' Y : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H'] [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Y]
  (i : H' →ₗ[F2] H) (W : Submodule F2 K) (B : Submodule F2 H)

variable (f : (Module.Dual F2 (H ⧸ B) →ₗ[F2] K) → Option Y)
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r)
  (X₀ : Module.Dual F2 H →ₗ[F2] K)

variable (hW : W ≤ LinearMap.ker A)

include hW

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem J_iff_restriction
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (hne : ∃ T : W ⊗[F2] H', GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true)
    (T : W ⊗[F2] H') :
    GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = true ↔
      TensorRestriction.restrictionMap (columnSpace i B f r ρ A X₀ hgood) T =
        target i W B f r ρ A X₀ hW hgood hne :=
  (J_iff_compatible i W B f r ρ A X₀ hW hgood T).trans
    (TensorProjectedSlice.columnEquations_iff_inducedTarget (B.mkQ.comp i) W
      (witness B f r ρ A X₀ hgood).columnSpace
      (MatrixRowQuotient.projectMatrix B X₀)
      ((witness B f r ρ A X₀ hgood).base.domRestrict
        (witness B f r ρ A X₀ hgood).columnSpace)
      (exists_compatible i W B f r ρ A X₀ hW hgood hne) T)

end
end PerfectCompleteness.TensorSelectedSlice



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputAffineSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OwnInputRawAssembly

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open OwnInputReference (RawSample ScalarSample UpperSpace UpperVector Cut)

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

theorem backgroundOf_assemble
    (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower) :
    HierarchicalMatrixTable.backgroundOf slots upper
        (OwnInputCanonicalQuery.assemble slots rows upper lower upperRows external) =
      HierarchicalMatrixTable.backgroundOf slots upper
        (OwnInputCanonicalQuery.assemble slots rows upper lower 0 external) := by
  funext node
  simp only [HierarchicalMatrixTable.backgroundOf, OwnInputCanonicalQuery.assemble,
    dite_eq_right node.property]

variable (W : Submodule F2 (UpperVector rows upper))
  (repeats : Nat → Nat) (cut : Cut upper lower)

theorem split_mergedTape (sample : RawSample slots rows upper lower W repeats cut) :
    HiddenBucketBias.splitTape W (ScalarSample slots upper lower repeats cut)
      (mergedTape slots rows upper lower W repeats cut sample) = (sample.1, sample.2.1) :=
  (HiddenBucketBias.splitTape W (ScalarSample slots upper lower repeats cut)).apply_symm_apply _

theorem arrays_upper (sample : RawSample slots rows upper lower W repeats cut) :
    arrays slots rows upper lower W repeats cut sample upper =
      BucketSampler.evaluate (rows (Nodes.height upper)) (scalarEval slots upper lower repeats cut)
        (mergedTape slots rows upper lower W repeats cut sample) :=
  OwnInputCanonicalQuery.assemble_upper slots rows upper lower _ _

theorem background_arrays (sample : RawSample slots rows upper lower W repeats cut) :
    HierarchicalMatrixTable.backgroundOf slots upper
      (arrays slots rows upper lower W repeats cut sample) =
      background slots rows upper lower W repeats cut sample.2 :=
  backgroundOf_assemble slots rows upper lower _ sample.2.2

end
end PerfectCompleteness.OwnInputRawAssembly

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedSlice

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) originalSlots upper)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH projectedSlots upper)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedSlice.rowSpaceFintype
local instance valueFintype_r03a1b9_1 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
theorem J_iff_restriction
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (hne : ∃ T, J originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true)
    (T : HiddenTensor projectedSlots upper A) :
    J originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true ↔
      TensorRestriction.restrictionMap
        (columnSpace originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) T =
      target originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood hne :=
  TensorSelectedSlice.J_iff_restriction (ProjectedNodeEmbedding.intoOriginal projection upper) (LinearMap.ker A)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) le_rfl hgood hne T

end
end PerfectCompleteness.HierarchicalProjectedSlice


namespace PerfectCompleteness.ProjectedRawAssembly

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s k, MixedSupport.Projection (originalSlots s k) (projectedSlots s k))
  (rows : Nat → Nat) (upper lower : Nodes branch n)

variable (W : Submodule F2 (Block rows upper))
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

theorem visibleMatrix_apply
    (visible : OwnInputAffineSlice.VisibleSample projectedSlots rows upper lower W repeats cut)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace originalSlots upper)) :
    visibleMatrix originalSlots projectedSlots projection rows upper lower W repeats cut visible q =
      ∑ v : HiddenBucketBias.VisibleDirection W,
        (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputRawAssembly.knownVisible projectedSlots rows upper lower W repeats cut visible v) •
            v.val.val :=
  HierarchicalTensorMatrix.visibleMatrix_apply originalSlots upper W
    (fun v => ProjectedNodeEmbedding.nativePullback projection upper
      (OwnInputRawAssembly.knownVisible projectedSlots rows upper lower W repeats cut visible v)) q

theorem background_arrays
    (sample : OwnInputReference.RawSample projectedSlots rows upper lower W repeats cut) :
    HierarchicalMatrixTable.backgroundOf originalSlots upper
        (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample) =
      background originalSlots projectedSlots projection rows upper lower W repeats cut sample.2 := by
  funext node row
  exact congrArg
    (fun bg : HierarchicalMatrixTable.Background (rows := rows) projectedSlots upper =>
      ProjectedNodeEmbedding.nativePullback projection node.val (bg node row))
    (OwnInputRawAssembly.background_arrays projectedSlots rows upper lower W repeats cut sample)

theorem matrix_arrays
    (sample : OwnInputReference.RawSample projectedSlots rows upper lower W repeats cut) :
    NodeEmbedding.matrix
        (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample) upper =
      TensorProjectedSlice.totalMatrix (ProjectedNodeEmbedding.intoOriginal projection upper) W
        (visibleMatrix originalSlots projectedSlots projection rows upper lower W repeats cut sample.2)
        (OwnInputAffineSlice.hiddenOutput projectedSlots rows upper lower W repeats cut sample) := by
  apply LinearMap.ext
  intro q
  have hsplit := TensorBucketEvaluation.evaluate_splitTape W
    (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
    (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut)
    (OwnInputRawAssembly.mergedTape projectedSlots rows upper lower W repeats cut sample)
  rw [OwnInputRawAssembly.split_mergedTape] at hsplit
  calc
    NodeEmbedding.matrix
        (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample) upper q =
        (fun row => (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputRawAssembly.arrays projectedSlots rows upper lower W repeats cut sample upper row)) := rfl
    _ = (fun row => (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
        (BucketSampler.evaluate (rows (Nodes.height upper))
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut)
          (OwnInputRawAssembly.mergedTape projectedSlots rows upper lower W repeats cut sample) row)) := by
      rw [OwnInputRawAssembly.arrays_upper]
    _ = TensorBucketEvaluation.visibleOutput W
          (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2.1 +
        TensorBucketEvaluation.tensorOutput W
          (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputAffineSlice.hiddenOutput projectedSlots rows upper lower W repeats cut sample) := hsplit
    _ = _ := by
      rw [TensorProjectedSlice.totalMatrix_apply,
        TensorProjectedSlice.includedEvaluation_eq_tensorOutput, visibleMatrix_apply]
      rfl

end
end PerfectCompleteness.ProjectedRawAssembly


namespace PerfectCompleteness.HierarchicalProjectedRawPrediction

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (rows : Nat → Nat) (upper lower : Nodes branch n) (lowerLevel : Nat)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rowSpaceFintype
local instance valueFintype_r03a1b9_2 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
theorem rawJ_eq_tensorJ (sample : Raw projectedSlots rows upper lower A repeats cut) :
    rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut sample =
      tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut
        sample.2 (hidden projectedSlots rows upper lower A repeats cut sample) := by
  exact congrArg₂
    (fun (b : HierarchicalMatrixTable.Background (rows := rows) originalSlots upper)
        (X : HierarchicalMatrixTable.Matrix (rows := rows) originalSlots upper) =>
      GoodAdviceEvents.J
        (HierarchicalUsefulness.table originalSlots upper lowerLevel original originalArrays lowerEvent κ σ b)
        r ρ (A, HierarchicalPrediction.quotientMatrix originalSlots upper lowerLevel b X))
    (ProjectedRawAssembly.background_arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A) repeats cut sample)
    (ProjectedRawAssembly.matrix_arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A) repeats cut sample)

theorem rawJ_iff_restriction (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true)
    (sample : Raw projectedSlots rows upper lower A repeats cut) (hv : sample.2 = v) :
    rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut sample =
        true ↔
      TensorRestriction.restrictionMap
        (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood) (hidden projectedSlots rows upper lower A repeats cut sample) =
        target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne := by
  rw [rawJ_eq_tensorJ, hv]
  exact HierarchicalProjectedSlice.J_iff_restriction originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v)
    hgood hne _

theorem given_eq_jointEvent_oai (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true) :
    given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v =
      OwnInputAffineSlice.jointEvent projectedSlots rows upper lower (LinearMap.ker A) repeats cut
        (fun data => decide (data = v))
        (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne) := by
  funext sample
  by_cases hv : sample.2 = v
  · have hJ : rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut sample =
      OwnInputAffineSlice.tensorSlice (LinearMap.ker A)
        (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne) (hidden projectedSlots rows upper lower A repeats cut sample) := by
      apply Bool.eq_iff_iff.mpr
      simp only [OwnInputAffineSlice.tensorSlice, decide_eq_true_eq]
      exact rawJ_iff_restriction originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood hne sample hv
    unfold given OwnInputAffineSlice.jointEvent
    rw [hJ]
  · simp only [given, OwnInputAffineSlice.jointEvent, hv, decide_false, Bool.and_false]

end
end PerfectCompleteness.HierarchicalProjectedRawPrediction

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.given_eq_jointEvent_oai.{u_1} := @OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.given_eq_jointEvent_oai.{u_1}
