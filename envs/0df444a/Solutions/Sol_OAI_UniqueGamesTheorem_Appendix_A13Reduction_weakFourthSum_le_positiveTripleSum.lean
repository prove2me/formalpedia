-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.A13Reduction.weakFourthSum_le_positiveTripleSum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:17:02.263448+00:00
-- url     : https://prove2.me/submissions/0935e7b1-2c69-49c7-ac19-189da3b88cdb

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P011
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_A13Reduction_weighted_geometric_moment_le
import Theorems.Thm_OAI_UniqueGamesTheorem_Appendix_OperatorNorm_a4_fourth_average_le

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_FiberEnergyLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Finite Gram-energy estimates used in Lemma A.1. -/
namespace UniqueGamesTheorem.Appendix.F1Gram
open scoped BigOperators

theorem sum_subtype_eq {A : Type*} [Fintype A] (P : A → Prop)
    [DecidablePred P] (f : A → ℝ) :
    (∑ x : {x // P x}, f x) = ∑ x : A, if P x then f x else 0 := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter P, f x := by
      refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩
      · intro x _ y _ h
        exact Subtype.ext h
      · intro y hy
        exact ⟨⟨y, (Finset.mem_filter.mp hy).2⟩, Finset.mem_univ _, rfl⟩
      · intro x _
        rfl
    _ = _ := by rw [Finset.sum_filter]

theorem sum_comp_le {A B : Type*} [Fintype A] [Fintype B] (e : A → B)
    (he : Function.Injective e) (f : B → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image e, f b :=
      (Finset.sum_image (fun a _ b _ h => he h)).symm
    _ ≤ ∑ b ∈ Finset.univ, f b := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun b _ _ => hf b)

end UniqueGamesTheorem.Appendix.F1Gram

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_CompressionCountLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.CompressionCount

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

variable {U K C}

variable [FiniteDimensional F2 U] [FiniteDimensional F2 K]

theorem natCard_linearMap [FiniteDimensional F2 C] : Nat.card (U →ₗ[F2] C) =
    2 ^ (finrank F2 U * finrank F2 C) := by
  let e : (Fin (finrank F2 U) → C) ≃ (U →ₗ[F2] C) :=
    ((Module.finBasis F2 U).constr F2).toEquiv
  calc
    Nat.card (U →ₗ[F2] C) = Nat.card C ^ finrank F2 U := by
      rw [← Nat.card_congr e, Nat.card_fun, Nat.card_fin]
    _ = (2 ^ finrank F2 C) ^ finrank F2 U := by
      rw [Module.natCard_eq_pow_finrank (K := F2) (V := C)]
      simp [F2, Nat.card_eq_fintype_card]
    _ = 2 ^ (finrank F2 U * finrank F2 C) := by
      rw [← pow_mul, Nat.mul_comm]

end UniqueGamesTheorem.Appendix.CompressionCount

end

section

/-! The actual Appendix A.4 index encoding. Its kernel and range recover the
two subspaces, and its quotient relation recovers the linear map. The final
count follows from this injection into a genuine binary linear-map space. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A4IndexCount

section Generic

variable {K : Type*} [Field K]

theorem factorViaRange_apply {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) (u : U) :
    factorViaRange X P hker (X.rangeRestrict u) = P u := by
  have hq : X.quotKerEquivRange.symm (X.rangeRestrict u) = X.ker.mkQ u :=
    X.quotKerEquivRange.symm_apply_apply (X.ker.mkQ u)
  dsimp only [factorViaRange, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hq]
  rfl

theorem factorViaRange_injective {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker = P.ker) :
    Function.Injective (factorViaRange X P hker.le) := by
  intro a b hab
  obtain ⟨u, rfl⟩ := X.surjective_rangeRestrict a
  obtain ⟨v, rfl⟩ := X.surjective_rangeRestrict b
  rw [factorViaRange_apply, factorViaRange_apply] at hab
  have hp : u - v ∈ P.ker := by
    change P (u - v) = 0
    rw [map_sub, hab, sub_self]
  have hx : u - v ∈ X.ker := by rwa [hker]
  apply Subtype.ext
  apply sub_eq_zero.mp
  change X u - X v = 0
  simpa only [LinearMap.mem_ker, map_sub] using hx

theorem factorViaRange_range {U L T : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup L] [Module K L]
    [AddCommGroup T] [Module K T]
    (X : U →ₗ[K] L) (P : U →ₗ[K] T) (hker : X.ker ≤ P.ker) :
    (factorViaRange X P hker).range = P.range := by
  have hc : (factorViaRange X P hker).comp X.rangeRestrict = P := by
    apply LinearMap.ext
    intro u
    exact factorViaRange_apply X P hker u
  calc
    _ = ((factorViaRange X P hker).comp X.rangeRestrict).range :=
      (LinearMap.range_comp_of_range_eq_top _ X.range_rangeRestrict).symm
    _ = _ := congrArg LinearMap.range hc

variable {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem aToRange_surjective (A A0 : Submodule K V) (B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hR : X.range = A.map A0.mkQ) :
    Function.Surjective (aToRange A A0 B0 X hR) := by
  intro c
  have hc : (c : V ⧸ A0) ∈ A.map A0.mkQ := by rw [← hR]; exact c.property
  rcases Submodule.mem_map.mp hc with ⟨a, ha, he⟩
  exact ⟨⟨a, ha⟩, Subtype.ext he⟩

theorem encodeFixed_relation (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (a : A) (b : B0) :
    encodeFixed A A0 B B0 X hK hR a = B.mkQ (b : W) ↔ A0.mkQ (a : V) = X b := by
  let P := quotientRestriction B B0
  have hXP : X.ker = P.ker := hK.trans (ker_quotientRestriction B B0).symm
  change factorViaRange X P hXP.le (aToRange A A0 B0 X hR a) = P b ↔ _
  rw [← factorViaRange_apply X P hXP.le b,
    (factorViaRange_injective X P hXP).eq_iff]
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

theorem ker_encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) :
    (encodeFixed A A0 B B0 X hK hR).ker = A0.comap A.subtype := by
  ext a
  have h := encodeFixed_relation A A0 B B0 X hK hR a (0 : B0)
  simpa using h

theorem range_encodeFixed (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) :
    (encodeFixed A A0 B B0 X hK hR).range = (quotientRestriction B B0).range := by
  rw [encodeFixed, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (aToRange_surjective A A0 B0 X hR))]
  exact factorViaRange_range _ _ _

theorem recover_A0 (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (hA : A0 ≤ A) :
    (encodeFixed A A0 B B0 X hK hR).ker.map A.subtype = A0 := by
  rw [ker_encodeFixed]
  ext a
  constructor
  · intro ha
    rcases Submodule.mem_map.mp ha with ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    exact Submodule.mem_map.mpr ⟨⟨a, hA ha⟩, ha, rfl⟩

theorem recover_B0 (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X : B0 →ₗ[K] (V ⧸ A0)) (hK : X.ker = B.comap B0.subtype)
    (hR : X.range = A.map A0.mkQ) (hB : B ≤ B0) :
    (encodeFixed A A0 B B0 X hK hR).range.comap B.mkQ = B0 := by
  rw [range_encodeFixed]
  ext w
  change B.mkQ w ∈ (quotientRestriction B B0).range ↔ w ∈ B0
  constructor
  · rintro ⟨b, hb⟩
    change B.mkQ (b : W) = B.mkQ w at hb
    have hm : w - (b : W) ∈ B := by
      apply (Submodule.Quotient.mk_eq_zero B).mp
      change B.mkQ (w - (b : W)) = 0
      rw [map_sub, hb, sub_self]
    simpa only [sub_add_cancel] using B0.add_mem (hB hm) b.property
  · intro hw
    exact ⟨⟨w, hw⟩, rfl⟩

theorem encodeFixed_injective (A A0 : Submodule K V) (B B0 : Submodule K W)
    (X X' : B0 →ₗ[K] (V ⧸ A0))
    (hK : X.ker = B.comap B0.subtype) (hR : X.range = A.map A0.mkQ)
    (hK' : X'.ker = B.comap B0.subtype) (hR' : X'.range = A.map A0.mkQ)
    (h : encodeFixed A A0 B B0 X hK hR = encodeFixed A A0 B B0 X' hK' hR') : X = X' := by
  apply LinearMap.ext
  intro b
  have hb : X b ∈ A.map A0.mkQ := by rw [← hR]; exact ⟨b, rfl⟩
  rcases Submodule.mem_map.mp hb with ⟨a, ha, he⟩
  have henc : encodeFixed A A0 B B0 X hK hR ⟨a, ha⟩ = B.mkQ (b : W) :=
    (encodeFixed_relation A A0 B B0 X hK hR ⟨a, ha⟩ b).mpr he
  have henc' : encodeFixed A A0 B B0 X' hK' hR' ⟨a, ha⟩ = B.mkQ (b : W) := by
    rw [← h]
    exact henc
  exact he.symm.trans
    ((encodeFixed_relation A A0 B B0 X' hK' hR' ⟨a, ha⟩ b).mp henc')

theorem encode_injective (A : Submodule K V) (B : Submodule K W) :
    Function.Injective (encode A B) := by
  rintro ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩ ⟨⟨A0', B0', X'⟩, hA', hB', hK', hR'⟩ h
  change encodeFixed A A0 B B0 X hK hR = encodeFixed A A0' B B0' X' hK' hR' at h
  have hAeq : A0 = A0' := by
    calc
      A0 = (encodeFixed A A0 B B0 X hK hR).ker.map A.subtype :=
        (recover_A0 A A0 B B0 X hK hR hA).symm
      _ = (encodeFixed A A0' B B0' X' hK' hR').ker.map A.subtype :=
        congrArg (fun T : A →ₗ[K] (W ⧸ B) => T.ker.map A.subtype) h
      _ = A0' := recover_A0 A A0' B B0' X' hK' hR' hA'
  have hBeq : B0 = B0' := by
    calc
      B0 = (encodeFixed A A0 B B0 X hK hR).range.comap B.mkQ :=
        (recover_B0 A A0 B B0 X hK hR hB).symm
      _ = (encodeFixed A A0' B B0' X' hK' hR').range.comap B.mkQ :=
        congrArg (fun T : A →ₗ[K] (W ⧸ B) => T.range.comap B.mkQ) h
      _ = B0' := recover_B0 A A0' B B0' X' hK' hR' hB'
  cases hAeq
  cases hBeq
  have hXeq := encodeFixed_injective A A0 B B0 X X' hK hR hK' hR' h
  cases hXeq
  rfl

end Generic

section Binary

open Integration.BinaryLinear

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem card_index_le (A : Submodule F2 V) (B : Submodule F2 W) :
    Nat.card (Index A B) ≤
      2 ^ (Module.finrank F2 A * Module.finrank F2 (W ⧸ B)) := by
  have hc := CompressionCount.natCard_linearMap (U := A) (C := W ⧸ B)
  let : Finite (A →ₗ[F2] (W ⧸ B)) := Nat.finite_of_card_ne_zero (by
    rw [hc]
    exact pow_ne_zero _ (by decide))
  have h := Nat.card_le_card_of_injective (encode A B) (encode_injective A B)
  rwa [hc] at h

end Binary

end UniqueGamesTheorem.Appendix.A4IndexCount

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_HybridCompositionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities

namespace UniqueGamesTheorem.Appendix.A13Reduction

attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem tripleMoment_nonneg (p : A4Index (K := F2) (W := F) (V := E))
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ tripleMoment p f := by
  apply Finset.expect_nonneg
  intro T _
  apply Finset.expect_nonneg
  intro N _
  positivity

/-- A.4's native fourth-moment bound with its proved binary index count. -/
theorem weak_fourth_le_counted (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
      (2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) *
        ∑ p : A4GeometricIndex A B, tripleMoment p.val f := by
  have hnat := Nat.pow_le_pow_left (A4IndexCount.card_index_le A B) 3
  rw [Nat.card_eq_fintype_card, ← pow_mul] at hnat
  have he : (Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * 3 =
      3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B) := by ring
  rw [he] at hnat
  have hc : (Fintype.card (A4GeometricIndex A B) : ℝ) ^ 3 ≤
      (2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) := by
    exact_mod_cast hnat
  have hn : 0 ≤ ∑ p : A4GeometricIndex A B, tripleMoment p.val f :=
    Finset.sum_nonneg fun p _ => tripleMoment_nonneg p.val f
  exact (OperatorNorm.a4_fourth_average_le A B f).trans
    (mul_le_mul_of_nonneg_right hc hn)

/-- Expand one original weak-pair term, retaining its original dimensions. -/
theorem weighted_weak_fourth_le_counted (d : ℕ)
    (A : Submodule F2 E) (B : Submodule F2 F)
    [Fintype (A4GeometricIndex A B)] (f : (E →ₗ[F2] F) → ℝ) :
    (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B))) *
      (𝔼 M, spectralProjector (fun Y => A ≤ Y.range ∧ Y.ker ≤ B) f M ^ 4) ≤
    ∑ p : A4GeometricIndex A B,
      (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B)) +
        3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) * tripleMoment p.val f := by
  calc
    _ ≤ (2 : ℝ) ^ (7 * d * (Module.finrank F2 A + Module.finrank F2 (F ⧸ B))) *
        ((2 : ℝ) ^ (3 * Module.finrank F2 A * Module.finrank F2 (F ⧸ B)) *
          ∑ p : A4GeometricIndex A B, tripleMoment p.val f) :=
      mul_le_mul_of_nonneg_left (weak_fourth_le_counted A B f) (by positivity)
    _ = _ := by simp only [pow_add, Finset.mul_sum, mul_assoc]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
theorem tripleTerm_nonneg (d : ℕ) (p : A13Index.Triple (E := E) (F := F))
    (f : (E →ₗ[F2] F) → ℝ) : 0 ≤ tripleTerm d p f :=
  mul_nonneg (by positivity) (tripleMoment_nonneg p f)

variable [Fintype (Submodule F2 E)] [Fintype (Submodule F2 F)]

/-- Apply A.4 and its count, then forget the uniquely reconstructible weak pair.
The old nonzero condition is carried by `positiveMap`; no descendant condition
is substituted for it. -/
theorem weakFourthSum_le_positiveTripleSum_oai (f : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hf : DerivativeDegree.DegreeAtMost d f) :
    A1Reduction.weakFourthSum d f ≤ positiveTripleSum d f := by
  classical
  have heq : A1Reduction.weakFourthSum d f =
      ∑ p : A13Index.WeakPositive (E := E) (F := F),
        (2 : ℝ) ^ (7 * d * (Module.finrank F2 p.val.1 +
          Module.finrank F2 (F ⧸ p.val.2))) *
          (𝔼 M, spectralProjector
            (fun Y => p.val.1 ≤ Y.range ∧ Y.ker ≤ p.val.2) f M ^ 4) := by
    symm
    exact F1Gram.sum_subtype_eq
      (fun p : Submodule F2 E × Submodule F2 F => p ≠ (⊥, ⊤))
      (fun p => (2 : ℝ) ^ (7 * d * (Module.finrank F2 p.1 +
        Module.finrank F2 (F ⧸ p.2))) *
        (𝔼 M, spectralProjector (fun Y => p.1 ≤ Y.range ∧ Y.ker ≤ p.2) f M ^ 4))
  rw [heq]
  calc
    _ ≤ ∑ p : A13Index.WeakPositive (E := E) (F := F),
        ∑ q : A4GeometricIndex p.val.1 p.val.2, tripleTerm d q.val f := by
      apply Finset.sum_le_sum
      intro p _
      exact (weighted_weak_fourth_le_counted d p.val.1 p.val.2 f).trans
        (Finset.sum_le_sum fun q _ => weighted_geometric_moment_le p.val.1 p.val.2 q f hf)
    _ = ∑ w : A13Index.PositiveWitness (E := E) (F := F),
        tripleTerm d w.2.val f := by
      simp only [Fintype.sum_sigma]
    _ ≤ positiveTripleSum d f :=
      F1Gram.sum_comp_le A13Index.positiveMap A13Index.positiveMap_injective
        (fun q : A13Index.PositiveTriple (E := E) (F := F) => tripleTerm d q.val f)
        (fun q => tripleTerm_nonneg d q.val f)

end UniqueGamesTheorem.Appendix.A13Reduction

end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.UniqueGamesTheorem.Appendix.A13Reduction.weakFourthSum_le_positiveTripleSum_oai.{u_1, u_2} := @OAI.UniqueGamesTheorem.Appendix.A13Reduction.weakFourthSum_le_positiveTripleSum_oai.{u_1, u_2}
