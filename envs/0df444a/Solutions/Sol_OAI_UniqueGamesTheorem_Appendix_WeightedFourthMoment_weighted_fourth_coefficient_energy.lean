-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Appendix.WeightedFourthMoment.weighted_fourth_coefficient_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:35.436203+00:00
-- url     : https://prove2.me/submissions/b7e2532f-7e8d-40d0-b27b-30eac296ec5f

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Std
import Definitions.Def_OAIQ252P006

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_FiberEnergyLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Energy after merging a bounded number of frequencies

This finite ordered-ring theorem supplies the Cauchy–Schwarz step in (A.10).
Its fiber-cardinality hypothesis is explicit.
-/

namespace UniqueGamesTheorem.Appendix.FiberEnergy

open scoped BigOperators

variable {α β R : Type*} [Fintype β] [DecidableEq β] [CommRing R] [LinearOrder R]
  [IsStrictOrderedRing R]

/-- The energy of a sum of merged coefficients is bounded by the largest
fiber size times the original coefficient energy. Signs and cancellations
are unrestricted; no injectivity assumption is made. -/
theorem finite_fiber_energy (s : Finset α) (compress : α → β) (a : α → R)
    (bound : R) (hbound : ∀ z,
      ((s.filter (fun y => compress y = z)).card : R) ≤ bound) :
    (∑ z, (∑ y ∈ s.filter (fun y => compress y = z), a y) ^ 2) ≤
      bound * ∑ y ∈ s, a y ^ 2 := by
  classical
  have hlocal (z : β) :
      (∑ y ∈ s.filter (fun y => compress y = z), a y) ^ 2 ≤
        bound * ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (s.filter (fun y => compress y = z)) (fun _ => (1 : R)) a
    calc
      _ ≤ ((s.filter (fun y => compress y = z)).card : R) *
          ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 := by simpa using hc
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound z)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ z, bound * ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 :=
      Finset.sum_le_sum (fun z _ => hlocal z)
    _ = bound * ∑ y ∈ s, a y ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise]

end UniqueGamesTheorem.Appendix.FiberEnergy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_CompressionCountLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
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

theorem card_parameters (Z : K →ₗ[F2] C) : Nat.card (Parameters (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [Nat.card_prod, natCard_linearMap, natCard_linearMap, ← pow_add]
  congr 1
  ring

theorem fiber_remainder_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 (Y.val - base U K C).range = finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := (toFiber_bijective Z).2 Y
  have hY : lift Z P = Y.val := congrArg Subtype.val hP
  rw [← hY, range_lift_sub_base]
  exact LinearMap.finrank_range_of_inj (graph_injective Z P.1)

theorem fiber_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 Y.val.range = finrank F2 U + finrank F2 Z.range := by
  rw [Y.property.1, fiber_remainder_rank]

/-- Lemma A.2 in arbitrary finite-dimensional block coordinates. -/
theorem card_fiber (Z : K →ₗ[F2] C) : Nat.card (Fiber (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [← Nat.card_congr (fiberEquiv (U := U) Z)]
  exact card_parameters Z

end UniqueGamesTheorem.Appendix.CompressionCount

end

section

namespace UniqueGamesTheorem.Appendix.CoordinateTransport

noncomputable section

variable {𝕜 E F : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

theorem finrank_comp_equiv {G : Type*} [AddCommGroup G] [Module 𝕜 G]
    (q : F ≃ₗ[𝕜] G) (Y : E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (q.toLinearMap.comp Y).range = Module.finrank 𝕜 Y.range := by
  have h := finrank_range_transport (LinearEquiv.refl 𝕜 E) q Y
  exact h

end

end UniqueGamesTheorem.Appendix.CoordinateTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_SubspaceCountingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite-field subspace cardinality bounds used in Appendix A.4. The objects
counted here are actual mathlib submodules, not encoded cardinality assumptions.
-/

namespace UniqueGamesTheorem.Appendix.SubspaceCounting

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V]

variable {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]

omit [Module.Finite K V] in
/-- Evaluating on a basis bounds the number of linear maps without counting
arbitrary functions on every vector. -/
theorem card_linearMaps_le [Finite V] :
    Nat.card (U →ₗ[K] V) ≤ Nat.card V ^ finrank K U := by
  let b := Module.finBasis K U
  let code : (U →ₗ[K] V) → (Fin (finrank K U) → V) := fun f i => f (b i)
  have hi : Function.Injective code := by
    intro f g h
    apply b.ext
    exact congrFun h
  simpa only [Nat.card_fun, Nat.card_fin] using Nat.card_le_card_of_injective code hi

omit [Module.Finite K V] in
/-- Every rank-k map factors through the actual coordinate vector space K^k. -/
theorem exists_rank_factorization (f : U →ₗ[K] V) (k : ℕ)
    (hk : finrank K (LinearMap.range f) = k) :
    ∃ (a : (Fin k → K) →ₗ[K] V) (b : U →ₗ[K] (Fin k → K)), a.comp b = f := by
  let e := (Module.finBasisOfFinrankEq K (LinearMap.range f) hk).equivFun
  refine ⟨(LinearMap.range f).subtype.comp e.symm.toLinearMap,
    e.toLinearMap.comp f.rangeRestrict, ?_⟩
  ext x
  simp

/-- Rank-k maps between r- and s-dimensional spaces number at most |K|^((r+s)k).
This is a general finite-field bound, proved by selecting the preceding
factorization and injecting into the pair of factor maps. -/
theorem card_rank_maps_le [Finite K] (k : ℕ) :
    Nat.card {f : U →ₗ[K] V // finrank K (LinearMap.range f) = k} ≤
      Nat.card K ^ ((finrank K U + finrank K V) * k) := by
  classical
  let : Finite U := Finite.of_injective (Module.finBasis K U).equivFun
    (Module.finBasis K U).equivFun.injective
  let : Finite V := Finite.of_injective (Module.finBasis K V).equivFun
    (Module.finBasis K V).equivFun.injective
  let A := (Fin k → K) →ₗ[K] V
  let B := U →ₗ[K] (Fin k → K)
  let : Finite A := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let : Finite B := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have hf (f : {f : U →ₗ[K] V // finrank K (LinearMap.range f) = k}) :
      ∃ p : A × B, p.1.comp p.2 = f.1 := by
    obtain ⟨a, b, h⟩ := exists_rank_factorization f.1 k f.2
    exact ⟨(a, b), h⟩
  let code := fun f => Classical.choose (hf f)
  have hi : Function.Injective code := by
    intro f g h
    apply Subtype.ext
    calc
      f.1 = (code f).1.comp (code f).2 := (Classical.choose_spec (hf f)).symm
      _ = (code g).1.comp (code g).2 := congrArg (fun p : A × B => p.1.comp p.2) h
      _ = g.1 := Classical.choose_spec (hf g)
  calc
    _ ≤ Nat.card (A × B) := Nat.card_le_card_of_injective code hi
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _
    _ ≤ Nat.card V ^ k * (Nat.card K ^ k) ^ finrank K U := by
      apply Nat.mul_le_mul
      · simpa [A] using card_linearMaps_le (K := K) (U := Fin k → K) (V := V)
      · simpa [B, Nat.card_fun] using
          card_linearMaps_le (K := K) (U := U) (V := Fin k → K)
    _ = Nat.card K ^ ((finrank K U + finrank K V) * k) := by
      rw [Module.natCard_eq_pow_finrank (K := K) (V := V)]
      simp only [← pow_mul, ← pow_add]
      congr 1
      simp [Nat.mul_add, Nat.mul_comm, Nat.add_comm]

omit [Module.Finite K V] [Module.Finite K U] in
theorem rank_quotientImageMap (Y X : U →ₗ[K] V)
    (hker : LinearMap.ker Y ≤ LinearMap.ker X)
    (himage : LinearMap.range X ≤ LinearMap.range Y) :
    finrank K (LinearMap.range (quotientImageMap Y X hker himage)) =
      finrank K (LinearMap.range X) := by
  rw [← Submodule.finrank_map_subtype_eq (LinearMap.range Y), ← LinearMap.range_comp]
  change finrank K (LinearMap.range ((LinearMap.ker Y).liftQ X hker)) = _
  rw [Submodule.range_liftQ]

omit [Module.Finite K V] in
/-- General ambient-independent rank-k bound for maps constrained by the image
and kernel of Y. This counts actual linear maps; neither cardinality nor
rank-additive predecessor estimates are supplied as hypotheses. -/
theorem card_constrained_maps_le [Finite K] (Y : U →ₗ[K] V) (k : ℕ) :
    Nat.card {X : U →ₗ[K] V // finrank K (LinearMap.range X) = k ∧
      LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} ≤
      Nat.card K ^ (2 * finrank K (LinearMap.range Y) * k) := by
  classical
  let : Finite (LinearMap.range Y) := Finite.of_injective
    (Module.finBasis K (LinearMap.range Y)).equivFun
    (Module.finBasis K (LinearMap.range Y)).equivFun.injective
  let : Finite (U ⧸ LinearMap.ker Y) := Finite.of_injective
    (Module.finBasis K (U ⧸ LinearMap.ker Y)).equivFun
    (Module.finBasis K (U ⧸ LinearMap.ker Y)).equivFun.injective
  let : Finite ((U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let code (X : {X : U →ₗ[K] V // finrank K (LinearMap.range X) = k ∧
      LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y}) :
      {f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y //
        finrank K (LinearMap.range f) = k} :=
    ⟨quotientImageMap Y X.1 X.2.2.1 X.2.2.2,
      (rank_quotientImageMap Y X.1 X.2.2.1 X.2.2.2).trans X.2.1⟩
  have hi : Function.Injective code := by
    intro X Z h
    apply Subtype.ext
    ext u
    have he := congrArg
      (fun f => ((f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y)
        ((LinearMap.ker Y).mkQ u) : V)) (congrArg Subtype.val h)
    exact he
  have hdim : finrank K (U ⧸ LinearMap.ker Y) = finrank K (LinearMap.range Y) := by
    have hq := (LinearMap.ker Y).finrank_quotient_add_finrank
    have hr := Y.finrank_range_add_finrank_ker
    omega
  calc
    _ ≤ Nat.card {f : (U ⧸ LinearMap.ker Y) →ₗ[K] LinearMap.range Y //
        finrank K (LinearMap.range f) = k} := Nat.card_le_card_of_injective code hi
    _ ≤ Nat.card K ^ ((finrank K (U ⧸ LinearMap.ker Y) +
        finrank K (LinearMap.range Y)) * k) :=
      card_rank_maps_le (K := K) (U := U ⧸ LinearMap.ker Y) (V := LinearMap.range Y) k
    _ = _ := by rw [hdim, ← two_mul]

section BinaryPredecessors

variable {U V : Type*} [AddCommGroup U] [AddCommGroup V]
  [Module (ZMod 2) U] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) U] [Module.Finite (ZMod 2) V]

omit [Module.Finite (ZMod 2) U] [Module.Finite (ZMod 2) V] in
theorem binary_add_cancel (X Y : U →ₗ[ZMod 2] V) : X + (Y + X) = Y := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hself (x : V) : x + x = 0 := by
    rw [← two_smul (ZMod 2) x, htwo, zero_smul]
  ext u
  change X u + (Y u + X u) = Y u
  rw [add_comm (Y u) (X u), ← add_assoc, hself, zero_add]

theorem card_binary_predecessors_le (Y : U →ₗ[ZMod 2] V) (d k : ℕ)
    (hd : finrank (ZMod 2) (LinearMap.range Y) ≤ d) :
    Nat.card {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
      finrank (ZMod 2) (LinearMap.range Y) =
        finrank (ZMod 2) (LinearMap.range X) +
        finrank (ZMod 2) (LinearMap.range (Y + X))} ≤ 2 ^ (3 * d * k) := by
  classical
  let : Finite U := Finite.of_injective (Module.finBasis (ZMod 2) U).equivFun
    (Module.finBasis (ZMod 2) U).equivFun.injective
  let : Finite V := Finite.of_injective (Module.finBasis (ZMod 2) V).equivFun
    (Module.finBasis (ZMod 2) V).equivFun.injective
  let : Finite (U →ₗ[ZMod 2] V) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let code (X : {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
      finrank (ZMod 2) (LinearMap.range Y) =
        finrank (ZMod 2) (LinearMap.range X) +
        finrank (ZMod 2) (LinearMap.range (Y + X))}) :
      {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
        LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} := by
    have hr : finrank (ZMod 2) (LinearMap.range (X.1 + (Y + X.1))) =
        finrank (ZMod 2) (LinearMap.range X.1) +
        finrank (ZMod 2) (LinearMap.range (Y + X.1)) := by
      rw [binary_add_cancel]
      exact X.2.2
    refine ⟨X.1, X.2.1, ?_, ?_⟩
    · simpa only [binary_add_cancel] using
        RankAdditivity.ker_add_le_ker_left X.1 (Y + X.1) hr
    · simpa only [binary_add_cancel] using
        RankAdditivity.range_left_le_range_add X.1 (Y + X.1) hr
  have hi : Function.Injective code := by
    intro X Z h
    apply Subtype.ext
    change (code X).1 = (code Z).1
    exact congrArg Subtype.val h
  calc
    _ ≤ Nat.card {X : U →ₗ[ZMod 2] V // finrank (ZMod 2) (LinearMap.range X) = k ∧
        LinearMap.ker Y ≤ LinearMap.ker X ∧ LinearMap.range X ≤ LinearMap.range Y} :=
      Nat.card_le_card_of_injective code hi
    _ ≤ Nat.card (ZMod 2) ^ (2 * finrank (ZMod 2) (LinearMap.range Y) * k) :=
      card_constrained_maps_le (K := ZMod 2) Y k
    _ = 2 ^ (2 * finrank (ZMod 2) (LinearMap.range Y) * k) := by simp
    _ ≤ 2 ^ (3 * d * k) := by
      apply Nat.pow_le_pow_right (by decide)
      apply Nat.mul_le_mul_right
      omega

end BinaryPredecessors

end UniqueGamesTheorem.Appendix.SubspaceCounting

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_AntecedentCountLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact compression fibers for arbitrary binary linear maps

This is the general cardinality assertion in Lemma A.2, with the actual kernel
restriction and range quotient. The map X is arbitrary; no chosen-coordinate
or fixed-dimension hypothesis occurs in `card_fiber`.
-/

namespace UniqueGamesTheorem.Appendix.FullCompression

open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.CoordinateTransport
open Module

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
/-- Lemma A.2: every compressed rank-r map has exactly `2^(2*k*r)`
rank-additive lifts above an arbitrary rank-k map X. -/
theorem card_fiber (X : E →ₗ[F2] F) (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :
    Nat.card (Fiber X Z) = 2 ^ (2 * finrank F2 X.range * finrank F2 Z.range) := by
  obtain ⟨P, hP⟩ := X.ker.exists_isCompl
  obtain ⟨C, hC⟩ := X.range.exists_isCompl
  rw [Nat.card_congr (fiberEquiv X Z P hP C hC), CompressionCount.card_fiber,
    finrank_comp_equiv]

omit [FiniteDimensional F2 F] in
/-- Every member of a compression fiber has rank `rank X + rank Z`. -/
theorem fiber_rank (X : E →ₗ[F2] F)
    (Z : X.ker →ₗ[F2] (F ⧸ X.range)) (Y : Fiber X Z) :
    finrank F2 Y.val.range = finrank F2 X.range + finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := X.ker.exists_isCompl
  obtain ⟨C, hC⟩ := X.range.exists_isCompl
  have h := CompressionCount.fiber_rank
    ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z)
    ((fiberEquiv X Z P hP C hC) Y)
  change finrank F2 (toBlocks X P hP C hC Y.val).range =
    finrank F2 X.range +
      finrank F2 ((X.range.quotientEquivOfIsCompl C hC).toLinearMap.comp Z).range at h
  rw [finrank_toBlocks, finrank_comp_equiv] at h
  exact h

end

end UniqueGamesTheorem.Appendix.FullCompression

end

section

/-! Exact coefficient-energy estimate underlying (A.10), with genuine
binary linear maps, their rank-additive order and quotient compression. -/
namespace UniqueGamesTheorem.Appendix.DerivativeEnergy

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity (RankBelow)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

omit [FiniteDimensional F2 F] in
theorem supported_fiber_energy (X : E →ₗ[F2] F)
    [Fintype (X.ker →ₗ[F2] (F ⧸ X.range))]
    (s : Finset (E →ₗ[F2] F)) (a : (E →ₗ[F2] F) → ℝ) (d : Nat)
    (hs : ∀ Y ∈ s, RankBelow X Y ∧ finrank F2 Y.range ≤ d) :
    (∑ Z, (∑ Y ∈ s.filter (fun Y => FullCompression.compression X Y = Z), a Y)^2) ≤
      (2 : ℝ)^(2 * finrank F2 X.range * (d - finrank F2 X.range)) *
        ∑ Y ∈ s, a Y^2 := by
  classical
  apply FiberEnergy.finite_fiber_energy
  intro Z
  let t := s.filter (fun Y => FullCompression.compression X Y = Z)
  by_cases ht : t.Nonempty
  · obtain ⟨Y, hY⟩ := ht
    have hy := Finset.mem_filter.mp hY
    have hys := hs Y hy.1
    let yz : FullCompression.Fiber X Z := ⟨Y, hys.1, hy.2⟩
    have hr := FullCompression.fiber_rank X Z yz
    have hz : finrank F2 Z.range ≤ d - finrank F2 X.range := by
      change finrank F2 Y.range = finrank F2 X.range + finrank F2 Z.range at hr
      omega
    let emb : ↥t → FullCompression.Fiber X Z := fun y =>
      ⟨y.val, (hs y.val (Finset.mem_filter.mp y.property).1).1,
        (Finset.mem_filter.mp y.property).2⟩
    have hemb : Function.Injective emb := by
      intro y y' h
      have hv : y.val = y'.val :=
        congrArg (fun z : FullCompression.Fiber X Z => z.val) h
      exact Subtype.ext hv
    let : Finite (FullCompression.Fiber X Z) :=
      Finite.of_injective (fun z : FullCompression.Fiber X Z => z.val)
        (fun _ _ h => Subtype.ext h)
    have hc : t.card ≤ Nat.card (FullCompression.Fiber X Z) := by
      have h := Nat.card_le_card_of_injective emb hemb
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h
    rw [FullCompression.card_fiber X Z] at hc
    have hpow := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2)
      (Nat.mul_le_mul_left (2 * finrank F2 X.range) hz)
    have hnat : t.card ≤ 2^(2 * finrank F2 X.range * (d - finrank F2 X.range)) :=
      hc.trans hpow
    exact_mod_cast hnat
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change (t.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity

omit [FiniteDimensional F2 F] in
/-- The precise merged-coefficient form of (A.10). Coefficients are arbitrary
real numbers with the stated degree support, not assumed nonnegative. -/
theorem coefficient_energy (X : E →ₗ[F2] F)
    [Fintype (X.ker →ₗ[F2] (F ⧸ X.range))]
    (a : (E →ₗ[F2] F) → ℝ) (d : Nat)
    (hdegree : ∀ Y, d < finrank F2 Y.range → a Y = 0) :
    (∑ Z, (∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z
      then a Y else 0)^2) ≤
      (2 : ℝ)^(2 * finrank F2 X.range * (d - finrank F2 X.range)) *
        ∑ Y, if RankBelow X Y then a Y^2 else 0 := by
  classical
  let s := Finset.univ.filter (fun Y : E →ₗ[F2] F =>
    RankBelow X Y ∧ finrank F2 Y.range ≤ d)
  have hs : ∀ Y ∈ s, RankBelow X Y ∧ finrank F2 Y.range ≤ d := by
    intro Y hY
    exact (Finset.mem_filter.mp hY).2
  have hsum (Z : X.ker →ₗ[F2] (F ⧸ X.range)) :
      (∑ Y ∈ s.filter (fun Y => FullCompression.compression X Y = Z), a Y) =
        ∑ Y, if RankBelow X Y ∧ FullCompression.compression X Y = Z then a Y else 0 := by
    simp only [s, Finset.filter_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hy : finrank F2 Y.range ≤ d
    · by_cases ho : RankBelow X Y <;> simp [hy, ho]
    · have ha : a Y = 0 := hdegree Y (Nat.lt_of_not_ge hy)
      simp [ha]
  have henergy : (∑ Y ∈ s, a Y^2) =
      ∑ Y, if RankBelow X Y then a Y^2 else 0 := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro Y _
    by_cases hy : finrank F2 Y.range ≤ d
    · by_cases ho : RankBelow X Y <;> simp [hy, ho]
    · have ha : a Y = 0 := hdegree Y (Nat.lt_of_not_ge hy)
      simp [ha]
  simpa only [hsum, henergy] using supported_fiber_energy X s a d hs

end UniqueGamesTheorem.Appendix.DerivativeEnergy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_WeightedFourthMoment
attribute [-instance] _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The corrected weighted fourth coefficient-energy estimate of Appendix A.4.
The proof uses the actual compression-fiber energy theorem and the actual
rank-additive predecessor count, not hypotheses replacing either result.
The remaining Fourier interpretation is separate: `energy a X` is the sum of
squares of coefficients after the actual derivative compression.
-/

noncomputable section
namespace UniqueGamesTheorem.Appendix.WeightedFourthMoment

open Module
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankAdditivity (RankBelow)
attribute [local instance] Classical.propDecidable

private lemma half_cancel (a b : ℕ) :
    (2:ℝ)^a * ((2:ℝ)⁻¹)^(a+b) = ((2:ℝ)⁻¹)^b := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  norm_num

private lemma half_sum_identity (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2:ℝ)⁻¹)^k) + 2*((2:ℝ)⁻¹)^n = 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    norm_num at *
    linarith

private lemma half_sum_le (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2:ℝ)⁻¹)^k) ≤ 2 := by
  have hid := half_sum_identity n
  have hp : 0 ≤ ((2:ℝ)⁻¹)^n := by positivity
  linarith

private lemma finite_level_sum {α : Type*} (s : Finset α) (r : α → ℕ) (d : ℕ)
    (hdeg : ∀ x ∈ s, r x ≤ d)
    (hc : ∀ k, ((s.filter (fun x => r x=k)).card : ℝ) ≤ (2:ℝ)^(3*d*k)) :
    (∑ x ∈ s, ((2:ℝ)⁻¹)^(4*d*r x)) ≤ 2 := by
  classical
  have hmap : ∀ x ∈ s, r x ∈ Finset.range (d+1) := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hdeg x hx))
  have hone (n : ℕ) : ((2:ℝ)⁻¹)^n ≤ 1 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ]
      have hn : 0 ≤ ((2:ℝ)⁻¹)^n := by positivity
      norm_num at *
      nlinarith
  calc
    _ = ∑ k ∈ Finset.range (d+1), ∑ x ∈ s.filter (fun x => r x=k),
        ((2:ℝ)⁻¹)^(4*d*r x) :=
      (Finset.sum_fiberwise_of_maps_to (g := r) hmap _).symm
    _ ≤ ∑ k ∈ Finset.range (d+1), ((2:ℝ)⁻¹)^k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hmul : k ≤ d*k := by
        by_cases hd : d=0
        · subst d
          have : k=0 := by omega
          simp [this]
        · have : 1 ≤ d := by omega
          simpa using Nat.mul_le_mul_right k this
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hmul
      have hdecay : ((2:ℝ)⁻¹)^(d*k) ≤ ((2:ℝ)⁻¹)^k := by
        rw [hj, pow_add]
        simpa using mul_le_mul_of_nonneg_left (hone j)
          (by positivity : 0 ≤ ((2:ℝ)⁻¹)^k)
      calc
        _ = ((s.filter (fun x => r x=k)).card : ℝ)*((2:ℝ)⁻¹)^(4*d*k) := by
          calc
            _ = ∑ x ∈ s.filter (fun x => r x=k), ((2:ℝ)⁻¹)^(4*d*k) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [(Finset.mem_filter.mp hx).2]
            _ = _ := by simp
        _ ≤ (2:ℝ)^(3*d*k)*((2:ℝ)⁻¹)^(4*d*k) :=
          mul_le_mul_of_nonneg_right (hc k) (by positivity)
        _ = ((2:ℝ)⁻¹)^(d*k) := by
          have he : 4*d*k=3*d*k+d*k := by simp only [Nat.mul_assoc]; omega
          rw [he, half_cancel]
        _ ≤ _ := hdecay
    _ ≤ 2 := half_sum_le (d+1)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

/-- Sum of predecessor weights, using the actual binary linear-map count. -/
theorem predecessor_weight_sum (Y : E →ₗ[F2] F) (d : ℕ) (hd : rank Y ≤ d) :
    (∑ X ∈ Finset.univ.filter (fun X => RankBelow X Y),
      ((2:ℝ)⁻¹)^(4*d*rank X)) ≤ 2 := by
  classical
  apply finite_level_sum _ rank d
  · intro X hX
    have hp := (Finset.mem_filter.mp hX).2
    change rank Y = rank X + rank (Y-X) at hp
    omega
  · intro k
    have hneg (X : E →ₗ[F2] F) : -X = X := by
      have htwo : (1+1:F2)=0 := by decide
      have hxx : X+X=0 := by
        have h := congrArg (fun c:F2 => c • X) htwo
        simpa only [add_smul, one_smul, zero_smul] using h
      exact neg_eq_iff_add_eq_zero.mpr hxx
    have hpred (X : E →ₗ[F2] F) : RankBelow X Y ↔
        rank Y = rank X + rank (Y+X) := by
      change (rank Y = rank X + rank (Y-X)) ↔ _
      rw [sub_eq_add_neg, hneg X]
    have hc := SubspaceCounting.card_binary_predecessors_le Y d k hd
    have hn : ((Finset.univ.filter (fun X => RankBelow X Y)).filter
        (fun X => rank X=k)).card ≤ 2^(3*d*k) := by
      simp_rw [hpred]
      simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_filter,
        and_comm, rank] using hc
    exact_mod_cast hn

/-- Corrected Appendix A.4, in exact coefficient form, for arbitrary real
coefficients supported on maps of rank at most d. -/
theorem weighted_fourth_coefficient_energy_oai (a : (E →ₗ[F2] F) → ℝ) (d : ℕ)
    (hdegree : ∀ Y, d < rank Y → a Y = 0) :
    (∑ X, ((2:ℝ)⁻¹)^(8*d*rank X)*(energy a X)^2) ≤ 2*(∑ Y, a Y^2)^2 := by
  classical
  let A : ℝ := ∑ Y, a Y^2
  let AX (X : E →ₗ[F2] F) : ℝ := ∑ Y, if RankBelow X Y then a Y^2 else 0
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hAX (X : E →ₗ[F2] F) : 0 ≤ AX X := by
    apply Finset.sum_nonneg
    intro Y _
    split_ifs <;> positivity
  have hAXA (X : E →ₗ[F2] F) : AX X ≤ A := by
    apply Finset.sum_le_sum
    intro Y _
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hmass : (∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*AX X) ≤ 2*A := by
    calc
      _ = ∑ Y, a Y^2 * (∑ X ∈ Finset.univ.filter (fun X => RankBelow X Y),
          ((2:ℝ)⁻¹)^(4*d*rank X)) := by
        simp only [AX, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro Y _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro X _
        split_ifs <;> ring
      _ ≤ ∑ Y, a Y^2*2 := by
        apply Finset.sum_le_sum
        intro Y _
        by_cases hy : rank Y ≤ d
        · exact mul_le_mul_of_nonneg_left (predecessor_weight_sum Y d hy) (sq_nonneg _)
        · have hz := hdegree Y (Nat.lt_of_not_ge hy)
          rw [hz]
          simp
      _ = 2*A := by rw [← Finset.sum_mul]; dsimp [A] <;> ring
  have hE (X : E →ₗ[F2] F) : 0 ≤ energy a X := by
    unfold energy
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcoarse (X : E →ₗ[F2] F) : energy a X ≤ (2:ℝ)^(2*d*rank X)*AX X := by
    let : Fintype (X.ker →ₗ[F2] (F ⧸ X.range)) := compressedFintype X
    have h10 := DerivativeEnergy.coefficient_energy X a d hdegree
    have he : 2*rank X*(d-rank X) ≤ 2*d*rank X := by
      calc
        _ ≤ 2*rank X*d := Nat.mul_le_mul_left _ (Nat.sub_le d (rank X))
        _ = _ := by ring
    have hn := Nat.pow_le_pow_right (n := 2) (by decide) he
    have hp : (2:ℝ)^(2*rank X*(d-rank X)) ≤ (2:ℝ)^(2*d*rank X) := by exact_mod_cast hn
    exact h10.trans (mul_le_mul_of_nonneg_right hp (hAX X))
  have hfour (X : E →ₗ[F2] F) : (energy a X)^2 ≤ (2:ℝ)^(4*d*rank X)*(A*AX X) := by
    have hs : (energy a X)^2 ≤ ((2:ℝ)^(2*d*rank X)*AX X)^2 :=
      (sq_le_sq₀ (hE X) (mul_nonneg (by positivity) (hAX X))).mpr (hcoarse X)
    have ha : (AX X)^2 ≤ A*AX X := by
      have hh := mul_le_mul_of_nonneg_right (hAXA X) (hAX X)
      simpa [pow_two] using hh
    calc
      _ ≤ ((2:ℝ)^(2*d*rank X)*AX X)^2 := hs
      _ = ((2:ℝ)^(2*d*rank X))^2*(AX X)^2 := by rw [mul_pow]
      _ ≤ ((2:ℝ)^(2*d*rank X))^2*(A*AX X) :=
        mul_le_mul_of_nonneg_left ha (sq_nonneg _)
      _ = _ := by
        rw [← pow_mul]
        congr 2
        ring
  calc
    (∑ X, ((2:ℝ)⁻¹)^(8*d*rank X)*(energy a X)^2)
        ≤ ∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*(A*AX X) := by
      apply Finset.sum_le_sum
      intro X _
      calc
        _ ≤ ((2:ℝ)⁻¹)^(8*d*rank X)*((2:ℝ)^(4*d*rank X)*(A*AX X)) :=
          mul_le_mul_of_nonneg_left (hfour X) (by positivity)
        _ = ((2:ℝ)^(4*d*rank X)*((2:ℝ)⁻¹)^(8*d*rank X))*(A*AX X) := by ring
        _ = _ := by
          have he : 8*d*rank X=4*d*rank X+4*d*rank X := by simp only [Nat.mul_assoc]; omega
          rw [he, half_cancel]
    _ = A*(∑ X, ((2:ℝ)⁻¹)^(4*d*rank X)*AX X) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro X _
      ring
    _ ≤ A*(2*A) := mul_le_mul_of_nonneg_left hmass hA
    _ = 2*A^2 := by ring

end UniqueGamesTheorem.Appendix.WeightedFourthMoment

end

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.UniqueGamesTheorem.Appendix.WeightedFourthMoment.weighted_fourth_coefficient_energy_oai.{u_1, u_2} := @OAI.UniqueGamesTheorem.Appendix.WeightedFourthMoment.weighted_fourth_coefficient_energy_oai.{u_1, u_2}
