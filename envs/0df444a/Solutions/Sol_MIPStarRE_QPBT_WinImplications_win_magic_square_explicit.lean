-- Prove2me | solution 1 for MIPStarRE.QPBT.WinImplications.win_magic_square_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:56:53.982991+00:00
-- url     : https://prove2.me/submissions/4193879d-8bd4-4a0d-a973-c219a200c830

-- Generated proof for MIPStarRE.QPBT.WinImplications.win_magic_square_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Games_CondLinear
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Anticommuting
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_MagicSquare
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_avgOver_anticomm_le_sixteen_mul_gated
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_gatedMsRejection_le_fixedEdge
import Theorems.Thm_MIPStarRE_QPBT_rejectionMass_eq_one_sub_value
import Theorems.Thm_MIPStarRE_QPBT_sum_indicatorVec_mul_indicatorVec
import Theorems.Thm_MIPStarRE_QPBT_trace_basis_eq_one_of_selfDual_normal

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.Basis
end MIPStarRE.QPBT.Basis
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Algebra/FieldBasis.lean. -/
/-!
# Finite-field bases and the fixed binary representation

The Pauli basis test uses fields of size `2^k` for odd `k`, together with a
chosen self-dual normal basis over `ZMod 2`.  This file constructs such bases
and records the resulting fixed field model for later proofs.

## References

The declarations correspond to blueprint `def:admissible-size`,
`def:dual-self-dual-normal-basis`, `def:subfields-kappa`, `def:subfield-trace`,
and `def:binary-representation`.
Their paper origin is `references/qpbt-paper/04_preliminaries.tex:433-502,653-728`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT



/-- An admissible field size is at least two, its binary exponent being odd
and therefore positive.  This is a property of blueprint
`def:admissible-size`, paper origin
`references/qpbt-paper/04_preliminaries.tex:662-667`.
-/
theorem IsAdmissibleSize.two_le {q : ℕ} (hq : _root_.MIPStarRE.QPBT.IsAdmissibleSize q) : 2 ≤ q := by
  obtain ⟨k, hk, hqk⟩ := hq
  obtain ⟨j, hj⟩ := hk
  rw [hqk, hj]
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 * j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)







/- The characteristic-two self-dual normal-basis construction is carried out
in the group algebra of the finite Galois group.  The transition from a normal
basis to its trace dual is a symmetric unit; odd cardinality makes its square
root unique and symmetric. -/











/-!
The paper fixes the field representation and self-dual normal basis once for
each admissible field size.  We expose that choice through a single global
selector rather than carrying a potentially different model in every game
parameter record.  Existence is a named stage-4.3 proof obligation; the
selector itself is the resulting noncomputable choice.
-/






















end MIPStarRE.QPBT

/- Source helpers from QPBT/Algebra/SelfDualBasisTheorems.lean. -/
/-! # Trace and coordinate identities for self-dual bases

Blueprint `lem:downsize_field` and `lem:one`; paper
`references/qpbt-paper/04_preliminaries.tex:505-550,730-767`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

-- The paper-facing interface fixes `Fintype ι`; its value is needed only for the matrix sum.






-- The finite carrier is part of the fixed source-aligned interface for the binary field model.


-- The finite carrier is part of the fixed source-aligned interface for the binary field model.


/-- Fixed-model specialization of the trace-one assertion in blueprint
`lem:one`, paper `04_preliminaries.tex:730-765`. -/
theorem fixedFieldModel_trace_basis_eq_one {q : ℕ} (F : _root_.MIPStarRE.QPBT.FixedFieldModel q)
    (i : Fin F.basisDim) : Algebra.trace (ZMod 2) F.K (F.basis i) = 1 := by
  apply _root_.MIPStarRE.QPBT.trace_basis_eq_one_of_selfDual_normal F.basisDimOdd F.basis
  · simpa [_root_.MIPStarRE.QPBT.Basis.IsSelfDual, _root_.MIPStarRE.QPBT.IsDualBasisPair] using F.selfDual
  · simpa [_root_.MIPStarRE.QPBT.Basis.IsNormal, ZMod.card] using F.normal











-- The fixed interface supplies decidable basis indices for the multiplication-table calculation.






end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/CondLinear.lean. -/
/-!
# Conditionally linear functions and graph distributions

The question distributions in the Pauli basis test are generated by a finite
graph of types and a shared seed, with each type applying a conditionally linear
map to that seed.  A conditionally linear map of level `ell` is a sum of `ell`
linear contributions on pairwise disjoint register subspaces, each contribution
selected by the values of the preceding ones.  The inductive predicate records
this decomposition, and the graph distribution is the law of the type pair.
Equal-level maps over pairwise disjoint coordinate registers have coordinatewise
direct sums whose shared-seed laws factor as products.

## References

The source-facing nodes are blueprint `def:cl-func`, `def:cl-dist`,
`lem:cl-concat`, and `def:graph-distribution`.
The paper origins are
`references/qpbt-paper/05_conditionally_linear_functions.tex:35-57,282-314`,
`references/qpbt-paper/07_types.tex:65-82`,
and `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:964-1010`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]













































/-- The graph distribution has total mass one whenever its edge set is
nonempty.  This is not a named statement of the source article; it is
blueprint
`lem:graph-distribution-mass`. -/
theorem graphDistribution_isProbability {T : Type*} [Fintype T] [DecidableEq T]
    (E : Finset (Sym2 T)) (hE : E.Nonempty) :
    (_root_.MIPStarRE.QPBT.graphDistribution E hE).IsProbability := by
  apply _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_isProbability
  obtain ⟨e, he⟩ := hE
  obtain ⟨⟨a, b⟩, rfl⟩ := Sym2.mk_surjective e
  change s(a, b) ∈ E at he
  exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩



end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/Defs.lean. -/
/-!
# Games, tensor-product strategies, and value

This file provides the finite game carrier used by the Pauli basis test.  Pure
states are vectors in `EuclideanSpace`, and POVMs use the project's matrix
`Measurement` structure.

## References

The source-facing nodes are blueprint `def:game`, `def:povm-conventions`,
`def:tensor-product-strategy`, and `def:tensor-product-value`.
The paper origin is `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



attribute [instance] _root_.MIPStarRE.QPBT.Game.questionAFintype _root_.MIPStarRE.QPBT.Game.questionBFintype
  _root_.MIPStarRE.QPBT.Game.answerAFintype _root_.MIPStarRE.QPBT.Game.answerBFintype _root_.MIPStarRE.QPBT.Game.questionADecidableEq
  _root_.MIPStarRE.QPBT.Game.questionBDecidableEq _root_.MIPStarRE.QPBT.Game.answerADecidableEq _root_.MIPStarRE.QPBT.Game.answerBDecidableEq









attribute [instance] _root_.MIPStarRE.QPBT.Strategy.ιAFintype _root_.MIPStarRE.QPBT.Strategy.ιBFintype
  _root_.MIPStarRE.QPBT.Strategy.ιADecidableEq _root_.MIPStarRE.QPBT.Strategy.ιBDecidableEq



/-! ### Algebra of the tensor placement

The shared tensor-placement API.  These identities are used both by the perfect
Magic Square strategy (blueprint `thm:ms-from-ac`) and by the rigidity transfer
step (blueprint `thm:ms-rigidity`), so they live
with the definition rather than in either development. -/





















/- The Euclidean linear map is the shared action used by the value and distance
functionals.  Keeping it at the Euclidean-space level avoids accidentally
using the function-space supremum norm of `Matrix.mulVec`. -/














/-- Every answer-pair Born weight is nonnegative.  This is formalization-only
support for the probability expression in `def:tensor-product-value`. -/
theorem outcomeWeight_nonneg {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB) (a : G.AnswerA) (b : G.AnswerB) :
    0 ≤ _root_.MIPStarRE.QPBT.outcomeWeight S x y a b := by
  unfold _root_.MIPStarRE.QPBT.outcomeWeight _root_.MIPStarRE.QPBT.applyOperatorToState _root_.MIPStarRE.QPBT.heteroKron
  exact
    (Matrix.isPositive_toEuclideanLin_iff.mpr
      (Matrix.nonneg_iff_posSemidef.mp
        (_root_.LIDT.MIPStarRE.Quantum.kronecker_nonneg ((S.A x).pos a) ((S.B y).pos b)))).re_inner_nonneg_right S.ψ










/-- Every answer event has nonnegative Born weight. -/
theorem outcome_event_weight_nonneg {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    (x : G.QuestionA) (y : G.QuestionB)
    (E : G.AnswerA → G.AnswerB → Prop) [DecidableRel E] :
    0 ≤ _root_.MIPStarRE.QPBT.outcomeEventWeight S x y E := by
  unfold _root_.MIPStarRE.QPBT.outcomeEventWeight
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    split_ifs
    · exact _root_.MIPStarRE.QPBT.outcomeWeight_nonneg S x y a b
    · exact le_rfl














end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/Averages.lean. -/
/-!
# Averaging lemmas for winning implications

This module derives the finite conditioning and fixed-edge rejection bounds
used by all seven exact winning implications.

## References

The formalization-only averaging and conditioning auxiliaries support items 1–7
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications























/-- Formalization-only auxiliary for items 1–7 of `lem:qld-win-implications`:
the average rejection mass of a finite game is one minus its value. -/
theorem rejectionEventAverage_eq_one_sub_value {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G) :
    _root_.LIDT.MIPStarRE.LDT.avgOver G.μ (fun questions =>
      _root_.MIPStarRE.QPBT.outcomeEventWeight S questions.1 questions.2 fun a b =>
        G.decide questions.1 questions.2 a b = false) =
      1 - S.value := by
  classical
  simpa only [_root_.MIPStarRE.QPBT.outcomeEventWeight, Bool.eq_false_iff, ite_not] using
    _root_.MIPStarRE.QPBT.rejectionMass_eq_one_sub_value S






end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/Anticommuting.lean. -/
/-!
# Commuting and anticommuting Pauli tuples

This module defines the tuple phase used in the Pauli basis test and the
conditional uniform distributions used by its observable analysis.

## References

The definitions and probability bounds formalize blueprint
`def:anticommuting-tuple` and `fact:omega-anticomm-prob`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:64-95`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section















/-! ### Auxiliary counting lemmas

The declarations of this section are formalization-only auxiliaries for the
proof of blueprint
`fact:omega-anticomm-prob`. They record the cardinalities used by the
exact computation of the anticommuting probability. -/

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has characteristic two, since it is an algebra over the two-element
field. Blueprint `fact:omega-anticomm-prob`. -/
private theorem pauliScalar_charTwo (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    CharP (_root_.MIPStarRE.QPBT.PauliScalar P) 2 :=
  (Algebra.charP_iff (ZMod 2) (_root_.MIPStarRE.QPBT.PauliScalar P) 2).mp (ZMod.charP 2)

/-- Formalization-only auxiliary: the scalar carrier of an admissible parameter
tuple has exactly `q` elements. Blueprint
`fact:omega-anticomm-prob`. -/
private theorem card_pauliScalar (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) = P.q :=
  @_root_.LIDT.MIPStarRE.LDT.FieldModel.card P.q P.model.toFieldModel

/-- The phase bit of a Pauli tuple is the trace of `r_Z r_X` times the product
of the coordinate sums `1 + u_{X,i} + u_{Z,i}`. This is the closed form of
`γ(ω)` derived in the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem gammaValue_eq_trace_prod (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (uX uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (rX rZ : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.MIPStarRE.QPBT.gammaValue P uX uZ rX rZ =
      _root_.MIPStarRE.QPBT.fixedBinTrace P.model (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) := by
  haveI := pauliScalar_charTwo P
  have hprod : (∑ y : _root_.MIPStarRE.QPBT.Cube P.m, _root_.MIPStarRE.QPBT.indicatorVec uX y * _root_.MIPStarRE.QPBT.indicatorVec uZ y)
      = ∏ i : Fin P.m, (1 + uX i + uZ i) :=
    _root_.MIPStarRE.QPBT.sum_indicatorVec_mul_indicatorVec uX uZ
  unfold _root_.MIPStarRE.QPBT.gammaValue
  congr 1
  rw [← hprod]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Formalization-only auxiliary: the field trace onto the two-element field
takes each of its two values on exactly half of the scalars. This is the final
step of the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem two_mul_card_trace_ne (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    2 * (Finset.univ.filter
        (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model a ≠ 0)).card = P.q := by
  classical
  haveI := pauliScalar_charTwo P
  have hK := card_pauliScalar P
  have hadd : ∀ a c : _root_.MIPStarRE.QPBT.PauliScalar P,
      _root_.MIPStarRE.QPBT.fixedBinTrace P.model (a + c)
        = _root_.MIPStarRE.QPBT.fixedBinTrace P.model a + _root_.MIPStarRE.QPBT.fixedBinTrace P.model c := by
    intro a c
    simp [_root_.MIPStarRE.QPBT.fixedBinTrace, _root_.MIPStarRE.QPBT.binTrace]
  obtain ⟨b, hb⟩ : ∃ b : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.fixedBinTrace P.model b = 1 := by
    have hpos : 0 < P.model.basisDim := by
      obtain ⟨j, hj⟩ := P.model.basisDimOdd
      omega
    exact ⟨P.model.basis ⟨0, hpos⟩,
      _root_.MIPStarRE.QPBT.fixedFieldModel_trace_basis_eq_one P.model ⟨0, hpos⟩⟩
  have hbb : b + b = 0 := CharTwo.add_self_eq_zero b
  have himg :
      (Finset.univ.filter
          (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0)).image (fun a => a + b)
        = Finset.univ.filter
            (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => ¬ (_root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [hadd, hc, hb]
      simp
    · intro ha
      refine ⟨a + b, ?_, ?_⟩
      · rw [hadd, hb]
        have hone : _root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 1 := by
          revert ha
          generalize _root_.MIPStarRE.QPBT.fixedBinTrace P.model a = t
          revert t
          decide
        rw [hone]
        decide
      · rw [add_assoc, hbb, add_zero]
  have hinj : Function.Injective (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => a + b) :=
    fun _ _ h => by simpa using h
  have hcard :
      (Finset.univ.filter (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0)).card
        = (Finset.univ.filter
            (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => ¬ (_root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0))).card := by
    rw [← himg, Finset.card_image_of_injective _ hinj]
  have hsplit :
      (Finset.univ.filter (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0)).card
          + (Finset.univ.filter
              (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => ¬ (_root_.MIPStarRE.QPBT.fixedBinTrace P.model a = 0))).card
        = Fintype.card (_root_.MIPStarRE.QPBT.PauliScalar P) :=
    Finset.card_filter_add_card_filter_not _
  rw [hK] at hsplit
  simp only [ne_eq]
  omega



/-- Twice the number of anticommuting tuples is `q^{m+1}(q-1)^{m+1}`. This is
the exact count established in the proof of blueprint
`fact:omega-anticomm-prob`. -/
private theorem two_mul_card_anticommuting (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    2 * (Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsAnticommuting P)).card
      = P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) := by
  classical
  haveI := pauliScalar_charTwo P
  have h2 : (2 : _root_.MIPStarRE.QPBT.PauliScalar P) = 0 := CharTwo.two_eq_zero
  have hK := card_pauliScalar P
  have htr0 : _root_.MIPStarRE.QPBT.fixedBinTrace P.model 0 = 0 := by
    simp [_root_.MIPStarRE.QPBT.fixedBinTrace, _root_.MIPStarRE.QPBT.binTrace]
  set N := (Finset.univ.filter
    (fun a : _root_.MIPStarRE.QPBT.PauliScalar P => _root_.MIPStarRE.QPBT.fixedBinTrace P.model a ≠ 0)).card with hNdef
  have hN : 2 * N = P.q := two_mul_card_trace_ne P
  -- the innermost sum, over the second scalar coordinate
  have hinner : ∀ c : _root_.MIPStarRE.QPBT.PauliScalar P,
      (∑ r : _root_.MIPStarRE.QPBT.PauliScalar P, if _root_.MIPStarRE.QPBT.fixedBinTrace P.model (r * c) ≠ 0 then (1 : ℕ) else 0)
        = if c = 0 then 0 else N := by
    intro c
    by_cases hc : c = 0
    · subst hc
      simp [htr0]
    · rw [if_neg hc, hNdef, Finset.card_filter]
      exact Fintype.sum_equiv (Equiv.mulRight₀ c hc)
        (fun r => if _root_.MIPStarRE.QPBT.fixedBinTrace P.model (r * c) ≠ 0 then (1 : ℕ) else 0)
        (fun a => if _root_.MIPStarRE.QPBT.fixedBinTrace P.model a ≠ 0 then (1 : ℕ) else 0)
        (fun r => rfl)
  -- the sum over the first scalar coordinate
  have hnzcard :
      (Finset.univ.filter (fun x : _root_.MIPStarRE.QPBT.PauliScalar P => ¬ (x = 0))).card = P.q - 1 := by
    have h1 : (Finset.univ.filter (fun x : _root_.MIPStarRE.QPBT.PauliScalar P => x ≠ 0))
        = Finset.univ.erase 0 := Finset.filter_ne' _ _
    simp only [ne_eq] at h1
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hK]
  have hmid : ∀ dd : _root_.MIPStarRE.QPBT.PauliScalar P,
      (∑ rX : _root_.MIPStarRE.QPBT.PauliScalar P, if rX * dd = 0 then (0 : ℕ) else N)
        = if dd = 0 then 0 else (P.q - 1) * N := by
    intro dd
    by_cases hd : dd = 0
    · subst hd
      simp
    · rw [if_neg hd]
      have hcong : ∀ rX : _root_.MIPStarRE.QPBT.PauliScalar P,
          (if rX * dd = 0 then (0 : ℕ) else N) = if rX = 0 then 0 else N := by
        intro rX
        by_cases hr : rX = 0
        · simp [hr]
        · rw [if_neg (by simpa using mul_ne_zero hr hd), if_neg hr]
      rw [Finset.sum_congr rfl (fun x _ => hcong x), Finset.sum_ite]
      simp [hnzcard]
  -- the sum over the second point block
  have hDcard : ∀ uX : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P,
      (Finset.univ.filter (fun uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P =>
        ¬ ((∏ i : Fin P.m, (1 + uX i + uZ i)) = 0))).card = (P.q - 1) ^ P.m := by
    intro uX
    have hset : (Finset.univ.filter (fun uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P =>
        ¬ ((∏ i : Fin P.m, (1 + uX i + uZ i)) = 0)))
        = Fintype.piFinset (fun i : Fin P.m => Finset.univ.erase (1 + uX i)) := by
      ext uZ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
        Finset.mem_erase, and_true]
      constructor
      · intro h i hi
        refine h ?_
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        rw [hi]
        linear_combination (1 + uX i) * h2
      · intro h hz
        rw [Finset.prod_eq_zero_iff] at hz
        obtain ⟨i, -, hi⟩ := hz
        exact h i (by linear_combination hi - (1 + uX i) * h2)
    rw [hset, Fintype.card_piFinset]
    simp [Finset.card_erase_of_mem, Finset.card_univ, hK]
  have houter : ∀ uX : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P,
      (∑ uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P,
          if (∏ i : Fin P.m, (1 + uX i + uZ i)) = 0 then (0 : ℕ) else (P.q - 1) * N)
        = (P.q - 1) ^ P.m * ((P.q - 1) * N) := by
    intro uX
    rw [Finset.sum_ite]
    simp [hDcard uX]
  have step1 : ∀ (uX uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (rX : _root_.MIPStarRE.QPBT.PauliScalar P),
      (∑ rZ : _root_.MIPStarRE.QPBT.PauliScalar P,
          if _root_.MIPStarRE.QPBT.IsAnticommuting ((uX, uZ, rX, rZ) : _root_.MIPStarRE.QPBT.PauliTuple P) then (1 : ℕ) else 0)
        = if rX * ∏ i : Fin P.m, (1 + uX i + uZ i) = 0 then 0 else N := by
    intro uX uZ rX
    have hcongr : ∀ rZ : _root_.MIPStarRE.QPBT.PauliScalar P,
        (if _root_.MIPStarRE.QPBT.IsAnticommuting ((uX, uZ, rX, rZ) : _root_.MIPStarRE.QPBT.PauliTuple P) then (1 : ℕ) else 0)
          = if _root_.MIPStarRE.QPBT.fixedBinTrace P.model
              (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0 then 1 else 0 := by
      intro rZ
      have hiff : _root_.MIPStarRE.QPBT.IsAnticommuting ((uX, uZ, rX, rZ) : _root_.MIPStarRE.QPBT.PauliTuple P)
          ↔ _root_.MIPStarRE.QPBT.fixedBinTrace P.model
              (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0 := by
        unfold _root_.MIPStarRE.QPBT.IsAnticommuting
        rw [gammaValue_eq_trace_prod]
      by_cases h : _root_.MIPStarRE.QPBT.fixedBinTrace P.model
          (rZ * (rX * ∏ i : Fin P.m, (1 + uX i + uZ i))) ≠ 0
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]
    rw [Finset.sum_congr rfl (fun x _ => hcongr x), hinner]
  have hcount : (Finset.univ.filter (@_root_.MIPStarRE.QPBT.IsAnticommuting P)).card
      = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)) := by
    rw [Finset.card_filter]
    simp only [Fintype.sum_prod_type]
    calc (∑ uX : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P, ∑ uZ : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P,
            ∑ rX : _root_.MIPStarRE.QPBT.PauliScalar P, ∑ rZ : _root_.MIPStarRE.QPBT.PauliScalar P,
              (if _root_.MIPStarRE.QPBT.IsAnticommuting ((uX, uZ, rX, rZ) : _root_.MIPStarRE.QPBT.PauliTuple P) then (1 : ℕ) else 0))
        = ∑ _uX : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P, (P.q - 1) ^ P.m * ((P.q - 1) * N) := by
          refine Finset.sum_congr rfl fun uX _ => ?_
          rw [← houter uX]
          refine Finset.sum_congr rfl fun uZ _ => ?_
          rw [← hmid (∏ i : Fin P.m, (1 + uX i + uZ i))]
          exact Finset.sum_congr rfl fun rX _ => step1 uX uZ rX
      _ = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          congr 1
          simp [hK]
  rw [hcount]
  have hexpand : 2 * (P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * N)))
      = P.q ^ P.m * ((P.q - 1) ^ P.m * ((P.q - 1) * (2 * N))) := by ring
  rw [hexpand, hN, pow_succ, pow_succ]
  ring





/-! ### The exact anticommuting probability -/













/-! ### Conditional uniform distributions -/





/-- The anticommuting conditional distribution is probabilistic. This is the
well-formedness companion to the conditional sampling in
blueprint `lem:qld-win-implications`. -/
theorem anticommTupleDist_isProbability (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.anticommTupleDist P).IsProbability := by
  refine _root_.LIDT.MIPStarRE.LDT.Distribution.uniformOnFinset_isProbability _ ?_
  rw [← Finset.card_pos]
  have hq2 : 2 ≤ P.q := P.hq.two_le
  have hcount := two_mul_card_anticommuting P
  have hpos : 0 < P.q ^ (P.m + 1) * (P.q - 1) ^ (P.m + 1) :=
    Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)
  omega



end

end MIPStarRE.QPBT

/-!
# Magic Square winning implications

This module proves the exact induced Magic Square value and variable
consistency bounds on anticommuting Pauli tuples.

## References

The Magic Square value and consistency theorems prove items 6 and 7
of `lem:qld-win-implications`
from `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`
and blueprint `lem:qld-win-implications` and `lem:qld-win-implications-obs`.
-/



open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.WinImplications

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ) (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε),
      0 ≤ ε →
      |1 - _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) S.msValueAt| ≤
        16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
  intro P ε S _
  let ν := _root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty
  have hpoint (ω : _root_.MIPStarRE.QPBT.PauliTuple P) :
      _root_.LIDT.MIPStarRE.LDT.avgOver ν (_root_.MIPStarRE.QPBT.WinImplications.inducedMsRejection S ω) = 1 - S.msValueAt ω := by
    change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.graphDistribution _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty)
        (fun questions : _root_.MIPStarRE.QPBT.MsType × _root_.MIPStarRE.QPBT.MsType =>
          _root_.MIPStarRE.QPBT.outcomeEventWeight (S.msStrategyAt ω) questions.1 questions.2
            (fun a b => _root_.MIPStarRE.QPBT.msWinPredicate questions.1 questions.2 a b = false)) =
      1 - S.msValueAt ω
    convert _root_.MIPStarRE.QPBT.WinImplications.rejectionEventAverage_eq_one_sub_value (S.msStrategyAt ω) using 1 <;>
      rfl
  have hvalue :
      1 - _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) S.msValueAt =
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
          _root_.LIDT.MIPStarRE.LDT.avgOver ν (_root_.MIPStarRE.QPBT.WinImplications.inducedMsRejection S ω)) := by
    calc
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω => 1 - S.msValueAt ω) := by
        symm
        rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _
          (_root_.MIPStarRE.QPBT.anticommTupleDist_isProbability P)]
      _ = _ := by
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
        intro ω
        exact (hpoint ω).symm
  rw [hvalue, abs_of_nonneg]
  · calc
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.anticommTupleDist P) (fun ω =>
          _root_.LIDT.MIPStarRE.LDT.avgOver ν (_root_.MIPStarRE.QPBT.WinImplications.inducedMsRejection S ω)) ≤
          16 * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) (fun ω =>
            if _root_.MIPStarRE.QPBT.IsAnticommuting ω then
              _root_.LIDT.MIPStarRE.LDT.avgOver ν (_root_.MIPStarRE.QPBT.WinImplications.inducedMsRejection S ω)
            else 0) := by
        apply _root_.MIPStarRE.QPBT.WinImplications.avgOver_anticomm_le_sixteen_mul_gated
        intro ω
        exact _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg ν _ fun xy =>
          _root_.MIPStarRE.QPBT.outcome_event_weight_nonneg (S.msStrategyAt ω) xy.1 xy.2 _
      _ = 16 * _root_.LIDT.MIPStarRE.LDT.avgOver ν (fun xy =>
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) (fun ω =>
            if _root_.MIPStarRE.QPBT.IsAnticommuting ω then _root_.MIPStarRE.QPBT.WinImplications.inducedMsRejection S ω xy else 0)) := by
        congr 1
        calc
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) (fun ω =>
              if _root_.MIPStarRE.QPBT.IsAnticommuting ω then
                _root_.LIDT.MIPStarRE.LDT.avgOver ν (_root_.MIPStarRE.QPBT.WinImplications.inducedMsRejection S ω)
              else 0) =
              _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.PauliTuple P)) (fun ω =>
                _root_.LIDT.MIPStarRE.LDT.avgOver ν (fun xy => if _root_.MIPStarRE.QPBT.IsAnticommuting ω then
                  _root_.MIPStarRE.QPBT.WinImplications.inducedMsRejection S ω xy else 0)) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro ω
            by_cases hanti : _root_.MIPStarRE.QPBT.IsAnticommuting ω <;>
              simp [hanti, _root_.LIDT.MIPStarRE.LDT.avgOver_zero]
          _ = _ := _root_.LIDT.MIPStarRE.LDT.avgOver_comm _ _ _
      _ ≤ 16 * _root_.LIDT.MIPStarRE.LDT.avgOver ν
          (fun _ => (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono_on_support
        intro xy hxy
        exact _root_.MIPStarRE.QPBT.WinImplications.gatedMsRejection_le_fixedEdge S xy hxy
      _ = 16 * (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * ε := by
        rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability ν]
        · ring
        · exact _root_.MIPStarRE.QPBT.graphDistribution_isProbability _root_.MIPStarRE.QPBT.msEdges _root_.MIPStarRE.QPBT.msEdges_nonempty
  · exact _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg (_root_.MIPStarRE.QPBT.anticommTupleDist P) _ fun ω =>
      _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg ν _ fun xy =>
        _root_.MIPStarRE.QPBT.outcome_event_weight_nonneg (S.msStrategyAt ω) xy.1 xy.2 _
