-- Prove2me | solution 1 for MIPStarRE.QPBT.tildeM_isProj
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:11:49.337206+00:00
-- url     : https://prove2.me/submissions/6a0290e1-1543-4dca-802f-03e97d7e339f

-- Generated proof for MIPStarRE.QPBT.tildeM_isProj.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_isProj_kronecker
import Theorems.Thm_MIPStarRE_QPBT_MagicSquareRigidity_mul_eq_zero_of_isProj_of_add_le_one
import Theorems.Thm_MIPStarRE_QPBT_tauDotProj_isProj

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.GlobalPairWitness
end MIPStarRE.QPBT.GlobalPairWitness
namespace MIPStarRE.QPBT.MagicSquareRigidity
end MIPStarRE.QPBT.MagicSquareRigidity
namespace MIPStarRE.QPBT.PauliKind
end MIPStarRE.QPBT.PauliKind

/- Source helpers from QPBT/Extraction/Observables.lean. -/
/-!
# Pulled-apart Pauli observables

This module constructs the measurements and observables used to pull the two
Pauli bases onto separate registers. The construction retains the distinct
local spaces of the two players and uses the binary basis fixed in the
canonical field model.

## References

The product form and observable relations formalize blueprint
`lem:tildew-product-form`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1456`.
The swap identities formalize blueprint `lem:v-swap-conjugation`, from paper
lines 1687-1713.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.LDT.Preliminaries LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Pulled-apart measurements and observables -/



namespace GlobalPairWitness



/-- The single-basis marginal remains a projective measurement. This is the
projectivity assertion implicit in blueprint
`def:s-w-marginals`, paper
`14_analysis_of_the_pauli_basis_test.tex:1421-1423`. Finite postprocessing
preserves projectivity, independently of the construction of the joint
measurement. -/
theorem marginalPoly_isProjective {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon delta : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S delta)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective (w.marginalPoly side W) := by
  exact _root_.MIPStarRE.QPBT.SandwichProduct.postprocess_isProjective
    (w.Smeas side) (w.projective side) W.selectPoly

end GlobalPairWitness





















/-! ## Swap conjugation -/























end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/Rigidity/Dilation.lean. -/
/-!
# A simultaneous projective dilation of a Magic Square strategy

The rigidity argument for the Magic Square game is stated for an arbitrary
tensor-product strategy, whose measurements are positive operator valued
measures.  The self-testing argument, however, manipulates projections.  This
file removes that discrepancy by dilating an arbitrary strategy to a projective
one without changing any observable quantity.

Each local Hilbert space `ℂ^ι` is enlarged by one auxiliary register whose
basis is indexed by `Option MsAnswer`, and the original space is identified with
the *ground slice* `ℂ^ι ⊗ |⊥⟩`.  The one-measurement Naimark lemma of the low
individual degree development supplies, for every question separately, a family
of projections on the enlarged space whose compression to the ground slice
returns the original effects; the ancilla is the same for all questions, so the
identification of `ℂ^ι` with the ground slice is a single isometry serving every
question at once.  Folding the deficiency `1 - ∑_a P_a` into one distinguished
answer turns the dilated family into a complete projective measurement without
disturbing the compression, because the original effects already sum to the
identity.

Since the dilated state is the image of the original state under the two ground
embeddings, every Born probability, and hence the game value and all the
rejection, malformed-answer, cell-consistency and parity masses of the
value-to-parity layer, is unchanged.  Conversely, the local isometries produced
by a rigidity argument applied to the dilated strategy compose with the ground
embeddings to give local isometries of the original strategy, and the
state-dependent norms occurring in the conclusion of `thm:ms-rigidity` transfer
along that composition.

## References

The rigidity statement supported here is blueprint
`thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`,
proved in Coladangelo--Stark, Theorem 6.9.  The dilation reuses the
one-measurement Naimark lemma of
`references/ldt-paper/orthonormalization.tex:121-159`, formalized as
`MIPStarRE.LDT.MakingMeasurementsProjective.oneMeasNaimark`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-! ## Orthogonality inside a subnormalized family of projections -/



/-- Formalization-only auxiliary lemma for the dilation of `thm:ms-rigidity`
(blueprint `thm:ms-rigidity`).  A finite family of orthogonal
projections whose sum is at most the identity is mutually orthogonal: for two
distinct indices the two projections already sum to at most the identity, so the
previous lemma applies. -/
theorem mul_eq_zero_of_isProj_family {d α : Type*} [Fintype d] [DecidableEq d]
    [Fintype α] {P : α → _root_.LIDT.MIPStarRE.Quantum.Op d} (hP : ∀ a, _root_.LIDT.MIPStarRE.Quantum.IsProj (P a))
    (hsum : ∑ a, P a ≤ 1) {a b : α} (hab : a ≠ b) :
    P a * P b = 0 := by
  classical
  refine _root_.MIPStarRE.QPBT.MagicSquareRigidity.mul_eq_zero_of_isProj_of_add_le_one (hP a) (hP b).nonneg ?_
  refine le_trans ?_ hsum
  have hpair : ∑ c ∈ ({a, b} : Finset α), P c = P a + P b := by
    rw [Finset.sum_pair hab]
  rw [← hpair]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun c _ _ => (hP c).nonneg)



/-! ## The ground slice of an enlarged local space -/



























/-! ## The dilated projective measurement -/

























/-! ## The dilated state -/













/-! ## The dilated Magic Square strategy -/













/-! ## Preservation of the value-to-parity layer -/



































/-! ## Composition of the dilation with later local isometries -/



















/-! ## Transfer of state-dependent bounds -/

















end

end MIPStarRE.QPBT.MagicSquareRigidity

/-!
# Pulled-apart Pauli observables

This module constructs the measurements and observables used to pull the two
Pauli bases onto separate registers. The construction retains the distinct
local spaces of the two players and uses the binary basis fixed in the
canonical field model.

## References

The product form and observable relations formalize blueprint
`lem:tildew-product-form`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1415-1456`.
The swap identities formalize blueprint `lem:v-swap-conjugation`, from paper
lines 1687-1713.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.LDT.Preliminaries LIDT.MIPStarRE.Quantum



/-! ## Pulled-apart measurements and observables -/

open MIPStarRE.QPBT.PauliKind





open MIPStarRE.QPBT.GlobalPairWitness

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon delta : ℝ}
    {S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon} (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S delta)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : _root_.MIPStarRE.QPBT.PauliRegister P)
    (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.tildeM w side W u a) := by
  classical
  have hproj (g : _root_.MIPStarRE.QPBT.Poly P) : _root_.LIDT.MIPStarRE.Quantum.IsProj
      (_root_.MIPStarRE.QPBT.heteroKron ((w.marginalPoly side W).effect g)
        (_root_.MIPStarRE.QPBT.tauDotProj W u (dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) u - a))) :=
    _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.isProj_kronecker
      (w.marginalPoly_isProjective side W g) (_root_.MIPStarRE.QPBT.tauDotProj_isProj W u _)
  unfold _root_.MIPStarRE.QPBT.tildeM
  constructor
  · change (∑ g : _root_.MIPStarRE.QPBT.Poly P, _) * (∑ g : _root_.MIPStarRE.QPBT.Poly P, _) = _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Matrix.mul_sum, Finset.sum_eq_single g]
    · exact (hproj g).isIdempotentElem
    · intro g' _ hg'
      rw [_root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.MagicSquareRigidity.mul_eq_zero_of_isProj_family
        (w.marginalPoly_isProjective side W) (w.marginalPoly side W).sum_le_one
        hg'.symm]
      simp [_root_.MIPStarRE.QPBT.heteroKron]
    · intro hg
      exact (hg (Finset.mem_univ g)).elim
  · change (∑ g : _root_.MIPStarRE.QPBT.Poly P, _)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun g _ => (hproj g).isSelfAdjoint
