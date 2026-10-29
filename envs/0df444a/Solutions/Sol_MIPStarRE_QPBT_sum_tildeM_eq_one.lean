-- Prove2me | solution 1 for MIPStarRE.QPBT.sum_tildeM_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:21:21.556207+00:00
-- url     : https://prove2.me/submissions/9c62fd82-dd79-432e-a95b-b6d08d88e4ad

-- Generated proof for MIPStarRE.QPBT.sum_tildeM_eq_one.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
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
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.GlobalPairWitness
end MIPStarRE.QPBT.GlobalPairWitness
namespace MIPStarRE.QPBT.PauliKind
end MIPStarRE.QPBT.PauliKind
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Extraction/Defs.lean. -/
/-!
# Extraction foundations

This module defines the register identifications used to pull the Pauli
measurements apart. It retains the distinct local spaces of a
heterogeneous strategy, coarse-grains the generalized Pauli projectors by a
dot product, and records the state and error expressions needed by the later
extraction witness.

The binary phases use the existing `phaseSign`; the fixed field basis remains
the basis stored in `P.model` and is not re-quantified here.

## References

The Pauli dot-product projectors formalize blueprint
`def:tau-dot-product-projector`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1426-1429`.
The register and state helpers support blueprint `def:tilde-m-measurement`,
`def:v-swap-unitary`, and `lem:qld-unitary`, from paper lines 1429-1435 and
1666-1713.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Heterogeneous extraction registers -/













/-! ## Coarse-grained Pauli projectors -/









/-- For fixed `W` and `u`, the dot-product projectors sum to the identity.
This is the completeness assertion of blueprint
`lem:tau-dot-product-projective`, paper
`14_analysis_of_the_pauli_basis_test.tex:1426-1429`.

The dot-product fibers partition the complete Pauli outcome family. -/
theorem sum_tauDotProj_eq_one {P : _root_.MIPStarRE.QPBT.AdmissibleParams} (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : _root_.MIPStarRE.QPBT.PauliRegister P) :
    ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.tauDotProj W u a = 1 := by
  classical
  unfold _root_.MIPStarRE.QPBT.tauDotProj _root_.MIPStarRE.QPBT.bracketOp
  rw [Finset.sum_fiberwise]
  exact _root_.MIPStarRE.QPBT.sum_pauliProj_eq_one W



/-! ## Conjugation and extraction error -/







end

end MIPStarRE.QPBT

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
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : _root_.MIPStarRE.QPBT.PauliRegister P) :
    ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.tildeM w side W u a = 1 := by
  classical
  simp only [_root_.MIPStarRE.QPBT.tildeM]
  rw [Finset.sum_comm]
  calc
    _ = ∑ g : _root_.MIPStarRE.QPBT.Poly P, _root_.MIPStarRE.QPBT.heteroKron ((w.marginalPoly side W).effect g)
        (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.tauDotProj W u (dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) u - a)) := by
      exact Finset.sum_congr rfl fun g _ =>
        (_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right _ _ _).symm
    _ = ∑ g : _root_.MIPStarRE.QPBT.Poly P, _root_.MIPStarRE.QPBT.heteroKron ((w.marginalPoly side W).effect g) 1 := by
      refine Finset.sum_congr rfl fun g _ => ?_
      congr 1
      calc
        _ = ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.tauDotProj W u a :=
          (Equiv.subLeft (dotProduct (_root_.MIPStarRE.QPBT.decodeFq g) u)).sum_comp (_root_.MIPStarRE.QPBT.tauDotProj W u)
        _ = 1 := _root_.MIPStarRE.QPBT.sum_tauDotProj_eq_one W u
    _ = _root_.MIPStarRE.QPBT.heteroKron (∑ g : _root_.MIPStarRE.QPBT.Poly P, (w.marginalPoly side W).effect g) 1 :=
      (_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left _ _ _).symm
    _ = 1 := by rw [(w.marginalPoly side W).sum_eq_one, _root_.MIPStarRE.QPBT.heteroKron_one_one]
