-- Prove2me | solution 1 for MIPStarRE.QPBT.tildeObs_eq_heteroKron
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T22:21:21.767553+00:00
-- url     : https://prove2.me/submissions/0654efcf-9e9b-47eb-a9a1-6082d46732f9

-- Generated proof for MIPStarRE.QPBT.tildeObs_eq_heteroKron.
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













/-- Fourier regrouping of the dot-product effects after translating their
outcomes. This is the change of variables in the product calculation at paper
`14_analysis_of_the_pauli_basis_test.tex:1442-1450`, supporting blueprint
`lem:tildew-product-form`. It uses only the definition of the coarse-graining,
not its projectivity. -/
private theorem sum_phaseSign_tauDotProj_sub {params : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (kind : _root_.MIPStarRE.QPBT.PauliKind) (vector : _root_.MIPStarRE.QPBT.PauliRegister params)
    (coefficient offset : _root_.MIPStarRE.QPBT.PauliScalar params) :
    (∑ value : _root_.MIPStarRE.QPBT.PauliScalar params,
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace params.model (coefficient * value)) •
        _root_.MIPStarRE.QPBT.tauDotProj kind vector (offset - value)) =
      _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace params.model (coefficient * offset)) •
        _root_.MIPStarRE.QPBT.tauObservable kind (coefficient • vector) := by
  classical
  calc
    _ = ∑ value : _root_.MIPStarRE.QPBT.PauliScalar params,
        _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace params.model (coefficient * (offset - value))) •
          _root_.MIPStarRE.QPBT.tauDotProj kind vector value := by
      symm
      simpa using (Equiv.subLeft offset).sum_comp
        (fun value => _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace params.model (coefficient * value)) •
          _root_.MIPStarRE.QPBT.tauDotProj kind vector (offset - value))
    _ = ∑ label : _root_.MIPStarRE.QPBT.PauliRegister params,
        _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace params.model
          (coefficient * (offset - dotProduct label vector))) • _root_.MIPStarRE.QPBT.pauliProj kind label := by
      simp only [_root_.MIPStarRE.QPBT.tauDotProj, _root_.MIPStarRE.QPBT.bracketOp, Finset.smul_sum]
      rw [← Finset.sum_fiberwise Finset.univ (fun label => dotProduct label vector)
        (fun label => _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace params.model
          (coefficient * (offset - dotProduct label vector))) • _root_.MIPStarRE.QPBT.pauliProj kind label)]
      apply Finset.sum_congr rfl
      intro value _
      apply Finset.sum_congr rfl
      intro label hlabel
      rw [(Finset.mem_filter.mp hlabel).2]
    _ = _ := by
      rw [_root_.MIPStarRE.QPBT.tauObservable_eq_sum_pauliProj, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro label _
      rw [smul_smul, smul_dotProduct, smul_eq_mul, dotProduct_comm vector label]
      congr 1
      rw [mul_sub, _root_.MIPStarRE.QPBT.fixedBinTrace, map_sub]
      have phaseSign_sub (first second : ZMod 2) :
          _root_.MIPStarRE.QPBT.phaseSign (first - second) = _root_.MIPStarRE.QPBT.phaseSign first * _root_.MIPStarRE.QPBT.phaseSign second := by
        rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, _root_.MIPStarRE.QPBT.phaseSign_add]
      exact phaseSign_sub _ _











/-! ## Swap conjugation -/























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
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : _root_.MIPStarRE.QPBT.PauliRegister P)
    (j : Fin P.model.basisDim) :
    _root_.MIPStarRE.QPBT.tildeObs w side W u j =
      _root_.MIPStarRE.QPBT.heteroKron
        (∑ pair : _root_.MIPStarRE.QPBT.PolyPair P,
          _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model
            (P.model.basis j * dotProduct (_root_.MIPStarRE.QPBT.decodeFq (W.selectPoly pair)) u)) •
            (w.Smeas side).effect pair)
        (_root_.MIPStarRE.QPBT.tauObservable W (P.model.basis j • u)) := by
  classical
  simp only [_root_.MIPStarRE.QPBT.tildeObs, _root_.MIPStarRE.QPBT.tildeM, Finset.smul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ polynomial : _root_.MIPStarRE.QPBT.Poly P,
        _root_.MIPStarRE.QPBT.heteroKron ((w.marginalPoly side W).effect polynomial)
          (∑ value : _root_.MIPStarRE.QPBT.PauliScalar P,
            _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model (P.model.basis j * value)) •
              _root_.MIPStarRE.QPBT.tauDotProj W u (dotProduct (_root_.MIPStarRE.QPBT.decodeFq polynomial) u - value)) := by
      apply Finset.sum_congr rfl
      intro polynomial _
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right]
      apply Finset.sum_congr rfl
      intro value _
      exact (Matrix.kronecker_smul _ _ _).symm
    _ = _root_.MIPStarRE.QPBT.heteroKron
        (∑ polynomial : _root_.MIPStarRE.QPBT.Poly P,
          _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model
            (P.model.basis j * dotProduct (_root_.MIPStarRE.QPBT.decodeFq polynomial) u)) •
              (w.marginalPoly side W).effect polynomial)
        (_root_.MIPStarRE.QPBT.tauObservable W (P.model.basis j • u)) := by
      simp_rw [sum_phaseSign_tauDotProj_sub]
      rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left]
      apply Finset.sum_congr rfl
      intro polynomial _
      simp only [_root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker, Matrix.kronecker_smul,
        Matrix.smul_kronecker]
    _ = _ := by
      congr 1
      simp only [_root_.MIPStarRE.QPBT.GlobalPairWitness.marginalPoly, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
        Finset.smul_sum]
      rw [← Finset.sum_fiberwise Finset.univ W.selectPoly
        (fun pair => _root_.MIPStarRE.QPBT.phaseSign (_root_.MIPStarRE.QPBT.fixedBinTrace P.model
          (P.model.basis j * dotProduct (_root_.MIPStarRE.QPBT.decodeFq (W.selectPoly pair)) u)) •
            (w.Smeas side).effect pair)]
      apply Finset.sum_congr rfl
      intro polynomial _
      apply Finset.sum_congr rfl
      intro pair hpair
      rw [(Finset.mem_filter.mp hpair).2]
