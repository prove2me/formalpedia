-- Prove2me | solution 1 for MIPStarRE.QPBT.Palomar.exists_spcc_value_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:32:41.106238+00:00
-- url     : https://prove2.me/submissions/ecebf7d2-57d6-4e4b-93a6-5019d767b589

-- Generated proof for MIPStarRE.QPBT.Palomar.exists_spcc_value_one.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Palomar_Bridge
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliExtractionBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Test_Completeness
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_eq_toPMF_realWeightedSum
import Theorems.Thm_LIDT_PMF_realWeightedSum_map
import Theorems.Thm_MIPStarRE_QPBT_Palomar_isCommutingOn_relabel_iff
import Theorems.Thm_MIPStarRE_QPBT_exists_spcc_value_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar
namespace MIPStarRE.QPBT.Palomar.Game
end MIPStarRE.QPBT.Palomar.Game
namespace MIPStarRE.QPBT.Palomar.PMF
end MIPStarRE.QPBT.Palomar.PMF
namespace MIPStarRE.QPBT.Palomar.POVM
end MIPStarRE.QPBT.Palomar.POVM
namespace MIPStarRE.QPBT.Palomar.Strategy
end MIPStarRE.QPBT.Palomar.Strategy
namespace MIPStarRE.QPBT.Palomar.SymmetricGame
end MIPStarRE.QPBT.Palomar.SymmetricGame
namespace MIPStarRE.QPBT.Palomar.SymmetricStrategy
end MIPStarRE.QPBT.Palomar.SymmetricStrategy

/- Source helpers from QPBT/Palomar/Bridge.lean. -/
/-!
# Exact bridges for the compact Palomar game foundation

This module converts the compact Mathlib-only game and strategy data to and
from the library structures.  The conversions preserve every effect, state,
Born value, and the projective, consistency, commutation, and SPCC predicates.

This bridge uses the repository's legacy import form because Lean `module`
files cannot import the current non-`module` game API.  The compact foundation
itself uses the public module surface required by the Palomar extraction.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:10-57,68-180`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder

namespace MIPStarRE.QPBT.Palomar

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum













namespace Strategy













/-- The compact and library Born values agree for a library strategy. -/
theorem value_ofStrategy {G : _root_.MIPStarRE.QPBT.Game}
    (S : _root_.MIPStarRE.QPBT.Strategy G) :
    (_root_.MIPStarRE.QPBT.Palomar.Strategy.ofStrategy S).value (_root_.MIPStarRE.QPBT.Palomar.Game.ofGame G) = S.value := by
  unfold _root_.MIPStarRE.QPBT.Palomar.Strategy.value _root_.MIPStarRE.QPBT.Strategy.value
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum G.μ G.μ_prob]
  rfl







end Strategy



/-- A project distribution and its PMF have the same positive-probability support. -/
theorem distribution_toPMF_pos_iff {α : Type*} (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α)
    (hμ : μ.IsProbability) (a : α) : 0 < μ.toPMF hμ a ↔ 0 < μ.weight a := by
  rw [_root_.LIDT.MIPStarRE.LDT.Distribution.toPMF_apply]
  exact ENNReal.ofReal_pos



/-- Existing and compact commutation predicates agree after `Distribution.toPMF`. -/
theorem isCommutingOn_toPMF_iff
    {X Y A B I : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution (X × Y)) (hμ : μ.IsProbability)
    (alice : X → _root_.LIDT.MIPStarRE.Quantum.Measurement A I)
    (bob : Y → _root_.LIDT.MIPStarRE.Quantum.Measurement B I) :
    _root_.MIPStarRE.QPBT.Palomar.IsCommutingOn (μ.toPMF hμ) (fun x => _root_.MIPStarRE.QPBT.Palomar.POVM.ofMeasurement (alice x))
        (fun y => _root_.MIPStarRE.QPBT.Palomar.POVM.ofMeasurement (bob y)) ↔
      _root_.MIPStarRE.QPBT.IsCommutingOn μ alice bob := by
  constructor
  · intro h x y hxy a b
    exact h x y ((_root_.MIPStarRE.QPBT.Palomar.distribution_toPMF_pos_iff μ hμ (x, y)).mpr hxy) a b
  · intro h x y hxy a b
    exact h x y ((_root_.MIPStarRE.QPBT.Palomar.distribution_toPMF_pos_iff μ hμ (x, y)).mp hxy) a b

namespace SymmetricStrategy









/-- The compact and library Born values agree for a library symmetric strategy. -/
theorem value_ofSymmetricStrategy {G : _root_.MIPStarRE.QPBT.SymmetricGame}
    (S : _root_.MIPStarRE.QPBT.SymmetricStrategy G) :
    (_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.ofSymmetricStrategy S).toStrategy.value
        (_root_.MIPStarRE.QPBT.Palomar.SymmetricGame.ofSymmetricGame G).toGame = S.toStrategy.value := by
  exact _root_.MIPStarRE.QPBT.Palomar.Strategy.value_ofStrategy S.toStrategy





/-- Library and compact SPCC predicates are exactly equivalent. -/
theorem isSPCC_ofSymmetricStrategy_iff {G : _root_.MIPStarRE.QPBT.SymmetricGame}
    (S : _root_.MIPStarRE.QPBT.SymmetricStrategy G) :
    (_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.ofSymmetricStrategy S).IsSPCC (_root_.MIPStarRE.QPBT.Palomar.SymmetricGame.ofSymmetricGame G) ↔ S.IsSPCC := by
  change
    ((∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (S.M x)) ∧
      (∀ x, _root_.MIPStarRE.QPBT.Measurement.IsConsistentOn (S.M x) S.ψ) ∧
      _root_.MIPStarRE.QPBT.Palomar.IsCommutingOn (G.μ.toPMF G.μ_prob)
        (fun x => _root_.MIPStarRE.QPBT.Palomar.POVM.ofMeasurement (S.M x))
        (fun x => _root_.MIPStarRE.QPBT.Palomar.POVM.ofMeasurement (S.M x))) ↔ _
  rw [_root_.MIPStarRE.QPBT.Palomar.isCommutingOn_toPMF_iff]
  rfl



end SymmetricStrategy

end MIPStarRE.QPBT.Palomar

/- Source helpers from QPBT/Palomar/LowDegreeGameStrategyBridge.lean. -/
/-!
# Strategy bridge for the compact low individual degree game

This module transports compact strategies across the exact question and answer
equivalences of `LowDegreeGameBridge`.  The transported game is the existing
low-degree game, and every compact strategy has exactly the same Born value
after conversion through the Palomar foundation bridge.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

noncomputable section

namespace POVM





/-- Outcome relabeling preserves projectivity exactly. -/
theorem relabel_isProjective_iff {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq I] (e : A ≃ B) (M : _root_.MIPStarRE.QPBT.Palomar.POVM A I) :
    (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel e M).IsProjective ↔ M.IsProjective := by
  constructor
  · intro h a
    simpa using h (e a)
  · intro h b
    exact h (e.symm b)

end POVM



namespace Strategy







/-- A double finite sum is invariant under equivalences of both indices. -/
private theorem sum_equiv₂ {A B A' B' : Type*} [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] (eA : A ≃ A') (eB : B ≃ B')
    (f : A → B → ℝ) :
    (∑ a : A', ∑ b : B', f (eA.symm a) (eB.symm b)) =
      ∑ a : A, ∑ b : B, f a b := by
  calc
    (∑ a : A', ∑ b : B', f (eA.symm a) (eB.symm b)) =
        ∑ a : A, ∑ b : B', f a (eB.symm b) :=
      Equiv.sum_comp eA.symm (fun a => ∑ b : B', f a (eB.symm b))
    _ = ∑ a : A, ∑ b : B, f a b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Equiv.sum_comp eB.symm (f a)

/-- Simultaneous relabeling of a compact game and strategy preserves value exactly. -/
theorem value_relabel {X Y A B X' Y' A' B' : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
    [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
    [DecidableEq X'] [DecidableEq Y'] [DecidableEq A'] [DecidableEq B']
    (G : _root_.MIPStarRE.QPBT.Palomar.Game X Y A B) (S : _root_.MIPStarRE.QPBT.Palomar.Strategy X Y A B)
    (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B') :
    (_root_.MIPStarRE.QPBT.Palomar.Strategy.relabel S eX eY eA eB).value (_root_.MIPStarRE.QPBT.Palomar.Game.relabel G eX eY eA eB) =
      S.value G := by
  unfold _root_.MIPStarRE.QPBT.Palomar.Strategy.value
  change _root_.LIDT.PMF.realWeightedSum (G.μ.map (Equiv.prodCongr eX eY)) _ =
    _root_.LIDT.PMF.realWeightedSum G.μ _
  rw [_root_.LIDT.PMF.realWeightedSum_map]
  apply congrArg (_root_.LIDT.PMF.realWeightedSum G.μ)
  funext xy
  simp only [_root_.MIPStarRE.QPBT.Palomar.Game.relabel, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    _root_.MIPStarRE.QPBT.Palomar.Strategy.outcomeWeight_relabel, Equiv.symm_apply_apply]
  exact sum_equiv₂ eA eB (fun a b =>
    if G.decide xy.1 xy.2 a b then S.outcomeWeight xy.1 xy.2 a b else 0)

end Strategy









end

end MIPStarRE.QPBT.Palomar

/- Source helpers from QPBT/Palomar/PauliExtractionBridge.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.Palomar.compactPauliQuestionDecidableEq
/-!
# Exact bridges for compact Pauli extraction quantities

This module identifies the compact Pauli parameter record, prescribed-answer
effects, ideal projectors, witnesses, and extraction errors with the registered
QPBT definitions.  Every comparison is an equality; no quantitative estimate
or soundness assumption is introduced here.

The legacy import form is required because the registered soundness modules
have not yet been converted to Lean's module system.

## References

`references/qpbt-paper/04_preliminaries.tex:1052-1208`;
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1491`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section

attribute [local instance] _root_.MIPStarRE.QPBT.Palomar.compactPauliQuestionDecidableEq















/-- The concrete compact SPCC predicate is exactly the transported symmetric-game predicate. -/
theorem isPauliSPCC_iff_isSPCC (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (S : _root_.MIPStarRE.QPBT.Palomar.SymmetricPauliStrategy (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P)
      (_root_.MIPStarRE.QPBT.PauliScalar P)) :
    S.IsPauliSPCC (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P)
        (_root_.MIPStarRE.QPBT.binaryRepresentation P.model) ↔
      S.IsSPCC (_root_.MIPStarRE.QPBT.Palomar.pauliSymmetricGame P) := by
  unfold _root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.IsPauliSPCC _root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.IsSPCC
  have hgame := congrArg _root_.MIPStarRE.QPBT.Palomar.Game.μ
    (_root_.MIPStarRE.QPBT.Palomar.pauliSymmetricGame_toGame P)
  have hmu : (_root_.MIPStarRE.QPBT.Palomar.pauliSymmetricGame P).μ =
      _root_.MIPStarRE.QPBT.Palomar.pauliQuestionPMF (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P)
        (_root_.MIPStarRE.QPBT.binaryRepresentation P.model) := by
    simpa only [_root_.MIPStarRE.QPBT.Palomar.pauliGame] using hgame
  rw [hmu]





















end

end MIPStarRE.QPBT.Palomar

/- Source helpers from QPBT/Palomar/PauliGameStrategyBridge.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.Palomar.compactPauliQuestionDecidableEq
/-!
# Strategy bridge for the compact Pauli basis game

This module transports compact strategies across the exact question and answer
equivalences of `PauliGameBridge`.  It preserves the game, Born value,
projectivity, symmetry, consistency, positive-support commutation, and the SPCC
predicate exactly.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1491`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section





namespace POVM

/-- Outcome relabeling preserves state-dependent consistency exactly. -/
theorem relabel_isConsistentOn_iff {A B I : Type*} [Fintype A] [Fintype B]
    [Fintype I] [DecidableEq A] [DecidableEq B] [DecidableEq I]
    (e : A ≃ B) (M : _root_.MIPStarRE.QPBT.Palomar.POVM A I) (ψ : EuclideanSpace ℂ (I × I)) :
    (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel e M).IsConsistentOn ψ ↔ M.IsConsistentOn ψ := by
  constructor
  · intro h a
    simpa using h (e a)
  · intro h b
    exact h (e.symm b)

end POVM







namespace SymmetricStrategy





/-- Symmetric relabeling preserves projectivity of the measurement family exactly. -/
theorem relabel_isProjective_iff {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    (S : _root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A') :
    (∀ x, ((_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.relabel S eX eA).meas x).IsProjective) ↔
      ∀ x, (S.meas x).IsProjective := by
  constructor
  · intro h x
    have hx := h (eX x)
    change (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel eA (S.meas (eX.symm (eX x)))).IsProjective at hx
    rw [eX.symm_apply_apply] at hx
    exact (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel_isProjective_iff eA (S.meas x)).mp hx
  · intro h x
    exact (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel_isProjective_iff eA (S.meas (eX.symm x))).mpr
      (h (eX.symm x))

/-- Symmetric relabeling preserves consistency exactly. -/
theorem relabel_isConsistent_iff {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    [DecidableEq A] [DecidableEq A']
    (S : _root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A') :
    (_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.relabel S eX eA).IsConsistent ↔ S.IsConsistent := by
  constructor
  · intro h x
    have hx := h (eX x)
    change (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel eA (S.meas (eX.symm (eX x)))).IsConsistentOn S.ψ at hx
    rw [eX.symm_apply_apply] at hx
    exact (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel_isConsistentOn_iff eA (S.meas x) S.ψ).mp hx
  · intro h x
    exact (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel_isConsistentOn_iff eA (S.meas (eX.symm x)) S.ψ).mpr
      (h (eX.symm x))

/-- Symmetric relabeling preserves the SPCC predicate under the exact PMF push-forward. -/
theorem relabel_isSPCC_iff {X A X' A' : Type}
    [Fintype X] [Fintype A] [Fintype X'] [Fintype A']
    [DecidableEq X] [DecidableEq A] [DecidableEq X'] [DecidableEq A']
    (G : _root_.MIPStarRE.QPBT.Palomar.SymmetricGame X A) (G' : _root_.MIPStarRE.QPBT.Palomar.SymmetricGame X' A')
    (S : _root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy X A) (eX : X ≃ X') (eA : A ≃ A')
    (hμ : G.μ.map (Equiv.prodCongr eX eX) = G'.μ) :
    (_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.relabel S eX eA).IsSPCC G' ↔ S.IsSPCC G := by
  rw [_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.IsSPCC, _root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.IsSPCC, ← hμ]
  constructor
  · rintro ⟨hproj, hcons, hcomm⟩
    exact ⟨(_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.relabel_isProjective_iff S eX eA).mp hproj,
      (_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.relabel_isConsistent_iff S eX eA).mp hcons,
      (_root_.MIPStarRE.QPBT.Palomar.isCommutingOn_relabel_iff G.μ S.meas S.meas eX eX eA eA).mp hcomm⟩
  · rintro ⟨hproj, hcons, hcomm⟩
    exact ⟨(_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.relabel_isProjective_iff S eX eA).mpr hproj,
      (_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.relabel_isConsistent_iff S eX eA).mpr hcons,
      (_root_.MIPStarRE.QPBT.Palomar.isCommutingOn_relabel_iff G.μ S.meas S.meas eX eX eA eA).mpr hcomm⟩

end SymmetricStrategy





















end

end MIPStarRE.QPBT.Palomar

/-!
# Compact Pauli basis test completeness

This module transports the registered value-one SPCC strategy to the compact
Palomar game.  Its public statement uses the concrete Pauli SPCC predicate and
the once-and-for-all field model, while symmetric-game and relabeling objects
occur only in the proof.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`,
paper `lem:pauli-completeness`.
-/



open MIPStarRE.QPBT.Palomar

theorem solution (P : _root_.MIPStarRE.QPBT.Palomar.PauliParams) :
    ∃ S : _root_.MIPStarRE.QPBT.Palomar.SymmetricPauliStrategy P
        (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K,
      S.IsPauliSPCC P
          (_root_.MIPStarRE.QPBT.binaryRepresentation
            (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) ∧
      S.toStrategy.value
          (_root_.MIPStarRE.QPBT.Palomar.pauliGame P
            (_root_.MIPStarRE.QPBT.binaryRepresentation
              (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))
            (_root_.MIPStarRE.QPBT.fixedBinTrace
              (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))) = 1 := by
  classical
  let Q := P.toAdmissibleParams
  obtain ⟨T, hspcc, hvalue⟩ := _root_.MIPStarRE.QPBT.exists_spcc_value_one Q
  let T' := _root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.ofSymmetricStrategy T
  let S := _root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.relabel T'
    (_root_.MIPStarRE.QPBT.Palomar.pauliQuestionEquiv Q).symm (_root_.MIPStarRE.QPBT.Palomar.pauliAnswerEquivCompact Q).symm
  have hspcc' : T'.IsSPCC
      (_root_.MIPStarRE.QPBT.Palomar.SymmetricGame.ofSymmetricGame (_root_.MIPStarRE.QPBT.pauliBasisTestSymm Q)) :=
    (_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.isSPCC_ofSymmetricStrategy_iff T).2 hspcc
  have hspccS : S.IsSPCC (_root_.MIPStarRE.QPBT.Palomar.pauliSymmetricGame Q) := by
    apply (_root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.relabel_isSPCC_iff
      (_root_.MIPStarRE.QPBT.Palomar.SymmetricGame.ofSymmetricGame (_root_.MIPStarRE.QPBT.pauliBasisTestSymm Q))
      (_root_.MIPStarRE.QPBT.Palomar.pauliSymmetricGame Q) T'
      (_root_.MIPStarRE.QPBT.Palomar.pauliQuestionEquiv Q).symm (_root_.MIPStarRE.QPBT.Palomar.pauliAnswerEquivCompact Q).symm rfl).2
    exact hspcc'
  have hvalueS : S.toStrategy.value (_root_.MIPStarRE.QPBT.Palomar.pauliSymmetricGame Q).toGame = 1 := by
    calc
      S.toStrategy.value (_root_.MIPStarRE.QPBT.Palomar.pauliSymmetricGame Q).toGame =
          T'.toStrategy.value
            (_root_.MIPStarRE.QPBT.Palomar.SymmetricGame.ofSymmetricGame
              (_root_.MIPStarRE.QPBT.pauliBasisTestSymm Q)).toGame := by
        exact _root_.MIPStarRE.QPBT.Palomar.Strategy.value_relabel
          (_root_.MIPStarRE.QPBT.Palomar.SymmetricGame.ofSymmetricGame
            (_root_.MIPStarRE.QPBT.pauliBasisTestSymm Q)).toGame
          T'.toStrategy (_root_.MIPStarRE.QPBT.Palomar.pauliQuestionEquiv Q).symm
          (_root_.MIPStarRE.QPBT.Palomar.pauliQuestionEquiv Q).symm (_root_.MIPStarRE.QPBT.Palomar.pauliAnswerEquivCompact Q).symm
          (_root_.MIPStarRE.QPBT.Palomar.pauliAnswerEquivCompact Q).symm
      _ = T.toStrategy.value := _root_.MIPStarRE.QPBT.Palomar.SymmetricStrategy.value_ofSymmetricStrategy T
      _ = 1 := hvalue
  have hP : _root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams Q = P := by
    simp [Q]
  let statement : _root_.MIPStarRE.QPBT.Palomar.PauliParams → Prop := fun R =>
    ∃ U : _root_.MIPStarRE.QPBT.Palomar.SymmetricPauliStrategy R
        (_root_.MIPStarRE.QPBT.fixedFieldModel R.q R.is_admissible_size).K,
      U.IsPauliSPCC R
          (_root_.MIPStarRE.QPBT.binaryRepresentation
            (_root_.MIPStarRE.QPBT.fixedFieldModel R.q R.is_admissible_size)) ∧
        U.toStrategy.value
          (_root_.MIPStarRE.QPBT.Palomar.pauliGame R
            (_root_.MIPStarRE.QPBT.binaryRepresentation
              (_root_.MIPStarRE.QPBT.fixedFieldModel R.q R.is_admissible_size))
            (_root_.MIPStarRE.QPBT.fixedBinTrace
              (_root_.MIPStarRE.QPBT.fixedFieldModel R.q R.is_admissible_size))) = 1
  have hstatement : statement (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams Q) := by
    let R := _root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams Q
    let fieldStatement : _root_.MIPStarRE.QPBT.FixedFieldModel Q.q → Prop := fun F =>
      ∃ U : _root_.MIPStarRE.QPBT.Palomar.SymmetricPauliStrategy R F.K,
        U.IsPauliSPCC R (_root_.MIPStarRE.QPBT.binaryRepresentation F) ∧
          U.toStrategy.value
            (_root_.MIPStarRE.QPBT.Palomar.pauliGame R (_root_.MIPStarRE.QPBT.binaryRepresentation F)
              (_root_.MIPStarRE.QPBT.fixedBinTrace F)) = 1
    have hfield : fieldStatement Q.model := by
      refine ⟨S, ?_, ?_⟩
      · exact (_root_.MIPStarRE.QPBT.Palomar.isPauliSPCC_iff_isSPCC Q S).2 hspccS
      · rw [← _root_.MIPStarRE.QPBT.Palomar.pauliSymmetricGame_toGame Q]
        exact hvalueS
    have hmodel : Q.model =
        _root_.MIPStarRE.QPBT.fixedFieldModel R.q R.is_admissible_size := by
      rfl
    have htransported := Eq.mp (congrArg fieldStatement hmodel) hfield
    exact htransported
  exact Eq.mp (congrArg statement hP) hstatement
