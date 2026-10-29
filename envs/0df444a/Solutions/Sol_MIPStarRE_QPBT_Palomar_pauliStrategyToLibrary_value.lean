-- Prove2me | solution 1 for MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary_value
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:51:21.046732+00:00
-- url     : https://prove2.me/submissions/5646e4be-098b-4f1d-a986-884cc1e8f52b

-- Generated proof for MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary_value.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Palomar_Bridge
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_eq_toPMF_realWeightedSum
import Theorems.Thm_LIDT_PMF_realWeightedSum_map

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

/-!
# Strategy bridge for the compact Pauli basis game

This module transports compact strategies across the exact question and answer
equivalences of `PauliGameBridge`.  It preserves the game, Born value,
projectivity, symmetry, consistency, positive-support commutation, and the SPCC
predicate exactly.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1126-1491`.
-/



open MIPStarRE.QPBT.Palomar





open MIPStarRE.QPBT.Palomar.PMF







open MIPStarRE.QPBT.Palomar.POVM







open MIPStarRE.QPBT.Palomar.Game





open MIPStarRE.QPBT.Palomar.SymmetricGame





open MIPStarRE.QPBT.Palomar.SymmetricStrategy
attribute [local instance] _root_.MIPStarRE.QPBT.Palomar.compactPauliQuestionDecidableEq

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    (S : _root_.MIPStarRE.QPBT.Palomar.Strategy
      (_root_.MIPStarRE.QPBT.Palomar.PauliQuestion (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P) (_root_.MIPStarRE.QPBT.PauliScalar P))
      (_root_.MIPStarRE.QPBT.Palomar.PauliQuestion (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P) (_root_.MIPStarRE.QPBT.PauliScalar P))
      (_root_.MIPStarRE.QPBT.Palomar.PauliAnswer (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P) (_root_.MIPStarRE.QPBT.PauliScalar P))
      (_root_.MIPStarRE.QPBT.Palomar.PauliAnswer (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P) (_root_.MIPStarRE.QPBT.PauliScalar P))) :
    (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P S).value =
      S.value (_root_.MIPStarRE.QPBT.Palomar.pauliGame (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P)
        (_root_.MIPStarRE.QPBT.binaryRepresentation P.model)
        (_root_.MIPStarRE.QPBT.fixedBinTrace P.model)) := by
  let S' := _root_.MIPStarRE.QPBT.Palomar.Strategy.relabel S
    (_root_.MIPStarRE.QPBT.Palomar.pauliQuestionEquiv P) (_root_.MIPStarRE.QPBT.Palomar.pauliQuestionEquiv P)
    (_root_.MIPStarRE.QPBT.Palomar.pauliAnswerEquivCompact P) (_root_.MIPStarRE.QPBT.Palomar.pauliAnswerEquivCompact P)
  calc
    (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P S).value =
        (_root_.MIPStarRE.QPBT.Palomar.Strategy.ofStrategy (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P S)).value
          (_root_.MIPStarRE.QPBT.Palomar.Game.ofGame (_root_.MIPStarRE.QPBT.pauliBasisTest P)) :=
      (_root_.MIPStarRE.QPBT.Palomar.Strategy.value_ofStrategy (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P S)).symm
    _ = S'.value (_root_.MIPStarRE.QPBT.Palomar.Game.ofGame (_root_.MIPStarRE.QPBT.pauliBasisTest P)) := by
      simp [_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary, S']
    _ = S'.value (_root_.MIPStarRE.QPBT.Palomar.Game.relabel
        (_root_.MIPStarRE.QPBT.Palomar.pauliGame (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P)
          (_root_.MIPStarRE.QPBT.binaryRepresentation P.model)
          (_root_.MIPStarRE.QPBT.fixedBinTrace P.model))
        (_root_.MIPStarRE.QPBT.Palomar.pauliQuestionEquiv P) (_root_.MIPStarRE.QPBT.Palomar.pauliQuestionEquiv P)
        (_root_.MIPStarRE.QPBT.Palomar.pauliAnswerEquivCompact P) (_root_.MIPStarRE.QPBT.Palomar.pauliAnswerEquivCompact P)) := by
      rw [_root_.MIPStarRE.QPBT.Palomar.pauliGame_relabel_eq]
    _ = S.value (_root_.MIPStarRE.QPBT.Palomar.pauliGame (_root_.MIPStarRE.QPBT.Palomar.PauliParams.ofAdmissibleParams P)
        (_root_.MIPStarRE.QPBT.binaryRepresentation P.model)
        (_root_.MIPStarRE.QPBT.fixedBinTrace P.model)) :=
      _root_.MIPStarRE.QPBT.Palomar.Strategy.value_relabel _ _ _ _ _ _
