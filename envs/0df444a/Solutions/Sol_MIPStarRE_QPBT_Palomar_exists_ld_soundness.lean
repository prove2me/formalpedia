-- Prove2me | solution 1 for MIPStarRE.QPBT.Palomar.exists_ld_soundness
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:05:35.245814+00:00
-- url     : https://prove2.me/submissions/eab0f644-223b-4a31-bbc0-16a9e53bbfc7

-- Generated proof for MIPStarRE.QPBT.Palomar.exists_ld_soundness.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Palomar_Bridge
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeConsistencyBridge
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameBridge
import Definitions.Def_QPBT_QPBT_Palomar_LowDegreeGameStrategyBridge
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_LDT_avgOver_eq_toPMF_realWeightedSum
import Theorems.Thm_MIPStarRE_QPBT_Palomar_Strategy_relabel_isProjective_iff
import Theorems.Thm_MIPStarRE_QPBT_Palomar_lowDegreeStrategyToLibrary_value
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_congr
import Theorems.Thm_MIPStarRE_QPBT_exists_ld_soundness

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar
namespace MIPStarRE.QPBT.Palomar.Game
end MIPStarRE.QPBT.Palomar.Game
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



















/-- Projectivity is unchanged by compact-to-library conversion. -/
theorem isProjective_toStrategy_iff {G : _root_.MIPStarRE.QPBT.Game}
    (S : _root_.MIPStarRE.QPBT.Palomar.Strategy G.QuestionA G.QuestionB G.AnswerA G.AnswerB) :
    (_root_.MIPStarRE.QPBT.Palomar.Strategy.toStrategy S).IsProjective ↔ S.IsProjective :=
  Iff.rfl

end Strategy











end MIPStarRE.QPBT.Palomar

/- Source helpers from QPBT/Palomar/LowDegreeConsistencyBridge.lean. -/
/-!
# Exact bridges for compact low-degree consistency

This module identifies the compact effect sums and three low-degree defects
with the corresponding library measurements and consistency defects.  It also
gives the inverse numerical-record conversion needed to apply the registered
soundness theorem to compact parameters.

## References

`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248` and
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:394-440`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT.Palomar

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section











/-- Relabeling before effect-level postprocessing only transports the relabeling map. -/
theorem postprocessEffect_relabel {A B C I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [DecidableEq C]
    [Fintype I] [DecidableEq I] (e : A ≃ B) (M : _root_.MIPStarRE.QPBT.Palomar.POVM A I)
    (f : B → C) (c : C) :
    _root_.MIPStarRE.QPBT.Palomar.postprocessEffect (_root_.MIPStarRE.QPBT.Palomar.POVM.relabel e M) f c =
      _root_.MIPStarRE.QPBT.Palomar.postprocessEffect M (fun a => f (e a)) c := by
  simp only [_root_.MIPStarRE.QPBT.Palomar.postprocessEffect, _root_.MIPStarRE.QPBT.Palomar.POVM.relabel_effect, Finset.sum_filter]
  rw [← Equiv.sum_comp e.symm
    (fun a => if f (e a) = c then M.effect a else 0)]
  simp

/-- The library postprocessing of a relabeled compact POVM is the compact effect sum. -/
theorem toMeasurement_relabel_postprocess_effect {A B C I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype I] [DecidableEq I]
    (e : A ≃ B) (M : _root_.MIPStarRE.QPBT.Palomar.POVM A I) (f : B → C) (c : C) :
    (((_root_.MIPStarRE.QPBT.Palomar.POVM.relabel e M).toMeasurement).postprocess f).effect c =
      _root_.MIPStarRE.QPBT.Palomar.postprocessEffect M (fun a => f (e a)) c := by
  rw [← _root_.MIPStarRE.QPBT.Palomar.postprocessEffect_ofMeasurement]
  exact _root_.MIPStarRE.QPBT.Palomar.postprocessEffect_relabel e M f c







/-- Alice's point-answer effect is unchanged by strategy and answer transport. -/
theorem lowDegreeStrategyToLibrary_alice_point_effect
    (L : _root_.MIPStarRE.QPBT.LdParams)
    (S : _root_.MIPStarRE.QPBT.Palomar.LowDegreeStrategy (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams L)
      (_root_.MIPStarRE.QPBT.ScalarQ L))
    (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (a : Fin L.k → _root_.MIPStarRE.QPBT.ScalarQ L) :
    ((((_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary L S).A (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
      (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect a) =
        _root_.MIPStarRE.QPBT.Palomar.postprocessEffect (S.alice (_root_.MIPStarRE.QPBT.Palomar.lowDegreePointQuestion
          (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams L) u)) _root_.MIPStarRE.QPBT.Palomar.lowDegreePointValuesOrZero a := by
  change ((((_root_.MIPStarRE.QPBT.Palomar.POVM.relabel (_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv L)
    (S.alice ((_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv L).symm
      (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)))).toMeasurement).postprocess
      (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect a) = _
  rw [_root_.MIPStarRE.QPBT.Palomar.toMeasurement_relabel_postprocess_effect]
  simp

/-- Bob's point-answer effect is unchanged by strategy and answer transport. -/
theorem lowDegreeStrategyToLibrary_bob_point_effect
    (L : _root_.MIPStarRE.QPBT.LdParams)
    (S : _root_.MIPStarRE.QPBT.Palomar.LowDegreeStrategy (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams L)
      (_root_.MIPStarRE.QPBT.ScalarQ L))
    (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (a : Fin L.k → _root_.MIPStarRE.QPBT.ScalarQ L) :
    ((((_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary L S).B (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
      (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect a) =
        _root_.MIPStarRE.QPBT.Palomar.postprocessEffect (S.bob (_root_.MIPStarRE.QPBT.Palomar.lowDegreePointQuestion
          (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams L) u)) _root_.MIPStarRE.QPBT.Palomar.lowDegreePointValuesOrZero a := by
  change ((((_root_.MIPStarRE.QPBT.Palomar.POVM.relabel (_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv L)
    (S.bob ((_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv L).symm
      (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)))).toMeasurement).postprocess
      (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect a) = _
  rw [_root_.MIPStarRE.QPBT.Palomar.toMeasurement_relabel_postprocess_effect]
  simp

/-- The compact PMF defect is exactly the library defect for the same distribution. -/
theorem consistencyDefect_toPMF {X O I J : Type*}
    [Fintype X] [DecidableEq X] [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (hμ : μ.IsProbability)
    (A : X → O → Matrix I I ℂ) (B : X → O → Matrix J J ℂ)
    (ψ : EuclideanSpace ℂ (I × J)) :
    _root_.MIPStarRE.QPBT.Palomar.consistencyDefect (μ.toPMF hμ) A B ψ =
      _root_.MIPStarRE.QPBT.consistencyDefect μ
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron (A x a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 (B x a)) ψ := by
  unfold _root_.MIPStarRE.QPBT.Palomar.consistencyDefect _root_.MIPStarRE.QPBT.consistencyDefect
  rw [_root_.LIDT.MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum μ hμ]
  simp only [_root_.LIDT.PMF.realWeightedSum, smul_eq_mul, _root_.MIPStarRE.QPBT.heteroKron]

/-- The compact point--polynomial defect is exactly the registered first defect. -/
theorem ldPointPolynomialDefect_ofMeasurement_eq
    (L : _root_.MIPStarRE.QPBT.LdParams)
    (S : _root_.MIPStarRE.QPBT.Palomar.LowDegreeStrategy (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams L)
      (_root_.MIPStarRE.QPBT.ScalarQ L))
    (GB : _root_.MIPStarRE.QPBT.PolyMeasTuple L S.ιB) :
    _root_.MIPStarRE.QPBT.Palomar.ldPointPolynomialDefect (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams L) S
        (_root_.MIPStarRE.QPBT.Palomar.POVM.ofMeasurement GB) =
      _root_.MIPStarRE.QPBT.consistencyDefect
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
          ((((_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary L S).A
            (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
              (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect outcome) 1)
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
          ((GB.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome))
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary L S).ψ := by
  unfold _root_.MIPStarRE.QPBT.Palomar.ldPointPolynomialDefect
  rw [← _root_.LIDT.MIPStarRE.LDT.uniformDistribution_toPMF]
  rw [_root_.MIPStarRE.QPBT.Palomar.consistencyDefect_toPMF]
  apply _root_.MIPStarRE.QPBT.consistencyDefect_congr
  · intro u outcome
    rw [_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary_alice_point_effect]
    rfl
  · intro u outcome
    simp only [_root_.MIPStarRE.QPBT.Palomar.postprocessEffect_ofMeasurement]
    rfl

/-- The compact polynomial--point defect is exactly the registered second defect. -/
theorem ldPolynomialPointDefect_ofMeasurement_eq
    (L : _root_.MIPStarRE.QPBT.LdParams)
    (S : _root_.MIPStarRE.QPBT.Palomar.LowDegreeStrategy (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams L)
      (_root_.MIPStarRE.QPBT.ScalarQ L))
    (GA : _root_.MIPStarRE.QPBT.PolyMeasTuple L S.ιA) :
    _root_.MIPStarRE.QPBT.Palomar.ldPolynomialPointDefect (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams L) S
        (_root_.MIPStarRE.QPBT.Palomar.POVM.ofMeasurement GA) =
      _root_.MIPStarRE.QPBT.consistencyDefect
        (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L))
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
          ((GA.postprocess (_root_.MIPStarRE.QPBT.evalPolyTupleAt u)).effect outcome) 1)
        (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
          ((((_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary L S).B
            (_root_.MIPStarRE.QPBT.ldPointQuestionOf L u)).postprocess
              (_root_.MIPStarRE.QPBT.ldPointValuesOrZero L)).effect outcome))
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary L S).ψ := by
  unfold _root_.MIPStarRE.QPBT.Palomar.ldPolynomialPointDefect
  rw [← _root_.LIDT.MIPStarRE.LDT.uniformDistribution_toPMF]
  rw [_root_.MIPStarRE.QPBT.Palomar.consistencyDefect_toPMF]
  apply _root_.MIPStarRE.QPBT.consistencyDefect_congr
  · intro u outcome
    simp only [_root_.MIPStarRE.QPBT.Palomar.postprocessEffect_ofMeasurement]
    rfl
  · intro u outcome
    rw [_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary_bob_point_effect]
    rfl

/-- The compact polynomial--polynomial defect is exactly the registered third defect. -/
theorem ldPolynomialPolynomialDefect_ofMeasurement_eq
    (L : _root_.MIPStarRE.QPBT.LdParams)
    (S : _root_.MIPStarRE.QPBT.Palomar.LowDegreeStrategy (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams L)
      (_root_.MIPStarRE.QPBT.ScalarQ L))
    (GA : _root_.MIPStarRE.QPBT.PolyMeasTuple L S.ιA)
    (GB : _root_.MIPStarRE.QPBT.PolyMeasTuple L S.ιB) :
    _root_.MIPStarRE.QPBT.Palomar.ldPolynomialPolynomialDefect (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams L) S
        (_root_.MIPStarRE.QPBT.Palomar.POVM.ofMeasurement GA) (_root_.MIPStarRE.QPBT.Palomar.POVM.ofMeasurement GB) =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
        (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g))
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary L S).ψ := by
  unfold _root_.MIPStarRE.QPBT.Palomar.ldPolynomialPolynomialDefect
  rw [← _root_.LIDT.MIPStarRE.LDT.uniformDistribution_toPMF]
  rw [_root_.MIPStarRE.QPBT.Palomar.consistencyDefect_toPMF]
  rfl



end


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













/-- Conversion to the registered low-degree game preserves projectivity exactly. -/
theorem lowDegreeStrategyToLibrary_isProjective_iff (P : _root_.MIPStarRE.QPBT.LdParams)
    (S : _root_.MIPStarRE.QPBT.Palomar.Strategy
      (_root_.MIPStarRE.QPBT.Palomar.LowDegreeQuestion (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P) (_root_.MIPStarRE.QPBT.ScalarQ P))
      (_root_.MIPStarRE.QPBT.Palomar.LowDegreeQuestion (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P) (_root_.MIPStarRE.QPBT.ScalarQ P))
      (_root_.MIPStarRE.QPBT.Palomar.LowDegreeAnswer (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P) (_root_.MIPStarRE.QPBT.ScalarQ P))
      (_root_.MIPStarRE.QPBT.Palomar.LowDegreeAnswer (_root_.MIPStarRE.QPBT.Palomar.LowDegreeParams.ofLdParams P) (_root_.MIPStarRE.QPBT.ScalarQ P))) :
    (_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary P S).IsProjective ↔ S.IsProjective := by
  change (_root_.MIPStarRE.QPBT.Palomar.Strategy.toStrategy (G := _root_.MIPStarRE.QPBT.ldGame P)
      (_root_.MIPStarRE.QPBT.Palomar.Strategy.relabel S
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P) (_root_.MIPStarRE.QPBT.Palomar.lowDegreeQuestionEquiv P)
        (_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P) (_root_.MIPStarRE.QPBT.Palomar.lowDegreeAnswerEquiv P))).IsProjective ↔
    S.IsProjective
  rw [_root_.MIPStarRE.QPBT.Palomar.Strategy.isProjective_toStrategy_iff]
  exact _root_.MIPStarRE.QPBT.Palomar.Strategy.relabel_isProjective_iff _ _ _ _ _

end

end MIPStarRE.QPBT.Palomar

/-!
# Compact low-degree soundness

This module transports the registered low-degree soundness theorem to the
compact Palomar game surface, preserving its constants, parameter domain,
quantifier order, and three separate consistency conclusions.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-440`,
paper `lem:ld-soundness`.
-/



open MIPStarRE.QPBT.Palomar

theorem solution :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b ≤ 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.Palomar.LowDegreeParams) (ε : ℝ), 0 < ε →
        ∀ S : _root_.MIPStarRE.QPBT.Palomar.LowDegreeStrategy P (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
            P.is_admissible_size).K,
          S.IsProjective →
          1 - ε ≤ S.value (_root_.MIPStarRE.QPBT.Palomar.lowDegreeGame P
            (_root_.MIPStarRE.QPBT.binaryRepresentation
              (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
                P.is_admissible_size))) →
          ∃ GA : _root_.MIPStarRE.QPBT.Palomar.LowDegreePolynomialPOVM P
              (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
                P.is_admissible_size).K S.ιA,
            ∃ GB : _root_.MIPStarRE.QPBT.Palomar.LowDegreePolynomialPOVM P
                (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
                  P.is_admissible_size).K S.ιB,
              _root_.MIPStarRE.QPBT.Palomar.ldPointPolynomialDefect P S GB ≤
                  _root_.MIPStarRE.QPBT.Palomar.deltaLd a b ε P.q P.m P.d P.k ∧
                _root_.MIPStarRE.QPBT.Palomar.ldPolynomialPointDefect P S GA ≤
                  _root_.MIPStarRE.QPBT.Palomar.deltaLd a b ε P.q P.m P.d P.k ∧
                _root_.MIPStarRE.QPBT.Palomar.ldPolynomialPolynomialDefect P S GA GB ≤
                  _root_.MIPStarRE.QPBT.Palomar.deltaLd a b ε P.q P.m P.d P.k := by
  classical
  obtain ⟨a, b, ha, hb, hb1, hsound⟩ := _root_.MIPStarRE.QPBT.exists_ld_soundness
  refine ⟨a, b, ha, hb, hb1, ?_⟩
  rintro ⟨q, m, d, k, hm, hd, hk, hq, hdvd⟩ ε hε S hprojective hvalue
  let L : _root_.MIPStarRE.QPBT.LdParams :=
    ⟨q, m, d, k, hm, hd, hk, hq, hdvd⟩
  have hprojective' : (_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary L S).IsProjective :=
    (_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary_isProjective_iff L S).2 hprojective
  have hvalue' : 1 - ε ≤ (_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary L S).value := by
    rw [_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary_value]
    exact hvalue
  obtain ⟨GA, GB, hpointPolynomial, hpolynomialPoint, hpolynomialPolynomial⟩ :=
    hsound L ε hε (_root_.MIPStarRE.QPBT.Palomar.lowDegreeStrategyToLibrary L S) hprojective' hvalue'
  refine ⟨_root_.MIPStarRE.QPBT.Palomar.POVM.ofMeasurement GA, _root_.MIPStarRE.QPBT.Palomar.POVM.ofMeasurement GB, ?_, ?_, ?_⟩
  · exact (_root_.MIPStarRE.QPBT.Palomar.ldPointPolynomialDefect_ofMeasurement_eq L S GB).trans_le
      hpointPolynomial
  · exact (_root_.MIPStarRE.QPBT.Palomar.ldPolynomialPointDefect_ofMeasurement_eq L S GA).trans_le
      hpolynomialPoint
  · exact (_root_.MIPStarRE.QPBT.Palomar.ldPolynomialPolynomialDefect_ofMeasurement_eq L S GA GB).trans_le
      hpolynomialPolynomial
