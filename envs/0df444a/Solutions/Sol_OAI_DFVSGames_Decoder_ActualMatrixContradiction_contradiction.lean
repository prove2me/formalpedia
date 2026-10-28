-- Prove2me | solution 1 for OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:46:01.405519+00:00
-- url     : https://prove2.me/submissions/4b2fbf3a-262e-40e7-bbd0-53d3b13700c5

import Mathlib
import Definitions.Def_OAIQ085D016
import Definitions.Def_OAIQ085D017
import Definitions.Def_OAIQ085D022
import Definitions.Def_OAIQ085D024
import Theorems.Thm_OAI_DFVSGames_Decoder_ActualProjectedTransfer_actual_success_lower

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_FormulaEncoding
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerFiniteDimensional _root_.OAI.DFVSGames.Soundness.PartnerLinear.partnerModule _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceFiniteDimensional _root_.OAI.DFVSGames.Soundness.PartnerLinear.sourceModule _root_.OAI.DFVSGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.DFVSGames.Soundness.RawMapLaw.rawMapsFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Integration.BinaryLinear

open BinaryCoordinates

theorem toBit_add : ∀ a b : F2, toBit (a + b) = (toBit a ^^ toBit b) := by decide

end DFVSGames.Integration.BinaryLinear


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_Basic
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace Game
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]

variable [Nonempty A₁] [Nonempty A₂]

theorem exists_deterministic_ge_stochastic (G : Game Q₁ Q₂ A₁ A₂)
    (responses₁ : Q₁ → FiniteDistribution A₁)
    (responses₂ : Q₂ → FiniteDistribution A₂) :
    ∃ strategy : Strategy Q₁ Q₂ A₁ A₂,
      G.stochasticSuccess responses₁ responses₂ ≤ G.success strategy := by
  obtain ⟨strategy, h⟩ := G.exists_optimal_strategy
  refine ⟨strategy, ?_⟩
  rw [h]
  exact G.stochasticSuccess_le_value responses₁ responses₂
end Game
end
end DFVSGames.Foundations.Games


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ChainRule
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

theorem probability_and_le_left (μ : FiniteDistribution Ω) (event event' : Ω → Bool) :
    μ.probability (fun x => event x && event' x) ≤ μ.probability event := by
  apply μ.probability_mono
  intro x hx
  have h : event x = true ∧ event' x = true := by simpa using hx
  exact h.1

theorem probability_and_eq_zero_of_probability_eq_zero (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (zero : μ.probability given = 0) :
    μ.probability (fun x => given x && event x) = 0 := by
  apply le_antisymm
  · exact (μ.probability_and_le_left given event).trans_eq zero
  · exact μ.probability_nonnegative _

end FiniteDistribution

end

end DFVSGames.Foundations.Games


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_TensorDomination
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Repetition


open DFVSGames.Foundations.Games
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem clean_repetition_value
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (n : ℕ)
    (hvalue : G.value ≤ (14 : ℝ) / 15) :
    (G.repetition n).value ≤ (1 - (1 : ℝ) / 3600) ^ n := by
  have hv : G.value ≤ 1 - (1 : ℝ) / 15 := by convert hvalue using 1 ; norm_num
  have h := projection_repetition_value G hG n
    (gap := (1 : ℝ) / 15) (by norm_num) (by norm_num) hv
  norm_num at h ⊢
  exact h

end
end DFVSGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_KernelCardinality
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.secondInputFintype _root_.OAI.DFVSGames.Soundness.PartnerMapCoordinates.partnerMapsFintype _root_.OAI.DFVSGames.Soundness.RawMapLaw.rawMapsFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.PartnerLinear

open PartnerProjection
open DFVSGames.Integration.BinaryLinear (F2 ofBit toBit scalar_cases ofBit_toBit
  toBit_ofBit ofBit_xor)

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

theorem projection_apply (x : SourcePoint rhs) :
    projection rhs active slot x = project rhs active slot x := rfl

end DFVSGames.Soundness.PartnerLinear


namespace DFVSGames.Soundness.ZeroInformation

theorem rowSum_congr {P R : Type} (positions : List P) (a b : P → Bits R)
    (h : ∀ j, a j = b j) : rowSum positions a = rowSum positions b := by
  have hab : a = b := funext h
  rw [hab]

theorem pullbackRow_index_independent {P R : Type} (positions : List P)
    (single : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (i i' : P → Fin 3)
    (agrees : ∀ j, single j = true → omega j ≠ zero → i j = i' j)
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    pullbackRow positions single zeta0 zeta1 zeta2 omega i homogeneous x =
      pullbackRow positions single zeta0 zeta1 zeta2 omega i' homogeneous x := by
  unfold pullbackRow
  congr 1
  apply rowSum_congr
  intro j
  cases hs : single j
  · simp
  · simp only [↓reduceIte]
    by_cases hz : omega j = zero
    · simp [hz]
    · rw [agrees j hs hz]

theorem decodeIndex_name {O N : Type} (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i') (o : O) (i : Fin 3) :
    decodeIndex name o (name o i) = i := by
  classical
  unfold decodeIndex
  have he : ∃ i', name o i' = name o i := ⟨i, rfl⟩
  simp only [he, ↓reduceDIte]
  exact distinct o _ i (Classical.choose_spec he)

theorem reconstructQuestion_actual {P X : Type} (hidden : P → Bool)
    (actual outside : P → X) (houtside : ∀ j, hidden j = false → outside j = actual j) :
    reconstructQuestion hidden actual outside = actual := by
  funext j
  cases hj : hidden j
  · simp [reconstructQuestion, hj, houtside j hj]
  · simp [reconstructQuestion, hj]

theorem first_input_reconstruction {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (hidden_zero : ∀ j, hidden j = true → omega j = zero)
    (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (occurrences outsideOccurrences : P → O) (indices : P → Fin 3)
    (outsideNames : P → N)
    (houtsideO : ∀ j, hidden j = false → outsideOccurrences j = occurrences j)
    (houtsideN : ∀ j, hidden j = false → outsideNames j = name (occurrences j) (indices j)) :
    reconstructFirst positions single hidden zeta0 zeta1 zeta2 omega name
        occurrences outsideOccurrences outsideNames =
      firstInput positions single zeta0 zeta1 zeta2 omega occurrences indices := by
  unfold reconstructFirst firstInput
  rw [reconstructQuestion_actual hidden occurrences outsideOccurrences houtsideO]
  congr 1
  funext homogeneous x
  apply pullbackRow_index_independent
  intro j _ hz
  have hj : hidden j = false := by
    cases hh : hidden j
    · rfl
    · exact False.elim (hz (hidden_zero j hh))
  rw [houtsideO j hj, houtsideN j hj]
  exact decodeIndex_name name distinct (occurrences j) (indices j)

theorem second_input_reconstruction {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (hidden_single : ∀ j, hidden j = true → single j = true)
    (occurrences outsideOccurrences : P → O) (names outsideNames : P → N)
    (houtsideO : ∀ j, hidden j = false → outsideOccurrences j = occurrences j)
    (houtsideN : ∀ j, hidden j = false → outsideNames j = names j) :
    reconstructSecond positions single hidden zeta0 zeta1 zeta2 omega
        outsideOccurrences names outsideNames =
      secondInput positions single zeta0 zeta1 zeta2 omega occurrences names := by
  unfold reconstructSecond secondInput
  rw [reconstructQuestion_actual hidden names outsideNames houtsideN]
  congr 1
  funext j
  unfold partnerQuestion
  cases hs : single j
  · have hj : hidden j = false := by
      cases hh : hidden j
      · rfl
      · have contradiction := hidden_single j hh
        rw [hs] at contradiction
        contradiction
    simp [houtsideO j hj]
  · simp

end DFVSGames.Soundness.ZeroInformation

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ConditionalIncidences
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalIncidences.zeroBits _root_.OAI.DFVSGames.Soundness.RawMapLaw.rawMapsFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped BigOperators

namespace DFVSGames.Soundness.PartnerMapCoordinates

open PartnerProjection
open ConditionalIncidences (PositionInside PositionOutside RawSlot RawCoefficients )
open DFVSGames.Integration.BinaryLinear (F2 ofBit toBit)

noncomputable section

variable {P : Type} [DecidableEq P] (rhs : P → Bool) (J : Finset P)

variable [Fintype P]

variable (R : Type) [AddCommGroup R] [Module F2 R]

theorem mapEquiv_expansion (gamma : RawCoefficients J R) (y : PartnerPoint rhs (activeOf J)) :
    mapEquiv rhs J R gamma y =
      ofBit y.homogeneous • gamma none +
        (∑ j : PositionOutside J,
          (ofBit (y.full j.val).first • gamma (some (.inl (j, 0))) +
            ofBit (y.full j.val).second • gamma (some (.inl (j, 1))))) +
        ∑ j : PositionInside J, ofBit (y.single j.val) • gamma (some (.inr j)) := by
  rw [mapEquiv_apply, Fintype.sum_option, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, pointEquiv_none, pointEquiv_full_first,
    pointEquiv_full_second, pointEquiv_single]
  simp only [add_assoc]

theorem pullback_expansion (gamma : RawCoefficients J R) (slot : P → Slot)
    (x : SourcePoint rhs) :
    mapEquiv rhs J R gamma (PartnerLinear.projection rhs (activeOf J) slot x) =
      ofBit x.homogeneous • gamma none +
        (∑ j : PositionOutside J,
          (ofBit (x.coordinates j.val).first • gamma (some (.inl (j, 0))) +
            ofBit (x.coordinates j.val).second • gamma (some (.inl (j, 1))))) +
        ∑ j : PositionInside J,
          ofBit (retained (slot j.val) (x.coordinates j.val)) • gamma (some (.inr j)) := by
  rw [mapEquiv_expansion]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [PartnerLinear.projection_apply, project, activeOf, j.property]
  · apply Finset.sum_congr rfl
    intro j _
    simp [PartnerLinear.projection_apply, project, activeOf, j.property]

end

end DFVSGames.Soundness.PartnerMapCoordinates
end

namespace DFVSGames.Soundness.IncidenceExtraction

theorem Incidence.accepts_implies_namedAccepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name) (o : Occurrence) (i : Fin 3)
    (a : Triple) (b : Bool) (h : g.accepts o i a b) :
    g.namedAccepts o (g.name o i) a b :=
  ⟨i, rfl, h⟩

theorem Incidence.namedAccepts_iff_accepts {Occurrence Name : Type}
    (g : Incidence Occurrence Name)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (o : Occurrence) (i : Fin 3) (a : Triple) (b : Bool) :
    g.namedAccepts o (g.name o i) a b ↔ g.accepts o i a b := by
  constructor
  · rintro ⟨j, hname, h⟩
    have hji := distinct o j i hname
    simpa [hji] using h
  · exact g.accepts_implies_namedAccepts o i a b

theorem LocalSimulation.induced_wins
    {InnerQA InnerQB InnerA InnerB OuterQA OuterQB OuterA OuterB : Type}
    {inner : Game InnerQA InnerQB InnerA InnerB}
    {outer : Game OuterQA OuterQB OuterA OuterB}
    (r : LocalSimulation inner outer)
    (s : Strategies OuterQA OuterQB OuterA OuterB)
    (qa : InnerQA) (qb : InnerQB)
    (hwins : s.wins outer (r.questionA qa) (r.questionB qb)) :
    (r.induced s).wins inner qa qb :=
  r.sound qa qb (s.first (r.questionA qa)) (s.second (r.questionB qb)) hwins

end DFVSGames.Soundness.IncidenceExtraction

namespace DFVSGames.Soundness.ConcreteExtraction

open PartnerProjection IncidenceExtraction

theorem parity_coordinates (x : PartnerProjection.Triple) :
    IncidenceExtraction.xorTriple (tripleCoordinates x) = PartnerProjection.parity x := rfl

theorem retained_coordinates (x : PartnerProjection.Triple) (i : PartnerProjection.Slot) :
    tripleCoordinates x (slotIndex i) = PartnerProjection.retained i x := by
  cases i <;> rfl

end DFVSGames.Soundness.ConcreteExtraction

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualCanonical
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.secondInputFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Soundness.ActualCanonicalPullback

open scoped BigOperators
open PartnerProjection PartnerMapCoordinates
open ConditionalIncidences
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction

noncomputable section

variable {k : Nat} (rhsB : Fin k → Bool) (J : Finset (Fin k))
variable (R : Type) [AddCommGroup R] [Module F2 R]

omit [Module F2 R] in
theorem sum_outside_inside (f : PositionOutside J → R) (g : PositionInside J → R) :
    (∑ j, f j) + (∑ j, g j) =
      ∑ j : Fin k, if hj : j ∈ J then g ⟨j,hj⟩ else f ⟨j,hj⟩ := by
  rw [← (outsideInsideEquiv J).sum_comp]
  rw [Fintype.sum_sum_type]
  congr 1 <;> apply Finset.sum_congr rfl
  · intro j _
    simp [outsideInsideEquiv, j.property]
  · intro j _
    simp [outsideInsideEquiv, j.property]

end
end DFVSGames.Soundness.ActualCanonicalPullback

namespace DFVSGames.Soundness.ConditionalIncidences

noncomputable section

theorem singleCoefficient_zero {P R : Type} [DecidableEq P]
    [Fintype R] [DecidableEq R] (J : Finset P)
    (gamma : RawCoefficients J (ZeroInformation.Bits R)) (j : P)
    (hj : j ∈ zeroSet J gamma) : singleCoefficient J gamma j = ZeroInformation.zero := by
  obtain ⟨hjJ, hz⟩ := (mem_zeroSet J gamma j).mp hj
  change gamma (some (.inr ⟨j, hjJ⟩)) = ZeroInformation.zero at hz
  simpa only [singleCoefficient, hjJ, ↓reduceDIte] using hz

variable {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  (J : Finset P) (name : O → Fin 3 → N)
  (gamma : RawCoefficients J (ZeroInformation.Bits R))
  (observed : PositionOutside (zeroSet J gamma) → O × N)

omit [Fintype P] [DecidableEq R] in
theorem outside_pair_agree (reference sample : RawObservationFibre J name gamma observed)
    (j : P) (hj : j ∉ zeroSet J gamma) :
    incidence name (reference.val.2 j) = incidence name (sample.val.2 j) := by
  exact congrFun (reference.property.2.trans sample.property.2.symm) ⟨j, hj⟩

omit [Fintype P] [DecidableEq R] in
theorem fillHidden_occurrences (reference sample : RawObservationFibre J name gamma observed) :
    fillHidden (zeroSet J gamma) (fun j => (reference.val.2 j).1)
        (fun j => (sample.val.2 j.val).1) =
      (fun j => (sample.val.2 j).1) := by
  funext j
  by_cases hj : j ∈ zeroSet J gamma
  · simp [fillHidden, hj]
  · simp only [fillHidden, hj, ↓reduceDIte]
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj)

omit [Fintype P] [DecidableEq R] in
theorem fillHidden_names (reference sample : RawObservationFibre J name gamma observed) :
    fillHidden (zeroSet J gamma)
        (fun j => name (reference.val.2 j).1 (reference.val.2 j).2)
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      (fun j => name (sample.val.2 j).1 (sample.val.2 j).2) := by
  funext j
  by_cases hj : j ∈ zeroSet J gamma
  · simp [fillHidden, hj]
  · simp only [fillHidden, hj, ↓reduceDIte]
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj)

theorem localFirstFromH_correct
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (reference sample : RawObservationFibre J name gamma observed) :
    localFirstFromH J name gamma observed reference (fun j => (sample.val.2 j.val).1) =
      actualFirst J gamma sample.val.2 := by
  unfold localFirstFromH actualFirst
  rw [fillHidden_occurrences J name gamma observed reference sample]
  apply ZeroInformation.first_input_reconstruction
  · intro j hj
    exact singleCoefficient_zero J gamma j (of_decide_eq_true hj)
  · exact distinct
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj')
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj')

omit [DecidableEq R] in

theorem localSecondFromH_correct (reference sample : RawObservationFibre J name gamma observed) :
    localSecondFromH J name gamma observed reference
        (fun j => name (sample.val.2 j.val).1 (sample.val.2 j.val).2) =
      actualSecond J name gamma sample.val.2 := by
  unfold localSecondFromH actualSecond
  rw [fillHidden_names J name gamma observed reference sample]
  apply ZeroInformation.second_input_reconstruction
  · intro j hj
    exact decide_eq_true (zeroSet_subset J gamma (of_decide_eq_true hj))
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg (fun p : O × N => p.1)
      (outside_pair_agree J name gamma observed reference sample j hj')
  · intro j hj
    have hj' : j ∉ zeroSet J gamma := of_decide_eq_false hj
    exact congrArg Prod.snd (outside_pair_agree J name gamma observed reference sample j hj')

end

end DFVSGames.Soundness.ConditionalIncidences

namespace DFVSGames.Soundness.BinaryRowTransport
open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open ConditionalIncidences PartnerMapCoordinates

noncomputable section
attribute [local instance] Classical.propDecidable
variable {Q : Type}

theorem rowBits_zero : rowBits (0 : Q → F2) = ZeroInformation.zero := by
  funext q
  change toBit (0 : F2) = false
  decide

theorem rowBits_add (v w : Q → F2) : rowBits (v+w) = ZeroInformation.add (rowBits v) (rowBits w) := by
  funext q
  exact toBit_add _ _

theorem rowBits_smul (b : Bool) (v : Q → F2) :
    rowBits (ofBit b • v) = ZeroInformation.scale (rowBits v) b := by
  cases b <;> funext q <;> simp [rowBits, ZeroInformation.scale, ofBit, toBit]

theorem rowBits_list_sum {P : Type} (xs : List P) (f : P → Q → F2) :
    rowBits (xs.map f |>.sum) = ZeroInformation.rowSum xs (fun j => rowBits (f j)) := by
  induction xs with
  | nil => exact rowBits_zero
  | cons j xs ih =>
    simp only [List.map_cons, List.sum_cons, rowBits_add, ih, ZeroInformation.rowSum, List.foldr_cons]

theorem rowBits_sum {P : Type} [Fintype P] (f : P → Q → F2) :
    rowBits (∑ j, f j) = ZeroInformation.rowSum Finset.univ.toList (fun j => rowBits (f j)) := by
  rw [← Finset.sum_map_toList]
  exact rowBits_list_sum _ _

theorem actual_pullbackRow {k : Nat} [Fintype Q] [DecidableEq Q]
    (rhs : Fin k → Bool) (J : Finset (Fin k))
    (gamma : RawCoefficients J (Q → F2)) (slot : Fin k → PartnerProjection.Slot)
    (x : PartnerProjection.SourcePoint rhs) :
    rowBits (mapEquiv rhs J (Q → F2) gamma
      (PartnerLinear.projection rhs (activeOf J) slot x)) =
    ZeroInformation.pullbackRow Finset.univ.toList (membershipBool J)
      ((rowCoefficients J gamma) none)
      (fullCoefficient J (rowCoefficients J gamma) 0)
      (fullCoefficient J (rowCoefficients J gamma) 1)
      (singleCoefficient J (rowCoefficients J gamma))
      (fun j => ConcreteExtraction.slotIndex (slot j)) x.homogeneous
      (fun j => ConcreteExtraction.tripleCoordinates (x.coordinates j)) := by
  let f : PositionOutside J → Q → F2 := fun j =>
    ofBit (x.coordinates j.val).first • gamma (some (.inl (j,0))) +
      ofBit (x.coordinates j.val).second • gamma (some (.inl (j,1)))
  let g : PositionInside J → Q → F2 := fun j =>
    ofBit (PartnerProjection.retained (slot j.val) (x.coordinates j.val)) • gamma (some (.inr j))
  rw [pullback_expansion]
  change rowBits ((ofBit x.homogeneous • gamma none + ∑ j, f j) + ∑ j, g j) = _
  rw [add_assoc, ActualCanonicalPullback.sum_outside_inside J (Q → F2) f g,
    rowBits_add, rowBits_smul, rowBits_sum]
  unfold ZeroInformation.pullbackRow
  congr 1
  apply ZeroInformation.rowSum_congr
  intro j
  by_cases hj : j ∈ J
  · simp [g, hj, membershipBool, singleCoefficient, rowCoefficients,
      rowBits_smul, ConcreteExtraction.retained_coordinates]
  · simp [f, hj, membershipBool, fullCoefficient, rowCoefficients,
      rowBits_add, rowBits_smul, ConcreteExtraction.tripleCoordinates]

theorem actual_partnerRow {k : Nat} [Fintype Q] [DecidableEq Q]
    (rhs : Fin k → Bool) (J : Finset (Fin k))
    (gamma : RawCoefficients J (Q → F2))
    (y : PartnerProjection.PartnerPoint rhs (activeOf J)) :
    rowBits (mapEquiv rhs J (Q → F2) gamma y) =
    ZeroInformation.partnerRow Finset.univ.toList (membershipBool J)
      ((rowCoefficients J gamma) none)
      (fullCoefficient J (rowCoefficients J gamma) 0)
      (fullCoefficient J (rowCoefficients J gamma) 1)
      (singleCoefficient J (rowCoefficients J gamma)) y.homogeneous
      (fun j => ConcreteExtraction.tripleCoordinates (y.full j)) y.single := by
  let f : PositionOutside J → Q → F2 := fun j =>
    ofBit (y.full j.val).first • gamma (some (.inl (j,0))) +
      ofBit (y.full j.val).second • gamma (some (.inl (j,1)))
  let g : PositionInside J → Q → F2 := fun j =>
    ofBit (y.single j.val) • gamma (some (.inr j))
  rw [mapEquiv_expansion]
  change rowBits ((ofBit y.homogeneous • gamma none + ∑ j, f j) + ∑ j, g j) = _
  rw [add_assoc, ActualCanonicalPullback.sum_outside_inside J (Q → F2) f g,
    rowBits_add, rowBits_smul, rowBits_sum]
  unfold ZeroInformation.partnerRow
  congr 1
  apply ZeroInformation.rowSum_congr
  intro j
  by_cases hj : j ∈ J
  · simp [g, hj, membershipBool, singleCoefficient, rowCoefficients, rowBits_smul]
  · simp [f, hj, membershipBool, fullCoefficient, rowCoefficients,
      rowBits_add, rowBits_smul, ConcreteExtraction.tripleCoordinates]

end
end DFVSGames.Soundness.BinaryRowTransport

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_RawPrivateTable
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Clean.AdviceImageLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Soundness.ConditionalIncidences
open DFVSGames.Soundness.PartnerMapCoordinates
open DFVSGames.Foundations.Games

noncomputable section

attribute [local instance] Classical.propDecidable

variable {K S W : Type} [AddCommGroup K] [Module F2 K]
  [AddCommGroup S] [Module F2 S]

theorem uniform_visible_coefficients {I : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [Fintype K] [Fintype S]
    (A : K →ₗ[F2] S) (F : (I → W × A.range) → ℝ) :
    (𝔼 columns : I → W × K, F (visibleCoefficients A columns)) =
      𝔼 visible : I → W × A.range, F visible := by
  calc
    (𝔼 columns : I → W × K, F (visibleCoefficients A columns)) =
        𝔼 pieces : (I → W × A.range) × (I → A.ker), F pieces.1 :=
      Fintype.expect_equiv (coefficientsSplitEquiv I A) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (I → W × A.range))
          (Finset.univ : Finset (I → A.ker)) (fun pieces => F pieces.1))

theorem visible_card_le [Fintype W] [Fintype K] [Fintype S] (A : K →ₗ[F2] S) :
    Fintype.card (W × A.range) ≤ Fintype.card W * Fintype.card S := by
  rw [Fintype.card_prod]
  exact Nat.mul_le_mul_left _
    (Fintype.card_le_of_injective (fun z : A.range => (z : S)) Subtype.val_injective)

theorem visible_card_binary_le [Fintype K] (w r : Nat)
    (A : K →ₗ[F2] (Fin r → F2)) :
    Fintype.card ((Fin w → F2) × A.range) ≤ 2 ^ (w + r) := by
  calc
    Fintype.card ((Fin w → F2) × A.range) ≤
        Fintype.card (Fin w → F2) * Fintype.card (Fin r → F2) :=
      visible_card_le A
    _ = 2 ^ (w + r) := by simp [F2, pow_add]


end

end DFVSGames.Clean.AdviceImageLaw

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_RepeatedGameBounds
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.firstInputFintype _root_.OAI.DFVSGames.Soundness.ConditionalSimulation.secondInputFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Soundness.ActualPointAnswers
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open PartnerProjection PartnerMapCoordinates RawPartnerTarget
open RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat}

private theorem triple_eq_of_first_second_parity_inline_ActualPointAnswers (a b : PartnerProjection.Triple)
    (h₁ : a.first = b.first) (h₂ : a.second = b.second) (hp : parity a = parity b) : a = b := by
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases b with ⟨b₁, b₂, b₃⟩
  dsimp only at h₁ h₂
  subst b₁
  subst b₂
  simp only [parity] at hp
  have h₃ := congrArg (fun z => (a₁ ^^ a₂) ^^ z) hp
  have cancel (c d : Bool) : (c ^^ (c ^^ d)) = d := by
    cases c <;> cases d <;> rfl
  simp only [cancel] at h₃
  cases h₃
  rfl

theorem secondAnswer_projection (rhs rhs' : Fin k → Bool) (J : Finset (Fin k))
    (slot : Fin k → Slot) (x : ActualHomogeneous.E k)
    (hout : ∀ j, j ∉ J → rhs' j = rhs j) :
    secondAnswer rhs' J (rawProjection rhs J slot x) =
      ActualProjection.project (activeOf J) (fun j => ConcreteExtraction.slotIndex (slot j))
        (firstAnswer rhs x) := by
  let p := (PartnerLinear.sourceLinearEquiv rhs).symm x
  let y := (pointEquiv rhs' J).symm (rawProjection rhs J slot x)
  let z := PartnerLinear.projection rhs (activeOf J) slot p
  have hr : pointEquiv rhs' J y = pointEquiv rhs J z :=
    (pointEquiv rhs' J).apply_symm_apply _
  have hh : y.homogeneous = z.homogeneous := by
    have h := congrArg toBit (congrFun hr none)
    simpa only [pointEquiv_none, toBit_ofBit] using h
  have hfull : y.full = z.full := by
    funext j
    by_cases hj : j ∈ J
    · rw [y.full_zero j (by simp [activeOf, hj]), z.full_zero j (by simp [activeOf, hj])]
    · have h₁ : (y.full j).first = (z.full j).first := by
        have h := congrArg toBit (congrFun hr (some (.inl (⟨j,hj⟩,(0:Fin 2)))))
        simpa only [pointEquiv_full_first, toBit_ofBit] using h
      have h₂ : (y.full j).second = (z.full j).second := by
        have h := congrArg toBit (congrFun hr (some (.inl (⟨j,hj⟩,(1:Fin 2)))))
        simpa only [pointEquiv_full_second, toBit_ofBit] using h
      have hp : parity (y.full j) = parity (z.full j) := by
        rw [y.full_valid j (by simp [activeOf, hj]),
          z.full_valid j (by simp [activeOf, hj]), hout j hj, hh]
      exact triple_eq_of_first_second_parity_inline_ActualPointAnswers _ _ h₁ h₂ hp
  have hsingle : y.single = z.single := by
    funext j
    by_cases hj : j ∈ J
    · have h := congrArg toBit (congrFun hr (some (.inr ⟨j,hj⟩)))
      simpa only [pointEquiv_single, toBit_ofBit] using h
    · rw [y.single_zero j (by simp [activeOf, hj]), z.single_zero j (by simp [activeOf, hj])]
  change (y.homogeneous, (fun j => ConcreteExtraction.tripleCoordinates (y.full j)), y.single) = _
  rw [hh, hfull, hsingle]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext j i
      change ConcreteExtraction.tripleCoordinates
          (if decide (j ∈ J) then zeroTriple else p.coordinates j) i =
        (if decide (j ∈ J) then false else ConcreteExtraction.tripleCoordinates (p.coordinates j) i)
      cases h : decide (j ∈ J) <;> simp [ConcreteExtraction.tripleCoordinates, zeroTriple]
    · funext j
      change (if decide (j ∈ J) then retained (slot j) (p.coordinates j) else false) =
        (if decide (j ∈ J) then ConcreteExtraction.tripleCoordinates (p.coordinates j)
          (ConcreteExtraction.slotIndex (slot j)) else false)
      rw [ConcreteExtraction.retained_coordinates]

theorem displayedRhs_full {Id Name : Type} (rhs : Id → Bool)
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name)
    (occ : Fin k → Id) (slot : Fin k → Slot) (j : Fin k) (hj : j ∉ J) :
    displayedRhs rhs (RawPrivateTable.displayed J names occ slot) j = rhs (occ j) := by
  simp [displayedRhs, RawPrivateTable.displayed, hj]

theorem actual_accepts {Q Id Name : Type} (J : Finset (Fin k))
    (g : IncidenceExtraction.Incidence Id Name)
    (qa : ZeroInformation.FirstInput (Fin k) Q Id)
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name)
    (slot : Fin k → Slot)
    (hquestion : qb.question = RawPrivateTable.displayed J g.name qa.question slot)
    (x : ActualHomogeneous.E k) (v : RawPoint J)
    (hone : sourceTau x = 1)
    (hprojection : rawProjection (fun j => g.rhs (qa.question j)) J slot x = v) :
    ActualProjection.accepts g (activeOf J) qa qb
      (firstAnswer (fun j => g.rhs (qa.question j)) x)
      (secondAnswer (displayedRhs g.rhs qb.question) J v) := by
  let p := (PartnerLinear.sourceLinearEquiv (fun j => g.rhs (qa.question j))).symm x
  have hp : p.homogeneous = true := by
    change toBit x.1 = true
    change x.1 = 1 at hone
    rw [hone]
    decide
  refine ⟨?_, hp, (fun j => ConcreteExtraction.slotIndex (slot j)), ?_, ?_⟩
  · intro j
    exact (ConcreteExtraction.parity_coordinates _).trans (p.valid j)
  · rw [hquestion]
    funext j
    by_cases hj : j ∈ J <;>
      simp [RawPrivateTable.displayed, ZeroInformation.partnerQuestion, activeOf, hj]
  · rw [← hprojection]
    exact secondAnswer_projection _ _ J slot x (fun j hj => by
      rw [hquestion]
      exact displayedRhs_full g.rhs J g.name qa.question slot j hj)

end
end DFVSGames.Soundness.ActualPointAnswers

namespace DFVSGames.Soundness.ActualInputRows
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open ConditionalIncidences PartnerMapCoordinates RawPartnerTarget BinaryRowTransport

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : Nat} {Q Id Name : Type}

theorem firstMap_eq (rhs : Id → Bool) (qa : ZeroInformation.FirstInput (Fin k) Q Id)
    (Z : ActualHomogeneous.E k →ₗ[F2] (Q → F2))
    (hZ : ∀ x, restrictedFirst rhs qa x = Z x) : firstMap rhs qa = Z := by
  have h : ∃ W : ActualHomogeneous.E k →ₗ[F2] (Q → F2),
      ∀ x, W x = restrictedFirst rhs qa x := ⟨Z, fun x => (hZ x).symm⟩
  unfold firstMap
  rw [dite_eq_left h]
  exact LinearMap.ext (fun x => (Classical.choose_spec h x).trans (hZ x))

theorem secondMap_eq (J : Finset (Fin k))
    (qb : ZeroInformation.SecondInput (Fin k) Q Id Name) (Y : RawPoint J →ₗ[F2] (Q → F2))
    (hY : ∀ v, restrictedSecond J qb v = Y v) : secondMap J qb = Y := by
  have h : ∃ W : RawPoint J →ₗ[F2] (Q → F2),
      ∀ v, W v = restrictedSecond J qb v := ⟨Y, fun v => (hY v).symm⟩
  unfold secondMap
  rw [dite_eq_left h]
  exact LinearMap.ext (fun v => (Classical.choose_spec h v).trans (hY v))

theorem firstMap_actual [Fintype Q] [DecidableEq Q]
    (J : Finset (Fin k)) (rhs : Id → Bool) (occ : Fin k → Id)
    (slot : Fin k → PartnerProjection.Slot) (Y : RawPoint J →ₗ[F2] (Q → F2)) :
    firstMap rhs (actualFirst J (rowCoefficients J (gammaOfRawMap J Y))
      (fun j => (occ j, ConcreteExtraction.slotIndex (slot j)))) =
      Y.comp (rawProjection (fun j => rhs (occ j)) J slot) := by
  apply firstMap_eq
  intro x
  let p := (PartnerLinear.sourceLinearEquiv (fun j => rhs (occ j))).symm x
  have h := actual_pullbackRow (fun j => rhs (occ j)) J (gammaOfRawMap J Y) slot p
  rw [← rawMap_on_partner (fun j => rhs (occ j)) J Y] at h
  funext q
  have he := congrArg ofBit (congrFun h q).symm
  simp only [rowBits, ofBit_toBit, restrictedFirst, actualFirst,
    ZeroInformation.firstInput, rawProjection, p, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap] at he ⊢
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 5

theorem secondMap_actual [Fintype Q] [DecidableEq Q]
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (draw : Draw (Fin k) Id)
    (Y : RawPoint J →ₗ[F2] (Q → F2)) :
    secondMap J (actualSecond J names (rowCoefficients J (gammaOfRawMap J Y)) draw) = Y := by
  apply secondMap_eq
  intro v
  let y := (pointEquiv (fun _ : Fin k => false) J).symm v
  have h := actual_partnerRow (fun _ : Fin k => false) J (gammaOfRawMap J Y) y
  rw [← rawMap_on_partner (fun _ : Fin k => false) J Y] at h
  have hy : pointEquiv (fun _ : Fin k => false) J y = v :=
    (pointEquiv (fun _ : Fin k => false) J).apply_symm_apply v
  rw [hy] at h
  funext q
  have he := congrArg ofBit (congrFun h q).symm
  simpa only [rowBits, ofBit_toBit, restrictedSecond, actualSecond,
    ZeroInformation.secondInput, y] using he

end
end DFVSGames.Soundness.ActualInputRows

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ProductLaw
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Clean.ProductLaw

open scoped BigOperators
open Foundations.Games
open Soundness.ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P Q S : Type} [Fintype P] [DecidableEq P] [Fintype Q] [Fintype S]

theorem table_split (μ : P → FiniteDistribution Q) (K : Finset P) :
    (FiniteDistribution.table μ).transport (splitCoordinates K) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).product
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro pieces
  change (∏ i, (μ i).weight ((splitCoordinates K).symm pieces i)) =
    (∏ i : PositionInside K, (μ i.val).weight (pieces.1 i)) *
      ∏ i : PositionOutside K, (μ i.val).weight (pieces.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : P => i ∈ K)
    (fun i => (μ i).weight ((splitCoordinates K).symm pieces i))
  have hi : Subtype.fintype (fun i : P => i ∈ K) =
      Finset.Subtype.fintype K := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : PositionInside K,
        (μ i.val).weight ((splitCoordinates K).symm pieces i.val)) *
        ∏ i : PositionOutside K,
          (μ i.val).weight ((splitCoordinates K).symm pieces i.val) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [splitCoordinates, Equiv.piEquivPiSubtypeProd, i.property]

theorem probability_product_and (μ : FiniteDistribution Q) (ν : FiniteDistribution S)
    (event : Q → Bool) (given : S → Bool) :
    (μ.product ν).probability (fun x => event x.1 && given x.2) =
      μ.probability event * ν.probability given := by
  classical
  simp only [FiniteDistribution.probability, FiniteDistribution.product,
    Fintype.sum_prod_type]
  calc
    _ = ∑ q, ∑ s, (if event q then μ.weight q else 0) *
        (if given s then ν.weight s else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro s _
      cases event q <;> cases given s <;> simp
    _ = _ := by rw [Finset.sum_mul_sum]

theorem table_inside_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (event : (PositionInside K → Q) → Bool)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability
        (fun x => event (fun i => x i.val) && given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event *
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  rw [← probability_product_and, ← table_split]
  exact (FiniteDistribution.probability_transport (FiniteDistribution.table μ)
    (splitCoordinates K) (fun pieces => event pieces.1 && given pieces.2)).symm

theorem table_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability (fun x => given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  simpa using table_inside_outside μ K (fun _ => true) given

theorem conditioned_inside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (positive : 0 < (FiniteDistribution.table μ).probability
      (fun x => given (fun i => x i.val)))
    (event : (PositionInside K → Q) → Bool) :
    ((FiniteDistribution.table μ).condition
      (fun x => given (fun i => x i.val)) positive).probability
        (fun x => event (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event := by
  rw [FiniteDistribution.probability_condition]
  simp_rw [Bool.and_comm (given _)]
  rw [table_inside_outside, table_outside]
  have hne : (FiniteDistribution.table
      (fun i : PositionOutside K => μ i.val)).probability given ≠ 0 := by
    rw [table_outside] at positive
    exact ne_of_gt positive
  exact mul_div_cancel_right₀ _ hne

theorem table_reindex (μ : FiniteDistribution Q) {A : Type} [Fintype A] [DecidableEq A]
    {r : ℕ} (e : Fin r ≃ A) :
    (FiniteDistribution.table (fun _ : A => μ)).transport (coordinateReindex e) =
      μ.iid r := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ a, μ.weight (x (e.symm a))) = ∏ i, μ.weight (x i)
  exact e.symm.prod_comp (fun i => μ.weight (x i))

theorem conditioned_incidence_reindex
    {O N D : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [Zero D] [DecidableEq D]
    (μ : FiniteDistribution (O × Fin 3))
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)))
    {r : ℕ} (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (event : (Fin r → O × N) → Bool) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed))
        positive).probability
          (fun x => event (fun i => incidence name (x (e i).val))) =
      ((μ.pushforward (incidence name)).iid r).probability event := by
  classical
  let given : (PositionOutside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => decide ((fun i => incidence name (x i)) = observed)
  let insideEvent : (PositionInside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => event (fun i => incidence name (x (e i)))
  have h := conditioned_inside (fun _ : P => μ) (zeroSet J gamma)
    given positive insideEvent
  change _ = _ at h
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.probability_pushforward]
  rw [← table_reindex μ e, FiniteDistribution.probability_transport]
  exact h

end
end DFVSGames.Clean.ProductLaw

namespace DFVSGames.Clean.WeightedPartition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {Ω H : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]

theorem sum_fibre_inter (μ : FiniteDistribution Ω) (observe : Ω → H)
    (event : Ω → Bool) :
    (∑ h, μ.probability (fun x => fibre observe h x && event x)) =
      μ.probability event := by
  classical
  unfold FiniteDistribution.probability fibre
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : event x = true <;> simp [hx]

theorem sum_fibre_bound (μ : FiniteDistribution Ω) (observe : Ω → H)
    (bound : H → ℝ) :
    (∑ h, μ.probability (fibre observe h) * bound h) =
      μ.expectation (fun x => bound (observe x)) := by
  classical
  unfold FiniteDistribution.probability FiniteDistribution.expectation fibre
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq, ite_mul, zero_mul]
  simp

theorem probability_le_conditional_bounds (μ : FiniteDistribution Ω)
    (observe : Ω → H) (event : Ω → Bool) (bound : H → ℝ)
    (conditional : ∀ h (positive : 0 < μ.probability (fibre observe h)),
      (μ.condition (fibre observe h) positive).probability event ≤ bound h) :
    μ.probability event ≤ μ.expectation (fun x => bound (observe x)) := by
  rw [← sum_fibre_inter μ observe event, ← sum_fibre_bound μ observe bound]
  apply Finset.sum_le_sum
  intro h _
  by_cases positive : 0 < μ.probability (fibre observe h)
  · rw [μ.probability_inter_eq_mul_conditional (fibre observe h) event positive]
    exact mul_le_mul_of_nonneg_left (conditional h positive) positive.le
  · have zero : μ.probability (fibre observe h) = 0 :=
      le_antisymm (le_of_not_gt positive) (μ.probability_nonnegative _)
    rw [μ.probability_and_eq_zero_of_probability_eq_zero (fibre observe h) event zero,
      zero, zero_mul]

theorem probability_le_of_conditional_le (μ : FiniteDistribution Ω)
    (observe : Ω → H) (event : Ω → Bool) (bound : ℝ)
    (conditional : ∀ h (positive : 0 < μ.probability (fibre observe h)),
      (μ.condition (fibre observe h) positive).probability event ≤ bound) :
    μ.probability event ≤ bound := by
  have estimate := probability_le_conditional_bounds μ observe event
    (fun _ => bound) conditional
  have constant : μ.expectation (fun _ => bound) = bound := by
    rw [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized, one_mul]
  simpa only [constant] using estimate

end
end DFVSGames.Clean.WeightedPartition

namespace DFVSGames.Soundness.ConditionalGameLaw
open scoped BigOperators
open Foundations.Games
open ConditionalIncidences ConditionalSimulation IncidenceExtraction RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem actualWin_iff_reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (sample : RawObservationFibre J g.name gamma observed) :
    actualWin J g gamma strategy sample.val.2 ↔
      reconstructedEvent J g gamma observed reference e strategy
        (fun i => incidence g.name (sample.val.2 (e i).val)) := by
  unfold actualWin reconstructedEvent
  simp only [incidence, Equiv.apply_symm_apply]
  rw [localFirstFromH_correct J g.name gamma observed distinct reference sample,
    localSecondFromH_correct J g.name gamma observed reference sample]

end
end DFVSGames.Soundness.ConditionalGameLaw

namespace DFVSGames.Clean.UpperBound

open scoped BigOperators
open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq R] [Fintype N] in
private theorem reference_of_positive_inline_UpperBound
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (name : O → Fin 3 → N) (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) name draw = observed))) :
    Nonempty (RawObservationFibre J name gamma observed) := by
  classical
  have exists_draw : ∃ draw : Draw P O,
      outsideRecord (zeroSet J gamma) name draw = observed := by
    by_contra h
    have absent : ∀ draw : Draw P O,
        outsideRecord (zeroSet J gamma) name draw ≠ observed := by
      simpa only [not_exists] using h
    simp [FiniteDistribution.probability, absent] at positive
  obtain ⟨draw, equality⟩ := exists_draw
  exact ⟨⟨(gamma, draw), rfl, equality⟩⟩

theorem conditioned_success_le_repeated_value_with_reference
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed)))
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  classical
  let event : (Fin (zeroSet J gamma).card → O × N) → Bool :=
    fun questions => decide (reconstructedEvent J g gamma observed reference e strategy questions)
  have agree : ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) =
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability
      (fun draw => event (fun i => incidence g.name (draw (e i).val))) := by
    unfold FiniteDistribution.probability FiniteDistribution.condition
    apply Finset.sum_congr rfl
    intro draw _
    by_cases hdraw : outsideRecord (zeroSet J gamma) g.name draw = observed
    · let sample : RawObservationFibre J g.name gamma observed :=
        ⟨(gamma, draw), rfl, hdraw⟩
      have equivalent : actualWin J g gamma strategy draw ↔
          reconstructedEvent J g gamma observed reference e strategy
            (fun i => incidence g.name (draw (e i).val)) :=
        actualWin_iff_reconstructedEvent J g gamma observed reference e strategy distinct sample
      simp only [event, decide_eq_true_eq, equivalent]
    · simp [hdraw]
  have distribution_law :=
    ProductLaw.conditioned_incidence_reindex μ J g.name gamma observed positive e event
  apply (le_of_eq (agree.trans distribution_law)).trans
  let G := (incidenceGame g (μ.pushforward (incidence g.name))).repetition (zeroSet J gamma).card
  let simulation := actualLocalSimulation J g gamma observed reference
    (μ.pushforward (incidence g.name)) e
  let induced := Simulation.strategyPair (simulation.induced strategy)
  refine le_trans ?_ (G.success_le_value induced)
  change ((μ.pushforward (incidence g.name)).iid (zeroSet J gamma).card).probability event ≤
    (((μ.pushforward (incidence g.name)).iid (zeroSet J gamma).card).transport
      (Game.tupleQuestionEquiv (zeroSet J gamma).card)).probability (G.wins induced)
  rw [FiniteDistribution.probability_transport]
  apply FiniteDistribution.probability_mono
  intro questions hwin
  have houter : strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
      (simulation.questionA (fun i => (questions i).1))
      (simulation.questionB (fun i => (questions i).2)) :=
    of_decide_eq_true hwin
  exact simulation.induced_wins strategy _ _ houter

theorem conditioned_success_le_repeated_value
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed)))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  classical
  let reference := Classical.choice (reference_of_positive_inline_UpperBound μ J g.name gamma observed positive)
  let e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma) :=
    (Fintype.equivFinOfCardEq (by simp [PositionInside])).symm
  exact conditioned_success_le_repeated_value_with_reference
    μ J g gamma observed positive reference e strategy distinct

theorem fixed_advice_success_le_repeated_value
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    fixedAdviceSuccess μ J g gamma strategy ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  unfold fixedAdviceSuccess
  apply WeightedPartition.probability_le_of_conditional_le
    _ (outsideRecord (zeroSet J gamma) g.name)
  intro observed positive
  exact conditioned_success_le_repeated_value μ J g gamma observed positive strategy distinct

end
end DFVSGames.Clean.UpperBound

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_Mixture
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Clean

open Foundations.Games
open scoped BigOperators

noncomputable section

theorem product_mask {k : ℕ} (mask : Fin k → Bool) (ρ : ℝ) :
    (∏ i, if mask i then ρ else 1) = ρ ^ maskCount mask := by
  classical
  simp [maskCount, Finset.prod_ite]

theorem iid_product_moment {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (f : Ω → ℝ) (k : ℕ) :
    (μ.iid k).expectation (fun x => ∏ i, f (x i)) = μ.expectation f ^ k := by
  classical
  unfold FiniteDistribution.expectation FiniteDistribution.iid
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib]

theorem bernoulli_mask_moment (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (k : ℕ) (ρ : ℝ) :
    ((bernoulli p hp₀ hp₁).iid k).expectation (fun mask => ρ ^ maskCount mask) =
      (1 - p * (1 - ρ)) ^ k := by
  calc
    _ = ((bernoulli p hp₀ hp₁).iid k).expectation
        (fun mask => ∏ i, if mask i then ρ else 1) :=
      FiniteDistribution.expectation_congr _ (fun mask => (product_mask mask ρ).symm)
    _ = ((bernoulli p hp₀ hp₁).expectation (fun b => if b then ρ else 1)) ^ k :=
      iid_product_moment (bernoulli p hp₀ hp₁) (fun b : Bool => if b then ρ else 1) k
    _ = _ := by
      congr 1
      simp [FiniteDistribution.expectation, bernoulli]
      ring

variable {E : Type*} [Fintype E] [Nonempty E]

theorem clean_pushforward (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (origin : E) :
    (singletonSlopeLaw (E := E) β hβ₀ hβ₁).pushforward (cleanBit origin) =
      bernoulli (cleanProbability β E)
        (cleanProbability_nonneg hβ₀) (cleanProbability_le_one hβ₁) := by
  classical
  let μ := (singletonSlopeLaw (E := E) β hβ₀ hβ₁).pushforward (cleanBit origin)
  have ht : μ.weight true = cleanProbability β E := by
    simp [μ, FiniteDistribution.pushforward, singletonSlopeLaw,
      FiniteDistribution.product, Fintype.sum_prod_type,
      bernoulli, cleanBit, FiniteDistribution.uniform, cleanProbability, div_eq_mul_inv]
  apply FiniteDistribution.eq_of_weight_eq
  intro b
  cases b with
  | false =>
      change μ.weight false = 1 - cleanProbability β E
      have hn := μ.normalized
      simp only [Fintype.sum_bool] at hn
      linarith
  | true => exact ht

theorem clean_mask_law (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k : ℕ) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).pushforward
        (fun sample i => cleanBit origin (sample i)) =
      (bernoulli (cleanProbability β E)
        (cleanProbability_nonneg hβ₀) (cleanProbability_le_one hβ₁)).iid k := by
  rw [← FiniteDistribution.iid_pushforward, clean_pushforward]

theorem clean_mask_moment (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k : ℕ) (ρ : ℝ) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).expectation
        (fun sample => ρ ^ maskCount (fun i => cleanBit origin (sample i))) =
      (1 - cleanProbability β E * (1 - ρ)) ^ k := by
  rw [← FiniteDistribution.expectation_pushforward
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k)
    (fun sample i => cleanBit origin (sample i)) (fun mask => ρ ^ maskCount mask)]
  rw [clean_mask_law, bernoulli_mask_moment]

theorem cleanProbability_ge_of_card_le {β : ℝ} (hβ₀ : 0 ≤ β) {N : ℝ}
    (hcard : (Fintype.card E : ℝ) ≤ N) :
    β / N ≤ cleanProbability β E := by
  exact div_le_div_of_nonneg_left hβ₀
    (Nat.cast_pos.mpr Fintype.card_pos) hcard

theorem mask_rate_antitone {p q ρ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hqp : q ≤ p) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (k : ℕ) :
    (1 - p * (1 - ρ)) ^ k ≤ (1 - q * (1 - ρ)) ^ k := by
  have hl : 0 ≤ 1 - p * (1 - ρ) := by
    nlinarith [mul_nonneg hp₀ hρ₀]
  apply pow_le_pow_left₀ hl
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hqp (sub_nonneg.mpr hρ₁)) 1

theorem clean_mask_moment_le (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k : ℕ) {N : ℝ} (hcard : (Fintype.card E : ℝ) ≤ N) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).expectation
        (fun sample => (1 - (1 : ℝ) / 3600) ^
          maskCount (fun i => cleanBit origin (sample i))) ≤
      (1 - (β / N) / 3600) ^ k := by
  rw [clean_mask_moment]
  have h := mask_rate_antitone (cleanProbability_nonneg (E := E) hβ₀)
    (cleanProbability_le_one (E := E) hβ₁)
    (cleanProbability_ge_of_card_le hβ₀ hcard)
    (ρ := 1 - (1 : ℝ) / 3600) (by norm_num) (by norm_num) k
  convert h using 1 ; congr 1 ; ring

theorem clean_mask_moment_le_dimension (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k dimW rs : ℕ) (hcard : Fintype.card E ≤ 2 ^ (dimW + rs)) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).expectation
        (fun sample => (1 - (1 : ℝ) / 3600) ^
          maskCount (fun i => cleanBit origin (sample i))) ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  apply clean_mask_moment_le β hβ₀ hβ₁ origin k
  exact_mod_cast hcard

end
end DFVSGames.Clean

namespace DFVSGames.Clean.Experiment

open scoped BigOperators
open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw

noncomputable section

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq R] in

theorem zeroSet_eq_cleanMask {k : ℕ} (extra : Additional k R) (seed : SparseSeed k R) :
    zeroSet (singletonSet seed) (coefficients extra seed) =
      Finset.univ.filter (fun i => cleanBit (ZeroInformation.zero : Coefficient R) (seed i) = true) := by
  classical
  ext i
  rw [mem_zeroSet]
  simp [singletonSet, coefficients, cleanBit]
  intro _
  rfl

omit [DecidableEq R] in
theorem zeroSet_card {k : ℕ} (extra : Additional k R) (seed : SparseSeed k R) :
    (zeroSet (singletonSet seed) (coefficients extra seed)).card =
      maskCount (fun i => cleanBit (ZeroInformation.zero : Coefficient R) (seed i)) := by
  rw [zeroSet_eq_cleanMask]
  rfl

private theorem expectation_mono_inline_Experiment {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

private theorem expectation_const_inline_Experiment {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (c : ℝ) : μ.expectation (fun _ => c) = c := by
  rw [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized, one_mul]

theorem success_le_of_repetition (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : Additional k R → SparseSeed k R → LocalStrategies k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (ρ : ℝ)
    (rate : ∀ n, ((incidenceGame g (μ.pushforward (incidence g.name))).repetition n).value ≤ ρ ^ n) :
    success k μ g extraLaw β hβ₀ hβ₁ strategy ≤
      (1 - (β / (Fintype.card (Coefficient R) : ℝ)) * (1 - ρ)) ^ k := by
  unfold success
  calc
    _ ≤ extraLaw.expectation (fun _ =>
      (1 - (β / (Fintype.card (Coefficient R) : ℝ)) * (1 - ρ)) ^ k) := by
      apply expectation_mono_inline_Experiment
      intro extra
      calc
        _ ≤ ((singletonSlopeLaw (E := Coefficient R) β hβ₀ hβ₁).iid k).expectation
            (fun seed => ρ ^ maskCount (fun i => cleanBit (ZeroInformation.zero : Coefficient R) (seed i))) := by
          apply expectation_mono_inline_Experiment
          intro seed
          have bound := (UpperBound.fixed_advice_success_le_repeated_value μ
            (singletonSet seed) g (coefficients extra seed) (strategy extra seed) distinct).trans (rate _)
          simpa only [zeroSet_card] using bound
        _ = _ := clean_mask_moment β hβ₀ hβ₁ (ZeroInformation.zero : Coefficient R) k ρ
    _ = _ := expectation_const_inline_Experiment _ _

end
end DFVSGames.Clean.Experiment

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PartnerFullSampling
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.DFVSGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Soundness.PartnerFullSampling

open scoped BigOperators

noncomputable section

theorem expect_restrictIndices {P X : Type*} [Fintype P] [DecidableEq P]
    [Fintype X] [Nonempty X] (J : Finset P) (h : (↥J → X) → ℝ) :
    (𝔼 indices : P → X, h (restrictIndices J indices)) =
      𝔼 activeIndices : ↥J → X, h activeIndices := by
  calc
    (𝔼 indices : P → X, h (restrictIndices J indices)) =
        𝔼 parts : (↥J → X) × ({j : P // j ∉ J} → X), h parts.1 :=
      Fintype.expect_equiv (restrictionProductEquiv J) _ _ (fun _ => rfl)
    _ = 𝔼 activeIndices : ↥J → X, h activeIndices := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (↥J → X))
          (Finset.univ : Finset ({j : P // j ∉ J} → X))
          (fun parts => h parts.1))

end

end DFVSGames.Soundness.PartnerFullSampling


namespace DFVSGames.Clean.CoefficientSampling

open Foundations.Games
open Soundness.ConditionalIncidences
open Soundness.PartnerFullSampling
open scoped BigOperators

noncomputable section

variable {P C : Type} [Fintype P] [DecidableEq P] [Fintype C] [Nonempty C]

theorem expect_outside (J : Finset P) (f : (PositionOutside J → C) → ℝ) :
    (𝔼 full : P → C, f (fun j => full j.val)) =
      𝔼 outside : PositionOutside J → C, f outside := by
  calc
    _ = 𝔼 parts : (PositionInside J → C) × (PositionOutside J → C), f parts.2 :=
      Fintype.expect_equiv (restrictionProductEquiv J) _ _ (fun _ => rfl)
    _ = _ := by
      simpa only [Finset.univ_product_univ, Fintype.expect_const] using
        (Finset.expect_product (Finset.univ : Finset (PositionInside J → C))
          (Finset.univ : Finset (PositionOutside J → C)) (fun parts => f parts.2))

omit [Nonempty C] in
theorem expect_rawCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (𝔼 gamma : RawCoefficients J C, F gamma) =
      𝔼 intercept : C, 𝔼 full : PositionOutside J → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm (intercept, full, single)) := by
  calc
    _ = 𝔼 parts : C × ((PositionOutside J → C × C) × (PositionInside J → C)),
        F ((coefficientProductEquiv J).symm parts) :=
      Fintype.expect_equiv (coefficientProductEquiv J) _ _ (fun _ => by simp)
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
      apply Finset.expect_congr rfl
      intro intercept _
      rw [← Finset.univ_product_univ, Finset.expect_product]

theorem expect_selectCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (𝔼 extra : C × (P → C × C), 𝔼 single : P → C,
      F (selectCoefficients J extra single)) =
      𝔼 gamma : RawCoefficients J C, F gamma := by
  calc
    _ = 𝔼 intercept : C, 𝔼 full : P → C × C, 𝔼 single : P → C,
        F (selectCoefficients J (intercept, full) single) := by
      rw [← Finset.univ_product_univ, Finset.expect_product]
    _ = 𝔼 intercept : C, 𝔼 full : P → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm
            (intercept, (fun i => full i.val), single)) := by
      apply Finset.expect_congr rfl
      intro intercept _
      apply Finset.expect_congr rfl
      intro full _
      exact expect_restrictIndices J (fun single =>
        F ((coefficientProductEquiv J).symm (intercept, (fun i => full i.val), single)))
    _ = 𝔼 intercept : C, 𝔼 full : PositionOutside J → C × C,
        𝔼 single : PositionInside J → C,
          F ((coefficientProductEquiv J).symm (intercept, full, single)) := by
      apply Finset.expect_congr rfl
      intro intercept _
      exact expect_outside J (fun full => 𝔼 single : PositionInside J → C,
        F ((coefficientProductEquiv J).symm (intercept, full, single)))
    _ = _ := (expect_rawCoefficients J F).symm

private theorem uniform_expectation_eq_expect_inline_CoefficientSampling {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) : (FiniteDistribution.uniform X).expectation f = 𝔼 x : X, f x := by
  rw [FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

theorem uniform_selectCoefficients (J : Finset P) (F : RawCoefficients J C → ℝ) :
    (FiniteDistribution.uniform (C × (P → C × C))).expectation (fun extra =>
      (FiniteDistribution.uniform (P → C)).expectation (fun single =>
        F (selectCoefficients J extra single))) =
      (FiniteDistribution.uniform (RawCoefficients J C)).expectation F := by
  simp_rw [uniform_expectation_eq_expect_inline_CoefficientSampling]
  exact expect_selectCoefficients J F

end
end DFVSGames.Clean.CoefficientSampling


namespace DFVSGames.Clean.NativeExperiment

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalGameLaw
open Experiment
open scoped BigOperators

noncomputable section

private theorem expectation_transport_inline_NativeExperiment {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (e : X ≃ Y) (f : Y → ℝ) :
    (μ.transport e).expectation f = μ.expectation (fun x => f (e x)) := by
  unfold FiniteDistribution.expectation FiniteDistribution.transport
  exact Fintype.sum_equiv e.symm _ _ (fun _ => by simp)

theorem iid_product_split {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (k : ℕ) :
    ((μ.product ν).iid k).transport (Game.tupleQuestionEquiv k) =
      (μ.iid k).product (ν.iid k) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro pair
  change (∏ i, μ.weight (pair.1 i) * ν.weight (pair.2 i)) =
    (∏ i, μ.weight (pair.1 i)) * ∏ i, ν.weight (pair.2 i)
  exact Finset.prod_mul_distrib

theorem expectation_iid_product {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (k : ℕ)
    (f : (Fin k → X × Y) → ℝ) :
    ((μ.product ν).iid k).expectation f =
      (μ.iid k).expectation (fun x =>
        (ν.iid k).expectation (fun y => f (fun i => (x i, y i)))) := by
  have law := expectation_transport_inline_NativeExperiment ((μ.product ν).iid k)
    (Game.tupleQuestionEquiv k) (fun pair => f (fun i => (pair.1 i, pair.2 i)))
  rw [iid_product_split, FiniteDistribution.expectation_product] at law
  exact law.symm

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq O] [Fintype N] [DecidableEq N] in

theorem success_eq_flat (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : MaskStrategy k R O N) :
    success k μ g β hβ₀ hβ₁ strategy =
      Experiment.success k μ g (FiniteDistribution.uniform (Additional k R))
        β hβ₀ hβ₁ (liftStrategy strategy) := by
  unfold success Experiment.success singletonSlopeLaw
  symm
  calc
    _ = (FiniteDistribution.uniform (Additional k R)).expectation fun extra =>
        ((bernoulli β hβ₀ hβ₁).iid k).expectation fun mask =>
          (FiniteDistribution.uniform (Fin k → Coefficient R)).expectation fun single =>
            UpperBound.fixedAdviceSuccess μ (maskSet mask) g
              (CoefficientSampling.selectCoefficients (maskSet mask) extra single)
              (strategy mask (CoefficientSampling.selectCoefficients (maskSet mask) extra single)) := by
      apply FiniteDistribution.expectation_congr
      intro extra
      rw [expectation_iid_product, FiniteDistribution.iid_uniform]
      apply FiniteDistribution.expectation_congr
      intro mask
      apply FiniteDistribution.expectation_congr
      intro single
      have hgamma : coefficients extra (fun i => (mask i, single i)) =
          CoefficientSampling.selectCoefficients (maskSet mask) extra single := by
        funext slot
        cases slot with
        | none => rfl
        | some slot =>
          cases slot with
          | inl pair => rfl
          | inr i => rfl
      change UpperBound.fixedAdviceSuccess μ (maskSet mask) g
        (coefficients extra (fun i => (mask i, single i)))
        (strategy mask (coefficients extra (fun i => (mask i, single i)))) = _
      rw [hgamma]
    _ = ((bernoulli β hβ₀ hβ₁).iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Additional k R)).expectation fun extra =>
          (FiniteDistribution.uniform (Fin k → Coefficient R)).expectation fun single =>
            UpperBound.fixedAdviceSuccess μ (maskSet mask) g
              (CoefficientSampling.selectCoefficients (maskSet mask) extra single)
              (strategy mask (CoefficientSampling.selectCoefficients (maskSet mask) extra single))) :=
      FiniteDistribution.expectation_comm _ _ _
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro mask
      exact CoefficientSampling.uniform_selectCoefficients (maskSet mask)
        (fun gamma => UpperBound.fixedAdviceSuccess μ (maskSet mask) g gamma (strategy mask gamma))

end
end DFVSGames.Clean.NativeExperiment


namespace DFVSGames.Clean.ActualAdviceBridge

open scoped BigOperators
open Foundations.Games Integration.BinaryLinear Reduction
open Soundness Soundness.ConditionalIncidences Soundness.ConditionalGameLaw
open Soundness.RawPartnerTarget Soundness.BinaryRowTransport
open AnswerBridge

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D]

theorem sample_question [Fintype Q] [DecidableEq Q]
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (gamma : RawCoefficients J (ZeroInformation.Bits Q)) (draw : Draw (Fin k) O) :
    (actualSecond J g.name gamma draw).question = (displayedQuestion g J draw).val := by
  funext j
  simp [actualSecond, ZeroInformation.secondInput, ZeroInformation.partnerQuestion,
    membershipBool, displayedQuestion, RawPrivateTable.supported,
    RawPrivateTable.displayed]

variable [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
  [Fintype N] [DecidableEq N] [Fintype D]

theorem uniform_maps_to_bits (coordinates : D ≃ₗ[F2] (Q → F2))
    (J : Finset (Fin k)) (F : RawCoefficients J (ZeroInformation.Bits Q) → ℝ) :
    (FiniteDistribution.uniform (RawPoint J →ₗ[F2] D)).expectation
      (fun Y => F (encodedMapCoefficients coordinates J Y)) =
      (FiniteDistribution.uniform (RawCoefficients J (ZeroInformation.Bits Q))).expectation F := by
  simp only [FiniteDistribution.expectation_uniform, ← Fintype.expect_eq_sum_div_card]
  exact Fintype.expect_equiv (mapBitsEquiv coordinates J) _ F (fun _ => rfl)

theorem expectation_mono {X : Type} [Fintype X] (μ : FiniteDistribution X)
    {f g : X → ℝ} (h : ∀ x, f x ≤ g x) : μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

end
end DFVSGames.Clean.ActualAdviceBridge


namespace DFVSGames.Clean.StochasticBound

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds
open scoped BigOperators

noncomputable section

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq R] [DecidableEq O] [DecidableEq N] in

theorem success_eq_fixedAdviceSuccess
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : Strategy (ZeroInformation.FirstInput P R O)
      (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)) :
    (actualGame μ J g gamma).success strategy =
      UpperBound.fixedAdviceSuccess μ J g gamma ⟨strategy.1, strategy.2⟩ := by
  classical
  unfold Game.success actualGame Simulation.weightedGame UpperBound.fixedAdviceSuccess
  rw [FiniteDistribution.probability_pushforward]
  rfl

omit [DecidableEq R] [DecidableEq O] [DecidableEq N] in

theorem exists_deterministic_ge_stochastic
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (responses₁ : ZeroInformation.FirstInput P R O →
      FiniteDistribution (ActualProjection.FirstAnswer P))
    (responses₂ : ZeroInformation.SecondInput P R O N →
      FiniteDistribution (ActualProjection.SecondAnswer P)) :
    ∃ strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N),
      (actualGame μ J g gamma).stochasticSuccess responses₁ responses₂ ≤
        UpperBound.fixedAdviceSuccess μ J g gamma strategy := by
  classical
  obtain ⟨strategy, h⟩ :=
    (actualGame μ J g gamma).exists_deterministic_ge_stochastic responses₁ responses₂
  refine ⟨⟨strategy.1, strategy.2⟩, ?_⟩
  calc
    _ ≤ (actualGame μ J g gamma).success strategy := h
    _ = _ := success_eq_fixedAdviceSuccess μ J g gamma strategy

private theorem expectation_mono_inline_StochasticBound {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

omit [DecidableEq O] [DecidableEq N] in

theorem native_stochastic_le_deterministic
    (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (responses : (mask : Fin k → Bool) →
      RawCoefficients (NativeExperiment.maskSet mask) (ZeroInformation.Bits R) →
      Responses (Fin k) R O N) :
    ∃ strategy : NativeExperiment.MaskStrategy k R O N,
      nativeStochasticSuccess k μ g β hβ₀ hβ₁ responses ≤
        NativeExperiment.success k μ g β hβ₀ hβ₁ strategy := by
  classical
  let strategy : NativeExperiment.MaskStrategy k R O N := fun mask gamma =>
    Classical.choose (exists_deterministic_ge_stochastic μ (NativeExperiment.maskSet mask)
      g gamma (responses mask gamma).1 (responses mask gamma).2)
  refine ⟨strategy, ?_⟩
  unfold nativeStochasticSuccess NativeExperiment.success
  apply expectation_mono_inline_StochasticBound
  intro mask
  apply expectation_mono_inline_StochasticBound
  intro gamma
  exact Classical.choose_spec (exists_deterministic_ge_stochastic μ
    (NativeExperiment.maskSet mask) g gamma (responses mask gamma).1 (responses mask gamma).2)

end
end DFVSGames.Clean.StochasticBound

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualAdviceStochasticBridge
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Clean.ActualAdviceStochasticBridge

open Foundations.Games Integration.BinaryLinear Reduction
open Soundness Soundness.ConditionalIncidences Soundness.RawPartnerTarget
open Soundness.RepeatedGameBounds
open AnswerBridge ActualAdviceBridge

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D]
  [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O]
  [Fintype N] [DecidableEq N] [Fintype D]

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem extendTargetKernel_apply (J : Finset (Fin k)) (names : O → Fin 3 → N)
    (kernel : RawPrivateTable.SupportedV J names → (RawPoint J →ₗ[F2] D) →
      FiniteDistribution (TargetAnswer J))
    (V : RawPrivateTable.SupportedV J names) (Y : RawPoint J →ₗ[F2] D) :
    extendTargetKernel J names kernel V.val Y = kernel V Y := by
  unfold extendTargetKernel
  rw [dite_eq_left V.property]
  congr 1

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem decodeFirstMap_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    coordinates.symm.toLinearMap.comp (ActualInputRows.firstMap g.rhs
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw)) =
      Y.comp (projection g J draw) := by
  have h := ActualInputRows.firstMap_actual J g.rhs (fun j => (draw j).1)
    (fun j => indexSlot (draw j).2) (coordinates.toLinearMap.comp Y)
  have repack : (fun j => ((draw j).1,
      ConcreteExtraction.slotIndex (indexSlot (draw j).2))) = draw := by
    funext j
    simp
  rw [repack] at h
  unfold encodedMapCoefficients projection
  rw [h]
  apply LinearMap.ext
  intro x
  exact coordinates.symm_apply_apply _

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem decodeSecondMap_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (J : Finset (Fin k))
    (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    coordinates.symm.toLinearMap.comp (ActualInputRows.secondMap J
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)) = Y := by
  unfold encodedMapCoefficients
  rw [ActualInputRows.secondMap_actual]
  ext x
  simp

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem firstResponse_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    firstResponse coordinates g policy J
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw) =
      (policy.first J (fun j => (draw j).1) (Y.comp (projection g J draw))).pushforward
        (fun x => ActualPointAnswers.firstAnswer (fun j => g.rhs (draw j).1) x.val) := by
  unfold firstResponse
  rw [decodeFirstMap_actual]
  rfl

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] [Fintype D] in
theorem secondResponse_actual (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) (draw : Draw (Fin k) O) :
    secondResponse coordinates g policy J
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw) =
      (policy.second J (displayedQuestion g J draw) Y).pushforward
        (fun v => ActualPointAnswers.secondAnswer
          (ActualPointAnswers.displayedRhs g.rhs (displayedQuestion g J draw).val) J v.val) := by
  unfold secondResponse
  rw [decodeSecondMap_actual, sample_question, extendTargetKernel_apply]

omit [DecidableEq O] [DecidableEq N] [Fintype D] in
theorem fixedMapSuccess_le (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (J : Finset (Fin k)) (Y : RawPoint J →ₗ[F2] D) :
    fixedMapSuccess μ g policy J Y ≤
      (StochasticBound.actualGame μ J g (encodedMapCoefficients coordinates J Y)).stochasticSuccess
        (firstResponse coordinates g policy J) (secondResponse coordinates g policy J) := by
  unfold fixedMapSuccess Game.stochasticSuccess StochasticBound.actualGame
    Simulation.weightedGame
  rw [FiniteDistribution.expectation_pushforward]
  apply expectation_mono
  intro draw
  rw [firstResponse_actual, secondResponse_actual,
    FiniteDistribution.expectation_pushforward]
  apply expectation_mono
  intro x
  rw [FiniteDistribution.expectation_pushforward]
  apply expectation_mono
  intro v
  by_cases h : projection g J draw x.val = v.val
  · have accepted := ActualPointAnswers.actual_accepts J g
      (actualFirst J (encodedMapCoefficients coordinates J Y) draw)
      (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)
      (fun j => indexSlot (draw j).2)
      (sample_question g J (encodedMapCoefficients coordinates J Y) draw)
      x.val v.val x.property h
    have firstQuestion :
        (actualFirst J (encodedMapCoefficients coordinates J Y) draw).question =
          (fun j => (draw j).1) := rfl
    rw [firstQuestion] at accepted
    have accepted' : (ActualProjection.predicateGame g (membershipBool J)).accepts
        (actualFirst J (encodedMapCoefficients coordinates J Y) draw)
        (actualSecond J g.name (encodedMapCoefficients coordinates J Y) draw)
        (ActualPointAnswers.firstAnswer (fun j => g.rhs (draw j).1) x.val)
        (ActualPointAnswers.secondAnswer
          (ActualPointAnswers.displayedRhs g.rhs (displayedQuestion g J draw).val)
          J v.val) := by
      change ActualProjection.accepts g (PartnerMapCoordinates.activeOf J) _ _ _ _
      rw [← sample_question g J (encodedMapCoefficients coordinates J Y) draw]
      exact accepted
    simp only [h, ite_eq_left, accepted', decide_true, le_refl]
  · simp only [h, ite_false]
    split <;> norm_num

omit [DecidableEq O] [DecidableEq N] in
theorem success_le_native_stochastic (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    success μ g policy β hβ₀ hβ₁ ≤
      StochasticBound.nativeStochasticSuccess k μ g β hβ₀ hβ₁
        (responses coordinates g policy) := by
  unfold success StochasticBound.nativeStochasticSuccess responses
  apply expectation_mono
  intro mask
  calc
    _ ≤ (FiniteDistribution.uniform
        (RawPoint (NativeExperiment.maskSet mask) →ₗ[F2] D)).expectation
        (fun Y => (StochasticBound.actualGame μ (NativeExperiment.maskSet mask) g
          (encodedMapCoefficients coordinates (NativeExperiment.maskSet mask) Y)).stochasticSuccess
          (firstResponse coordinates g policy (NativeExperiment.maskSet mask))
          (secondResponse coordinates g policy (NativeExperiment.maskSet mask))) :=
      expectation_mono _ (fun Y => fixedMapSuccess_le coordinates μ g policy _ Y)
    _ = _ := uniform_maps_to_bits coordinates (NativeExperiment.maskSet mask)
      (fun gamma => (StochasticBound.actualGame μ (NativeExperiment.maskSet mask) g gamma).stochasticSuccess
        (firstResponse coordinates g policy (NativeExperiment.maskSet mask))
        (secondResponse coordinates g policy (NativeExperiment.maskSet mask)))

omit [DecidableEq O] [DecidableEq N] in
theorem success_le_some_native (coordinates : D ≃ₗ[F2] (Q → F2))
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (policy : Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    ∃ strategy : NativeExperiment.MaskStrategy k Q O N,
      success μ g policy β hβ₀ hβ₁ ≤ NativeExperiment.success k μ g β hβ₀ hβ₁ strategy := by
  obtain ⟨strategy, h⟩ := StochasticBound.native_stochastic_le_deterministic
    k μ g β hβ₀ hβ₁ (responses coordinates g policy)
  exact ⟨strategy, (success_le_native_stochastic coordinates μ g policy β hβ₀ hβ₁).trans h⟩

end
end DFVSGames.Clean.ActualAdviceStochasticBridge

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Explicit
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.kernelFintype _root_.OAI.DFVSGames.Clean.AdviceImageLaw.rangeFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Decoder.PaddedLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open ConditionalIncidences PartnerProjection RawPartnerTarget RawMapLaw
open ActualCanonicalPullback
open SparseLaw

noncomputable section
attribute [local instance] Classical.propDecidable

variable {k : ℕ} {V : Type} [AddCommGroup V] [Module F2 V]

theorem uniform_rawMaps [Fintype V] (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] V) → ℝ) :
    (𝔼 gamma : RawCoefficients J V, H (rawMap J V gamma)) = 𝔼 Y, H Y := by
  exact Fintype.expect_equiv (rawMapEquiv J V) _ H (fun _ => rfl)


end
end DFVSGames.Decoder.PaddedLaw

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AdviceLaw
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.ActualGame.dualFintype _root_.OAI.DFVSGames.Reduction.ActualGame.mapFintype _root_.OAI.DFVSGames.Reduction.ActualSource.sourceIndexNonempty _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section

section

namespace DFVSGames.Decoder.AdviceLaw

open scoped BigOperators
open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Soundness
open ConditionalIncidences RawPartnerTarget RawMapLaw
open DFVSGames.Foundations.Games
open DFVSGames.Clean

noncomputable section
attribute [local instance] Classical.propDecidable

section VisibleMap

variable {k : ℕ} {K W R : Type}
  [AddCommGroup K] [Module F2 K] [Fintype K]
  [AddCommGroup W] [Module F2 W] [Fintype W]
  [AddCommGroup R] [Module F2 R] [Fintype R]

omit [Fintype K] [Fintype W] [Fintype R] in
theorem visibleMap_raw (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (TM : (RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K)) :
    visibleMap A TM.1 TM.2 = rawMap J (W × A.range)
      (AdviceImageLaw.visibleCoefficients A (rawMapPairCoefficientsEquiv J TM)) := by
  exact (rawMap_coefficients J (W × A.range) (visibleMap A TM.1 TM.2)).symm

theorem uniform_visible_maps (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] (W × A.range)) → ℝ) :
    (𝔼 TM : (RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K),
      H (visibleMap A TM.1 TM.2)) =
      𝔼 Y : RawPoint J →ₗ[F2] (W × A.range), H Y := by
  calc
    _ = 𝔼 columns : RawSlot J → W × K,
        H (rawMap J (W × A.range) (AdviceImageLaw.visibleCoefficients A columns)) := by
      apply Fintype.expect_equiv (rawMapPairCoefficientsEquiv J)
      intro TM
      rw [visibleMap_raw]
    _ = 𝔼 gamma : RawSlot J → W × A.range, H (rawMap J (W × A.range) gamma) :=
      AdviceImageLaw.uniform_visible_coefficients (I := RawSlot J) (W := W) A
        (fun gamma : RawSlot J → W × A.range => H (rawMap J (W × A.range) gamma))
    _ = _ := PaddedLaw.uniform_rawMaps J H

theorem uniform_visible_maps_expectation (A : K →ₗ[F2] R) (J : Finset (Fin k))
    (H : (RawPoint J →ₗ[F2] (W × A.range)) → ℝ) :
    (FiniteDistribution.uniform
      ((RawPoint J →ₗ[F2] W) × (RawPoint J →ₗ[F2] K))).expectation
        (fun TM => H (visibleMap A TM.1 TM.2)) =
      (FiniteDistribution.uniform (RawPoint J →ₗ[F2] (W × A.range))).expectation H := by
  simpa only [FiniteDistribution.expectation_uniform,
    ← Fintype.expect_eq_sum_div_card] using uniform_visible_maps A J H

variable {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem actualSuccess_eq_cleanSuccess (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N) (A : K →ₗ[F2] R)
    (policy : ActualAdviceStochasticBridge.Policies k g (W × A.range))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    actualSuccess μ g A policy β hβ₀ hβ₁ =
      ActualAdviceStochasticBridge.success μ g policy β hβ₀ hβ₁ := by
  unfold actualSuccess ActualAdviceStochasticBridge.success
  apply FiniteDistribution.expectation_congr
  intro mask
  exact uniform_visible_maps_expectation A (NativeExperiment.maskSet mask)
    (ActualAdviceStochasticBridge.fixedMapSuccess μ g policy (NativeExperiment.maskSet mask))

end VisibleMap

section MaskSlots

theorem maskSlotChoice_pushforward (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((Clean.bernoulli β hβ hβ').product (FiniteDistribution.uniform (Fin 3))).pushforward
      maskSlotChoice = choiceDistribution β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.uniform, Clean.bernoulli, choiceDistribution]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases c <;> simp [maskSlotChoice, PaddedLaw.choiceWeight, div_eq_mul_inv] ; ring

theorem choices_expectation {k : ℕ} (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (H : (Fin k → PaddedLaw.ProjectionChoice) → ℝ) :
    ((choiceDistribution β hβ hβ').iid k).expectation H =
      ((Clean.bernoulli β hβ hβ').iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
          H (choicesOfMaskSlots mask slots))) := by
  rw [← maskSlotChoice_pushforward, FiniteDistribution.iid_pushforward,
    FiniteDistribution.expectation_pushforward, NativeExperiment.expectation_iid_product,
    FiniteDistribution.iid_uniform]
  rfl

theorem choices_mask {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    PaddedLaw.choiceMask (choicesOfMaskSlots mask slots) =
      NativeExperiment.maskSet mask := by
  ext j
  cases h : mask j <;>
    simp [PaddedLaw.choiceMask, NativeExperiment.maskSet, choicesOfMaskSlots,
      maskSlotChoice, h]

theorem choices_active_slot {k : ℕ} (mask : Fin k → Bool) (slots : Fin k → Fin 3)
    (j : Fin k) (hj : mask j = true) :
    PaddedLaw.choiceSlots (choicesOfMaskSlots mask slots) j = PaddedLaw.decodeSlot (slots j) := by
  simp [PaddedLaw.choiceSlots, PaddedLaw.choiceSlot, choicesOfMaskSlots, maskSlotChoice, hj]

theorem projectionSeed_mask_slots_expectation {k : ℕ} {V : Type}
    [AddCommGroup V] [Module F2 V] [Fintype V]
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (H : ProjectionSeed k V → ℝ) :
    (projectionSeedDistribution β hβ hβ').expectation H =
      ((Clean.bernoulli β hβ hβ').iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
          (FiniteDistribution.uniform
            (RawPoint (PaddedLaw.choiceMask (choicesOfMaskSlots mask slots)) →ₗ[F2] V)).expectation
              (fun Y => H ⟨choicesOfMaskSlots mask slots, Y⟩))) := by
  calc
    _ = ((choiceDistribution β hβ hβ').iid k).expectation (fun c =>
        (FiniteDistribution.uniform (RawPoint (PaddedLaw.choiceMask c) →ₗ[F2] V)).expectation
          (fun Y => H ⟨c, Y⟩)) := by
      unfold FiniteDistribution.expectation
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro c _
      change (∑ Y, PaddedLaw.choiceTupleWeight β c * SparseLaw.uniformWeights _ Y * H ⟨c, Y⟩) =
        PaddedLaw.choiceTupleWeight β c * ∑ Y, SparseLaw.uniformWeights _ Y * H ⟨c, Y⟩
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Y _
      exact mul_assoc _ _ _
    _ = _ := choices_expectation β hβ hβ' _

end MaskSlots

end
end DFVSGames.Decoder.AdviceLaw

end

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_RowErasureSliceQuotient
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.ActualAdviceUpper.publicMapFintype _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Clean.IncidenceGap

open DFVSGames.Foundations.Games
open DFVSGames.Soundness.IncidenceExtraction (Incidence Triple xorTriple)
open scoped BigOperators

noncomputable section

variable {O N : Type} [Fintype O] [Fintype N]

attribute [local instance] OAI.DFVSGames.Clean.IncidenceGap.accepts_decidable
theorem game_isProjection (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    DFVSGames.Repetition.IsProjection (game g ω) := by
  intro o n a b b' hb hb'
  obtain ⟨i, hi, _, hai⟩ := (game_accepts_iff g ω o n a b).mp hb
  obtain ⟨j, hj, _, haj⟩ := (game_accepts_iff g ω o n a b').mp hb'
  have hij := distinct o i j (hi.trans hj.symm)
  subst j
  exact hai.symm.trans haj

theorem paritySuccess_le_parityValue (g : Incidence O N) (ω : FiniteDistribution O)
    (b : N → Bool) : paritySuccess g ω b ≤ parityValue g ω := by
  classical
  exact Finset.le_sup' (paritySuccess g ω) (Finset.mem_univ b)

theorem local_count_bound (a b : Triple) (rhs : Bool) :
    (∑ i : Fin 3, if xorTriple a = rhs ∧ a i = b i then (1 : ℝ) else 0) ≤
      2 + if xorTriple b = rhs then (1 : ℝ) else 0 := by
  rw [Fin.sum_univ_three]
  by_cases ha : xorTriple a = rhs
  · by_cases hb : xorTriple b = rhs
    · simp only [ha, hb, true_and, ite_true, if_true]
      split_ifs <;> norm_num
    · by_cases h0 : a 0 = b 0 <;> by_cases h1 : a 1 = b 1 <;>
        by_cases h2 : a 2 = b 2 <;> simp_all [xorTriple] <;> norm_num
  · simp only [ha, false_and, ite_false, zero_add]
    split_ifs <;> norm_num

theorem game_success_eq_slot_average (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (a : O → Triple) (b : N → Bool) :
    (game g ω).success (a, b) =
      ∑ o, ω.weight o * ((∑ i : Fin 3,
        if g.accepts o i (a o) (b (g.name o i)) then (1 : ℝ) else 0) / 3) := by
  classical
  unfold Game.success
  change ((slotLaw ω).pushforward (fun q => (q.1, g.name q.1 q.2))).probability _ = _
  rw [FiniteDistribution.probability_pushforward]
  simp only [FiniteDistribution.probability, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Game.wins, game, decide_eq_true_eq, slotLaw_weight,
    Incidence.namedAccepts_iff_accepts g distinct]
  by_cases h : g.accepts o i (a o) (b (g.name o i)) <;> simp [h, div_eq_mul_inv]

theorem game_success_le_two_add_parity_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (a : O → Triple) (b : N → Bool) :
    (game g ω).success (a, b) ≤ (2 + paritySuccess g ω b) / 3 := by
  classical
  rw [game_success_eq_slot_average g ω distinct]
  calc
    _ ≤ ∑ o, ω.weight o * ((2 + if xorTriple (fun i => b (g.name o i)) =
        g.rhs o then (1 : ℝ) else 0) / 3) := by
      apply Finset.sum_le_sum
      intro o _
      apply mul_le_mul_of_nonneg_left _ (ω.nonnegative o)
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 3)
      exact local_count_bound (a o) (fun i => b (g.name o i)) (g.rhs o)
    _ = (2 + paritySuccess g ω b) / 3 := by
      simp_rw [← mul_div_assoc, mul_add]
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ω.normalized]
      simp only [one_mul, paritySuccess, FiniteDistribution.probability,
        decide_eq_true_eq, mul_ite, mul_one, mul_zero]

theorem game_value_le_one_sub_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    (game g ω).value ≤ 1 - (1 - parityValue g ω) / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro s
  have h := game_success_le_two_add_parity_third g ω distinct s.1 s.2
  have hv := paritySuccess_le_parityValue g ω s.2
  linarith

theorem game_value_le_fourteen_fifteenths
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : parityValue g ω ≤ (4 : ℝ) / 5) :
    (game g ω).value ≤ (14 : ℝ) / 15 := by
  have h := game_value_le_one_sub_third g ω distinct
  linarith

end
end DFVSGames.Clean.IncidenceGap

namespace DFVSGames.Clean.Bound

open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Experiment

noncomputable section

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

omit [DecidableEq O] [DecidableEq N] in

theorem repeated_incidence_value_le
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) (n : ℕ) :
    ((incidenceGame g ((IncidenceGap.slotLaw ω).pushforward (incidence g.name))).repetition n).value ≤
      (1 - (1 : ℝ) / 3600) ^ n := by
  change ((IncidenceGap.game g ω).repetition n).value ≤ _
  exact Repetition.clean_repetition_value (IncidenceGap.game g ω)
    (IncidenceGap.game_isProjection g ω distinct) n
    (IncidenceGap.game_value_le_fourteen_fifteenths g ω distinct hopt)

theorem clean_success_le_dimension (k : ℕ) (g : IncidenceExtraction.Incidence O N)
    (ω : FiniteDistribution O) (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : Additional k R → SparseSeed k R → LocalStrategies k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card (Coefficient R) ≤ 2 ^ (dimW + rs)) :
    success k (IncidenceGap.slotLaw ω) g extraLaw β hβ₀ hβ₁ strategy ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  have comparison := clean_mask_moment_le_dimension β hβ₀ hβ₁
    (ZeroInformation.zero : Coefficient R) k dimW rs hcard
  rw [clean_mask_moment] at comparison
  have estimate := success_le_of_repetition k (IncidenceGap.slotLaw ω) g extraLaw
    β hβ₀ hβ₁ strategy distinct (1 - (1 : ℝ) / 3600)
    (repeated_incidence_value_le g ω distinct hopt)
  exact estimate.trans comparison

theorem native_clean_success_le_dimension (k : ℕ)
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : NativeExperiment.MaskStrategy k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card (Coefficient R) ≤ 2 ^ (dimW + rs)) :
    NativeExperiment.success k (IncidenceGap.slotLaw ω) g β hβ₀ hβ₁ strategy ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  rw [NativeExperiment.success_eq_flat]
  exact clean_success_le_dimension k g ω (FiniteDistribution.uniform (Additional k R))
    β hβ₀ hβ₁ (NativeExperiment.liftStrategy strategy) distinct hopt dimW rs hcard

end
end DFVSGames.Clean.Bound

namespace DFVSGames.Clean.ActualAdviceBound

open Foundations.Games Integration.BinaryLinear
open Soundness
open AnswerBridge

noncomputable section

variable {k : ℕ} {D Q O N : Type} [AddCommGroup D] [Module F2 D] [Fintype D]
  [Fintype Q] [DecidableEq Q] [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

theorem stochastic_success_le_dimension (coordinates : D ≃ₗ[F2] (Q → F2))
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : ActualAdviceStochasticBridge.Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card D ≤ 2 ^ (dimW + rs)) :
    ActualAdviceStochasticBridge.success (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  have hcard' : Fintype.card (Experiment.Coefficient Q) ≤ 2 ^ (dimW + rs) :=
    (Fintype.card_congr (bitsCoordinatesEquiv coordinates).symm).le.trans hcard
  obtain ⟨strategy, h⟩ := ActualAdviceStochasticBridge.success_le_some_native coordinates
    (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁
  exact h.trans (Bound.native_clean_success_le_dimension k g ω β hβ₀ hβ₁
    strategy distinct hopt dimW rs hcard')

theorem stochastic_success_le_dimension_finite [FiniteDimensional F2 D]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : ActualAdviceStochasticBridge.Policies k g D)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5)
    (dimW rs : ℕ) (hcard : Fintype.card D ≤ 2 ^ (dimW + rs)) :
    ActualAdviceStochasticBridge.success (IncidenceGap.slotLaw ω) g policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k :=
  stochastic_success_le_dimension finiteCoordinates g ω policy β hβ₀ hβ₁
    distinct hopt dimW rs hcard

end
end DFVSGames.Clean.ActualAdviceBound

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualAdviceUpper
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Decoder.SelectedDecoding.affineSliceFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.DFVSGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.DFVSGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.DFVSGames.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Gadget.StageQuotient.spaceFinite _root_.OAI.DFVSGames.Integration.AddressTupleBody.labelFintype _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DFVSGames.Quadratic.finiteBlockOrientation _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.DFVSGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFiniteRank _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Decoder.ActualAdviceUpper

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction
open DFVSGames.Soundness
open DFVSGames.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

theorem fullInput_actual (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    fullInput S A occ ((AdviceLaw.visibleMap A T M).comp
      (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) =
      AdviceExperiment.leftObservation (ActualGame.rhs S) (actualDraw S A J occ slot T M) :=
  rfl

theorem projectedInput_actual (S : Source) (A : Alphabet s →ₗ[F2] Vector rs)
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    projectedInput S A J (RawPrivateTable.supported J (ActualGame.names S) occ slot)
        (AdviceLaw.visibleMap A T M) =
      (AdviceExperiment.rightObservation (ActualGame.names S)
        (actualDraw S A J occ slot T M)).2 :=
  rfl

theorem policyAgreement_actual (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs) (J : Finset (Fin k))
    (occ : Fin k → Fin S.occurrences) (slot : Fin k → PartnerProjection.Slot)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    (((policies S labeling good A).first J occ
        ((AdviceLaw.visibleMap A T M).comp
          (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))).product
      ((policies S labeling good A).second J
        (RawPrivateTable.supported J (ActualGame.names S) occ slot)
        (AdviceLaw.visibleMap A T M))).probability
        (fun answers => decide
          (RawPrivateTable.projection J (ActualGame.rhs S) occ slot answers.1.val =
            answers.2.val)) =
      VisiblePolicies.observedAgreement S labeling good (actualDraw S A J occ slot T M) := by
  dsimp only [policies, sourceIncidence]
  rw [fullInput_actual S A J occ slot T M, projectedInput_actual S A J occ slot T M]
  rfl

theorem source_projection_eq (S : Source) (J : Finset (Fin k))
    (draw : Fin k → Fin S.occurrences × Fin 3) :
    Clean.ActualAdviceBridge.projection (sourceIncidence S) J draw =
      RawPrivateTable.projection J (ActualGame.rhs S) (fun j => (draw j).1)
        (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) := by
  simp only [Clean.ActualAdviceBridge.projection, sourceIncidence,
    RawPrivateTable.projection, ActualGame.rhs, toBit_ofBit]

theorem fixed_public_map_bound
    {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (A : Alphabet s →ₗ[F2] Vector rs)
    (policy : Clean.ActualAdviceStochasticBridge.Policies k g (Visible d A))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    AdviceLaw.actualSuccess (Clean.IncidenceGap.slotLaw ω) g A policy β hβ₀ hβ₁ ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  rw [AdviceLaw.actualSuccess_eq_cleanSuccess]
  exact Clean.ActualAdviceBound.stochastic_success_le_dimension_finite g ω policy
    β hβ₀ hβ₁ distinct hopt d rs (Clean.AdviceImageLaw.visible_card_binary_le d rs A)

theorem public_map_average_bound
    {O N : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (g : IncidenceExtraction.Incidence O N) (ω : FiniteDistribution O)
    (policy : (A : Alphabet s →ₗ[F2] Vector rs) →
      Clean.ActualAdviceStochasticBridge.Policies k g (Visible d A))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue g ω ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => AdviceLaw.actualSuccess (Clean.IncidenceGap.slotLaw ω) g A
          (policy A) β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  calc
    _ ≤ (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun _ => (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k) :=
      Clean.ActualAdviceBridge.expectation_mono _
        (fun A => fixed_public_map_bound g ω A (policy A) β hβ₀ hβ₁ distinct hopt)
    _ = _ := by
      rw [FiniteDistribution.expectation, ← Finset.sum_mul,
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).normalized, one_mul]

theorem actual_source_average_bound (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, (sourceIncidence S).name o i =
      (sourceIncidence S).name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue (sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => AdviceLaw.actualSuccess
          (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
          (sourceIncidence S) A (policies S labeling good A) β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k :=
  public_map_average_bound (sourceIncidence S) (FiniteDistribution.uniform (Fin S.occurrences))
    (policies S labeling good) β hβ₀ hβ₁ distinct hopt

end

end DFVSGames.Decoder.ActualAdviceUpper
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Clone100Counting
attribute [-instance] _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Outer.SourceIncidence

open DFVSGames.Reduction ActualSource
open DFVSGames.Foundations Games Target PCP
open DFVSGames.Soundness.IncidenceExtraction
open DFVSGames.Clean.IncidenceGap
open scoped BigOperators

noncomputable section

theorem names_distinct (S : Source) (hS : S.DistinctNames) :
    ∀ o i j, (incidence S).name o i = (incidence S).name o j → i = j := by
  intro o i j hij
  obtain ⟨h12, h13, h23⟩ := hS o
  fin_cases i <;> fin_cases j <;>
    simp_all [incidence, ActualGame.names, eq_comm]

end
end DFVSGames.Outer.SourceIncidence

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ActualAdviceSampling
attribute [-instance] _root_.OAI.DFVSGames.Appendix.A5Passage.pairFintype _root_.OAI.DFVSGames.Appendix.Derivatives.hybridIndexFintype _root_.OAI.DFVSGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.DFVSGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.DFVSGames.Quadratic.binaryFieldFintype _root_.OAI.DFVSGames.Quadratic.blockOrientationFintype _root_.OAI.DFVSGames.Quadratic.fieldLineFintype _root_.OAI.DirectedFeedback.Construction.allVertexFintype _root_.OAI.DirectedFeedback.Construction.bigSupportFintype _root_.OAI.DirectedFeedback.Construction.comparisonSupportFintype _root_.OAI.DirectedFeedback.Construction.fullSupportFintype _root_.OAI.DirectedFeedback.Construction.outputFintype _root_.OAI.DirectedFeedback.Construction.rankFintype _root_.OAI.DirectedFeedback.Construction.rawBigFintype _root_.OAI.DirectedFeedback.Construction.rawCompareFintype _root_.OAI.DirectedFeedback.Construction.rawFullFintype _root_.OAI.DirectedFeedback.Construction.rawSmallFintype _root_.OAI.DirectedFeedback.Construction.smallSupportFintype _root_.OAI.DirectedFeedback.CookLevin.NPTableau.codec_width_nonempty _root_.OAI.DirectedFeedback.LivePackets.liveFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedBigFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCommonFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedCompareFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedFullFintype _root_.OAI.DirectedFeedback.PacketSeeds.seedSmallFintype _root_.OAI.DirectedFeedback.Pivotal.labelOrderNonempty _root_.OAI.DirectedFeedback.Pivotal.nonemptyOrder _root_.OAI.DirectedFeedback.RankGraph.instFintypeDomain _root_.OAI.DirectedFeedback.RankGraph.instNonemptyDomain _root_.OAI.DirectedFeedback.RankPackets.shapeFintype _root_.OAI.DirectedFeedback.RawFamily.eNonempty _root_.OAI.DirectedFeedback.RawFamily.tagNonempty _root_.OAI.DirectedFeedback.RawFamily.wNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualAdviceSampling

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Soundness
open DFVSGames.Foundations.Games
open ActualSource ActualAdviceUpper

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

theorem fixedMapSuccess_eq_product {O N D : Type}
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [AddCommGroup D] [Module F2 D] [Fintype D]
    (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (policy : Clean.ActualAdviceStochasticBridge.Policies k g D)
    (J : Finset (Fin k)) (Y : RawPartnerTarget.RawPoint J →ₗ[F2] D) :
    Clean.ActualAdviceStochasticBridge.fixedMapSuccess μ g policy J Y =
      (FiniteDistribution.table (fun _ : Fin k => μ)).expectation (fun draw =>
        ((policy.first J (fun j => (draw j).1)
          (Y.comp (Clean.ActualAdviceBridge.projection g J draw))).product
          (policy.second J (Clean.ActualAdviceBridge.displayedQuestion g J draw) Y)).probability
          (fun answers => decide
            (Clean.ActualAdviceBridge.projection g J draw answers.1.val = answers.2.val))) := by
  unfold Clean.ActualAdviceStochasticBridge.fixedMapSuccess
  apply FiniteDistribution.expectation_congr
  intro draw
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum,
    mul_ite, decide_eq_true_eq, mul_one, mul_zero]

theorem fixedMapSuccess_eq_observed (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs) (J : Finset (Fin k))
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s) :
    Clean.ActualAdviceStochasticBridge.fixedMapSuccess μ (sourceIncidence S)
      (policies S labeling good A) J (AdviceLaw.visibleMap A T M) =
      (FiniteDistribution.table (fun _ : Fin k => μ)).expectation (fun draw =>
        VisiblePolicies.observedAgreement S labeling good
          (actualDraw S A J (fun j => (draw j).1)
            (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) T M)) := by
  rw [fixedMapSuccess_eq_product]
  apply FiniteDistribution.expectation_congr
  intro draw
  rw [source_projection_eq]
  exact policyAgreement_actual S labeling good A J (fun j => (draw j).1)
    (fun j => Clean.ActualAdviceBridge.indexSlot (draw j).2) T M

theorem actualSuccess_eq_sampledAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (μ : FiniteDistribution (Fin S.occurrences × Fin 3))
    (A : Alphabet s →ₗ[F2] Vector rs)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    AdviceLaw.actualSuccess μ (sourceIncidence S) A (policies S labeling good A)
        β hβ₀ hβ₁ = sampledAgreement S labeling good μ A β hβ₀ hβ₁ := by
  unfold AdviceLaw.actualSuccess sampledAgreement
  apply FiniteDistribution.expectation_congr
  intro mask
  apply FiniteDistribution.expectation_congr
  intro TM
  exact fixedMapSuccess_eq_observed S labeling good μ A _ TM.1 TM.2

theorem sampledAgreement_average_bound (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, (sourceIncidence S).name o i =
      (sourceIncidence S).name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue (sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) :
    (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
      (fun A => sampledAgreement S labeling good
        (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
        A β hβ₀ hβ₁) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  simp_rw [← actualSuccess_eq_sampledAgreement]
  exact actual_source_average_bound S labeling good β hβ₀ hβ₁ distinct hopt

end

end DFVSGames.Decoder.ActualAdviceSampling

namespace DFVSGames.Decoder.ActualSeedPointwise

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Soundness
open DFVSGames.Foundations.Games
open ActualSource
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

theorem rawProjection_congr_slots {k : Nat} (rhsB : Fin k → Bool)
    (J : Finset (Fin k)) (slot slot' : Fin k → PartnerProjection.Slot)
    (h : ∀ j, j ∈ J → slot j = slot' j) :
    RawPartnerTarget.rawProjection rhsB J slot =
      RawPartnerTarget.rawProjection rhsB J slot' := by
  have hp : PartnerLinear.projection rhsB (PartnerMapCoordinates.activeOf J) slot =
      PartnerLinear.projection rhsB (PartnerMapCoordinates.activeOf J) slot' := by
    apply LinearMap.ext
    intro x
    change PartnerProjection.project rhsB (PartnerMapCoordinates.activeOf J) slot x =
      PartnerProjection.project rhsB (PartnerMapCoordinates.activeOf J) slot' x
    apply PartnerProjection.partner_ext
    · rfl
    · rfl
    · funext j
      by_cases hj : j ∈ J
      · simp [PartnerProjection.project, PartnerMapCoordinates.activeOf, hj, h j hj]
      · simp [PartnerProjection.project, PartnerMapCoordinates.activeOf, hj]
  simp only [RawPartnerTarget.rawProjection, hp]

theorem supported_congr_slots {k : Nat} {Id Name : Type}
    (J : Finset (Fin k)) (names : Id → Fin 3 → Name) (occ : Fin k → Id)
    (slot slot' : Fin k → PartnerProjection.Slot)
    (h : ∀ j, j ∈ J → slot j = slot' j) :
    RawPrivateTable.supported J names occ slot =
      RawPrivateTable.supported J names occ slot' := by
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ J
  · simp [RawPrivateTable.supported, RawPrivateTable.displayed, hj, h j hj]
  · simp [RawPrivateTable.supported, RawPrivateTable.displayed, hj]

variable {k s d rs : Nat}

theorem observedAgreement_changePositions (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (draw : AdviceExperiment.Draw k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector rs))
    (slot : Fin k → PartnerProjection.Slot)
    (hslot : ∀ j, j ∈ draw.singletons → draw.positions j = slot j) :
    VisiblePolicies.observedAgreement S labeling good draw =
      VisiblePolicies.observedAgreement S labeling good { draw with positions := slot } := by
  cases draw with
  | mk J occ positions A M T =>
    have hp := rawProjection_congr_slots (fun j => toBit (ActualGame.rhs S (occ j)))
      J positions slot hslot
    have hs := supported_congr_slots J (ActualGame.names S) occ positions slot hslot
    simp only [VisiblePolicies.observedAgreement, AdviceExperiment.leftObservation,
      AdviceExperiment.rightObservation, AdviceExperiment.projection,
      RawPrivateTable.projection, hp, hs]
    rfl

theorem seedAgreement_pointwise (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (occ : Fin k → Fin S.occurrences) (A : Alphabet s →ₗ[F2] Vector rs)
    (choices : Fin k → PaddedLaw.ProjectionChoice)
    (slot : Fin k → PartnerProjection.Slot)
    (hslot : ∀ j, j ∈ PaddedLaw.choiceMask choices →
      PaddedLaw.choiceSlots choices j = slot j)
    (Y : RawPartnerTarget.RawPoint (PaddedLaw.choiceMask choices) →ₗ[F2]
      (Alphabet s × Vector d)) :
    VisiblePolicies.observedAgreement S labeling good
        (AdviceLaw.seedToActualDraw occ A ⟨choices, Y⟩) =
      VisiblePolicies.observedAgreement S labeling good
        (ActualAdviceUpper.actualDraw S A (PaddedLaw.choiceMask choices) occ slot
          ((LinearMap.snd F2 (Alphabet s) (Vector d)).comp Y)
          ((LinearMap.fst F2 (Alphabet s) (Vector d)).comp Y)) :=
  observedAgreement_changePositions S labeling good
    (AdviceLaw.seedToActualDraw occ A ⟨choices, Y⟩) slot hslot

private theorem seedAgreement_repack_at_inline_ActualSeedPointwise (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (occ : Fin k → Fin S.occurrences) (A : Alphabet s →ₗ[F2] Vector rs)
    (choices : Fin k → PaddedLaw.ProjectionChoice) (J : Finset (Fin k))
    (hJ : PaddedLaw.choiceMask choices = J)
    (slot : Fin k → PartnerProjection.Slot)
    (hslot : ∀ j, j ∈ PaddedLaw.choiceMask choices →
      PaddedLaw.choiceSlots choices j = slot j) :
    (FiniteDistribution.uniform
      (RawPartnerTarget.RawPoint (PaddedLaw.choiceMask choices) →ₗ[F2]
        (Alphabet s × Vector d))).expectation (fun Y =>
          VisiblePolicies.observedAgreement S labeling good
            (AdviceLaw.seedToActualDraw occ A ⟨choices, Y⟩)) =
      (FiniteDistribution.uniform
        ((RawPartnerTarget.RawPoint J →ₗ[F2] Vector d) ×
          (RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s))).expectation (fun TM =>
            VisiblePolicies.observedAgreement S labeling good
              (ActualAdviceUpper.actualDraw S A J occ slot TM.1 TM.2)) := by
  subst J
  simp only [FiniteDistribution.expectation_uniform, ← Fintype.expect_eq_sum_div_card]
  apply Fintype.expect_equiv
    ((LinearMap.prodEquiv F2).toEquiv.symm.trans (Equiv.prodComm _ _))
  intro Y
  exact seedAgreement_pointwise S labeling good occ A choices slot hslot Y

theorem seedAgreement_repack (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (occ : Fin k → Fin S.occurrences) (A : Alphabet s →ₗ[F2] Vector rs)
    (mask : Fin k → Bool) (slots : Fin k → Fin 3) :
    (FiniteDistribution.uniform
      (RawPartnerTarget.RawPoint
        (PaddedLaw.choiceMask (AdviceLaw.choicesOfMaskSlots mask slots)) →ₗ[F2]
          (Alphabet s × Vector d))).expectation (fun Y =>
            VisiblePolicies.observedAgreement S labeling good
              (AdviceLaw.seedToActualDraw occ A
                ⟨AdviceLaw.choicesOfMaskSlots mask slots, Y⟩)) =
      (FiniteDistribution.uniform
        ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
          (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2]
            Alphabet s))).expectation (fun TM =>
              VisiblePolicies.observedAgreement S labeling good
                (ActualAdviceUpper.actualDraw S A (Clean.NativeExperiment.maskSet mask)
                  occ (fun j => Clean.ActualAdviceBridge.indexSlot (slots j)) TM.1 TM.2)) := by
  apply seedAgreement_repack_at_inline_ActualSeedPointwise S labeling good occ A
    (AdviceLaw.choicesOfMaskSlots mask slots) (Clean.NativeExperiment.maskSet mask)
    (AdviceLaw.choices_mask mask slots)
  intro j hj
  have hmask : mask j = true := by
    rw [AdviceLaw.choices_mask] at hj
    simpa only [Clean.NativeExperiment.maskSet, Finset.mem_filter, Finset.mem_univ,
      true_and] using hj
  exact AdviceLaw.choices_active_slot mask slots j hmask

end
end DFVSGames.Decoder.ActualSeedPointwise

namespace DFVSGames.Decoder.ActualSeedSampling

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Reduction DFVSGames.Soundness
open DFVSGames.Foundations.Games
open ActualSource ActualAdviceUpper ActualAdviceSampling

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d rs : Nat}

theorem uniform_occurrence_slots {O : Type} [Fintype O] [Nonempty O]
    (H : (Fin k → O × Fin 3) → ℝ) :
    (FiniteDistribution.table (fun _ : Fin k =>
      Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform O))).expectation H =
      (FiniteDistribution.uniform (Fin k → O)).expectation (fun occ =>
        (FiniteDistribution.uniform (Fin k → Fin 3)).expectation
          (fun slots => H (fun j => (occ j, slots j)))) := by
  change (((FiniteDistribution.uniform O).product
    (FiniteDistribution.uniform (Fin 3))).iid k).expectation H = _
  rw [Clean.NativeExperiment.expectation_iid_product,
    FiniteDistribution.iid_uniform, FiniteDistribution.iid_uniform]

theorem sampledAgreement_eq_separated (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (A : Alphabet s →ₗ[F2] Vector rs)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    sampledAgreement S labeling good
      (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
      A β hβ₀ hβ₁ =
      ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation (fun mask =>
        (FiniteDistribution.uniform (Fin k → Fin S.occurrences)).expectation (fun occ =>
          (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
            (FiniteDistribution.uniform
              ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
                (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
              (drawAgreement S labeling good A mask occ slots)))) := by
  unfold sampledAgreement
  apply FiniteDistribution.expectation_congr
  intro mask
  calc
    _ = (FiniteDistribution.uniform
        ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
          (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
        (fun TM => (FiniteDistribution.uniform (Fin k → Fin S.occurrences)).expectation
          (fun occ => (FiniteDistribution.uniform (Fin k → Fin 3)).expectation
            (fun slots => drawAgreement S labeling good A mask occ slots TM))) := by
      apply FiniteDistribution.expectation_congr
      intro TM
      exact uniform_occurrence_slots _
    _ = _ := by
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro occ
      exact FiniteDistribution.expectation_comm _ _ _

theorem fullSeedLaw_eq_sampledAgreement (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    (AdviceLaw.fullSeedLaw (V := Alphabet s × Vector d)
      (FiniteDistribution.uniform (Fin k → Fin S.occurrences))
      (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)) β hβ₀ hβ₁).expectation
      (fun seed => VisiblePolicies.observedAgreement S labeling good
        (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) =
      (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)).expectation
        (fun A => sampledAgreement S labeling good
          (Clean.IncidenceGap.slotLaw (FiniteDistribution.uniform (Fin S.occurrences)))
          A β hβ₀ hβ₁) := by
  unfold AdviceLaw.fullSeedLaw
  rw [FiniteDistribution.expectation_product, FiniteDistribution.expectation_product,
    FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro A
  rw [sampledAgreement_eq_separated]
  calc
    _ = (FiniteDistribution.uniform (Fin k → Fin S.occurrences)).expectation (fun occ =>
        ((Clean.bernoulli β hβ₀ hβ₁).iid k).expectation (fun mask =>
          (FiniteDistribution.uniform (Fin k → Fin 3)).expectation (fun slots =>
            (FiniteDistribution.uniform
              ((RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Vector d) ×
                (RawPartnerTarget.RawPoint (Clean.NativeExperiment.maskSet mask) →ₗ[F2] Alphabet s))).expectation
              (drawAgreement S labeling good A mask occ slots)))) := by
      apply FiniteDistribution.expectation_congr
      intro occ
      rw [AdviceLaw.projectionSeed_mask_slots_expectation]
      apply FiniteDistribution.expectation_congr
      intro mask
      apply FiniteDistribution.expectation_congr
      intro slots
      exact ActualSeedPointwise.seedAgreement_repack S labeling good occ A mask slots
    _ = _ := FiniteDistribution.expectation_comm _ _ _

theorem fullSeedLaw_upper (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (good : VisiblePolicies.LeftInput S k s d (Vector rs) →
      VisiblePolicies.ResponseWitness k → Prop)
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (distinct : ∀ o i j, (sourceIncidence S).name o i =
      (sourceIncidence S).name o j → i = j)
    (hopt : Clean.IncidenceGap.parityValue (sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) :
    (AdviceLaw.fullSeedLaw (V := Alphabet s × Vector d)
      (FiniteDistribution.uniform (Fin k → Fin S.occurrences))
      (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector rs)) β hβ₀ hβ₁).expectation
      (fun seed => VisiblePolicies.observedAgreement S labeling good
        (AdviceLaw.seedToActualDraw seed.1.1 seed.1.2 seed.2)) ≤
      (1 - (β / (2 : ℝ) ^ (d + rs)) / 3600) ^ k := by
  rw [fullSeedLaw_eq_sampledAgreement]
  exact sampledAgreement_average_bound S labeling good β hβ₀ hβ₁ distinct hopt

end

end DFVSGames.Decoder.ActualSeedSampling

namespace DFVSGames.Decoder.ActualMatrixContradiction

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

theorem law_expectation_eq (S : Source) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (f : ActualSeedEvents.Seed S k s d r → ℝ) :
    expectationOf_inline_ActualMatrixContradiction (ActualSeedEvents.law S k s d r β hβ hβ') f =
      expectationOf_inline_ActualMatrixContradiction (AdviceLaw.fullSeedLaw (V := Alphabet s × Vector d)
        (FiniteDistribution.uniform (Fin k → Fin S.occurrences))
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)) β hβ hβ') f := by
  simp only [expectationOf_inline_ActualMatrixContradiction, FiniteDistribution.expectation, ActualSeedEvents.law,
    AdviceLaw.fullSeedLaw, FiniteDistribution.product, FiniteDistribution.uniform]

theorem contradiction_oai (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : ActualProjectedTransfer.slopeVariation k s d β ≤
      ConstantSelection.variationBudget α g₀ s r)
    (hrate : (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k <
      ConstantSelection.decodingMass α g₀ s r)
    (hdistinct : S.DistinctNames)
    (hopt : Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) : False := by
  have hlower := ActualProjectedTransfer.actual_success_lower S labeling α g₀ β
    hα hsmall hβ hβ' hgood hvariation
  have hnames : ∀ o i j, (ActualAdviceUpper.sourceIncidence S).name o i =
      (ActualAdviceUpper.sourceIncidence S).name o j → i = j :=
    Outer.SourceIncidence.names_distinct S hdistinct
  have hupper := ActualSeedSampling.fullSeedLaw_upper S labeling
    (SelectedPolicies.goodPredicate S labeling α hα hsmall) β hβ hβ' hnames hopt
  have hbound : ConstantSelection.decodingMass α g₀ s r ≤
      (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k := by
    apply hlower.trans
    change expectationOf_inline_ActualMatrixContradiction (ActualSeedEvents.law S k s d r β hβ hβ') _ ≤ _
    rw [law_expectation_eq]
    exact hupper
  exact (not_lt_of_ge hbound) hrate

end
end DFVSGames.Decoder.ActualMatrixContradiction

namespace DFVSGames.Gadget

universe u v

attribute [instance] Stage.inputAdd Stage.inputModule Stage.shiftAdd Stage.shiftModule
  Stage.inputFinite Stage.shiftFinite Stage.noiseFinite Stage.noiseNonempty

end DFVSGames.Gadget

end OAI
end

theorem solution : type_of% @OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction_oai := @OAI.DFVSGames.Decoder.ActualMatrixContradiction.contradiction_oai
