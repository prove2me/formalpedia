-- Prove2me | solution 1 for OAI.BinPackingGap.pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:42:03.376263+00:00
-- url     : https://prove2.me/submissions/fb7bb20a-66f9-41ba-9c70-28ab9159244d

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C025
import Theorems.Thm_OAI_BinPackingGap_packingGapNPHard_oaiq082

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_DropPackingBoundMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.DropPackingBoundMachine

open Turing BinPackingGames.Foundations.Complexity BinPackingGames.Reduction
open BinaryEncoding

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm := by
  intro k
  rcases k with k | k | k <;> change Finite Bool <;> infer_instance

end BinPackingGap.DropPackingBoundMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ApproximationImpliesP
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

theorem approximationAccepts_iff_bins_le (c B : Nat) (r : RawInstance)
    (hcount : r.length = 5 * B) (p : RawPacking)
    (hp : RawPacking.Feasible r p) :
    approximationAccepts c (some p) = true ↔ p.bins ≤ B + c := by
  rw [approximationAccepts_some, hp.1, hcount]
  omega

theorem AbsoluteAdditiveAlgorithm.accepts_of_hasPacking {c : Nat}
    (algorithm : AbsoluteAdditiveAlgorithm c) (r : RawInstance)
    (hr : r.Valid) (B : Nat) (hcount : r.length = 5 * B)
    (hyes : HasPacking (r.toInstance hr) B) :
    approximationAccepts c (algorithm.run (BinaryEncoding.rawInstanceBits r)) = true := by
  obtain ⟨p, hrun, hfeasible, hbound⟩ := algorithm.guarantee r hr
  rw [hrun, approximationAccepts_iff_bins_le c B r hcount p hfeasible]
  exact hbound.trans (Nat.add_le_add_right (opt_le_of_hasPacking hyes) c)

theorem AbsoluteAdditiveAlgorithm.rejects_of_not_hasPacking {c : Nat}
    (algorithm : AbsoluteAdditiveAlgorithm c) (r : RawInstance)
    (hr : r.Valid) (B : Nat) (hcount : r.length = 5 * B)
    (hno : ¬ HasPacking (r.toInstance hr) (B + c)) :
    approximationAccepts c (algorithm.run (BinaryEncoding.rawInstanceBits r)) = false := by
  obtain ⟨p, hrun, hfeasible, _⟩ := algorithm.guarantee r hr
  rw [hrun]
  have hnot : ¬ approximationAccepts c (some p) = true := by
    intro accepted
    have hbins := (approximationAccepts_iff_bins_le c B r hcount p hfeasible).mp accepted
    exact hno ((show HasPacking (r.toInstance hr) p.bins from
      ⟨RawPacking.toPacking r hr p hfeasible⟩).mono hbins)
  cases h : approximationAccepts c (some p) <;> simp_all

theorem PackingGapReduction.approximation_decides {c : Nat} {L : BitLanguage}
    (reduction : PackingGapReduction c L) (algorithm : AbsoluteAdditiveAlgorithm c)
    (x : List Bool) :
    L x ↔ approximationAccepts c
      (algorithm.run (BinaryEncoding.rawInstanceBits (reduction.reduce x).2)) = true := by
  constructor
  · intro hx
    exact algorithm.accepts_of_hasPacking _ (reduction.valid x) _
      (reduction.itemCount x) (reduction.completeness x hx)
  · intro hx
    by_contra hn
    have hf := algorithm.rejects_of_not_hasPacking _ (reduction.valid x) _
      (reduction.itemCount x) (reduction.soundness x hn)
    rw [hx] at hf
    cases hf

end BinPackingGap

namespace BinPackingGap.ApproximationDecisionMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinaryEncoding
open BinPackingCompleteness.BinaryEncoding (bitsValue bitsValue_bits frame)

theorem finiteAlphabet (c : Nat) :
    MachineFiniteAlphabet.FiniteAlphabet (computation c).tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (program c) cleanupTapes
    (cleanup_complete c) packingResultBits (fun bit => [bit]) (approximationAccepts c)
    (rawTime c) (rawRun c)

end BinPackingGap.ApproximationDecisionMachine

noncomputable section

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

theorem PackingGapReduction.approximationComputation_finiteAlphabet
    {c : Nat} {L : BitLanguage} (reduction : PackingGapReduction c L)
    (algorithm : AbsoluteAdditiveAlgorithm c) :
    MachineFiniteAlphabet.FiniteAlphabet (reduction.approximationComputation algorithm).tm := by
  have rawFinite : MachineFiniteAlphabet.FiniteAlphabet algorithm.rawComputation.tm :=
    algorithm.finiteAlphabet
  have projectedFinite := MachineFiniteAlphabet.composeBits reduction.computation
    DropPackingBoundMachine.computation reduction.finiteAlphabet
    DropPackingBoundMachine.finiteAlphabet
  have approximatedFinite := MachineFiniteAlphabet.composeBits
    (MachineSequential.composeBits reduction.computation DropPackingBoundMachine.computation)
    algorithm.rawComputation projectedFinite rawFinite
  exact MachineFiniteAlphabet.composeBits
    (MachineSequential.composeBits
      (MachineSequential.composeBits reduction.computation DropPackingBoundMachine.computation)
      algorithm.rawComputation)
    (ApproximationDecisionMachine.computation c) approximatedFinite
    (ApproximationDecisionMachine.finiteAlphabet c)

theorem PackingGapReduction.inP_of_absoluteAdditiveAlgorithm
    {c : Nat} {L : BitLanguage} (reduction : PackingGapReduction c L)
    (algorithm : AbsoluteAdditiveAlgorithm c) : InP L :=
  ⟨_, reduction.approximationComputation algorithm,
    reduction.approximationComputation_finiteAlphabet algorithm,
    reduction.approximation_decides algorithm⟩

theorem PackingGapNPHard.pEqualsNP_of_absoluteAdditiveAlgorithm {c : Nat}
    (hard : PackingGapNPHard c) (algorithm : AbsoluteAdditiveAlgorithm c) : PEqualsNP := by
  apply pEqualsNP_iff_np_subset_p.mpr
  intro L hL
  obtain ⟨reduction⟩ := hard L hL
  exact reduction.inP_of_absoluteAdditiveAlgorithm algorithm

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Results_AdditiveHardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

theorem pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082_oai (c : Nat)
    (algorithm : AbsoluteAdditiveAlgorithm c) : PEqualsNP :=
  (packingGapNPHard_oaiq082 c).pEqualsNP_of_absoluteAdditiveAlgorithm algorithm

end BinPackingGap

end OAI
end

theorem solution : type_of% @OAI.BinPackingGap.pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082_oai := @OAI.BinPackingGap.pEqualsNP_of_absoluteAdditiveAlgorithm_oaiq082_oai
