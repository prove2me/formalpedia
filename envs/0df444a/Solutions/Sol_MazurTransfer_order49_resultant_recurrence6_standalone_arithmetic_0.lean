-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_0
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T20:31:28.413445+00:00
-- url     : https://prove2.me/submissions/078da218-a275-4ef9-9e19-b3a9b13d28cd

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData0
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData1
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData3
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ComputeDegree
namespace MazurTransfer.Order49Standalone



/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Inner. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: Inner

This file is a checked arithmetic shard for the sixth pseudo-division
recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private def recurrence6InnerBand0 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block0 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block0 +
    0
private theorem recurrence6InnerBand0_eq :
    recurrence6InnerBand0 = normalizedResidual6InnerBlock0 := by
  unfold recurrence6InnerBand0 remainder7Coefficient1TimesRemainder6Coefficient1Block0
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block0 normalizedResidual6InnerBlock0
  ring

private def recurrence6InnerBand1 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block1 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block1 +
    0
private theorem recurrence6InnerBand1_eq :
    recurrence6InnerBand1 = normalizedResidual6InnerBlock1 := by
  unfold recurrence6InnerBand1 remainder7Coefficient1TimesRemainder6Coefficient1Block1
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block1 normalizedResidual6InnerBlock1
  ring

private def recurrence6InnerBand2 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block2 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block2 +
    0
private theorem recurrence6InnerBand2_eq :
    recurrence6InnerBand2 = normalizedResidual6InnerBlock2 := by
  unfold recurrence6InnerBand2 remainder7Coefficient1TimesRemainder6Coefficient1Block2
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block2 normalizedResidual6InnerBlock2
  ring

private def recurrence6InnerBand3 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block3 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block3 +
    0
private theorem recurrence6InnerBand3_eq :
    recurrence6InnerBand3 = normalizedResidual6InnerBlock3 := by
  unfold recurrence6InnerBand3 remainder7Coefficient1TimesRemainder6Coefficient1Block3
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block3 normalizedResidual6InnerBlock3
  ring

private def recurrence6InnerBand4 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block4 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block4 +
    0
private theorem recurrence6InnerBand4_eq :
    recurrence6InnerBand4 = normalizedResidual6InnerBlock4 := by
  unfold recurrence6InnerBand4 remainder7Coefficient1TimesRemainder6Coefficient1Block4
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block4 normalizedResidual6InnerBlock4
  ring

private def recurrence6InnerBand5 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block5 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block5 +
    0
private theorem recurrence6InnerBand5_eq :
    recurrence6InnerBand5 = normalizedResidual6InnerBlock5 := by
  unfold recurrence6InnerBand5 remainder7Coefficient1TimesRemainder6Coefficient1Block5
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block5 normalizedResidual6InnerBlock5
  ring

private def recurrence6InnerBand6 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block6 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block6 +
    0
private theorem recurrence6InnerBand6_eq :
    recurrence6InnerBand6 = normalizedResidual6InnerBlock6 := by
  unfold recurrence6InnerBand6 remainder7Coefficient1TimesRemainder6Coefficient1Block6
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block6 normalizedResidual6InnerBlock6
  ring

private def recurrence6InnerBand7 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block7 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block7 +
    0
private theorem recurrence6InnerBand7_eq :
    recurrence6InnerBand7 = normalizedResidual6InnerBlock7 := by
  unfold recurrence6InnerBand7 remainder7Coefficient1TimesRemainder6Coefficient1Block7
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block7 normalizedResidual6InnerBlock7
  ring

private def recurrence6InnerBand8 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block8 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block8 +
    0
private theorem recurrence6InnerBand8_eq :
    recurrence6InnerBand8 = normalizedResidual6InnerBlock8 := by
  unfold recurrence6InnerBand8 remainder7Coefficient1TimesRemainder6Coefficient1Block8
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block8 normalizedResidual6InnerBlock8
  ring

private def recurrence6InnerBand9 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block9 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block9 +
    0
private theorem recurrence6InnerBand9_eq :
    recurrence6InnerBand9 = normalizedResidual6InnerBlock9 := by
  unfold recurrence6InnerBand9 remainder7Coefficient1TimesRemainder6Coefficient1Block9
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block9 normalizedResidual6InnerBlock9
  ring

private def recurrence6InnerBand10 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block10 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block10 +
    0
private theorem recurrence6InnerBand10_eq :
    recurrence6InnerBand10 = normalizedResidual6InnerBlock10 := by
  unfold recurrence6InnerBand10 remainder7Coefficient1TimesRemainder6Coefficient1Block10
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block10 normalizedResidual6InnerBlock10
  ring

private def recurrence6InnerBand11 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block11 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block11 +
    0
private theorem recurrence6InnerBand11_eq :
    recurrence6InnerBand11 = normalizedResidual6InnerBlock11 := by
  unfold recurrence6InnerBand11 remainder7Coefficient1TimesRemainder6Coefficient1Block11
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block11 normalizedResidual6InnerBlock11
  ring

private def recurrence6InnerBand12 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block12 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block12 +
    0
private theorem recurrence6InnerBand12_eq :
    recurrence6InnerBand12 = normalizedResidual6InnerBlock12 := by
  unfold recurrence6InnerBand12 remainder7Coefficient1TimesRemainder6Coefficient1Block12
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block12 normalizedResidual6InnerBlock12
  ring

private def recurrence6InnerBand13 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block13 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block13 +
    0
private theorem recurrence6InnerBand13_eq :
    recurrence6InnerBand13 = normalizedResidual6InnerBlock13 := by
  unfold recurrence6InnerBand13 remainder7Coefficient1TimesRemainder6Coefficient1Block13
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block13 normalizedResidual6InnerBlock13
  ring

private def recurrence6InnerBand14 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block14 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block14 +
    0
private theorem recurrence6InnerBand14_eq :
    recurrence6InnerBand14 = normalizedResidual6InnerBlock14 := by
  unfold recurrence6InnerBand14 remainder7Coefficient1TimesRemainder6Coefficient1Block14
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block14 normalizedResidual6InnerBlock14
  ring

private def recurrence6InnerBand15 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block15 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block15 +
    0
private theorem recurrence6InnerBand15_eq :
    recurrence6InnerBand15 = normalizedResidual6InnerBlock15 := by
  unfold recurrence6InnerBand15 remainder7Coefficient1TimesRemainder6Coefficient1Block15
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block15 normalizedResidual6InnerBlock15
  ring

private def recurrence6InnerBand16 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block16 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block16 +
    0
private theorem recurrence6InnerBand16_eq :
    recurrence6InnerBand16 = normalizedResidual6InnerBlock16 := by
  unfold recurrence6InnerBand16 remainder7Coefficient1TimesRemainder6Coefficient1Block16
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block16 normalizedResidual6InnerBlock16
  ring

private def recurrence6InnerBand17 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block17 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block17 +
    0
private theorem recurrence6InnerBand17_eq :
    recurrence6InnerBand17 = normalizedResidual6InnerBlock17 := by
  unfold recurrence6InnerBand17 remainder7Coefficient1TimesRemainder6Coefficient1Block17
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block17 normalizedResidual6InnerBlock17
  ring

private def recurrence6InnerBand18 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block18 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block18 +
    0
private theorem recurrence6InnerBand18_eq :
    recurrence6InnerBand18 = normalizedResidual6InnerBlock18 := by
  unfold recurrence6InnerBand18 remainder7Coefficient1TimesRemainder6Coefficient1Block18
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block18 normalizedResidual6InnerBlock18
  ring

private def recurrence6InnerBand19 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block19 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block19 +
    0
private theorem recurrence6InnerBand19_eq :
    recurrence6InnerBand19 = normalizedResidual6InnerBlock19 := by
  unfold recurrence6InnerBand19 remainder7Coefficient1TimesRemainder6Coefficient1Block19
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block19 normalizedResidual6InnerBlock19
  ring

private def recurrence6InnerBand20 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block20 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block20 +
    0
private theorem recurrence6InnerBand20_eq :
    recurrence6InnerBand20 = normalizedResidual6InnerBlock20 := by
  unfold recurrence6InnerBand20 remainder7Coefficient1TimesRemainder6Coefficient1Block20
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block20 normalizedResidual6InnerBlock20
  ring

private def recurrence6InnerBand21 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block21 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block21 +
    0
private theorem recurrence6InnerBand21_eq :
    recurrence6InnerBand21 = normalizedResidual6InnerBlock21 := by
  unfold recurrence6InnerBand21 remainder7Coefficient1TimesRemainder6Coefficient1Block21
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block21 normalizedResidual6InnerBlock21
  ring

private def recurrence6InnerBand22 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block22 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block22 +
    0
private theorem recurrence6InnerBand22_eq :
    recurrence6InnerBand22 = normalizedResidual6InnerBlock22 := by
  unfold recurrence6InnerBand22 remainder7Coefficient1TimesRemainder6Coefficient1Block22
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block22 normalizedResidual6InnerBlock22
  ring

private def recurrence6InnerBand23 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block23 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block23 +
    0
private theorem recurrence6InnerBand23_eq :
    recurrence6InnerBand23 = normalizedResidual6InnerBlock23 := by
  unfold recurrence6InnerBand23 remainder7Coefficient1TimesRemainder6Coefficient1Block23
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block23 normalizedResidual6InnerBlock23
  ring

private def recurrence6InnerBand24 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block24 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block24 +
    0
private theorem recurrence6InnerBand24_eq :
    recurrence6InnerBand24 = normalizedResidual6InnerBlock24 := by
  unfold recurrence6InnerBand24 remainder7Coefficient1TimesRemainder6Coefficient1Block24
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block24 normalizedResidual6InnerBlock24
  ring

private def recurrence6InnerBand25 : Coefficient :=
  remainder7Coefficient1TimesRemainder6Coefficient1Block25 -
    remainder7Coefficient0TimesRemainder6Coefficient2Block25 +
    0
private theorem recurrence6InnerBand25_eq :
    recurrence6InnerBand25 = normalizedResidual6InnerBlock25 := by
  unfold recurrence6InnerBand25 remainder7Coefficient1TimesRemainder6Coefficient1Block25
  unfold remainder7Coefficient0TimesRemainder6Coefficient2Block25 normalizedResidual6InnerBlock25
  ring

private def recurrence6InnerBands : Coefficient :=
  recurrence6InnerBand0 +
  recurrence6InnerBand1 +
  recurrence6InnerBand2 +
  recurrence6InnerBand3 +
  recurrence6InnerBand4 +
  recurrence6InnerBand5 +
  recurrence6InnerBand6 +
  recurrence6InnerBand7 +
  recurrence6InnerBand8 +
  recurrence6InnerBand9 +
  recurrence6InnerBand10 +
  recurrence6InnerBand11 +
  recurrence6InnerBand12 +
  recurrence6InnerBand13 +
  recurrence6InnerBand14 +
  recurrence6InnerBand15 +
  recurrence6InnerBand16 +
  recurrence6InnerBand17 +
  recurrence6InnerBand18 +
  recurrence6InnerBand19 +
  recurrence6InnerBand20 +
  recurrence6InnerBand21 +
  recurrence6InnerBand22 +
  recurrence6InnerBand23 +
  recurrence6InnerBand24 +
  recurrence6InnerBand25

theorem normalizedResidual6Inner_eq :
    remainder7Coefficient1TimesRemainder6Coefficient1 -
        remainder7Coefficient0TimesRemainder6Coefficient2 +
      0 =
    normalizedResidual6Inner := by
  have rearrange :
      remainder7Coefficient1TimesRemainder6Coefficient1 -
          remainder7Coefficient0TimesRemainder6Coefficient2 +
        0 =
      recurrence6InnerBands := by
    unfold remainder7Coefficient1TimesRemainder6Coefficient1
    unfold remainder7Coefficient0TimesRemainder6Coefficient2 recurrence6InnerBands
    unfold recurrence6InnerBand0 recurrence6InnerBand1 recurrence6InnerBand2 recurrence6InnerBand3
    unfold recurrence6InnerBand4 recurrence6InnerBand5 recurrence6InnerBand6 recurrence6InnerBand7
    unfold recurrence6InnerBand8 recurrence6InnerBand9 recurrence6InnerBand10 recurrence6InnerBand11
    unfold recurrence6InnerBand12 recurrence6InnerBand13 recurrence6InnerBand14
    unfold recurrence6InnerBand15 recurrence6InnerBand16 recurrence6InnerBand17
    unfold recurrence6InnerBand18 recurrence6InnerBand19 recurrence6InnerBand20
    unfold recurrence6InnerBand21 recurrence6InnerBand22 recurrence6InnerBand23
    unfold recurrence6InnerBand24 recurrence6InnerBand25
    ring
  rw [rearrange]
  unfold recurrence6InnerBands
  unfold normalizedResidual6Inner
  rw [recurrence6InnerBand0_eq]
  rw [recurrence6InnerBand1_eq]
  rw [recurrence6InnerBand2_eq]
  rw [recurrence6InnerBand3_eq]
  rw [recurrence6InnerBand4_eq]
  rw [recurrence6InnerBand5_eq]
  rw [recurrence6InnerBand6_eq]
  rw [recurrence6InnerBand7_eq]
  rw [recurrence6InnerBand8_eq]
  rw [recurrence6InnerBand9_eq]
  rw [recurrence6InnerBand10_eq]
  rw [recurrence6InnerBand11_eq]
  rw [recurrence6InnerBand12_eq]
  rw [recurrence6InnerBand13_eq]
  rw [recurrence6InnerBand14_eq]
  rw [recurrence6InnerBand15_eq]
  rw [recurrence6InnerBand16_eq]
  rw [recurrence6InnerBand17_eq]
  rw [recurrence6InnerBand18_eq]
  rw [recurrence6InnerBand19_eq]
  rw [recurrence6InnerBand20_eq]
  rw [recurrence6InnerBand21_eq]
  rw [recurrence6InnerBand22_eq]
  rw [recurrence6InnerBand23_eq]
  rw [recurrence6InnerBand24_eq]
  rw [recurrence6InnerBand25_eq]
  try ring

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

end

open Polynomial
open MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate


end MazurTransfer.Order49Standalone
open Polynomial
open MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate

theorem solution :
MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient1TimesRemainder6Coefficient1 -
        MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.remainder7Coefficient0TimesRemainder6Coefficient2 +
      0 =
    MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Inner := by
  exact MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Inner_eq

#print axioms solution
