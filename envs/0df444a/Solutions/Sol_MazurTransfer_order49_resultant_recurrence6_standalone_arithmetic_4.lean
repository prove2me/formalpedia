-- Prove2me | solution 1 for MazurTransfer.order49_resultant_recurrence6_standalone_arithmetic_4
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T21:07:42.415894+00:00
-- url     : https://prove2.me/submissions/ed21662a-2a1a-4c3a-a072-e57f06c154ba

import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneNormalizedData
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData4
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData5
import Definitions.Def_MazurTransfer_Order49Recurrence6StandaloneArithmeticData6
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ComputeDegree
namespace MazurTransfer.Order49Standalone



/- Source module: MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence6Residual. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Recurrence 6 certificate: Residual

This file is a checked arithmetic shard for the sixth pseudo-division
recurrence in the order-seven branch-zero resultant certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

private def recurrence6ResidualBand0 : Coefficient :=
  normalizedResidual6Term1Block0 -
    normalizedResidual6Term2Block0 +
    normalizedResidual6Term3Block0

private theorem recurrence6ResidualBand0_eq : recurrence6ResidualBand0 = 0 := by
  unfold recurrence6ResidualBand0 normalizedResidual6Term1Block0 normalizedResidual6Term2Block0
  unfold normalizedResidual6Term3Block0
  ring

private def recurrence6ResidualBand1 : Coefficient :=
  normalizedResidual6Term1Block1 -
    normalizedResidual6Term2Block1 +
    normalizedResidual6Term3Block1

private theorem recurrence6ResidualBand1_eq : recurrence6ResidualBand1 = 0 := by
  unfold recurrence6ResidualBand1 normalizedResidual6Term1Block1 normalizedResidual6Term2Block1
  unfold normalizedResidual6Term3Block1
  ring

private def recurrence6ResidualBand2 : Coefficient :=
  normalizedResidual6Term1Block2 -
    normalizedResidual6Term2Block2 +
    normalizedResidual6Term3Block2

private theorem recurrence6ResidualBand2_eq : recurrence6ResidualBand2 = 0 := by
  unfold recurrence6ResidualBand2 normalizedResidual6Term1Block2 normalizedResidual6Term2Block2
  unfold normalizedResidual6Term3Block2
  ring

private def recurrence6ResidualBand3 : Coefficient :=
  normalizedResidual6Term1Block3 -
    normalizedResidual6Term2Block3 +
    normalizedResidual6Term3Block3

private theorem recurrence6ResidualBand3_eq : recurrence6ResidualBand3 = 0 := by
  unfold recurrence6ResidualBand3 normalizedResidual6Term1Block3 normalizedResidual6Term2Block3
  unfold normalizedResidual6Term3Block3
  ring

private def recurrence6ResidualBand4 : Coefficient :=
  normalizedResidual6Term1Block4 -
    normalizedResidual6Term2Block4 +
    normalizedResidual6Term3Block4

private theorem recurrence6ResidualBand4_eq : recurrence6ResidualBand4 = 0 := by
  unfold recurrence6ResidualBand4 normalizedResidual6Term1Block4 normalizedResidual6Term2Block4
  unfold normalizedResidual6Term3Block4
  ring

private def recurrence6ResidualBand5 : Coefficient :=
  normalizedResidual6Term1Block5 -
    normalizedResidual6Term2Block5 +
    normalizedResidual6Term3Block5

private theorem recurrence6ResidualBand5_eq : recurrence6ResidualBand5 = 0 := by
  unfold recurrence6ResidualBand5 normalizedResidual6Term1Block5 normalizedResidual6Term2Block5
  unfold normalizedResidual6Term3Block5
  ring

private def recurrence6ResidualBand6 : Coefficient :=
  normalizedResidual6Term1Block6 -
    normalizedResidual6Term2Block6 +
    normalizedResidual6Term3Block6

private theorem recurrence6ResidualBand6_eq : recurrence6ResidualBand6 = 0 := by
  unfold recurrence6ResidualBand6 normalizedResidual6Term1Block6 normalizedResidual6Term2Block6
  unfold normalizedResidual6Term3Block6
  ring

private def recurrence6ResidualBand7 : Coefficient :=
  normalizedResidual6Term1Block7 -
    normalizedResidual6Term2Block7 +
    normalizedResidual6Term3Block7

private theorem recurrence6ResidualBand7_eq : recurrence6ResidualBand7 = 0 := by
  unfold recurrence6ResidualBand7 normalizedResidual6Term1Block7 normalizedResidual6Term2Block7
  unfold normalizedResidual6Term3Block7
  ring

private def recurrence6ResidualBand8 : Coefficient :=
  normalizedResidual6Term1Block8 -
    normalizedResidual6Term2Block8 +
    normalizedResidual6Term3Block8

private theorem recurrence6ResidualBand8_eq : recurrence6ResidualBand8 = 0 := by
  unfold recurrence6ResidualBand8 normalizedResidual6Term1Block8 normalizedResidual6Term2Block8
  unfold normalizedResidual6Term3Block8
  ring

private def recurrence6ResidualBand9 : Coefficient :=
  normalizedResidual6Term1Block9 -
    normalizedResidual6Term2Block9 +
    normalizedResidual6Term3Block9

private theorem recurrence6ResidualBand9_eq : recurrence6ResidualBand9 = 0 := by
  unfold recurrence6ResidualBand9 normalizedResidual6Term1Block9 normalizedResidual6Term2Block9
  unfold normalizedResidual6Term3Block9
  ring

private def recurrence6ResidualBand10 : Coefficient :=
  normalizedResidual6Term1Block10 -
    normalizedResidual6Term2Block10 +
    normalizedResidual6Term3Block10

private theorem recurrence6ResidualBand10_eq : recurrence6ResidualBand10 = 0 := by
  unfold recurrence6ResidualBand10 normalizedResidual6Term1Block10 normalizedResidual6Term2Block10
  unfold normalizedResidual6Term3Block10
  ring

private def recurrence6ResidualBand11 : Coefficient :=
  normalizedResidual6Term1Block11 -
    normalizedResidual6Term2Block11 +
    normalizedResidual6Term3Block11

private theorem recurrence6ResidualBand11_eq : recurrence6ResidualBand11 = 0 := by
  unfold recurrence6ResidualBand11 normalizedResidual6Term1Block11 normalizedResidual6Term2Block11
  unfold normalizedResidual6Term3Block11
  ring

private def recurrence6ResidualBand12 : Coefficient :=
  normalizedResidual6Term1Block12 -
    normalizedResidual6Term2Block12 +
    normalizedResidual6Term3Block12

private theorem recurrence6ResidualBand12_eq : recurrence6ResidualBand12 = 0 := by
  unfold recurrence6ResidualBand12 normalizedResidual6Term1Block12 normalizedResidual6Term2Block12
  unfold normalizedResidual6Term3Block12
  ring

private def recurrence6ResidualBand13 : Coefficient :=
  normalizedResidual6Term1Block13 -
    normalizedResidual6Term2Block13 +
    normalizedResidual6Term3Block13

private theorem recurrence6ResidualBand13_eq : recurrence6ResidualBand13 = 0 := by
  unfold recurrence6ResidualBand13 normalizedResidual6Term1Block13 normalizedResidual6Term2Block13
  unfold normalizedResidual6Term3Block13
  ring

private def recurrence6ResidualBand14 : Coefficient :=
  normalizedResidual6Term1Block14 -
    normalizedResidual6Term2Block14 +
    normalizedResidual6Term3Block14

private theorem recurrence6ResidualBand14_eq : recurrence6ResidualBand14 = 0 := by
  unfold recurrence6ResidualBand14 normalizedResidual6Term1Block14 normalizedResidual6Term2Block14
  unfold normalizedResidual6Term3Block14
  ring

private def recurrence6ResidualBand15 : Coefficient :=
  normalizedResidual6Term1Block15 -
    normalizedResidual6Term2Block15 +
    normalizedResidual6Term3Block15

private theorem recurrence6ResidualBand15_eq : recurrence6ResidualBand15 = 0 := by
  unfold recurrence6ResidualBand15 normalizedResidual6Term1Block15 normalizedResidual6Term2Block15
  unfold normalizedResidual6Term3Block15
  ring

private def recurrence6ResidualBand16 : Coefficient :=
  normalizedResidual6Term1Block16 -
    normalizedResidual6Term2Block16 +
    normalizedResidual6Term3Block16

private theorem recurrence6ResidualBand16_eq : recurrence6ResidualBand16 = 0 := by
  unfold recurrence6ResidualBand16 normalizedResidual6Term1Block16 normalizedResidual6Term2Block16
  unfold normalizedResidual6Term3Block16
  ring

private def recurrence6ResidualBand17 : Coefficient :=
  normalizedResidual6Term1Block17 -
    normalizedResidual6Term2Block17 +
    normalizedResidual6Term3Block17

private theorem recurrence6ResidualBand17_eq : recurrence6ResidualBand17 = 0 := by
  unfold recurrence6ResidualBand17 normalizedResidual6Term1Block17 normalizedResidual6Term2Block17
  unfold normalizedResidual6Term3Block17
  ring

private def recurrence6ResidualBand18 : Coefficient :=
  normalizedResidual6Term1Block18 -
    normalizedResidual6Term2Block18 +
    normalizedResidual6Term3Block18

private theorem recurrence6ResidualBand18_eq : recurrence6ResidualBand18 = 0 := by
  unfold recurrence6ResidualBand18 normalizedResidual6Term1Block18 normalizedResidual6Term2Block18
  unfold normalizedResidual6Term3Block18
  ring

private def recurrence6ResidualBand19 : Coefficient :=
  normalizedResidual6Term1Block19 -
    normalizedResidual6Term2Block19 +
    normalizedResidual6Term3Block19

private theorem recurrence6ResidualBand19_eq : recurrence6ResidualBand19 = 0 := by
  unfold recurrence6ResidualBand19 normalizedResidual6Term1Block19 normalizedResidual6Term2Block19
  unfold normalizedResidual6Term3Block19
  ring

private def recurrence6ResidualBand20 : Coefficient :=
  normalizedResidual6Term1Block20 -
    normalizedResidual6Term2Block20 +
    normalizedResidual6Term3Block20

private theorem recurrence6ResidualBand20_eq : recurrence6ResidualBand20 = 0 := by
  unfold recurrence6ResidualBand20 normalizedResidual6Term1Block20 normalizedResidual6Term2Block20
  unfold normalizedResidual6Term3Block20
  ring

private def recurrence6ResidualBand21 : Coefficient :=
  normalizedResidual6Term1Block21 -
    normalizedResidual6Term2Block21 +
    normalizedResidual6Term3Block21

private theorem recurrence6ResidualBand21_eq : recurrence6ResidualBand21 = 0 := by
  unfold recurrence6ResidualBand21 normalizedResidual6Term1Block21 normalizedResidual6Term2Block21
  unfold normalizedResidual6Term3Block21
  ring

private def recurrence6ResidualBand22 : Coefficient :=
  normalizedResidual6Term1Block22 -
    normalizedResidual6Term2Block22 +
    normalizedResidual6Term3Block22

private theorem recurrence6ResidualBand22_eq : recurrence6ResidualBand22 = 0 := by
  unfold recurrence6ResidualBand22 normalizedResidual6Term1Block22 normalizedResidual6Term2Block22
  unfold normalizedResidual6Term3Block22
  ring

private def recurrence6ResidualBand23 : Coefficient :=
  normalizedResidual6Term1Block23 -
    normalizedResidual6Term2Block23 +
    normalizedResidual6Term3Block23

private theorem recurrence6ResidualBand23_eq : recurrence6ResidualBand23 = 0 := by
  unfold recurrence6ResidualBand23 normalizedResidual6Term1Block23 normalizedResidual6Term2Block23
  unfold normalizedResidual6Term3Block23
  ring

private def recurrence6ResidualBand24 : Coefficient :=
  normalizedResidual6Term1Block24 -
    normalizedResidual6Term2Block24 +
    normalizedResidual6Term3Block24

private theorem recurrence6ResidualBand24_eq : recurrence6ResidualBand24 = 0 := by
  unfold recurrence6ResidualBand24 normalizedResidual6Term1Block24 normalizedResidual6Term2Block24
  unfold normalizedResidual6Term3Block24
  ring

private def recurrence6ResidualBand25 : Coefficient :=
  normalizedResidual6Term1Block25 -
    normalizedResidual6Term2Block25 +
    normalizedResidual6Term3Block25

private theorem recurrence6ResidualBand25_eq : recurrence6ResidualBand25 = 0 := by
  unfold recurrence6ResidualBand25 normalizedResidual6Term1Block25 normalizedResidual6Term2Block25
  unfold normalizedResidual6Term3Block25
  ring

private def recurrence6ResidualBand26 : Coefficient :=
  normalizedResidual6Term1Block26 -
    normalizedResidual6Term2Block26 +
    normalizedResidual6Term3Block26

private theorem recurrence6ResidualBand26_eq : recurrence6ResidualBand26 = 0 := by
  unfold recurrence6ResidualBand26 normalizedResidual6Term1Block26 normalizedResidual6Term2Block26
  unfold normalizedResidual6Term3Block26
  ring

private def recurrence6ResidualBand27 : Coefficient :=
  normalizedResidual6Term1Block27 -
    normalizedResidual6Term2Block27 +
    normalizedResidual6Term3Block27

private theorem recurrence6ResidualBand27_eq : recurrence6ResidualBand27 = 0 := by
  unfold recurrence6ResidualBand27 normalizedResidual6Term1Block27 normalizedResidual6Term2Block27
  unfold normalizedResidual6Term3Block27
  ring

private def recurrence6ResidualBand28 : Coefficient :=
  normalizedResidual6Term1Block28 -
    normalizedResidual6Term2Block28 +
    normalizedResidual6Term3Block28

private theorem recurrence6ResidualBand28_eq : recurrence6ResidualBand28 = 0 := by
  unfold recurrence6ResidualBand28 normalizedResidual6Term1Block28 normalizedResidual6Term2Block28
  unfold normalizedResidual6Term3Block28
  ring

private def recurrence6ResidualBand29 : Coefficient :=
  normalizedResidual6Term1Block29 -
    normalizedResidual6Term2Block29 +
    normalizedResidual6Term3Block29

private theorem recurrence6ResidualBand29_eq : recurrence6ResidualBand29 = 0 := by
  unfold recurrence6ResidualBand29 normalizedResidual6Term1Block29 normalizedResidual6Term2Block29
  unfold normalizedResidual6Term3Block29
  ring

private def recurrence6ResidualBand30 : Coefficient :=
  normalizedResidual6Term1Block30 -
    normalizedResidual6Term2Block30 +
    normalizedResidual6Term3Block30

private theorem recurrence6ResidualBand30_eq : recurrence6ResidualBand30 = 0 := by
  unfold recurrence6ResidualBand30 normalizedResidual6Term1Block30 normalizedResidual6Term2Block30
  unfold normalizedResidual6Term3Block30
  ring

private def recurrence6ResidualBand31 : Coefficient :=
  normalizedResidual6Term1Block31 -
    normalizedResidual6Term2Block31 +
    normalizedResidual6Term3Block31

private theorem recurrence6ResidualBand31_eq : recurrence6ResidualBand31 = 0 := by
  unfold recurrence6ResidualBand31 normalizedResidual6Term1Block31 normalizedResidual6Term2Block31
  unfold normalizedResidual6Term3Block31
  ring

private def recurrence6ResidualBand32 : Coefficient :=
  normalizedResidual6Term1Block32 -
    normalizedResidual6Term2Block32 +
    normalizedResidual6Term3Block32

private theorem recurrence6ResidualBand32_eq : recurrence6ResidualBand32 = 0 := by
  unfold recurrence6ResidualBand32 normalizedResidual6Term1Block32 normalizedResidual6Term2Block32
  unfold normalizedResidual6Term3Block32
  ring

private def recurrence6ResidualBand33 : Coefficient :=
  normalizedResidual6Term1Block33 -
    normalizedResidual6Term2Block33 +
    normalizedResidual6Term3Block33

private theorem recurrence6ResidualBand33_eq : recurrence6ResidualBand33 = 0 := by
  unfold recurrence6ResidualBand33 normalizedResidual6Term1Block33 normalizedResidual6Term2Block33
  unfold normalizedResidual6Term3Block33
  ring

private def recurrence6ResidualBand34 : Coefficient :=
  normalizedResidual6Term1Block34 -
    normalizedResidual6Term2Block34 +
    normalizedResidual6Term3Block34

private theorem recurrence6ResidualBand34_eq : recurrence6ResidualBand34 = 0 := by
  unfold recurrence6ResidualBand34 normalizedResidual6Term1Block34 normalizedResidual6Term2Block34
  unfold normalizedResidual6Term3Block34
  ring

private def recurrence6ResidualBand35 : Coefficient :=
  normalizedResidual6Term1Block35 -
    normalizedResidual6Term2Block35 +
    normalizedResidual6Term3Block35

private theorem recurrence6ResidualBand35_eq : recurrence6ResidualBand35 = 0 := by
  unfold recurrence6ResidualBand35 normalizedResidual6Term1Block35 normalizedResidual6Term2Block35
  unfold normalizedResidual6Term3Block35
  ring

private def recurrence6ResidualBands : Coefficient :=
  recurrence6ResidualBand0 +
  recurrence6ResidualBand1 +
  recurrence6ResidualBand2 +
  recurrence6ResidualBand3 +
  recurrence6ResidualBand4 +
  recurrence6ResidualBand5 +
  recurrence6ResidualBand6 +
  recurrence6ResidualBand7 +
  recurrence6ResidualBand8 +
  recurrence6ResidualBand9 +
  recurrence6ResidualBand10 +
  recurrence6ResidualBand11 +
  recurrence6ResidualBand12 +
  recurrence6ResidualBand13 +
  recurrence6ResidualBand14 +
  recurrence6ResidualBand15 +
  recurrence6ResidualBand16 +
  recurrence6ResidualBand17 +
  recurrence6ResidualBand18 +
  recurrence6ResidualBand19 +
  recurrence6ResidualBand20 +
  recurrence6ResidualBand21 +
  recurrence6ResidualBand22 +
  recurrence6ResidualBand23 +
  recurrence6ResidualBand24 +
  recurrence6ResidualBand25 +
  recurrence6ResidualBand26 +
  recurrence6ResidualBand27 +
  recurrence6ResidualBand28 +
  recurrence6ResidualBand29 +
  recurrence6ResidualBand30 +
  recurrence6ResidualBand31 +
  recurrence6ResidualBand32 +
  recurrence6ResidualBand33 +
  recurrence6ResidualBand34 +
  recurrence6ResidualBand35

theorem normalizedResidual6_eq_zero :
    normalizedResidual6Term1 -
        normalizedResidual6Term2 +
      normalizedResidual6Term3 =
    (0 : Coefficient) := by
  have rearrange :
      normalizedResidual6Term1 -
          normalizedResidual6Term2 +
        normalizedResidual6Term3 =
      recurrence6ResidualBands := by
    unfold normalizedResidual6Term1 normalizedResidual6Term2 normalizedResidual6Term3
    unfold recurrence6ResidualBands recurrence6ResidualBand0 recurrence6ResidualBand1
    unfold recurrence6ResidualBand2 recurrence6ResidualBand3 recurrence6ResidualBand4
    unfold recurrence6ResidualBand5 recurrence6ResidualBand6 recurrence6ResidualBand7
    unfold recurrence6ResidualBand8 recurrence6ResidualBand9 recurrence6ResidualBand10
    unfold recurrence6ResidualBand11 recurrence6ResidualBand12 recurrence6ResidualBand13
    unfold recurrence6ResidualBand14 recurrence6ResidualBand15 recurrence6ResidualBand16
    unfold recurrence6ResidualBand17 recurrence6ResidualBand18 recurrence6ResidualBand19
    unfold recurrence6ResidualBand20 recurrence6ResidualBand21 recurrence6ResidualBand22
    unfold recurrence6ResidualBand23 recurrence6ResidualBand24 recurrence6ResidualBand25
    unfold recurrence6ResidualBand26 recurrence6ResidualBand27 recurrence6ResidualBand28
    unfold recurrence6ResidualBand29 recurrence6ResidualBand30 recurrence6ResidualBand31
    unfold recurrence6ResidualBand32 recurrence6ResidualBand33 recurrence6ResidualBand34
    unfold recurrence6ResidualBand35
    ring
  rw [rearrange]
  unfold recurrence6ResidualBands
  rw [recurrence6ResidualBand0_eq]
  rw [recurrence6ResidualBand1_eq]
  rw [recurrence6ResidualBand2_eq]
  rw [recurrence6ResidualBand3_eq]
  rw [recurrence6ResidualBand4_eq]
  rw [recurrence6ResidualBand5_eq]
  rw [recurrence6ResidualBand6_eq]
  rw [recurrence6ResidualBand7_eq]
  rw [recurrence6ResidualBand8_eq]
  rw [recurrence6ResidualBand9_eq]
  rw [recurrence6ResidualBand10_eq]
  rw [recurrence6ResidualBand11_eq]
  rw [recurrence6ResidualBand12_eq]
  rw [recurrence6ResidualBand13_eq]
  rw [recurrence6ResidualBand14_eq]
  rw [recurrence6ResidualBand15_eq]
  rw [recurrence6ResidualBand16_eq]
  rw [recurrence6ResidualBand17_eq]
  rw [recurrence6ResidualBand18_eq]
  rw [recurrence6ResidualBand19_eq]
  rw [recurrence6ResidualBand20_eq]
  rw [recurrence6ResidualBand21_eq]
  rw [recurrence6ResidualBand22_eq]
  rw [recurrence6ResidualBand23_eq]
  rw [recurrence6ResidualBand24_eq]
  rw [recurrence6ResidualBand25_eq]
  rw [recurrence6ResidualBand26_eq]
  rw [recurrence6ResidualBand27_eq]
  rw [recurrence6ResidualBand28_eq]
  rw [recurrence6ResidualBand29_eq]
  rw [recurrence6ResidualBand30_eq]
  rw [recurrence6ResidualBand31_eq]
  rw [recurrence6ResidualBand32_eq]
  rw [recurrence6ResidualBand33_eq]
  rw [recurrence6ResidualBand34_eq]
  rw [recurrence6ResidualBand35_eq]
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
MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term1 -
        MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term2 +
      MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6Term3 =
    (0 : MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.Coefficient) := by
  exact MazurTransfer.Order49Standalone.MazurTorsion.Kubert.OrderSevenBacktrackingCertificate.Internal.ResultantCertificate.normalizedResidual6_eq_zero

#print axioms solution
