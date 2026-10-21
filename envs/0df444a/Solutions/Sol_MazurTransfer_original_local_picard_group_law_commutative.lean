-- Prove2me | solution 1 for MazurTransfer.original_local_picard_group_law_commutative
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T04:58:24.325987+00:00
-- url     : https://prove2.me/submissions/a472fe34-28f6-486f-bee5-a5bb7ed27311

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same chosen integral local Picard group law is commutative, with the original prime and coefficient hypotheses.
Named downstream consumer: positive-scalar finiteness and flatness of the same actual nineteen norm models.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalPicardModelsData
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13LocalIntegralCoefficientMaps MazurTransfer.Order13GoodPrimeLocalPicardModels
open MazurTorsion.XOneThirteenProjectiveCurve MazurTransfer.Order13IntegralSections
namespace MazurTransfer.OriginalLocalPicardGroupLawCommutativeBoundary20261020
end MazurTransfer.OriginalLocalPicardGroupLawCommutativeBoundary20261020
namespace MazurTransfer.OriginalLocalPicardGroupLawCommutativeProof20261020
variable (q : ℕ) [Fact q.Prime]
theorem local_law_isCommutative (hq : ¬ (q : ℤ) ∣ 104) :
    (localLaw q hq).IsCommutative :=
  (show RepresentsRelSubPic (curveToBase (LocalRing q))
    (positiveInfinitySection (LocalRing q))
    (algEquivZeroGroupCut (curveToBase (LocalRing q))
      (positiveInfinitySection (LocalRing q))).toSubPicCondition (localPicard q hq)
    from localRepresentation q hq).relativeGroupLaw_isCommutative
end MazurTransfer.OriginalLocalPicardGroupLawCommutativeProof20261020
theorem solution : ∀ (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104), (localLaw q hq).IsCommutative := by
  exact MazurTransfer.OriginalLocalPicardGroupLawCommutativeProof20261020.local_law_isCommutative
#print axioms solution
