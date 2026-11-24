-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.exists_isReps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:33.206995+00:00
-- url     : https://prove2.me/submissions/1a612e86-1d0b-4d03-804e-8c626c4eb985

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousDistribHaarCharUnitsOfCompactOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsHaarQuotientIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtMeas
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.EtMeas
theorem _root_.solution (A : Et F E) : ∃ S : Set A.Kˣ, A.IsReps S := by
  let H : Subgroup A.Kˣ := (Units.map (Algebra.norm A.K : A.L →* A.K)).range
  have key : ∀ a x : A.Kˣ, (∃ y : A.L, IsUnit y ∧ (a : A.K) = x * A.NL y) ↔
      (QuotientGroup.mk x : A.Kˣ ⧸ H) = QuotientGroup.mk a := by
    intro a x
    rw [QuotientGroup.eq]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨hy.unit, Units.ext ?_⟩
      simp [h, Et.NL]
    · rintro ⟨y, h⟩
      refine ⟨y, y.isUnit, ?_⟩
      have := congrArg Units.val h
      simp only [Units.coe_map, Units.val_mul] at this
      rw [Et.NL, this]; simp
  refine ⟨Set.range (Quotient.out : A.Kˣ ⧸ H → A.Kˣ), fun a => ⟨Quotient.out (QuotientGroup.mk a : A.Kˣ ⧸ H),
    ⟨⟨_, rfl⟩, (key _ _).2 (QuotientGroup.out_eq' _)⟩, ?_⟩⟩
  rintro _ ⟨⟨q, rfl⟩, h⟩
  rw [← (key _ _).1 h, QuotientGroup.out_eq']
end GlobalTheory.JR.EtMeas
