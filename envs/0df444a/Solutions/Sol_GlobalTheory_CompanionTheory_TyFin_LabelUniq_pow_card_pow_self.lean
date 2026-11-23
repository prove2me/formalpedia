-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.LabelUniq.pow_card_pow_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:52.945346+00:00
-- url     : https://prove2.me/submissions/ae3ea75a-582b-4bc5-9c1e-43321c351c95

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.LabelUniq
variable {K : Type} [Field K] [Fintype K]
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
theorem _root_.solution (x : AlgebraicClosure K) {d : ℕ} (hd : (minpoly K x).natDegree = d) :
    x ^ (Fintype.card K ^ d) = x := by
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hfin : Module.finrank K (IntermediateField.adjoin K {x}) = d := by
    rw [IntermediateField.adjoin.finrank hint, hd]
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
  letI : Fintype (IntermediateField.adjoin K {x}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin K {x}) = Fintype.card K ^ d := by
    rw [Module.card_fintype (Module.finBasis K (IntermediateField.adjoin K {x})), Fintype.card_fin, hfin]
  have h := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : IntermediateField.adjoin K {x})
  rw [hcard] at h
  simpa using congrArg (fun y : IntermediateField.adjoin K {x} => (y : AlgebraicClosure K)) h
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
