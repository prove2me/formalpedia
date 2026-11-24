-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.LabelUniq.minpoly_pow_card_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:44:17.929671+00:00
-- url     : https://prove2.me/submissions/dc35bab9-c368-430e-89f9-f4ce0d421973

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
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
section Field
variable {K : Type} [Field K] [Fintype K]
private theorem minpoly_pow_card_pow_lemma (x : AlgebraicClosure K) :
    minpoly K (x ^ Fintype.card K) = minpoly K x := by
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  symm
  apply minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint)
  · rw [← Polynomial.expand_aeval, FiniteField.expand_card, map_pow, minpoly.aeval,
      zero_pow Fintype.card_ne_zero]
  · exact minpoly.monic hint
end Field
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
section Label
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Label
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
end

set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.LabelUniq
variable {K : Type} [Field K] [Fintype K]
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
theorem _root_.solution (x : AlgebraicClosure K) (i : ℕ) :
    minpoly K (x ^ (Fintype.card K ^ i)) = minpoly K x := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_mul, minpoly_pow_card_pow_lemma, ih]
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
