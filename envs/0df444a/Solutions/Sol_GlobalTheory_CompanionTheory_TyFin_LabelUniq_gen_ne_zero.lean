-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.LabelUniq.gen_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:44:17.173952+00:00
-- url     : https://prove2.me/submissions/97416803-aacc-496c-b21f-035efd729f91

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_gen_primitive
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_card_pow_sub_one_pos

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
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
theorem _root_.solution (C : LabelConv K) {d : ℕ} (hd : 0 < d) : C.gen d ≠ 0 := by
  exact (gen_primitive C hd).ne_zero (card_pow_sub_one_pos hd).ne'
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
