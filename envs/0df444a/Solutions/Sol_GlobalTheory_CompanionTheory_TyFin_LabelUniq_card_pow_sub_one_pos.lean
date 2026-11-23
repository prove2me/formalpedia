-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.LabelUniq.card_pow_sub_one_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:16.543175+00:00
-- url     : https://prove2.me/submissions/bb587ac2-480e-495d-98bd-f54afaea8fb1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_two_le_card

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
theorem _root_.solution {d : ℕ} (hd : 0 < d) : 0 < Fintype.card K ^ d - 1 := by
  have h2 : 2 ≤ Fintype.card K := two_le_card
  have h3 : Fintype.card K ≤ Fintype.card K ^ d := Nat.le_self_pow hd.ne' _
  omega
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
