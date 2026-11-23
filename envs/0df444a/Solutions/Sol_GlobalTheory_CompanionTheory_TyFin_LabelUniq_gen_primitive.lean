-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.LabelUniq.gen_primitive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:04.295158+00:00
-- url     : https://prove2.me/submissions/f23c9a1e-fa88-47a0-9c31-7a952be4a671

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
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
theorem _root_.solution (C : LabelConv K) {d : ℕ} (hd : 0 < d) :
    IsPrimitiveRoot (C.gen d) (Fintype.card K ^ d - 1) := by
  rw [← C.gen_order d hd]
  exact IsPrimitiveRoot.orderOf _
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
