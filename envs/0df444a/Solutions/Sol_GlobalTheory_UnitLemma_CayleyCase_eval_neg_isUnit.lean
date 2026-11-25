-- Prove2me | solution 1 for GlobalTheory.UnitLemma.CayleyCase.eval_neg_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:01:52.333455+00:00
-- url     : https://prove2.me/submissions/bd49fee8-138d-4f5a-a63b-4eca8d89775e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}
namespace GlobalTheory.UnitLemma.CayleyCase
theorem _root_.solution (hodd : K.Odd) (Q : K.O[X]) (s : K.Oˣ)
    (hQr : Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) :
    IsUnit (Q.eval (-(s : K.O))) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← eval₂_hom, ← eval_map, hQr]
  simp only [eval_pow, eval_sub, eval_X, eval_C, map_neg]
  apply pow_ne_zero
  have h2 : IsLocalRing.residue K.O 2 ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hodd
  have hs : IsLocalRing.residue K.O s ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 s.isUnit
  rw [show -(IsLocalRing.residue K.O s) - IsLocalRing.residue K.O s =
    -(IsLocalRing.residue K.O 2 * IsLocalRing.residue K.O s) by rw [map_ofNat]; ring]
  exact neg_ne_zero.2 (mul_ne_zero h2 hs)
end GlobalTheory.UnitLemma.CayleyCase
