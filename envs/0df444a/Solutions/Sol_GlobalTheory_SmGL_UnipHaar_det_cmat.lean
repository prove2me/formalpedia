-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.det_cmat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:16.371796+00:00
-- url     : https://prove2.me/submissions/12c6c923-097e-4e5e-8034-97cc174036a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_lmat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_rmat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable (e : (Σ a, m a) ≃ n)
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution (g : Levi R m) :
    ((∏ a, GeneralLinearGroup.det (g a) ^ modExp m a : Rˣ) : R) = (cmat e g).det := by
  rw [cmat, det_mul, det_rmat, det_lmat e (leviEmb_mem_parab R e g) _ (leviEmb_apply_same R e g),
    ← Finset.prod_mul_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [modExp, ← Nat.cast_sum, ← Nat.cast_sum, sub_eq_neg_add, _root_.zpow_add, _root_.zpow_neg,
    ← _root_.inv_zpow, zpow_natCast, zpow_natCast, ← map_inv, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val]
  rfl
end GlobalTheory.SmGL.UnipHaar
