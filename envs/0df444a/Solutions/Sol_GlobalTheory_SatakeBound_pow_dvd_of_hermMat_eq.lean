-- Prove2me | solution 1 for GlobalTheory.SatakeBound.pow_dvd_of_hermMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:31:26.485632+00:00
-- url     : https://prove2.me/submissions/ea4c5255-31ad-43de-aa3f-a4426d1d1529

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsBorelSphRevInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormLeOfCompleteHomogeneousLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HermiteReductionUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Theorems.Thm_GlobalTheory_SatakeBound_eq_zero_of_upper
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open GlobalTheory GlobalTheory.SatakeBound
variable {R : Type} [CommRing R] {n : ℕ}
variable {p : R} {a a' : Fin n → ℕ}
variable [IsDomain R]
namespace GlobalTheory.SatakeBound
theorem _root_.solution (hp : p ≠ 0) {c : HermIdx p a} {c' : HermIdx p a'} {W : Matrix (Fin n) (Fin n) R}
    (h : hermMat p a c = hermMat p a' c' * W) (i : Fin n) : p ^ a' i ∣ p ^ a i := by
  have hW : ∀ l, i < l → W l i = 0 :=
    eq_zero_of_upper (fun _ _ => hermMat_gt c') (fun l => W l i) _ (fun _ _ h1 h2 => h2.trans h1) fun l hl e => by
      rw [← Matrix.mul_apply, ← h, hermMat_gt c hl, hermMat_diag] at e
      exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero _ hp)
  refine ⟨W i i, ?_⟩
  rw [← hermMat_diag c, h, Matrix.mul_apply, Finset.sum_eq_single i (fun s _ hs => ?_) (by simp), hermMat_diag]
  rcases lt_or_gt_of_ne hs with h1 | h1
  · rw [hermMat_gt c' h1, zero_mul]
  · rw [hW s h1, mul_zero]
end GlobalTheory.SatakeBound
