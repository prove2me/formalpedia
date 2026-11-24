-- Prove2me | solution 1 for GlobalTheory.SatakeBound.eq_of_hermMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:31:00.341847+00:00
-- url     : https://prove2.me/submissions/dd8f6de2-2bce-4772-9608-6e6e5821d2c8

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
import Theorems.Thm_GlobalTheory_SatakeBound_hermMat_lt
import Theorems.Thm_GlobalTheory_SatakeBound_eq_zero_of_upper
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
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
theorem _root_.solution (hp : p ≠ 0) {c c' : HermIdx p a} {W : Matrix (Fin n) (Fin n) R}
    (h : hermMat p a c = hermMat p a c' * W) : c = c' := by
  have key : ∀ l j (hl : l < j), p ^ a l ∣ hermMat p a c l j - hermMat p a c' l j →
      c l ⟨j, hl⟩ = c' l ⟨j, hl⟩ := fun l j hl e => by
    rw [hermMat_lt c hl, hermMat_lt c' hl, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at e
    simpa using e
  have hW : W - 1 = 0 := by
    ext l j
    refine eq_zero_of_upper (fun _ _ => hermMat_gt c') (fun l => (W - 1) l j) (fun _ => True) (fun _ _ _ _ => trivial)
      (fun l _ e => ?_) l trivial
    rw [← Matrix.mul_apply, mul_sub, mul_one, ← h, hermMat_diag, Matrix.sub_apply (hermMat p a c)] at e
    have : hermMat p a c l j = hermMat p a c' l j := by
      rcases lt_trichotomy l j with h1 | rfl | h1
      · rw [hermMat_lt c h1, hermMat_lt c' h1, key l j h1 ⟨_, e.symm⟩]
      · rw [hermMat_diag, hermMat_diag]
      · rw [hermMat_gt c h1, hermMat_gt c' h1]
    rw [this, sub_self] at e
    exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero _ hp)
  rw [sub_eq_zero.1 hW, mul_one] at h
  funext l ⟨j, hl⟩
  exact key l j hl (by simp [h])
end GlobalTheory.SatakeBound
