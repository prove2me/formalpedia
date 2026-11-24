-- Prove2me | solution 1 for GlobalTheory.SatakeBound.eq_zero_of_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:58.326708+00:00
-- url     : https://prove2.me/submissions/3aa4c3db-8725-4bb8-a360-3d0ced58131e

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
namespace GlobalTheory.SatakeBound
theorem _root_.solution {b : Matrix (Fin n) (Fin n) R} (hb : ∀ i j, j < i → b i j = 0) (x : Fin n → R)
    (P : Fin n → Prop) (hP : ∀ l l', l < l' → P l → P l')
    (h : ∀ l, P l → b l l * x l = ∑ s, b l s * x s → x l = 0) (l : Fin n) : P l → x l = 0 := by
  induction l using WellFoundedGT.induction with
  | ind l ih =>
    intro hl
    refine h l hl (Finset.sum_eq_single (f := fun s => b l s * x s) l (fun s _ hs => ?_) (by simp)).symm
    rcases lt_or_gt_of_ne hs with h1 | h1
    · rw [hb _ _ h1, zero_mul]
    · rw [ih s h1 (hP _ _ h1 hl), mul_zero]
end GlobalTheory.SatakeBound
