-- Prove2me | solution 1 for GlobalTheory.HL.OrthCompl.isON_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:45:15.342912+00:00
-- url     : https://prove2.me/submissions/8721a4c8-ce91-4036-82bb-07f136356ea9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
import Theorems.Thm_GlobalTheory_HL_OrthCompl_hf_eq_zero_symm
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.HL.OrthCompl
theorem _root_.solution (h : IsHerm L Hm) {k : ℕ} {v : Fin n → E} {e : Fin k → Fin n → E}
    (hv : hf L Hm v v = 1) (hev : ∀ i, hf L Hm (e i) v = 0) (he : IsON L Hm e) :
    IsON L Hm (Fin.cons v e : Fin (k + 1) → Fin n → E) := by
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · simpa using hv
  · simpa [(Fin.succ_ne_zero j).symm] using hf_eq_zero_symm L h (hev j)
  · simpa using hev i
  · simpa using he i j
end GlobalTheory.HL.OrthCompl
