-- Prove2me | solution 1 for GlobalTheory.TorsionCard.eq_one_of_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:00.225987+00:00
-- url     : https://prove2.me/submissions/30717085-32f9-4e3f-89f1-ba042fc72c68

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCosetRepresentativesOfFiniteSubgroupPadicI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChiOntoOfUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardTorsionMulFinrank
import Theorems.Thm_GlobalTheory_TorsionCard_red_val
import Theorems.Thm_GlobalTheory_padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory GlobalTheory.TorsionCard
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.TorsionCard
theorem _root_.solution (h2 : l ≠ 2) (x : ℤ_[l]ˣ) (hx : IsOfFinOrder x) (h1 : red l x = 1) :
    x = 1 := by
  have hpos : 0 < orderOf x := hx.orderOf_pos
  have hpow : ((x : ℤ_[l])) ^ orderOf x = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hred : PadicInt.toZMod (x : ℤ_[l]) = 1 := by
    rw [← red_val, h1, Units.val_one]
  exact Units.ext (GlobalTheory.padicInt_eq_one_of_pow_eq_one_of_toZMod_eq_one h2 _ hpos.ne' hpow hred)
end GlobalTheory.TorsionCard
