-- Prove2me | solution 1 for GlobalTheory.TorsionCard.exists_chi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:17.635509+00:00
-- url     : https://prove2.me/submissions/e1a26088-b24f-4202-8b4c-a5b97b4b655a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCosetRepresentativesOfFiniteSubgroupPadicI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChiOntoOfUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardTorsionMulFinrank
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_norm_eq_one


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
theorem _root_.solution (P : LocPrime l) :
    ∃ χ : GQ l →* ℤ_[l]ˣ, ∀ g, ((χ g : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l]) := by
  have hn := GlobalTheory.Cyc.IsCyc.norm_eq_one P.χQ_cyc
  refine ⟨{ toFun := fun g => PadicInt.mkUnits (hn g), map_one' := ?_, map_mul' := ?_ },
    fun g => PadicInt.mkUnits_eq (hn g)⟩
  · apply Units.ext; apply PadicInt.ext
    simp
  · intro a b; apply Units.ext; apply PadicInt.ext
    simp only [Units.val_mul, PadicInt.coe_mul, PadicInt.mkUnits_eq, map_mul]
end GlobalTheory.TorsionCard
