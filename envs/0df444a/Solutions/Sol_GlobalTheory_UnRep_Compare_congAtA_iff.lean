-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.congAtA_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:27:02.756299+00:00
-- url     : https://prove2.me/submissions/78b96bbd-081a-49d7-8f30-77848daa4988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_congAtA_iff_of_bounded
import Theorems.Thm_GlobalTheory_AdLat_Translate_exists_bound
import Theorems.Thm_GlobalTheory_AdLat_hat_rational_points_and_approx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) {N D : ℕ} (hN : N ≠ 0) (hD : D ≠ 0)
    (k : Matrix (Fin n) (Fin n) (RA F E)) :
    CongAtA F L N D k ↔ CongOneAt N D (L : Set (Fin n → E)) k := by
  obtain ⟨d, hd, hk⟩ := Translate.exists_bound k hfg (hat_rational_points_and_approx F E n L hfg hsp).2.2.2
  exact congAtA_iff_of_bounded L hN hD hd.ne' k hk
end GlobalTheory.UnRep.Compare
