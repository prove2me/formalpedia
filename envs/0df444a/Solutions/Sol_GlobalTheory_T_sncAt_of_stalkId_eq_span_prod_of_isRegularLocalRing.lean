-- Prove2me | solution 1 for GlobalTheory.T.sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:33:41.304432+00:00
-- url     : https://prove2.me/submissions/856936e4-f6e7-4627-9b79-3238a7b8bdd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SncAtOfStalkIdEqSpanProd
import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SncAtOfStalkIdEqSpanProdStatement
import Theorems.Thm_GlobalTheory_sncAt_of_stalkId_eq_span_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y), IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)), FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by
  first | exact @GlobalTheory.sncAt_of_stalkId_eq_span_prod | exact GlobalTheory.sncAt_of_stalkId_eq_span_prod | (intros; apply GlobalTheory.sncAt_of_stalkId_eq_span_prod <;> assumption)
end _root_.GlobalTheory.T
