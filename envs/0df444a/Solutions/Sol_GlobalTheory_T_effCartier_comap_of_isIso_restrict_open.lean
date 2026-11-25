-- Prove2me | solution 1 for GlobalTheory.T.effCartier_comap_of_isIso_restrict_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:23:46.22338+00:00
-- url     : https://prove2.me/submissions/33c0df8f-b048-4459-bb25-638bdb8b473a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EffCartierComapOfIsIsoRestrictOpen
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EffCartierComapOfIsIsoRestrictOpenStatement
import Theorems.Thm_GlobalTheory_effCartier_comap_of_isIso_restrict


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by
  first | exact @GlobalTheory.effCartier_comap_of_isIso_restrict | exact GlobalTheory.effCartier_comap_of_isIso_restrict | (intros; apply GlobalTheory.effCartier_comap_of_isIso_restrict <;> assumption)
end _root_.GlobalTheory.T
