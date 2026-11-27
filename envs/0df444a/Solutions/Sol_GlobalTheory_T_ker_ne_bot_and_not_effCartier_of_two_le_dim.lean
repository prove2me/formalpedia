-- Prove2me | solution 1 for GlobalTheory.T.ker_ne_bot_and_not_effCartier_of_two_le_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:38:02.920709+00:00
-- url     : https://prove2.me/submissions/495bded6-e484-4e68-acbb-93cc8d9ad569

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerNeBotAndNotEffCartier
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerNeBotAndNotEffCartierStatement
import Theorems.Thm_GlobalTheory_NotCartier_ker_ne_bot_and_not_effCartier


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
theorem _root_.solution : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y) [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) → i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by
  first | exact @GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier | exact GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier | (intros; apply GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier <;> assumption)
end _root_.GlobalTheory.T
