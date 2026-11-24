-- Prove2me | solution 1 for GlobalTheory.LevQuot.appLE_congr_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:40:56.206477+00:00
-- url     : https://prove2.me/submissions/30743454-83d0-4e66-af89-2ee4a36d0382

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}
namespace GlobalTheory.LevQuot
theorem _root_.solution {Z : Scheme.{0}} {f g : Z ⟶ X} (e : f = g) (U : X.Opens) (V : Z.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (h' : V ≤ g ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V h' := by
  simp only [e]
end GlobalTheory.LevQuot
