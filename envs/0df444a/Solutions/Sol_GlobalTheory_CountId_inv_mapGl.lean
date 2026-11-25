-- Prove2me | solution 1 for GlobalTheory.CountId.inv_mapGl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:11.366267+00:00
-- url     : https://prove2.me/submissions/c6cc8767-0cf5-4cff-b734-f2d10270682b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_GlobalTheory_CountId_mom_mapGl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k']
namespace GlobalTheory.CountId
theorem _root_.solution (φ : k →+* k') (Y : Gl r k) : inv (mapGl φ Y) = (inv Y).map φ := by
  simp only [JR.inv, Inv.map, mapGl]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only
    rw [Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    exact mom_mapGl φ Y i
end GlobalTheory.CountId
