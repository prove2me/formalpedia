-- Prove2me | solution 1 for GlobalTheory.CountId.mapGl_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:38:31.418776+00:00
-- url     : https://prove2.me/submissions/63c670cb-9aec-43bd-9bf7-757cebd0ef6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_P2M_GlobalTheory_CountId_map_mulVec__74df2fa150c8
import Theorems.Thm_P2M_GlobalTheory_CountId_map_vecMul__4969f4544bd1

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
theorem _root_.solution (φ : k →+* k') (γ : GL (Fin r) k) (Y : Gl r k) :
    mapGl φ (act γ Y) = act (Matrix.GeneralLinearGroup.map φ γ) (mapGl φ Y) := by
  simp only [mapGl, act]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp [Matrix.map_mul, Matrix.GeneralLinearGroup.map]
  · exact map_mulVec' φ _ _
  · simp only
    rw [map_vecMul']
    simp [Matrix.GeneralLinearGroup.map]
end GlobalTheory.CountId
