-- Prove2me | solution 1 for GlobalTheory.CountId.mom_mapGl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:15.392805+00:00
-- url     : https://prove2.me/submissions/445de205-cef6-4248-800f-a1c1b30f69a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
import Theorems.Thm_P2M_GlobalTheory_CountId_map_mulVec__74df2fa150c8
import Theorems.Thm_P2M_GlobalTheory_CountId_map_pow__f545ffa1a6ed

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
theorem _root_.solution (φ : k →+* k') (Y : Gl r k) (i : ℕ) : mom (mapGl φ Y) i = φ (mom Y i) := by
  simp only [mom, mapGl]
  rw [← map_pow', ← map_mulVec']
  simp [dotProduct, map_sum, map_mul]
end GlobalTheory.CountId
