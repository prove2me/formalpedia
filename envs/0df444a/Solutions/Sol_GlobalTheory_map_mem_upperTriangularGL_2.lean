-- Prove2me | solution 2 for GlobalTheory.map_mem_upperTriangularGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:53.3278+00:00
-- url     : https://prove2.me/submissions/2db4a929-f8ed-4bea-bed6-0b73f68c2cef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
import Theorems.Thm_GlobalTheory_mem_upperTriangularGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]
variable {ι R}
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S] (f : R →+* S) {g : GL ι R}
    (hg : g ∈ upperTriangularGL ι R) :
    Matrix.GeneralLinearGroup.map f g ∈ upperTriangularGL ι S := by
  rw [mem_upperTriangularGL] at hg ⊢
  intro i j hij
  simp [Matrix.GeneralLinearGroup.map_apply, hg i j hij]
end GlobalTheory
