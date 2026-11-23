-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnrExt.isUnit_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:09.23992+00:00
-- url     : https://prove2.me/submissions/ea2d453a-0580-49f5-b15a-9f3d7f5c9a93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial IsLocalRing
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnrExt
variable {W k : Type} [CommRing W] [IsLocalRing W] [Field k] (v : W →+* k)
  (hker : RingHom.ker v = maximalIdeal W)
include hker
namespace GlobalTheory.UnitLemma.UnrExt
theorem _root_.solution {x : W} (hx : v x ≠ 0) : IsUnit x := by
  by_contra h
  have : x ∈ maximalIdeal W := h
  rw [← hker] at this
  exact hx this
end GlobalTheory.UnitLemma.UnrExt
