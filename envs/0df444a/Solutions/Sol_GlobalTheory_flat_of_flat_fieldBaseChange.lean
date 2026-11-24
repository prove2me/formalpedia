-- Prove2me | solution 1 for GlobalTheory.flat_of_flat_fieldBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:09.399747+00:00
-- url     : https://prove2.me/submissions/72c7b125-0dd3-48b1-993a-002e94b2bc63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Theorems.Thm_GlobalTheory_flat_descendsAlong_fpqc
import Theorems.Thm_GlobalTheory_isPullback_overPullback_map_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k k' : Type) [Field k] [Field k'] (σ : k →+* k')
    (X Y : Over (Sp k)) (φ : X ⟶ Y)
    (h : Flat ((Over.pullback (spMap σ)).map φ).left) : Flat φ.left := by
  haveI := flat_descendsAlong_fpqc
  have h₁ : Flat (spMap σ) := inferInstance
  have h₂ : Surjective (spMap σ) := inferInstance
  have h₃ : QuasiCompact (spMap σ) := inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_overPullback_map_left (spMap σ) φ)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h
end GlobalTheory
