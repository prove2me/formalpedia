-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LGroupSection.isClopen_cosetImage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:42:09.964799+00:00
-- url     : https://prove2.me/submissions/ef741fce-b47c-4c08-bce8-4b0026b2e5c4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LGroupSection
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.LGroupSection
theorem _root_.solution (H K : Subgroup G) [IsClosed (H : Set G)]
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (d : G) :
    IsClopen (cosetImage H K d) := by
  have himg : cosetImage H K d =
      ((↑) : G → G ⧸ H) '' ((fun k : G => d * k) '' (K : Set G)) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨d * k, ⟨k, hk, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
  rw [himg]
  have hopen : IsOpen ((fun k : G => d * k) '' (K : Set G)) :=
    (Homeomorph.mulLeft d).isOpenMap _ hKo
  have hcomp : IsCompact ((fun k : G => d * k) '' (K : Set G)) :=
    hKc.image (continuous_const.mul continuous_id)
  have hcomp' : IsCompact (((↑) : G → G ⧸ H) '' ((fun k : G => d * k) '' (K : Set G))) :=
    hcomp.image continuous_quotient_mk'
  exact ⟨hcomp'.isClosed, QuotientGroup.isOpenMap_coe _ hopen⟩
end GlobalTheory.CompanionTheory.LGroupSection
