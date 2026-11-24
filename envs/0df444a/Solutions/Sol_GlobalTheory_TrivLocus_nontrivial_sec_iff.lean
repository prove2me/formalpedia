-- Prove2me | solution 1 for GlobalTheory.TrivLocus.nontrivial_sec_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:29:49.404882+00:00
-- url     : https://prove2.me/submissions/e5be88d0-1d31-42a4-8a5b-754f0ddf3edd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKerIffMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.TrivLocus
variable {X Y : Scheme.{0}}
namespace GlobalTheory.TrivLocus
theorem _root_.solution (N : LB X) : Nontrivial (LB.Sec N) ↔ ∃ (s : LB.Sec N) (i : N.ι), s.f i ≠ 0 := by
  rw [nontrivial_iff_exists_ne (zeroSec N)]
  refine exists_congr fun s => ?_
  obtain ⟨sf, hs⟩ := s
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have : sf = fun _ => 0 := funext hn
    subst this
    exact h rfl
  · rintro ⟨i, hi⟩ h
    exact hi (congrArg (fun s => s.f i) h)
end GlobalTheory.TrivLocus
