-- Prove2me | solution 1 for GlobalTheory.SecSpread.pull_sec_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:03:45.146984+00:00
-- url     : https://prove2.me/submissions/712932e1-0d89-461b-8a4c-28d1f2f1c31d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread
variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}
namespace GlobalTheory.SecSpread
theorem _root_.solution {L : LB X} (s : (L.pull φ).Sec) (z : X') {i j : L.ι} (hi : φ z ∈ L.U i) (hj : φ z ∈ L.U j) :
    gs (𝟙 X') z ((L.pull φ).U (fun _ => i)) (s.f (fun _ => i)) =
      (gm φ z _ (L.g i j)).val * gs (𝟙 X') z ((L.pull φ).U (fun _ => j)) (s.f (fun _ => j)) := by
  have := sec_trans s (𝟙 X') z (j := fun _ => i) (j' := fun _ => j) (mem_pull.2 hi) (mem_pull.2 hj)
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp] at this
  exact this
end GlobalTheory.SecSpread
