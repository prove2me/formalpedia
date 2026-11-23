-- Prove2me | solution 1 for GlobalTheory.ExtUnique.oAct_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:11.320852+00:00
-- url     : https://prove2.me/submissions/176a5737-2c27-4d72-80f9-631bc62725d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExtUnique
variable {U S : Scheme.{0}} {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
namespace GlobalTheory.ExtUnique
theorem _root_.solution {O : Type} [CommRing O] {G : Over S} [GrpObj G] {a b : OAct O G} (h : ∀ x, a.act x = b.act x) :
    a = b := by
  obtain ⟨a, _, _, _, _⟩ := a
  obtain ⟨b, _, _, _, _⟩ := b
  obtain rfl : a = b := funext h
  rfl
end GlobalTheory.ExtUnique
