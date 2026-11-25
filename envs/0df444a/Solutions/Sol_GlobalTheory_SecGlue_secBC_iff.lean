-- Prove2me | solution 1 for GlobalTheory.SecGlue.secBC_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:12.060706+00:00
-- url     : https://prove2.me/submissions/185a9162-42d5-4940-b12d-7e5920d17b8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
import Theorems.Thm_GlobalTheory_SecGlue_Can_unique
import Theorems.Thm_P2M_GlobalTheory_SecGlue_scal_one__5d4d8c965e1e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.SecGlue
theorem _root_.solution {S T : Type} [CommRing S] [CommRing T] {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    {pm} (h : Can Xo.univ.t.G (spMap φ) x x' pm) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) :
    SecBC φ 1 x x' s s' ↔ Rel pm s s' := by
  have e : ∀ j, scal x 1 j * s.f j = s.f j := fun j => by rw [scal_one', _root_.one_mul]
  constructor
  · rintro ⟨pm', h1, h2, h3⟩ j hh
    obtain rfl : pm' = pm := Can.unique ⟨h1, h2⟩ h
    exact (congrArg _ (e j).symm).trans (h3 j hh)
  · exact fun H => ⟨pm, h.1, h.2, fun j hh => (congrArg _ (e j)).trans (H j hh)⟩
end GlobalTheory.SecGlue
