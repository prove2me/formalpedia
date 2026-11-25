-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dict.face_one_mk3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:01.680928+00:00
-- url     : https://prove2.me/submissions/deed8aa1-e25d-4817-9f53-7ca406ce30d4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Dict_eq_mk__f0261a00c975

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dict
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''')
namespace GlobalTheory.CompanionTheory.Dict
theorem _root_.solution : face 1 (mk₃ φ ψ χ) = mk₂ (φ ≫ ψ) χ := by
  exact eq_mk₂ (face 1 (mk₃ φ ψ χ)) (φ ≫ ψ) χ rfl rfl
end GlobalTheory.CompanionTheory.Dict
