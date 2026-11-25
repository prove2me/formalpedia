-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dict.L1_dn_zero_eq_d0_L0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:11:15.138544+00:00
-- url     : https://prove2.me/submissions/0c357273-56ab-4b06-aa87-df9d155195e8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_cof_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_dn0
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_cech_nerve_face_one_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_cech_nerve_face_one_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows
namespace GlobalTheory.CompanionTheory.Dict
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
section Faces
variable {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''')
end Faces
private theorem mp_id_apply (X : C) (x : F.obj X) : mp F (𝟙 X) x = x := by
  rw [mp, CategoryTheory.Functor.map_id]
  rfl
end GlobalTheory.CompanionTheory.Dict
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dict
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.Dict
theorem _root_.solution (f : Cn F 0) : L1 F (dn F 0 f) = d0 F (L0 F f) := by
  funext T T' φ
  show dn F 0 f (mk₁ φ) = L0 F f T' - mp F φ (L0 F f T)
  rw [dn0, cof_eq F (n := 0) 0 (mk₁ φ) (mk₀ T') (cech_nerve_face_one_zero φ) (𝟙 T') HEq.rfl f,
    cof_eq F (n := 0) 1 (mk₁ φ) (mk₀ T) (cech_nerve_face_one_one φ) φ HEq.rfl f]
  show mp F (𝟙 T') (f (mk₀ T')) - mp F φ (f (mk₀ T)) = _
  rw [mp_id_apply F T' (f (mk₀ T'))]
  rfl
end GlobalTheory.CompanionTheory.Dict
