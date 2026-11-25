-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dict.L3_dn_two_eq_d2_L2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:31:53.87226+00:00
-- url     : https://prove2.me/submissions/bbec0c13-aa16-4648-9e0b-175bc48e5a15

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_cof_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_dn2
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_face_zero_mk3
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_face_one_mk3
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_face_two_mk3
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_face_three_mk3
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
theorem _root_.solution (f : Cn F 2) : L3 F (dn F 2 f) = d2 F (L2 F f) := by
  funext T T' T'' T''' φ ψ χ
  show dn F 2 f (mk₃ φ ψ χ) = L2 F f T' T'' T''' ψ χ - L2 F f T T'' T''' (φ ≫ ψ) χ +
    L2 F f T T' T''' φ (ψ ≫ χ) - mp F χ (L2 F f T T' T'' φ ψ)
  rw [dn2, cof_eq F (n := 2) 0 (mk₃ φ ψ χ) (mk₂ ψ χ) (face_zero_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 1 (mk₃ φ ψ χ) (mk₂ (φ ≫ ψ) χ) (face_one_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 2 (mk₃ φ ψ χ) (mk₂ φ (ψ ≫ χ)) (face_two_mk3 φ ψ χ) (𝟙 T''') HEq.rfl f,
    cof_eq F (n := 2) 3 (mk₃ φ ψ χ) (mk₂ φ ψ) (face_three_mk3 φ ψ χ) χ HEq.rfl f]
  show mp F (𝟙 T''') (f (mk₂ ψ χ)) - mp F (𝟙 T''') (f (mk₂ (φ ≫ ψ) χ)) +
    mp F (𝟙 T''') (f (mk₂ φ (ψ ≫ χ))) - mp F χ (f (mk₂ φ ψ)) = _
  rw [mp_id_apply F T''' (f (mk₂ ψ χ)), mp_id_apply F T''' (f (mk₂ (φ ≫ ψ) χ)),
    mp_id_apply F T''' (f (mk₂ φ (ψ ≫ χ)))]
  rfl
end GlobalTheory.CompanionTheory.Dict
