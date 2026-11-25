-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dict.L2_dn_one_eq_d1_L1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:01:03.68558+00:00
-- url     : https://prove2.me/submissions/b43017e7-d3e8-4667-864d-01d04ccd0015

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_cof_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_dn1
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_cech_nerve_face_two_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_cech_nerve_face_two_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Dict_cech_nerve_face_two_two
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
theorem _root_.solution (f : Cn F 1) : L2 F (dn F 1 f) = d1 F (L1 F f) := by
  funext T T' T'' φ ψ
  show dn F 1 f (mk₂ φ ψ) = mp F ψ (L1 F f T T' φ) - L1 F f T T'' (φ ≫ ψ) + L1 F f T' T'' ψ
  rw [dn1, cof_eq F (n := 1) 0 (mk₂ φ ψ) (mk₁ ψ) (cech_nerve_face_two_zero φ ψ) (𝟙 T'') HEq.rfl f,
    cof_eq F (n := 1) 1 (mk₂ φ ψ) (mk₁ (φ ≫ ψ)) (cech_nerve_face_two_one φ ψ) (𝟙 T'') HEq.rfl f,
    cof_eq F (n := 1) 2 (mk₂ φ ψ) (mk₁ φ) (cech_nerve_face_two_two φ ψ) ψ HEq.rfl f]
  conv_lhs => rw [sub_add_comm]
  show mp F ψ (f (mk₁ φ)) - mp F (𝟙 T'') (f (mk₁ (φ ≫ ψ))) + mp F (𝟙 T'') (f (mk₁ ψ)) = _
  rw [mp_id_apply F T'' (f (mk₁ (φ ≫ ψ))), mp_id_apply F T'' (f (mk₁ ψ))]
  rfl
end GlobalTheory.CompanionTheory.Dict
