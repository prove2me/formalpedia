-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AbForms.Zp_sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:49:07.642611+00:00
-- url     : https://prove2.me/submissions/dd1a3ebb-d6a5-42e4-b7bd-821fe2d6dc32

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UOfIsBaseChange
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_Zp_map
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_tzo_map
import Theorems.Thm_GlobalTheory_CompanionTheory_AbForms_uOf_spec

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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AbForms
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
variable {R : Type} [CommRing R]
variable {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W] [Module Rᵐᵒᵖ W]
  [IsCentralScalar R W] {y₀ : Sp (TrivSqZeroExt R W) ⟶ A.left} (hy : IsCot A.hom η[A].left W y₀)
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M']
variable (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap (algebraMap R B))
namespace GlobalTheory.CompanionTheory.AbForms
theorem _root_.solution (f : Ω[B⁄R] →ₗ[B] M) :
    Zp x hx (sg f) (sg_w f) = tzo hy ((f.restrictScalars R) ∘ₗ uOf hy x hx) := by
  have h := Zp_map x hx x hx (RingHom.id B) (by rw [spMap_id, Category.id_comp]) rfl
    ((f.restrictScalars R : Ω[B⁄R] →ₗ[R] M) : Ω[B⁄R] →+ M) (fun b m ↦ f.map_smul b m)
    (diagSec R B : B →+* _) diag_w (sg f) (sg_w f) rfl (tm_w f)
  rw [← h, uOf_spec hy x hx]
  exact tzo_map hy (RingHom.id B) rfl (f.restrictScalars R) (fun b m ↦ f.map_smul b m) _ _
end GlobalTheory.CompanionTheory.AbForms
