-- Prove2me | solution 1 for GlobalTheory.LiftTest.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:59:30.365259+00:00
-- url     : https://prove2.me/submissions/07ce91a1-d2c7-4a2e-8bfd-2a674fca0967

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Theorems.Thm_GlobalTheory_LiftTest_sval_eq_zero_of_flat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.LiftTest
namespace GlobalTheory.LiftTest
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p X L hL K _ φ ε d H Z r ⟨ρ, hρ⟩ z J hJ
  have := g.q_flat
  have := g.q_surj
  let b : Z ⟶ (thickObj R I e D.P.A).left :=
    pullback.lift (r ≫ p.left) ρ (by rw [Category.assoc, Over.w p, hρ])
  have hb : b ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ p.left := pullback.lift_fst _ _ _
  obtain ⟨w, rfl⟩ := (pullback.fst b g.q.left).surjective z
  refine sval_eq_zero_of_flat hL d r (pullback.fst b g.q.left) w (fun J' hJ' => ?_) J hJ
  refine H _ (pullback.snd b g.q.left) _ ?_ w J' hJ'
  rw [Category.assoc, ← hb, pullback.condition_assoc]
  rfl
end GlobalTheory.LiftTest
