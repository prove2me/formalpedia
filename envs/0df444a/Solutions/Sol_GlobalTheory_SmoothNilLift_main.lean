-- Prove2me | solution 1 for GlobalTheory.SmoothNilLift.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:16:36.367585+00:00
-- url     : https://prove2.me/submissions/84ca67f9-0423-49c8-9497-f0cfc6ddf518

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLiftOfNil
import Theorems.Thm_GlobalTheory_SmoothNilLift_exists_point_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SmoothNilLift
namespace GlobalTheory.SmoothNilLift
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    Smooth G.hom → ∀ (K W : LAlg R₀) (ρW : LHom W K), IsNilOver ρW → SM B K W ρW) := by
  intro R₀ _ G _ _ B e hb _ hnat hsm K W ρW hρ
  refine ⟨hρ, fun x => ?_⟩
  obtain ⟨y, hy⟩ := exists_point_lift G ρW.1 hρ.1 hρ.2 (e K x)
  obtain ⟨y', rfl⟩ := (hb W).2 y
  exact ⟨y', (hb K).1 (by rw [hnat, hy])⟩
end GlobalTheory.SmoothNilLift
