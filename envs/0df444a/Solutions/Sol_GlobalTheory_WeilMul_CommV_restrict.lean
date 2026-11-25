-- Prove2me | solution 1 for GlobalTheory.WeilMul.CommV.restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:14:44.005957+00:00
-- url     : https://prove2.me/submissions/b98f5310-b922-401b-a8a6-645daaeefc17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Theorems.Thm_GlobalTheory_WeilMul_exists_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilMul
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.WeilMul
namespace CommV
theorem _root_.solution (hL : L.IsLB) {T T₀ T₁ : Over S}
    {θx θy : ThetaGrp A L k T} {g : T ⟶ T₀} {c : Γ(T₀.left, ⊤)ˣ} (h : CommV θx θy g c) (f : T₁ ⟶ T) :
    ∃ θx₁ θy₁ : ThetaGrp A L k T₁, θx₁.pt = f ≫ θx.pt ∧ θy₁.pt = f ≫ θy.pt ∧ CommV θx₁ θy₁ (f ≫ g) c := by
  obtain ⟨θx₁, px, vx⟩ := exists_restrict hL θx f
  obtain ⟨θy₁, py, vy⟩ := exists_restrict hL θy f
  refine ⟨θx₁, θy₁, px, py, fun T' t a z J hJ => ?_⟩
  rw [vx _ _ _ _ _ hJ, vx _ _ _ _ _ hJ, vy _ _ _ _ _ hJ, vy _ _ _ _ _ hJ, px, py, ← Category.assoc,
    ← Category.assoc, ← Category.assoc]
  exact h T' (t ≫ f) a z J hJ
end CommV
end GlobalTheory.WeilMul
