-- Prove2me | solution 1 for GlobalTheory.WeilMul.exists_commV_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:27:55.400384+00:00
-- url     : https://prove2.me/submissions/942aedd5-8ecd-48d0-8eaf-d2d55a814e59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Theorems.Thm_GlobalTheory_WeilMul_commIs_iff
import Theorems.Thm_GlobalTheory_WeilMul_CommV_restrict

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
theorem _root_.solution (hL : L.IsLB) {T : Over S} {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} {V W : T.left.Opens}
    (hle : W ≤ V)
    (h₁ : ∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y)
    (h₂ : ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
      CommIsOf A L k θx θy (unitRes V c)) :
    ∃ θx θy : ThetaGrp A L k (overRes W), θx.pt = overResι W ≫ x ∧ θy.pt = overResι W ≫ y ∧
      CommV θx θy (overResι W) c := by
  obtain ⟨θx, θy, px, py⟩ := h₁
  let f : overRes W ⟶ overRes V := Over.homMk (T.left.homOfLE hle) (by
    show T.left.homOfLE hle ≫ V.ι ≫ T.hom = W.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  have hf : f ≫ overResι V = overResι W := Over.OverMorphism.ext (T.left.homOfLE_ι hle)
  obtain ⟨θx₁, θy₁, qx, qy, hc⟩ := ((commIs_iff hL V θx θy c).1 (h₂ θx θy px py)).restrict hL f
  refine ⟨θx₁, θy₁, ?_, ?_, hf ▸ hc⟩
  · rw [qx, px, ← Category.assoc, hf]
  · rw [qy, py, ← Category.assoc, hf]
end GlobalTheory.WeilMul
