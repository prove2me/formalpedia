-- Prove2me | solution 1 for GlobalTheory.CommPairing.commIsOf_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:40:04.146016+00:00
-- url     : https://prove2.me/submissions/f7ac917e-d68d-4f9f-9101-c64e682ca571

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_iff
import Theorems.Thm_GlobalTheory_CommPairing_tval_div

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommPairing
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    {θx θy θx' θy' : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (hx : θx'.pt = θx.pt) (hy : θy'.pt = θy.pt)
    (H : CommIsOf A L k θx θy c) : CommIsOf A L k θx' θy' c := by
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  have e₀ := H Z r z J hJ
  have e₁ := tval_div hG hA hL θx' θx hx r θy.pt z J hJ
  have e₂ := tval_div hG hA hL θy' θy hy r θx.pt z J hJ
  rw [hx, hy]
  apply Additive.ofMul.injective
  have a₀ := congrArg Additive.ofMul e₀
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  simp only [ofMul_mul, ofMul_inv] at a₀ a₁ a₂ ⊢
  linear_combination (norm := abel) a₀ + a₁ - a₂
end GlobalTheory.CommPairing
