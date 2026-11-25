-- Prove2me | solution 1 for GlobalTheory.WeilMul.CommV.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:12:21.0476+00:00
-- url     : https://prove2.me/submissions/31a43d32-d96e-4db2-b311-b3e2399a335f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Theorems.Thm_GlobalTheory_WeilMul_exists_mul

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
theorem _root_.solution [IsCommMonObj A] (hL : L.IsLB) {T T₀ : Over S}
    {θx θx' θy : ThetaGrp A L k T} {g : T ⟶ T₀} {c c' : Γ(T₀.left, ⊤)ˣ} (h : CommV θx θy g c)
    (h' : CommV θx' θy g c') : ∃ θ : ThetaGrp A L k T, θ.pt = θx.pt * θx'.pt ∧ CommV θ θy g (c * c') := by
  obtain ⟨θ, p, v⟩ := exists_mul hL θx θx'
  refine ⟨θ, p, fun T' t a z J hJ => ?_⟩
  have e₀ := congrArg Additive.ofMul (h T' t a z J hJ)
  have e₁ := congrArg Additive.ofMul (h' T' t ((t ≫ θx.pt) * a) z J hJ)
  rw [v _ _ _ _ _ hJ, v _ _ _ _ _ hJ, p, MonObj.comp_mul, map_mul, mul_comm (t ≫ θx.pt) (t ≫ θx'.pt),
    _root_.mul_assoc (t ≫ θx'.pt), mul_left_comm (t ≫ θx.pt) (t ≫ θy.pt)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at e₀ e₁ ⊢
  linear_combination (norm := abel) e₀ + e₁
end CommV
end GlobalTheory.WeilMul
