-- Prove2me | solution 1 for GlobalTheory.ThetaScalar.exists_theta_of_weilIs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:12:05.470617+00:00
-- url     : https://prove2.me/submissions/9203c5cf-dee9-4cae-ab96-a5206122e282

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Theorems.Thm_GlobalTheory_ThetaScalar_exists_theta_pull
import Theorems.Thm_P2M_GlobalTheory_ThetaScalar_exists_section_overRes__e8dc21895a9a

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaScalar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaScalar
theorem _root_.solution (hL : L.IsLB) (p : T.left) (hp : ∀ V : T.left.Opens, p ∈ V → V = ⊤) {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k x y c) : ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  obtain ⟨V, hV, ⟨θx, θy, hx, -⟩, -⟩ := h p
  obtain rfl := hp V hV
  obtain ⟨e, he⟩ := exists_section_overResι T
  obtain ⟨θ, hθ, -⟩ := exists_theta_pull hL e θx
  exact ⟨θ, by rw [hθ, hx, ← Category.assoc, he, Category.id_comp]⟩
end GlobalTheory.ThetaScalar
