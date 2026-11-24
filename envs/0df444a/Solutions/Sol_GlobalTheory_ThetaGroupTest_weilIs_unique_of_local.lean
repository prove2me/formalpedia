-- Prove2me | solution 1 for GlobalTheory.ThetaGroupTest.weilIs_unique_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:31:16.575109+00:00
-- url     : https://prove2.me/submissions/212bf9b8-10ee-4652-a32b-3d3fe1f630a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_WeilIsUniqueOfLocal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_commIsOf_unique


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
open GlobalTheory GlobalTheory.ThetaGroupTest
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.ThetaScalar
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
namespace GlobalTheory.ThetaGroupTest
theorem _root_.solution (p : T.left) (hp : ∀ V : T.left.Opens, p ∈ V → V = ⊤) (hL : L.IsLB) {x y : T ⟶ A}
    {c c' : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k x y c) (h' : WeilIs A L k x y c') :
    unitRes (T := T) ⊤ c = unitRes (T := T) ⊤ c' := by
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', -, H'⟩ := h' p
  obtain rfl := hp V hV
  obtain rfl := hp V' hV'
  exact commIsOf_unique hL θx θy _ _ (H θx θy hx hy) (H' θx θy hx hy)
end GlobalTheory.ThetaGroupTest
