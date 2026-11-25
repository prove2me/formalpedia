-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.existsUnique_weilIs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:56:45.290882+00:00
-- url     : https://prove2.me/submissions/4b0a9591-f894-4295-8b5c-757feda0472e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_GlobalTheory_CommutatorPairing_weilIs_unique
import Theorems.Thm_GlobalTheory_CommutatorPairing_exists_weilIs

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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable {L : LB A.left} {k : ℤ}
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A),
    x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) →
    ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x y : T ⟶ P.A), x ^ k = 1 → y ^ k = 1 →
      ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L k x y c := by
  intro hG hl S P k T x y hx hy
  obtain ⟨c, hc⟩ := exists_weilIs hG P.isAb P.isLB (hl S P k T x hx) (hl S P k T y hy)
  exact ⟨c, hc, fun c' hc' => weilIs_unique hG P.isAb P.isLB hc' hc⟩
end GlobalTheory.CommutatorPairing
