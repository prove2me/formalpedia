-- Prove2me | solution 1 for GlobalTheory.weilIs_alternating_skew_natural
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:21:12.34362+00:00
-- url     : https://prove2.me/submissions/f8ed493c-0347-47d9-9f01-729d54c2f2cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_change
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_self
import Theorems.Thm_GlobalTheory_CommPairing_weilIs_symm
import Theorems.Thm_GlobalTheory_CommPairing_weilIs_pull

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
open GlobalTheory
open CommPairing
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) := by
  intro hG hlift S P k T
  refine ⟨fun x hx p => ?_, fun x y c H => weilIs_symm P.isLB H,
    fun T' h x y c H => weilIs_pull hG P.isAb P.isLB h H⟩
  obtain ⟨V, hp, θ, hθ⟩ := hlift S P k T x hx p
  refine ⟨V, hp, ⟨θ, θ, hθ, hθ⟩, fun a b ha hb => ?_⟩
  have e : unitRes V (1 : Γ(T.left, ⊤)ˣ) = 1 := map_one _
  rw [e]
  exact commIsOf_change hG P.isAb P.isLB (ha.trans hθ.symm) (hb.trans hθ.symm) (commIsOf_self P.isLB θ)
end GlobalTheory
