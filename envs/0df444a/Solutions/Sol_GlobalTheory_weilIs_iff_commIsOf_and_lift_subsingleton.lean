-- Prove2me | solution 1 for GlobalTheory.weilIs_iff_commIsOf_and_lift_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:10:43.977773+00:00
-- url     : https://prove2.me/submissions/54ce4c40-f397-4af1-847f-d4de7c8c069f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Theorems.Thm_GlobalTheory_GlobalLift_weilIs_iff_commIsOf
import Theorems.Thm_GlobalTheory_GlobalLift_exists_symLift_pull
import Theorems.Thm_GlobalTheory_GlobalLift_exists_symLift_empty
import Theorems.Thm_GlobalTheory_GlobalLift_exists_section
import Theorems.Thm_GlobalTheory_CommPairing_exists_pull
import Theorems.Thm_GlobalTheory_CommutatorPairing_exists_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalLift
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ), Odd k → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L k (overRes V), SymLift P.A P.L k k (overResι V ≫ x) θ) ∧ ∀ θ θ' : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ → SymLift P.A P.L k k x θ' → LB.Gen.Corr P.L _ _ _ _ θ.φ θ'.φ) → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ)) := by
  intro hG hlift hsym S P k T
  refine ⟨weilIs_iff_commIsOf hG P.isAb P.isLB, fun x hx hT => ?_⟩
  rcases isEmpty_or_nonempty T.left with he | ⟨⟨p⟩⟩
  · obtain ⟨θ, H⟩ := exists_symLift_empty (k := (k : ℤ)) P.isLB k x
    exact ⟨θ, H.pt_eq, fun _ => H⟩
  by_cases hk : Odd k
  · obtain ⟨V, hp, θ, H⟩ := (hsym S P k hk T x hx).1 p
    obtain ⟨h, e⟩ := exists_section hp
    obtain ⟨θ', H'⟩ := exists_symLift_pull P.isLB h H
    rw [← Category.assoc, e, Category.id_comp] at H'
    exact ⟨θ', H'.pt_eq, fun _ => H'⟩
  · obtain ⟨V, hp, θ, H⟩ := hlift S P k T x hx p
    obtain ⟨h, e⟩ := exists_section hp
    obtain ⟨θ', e', -⟩ := CommPairing.exists_pull P.isLB h θ
    rw [H, ← Category.assoc, e, Category.id_comp] at e'
    exact ⟨θ', e', fun h => absurd h hk⟩
end GlobalTheory
