-- Prove2me | solution 1 for GlobalTheory.symLift_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:17:25.498804+00:00
-- url     : https://prove2.me/submissions/e8318b70-0f64-4f02-bf58-5a4026190953

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Theorems.Thm_P2M_GlobalTheory_SymLiftOdd_comp_pow__fae19791c0f2
import Theorems.Thm_GlobalTheory_SymLiftOdd_exists_symLift
import Theorems.Thm_GlobalTheory_SymLiftOdd_symLift_unique

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
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ), Odd k → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L k (overRes V), SymLift P.A P.L k k (overResι V ≫ x) θ) ∧ ∀ θ θ' : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ → SymLift P.A P.L k k x θ' → LB.Gen.Corr P.L _ _ _ _ θ.φ θ'.φ) ∧ SymLiftSt := by
  intro hG hlift hneg
  have main : ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ), Odd k → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 →
      (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
        ∃ θ : ThetaGrp P.A P.L k (overRes V), SymLift P.A P.L k k (overResι V ≫ x) θ) ∧
      ∀ θ θ' : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ → SymLift P.A P.L k k x θ' →
        LB.Gen.Corr P.L _ _ _ _ θ.φ θ'.φ := by
    intro S P k hk T x hx
    refine ⟨fun p => ?_, fun θ θ' => SymLiftOdd.symLift_unique hG P.isAb P.isLB hk θ θ'⟩
    obtain ⟨V, hV, θ, hθ⟩ := hlift S P k T x hx p
    obtain ⟨nu, hnu⟩ := hneg S P k (overRes V)
    exact ⟨V, hV, SymLiftOdd.exists_symLift hG P.isAb P.isLB hk
      (by rw [← SymLiftOdd.comp_pow', hx, MonObj.comp_one]) θ hθ hnu⟩
  exact ⟨main, fun S _ P k hk _ => main S P k hk⟩
end GlobalTheory
