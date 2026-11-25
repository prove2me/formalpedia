-- Prove2me | solution 1 for GlobalTheory.FinrankGrowthBounds.finrank_sections_lineBundlePow_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:45.316172+00:00
-- url     : https://prove2.me/submissions/5086c8d2-4989-4169-b48e-475d1b0f2324

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow
import Theorems.Thm_GlobalTheory_FinrankGrowthBounds_eq_pow_of_growth
import Theorems.Thm_GlobalTheory_FinrankGrowthBounds_finrank_eq_mul
import Theorems.Thm_GlobalTheory_FinrankGrowthBounds_mulSec_injective
import Theorems.Thm_GlobalTheory_FinrankGrowthBounds_isField_base

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinrankGrowthBounds
open Filter Topology
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S)
namespace GlobalTheory.FinrankGrowthBounds
theorem _root_.solution : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n j : ℕ), (n : K) ≠ 0 → 1 ≤ j → Nonempty (SecM P.A P.L ((n ^ 2 * j : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K))) ≃ₗ[Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)] ({x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ n = 1} → SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K)))))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (∀ j : ℕ, Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) ∧ ∃ N c C : ℕ, 1 ≤ N ∧ 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ P.g ≤ c * Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ∧ Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L ((N * t : ℕ) : ℤ) (baseOver (Spec (CommRingCat.of K)))) ≤ C * t ^ P.g) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → GlobalSectionsRankAlgClosed := by
  intro hint hone hrel hgrow _ K _ _ P
  obtain ⟨hfin, N, c, C, hN, -, hgr⟩ := hgrow K P
  have hF := isField_base K
  haveI : Nontrivial Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) := hF.nontrivial
  haveI : GeometricallyIntegral P.A.hom := hint _ _ _ P.isAb.smooth P.isAb.geomConnected
  haveI : IsIntegral (baseOver (Spec (CommRingCat.of K)) ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral (f := P.A.hom) _ _ _
      (IsPullback.of_hasPullback (𝟙 (Spec (CommRingCat.of K))) P.A.hom).flip
  have h1 := hone K P
  haveI : Nontrivial (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) :=
    Module.nontrivial_of_finrank_eq_succ h1
  obtain ⟨s, hs⟩ := exists_ne (0 : SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K))))
  intro n hn
  refine eq_pow_of_growth (fun j : ℕ => Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
      (SecM P.A P.L (j : ℤ) (baseOver (Spec (CommRingCat.of K))))) P.g (fun m => (m : K) ≠ 0)
      ?_ (by simp) h1 ?_ ?_ N c C hN hgr n hn
  · intro m
    by_cases hm : (m : K) = 0
    · right
      simp [hm]
    · exact Or.inl hm
  · refine monotone_nat_of_le_succ fun j => ?_
    haveI : Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
      (SecM P.A P.L ((j : ℤ) + 1) (baseOver (Spec (CommRingCat.of K)))) := hfin (j + 1)
    exact LinearMap.finrank_le_finrank_of_injective (mulSec_injective P.A P.L _ (j : ℤ) 1 s hs)
  · intro m j hm hj
    obtain ⟨e⟩ := hrel K P m 1 hm le_rfl
    obtain ⟨e'⟩ := hrel K P m j hm hj
    rw [Nat.mul_one] at e
    haveI := hfin (m ^ 2)
    haveI := hfin j
    exact finrank_eq_mul hF h1 e e'
end GlobalTheory.FinrankGrowthBounds
