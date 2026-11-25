-- Prove2me | solution 1 for GlobalTheory.ThetaModelGroup.exists_hom_of_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:09:45.453885+00:00
-- url     : https://prove2.me/submissions/1b8b5102-9d12-414c-8b2a-c307e0b96e77

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LocallyOfFiniteTypeTensor
import Theorems.Thm_GlobalTheory_ThetaModelGroup_exists_regOn_div
import Theorems.Thm_GlobalTheory_ThetaModelGroup_exists_chart
import Theorems.Thm_P2M_GlobalTheory_ThetaModelGroup_valAt__eval__5710659469e1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaModelGroup
variable {X Y : Over (Sp ℂ)}
namespace GlobalTheory.ThetaModelGroup
theorem _root_.solution (H : PointCriterion) (h1 : IsReduced Y.left) (h2 : LocallyOfFiniteType Y.hom)
    {κ A : Type} [Finite κ] {D : κ → X.left.Opens} (hD : ⨆ c, D c = ⊤) (ex : A → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (θ : κ → A → ℂ)
    (hc : ∀ c, IsAffineOpen (D c) ∧ (∀ z, ⊤ ≤ (ex z).left ⁻¹ᵁ D c ↔ θ c z ≠ 0) ∧ ∃ r : κ → Γ(X.left, D c),
      (∀ c' z, θ c z ≠ 0 → valAt' (ex z).left (D c) (r c') = θ c' z / θ c z) ∧
      ∀ f : Γ(X.left, D c), ∃ F : MvPolynomial κ ℂ, f = MvPolynomial.eval₂ (RingHom.comp
        (X.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F)
    (G : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → A)
    (hG : ∀ y, ∃ l : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → ℂ, l y ≠ 0 ∧ ∀ c, RegAt y (fun y' => l y' * θ c (G y'))) :
    ∃ m : Y ⟶ X, ∀ y, y ≫ m = ex (G y) := by
  refine (H X Y h1 h2 (fun y => ex (G y)) fun y => ?_).exists
  obtain ⟨c, hcy⟩ := exists_chart hD (ex (G y))
  obtain ⟨ha, hm, r, hr, hF⟩ := hc c
  obtain ⟨l, hl, hR⟩ := hG y
  obtain ⟨U, hU, hne, hq⟩ := exists_regOn_div hR c (mul_ne_zero hl ((hm _).1 hcy))
  choose ρ hρ using hq
  refine ⟨U, D c, hU, ha, fun y' hy' => (hm _).2 (right_ne_zero_of_mul (hne y' hy')), fun φ => ?_⟩
  obtain ⟨F, rfl⟩ := hF φ
  refine ⟨MvPolynomial.eval₂ (RingHom.comp (Y.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ F, fun y' hy' => ?_⟩
  have h0 := right_ne_zero_of_mul (hne y' hy')
  rw [valAt'_eval₂ y' U hy', valAt'_eval₂ _ _ ((hm _).2 h0)]
  congr 2
  funext c'
  rw [hρ c' y' hy', hr c' _ h0]
  exact mul_div_mul_left _ _ (left_ne_zero_of_mul (hne y' hy'))
end GlobalTheory.ThetaModelGroup
