-- Prove2me | solution 1 for GlobalTheory.NilChart.existsUnique_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:33.863074+00:00
-- url     : https://prove2.me/submissions/56d84968-d6d5-425a-9613-fe021e335cdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueCoord
import Theorems.Thm_GlobalTheory_NilChart_coord_unique
import Theorems.Thm_GlobalTheory_NilChart_coord_exists

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilChart
open SqZero
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ}
  {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
  (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
  (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
  (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
include hG hv hx₁ hx₂ hx₃
namespace GlobalTheory.NilChart
theorem _root_.solution {m : ℕ} {N : Ideal B} (hN : N ^ (m + 1) = ⊥) (y : sp (R₀ := R) B ⟶ G)
    (hy : spMap (Ideal.Quotient.mkₐ R N) ≫ y = 1) : ∃! ψ : JetR R (Fin d) m →ₐ[R] B, spMap ψ ≫ x m = y := by
  obtain ⟨ψ, h⟩ := coord_exists hG hv hx₁ hx₂ hx₃ hN y hy
  exact ⟨ψ, h, fun ψ' h' => coord_unique hG hv hx₁ hx₂ hx₃ _ _ (h'.trans h.symm)⟩
end GlobalTheory.NilChart
