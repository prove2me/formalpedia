-- Prove2me | solution 1 for GlobalTheory.T.jetPoint_add_sqZero_eq_prod_mul_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:39.653809+00:00
-- url     : https://prove2.me/submissions/de2e4609-f0e7-47b6-a5ad-b3c5441e09da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangentStatement
import Theorems.Thm_GlobalTheory_jet_add_sqZero_eq_prod_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (J : Ideal A), J * RingHom.ker aug = ⊥ → J ≤ RingHom.ker aug → ∀ (m : ℕ) (ψ ψ' : JetR R (Fin d) m →ₐ[R] A), aug.comp ψ = jetAug R (Fin d) m → aug.comp ψ' = jetAug R (Fin d) m → ∀ e : Fin d → (DualNumber R →ₐ[R] A), (∀ j, e j (TrivSqZeroExt.inr 1) ∈ J) → (∀ j, ψ' (zR m j) = ψ (zR m j) + e j (TrivSqZeroExt.inr 1)) → spMap ψ' ≫ x m = (∏ j, (spMap (e j) ≫ v j : sp (R₀ := R) A ⟶ G)) * (spMap ψ ≫ x m) := by
  first | exact @GlobalTheory.jet_add_sqZero_eq_prod_mul | exact GlobalTheory.jet_add_sqZero_eq_prod_mul | (intros; apply GlobalTheory.jet_add_sqZero_eq_prod_mul <;> assumption)
end _root_.GlobalTheory.T
