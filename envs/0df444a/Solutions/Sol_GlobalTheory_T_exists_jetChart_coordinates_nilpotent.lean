-- Prove2me | solution 1 for GlobalTheory.T.exists_jetChart_coordinates_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:38.699844+00:00
-- url     : https://prove2.me/submissions/966ec65a-c118-439e-8055-6356682433b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetChartCoordinatesNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsJetChartCoordinatesNilpotentStatement
import Theorems.Thm_GlobalTheory_exists_jet_coordinates


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) → (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) → (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) → ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ → ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 → ∃ ψ : JetR R (Fin d) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin d) m ∧ y = spMap ψ ≫ x m := by
  first | exact @GlobalTheory.exists_jet_coordinates | exact GlobalTheory.exists_jet_coordinates | (intros; apply GlobalTheory.exists_jet_coordinates <;> assumption)
end _root_.GlobalTheory.T
