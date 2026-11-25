-- Prove2me | solution 1 for GlobalTheory.ClosedFibreTerm.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:04:49.925803+00:00
-- url     : https://prove2.me/submissions/66474a58-2844-4947-ad89-97b042275cbf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_PGAppEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_VanishOfTermsVanish
import Theorems.Thm_GlobalTheory_ClosedFibreTerm_vanish_of_terms_vanish
import Theorems.Thm_GlobalTheory_ExtDiv_main
import Theorems.Thm_GlobalTheory_ThickDiv_main
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_weightIndep


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ClosedFibreTerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ClosedFibreTerm
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (σ : H0 U.LG.L 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), U.ExpandsAt 0 1 σ g → (∀ χ, χ ≠ 0 → ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom ϖ (g χ) g') → ((∃ j, ((fstG (maximalIdeal V) 0 G).left.app _).hom (σ.f j) ≠ 0) ↔ ¬ ∃ g' : D.toPre.SecB 1 0, SecIsMul D.toPre.P.A.hom ϖ (g 0) g') := by
  intro V _ _ _ ϖ hϖ D A G _ _ U σ g hE hχ
  have Q : ∀ α : D.toPre.X, (∀ j, ((U.gt 0).pG.left.app _).hom ((g α).f j) = 0) ↔
      ∃ g' : D.toPre.SecB 1 α, SecIsMul D.toPre.P.A.hom ϖ (g α) g' := fun α => by
    have := GlobalTheory.ExtDiv.main V ϖ hϖ D A G U 0 1 α (g α)
    have hp : ϖ ^ (0 + 1) = ϖ := pow_one ϖ
    rwa [hp] at this
  rw [← not_forall]
  refine not_congr ⟨fun h => (Q 0).1 (WeightPf.weightIndep V _ D A G U 0 1 σ g h hE 0), fun h => ?_⟩
  refine vanish_of_terms_vanish U 0 1 σ g hE fun α => (Q α).2 ?_
  by_cases hα : α = 0
  · subst hα; exact h
  · exact hχ α hα
end GlobalTheory.ClosedFibreTerm
