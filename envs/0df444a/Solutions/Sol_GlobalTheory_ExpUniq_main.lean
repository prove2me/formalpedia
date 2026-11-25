-- Prove2me | solution 1 for GlobalTheory.ExpUniq.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:03.346458+00:00
-- url     : https://prove2.me/submissions/6ac6953e-16fa-49c0-9665-70f075584418

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsPullOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_PGAppEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntegralExpansionUniqueOfUniformization
import Theorems.Thm_GlobalTheory_ExtDiv_main
import Theorems.Thm_GlobalTheory_ThickDiv_main
import Theorems.Thm_GlobalTheory_expandsAt_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB
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
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ExpUniq
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ExpUniq
theorem _root_.solution : lemmaBSt.{0} → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (k : ℕ) (σ : H0 U.LG.L k) (f g : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.ExpandsAt e k σ f) → (∀ e, U.ExpandsAt e k σ g) → f = g := by
  intro hB V _ _ _ D A G _ _ U k σ f g hf hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.proper
  have := D.toPre.P.isAb.geomConnected
  let d : ∀ α : D.toPre.X, D.toPre.SecB k α := fun α => SecOps.secAdd (f α) (SecOps.secNeg (g α))
  have hd : ∀ α j, (d α).f j = (f α).f j - (g α).f j := fun α j => (sub_eq_add_neg _ _).symm
  have h0 : ∀ e, U.ExpandsAt e k SecOps.secZero d := fun e =>
    GlobalTheory.expandsAt_sub V _ D A G U e k σ σ SecOps.secZero f g d (fun j => (sub_self _).symm) hd (hf e) (hg e)
  funext α
  refine SecOps.sec_ext fun j => sub_eq_zero.1 ((hd α j).symm.trans ?_)
  refine hB V D.toPre.P.A _ (linComb_isLB _ D.toPre.P.isLB _ _) (d α) ϖ hϖ (fun i e => ?_) j
  obtain ⟨τ, hτ⟩ := (GlobalTheory.ExtDiv.main V ϖ hϖ D A G U e k α (d α)).1
    (WeightPf.weightIndep V _ D A G U e k SecOps.secZero d (fun _ => map_zero _) (h0 e) α)
  rw [hτ i, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine Dvd.dvd.mul_right ?_ _
  simp only [scal, pow_succ, map_mul, map_pow]
  exact Dvd.dvd.mul_right (dvd_refl _) _
end GlobalTheory.ExpUniq
