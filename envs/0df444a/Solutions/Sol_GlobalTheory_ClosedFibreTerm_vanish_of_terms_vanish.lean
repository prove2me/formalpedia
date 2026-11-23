-- Prove2me | solution 1 for GlobalTheory.ClosedFibreTerm.vanish_of_terms_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:23.680578+00:00
-- url     : https://prove2.me/submissions/0ffb7eea-9d0a-4c0c-b02a-9da49ded5ec6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_PGAppEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_VanishOfTermsVanish
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_expandsAt_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gs_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_exists_chart


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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (h : U.ExpandsAt e k σ f)
    (h0 : ∀ α j, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) (j) :
    ((fstG I e G).left.app _).hom (σ.f j) = 0 := by
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  refine fn_ext fun y hy => ?_
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have H := (hS _ (𝟙 _) y J hJ).2 jL (Set.mem_iInter.1 hy 0)
  have hz : ∀ α, sval (f α) (𝟙 _ ≫ pGl U e) y J = 0 := fun α => by
    have m := hJ.mem (D.toPre.famφB α) (𝟙 _ ≫ pGl U e)
    exact (gs_pull (𝟙 _) _ y _ m _).symm.trans ((congrArg (gs (𝟙 _) y _) (h0 α _)).trans (gs_zero (𝟙 _) y _ m))
  rw [Finset.sum_eq_zero fun α _ => by rw [hz α, zero_mul]] at H
  exact (gs_pull (𝟙 _) _ y _ hy _).trans (((Units.mul_right_eq_zero _).1 H).trans (gs_zero (𝟙 _) y _ hy).symm)
end GlobalTheory.ClosedFibreTerm
