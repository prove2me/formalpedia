-- Prove2me | solution 1 for GlobalTheory.FamBaseChange.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:06:22.228564+00:00
-- url     : https://prove2.me/submissions/51ff4928-fedf-4c60-a9f6-3da08357b335

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntegralDegenerationFamilyBaseChangeExtensionFie
import Theorems.Thm_GlobalTheory_FamBaseChange_bc_prB
import Theorems.Thm_GlobalTheory_FamBaseChange_bc_tr_prB
import Theorems.Thm_GlobalTheory_FamBaseChange_uVal_bc
import Theorems.Thm_GlobalTheory_FamBaseChange_famMult_bc
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_of_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff


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
open GlobalTheory GlobalTheory.FamBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FamBaseChange
theorem _root_.solution : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (k : ℕ) (E : Fam D.toPre (FractionRing R) k) (g : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ θ : Fam D.toPre F k, ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (θ.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre F).left 1 := by
  intro hG R _ _ I D k E g hg F _ _
  have hL := D.toPre.P.isLB
  have e2 : ∀ χ, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)),
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval t ρ z J = sval (g χ) (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun χ => by
    have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB χ i) (DegPre.famε k)
        (DegPre.famφ D.toPre F χ) (DegPre.famε k) := fun U _ g =>
      Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
    obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ (g χ) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (SectionScalarValuation.sval_pullSec _ _ _ _ ρ z hJ)⟩
  choose t ht using e2
  refine ⟨⟨t, fun mu α u hu hc => ?_⟩, fun α => SectionScalarValuation.secScal_of_sval hL fun y J hJ => (ht α _ (𝟙 _) y J hJ).symm⟩
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e₃ := (gen_fe hG k mu α).2 u hu hc _ (𝟙 _) y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D.toPre) (F := FractionRing R) hG k mu α
  have e₄ := (secRel_iff hL _ _ _ _ _ _ _ _ _ u').1 (E.fe mu α u' hu' hc') _ (bc D.toPre F).left y J hJ
  rw [hv' u' hu' hc' _ (bc D.toPre F) y J hJ, uVal_bc, famMult_bc D.toPre F k α mu y hJ, ← e₃,
    ← SectionScalarValuation.secScal_sval (hg _) _ y hJ, ← SectionScalarValuation.secScal_sval (hg _) _ y hJ, ← Over.comp_left, bc_prB,
    Category.assoc, ← Over.comp_left, ← Over.comp_left, bc_tr_prB] at e₄
  rw [ht _ _ _ y J hJ, ht _ _ _ y J hJ, Category.id_comp, Category.id_comp]
  exact e₄
end GlobalTheory.FamBaseChange
