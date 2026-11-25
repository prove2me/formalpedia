-- Prove2me | solution 1 for GlobalTheory.exists_fam_of_isPullDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:28:53.774502+00:00
-- url     : https://prove2.me/submissions/32777cde-a6e3-4cf2-a972-9f3b109c07b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFamOfIsPullDeg
import Theorems.Thm_GlobalTheory_FamPull_prod_famB
import Theorems.Thm_GlobalTheory_FamPull_famFE_iff
import Theorems.Thm_GlobalTheory_FamPull_fe_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_secScal_of_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_SectionScalarValuation_sval_pullSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_fam
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
namespace GlobalTheory
theorem _root_.solution : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (k : ℕ) (F : Fam D (FractionRing R) k) (f : ∀ α, D.SecB k α) (f' : ∀ α, D'.SecB k α), (∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F.s α) (D.famφB α) (DegPre.famε k) (f α) (DegPre.prB D (FractionRing R)).left 1) → (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) z (LB.wchart D.P.L (D.famφB (hD.xe x)) p) ((f (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' x).f q))) → ∃ F' : Fam D' (FractionRing R') k, (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) (F'.s α) (D'.famφB α) (DegPre.famε k) (f' α) (DegPre.prB D' (FractionRing R')).left 1) := by
  intro hG R R' _ _ _ _ φ D D' hD k F f f' hs hf
  have ex : ∀ α, ∃ s : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k)),
      GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) s (D'.famφB α) (DegPre.famε k) (f' α)
        (DegPre.prB D' (FractionRing R')).left 1 := fun α => by
    obtain ⟨s, hs⟩ := exists_sec D'.P.isLB (φ' := DegPre.famφ D' (FractionRing R') α) (ε' := DegPre.famε k)
      (fun U _ h => by
        have p := prod_fam D' (FractionRing R') (𝟙 _) α k h
        simp only [Over.id_left, Category.id_comp] at p
        exact (FamPull.prod_famB D' _ α k h).trans p.symm)
      (pullSec D'.P.L _ _ (f' α) (DegPre.prB D' (FractionRing R')).left)
    exact ⟨s, secScal_of_sval D'.P.isLB fun y J hJ => ((hs _ _ y J hJ).trans (sval_pullSec _ _ _ _ _ y hJ)).symm⟩
  choose s hs' using ex
  refine ⟨⟨s, (FamPull.famFE_iff hG s f' hs').2 fun mu α T ρ z J hJ => ?_⟩, hs'⟩
  exact FamPull.fe_pull hG hD F f f' hs hf mu α (Over.homMk ((ρ ≫ fst _ _).left ≫ jFK (R := R') (FractionRing R'))
    ((Category.assoc _ _ _).trans (Over.w (ρ ≫ fst _ _)))) _ hJ
end GlobalTheory
