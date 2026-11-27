-- Prove2me | solution 1 for GlobalTheory.TorsionFormCompare.isPullGtF_self_of_isIdPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:31.628101+00:00
-- url     : https://prove2.me/submissions/ed82935b-24b9-41dd-b7ec-9f149b111075

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PullPointIdentityDegeneration
import Theorems.Thm_GlobalTheory_TorsionFormCompare_pmaps_self_of_tautological
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorsionFormCompare
namespace GlobalTheory.TorsionFormCompare
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hD : IsPullDeg (RingHom.id R) D D), IsIdPull hD → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g : GtPtF D F), IsPullGtF (RingHom.id R) hD F g g := by
  intro R _ _ D hD ⟨hx, he, hw⟩ F _ _ g
  refine ⟨by rw [he, Category.comp_id], fun χ => ?_⟩
  have key : ∀ χ' : D.X, χ = χ' → ∃ hψ : ∀ k : Fin 4,
      DegPre.gtφ D F g.b χ k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
        𝟙 _ ≫ DegPre.gtφ D F g.b χ' k,
    LB.Gen.Maps (LB.linCombIso hD.w _ DegPre.gtε) (g.s χ)
      (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) (𝟙 _) _
        DegPre.gtε _ hψ (g.s χ')) := by
    rintro _ rfl
    have hψ : ∀ k : Fin 4,
      DegPre.gtφ D F g.b χ k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
        𝟙 _ ≫ DegPre.gtφ D F g.b χ k := fun k => by rw [he, Category.comp_id, Category.id_comp]
    exact ⟨hψ, (maps_iff hD.w _ _ _ _ _ (𝟙 _) _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).2
      (pmaps_self_of_tautological he hD.w hw _ _ _ (g.isGen _))⟩
  exact key _ (hx χ).symm
end GlobalTheory.TorsionFormCompare
