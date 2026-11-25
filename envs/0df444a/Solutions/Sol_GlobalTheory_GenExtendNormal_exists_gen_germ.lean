-- Prove2me | solution 1 for GlobalTheory.GenExtendNormal.exists_gen_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:37:10.208446+00:00
-- url     : https://prove2.me/submissions/0ca11047-f5af-408c-81cd-314392353301

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Theorems.Thm_GlobalTheory_DvrModel_wchart_comp
import Theorems.Thm_GlobalTheory_GenExtend_existsUnique_gen_extend
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtendNormal
open GlobalTheory.DvrModel
namespace GlobalTheory.GenExtendNormal
theorem _root_.solution (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] {H X : Scheme.{0}}
    (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H) (hs : Smooth p)
    (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _)
    (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K))
    (heK : eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e) {L : LB X} (hL : L.IsLB)
    {I : Type} [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ)
    (ψ : I → (pullback p (etaK V K) ⟶ X)) (hψ : ψ = fun i ↦ pullback.fst p (etaK V K) ≫ φ i)
    (χ : I → (Spec (CommRingCat.of V) ⟶ X)) (hχ : χ = fun i ↦ e ≫ φ i)
    (t : LB.Gen (LB.LinComb L ψ ε)) (ρ : LB.Gen (LB.LinComb L χ ε)) (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K))) :
    ∃ c : LB.Gen (LB.LinComb L φ ε), ∀ z a, pullback.fst p (etaK V K) z ∈ LB.wchart L φ a →
      gm (pullback.fst p (etaK V K)) z (LB.wchart L φ a) (c.s a) =
        gm (𝟙 _) z (LB.wchart L ψ a) (t.s a) := by
  subst hψ hχ
  obtain ⟨c, ⟨-, rfl⟩, -⟩ := GlobalTheory.GenExtend.existsUnique_gen_extend V K H X p e hs hg he eK heK L hL
    I φ ε t ρ ht hρ hc
  refine ⟨c, fun z a hz ↦ ?_⟩
  have hm : (𝟙 _ : pullback p (etaK V K) ⟶ _) z ∈
      LB.wchart L (fun i ↦ pullback.fst p (etaK V K) ≫ φ i) a := (wchart_comp L _ φ a).ge hz
  exact ((gm_res _ z _ hm _).trans ((gm_pull _ _ z _ hz _).trans (by rw [Category.id_comp]; rfl))).symm
end GlobalTheory.GenExtendNormal
