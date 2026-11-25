-- Prove2me | solution 1 for GlobalTheory.GenExtend.existsUnique_gen_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:55:26.82537+00:00
-- url     : https://prove2.me/submissions/5c9800d4-a2d5-484a-8942-47b17504b066

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Theorems.Thm_GlobalTheory_GenExtend_res_pullU_eq_of_corr
import Theorems.Thm_GlobalTheory_DvrModel_existsUnique_isUnit_appLE_eq
import Theorems.Thm_GlobalTheory_DvrModel_wchart_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtend
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DvrModel
namespace GlobalTheory.GenExtend
theorem _root_.solution :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t := by
  intro V _ _ _ K _ _ _ H X p e hsm hgi he eK heK L hL I _ φ ε t ρ ht hρ hc
  have hK := IsPullback.of_hasPullback p (etaK V K)
  have hs := IsPullback.of_hasPullback p
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := isIntegral_of_geometricallyIntegral hK
  have := isIntegral_of_geometricallyIntegral hs
  have hcomp : ∀ i, eK ≫ pullback.fst p (etaK V K) ≫ φ i = etaK V K ≫ e ≫ φ i := fun i => by
    rw [← Category.assoc, heK, Category.assoc]
  obtain ⟨a₀, h₀⟩ := LB.mem_of_cover (LB.isLB_linComb hL (fun i => e ≫ φ i) ε)
    (IsLocalRing.closedPoint V)
  have hA' : LB.wchart L (fun i => etaK V K ≫ e ≫ φ i) a₀ =
      etaK V K ⁻¹ᵁ LB.wchart L (fun i => e ≫ φ i) a₀ := wchart_comp L _ _ _
  have hA'' : LB.wchart L (fun i => etaK V K ≫ e ≫ φ i) a₀ ≤
      eK ⁻¹ᵁ LB.wchart L (fun i => pullback.fst p (etaK V K) ≫ φ i) a₀ := by
    rw [← wchart_comp, funext hcomp]
  obtain ⟨s, ⟨hsu, hsc, hsr⟩, huniq⟩ := existsUnique_isUnit_appLE_eq hK hs
    (U := LB.wchart L φ) (g := fun a b ↦ LB.lcg L φ ε a b)
    (W := LB.wchart L fun k ↦ pullback.fst p (etaK V K) ≫ φ k)
    (wchart_comp L _ φ) (LB.mem_of_cover (LB.isLB_linComb hL φ ε)) (fun a b ↦ Units.isUnit _)
    (r := fun a ↦ LB.ts t a)
    (fun a b ↦ by
      have := congrArg Units.val ((LB.isGen_iff L t).1 ht a b)
      rw [LB.lcg_comp] at this
      exact this)
    (fun a ↦ Units.isUnit _) he heK (a₀ := a₀) (A := LB.wchart L (fun i => e ≫ φ i) a₀) h₀
    (wchart_comp L e φ a₀).le hA' hA'' (LB.ts ρ a₀).isUnit
    (res_pullU_eq_of_corr hL ht hρ eK (etaK V K) hcomp hc a₀ hA'' hA'.le)
  refine ⟨⟨fun a ↦ (hsu a).unit⟩, ⟨fun a b ↦ Units.ext (hsc a b), ?_⟩, ?_⟩
  · exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (hsr a))
  · rintro ⟨r'⟩ ⟨h₁, h₂⟩
    have := huniq (fun a ↦ (r' a).val) ⟨fun a ↦ Units.isUnit _,
      fun a b ↦ congrArg Units.val (h₁ a b), fun a ↦ congrArg (fun c ↦ (LB.ts c a).val) h₂⟩
    exact congrArg LB.Gen.mk (funext fun a ↦ Units.ext (congrFun this a))
end GlobalTheory.GenExtend
