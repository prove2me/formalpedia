-- Prove2me | solution 1 for GlobalTheory.cubical_extends_of_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:00.662898+00:00
-- url     : https://prove2.me/submissions/e1e2026a-8a4d-42d0-a1f2-d10b6d5bc814

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalExtendsAndExtendGen
import Theorems.Thm_GlobalTheory_CubeExtension_smooth_tensor
import Theorems.Thm_GlobalTheory_CubeExtension_geometricallyConnected_tensor
import Theorems.Thm_GlobalTheory_CubeExtension_eSec_comp
import Theorems.Thm_GlobalTheory_CubeExtension_formEq_origin
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_oneGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CubeExtension
namespace GlobalTheory
theorem _root_.solution
    (h₁ : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f))
    (h₂ : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t)) : Semi.cubical_extendsSt.{0} := by
  intro V _ _ _ K _ _ _ G _ _ _ _ _ _ eA heA L t hc ht
  have s₂ := smooth_tensor G G
  have s₃ := smooth_tensor G (G ⊗ G)
  have c₂ := geometricallyConnected_tensor G G
  have c₃ := geometricallyConnected_tensor G (G ⊗ G)
  obtain ⟨ρ, hρ, hv⟩ := exists_gen L.isLB (formEq_origin G) (LB.oneGen L.L) (LB.isGen_oneGen L.L)
  refine h₂ V K (G3 G).left G.left (G3 G).hom (eSec (G3 G)) s₃ (h₁ _ _ _ s₃ c₃) (eSec_comp _) eA heA
    L.L L.isLB thK (thφ G (x3 G)) thε t ρ ht hρ (corr_of_val L.isLB fun y J hJ => ?_)
  refine (val_corr hJ hc (𝟙 _)).trans ((val_one _).trans (Eq.symm ?_))
  exact (val_pull hJ ρ _ _).trans ((hv _ _ y J hJ).trans (val_one _))
end GlobalTheory
