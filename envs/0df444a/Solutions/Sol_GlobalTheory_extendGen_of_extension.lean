-- Prove2me | solution 1 for GlobalTheory.extendGen_of_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:53:53.370047+00:00
-- url     : https://prove2.me/submissions/8e252042-1778-4a24-abb4-9a0ffff49a08

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalExtendsAndExtendGen
import Theorems.Thm_GlobalTheory_CubeExtension_eSec_comp
import Theorems.Thm_GlobalTheory_CubeExtension_pullGen_genPull
import Theorems.Thm_GlobalTheory_existsUnique_genPull_eq
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_genPull


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
    (h₂ : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t)) : Semi.extendGenSt.{0} := by
  intro V _ _ _ K _ _ _ G _ _ _ _ _ _ eA heA N r hr hc
  obtain ⟨c, ⟨hc₁, hc₂⟩, hu⟩ := h₂ V K G.left G.left G.hom (eSec G) inferInstance
    (h₁ _ _ _ inferInstance inferInstance) (eSec_comp _) eA heA N.L N.isLB PUnit (fun _ => 𝟙 _)
    (fun _ => 1) r N.rig hr N.rigGen hc
  obtain ⟨r', ⟨h₃, h₄⟩, hu'⟩ := existsUnique_genPull_eq (𝟙 G.left)
    (fun _ => Function.bijective_id) N.L c hc₁
  refine ⟨r', ⟨h₃, ?_⟩, fun r'' ⟨h₅, h₆⟩ => hu' r'' ⟨h₅, hu _ ⟨LB.isGen_genPull _ _ h₅ _, ?_⟩⟩⟩
  · rw [← h₄, pullGen_genPull] at hc₂
    exact hc₂
  · rw [pullGen_genPull]
    exact h₆
end GlobalTheory
