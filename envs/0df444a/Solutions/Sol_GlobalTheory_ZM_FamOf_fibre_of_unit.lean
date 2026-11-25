-- Prove2me | solution 1 for GlobalTheory.ZM.FamOf.fibre_of_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:32.285783+00:00
-- url     : https://prove2.me/submissions/2793b055-270a-4c0d-9b59-eb6d85da3680

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSectionsFam
import Theorems.Thm_GlobalTheory_ZM_FamOf_snd_unitInv
import Theorems.Thm_GlobalTheory_ZM_FamOf_pt_unitInv
import Theorems.Thm_GlobalTheory_ZM_FamOf_isPullback_unitInv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_chartPull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.FamOf
namespace GlobalTheory.ZM.FamOf
theorem _root_.solution {R K σ : Type} [CommRing R] [CommRing K] {x : R →+* K} {Z : Scheme.{0}} {s : Z ⟶ Sp R} {M : LB Z}
    {th : σ → M.Sec} (A : Over (Sp K)) (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k)
    (th' : σ → (Out.LPow A L a (Over.mk (𝟙 (Sp K)))).Sec) (φ₀ : (Over.mk (𝟙 (Sp K)) ⊗ A).left ⟶ Z)
    (h1 : IsPullback φ₀ (fst (Over.mk (𝟙 (Sp K))) A).left s (spMap x))
    (h2 : LBIso (Out.LPow A L a (Over.mk (𝟙 (Sp K)))) (M.pull φ₀))
    (h3 : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
      SecCoord _ th' y w ↔ SecCoord M th (y ≫ φ₀) w) :
    ∃ φ : A.left ⟶ Z, IsPullback φ A.hom s (spMap x) ∧
      (∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
        SecCoord _ th' y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) A).left ≫ φ) w) ∧
      LBIso (lbPow L k) (M.pull φ) ∧
      ∀ (z : Over.mk (𝟙 (Sp K)) ⟶ A) (w : σ → K), SecCoord _ th' (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left w →
        SecCoord M th (z.left ≫ φ) w := by
  refine ⟨(unitInv A).left ≫ φ₀, ?_, fun T _ y w => ?_, ?_, fun z w hz => ?_⟩
  · have := (isPullback_unitInv A).paste_horiz h1
    rwa [Category.id_comp] at this
  · have e : (snd (Over.mk (𝟙 (Sp K))) A).left ≫ (unitInv A).left ≫ φ₀ = φ₀ := by
      rw [← Category.assoc, snd_unitInv, Category.id_comp]
    rw [e]
    exact h3 T y w
  · exact LBIso.chartPull (chartPullUnit A L k a ha) (chartPullSame M _ _ _ (unitInv A).left fun _ => rfl) h2
  · have e : z.left ≫ (unitInv A).left ≫ φ₀ = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left ≫ φ₀ := by
      rw [← Category.assoc, pt_unitInv]
    rw [e]
    exact (h3 K _ w).1 hz
end GlobalTheory.ZM.FamOf
