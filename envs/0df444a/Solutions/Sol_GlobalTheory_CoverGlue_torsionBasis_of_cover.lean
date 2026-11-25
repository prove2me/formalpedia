-- Prove2me | solution 1 for GlobalTheory.CoverGlue.torsionBasis_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:25:26.475838+00:00
-- url     : https://prove2.me/submissions/d887cd68-5cf0-44da-a3f2-d4ddc95db0d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionBasisGeometricFibresOfOpenCover
import Theorems.Thm_GlobalTheory_CoverGlue_exists_fac_field
import Theorems.Thm_GlobalTheory_CoverGlue_map_linComb
import Theorems.Thm_GlobalTheory_CoverGlue_exists_lift
import Theorems.Thm_GlobalTheory_CoverGlue_lift_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.CoverGlue
private theorem exists_bijective_monoidHom_points_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {ψ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f ψ) (T : Over S') :
    ∃ ρ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G),
      (∀ z, (ρ z).left = z.left ≫ ψ) ∧ Function.Injective ρ ∧ Function.Surjective ρ := by
  have hw : ∀ z : T ⟶ G', (z.left ≫ ψ) ≫ G.hom = T.hom ≫ f := fun z => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w z]
  refine ⟨MonoidHom.mk' (fun z => Over.homMk (z.left ≫ ψ) (hw z)) (fun a b => ?_), fun _ => rfl, ?_, ?_⟩
  · exact Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm
  · intro a b hab
    exact lift_ext h.1 (congrArg CommaMorphism.left hab)
  · intro y
    obtain ⟨z, hz⟩ := exists_lift h.1 y
    exact ⟨z, Over.OverMorphism.ext hz.symm⟩
end GlobalTheory.CoverGlue
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue
namespace GlobalTheory.CoverGlue
theorem _root_.solution : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (g k : ℕ) (P : Fin (2 * g) → (Out.baseOver S ⟶ A)) (Q : ∀ i, Fin (2 * g) → (Out.baseOver (U i).toScheme ⟶ G i)), (∀ i l, (Q i l).left ≫ ψ i = (U i).ι ≫ (P l).left) → (∀ i (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ (U i).toScheme) (y : Over.mk x ⟶ G i), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) (fun l => (c l).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ P l) (fun l => (c l).val) = y := by
  intro S I U A _ G _ ψ hU hψ _ _ g k P Q hPQ hQ K _ _ x y hy
  obtain ⟨i, x', rfl⟩ := exists_fac_field hU K x
  obtain ⟨ρ, hρ, hinj, hsurj⟩ := exists_bijective_monoidHom_points_of_isGrpPullback (hψ i) (Over.mk x')
  obtain ⟨y', rfl⟩ := hsurj y
  have hpt : ∀ l, ρ ((Over.homMk x' (by simp) : Over.mk x' ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) =
      (Over.homMk (x' ≫ (U i).ι) (by simp) : Over.mk (x' ≫ (U i).ι) ⟶ Out.baseOver S) ≫ P l := by
    intro l
    apply Over.OverMorphism.ext
    rw [hρ]
    simp [hPQ]
  have hy' : y' ^ k = 1 := hinj (by rw [map_pow, map_one]; exact hy)
  obtain ⟨c, hc, huniq⟩ := hQ i K x' y' hy'
  refine ⟨c, ?_, fun c' hc' => huniq c' (hinj ?_)⟩
  · rw [← hc, map_linComb]
    simp only [hpt]
  · rw [map_linComb]
    simp only [hpt]
    exact hc'
end GlobalTheory.CoverGlue
