-- Prove2me | solution 1 for GlobalTheory.torsion_point_fixed_of_generic_sections_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:06.681189+00:00
-- url     : https://prove2.me/submissions/b080b7df-0070-4693-b63f-ff23731bc417

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDominantGeometricPointOfIsPreimmersion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionPointFixedOfGenericSectionsFixed
import Theorems.Thm_GlobalTheory_comp_eq_of_extending_section
import Theorems.Thm_GlobalTheory_GrpTangent_etale_torsion
import Theorems.Thm_GlobalTheory_GrpTangent_isPullback_torsion
import Theorems.Thm_GlobalTheory_exists_opens_isOpenImmersion_extending_section


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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → ∀ (G : Over X) [GrpObj G] (n : ℕ) (I : Type) [Finite I] (σ : I → (Over.mk j ⟶ G)) (r : X ⟶ X) (r₀ : U ⟶ U) (φ : G.left ⟶ G.left), IsSemiAbelian G → IsUnit (n : Γ(X, ⊤)) → (∀ i, σ i ^ n = 1) → (∀ (k : Type) [Field k] [IsAlgClosed k] (u : Sp k ⟶ U) (y : Over.mk (u ≫ j) ⟶ G), y ^ n = 1 → ∃ i, y.left = u ≫ (σ i).left) → r₀ ≫ j = j ≫ r → IsIso r → IsGrpPullback G G r φ → (∀ i, (σ i).left ≫ φ = r₀ ≫ (σ i).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (y : Over.mk x ⟶ G), x ≫ r = x → y ^ n = 1 → y.left ≫ φ = y.left := by
  intro X U _ j hN hj₁ hj₂ hj₃ hj₄ G _ n I _ σ r r₀ φ hG hn hσ hgeo hr _ hφ hσφ k _ _ x y hx hy
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := IsNormalScheme.of_pred hN
  have hex : ∀ {T : Over X} (z : T ⟶ G), z ^ n = 1 →
      ∃ z' : T ⟶ torsion G n, z' ≫ torsion.ι G n = z := fun z hz =>
    ⟨pullback.lift z (toUnit _) (by rw [GrpTangent.comp_mulN, hz, Hom.one_def]),
      pullback.lift_fst _ _ _⟩
  have hι : torsion.ι G n ^ n = 1 := by
    rw [← GrpTangent.comp_mulN, Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ _) (toUnit_unique _ _))
  have hcl : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by
      rw [Over.w]; exact inferInstanceAs (IsClosedImmersion (𝟙 X))
    exact IsClosedImmersion.of_comp _ G.hom
  have : IsClosedImmersion (torsion.ι G n).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (GrpTangent.isPullback_torsion G n).flip hcl
  have hsep : IsSeparated (torsion G n).hom := by
    rw [← Over.w (torsion.ι G n)]; infer_instance
  choose τ hτ using fun i => hex (σ i) (hσ i)
  have hτ' : ∀ i, (τ i).left ≫ (torsion.ι G n).left = (σ i).left := fun i =>
    congrArg Over.Hom.left (hτ i)
  obtain ⟨y', rfl⟩ := hex y hy
  obtain ⟨i, W, hyW, hW, he⟩ := exists_opens_isOpenImmersion_extending_section X U j hN hj₁ hj₂
    hj₃ hj₄ _ (torsion G n).hom I (fun i => (τ i).left) (GrpTangent.etale_torsion G hn) hsep
    (fun i => Over.w (τ i)) (fun k _ _ u z hz => by
      obtain ⟨i, hi⟩ := hgeo k u (Over.homMk z hz ≫ torsion.ι G n)
        (by rw [← comp_pow, hι, comp_one])
      refine ⟨i, ?_⟩
      rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτ']
      exact hi) (y'.left (IsLocalRing.closedPoint k))
  have hrange : Set.range y'.left ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim (α := PrimeSpectrum k) z (IsLocalRing.closedPoint k)]
    exact hyW
  have hw := IsOpenImmersion.lift_fac W.ι y'.left hrange
  have hq : (W.ι ≫ (torsion.ι G n).left) ≫ G.hom = W.ι ≫ (torsion G n).hom := by
    rw [Category.assoc, Over.w]
  have : IsOpenImmersion ((W.ι ≫ (torsion.ι G n).left) ≫ G.hom) := hq ▸ hW
  have hyx : y'.left ≫ (torsion G n).hom = x := Over.w y'
  have := comp_eq_of_extending_section j G.hom (W.ι ≫ (torsion.ι G n).left) (σ i).left (by
      have h := congrArg (pullback.lift (pullback.fst ((W.ι ≫ (torsion.ι G n).left) ≫ G.hom) j)
        (pullback.snd _ j) (by rw [← hq]; exact pullback.condition) ≫ · ≫ (torsion.ι G n).left) he
      simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc, hτ'] using h)
    r r₀ φ hr hφ.1.w (hσφ i) (IsOpenImmersion.lift W.ι y'.left hrange)
    (by rw [hq, Category.assoc, reassoc_of% hw, reassoc_of% hw, reassoc_of% hyx, hyx, hx])
  simpa only [Category.assoc, reassoc_of% hw, Over.comp_left] using this
end GlobalTheory
