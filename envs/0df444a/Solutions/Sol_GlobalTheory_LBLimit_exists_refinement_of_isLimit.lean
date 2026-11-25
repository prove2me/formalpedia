-- Prove2me | solution 1 for GlobalTheory.LBLimit.exists_refinement_of_isLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:22:12.020796+00:00
-- url     : https://prove2.me/submissions/bed57418-0df6-4a9c-8c2d-03a93a96a493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsRefinementOfIsLimit
import Theorems.Thm_GlobalTheory_LBLimit_isLB_of_germs
import Theorems.Thm_GlobalTheory_LBLimit_exists_unit_eq
import Theorems.Thm_GlobalTheory_FGAbove_exists_mem
import Theorems.Thm_GlobalTheory_exists_common_refinement
import Theorems.Thm_GlobalTheory_exists_pullU_eq
import Theorems.Thm_GlobalTheory_gm_id_pullU
import Theorems.Thm_GlobalTheory_gm_res_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.LBLimit
variable {I : Type} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, QuasiSeparatedSpace (D.obj i)]
include hc
namespace GlobalTheory.LBLimit
theorem _root_.solution [∀ i, CompactSpace (D.obj i)] (L : LB X) (hL : L.IsLB) :
    ∃ (j : I) (M : LB (D.obj j)) (e : M.ι → L.ι), M.IsLB ∧ (∀ a, π j ⁻¹ᵁ M.U a ≤ L.U (e a)) ∧
      ∀ a b (y : X), π j y ∈ M.U a → π j y ∈ M.U b →
        gm (π j) y _ (M.g a b) = gm (𝟙 X) y _ (L.g (e a) (e b)) := by
  have loc : ∀ x : X, ∃ (V : X.Opens) (p : L.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ L.U p := by
    intro x
    obtain ⟨p, hp⟩ := exists_chart hL x
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hp (L.U p).isOpen
    exact ⟨V, p, hV, hx, hle⟩
  choose W p hW hx hle using loc
  obtain ⟨i, σ, V, hcov, hV⟩ := Scheme.exists_isOpenCover_and_isAffine D _ hc W
    (top_le_iff.1 fun y _ => Opens.mem_iSup.2 ⟨y, hx y⟩) hW
  have hV' : ∀ a : σ, π i ⁻¹ᵁ V a ≤ L.U (p a) := fun a => (hV a).2.ge.trans (hle a)
  have cpt : ∀ {U U' : (D.obj i).Opens}, IsCompact (U : Set (D.obj i)) → IsCompact (U' : Set (D.obj i)) →
      IsCompact ((U ⊓ U' : (D.obj i).Opens) : Set (D.obj i)) := fun {U U'} h h' =>
    QuasiSeparatedSpace.inter_isCompact _ _ U.isOpen h U'.isOpen h'
  have le : ∀ {j k : I} (f : j ⟶ i) (g : k ⟶ j) (U : (D.obj i).Opens),
      D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := fun f g U => by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  have l₀ : ∀ a b : σ, π i ⁻¹ᵁ (V a ⊓ V b) ≤ L.U (p a) ⊓ L.U (p b) :=
    fun a b y hy => ⟨hV' a hy.1, hV' b hy.2⟩
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (q : σ × σ) j f => ∃ t : Γ(D.obj j, D.map f ⁻¹ᵁ (V q.1 ⊓ V q.2))ˣ, ∀ y : X,
      y ∈ π i ⁻¹ᵁ (V q.1 ⊓ V q.2) → gm (π j) y _ t = gm (𝟙 X) y _ (L.g (p q.1) (p q.2)))
    (by
      rintro q j f k g ⟨t, ht⟩
      refine ⟨res (le f g _) (pullU (D.map g) _ t), fun y hy => ?_⟩
      have hy' := cone_preimage_le D π w (g ≫ f) _ hy
      refine (gm_res_pullU (π k) (D.map g) y (le f g (V q.1 ⊓ V q.2)) hy' t).trans ?_
      rw [w g]
      exact ht y hy)
    (by
      rintro ⟨a, b⟩
      obtain ⟨j, f, t, ht⟩ := exists_unit_eq D π w hc (cpt (hV a).1.isCompact (hV b).1.isCompact)
        (res (l₀ a b) (L.g (p a) (p b)))
      exact ⟨j, f, t, fun y hy => (ht y hy).trans (gm_res (𝟙 X) y _ hy _)⟩)
  choose t ht using hj
  have l₁ : ∀ a b c, D.map f ⁻¹ᵁ (V a ⊓ V b ⊓ V c) ≤ D.map f ⁻¹ᵁ (V a ⊓ V b) := fun a b c _ hy => hy.1
  have l₂ : ∀ a b c, D.map f ⁻¹ᵁ (V a ⊓ V b ⊓ V c) ≤ D.map f ⁻¹ᵁ (V b ⊓ V c) :=
    fun a b c _ hy => ⟨hy.1.2, hy.2⟩
  have l₃ : ∀ a b c, D.map f ⁻¹ᵁ (V a ⊓ V b ⊓ V c) ≤ D.map f ⁻¹ᵁ (V a ⊓ V c) :=
    fun a b c _ hy => ⟨hy.1.1, hy.2⟩
  obtain ⟨k, g, hk⟩ := exists_common_refinement (i := j)
    (fun (q : σ × σ × σ) k g =>
      pullU (D.map g) _ (res (l₁ q.1 q.2.1 q.2.2) (t (q.1, q.2.1)) * res (l₂ q.1 q.2.1 q.2.2) (t (q.2.1, q.2.2))) =
      pullU (D.map g) _ (res (l₃ q.1 q.2.1 q.2.2) (t (q.1, q.2.2))))
    (by
      intro q k g k' g' h
      rw [D.map_comp]
      exact congrArg (pullU (D.map g') _) h)
    (by
      rintro ⟨a, b, c⟩
      refine exists_pullU_eq D π w hc ?_ _ _ fun y hy => ?_
      · exact QuasiCompact.isCompact_preimage (f := D.map f) _ (V a ⊓ V b ⊓ V c).isOpen
          (cpt (cpt (hV a).1.isCompact (hV b).1.isCompact) (hV c).1.isCompact)
      · have hy' : y ∈ π i ⁻¹ᵁ (V a ⊓ V b ⊓ V c) := by
          rw [← w f]; exact hy
        refine ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res (π j) y _ hy _).trans (ht (a, b) y hy'.1))
          ((gm_res (π j) y _ hy _).trans (ht (b, c) y ⟨hy'.1.2, hy'.2⟩)))).trans (Eq.trans ?_
          ((gm_res (π j) y _ hy _).trans (ht (a, c) y ⟨hy'.1.1, hy'.2⟩)).symm)
        exact gm_cocycle hL (𝟙 X) y (hV' a hy'.1.1) (hV' b hy'.1.2) (hV' c hy'.2))
  have l₄ : ∀ a b, D.map (g ≫ f) ⁻¹ᵁ V a ⊓ D.map (g ≫ f) ⁻¹ᵁ V b ≤
      D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ (V a ⊓ V b)) := fun a b => le f g (V a ⊓ V b)
  let M : LB (D.obj k) := ⟨σ, fun a => D.map (g ≫ f) ⁻¹ᵁ V a,
    fun a b => res (l₄ a b) (pullU (D.map g) _ (t (a, b)))⟩
  have val : ∀ {Z : Scheme.{0}} (r : Z ⟶ D.obj k) (z : Z) (a b : σ), r z ∈ M.U a → r z ∈ M.U b →
      gm r z _ (M.g a b) = gm (r ≫ D.map g) z _ (t (a, b)) :=
    fun r z a b ha hb => gm_res_pullU r (D.map g) z (l₄ a b) ⟨ha, hb⟩ _
  have pre : ∀ a, π k ⁻¹ᵁ M.U a ≤ π i ⁻¹ᵁ V a := fun a => by
    show π k ⁻¹ᵁ (D.map (g ≫ f) ⁻¹ᵁ V a) ≤ _
    rw [← Scheme.Hom.comp_preimage, w]
  refine ⟨k, M, fun a => p a.1, isLB_of_germs M (fun y => ?_) fun a b c y ha hb hc' => ?_,
    fun a => (pre a).trans (hV' a), fun a b y ha hb => ?_⟩
  · exact hcov.exists_mem (D.map (g ≫ f) y)
  · have hy : D.map g y ∈ D.map f ⁻¹ᵁ (V a ⊓ V b ⊓ V c) := le f g _ (show y ∈ D.map (g ≫ f) ⁻¹ᵁ
      (V a ⊓ V b ⊓ V c) from ⟨⟨ha, hb⟩, hc'⟩)
    have e := (gm_id_pullU (D.map g) y _ hy _).symm.trans
      ((congrArg (gm (𝟙 (D.obj k)) y (D.map g ⁻¹ᵁ D.map f ⁻¹ᵁ (V a ⊓ V b ⊓ V c))) (hk (a, b, c))).trans
        (gm_id_pullU (D.map g) y _ hy _))
    rw [val _ y a b ha hb, val _ y b c hb hc', val _ y a c ha hc', Category.id_comp]
    exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (D.map g) y _ hy _)
      (gm_res (D.map g) y _ hy _))).symm.trans (e.trans (gm_res (D.map g) y _ hy _))
  · rw [val _ y a b ha hb, w g]
    exact ht (a, b) y ⟨pre a ha, pre b hb⟩
end GlobalTheory.LBLimit
