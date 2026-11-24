-- Prove2me | solution 1 for GlobalTheory.QuotientGluing.exists_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:57.604206+00:00
-- url     : https://prove2.me/submissions/4d93727e-6d05-476d-8d99-245a29327582

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientOfFiniteGroup
import Theorems.Thm_GlobalTheory_QuotientGluing_isOpenImmersion_desc
import Theorems.Thm_GlobalTheory_QuotientGluing_app_of_chart
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_IsAffineQuotient_of_cover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.QuotientGluing
variable {G : Type} [Group G] [Finite G] {X : Scheme.{0}}
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.QuotientGluing
theorem _root_.solution (ρ : G →* Aut X) (𝒰 : Set X.Opens)
    (hbas : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V)
    (hc : ∀ x : X, ∃ U : 𝒰, x ∈ U.1)
    (T : 𝒰 → Scheme.{0}) (i : ∀ U, T U ⟶ X) [∀ U, IsOpenImmersion (i U)]
    (hr : ∀ U, (i U).opensRange = U.1) (haff : ∀ U : 𝒰, IsAffineOpen U.1)
    (σ : ∀ U, G →* Aut (T U)) (hσ : ∀ U g, (σ U g).hom ≫ i U = i U ≫ (ρ g).hom)
    (Y : 𝒰 → Scheme.{0}) [∀ U, IsAffine (Y U)] (q : ∀ U, T U ⟶ Y U)
    (hq : ∀ U, IsAffineQuotient (σ U) (q U)) :
    ∃ (X' : Scheme.{0}) (π : X ⟶ X'), IsAffineQuotient ρ π := by
  have hmem (U : 𝒰) (x : T U) : i U x ∈ U.1 := hr U ▸ ⟨x, rfl⟩
  have hex (U : 𝒰) (x : X) (hx : x ∈ U.1) : ∃ y, i U y = x := by
    rw [← hr U] at hx; exact hx
  have hinj (U : 𝒰) : Function.Injective (i U) := (i U).isOpenEmbedding.injective
  have hσ' (U : 𝒰) (g : G) (x : T U) : i U ((σ U g).hom x) = (ρ g).hom (i U x) :=
    congr($(hσ U g) x)
  have hqσ (U : 𝒰) (g : G) (x : T U) : q U ((σ U g).hom x) = q U x :=
    congr($((hq U).comp_eq g) x)
  let m {U V : 𝒰} (h : U.1 ≤ V.1) : T U ⟶ T V := IsOpenImmersion.lift (i V) (i U) (by
    rintro _ ⟨x, rfl⟩
    exact hex V _ (h (hmem U x)))
  have hm {U V : 𝒰} (h : U.1 ≤ V.1) : m h ≫ i V = i U := IsOpenImmersion.lift_fac _ _ _
  clear_value m
  have hm' {U V : 𝒰} (h : U.1 ≤ V.1) (x : T U) : i V (m h x) = i U x := congr($(hm h) x)
  have hmo {U V : 𝒰} (h : U.1 ≤ V.1) : IsOpenImmersion (m h) := by
    have : IsOpenImmersion (m h ≫ i V) := by rw [hm]; infer_instance
    exact .of_comp _ (i V)
  have hmσ {U V : 𝒰} (h : U.1 ≤ V.1) (g : G) : (σ U g).hom ≫ m h = m h ≫ (σ V g).hom := by
    rw [← cancel_mono (i V), Category.assoc, Category.assoc, hm, hσ, hσ, reassoc_of% hm]
  let F : 𝒰 ⥤ Scheme.{0} :=
    { obj := Y
      map {U V} f := (hq U).desc (m (show U.1 ≤ V.1 from f.le) ≫ q V) fun g ↦ by
        rw [reassoc_of% hmσ, (hq V).comp_eq]
      map_id U := (hq U).hom_ext (by
        have : m (le_refl U.1) = 𝟙 _ := by rw [← cancel_mono (i U), hm, Category.id_comp]
        rw [IsAffineQuotient.comp_desc, this, Category.id_comp, Category.comp_id])
      map_comp {U V W} f g := (hq U).hom_ext (by
        have : m (show U.1 ≤ W.1 from (f ≫ g).le) =
            m (show U.1 ≤ V.1 from f.le) ≫ m (show V.1 ≤ W.1 from g.le) := by
          rw [← cancel_mono (i W), Category.assoc, hm, hm, hm]
        rw [IsAffineQuotient.comp_desc, IsAffineQuotient.comp_desc_assoc, Category.assoc,
          IsAffineQuotient.comp_desc, this, Category.assoc]) }
  let e (U : 𝒰) : T U ⟶ F.obj U := q U
  have hnat {U V : 𝒰} (f : U ⟶ V) : e U ≫ F.map f = m (show U.1 ≤ V.1 from f.le) ≫ e V :=
    (hq U).comp_desc _ fun g ↦ by rw [reassoc_of% hmσ, (hq V).comp_eq]
  have hnat' {U V : 𝒰} (f : U ⟶ V) (x : T U) :
      F.map f (e U x) = e V (m (show U.1 ≤ V.1 from f.le) x) := congr($(hnat f) x)
  have hF {U V : 𝒰} (f : U ⟶ V) : IsOpenImmersion (F.map f) :=
    have := hmo (show U.1 ≤ V.1 from f.le)
    isOpenImmersion_desc (hq U) (hq V) _ (hmσ _) _ (hnat f)
  have hsurj (U : 𝒰) : Function.Surjective (e U) := (hq U).surjective.surj
  have hfib (U : 𝒰) (x y : T U) (h : e U x = e U y) : ∃ g, (ρ g).hom (i U x) = i U y := by
    obtain ⟨g, rfl⟩ := ((hq U).apply_eq_iff x y).mp h
    exact ⟨g, (hσ' U g x).symm⟩
  have key {U V : 𝒰} (x : T U) (y : T V) (h : i U x = i V y) :
      ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W),
        F.map f z = e U x ∧ F.map g z = e V y := by
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (hmem U x) (h ▸ hmem V y)
    obtain ⟨z, hz⟩ := hex ⟨W, hW⟩ _ hxW
    refine ⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ z, ?_, ?_⟩
    · rw [hnat']; congr 1; apply hinj; rw [hm', hz]
    · rw [hnat']; congr 1; apply hinj; rw [hm', hz, h]
  have : (F ⋙ Scheme.forget).IsLocallyDirected := by
    constructor
    intro U V W f g x y h
    obtain ⟨x, rfl⟩ := hsurj U x
    obtain ⟨y, rfl⟩ := hsurj V y
    have h' : F.map f (e U x) = F.map g (e V y) := h
    rw [hnat', hnat'] at h'
    obtain ⟨k, hk⟩ := hfib _ _ _ h'
    rw [hm', hm', ← hσ'] at hk
    have := key _ _ hk
    rwa [show e U ((σ U k).hom x) = e U x from hqσ U k x] at this
  have key2 {U V : 𝒰} (x : T U) (y : T V)
      (h : colimit.ι F U (e U x) = colimit.ι F V (e V y)) : i V y ∈ U.1 := by
    obtain ⟨W, f, g, z, -, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := hsurj W z
    rw [hnat'] at h2
    obtain ⟨k, hk⟩ := hfib _ _ _ h2
    rw [hm', ← hσ'] at hk
    exact hk ▸ (show W.1 ≤ U.1 from f.le) (hmem W _)
  let 𝒱 : X.OpenCover := Scheme.Cover.mkOfCovers 𝒰 T i (fun x ↦ by
    obtain ⟨U, hU⟩ := hc x
    exact ⟨U, hex U x hU⟩)
  let j : X ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : i U (pullback.fst (i U) (i V) x) = i V (pullback.snd (i U) (i V) x) :=
      congr($(pullback.condition (f := i U) (g := i V)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (hmem U _) (hx ▸ hmem V _)
    let α : T ⟨W, hW⟩ ⟶ pullback (i U) (i V) :=
      pullback.lift (m h1) (m h2) ((hm h1).trans (hm h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = m h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = m h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; exact hmo _
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    obtain ⟨z, hz⟩ := hex ⟨W, hW⟩ _ hxW
    refine ⟨α.opensRange, ⟨z, ?_⟩, ?_⟩
    · apply (pullback.fst (i U) (i V)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      apply hinj
      rw [hm', hz]
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      change α ≫ pullback.fst (i U) (i V) ≫ e U ≫ colimit.ι F U =
        α ≫ pullback.snd (i U) (i V) ≫ e V ≫ colimit.ι F V
      rw [reassoc_of% hα1, reassoc_of% hα2,
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) (homOfLE h1)),
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) (homOfLE h2)), colimit.w, colimit.w])
  have hj (U : 𝒰) : i U ≫ j = e U ≫ colimit.ι F U := 𝒱.ι_glueMorphisms _ _ U
  have hj' (U : 𝒰) (x : T U) : j (i U x) = colimit.ι F U (e U x) := congr($(hj U) x)
  have hpre (U : 𝒰) : j ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := hsurj U y
      obtain ⟨V, hV⟩ := hc x
      obtain ⟨z, rfl⟩ := hex V x hV
      exact key2 y z (hy.trans (hj' V z))
    · intro hx
      obtain ⟨z, rfl⟩ := hex U x hx
      exact ⟨_, (hj' U z).symm⟩
  refine ⟨colimit F, j, .of_cover (fun g ↦ 𝒱.hom_ext _ _ fun U ↦ ?_) fun y ↦ ?_⟩
  · change i U ≫ _ = i U ≫ _
    have : (σ U g).hom ≫ e U = e U := (hq U).comp_eq g
    rw [← reassoc_of% hσ, hj, reassoc_of% this]
  · obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F y
    have : IsAffine (F.obj U) := inferInstanceAs (IsAffine (Y U))
    refine ⟨(colimit.ι F U).opensRange, isAffineOpen_opensRange _, ⟨x, rfl⟩,
      by rw [hpre]; exact haff U, ?_⟩
    exact app_of_chart (hq U) j (i U) (hσ U) (colimit.ι F U) (hj U) _ le_rfl
      (by rw [hpre, hr])
end GlobalTheory.QuotientGluing
