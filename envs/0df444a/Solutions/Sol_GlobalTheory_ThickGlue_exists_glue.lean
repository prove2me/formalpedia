-- Prove2me | solution 1 for GlobalTheory.ThickGlue.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:19.420742+00:00
-- url     : https://prove2.me/submissions/16920319-f300-4898-9c23-df0e1bc43e5f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThickGlue
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.ThickGlue
theorem _root_.solution (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens)
    (hbas : ∀ U ∈ 𝒰, ∀ (W : B₀.Opens) (x : B₀), x ∈ U → x ∈ W → ∃ V ∈ 𝒰, x ∈ V ∧ V ≤ U ∧ V ≤ W)
    (hcov : sSup 𝒰 = ⊤) (F : 𝒰 ⥤ Scheme.{0})
    (hF : ∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f))
    (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U)
    (he : ∀ U, IsClosedImmersion (e U)) (hs : ∀ U, Surjective (e U))
    (hnat : ∀ {U V : 𝒰} (h : U.1 ≤ V.1),
      B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) :
    ∃ (B : Scheme.{0}) (j : B₀ ⟶ B) (_ : IsClosedImmersion j) (_ : Surjective j)
      (κ : ∀ U, F.obj U ⟶ B) (_ : ∀ U, IsOpenImmersion (κ U)),
      (∀ U, U.1.ι ≫ j = e U ≫ κ U) ∧ (∀ U, j ⁻¹ᵁ (κ U).opensRange = U.1) ∧
      ∀ {U V : 𝒰} (f : U ⟶ V), F.map f ≫ κ V = κ U := by
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme),
      F.map f (e U x) = e V (B₀.homOfLE (show U.1 ≤ V.1 from f.le) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat]
    rfl
  have hinj : ∀ U, Function.Injective (e U) := fun U ↦ (e U).isClosedEmbedding.injective
  have key : ∀ {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme), x.1 = y.1 →
      ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W),
        F.map f z = e U x ∧ F.map g z = e V y := by
    intro U V x y h
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 x.1 x.2 (h ▸ y.2)
    refine ⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ ⟨x.1, hxW⟩, ?_, ?_⟩
    · rw [hnat']; congr 1; apply Subtype.ext; simp
    · rw [hnat']; congr 1; apply Subtype.ext; simpa using h
  have : (F ⋙ Scheme.forget).IsLocallyDirected := by
    constructor
    intro U V W f g x y h
    obtain ⟨x, rfl⟩ := (e U).surjective x
    obtain ⟨y, rfl⟩ := (e V).surjective y
    have h' : F.map f (e U x) = F.map g (e V y) := h
    rw [hnat', hnat'] at h'
    have h'' := congrArg Subtype.val (hinj _ h')
    exact key x y (by simpa using h'')
  have key2 : ∀ {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme),
      colimit.ι F U (e U x) = colimit.ι F V (e V y) → x.1 = y.1 := by
    intro U V x y h
    obtain ⟨W, f, g, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := (e W).surjective z
    rw [hnat'] at h1 h2
    have h1' := congrArg Subtype.val (hinj _ h1)
    have h2' := congrArg Subtype.val (hinj _ h2)
    simp only [Scheme.homOfLE_apply] at h1' h2'
    exact h1'.symm.trans h2'
  have hc : ∀ x : B₀, ∃ U : 𝒰, x ∈ U.1 := by
    intro x
    have : x ∈ sSup 𝒰 := by rw [hcov]; trivial
    obtain ⟨U, hU, hx⟩ := TopologicalSpace.Opens.mem_sSup.mp this
    exact ⟨⟨U, hU⟩, hx⟩
  let 𝒱 : B₀.OpenCover := B₀.openCoverOfIsOpenCover (fun U : 𝒰 ↦ U.1) (by
    rw [TopologicalSpace.IsOpenCover, ← hcov, sSup_eq_iSup'])
  let j : B₀ ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : (pullback.fst (𝒱.f U) (𝒱.f V) x).1 = (pullback.snd (𝒱.f U) (𝒱.f V) x).1 :=
      congr($(pullback.condition (f := 𝒱.f U) (g := 𝒱.f V)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 _ (pullback.fst (𝒱.f U) (𝒱.f V) x).2
      (hx ▸ (pullback.snd (𝒱.f U) (𝒱.f V) x).2)
    let α : W.toScheme ⟶ pullback (𝒱.f U) (𝒱.f V) :=
      pullback.lift (B₀.homOfLE h1) (B₀.homOfLE h2) ((B₀.homOfLE_ι h1).trans (B₀.homOfLE_ι h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = B₀.homOfLE h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = B₀.homOfLE h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; infer_instance
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    refine ⟨α.opensRange, ⟨⟨_, hxW⟩, ?_⟩, ?_⟩
    · apply (pullback.fst (𝒱.f U) (𝒱.f V)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      rw [reassoc_of% hα1, reassoc_of% hα2, reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) h1),
        reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) h2), colimit.w, colimit.w])
  have hj : ∀ U : 𝒰, U.1.ι ≫ j = e U ≫ colimit.ι F U := fun U ↦ 𝒱.ι_glueMorphisms _ _ U
  have hj' : ∀ (U : 𝒰) (x : U.1.toScheme), j x.1 = colimit.ι F U (e U x) := fun U x ↦
    congr($(hj U) x)
  have hpre : ∀ U, j ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    intro U
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (e U).surjective y
      obtain ⟨V, hV⟩ := hc x
      have := key2 y ⟨x, hV⟩ (hy.trans (hj' V ⟨x, hV⟩))
      have h2 : y.1 = x := this
      exact h2 ▸ y.2
    · intro hx
      exact ⟨_, (hj' U ⟨x, hx⟩).symm⟩
  refine ⟨colimit F, j, ?_, ⟨?_⟩, colimit.ι F, inferInstance, hj, hpre, fun f ↦ colimit.w F f⟩
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
      (Scheme.IsLocallyDirected.openCover F)]
    intro U
    have H : IsPullback (e U) U.1.ι (colimit.ι F U) j :=
      IsOpenImmersion.isPullback _ _ _ _ (hj U) (by rw [hpre]; simp)
    have : pullback.snd j (colimit.ι F U) = H.flip.isoPullback.inv ≫ e U := by simp
    change IsClosedImmersion (pullback.snd j (colimit.ι F U))
    rw [this]
    infer_instance
  · intro b
    obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F b
    obtain ⟨x, rfl⟩ := (e U).surjective x
    exact ⟨_, hj' U x⟩
end GlobalTheory.ThickGlue
