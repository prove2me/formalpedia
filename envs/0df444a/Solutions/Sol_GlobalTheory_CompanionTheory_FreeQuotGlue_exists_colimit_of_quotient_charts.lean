-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FreeQuotGlue.exists_colimit_of_quotient_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:12.230149+00:00
-- url     : https://prove2.me/submissions/7a0fadae-b49f-4139-951d-ed222d47cb1c

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_GlueQuotientChartsCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot GlobalTheory.CompanionTheory.FreeQuotGlue
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FreeQuotGlue
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.CompanionTheory.FreeQuotGlue
theorem _root_.solution : ∀ {X : Scheme.{0}} (R : X → X → Prop) (𝒰 : Set X.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → (∀ x : X, ∃ U : 𝒰, x ∈ U.1) → ∀ (Y : 𝒰 → Scheme.{0}) (q : ∀ U : 𝒰, U.1.toScheme ⟶ Y U), (∀ U, Epi (q U)) → (∀ U, Function.Surjective (q U)) → (∀ (U : 𝒰) (u v : U.1.toScheme), q U u = q U v ↔ R (U.1.ι u) (U.1.ι v)) → (∀ (U : 𝒰) (x y : X), R x y → x ∈ U.1 → y ∈ U.1) → ∀ (k : ∀ U V : 𝒰, U.1 ≤ V.1 → (Y U ⟶ Y V)), (∀ U V h, IsOpenImmersion (k U V h)) → (∀ U V h, q U ≫ k U V h = X.homOfLE h ≫ q V) → ∃ (Y' : Scheme.{0}) (π : X ⟶ Y') (em : ∀ U, Y U ⟶ Y') (_ : ∀ U, IsOpenImmersion (em U)), (∀ U, U.1.ι ≫ π = q U ≫ em U) ∧ (∀ U, π ⁻¹ᵁ (em U).opensRange = U.1) ∧ ∀ y : Y', ∃ U, ∃ z : Y U, em U z = y := by
  intro X R 𝒰 hbas hc Y q hepi hsurj hfib hst k hko hqk
  have hr (U : 𝒰) : U.1.ι.opensRange = U.1 := Scheme.Opens.opensRange_ι _
  have hmem (U : 𝒰) (x : U.1.toScheme) : U.1.ι x ∈ U.1 := by
    have : U.1.ι x ∈ U.1.ι.opensRange := ⟨x, rfl⟩
    rwa [hr U] at this
  have hex (U : 𝒰) (x : X) (hx : x ∈ U.1) : ∃ y, U.1.ι y = x := by
    rw [← hr U] at hx; exact hx
  have hinj (U : 𝒰) : Function.Injective U.1.ι := U.1.ι.isOpenEmbedding.injective
  have hm {U V : 𝒰} (h : U.1 ≤ V.1) : X.homOfLE h ≫ V.1.ι = U.1.ι := X.homOfLE_ι h
  have hm' {U V : 𝒰} (h : U.1 ≤ V.1) (x : U.1.toScheme) : V.1.ι (X.homOfLE h x) = U.1.ι x :=
    congr($(hm h) x)
  have hmo {U V : 𝒰} (h : U.1 ≤ V.1) : IsOpenImmersion (X.homOfLE h) := by
    have : IsOpenImmersion (X.homOfLE h ≫ V.1.ι) := by rw [hm]; infer_instance
    exact .of_comp _ V.1.ι
  let F : 𝒰 ⥤ Scheme.{0} :=
    { obj := Y
      map {U V} f := k U V f.le
      map_id U := by
        have := hepi U
        rw [← cancel_epi (q U), hqk]
        have : X.homOfLE (show U.1 ≤ U.1 from (𝟙 U : U ⟶ U).le) = 𝟙 _ := by
          rw [← cancel_mono U.1.ι, hm, Category.id_comp]
        rw [this, Category.id_comp]
        exact (Category.comp_id _).symm
      map_comp {U V W} f g := by
        have := hepi U
        rw [← cancel_epi (q U), hqk, reassoc_of% (hqk U V f.le), hqk]
        have : X.homOfLE (show U.1 ≤ W.1 from (f ≫ g).le) =
            X.homOfLE (show U.1 ≤ V.1 from f.le) ≫ X.homOfLE (show V.1 ≤ W.1 from g.le) := by
          rw [← cancel_mono W.1.ι, Category.assoc, hm, hm, hm]
        rw [this, Category.assoc] }
  let e (U : 𝒰) : U.1.toScheme ⟶ F.obj U := q U
  have hnat {U V : 𝒰} (f : U ⟶ V) :
      e U ≫ F.map f = X.homOfLE (show U.1 ≤ V.1 from f.le) ≫ e V := hqk U V f.le
  have hnat' {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme) :
      F.map f (e U x) = e V (X.homOfLE (show U.1 ≤ V.1 from f.le) x) := congr($(hnat f) x)
  have hF {U V : 𝒰} (f : U ⟶ V) : IsOpenImmersion (F.map f) := hko U V f.le
  have hsurj' (U : 𝒰) : Function.Surjective (e U) := hsurj U
  have hfib' (U : 𝒰) (x y : U.1.toScheme) : e U x = e U y ↔ R (U.1.ι x) (U.1.ι y) := hfib U x y
  have key {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme) (h : U.1.ι x = V.1.ι y) :
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
    obtain ⟨x, rfl⟩ := hsurj' U x
    obtain ⟨y, rfl⟩ := hsurj' V y
    have h' : F.map f (e U x) = F.map g (e V y) := h
    rw [hnat', hnat'] at h'
    have hR := (hfib' _ _ _).mp h'
    rw [hm', hm'] at hR
    obtain ⟨y', hy'⟩ := hex U _ (hst U _ _ hR (hmem U x))
    have hxy : e U x = e U y' := (hfib' U _ _).mpr (by rw [hy']; exact hR)
    have := key _ _ hy'
    rwa [← hxy] at this
  have key2 {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme)
      (h : colimit.ι F U (e U x) = colimit.ι F V (e V y)) : V.1.ι y ∈ U.1 := by
    obtain ⟨W, f, g, z, -, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := hsurj' W z
    rw [hnat'] at h2
    have hR := (hfib' _ _ _).mp h2
    rw [hm'] at hR
    exact hst U _ _ hR ((show W.1 ≤ U.1 from f.le) (hmem W _))
  let 𝒱 : X.OpenCover := Scheme.Cover.mkOfCovers 𝒰 (fun U ↦ U.1.toScheme) (fun U ↦ U.1.ι)
    (fun x ↦ by
      obtain ⟨U, hU⟩ := hc x
      exact ⟨U, hex U x hU⟩)
  let j : X ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : U.1.ι (pullback.fst U.1.ι V.1.ι x) = V.1.ι (pullback.snd U.1.ι V.1.ι x) :=
      congr($(pullback.condition (f := U.1.ι) (g := V.1.ι)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (hmem U _) (hx ▸ hmem V _)
    let α : W.toScheme ⟶ pullback U.1.ι V.1.ι :=
      pullback.lift (X.homOfLE h1) (X.homOfLE h2) ((hm (U := ⟨W, hW⟩) h1).trans (hm (U := ⟨W, hW⟩) h2).symm)
    have hα1 : α ≫ pullback.fst _ _ = X.homOfLE h1 := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = X.homOfLE h2 := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; exact hmo (U := ⟨W, hW⟩) _
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    obtain ⟨z, hz⟩ := hex ⟨W, hW⟩ _ hxW
    refine ⟨α.opensRange, ⟨z, ?_⟩, ?_⟩
    · apply (pullback.fst U.1.ι V.1.ι).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      apply hinj
      rw [hm' (U := ⟨W, hW⟩), hz]
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      change α ≫ pullback.fst U.1.ι V.1.ι ≫ e U ≫ colimit.ι F U =
        α ≫ pullback.snd U.1.ι V.1.ι ≫ e V ≫ colimit.ι F V
      rw [reassoc_of% hα1, reassoc_of% hα2,
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) (homOfLE h1)),
        ← reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) (homOfLE h2)), colimit.w, colimit.w])
  have hj (U : 𝒰) : U.1.ι ≫ j = e U ≫ colimit.ι F U := 𝒱.ι_glueMorphisms _ _ U
  have hj' (U : 𝒰) (x : U.1.toScheme) : j (U.1.ι x) = colimit.ι F U (e U x) := congr($(hj U) x)
  have hpre (U : 𝒰) : j ⁻¹ᵁ (colimit.ι F U).opensRange = U.1 := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := hsurj' U y
      obtain ⟨V, hV⟩ := hc x
      obtain ⟨z, rfl⟩ := hex V x hV
      exact key2 y z (hy.trans (hj' V z))
    · intro hx
      obtain ⟨z, rfl⟩ := hex U x hx
      exact ⟨_, (hj' U z).symm⟩
  refine ⟨colimit F, j, fun U ↦ colimit.ι F U, fun U ↦ inferInstance, hj, hpre, fun y ↦ ?_⟩
  obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F y
  exact ⟨U, x, rfl⟩
end GlobalTheory.CompanionTheory.FreeQuotGlue
