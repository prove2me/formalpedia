-- Prove2me | solution 1 for GlobalTheory.spread_hom_generic_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:35:18.683332+00:00
-- url     : https://prove2.me/submissions/0419618d-7569-45be-983a-f5b6d9b14a3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_StalkLimit_exists_spread
import Theorems.Thm_GlobalTheory_IsGenericPointHom_range_eq
import Theorems.Thm_GlobalTheory_IsGenericPointHom_quasiCompact_and_dominant_of_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
namespace GlobalTheory.StalkLimit
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
variable {S X : Scheme.{u}} (x : S) (p : X ⟶ S)
variable {x p} {X' : Scheme.{u}} {φ : X' ⟶ X} {p' : X' ⟶ Spec (S.presheaf.stalk x)}
end GlobalTheory.StalkLimit
namespace GlobalTheory
open ExtUnique
namespace IsGenericPointHom
variable {U S : Scheme.{u}} [IsIntegral S] {j : U ⟶ S}
private lemma hom_ext_lemma {W X Y Z : Scheme.{u}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s]
    (hs : f ≫ s = g ≫ s) (w : W ⟶ X) [IsSchemeTheoreticallyDominant w] (hw : w ≫ f = w ≫ g) : f = g := by
  let e := pullback.fst (pullback.lift f g hs) (pullback.diagonal s)
  let k : W ⟶ pullback (pullback.lift f g hs) (pullback.diagonal s) :=
    pullback.lift w (w ≫ f) (by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hw])
  have hk : k ≫ e = w := pullback.lift_fst _ _ _
  have hker : e.ker = ⊥ := by
    refine le_bot_iff.mp ((Scheme.Hom.le_ker_comp k e).trans ?_)
    rw [hk, w.ker_eq_bot]
  have : IsIso e := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  have hc := pullback.condition (f := pullback.lift f g hs) (g := pullback.diagonal s)
  have h₁ : e ≫ f = pullback.snd _ _ := by
    calc e ≫ f = e ≫ pullback.lift f g hs ≫ pullback.fst s s := by rw [pullback.lift_fst]
      _ = pullback.snd _ _ ≫ pullback.diagonal s ≫ pullback.fst s s := by rw [reassoc_of% hc]
      _ = pullback.snd _ _ := by simp
  have h₂ : e ≫ g = pullback.snd _ _ := by
    calc e ≫ g = e ≫ pullback.lift f g hs ≫ pullback.snd s s := by rw [pullback.lift_snd]
      _ = pullback.snd _ _ ≫ pullback.diagonal s ≫ pullback.snd s s := by rw [reassoc_of% hc]
      _ = pullback.snd _ _ := by simp
  exact (cancel_epi e).mp (h₁.trans h₂.symm)
private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_⟩
  intro T x y x₀ y₀ hx hy
  have e : ∀ {A B : Over S} (g : A ⟶ B),
      ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left := by
    intro A B g
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have key : (lift x₀ y₀).left =
      (lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫ pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · calc (lift x₀ y₀).left ≫ pullback.fst G.hom G.hom = (lift x₀ y₀ ≫ fst G G).left := rfl
        _ = x.left ≫ pullback.fst G.hom f := by rw [lift_fst, hx]
        _ = (lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map (fst G G)).left ≫
              pullback.fst G.hom f := by
          rw [Functor.Monoidal.μ_fst, lift_fst]
        _ = _ := by simp only [Over.comp_left, Category.assoc, e]; rfl
    · calc (lift x₀ y₀).left ≫ pullback.snd G.hom G.hom = (lift x₀ y₀ ≫ snd G G).left := rfl
        _ = y.left ≫ pullback.fst G.hom f := by rw [lift_snd, hy]
        _ = (lift x y ≫ Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map (snd G G)).left ≫
              pullback.fst G.hom f := by
          rw [Functor.Monoidal.μ_snd, lift_snd]
        _ = _ := by simp only [Over.comp_left, Category.assoc, e]; rfl
  change (lift x₀ y₀ ≫ μ).left =
    (lift x y ≫ (Functor.LaxMonoidal.μ (Over.pullback f) G G ≫ (Over.pullback f).map μ)).left ≫ pullback.fst G.hom f
  rw [Over.comp_left, key]
  simp only [Over.comp_left, Category.assoc, e]
end IsGenericPointHom
end GlobalTheory
namespace GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}
end GlobalTheory.Published.SemiAbelianHomExtension
end
end

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory
open ExtUnique
namespace GlobalTheory
theorem _root_.solution {U S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] {j : U ⟶ S}
    (hj : IsGenericPointHom j) {G H : Over S} [GrpObj G] [GrpObj H] [Flat G.hom] [QuasiCompact G.hom]
    [QuasiSeparated G.hom] [IsSeparated H.hom] [LocallyOfFinitePresentation H.hom] {G' H' : Over U} [GrpObj G']
    [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ)
    (hψ : IsGrpPullback H' H j ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃ (V : S.Opens) (_ : genericPoint S ∈ V) (_ : IsAffineOpen V)
      (g : (Over.pullback V.ι).obj G ⟶ (Over.pullback V.ι).obj H) (_ : IsMonHom g)
      (w : G'.left ⟶ ((Over.pullback V.ι).obj G).left),
      w ≫ pullback.fst G.hom V.ι = φ ∧ w ≫ g.left ≫ pullback.fst H.hom V.ι = f.left ≫ ψ := by
  obtain ⟨e, he⟩ := hj
  have hsq : IsPullback j e.hom (𝟙 S) (S.fromSpecStalk (genericPoint S)) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, he]⟩
  have hpb := hφ.1.paste_vert hsq
  rw [Category.comp_id] at hpb
  have ha : (f.left ≫ ψ) ≫ H.hom = φ ≫ G.hom := by
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w f, hφ.1.w]
  obtain ⟨V, hηV, hVa, w, g₀, hw, hwg, hg₀⟩ := StalkLimit.exists_spread hpb H.hom (f.left ≫ ψ) ha
  let g : (Over.pullback V.ι).obj G ⟶ (Over.pullback V.ι).obj H :=
    Over.homMk (pullback.lift g₀ (pullback.snd G.hom V.ι) (by rw [hg₀, pullback.condition]))
      (pullback.lift_snd _ _ _)
  have hgl : g.left ≫ pullback.fst H.hom V.ι = g₀ := pullback.lift_fst _ _ _
  have hmon : IsMonHom g := by
    obtain ⟨k, hk⟩ : ∃ k : U ⟶ V, k ≫ V.ι = j := by
      refine ⟨IsOpenImmersion.lift V.ι j ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rintro _ ⟨u, rfl⟩
      have hr : j u ∈ Set.range j := ⟨u, rfl⟩
      rw [IsGenericPointHom.range_eq ⟨e, he⟩, Set.mem_singleton_iff] at hr
      rw [Scheme.Opens.range_ι]
      exact hr ▸ hηV
    subst hk
    obtain ⟨_, _⟩ := IsGenericPointHom.quasiCompact_and_dominant_of_comp (k := k) (i := V.ι) ⟨e, he⟩
    have hwk : w ≫ pullback.snd G.hom V.ι = G'.hom ≫ k := by
      rw [← cancel_mono V.ι, Category.assoc, ← pullback.condition, ← Category.assoc, hw, hφ.1.w,
        Category.assoc]
    have hsqV : IsPullback w G'.hom (pullback.snd G.hom V.ι) k :=
      IsPullback.of_right (by rw [hw]; exact hφ.1) hwk (IsPullback.of_hasPullback G.hom V.ι)
    have hG'V2 : ∀ (T : Over U) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ k) ⟶ (Over.pullback V.ι).obj G),
        x₀.left = x.left ≫ w → y₀.left = y.left ≫ w → (x₀ * y₀).left = (x * y).left ≫ w := by
      intro T x y x₀ y₀ hx hy
      let E : Over.mk (T.hom ≫ (k ≫ V.ι)) ≅ Over.mk ((T.hom ≫ k) ≫ V.ι) :=
        Over.isoMk (Iso.refl _) (by simp)
      let x₁ : Over.mk ((T.hom ≫ k) ≫ V.ι) ⟶ G := Over.homMk (x₀.left ≫ pullback.fst G.hom V.ι) (by
        rw [Category.assoc x₀.left, pullback.condition, ← Category.assoc x₀.left]
        exact congr_arg (· ≫ V.ι) (Over.w x₀))
      let y₁ : Over.mk ((T.hom ≫ k) ≫ V.ι) ⟶ G := Over.homMk (y₀.left ≫ pullback.fst G.hom V.ι) (by
        rw [Category.assoc y₀.left, pullback.condition, ← Category.assoc y₀.left]
        exact congr_arg (· ≫ V.ι) (Over.w y₀))
      have hC : (x₁ * y₁).left = (x₀ * y₀).left ≫ pullback.fst G.hom V.ι :=
        (IsGenericPointHom.isGrpPullback_pullback_fst V.ι G).2 (Over.mk (T.hom ≫ k)) x₀ y₀ x₁ y₁ rfl rfl
      have hB : ((E.hom ≫ x₁) * (E.hom ≫ y₁)).left = (x * y).left ≫ φ :=
        hφ.2 T x y (E.hom ≫ x₁) (E.hom ≫ y₁) (by simp [E, x₁, hx, hw]) (by simp [E, y₁, hy, hw])
      have hEc : ((E.hom ≫ x₁) * (E.hom ≫ y₁)).left = (x₁ * y₁).left := by
        rw [← MonObj.comp_mul]
        simp [E]
      apply pullback.hom_ext
      · rw [← hC, ← hEc, hB, Category.assoc, hw]
      · rw [Category.assoc, hwk, ← Category.assoc, Over.w (x * y)]
        exact Over.w (x₀ * y₀)
    have _ : Flat ((Over.pullback V.ι).obj G).hom :=
      show Flat (pullback.snd G.hom V.ι) from inferInstance
    have _ : Flat ((Over.pullback V.ι).obj G ⊗ (Over.pullback V.ι).obj G).hom :=
      show Flat (pullback.fst ((Over.pullback V.ι).obj G).hom ((Over.pullback V.ι).obj G).hom ≫
        ((Over.pullback V.ι).obj G).hom) from inferInstance
    have hsnd : ∀ {A : Over V.toScheme} (u v : A ⟶ (Over.pullback V.ι).obj H),
        u.left ≫ pullback.snd H.hom V.ι = v.left ≫ pullback.snd H.hom V.ι :=
      fun u v => (Over.w u).trans (Over.w v).symm
    have hmul : μ[(Over.pullback V.ι).obj G] ≫ g = (g ⊗ₘ g) ≫ μ[(Over.pullback V.ι).obj H] := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      swap
      · exact hsnd _ _
      let GV := (Over.pullback V.ι).obj G
      let π := pullback.fst (GV ⊗ GV).hom k
      let σ := pullback.snd (GV ⊗ GV).hom k
      let T' : Over U := Over.mk σ
      let a₁ : Over.mk (σ ≫ k) ⟶ GV := Over.homMk (π ≫ pullback.fst GV.hom GV.hom) (by
        rw [Category.assoc]
        exact pullback.condition)
      let a₂ : Over.mk (σ ≫ k) ⟶ GV := Over.homMk (π ≫ pullback.snd GV.hom GV.hom) (by
        rw [Category.assoc, ← pullback.condition (f := GV.hom) (g := GV.hom)]
        exact pullback.condition)
      have hl : (lift a₁ a₂).left = π := by
        apply pullback.hom_ext
        · exact congr_arg (fun u => u.left) (lift_fst a₁ a₂)
        · exact congr_arg (fun u => u.left) (lift_snd a₁ a₂)
      let x₁ : T' ⟶ G' := Over.homMk (hsqV.lift a₁.left σ (Over.w a₁)) (hsqV.lift_snd _ _ _)
      let x₂ : T' ⟶ G' := Over.homMk (hsqV.lift a₂.left σ (Over.w a₂)) (hsqV.lift_snd _ _ _)
      have hx₁ : x₁.left ≫ w = a₁.left := hsqV.lift_fst _ _ _
      have hx₂ : x₂.left ≫ w = a₂.left := hsqV.lift_fst _ _ _
      have hA : (a₁ * a₂).left = (x₁ * x₂).left ≫ w := hG'V2 T' x₁ x₂ a₁ a₂ hx₁.symm hx₂.symm
      let E : Over.mk (σ ≫ (k ≫ V.ι)) ≅ Over.mk ((σ ≫ k) ≫ V.ι) :=
        Over.isoMk (Iso.refl _) (by simp)
      let c₁ : Over.mk ((σ ≫ k) ≫ V.ι) ⟶ H :=
        Over.homMk ((a₁ ≫ g).left ≫ pullback.fst H.hom V.ι) (by
          rw [Category.assoc (a₁ ≫ g).left, pullback.condition, ← Category.assoc (a₁ ≫ g).left]
          exact congr_arg (· ≫ V.ι) (Over.w (a₁ ≫ g)))
      let c₂ : Over.mk ((σ ≫ k) ≫ V.ι) ⟶ H :=
        Over.homMk ((a₂ ≫ g).left ≫ pullback.fst H.hom V.ι) (by
          rw [Category.assoc (a₂ ≫ g).left, pullback.condition, ← Category.assoc (a₂ ≫ g).left]
          exact congr_arg (· ≫ V.ι) (Over.w (a₂ ≫ g)))
      have hC : (c₁ * c₂).left = ((a₁ ≫ g) * (a₂ ≫ g)).left ≫ pullback.fst H.hom V.ι :=
        (IsGenericPointHom.isGrpPullback_pullback_fst V.ι H).2 (Over.mk (σ ≫ k)) (a₁ ≫ g) (a₂ ≫ g) c₁ c₂ rfl rfl
      have hci : ∀ (a : Over.mk (σ ≫ k) ⟶ GV) (x : T' ⟶ G'), x.left ≫ w = a.left →
          (a ≫ g).left ≫ pullback.fst H.hom V.ι = (x ≫ f).left ≫ ψ := by
        intro a x hx
        rw [Over.comp_left, Category.assoc, hgl, ← hx, Category.assoc, hwg, Over.comp_left,
          Category.assoc]
      have hB : ((E.hom ≫ c₁) * (E.hom ≫ c₂)).left = ((x₁ ≫ f) * (x₂ ≫ f)).left ≫ ψ :=
        hψ.2 T' (x₁ ≫ f) (x₂ ≫ f) (E.hom ≫ c₁) (E.hom ≫ c₂)
          ((Category.id_comp _).trans (hci a₁ x₁ hx₁)) ((Category.id_comp _).trans (hci a₂ x₂ hx₂))
      have hEc : ((E.hom ≫ c₁) * (E.hom ≫ c₂)).left = (c₁ * c₂).left := by
        rw [← MonObj.comp_mul]
        simp [E]
      apply IsGenericPointHom.hom_ext_lemma H.hom (by
          rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc,
            hsnd (μ[GV] ≫ g) ((g ⊗ₘ g) ≫ μ[(Over.pullback V.ι).obj H])]) π
      rw [← hl]
      calc (lift a₁ a₂).left ≫ (μ[GV] ≫ g).left ≫ pullback.fst H.hom V.ι
          = (a₁ * a₂).left ≫ g.left ≫ pullback.fst H.hom V.ι := by
            simp only [Over.comp_left, Category.assoc, Hom.mul_def]
        _ = ((x₁ ≫ f) * (x₂ ≫ f)).left ≫ ψ := by
            rw [hA, hgl, Category.assoc, hwg, ← MonObj.mul_comp, Over.comp_left, Category.assoc]
        _ = ((a₁ ≫ g) * (a₂ ≫ g)).left ≫ pullback.fst H.hom V.ι := by rw [← hB, hEc, hC]
        _ = (lift a₁ a₂).left ≫ ((g ⊗ₘ g) ≫ μ[(Over.pullback V.ι).obj H]).left ≫
              pullback.fst H.hom V.ι := by
            simp only [Over.comp_left, Category.assoc, Hom.mul_def, ← lift_map]
    refine ⟨?_, hmul⟩
    have h1 : (1 : 𝟙_ (Over V.toScheme) ⟶ (Over.pullback V.ι).obj G) ≫ g =
        ((1 : 𝟙_ (Over V.toScheme) ⟶ (Over.pullback V.ι).obj G) ≫ g) * ((1 : 𝟙_ (Over V.toScheme) ⟶ _) ≫ g) := by
      conv_lhs => rw [← mul_one (1 : 𝟙_ (Over V.toScheme) ⟶ (Over.pullback V.ι).obj G)]
      rw [Hom.mul_def, Hom.mul_def, Category.assoc, hmul, ← Category.assoc, lift_map]
    have h2 : (1 : 𝟙_ (Over V.toScheme) ⟶ (Over.pullback V.ι).obj G) ≫ g = 1 := by
      simpa using h1.symm
    simpa [Hom.one_def] using h2
  exact ⟨V, hηV, hVa, g, hmon, w, hw, by rw [hgl, hwg]⟩
end GlobalTheory
