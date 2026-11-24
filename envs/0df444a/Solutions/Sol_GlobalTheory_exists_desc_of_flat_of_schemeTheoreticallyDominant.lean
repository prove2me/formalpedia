-- Prove2me | solution 1 for GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:08.203644+00:00
-- url     : https://prove2.me/submissions/d4afe9da-3f25-4522-89a5-fecb15afe0eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDescOfFlatOfSchemeTheoreticallyDominantBas
import Theorems.Thm_GlobalTheory_ExtUnique_hom_ext_of_dominant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {S S' U U' X Y Y' YU Y'' : Scheme.{0}} (f : S' ⟶ S) (j : U ⟶ S) (f' : U' ⟶ U) (j' : U' ⟶ S')
      [Flat f] [Surjective f] [QuasiCompact f] [QuasiCompact j] [IsSchemeTheoreticallyDominant j],
      IsPullback j' f' f j → ∀ (x : X ⟶ S) [IsSeparated x] (y : Y ⟶ S) [Flat y] (y' : Y' ⟶ S')
      (π : Y' ⟶ Y), IsPullback π y' y f → ∀ (yU : YU ⟶ U) (ιY : YU ⟶ Y), IsPullback ιY yU y j →
      ∀ (y'' : Y'' ⟶ U') (c : Y'' ⟶ Y') (cU : Y'' ⟶ YU), IsPullback c y'' y' j' →
      IsPullback cU y'' yU f' → cU ≫ ιY = c ≫ π → ∀ (h' : Y' ⟶ X) (hU : YU ⟶ X),
      h' ≫ x = y' ≫ f → c ≫ h' = cU ≫ hU → ∃ h : Y ⟶ X, π ≫ h = h' ∧ ιY ≫ h = hU ∧ h ≫ x = y := by
  intro S S' U U' X Y Y' YU Y'' f j f' j' _ _ _ _ _ hUsq x _ y _ y' π hπ yU ιY hι y'' c cU hc hcU
    hcomm h' hU hx hagree
  have : Flat π := MorphismProperty.of_isPullback (P := @Flat) hπ.flip ‹_›
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) hπ.flip ‹_›
  have : QuasiCompact π := MorphismProperty.of_isPullback (P := @QuasiCompact) hπ.flip ‹_›
  have : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hUsq ‹_›
  have : Surjective f' := MorphismProperty.of_isPullback (P := @Surjective) hUsq ‹_›
  have : Flat cU := MorphismProperty.of_isPullback (P := @Flat) hcU.flip ‹_›
  have : Surjective cU := MorphismProperty.of_isPullback (P := @Surjective) hcU.flip ‹_›
  have : Epi cU := Flat.epi_of_flat_of_surjective cU

  have key : ∀ {T : Scheme.{0}} (a : T ⟶ Y') (ψ : T ⟶ U) (w : (a ≫ π) ≫ y = ψ ≫ j),
      a ≫ h' = hι.lift (a ≫ π) ψ w ≫ hU := by
    intro T a ψ w
    have w1 : (a ≫ y') ≫ f = ψ ≫ j := by
      rw [Category.assoc, ← hπ.w, ← Category.assoc, w]
    let u : T ⟶ U' := hUsq.lift (a ≫ y') ψ w1
    have w2 : a ≫ y' = u ≫ j' := (hUsq.lift_fst _ _ _).symm
    let q : T ⟶ Y'' := hc.lift a u w2
    have hq : q ≫ cU = hι.lift (a ≫ π) ψ w := by
      apply hι.hom_ext
      · rw [Category.assoc, hcomm, ← Category.assoc, hc.lift_fst, hι.lift_fst]
      · rw [Category.assoc, hcU.w, ← Category.assoc, hc.lift_snd, hι.lift_snd, hUsq.lift_snd]
    calc a ≫ h' = q ≫ c ≫ h' := by rw [← Category.assoc, hc.lift_fst]
      _ = q ≫ cU ≫ hU := by rw [hagree]
      _ = _ := by rw [← Category.assoc, hq]

  have hP : pullback.fst π π ≫ h' = pullback.snd π π ≫ h' := by
    let g : pullback π π ⟶ S := pullback.fst π π ≫ π ≫ y
    have : Flat g := by dsimp [g]; infer_instance
    let φ : pullback g j ⟶ pullback π π := pullback.fst g j
    have : IsSchemeTheoreticallyDominant φ := IsSchemeTheoreticallyDominant.pullbackFst g j
    refine ExtUnique.hom_ext_of_dominant x ?_ φ ?_
    · simp only [Category.assoc, hx]
      rw [← hπ.w, pullback.condition_assoc]
    · have e1 : ((φ ≫ pullback.fst π π) ≫ π) ≫ y = pullback.snd g j ≫ j := by
        simpa [g, Category.assoc] using pullback.condition (f := g) (g := j)
      have e2 : ((φ ≫ pullback.snd π π) ≫ π) ≫ y = pullback.snd g j ≫ j := by
        rw [Category.assoc φ, ← pullback.condition]; exact e1
      have l : hι.lift ((φ ≫ pullback.fst π π) ≫ π) (pullback.snd g j) e1 =
          hι.lift ((φ ≫ pullback.snd π π) ≫ π) (pullback.snd g j) e2 := by
        congr 1; rw [Category.assoc, Category.assoc, pullback.condition]
      rw [← Category.assoc, ← Category.assoc, key _ _ e1, key _ _ e2, l]
  have H : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Y'), a ≫ π = b ≫ π → a ≫ h' = b ≫ h' := by
    intro Z a b hab
    calc a ≫ h' = pullback.lift a b hab ≫ pullback.fst π π ≫ h' := by rw [pullback.lift_fst_assoc]
      _ = pullback.lift a b hab ≫ pullback.snd π π ≫ h' := by rw [hP]
      _ = b ≫ h' := by rw [pullback.lift_snd_assoc]
  let h : Y ⟶ X := EffectiveEpi.desc π h' H
  have h1 : π ≫ h = h' := EffectiveEpi.fac π h' H
  refine ⟨h, h1, ?_, ?_⟩
  · apply (cancel_epi cU).1
    rw [← Category.assoc, hcomm, Category.assoc, h1, hagree]
  · apply (cancel_epi π).1
    rw [← Category.assoc, h1, hx, hπ.w]
end GlobalTheory
