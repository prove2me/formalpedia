-- Prove2me | solution 1 for GlobalTheory.CechDR.FormExt.exists_cocycle_restrict_sub_eq_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:03:23.671792+00:00
-- url     : https://prove2.me/submissions/a4f5d510-b624-4f95-b9a8-30ddd9a0b03c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOneFormsCocycleRestrictSubCoboundary
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.FormExt
attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler
namespace GlobalTheory.CechDR.FormExt
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict (FormExt.omExt F) G).pull1 → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) := by
  intro R _ C _ C' _ F G hsurj β' hβ'
  let f' : Z1 (G ⋙ omExt F) := ⟨fun t t' a ↦ (TrivSqZeroExt.inr (β' t t' a) : (omExt F).obj (G.obj t')),
    fun t t' t'' a b ↦ by
      apply TrivSqZeroExt.ext
      · show (0 : F.obj (G.obj t'')) = (extMap F (G.map b) (TrivSqZeroExt.inr (β' t t' a))).fst + 0
        rw [fst_extMap]; simp
      · show β' t t'' (a ≫ b) = (extMap F (G.map b) (TrivSqZeroExt.inr (β' t t' a))).snd + β' t' t'' b
        rw [snd_extMap, hβ']; rfl⟩
  obtain ⟨h0, hh⟩ := hsurj (H1.mk _ f')
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ h0
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hh
  obtain ⟨g, hg⟩ := hh
  refine ⟨fun T T' φ ↦ (f.1 T T' φ).snd, fun T T' T'' φ ψ ↦ ?_, fun t ↦ (g t).snd, fun t t' a ↦ ?_⟩
  · have e := congrArg TrivSqZeroExt.snd (Z1.comp f φ ψ)
    have e2 : TrivSqZeroExt.snd (mp (omExt F) ψ (f.1 T T' φ) + f.1 T' T'' ψ) =
        p1 F ψ (f.1 T T' φ).snd + (f.1 T' T'' ψ).snd := by
      show (extMap F ψ (f.1 T T' φ)).snd + (f.1 T' T'' ψ).snd = _
      exact congrArg (· + (f.1 T' T'' ψ).snd) (snd_extMap F ψ (f.1 T T' φ))
    exact e.trans e2
  · have e := congrArg TrivSqZeroExt.snd (congrFun (congrFun (congrFun hg t) t') a)
    have e2 : (g t').snd - p1 F (G.map a) (g t).snd = (f.1 _ _ (G.map a)).snd - β' t t' a :=
      calc (g t').snd - p1 F (G.map a) (g t).snd
          = (g t').snd - (extMap F (G.map a) (g t)).snd :=
            congrArg (fun z ↦ (g t').snd - z) (snd_extMap F (G.map a) (g t)).symm
        _ = TrivSqZeroExt.snd (d0 (G ⋙ omExt F) g t t' a) := rfl
        _ = _ := e
        _ = (f.1 _ _ (G.map a)).snd - β' t t' a := rfl
    exact e2.symm
end GlobalTheory.CechDR.FormExt
