-- Prove2me | solution 1 for GlobalTheory.CechDR.pullHyp1_restrict_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:39:29.712804+00:00
-- url     : https://prove2.me/submissions/f7e1b534-a667-4334-85dc-9fb26a83f8b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullHyp1RestrictSurjective
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamCoefMapOneForms_restrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_pullHyp1_mk
import Theorems.Thm_GlobalTheory_CechDR_toO_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hO : Function.Surjective (CoefMap.restrict F G).pull1)
    (hc : ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
        κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) →
      ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
        κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) →
      ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T))
    (hf : Function.Surjective (pullGlob1 (CoefMap.restrict F G)))
    (hs : ∀ (T : C) (η : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u η = 0) → η = 0) :
    Function.Surjective (pullHyp1 (CoefMap.restrict F G)) := by
  intro c'
  obtain ⟨c', rfl⟩ := Hyp1.mk_surjective _ c'
  obtain ⟨h0, hh⟩ := hO (toO _ (Hyp1.mk _ c'))
  obtain ⟨f, rfl⟩ := H1.mk_surjective F h0
  rw [toO_mk, CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hh
  obtain ⟨g', hg'⟩ := hh
  let g : ∀ t, F.obj (G.obj t) := g'
  let f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t') := c'.1.1
  let ω' : ∀ t, Ω[F.obj (G.obj t)⁄R] := c'.1.2
  have hga : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) - f' t t' a := fun t t' a ↦
    congrFun (congrFun (congrFun hg' t) t') a
  have hκ : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      D R _ (f.1 T T'' (φ ≫ ψ)) = p1 F ψ (D R _ (f.1 T T' φ)) + D R _ (f.1 T' T'' ψ) := by
    intro T T' T'' φ ψ
    rw [Z1.comp f φ ψ, map_add, p1_D]
  let θ' : ∀ t, Ω[F.obj (G.obj t)⁄R] := fun t ↦ ω' t + D R _ (g t)
  have hθ' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      D R _ (f.1 _ _ (G.map a)) = θ' t' - p1 F (G.map a) (θ' t) := by
    intro t t' a
    have e1 : ω' t' = p1 F (G.map a) (ω' t) + D R _ (f' t t' a) := cechDeRhamTotalCocyclesOne.conn c' a
    have e2 : f.1 _ _ (G.map a) = g t' - mp F (G.map a) (g t) + f' t t' a :=
      (sub_eq_iff_eq_add.1 (hga a).symm)
    simp only [θ']
    rw [e1, e2]
    simp only [map_add, map_sub, p1_D]
    abel
  obtain ⟨θ, hθ⟩ := hc (fun T T' φ ↦ D R _ (f.1 T T' φ)) hκ θ' hθ'
  have hθ2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), D R _ (f.1 T T' φ) = θ T' - p1 F φ (θ T) := hθ
  let ψ0 : Glob1 (G ⋙ F) := ⟨fun t ↦ θ' t - θ (G.obj t), fun t t' a ↦ by
    change θ' t' - θ (G.obj t') = p1 F (G.map a) (θ' t - θ (G.obj t))
    have e := (hθ2 (G.map a)).symm.trans (hθ' a)
    rw [map_sub]
    rw [← sub_eq_zero] at e ⊢
    rw [← neg_eq_zero, ← e]
    abel⟩
  obtain ⟨ψ, hψ⟩ := hf ψ0
  have hψG : ∀ t, ψ.1 (G.obj t) = θ' t - θ (G.obj t) := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun z : Glob1 (G ⋙ F) ↦ z.1 t) hψ)
  let ω : A0 F := fun T ↦ θ T + ψ.1 T
  have hωG : ∀ t, ω (G.obj t) = θ' t := fun t ↦ by
    change θ (G.obj t) + ψ.1 (G.obj t) = _
    rw [hψG]; abel
  have hconn : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), ω T' = p1 F φ (ω T) + D R _ (f.1 T T' φ) := by
    intro T T' φ
    change θ T' + ψ.1 T' = p1 F φ (θ T + ψ.1 T) + D R _ (f.1 T T' φ)
    rw [map_add, ← ψ.2 φ, hθ2 φ]; abel
  have hclosed : ∀ T, dOne R _ (ω T) = 0 := by
    intro T
    refine hs T _ fun t u ↦ ?_
    have e : p1 F u (ω T) = ω' t + D R _ (g t) - D R _ (f.1 _ _ u) := by
      rw [eq_sub_iff_add_eq, ← hconn u, hωG]
    rw [pOm_dOne, e, map_sub, map_add, dOne_D, dOne_D]
    have e3 : dOne R _ (ω' t) = 0 := cechDeRhamTotalCocyclesOne.closed c' t
    rw [e3]; simp
  let c : cechDeRhamTotalCocyclesOne F := ⟨(f.1, ω), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, hconn, hclosed⟩⟩
  refine ⟨Hyp1.mk F c, ?_⟩
  rw [pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨g', Tot1.ext (fun t t' a ↦ hga a) fun t ↦ ?_⟩
  have e4 : q1 (CoefMap.restrict F G) t (ω (G.obj t)) = θ' t := (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).trans (hωG t)
  change D R _ (g t) = q1 (CoefMap.restrict F G) t (ω (G.obj t)) - c'.1.2 t
  rw [e4]
  change _ = ω' t + D R _ (g t) - ω' t
  abel
end GlobalTheory.CechDR
