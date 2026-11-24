-- Prove2me | solution 1 for GlobalTheory.CechDR.pullHyp2_restrict_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:03:40.220107+00:00
-- url     : https://prove2.me/submissions/29e700f3-015d-4b12-a1d3-b4dab975e560

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocalizationOfData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitMpOmjExtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommaSecondOrderCocycleLift
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamCoefMapOneForms_restrictAlongFunctor
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_one
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_two
import Theorems.Thm_GlobalTheory_CechDR_pOm_dTwo
import Theorems.Thm_GlobalTheory_CechDR_pullHyp2_mk
import Theorems.Thm_GlobalTheory_CechDR_qOm_restrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CechDR
namespace GlobalTheory.CechDR
theorem _root_.solution : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict F G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) → (∀ κ : W1 F 2, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = pOm F 2 ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F 2 (G.map a) (θ' t)) → ∃ θ : W0 F 2, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F 2 φ (θ T)) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F 2 (G.map a) (η' t)) → ∃ η : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) → (∀ (T : C) (x : Om R (F.obj T) 3), (∀ t (u : T ⟶ G.obj t), pOm F 3 u x = 0) → x = 0) → Function.Surjective (pullHyp2 (CoefMap.restrict F G)) := by
  intro R _ C _ C' _ F G hO hκ hl h2 he hs c'
  obtain ⟨c', rfl⟩ := Hyp2.mk_surjective _ c'
  obtain ⟨h0, hh⟩ := hO (H2.mk _ ⟨c'.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c'.2).1⟩)
  obtain ⟨z, rfl⟩ := H2.mk_surjective F h0
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hh
  obtain ⟨y', hy'⟩ := hh
  let z' : ∀ (t t' t'' : C') (_ : t ⟶ t') (_ : t' ⟶ t''), F.obj (G.obj t'') := c'.1.1
  let a' : ∀ (t t' : C') (_ : t ⟶ t'), Ω[F.obj (G.obj t')⁄R] := c'.1.2.1
  let η' : ∀ t : C', Om R (F.obj (G.obj t)) 2 := c'.1.2.2
  let y : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t') := y'
  have hz : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), z.1 _ _ _ (G.map a) (G.map b) =
      z' t t' t'' a b + (mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b) := by
    intro t t' t'' a b
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hy' t) t') t'') a) b
    change mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b =
      z.1 _ _ _ (G.map a) (G.map b) - z' t t' t'' a b at e
    rw [e]; ring
  let a2 : ∀ (t t' : C') (_ : t ⟶ t'), Ω[F.obj (G.obj t')⁄R] := fun t t' a ↦ a' t t' a - D R _ (y t t' a)
  have ha2 : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), a2 t t'' (a ≫ b) =
      p1 F (G.map b) (a2 t t' a) + a2 t' t'' b + D R _ (z.1 _ _ _ (G.map a) (G.map b)) := by
    intro t t' t'' a b
    have e : a' t t'' (a ≫ b) = p1 F (G.map b) (a' t t' a) + a' t' t'' b +
      D R _ (z' t t' t'' a b) := cechDeRhamTotalCocyclesTwo.one c' a b
    simp only [a2]
    rw [e, hz, map_sub, p1_D]
    simp only [map_add, map_sub]
    abel

  obtain ⟨a₀, ha₀⟩ := hκ (fun T T' T'' φ ψ ↦ -D R _ (z.1 T T' T'' φ ψ)) (by
      intro T T' T'' T''' φ ψ χ
      have e := z.2 φ ψ χ
      simp only [p1_D, map_neg]
      rw [← neg_add, ← neg_add, ← map_add, ← map_add, e]) a2 (by
      intro t t' t'' a b
      beta_reduce
      rw [ha2]; abel)
  have ha₀' : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a₀ T T'' (φ ≫ ψ) = p1 F ψ (a₀ T T' φ) + a₀ T' T'' ψ + D R _ (z.1 T T' T'' φ ψ) := by
    intro T T' T'' φ ψ
    have e := ha₀ φ ψ
    beta_reduce at e
    linear_combination (norm := abel1) e
  obtain ⟨β, hβ, θ', hθ'⟩ := hl (fun t t' a ↦ a₀ _ _ (G.map a) - a2 t t' a) (by
      intro t t' t'' a b
      beta_reduce
      rw [G.map_comp, ha2, ha₀']
      simp only [a2, map_sub]
      abel)
  let a : A1 F := fun T T' φ ↦ a₀ T T' φ - β T T' φ
  have ha : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ + D R _ (z.1 T T' T'' φ ψ) := by
    intro T T' T'' φ ψ
    simp only [a]
    rw [ha₀', hβ, map_sub]
    abel
  have haG : ∀ ⦃t t' : C'⦄ (b : t ⟶ t'), a _ _ (G.map b) =
      a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) := by
    intro t t' b
    have e := hθ' b
    beta_reduce at e
    simp only [a]
    linear_combination (norm := abel1) -e
  let η3 : ∀ t : C', Om R (F.obj (G.obj t)) 2 := fun t ↦ η' t - dOne R _ (θ' t)
  have hη3 : ∀ ⦃t t' : C'⦄ (b : t ⟶ t'), dOne R _ (a _ _ (G.map b)) =
      η3 t' - pOm F 2 (G.map b) (η3 t) := by
    intro t t' b
    have e : η' t' = pOm F 2 (G.map b) (η' t) + dOne R _ (a' t t' b) := cechDeRhamTotalCocyclesTwo.two c' b
    simp only [η3]
    rw [haG, e]
    simp only [a2, map_sub, dOne_D, pOm_dOne]
    abel
  obtain ⟨η₀, hη₀⟩ := h2 (fun T T' φ ↦ dOne R _ (a T T' φ)) (by
      intro T T' T'' φ ψ
      beta_reduce
      rw [ha, map_add, map_add, dOne_D, pOm_dOne, add_zero]) η3 hη3
  obtain ⟨ε, hε, hεG⟩ := he (fun t ↦ η3 t - η₀ (G.obj t)) (by
      intro t t' b
      beta_reduce
      have e1 := hη3 b
      have e2 := hη₀ (G.map b)
      beta_reduce at e2
      rw [map_sub]
      linear_combination (norm := abel1) e2 - e1)
  let η : W0 F 2 := fun T ↦ η₀ T + ε T
  have hη : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T) + dOne R _ (a T T' φ) := by
    intro T T' φ
    have e := hη₀ φ
    beta_reduce at e
    simp only [η]
    rw [hε φ, e, map_add]
    abel
  have hηG : ∀ t, η (G.obj t) = η3 t := by
    intro t
    simp only [η]
    rw [hεG t]
    abel
  have hclosed : ∀ T, dTwo R _ (η T) = 0 := by
    intro T
    refine hs T _ fun t u ↦ ?_
    have e : pOm F 2 u (η T) = η3 t - dOne R _ (a _ _ u) := by
      rw [← hηG, hη u]; abel
    have e3 : dTwo R _ (η' t) = 0 := cechDeRhamTotalCocyclesTwo.closed c' t
    rw [pOm_dTwo, e]
    simp only [η3, map_sub, dTwo_dOne, e3, sub_zero]
  let c : cechDeRhamTotalCocyclesTwo F := ⟨(z.1, a, η), mem_cechDeRhamTotalCocyclesTwo_iff.2 ⟨z.2, ha, hη, hclosed⟩⟩
  refine ⟨Hyp2.mk F c, ?_⟩
  rw [pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨(y, fun t ↦ -θ' t), Tot2.ext (fun t t' t'' b b' ↦ ?_) (fun t t' b ↦ ?_) fun t ↦ ?_⟩
  · change mp F (G.map b') (y t t' b) - y t t'' (b ≫ b') + y t' t'' b' =
      z.1 _ _ _ (G.map b) (G.map b') - z' t t' t'' b b'
    rw [hz]; ring
  · change -θ' t' - p1 F (G.map b) (-θ' t) - D R _ (y t t' b) =
      q1 (CoefMap.restrict F G) t' (a _ _ (G.map b)) - c'.1.2.1 t t' b
    have e4 : q1 (CoefMap.restrict F G) t' (a _ _ (G.map b)) =
        a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) := (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t' _).trans (haG b)
    rw [e4]
    change -θ' t' - p1 F (G.map b) (-θ' t) - D R _ (y t t' b) =
      a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) - a' t t' b
    simp only [a2, map_neg]
    abel
  · change dOne R _ (-θ' t) = qOm (CoefMap.restrict F G) 2 t (η (G.obj t)) - c'.1.2.2 t
    have e5 : qOm (CoefMap.restrict F G) 2 t (η (G.obj t)) = η3 t :=
      (qOm_restrict F G t _).trans (hηG t)
    rw [e5]
    change dOne R _ (-θ' t) = η3 t - η' t
    simp only [η3, map_neg]
    abel
end GlobalTheory.CechDR
