-- Prove2me | solution 1 for M4aHerbrand.map_prG_map_eq_map_map_prH_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/cedfea57-7a07-5eb6-8bf3-e6d104c38a80

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_map_prG_map_eq_map_map_prH_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_map_prG_map_eq_map_map_prH_of_smul_eq.M4aHerbrand"
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport
open scoped Pointwise

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart coe_finPart_apply IdeleGaloisDescent GenuineDescent.genuineDescentDatum_act_snd_apply GenuineDescent.genuineDescentDatum subsingleton_ideleGaloisDescent"
namespace ConjSqKProof
p2m_open "M4aHerbrand"

theorem map_eq_map_of_hom_eq {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ B) (φ₂ : Rep.res f₂ A ⟶ B)
    (hφ : ∀ a : A, φ₁.hom a = φ₂.hom a) (n : ℕ) :
    groupCohomology.map f₁ φ₁ n = groupCohomology.map f₂ φ₂ n := by
  subst h
  obtain rfl : φ₁ = φ₂ := by
    ext a
    exact hφ a
  rfl

end M4aHerbrand.ConjSqKProof

set_option maxHeartbeats 3200000 in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (H : Subgroup (F ≃ₐ[E] F))

    (prH : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ H)) (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
    (hprH : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (w : HeightOneSpectrum (𝓞 F))
    (prG : Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ x : (AdeleRing (𝓞 F) F)ˣ, prG.hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (w₁ : HeightOneSpectrum (𝓞 F)) (g : F ≃ₐ[E] F) (hg : g • w₁ = w)
    (c : ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) →* ↥H)
    (hc : ∀ x : ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)),
      ((c x : ↥H) : F ≃ₐ[E] F) = g⁻¹ * ((x : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) * g)
    (T : Rep.res c (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
        Rep.res ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
          (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)))
    (hT : ∀ a : (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ),
      T.hom a = (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ).ρ g a)

    (c'' : ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)) →* ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)))
    (hc'' : ∀ x : ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)),
      ((c'' x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁))) : F ≃ₐ[E] F) = g⁻¹ * ((x : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) * g)
    (T'' : Rep.res c'' (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)) ⟶
        Rep.res ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
    (hT'' : ∀ x : (w₁.adicCompletion F)ˣ, ((Additive.toMul (T''.hom (Additive.ofMul x)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
      NumberField.PlaceTransport.transport g hg (x : w₁.adicCompletion F))
    (n : ℕ) (y : groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) n) :
    (groupCohomology.map (MonoidHom.id ↥((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)))
        ((Rep.resFunctor ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype).map prG) n).hom
        ((groupCohomology.map c T n).hom y) =
      (groupCohomology.map c'' T'' n).hom
        ((groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ H)) (prH w₁) n).hom y) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  obtain rfl : D = GenuineDescent.genuineDescentDatum E F := Subsingleton.elim _ _

  have h1 := congrArg (fun S => S.hom y)
    (groupCohomology.map_comp
      (A := Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
      (B := Rep.res ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
          (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)))
      (C := Rep.res ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
      c (MonoidHom.id _) T
      ((Rep.resFunctor ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype).map prG) n)
  have h2 := congrArg (fun S => S.hom y)
    (groupCohomology.map_comp
      (A := Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
      (B := Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ))
      (C := Rep.res ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
      (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ H)) c'' (prH w₁) T'' n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2]

  have hgrp : c.comp (MonoidHom.id _) =
      (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ H)).comp c'' := by
    ext x : 2
    change ((c x : ↥H) : F ≃ₐ[E] F) = ((c'' x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁))) : F ≃ₐ[E] F)
    rw [hc, hc'']
  refine congrArg
    (fun (S : groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) n ⟶
        groupCohomology (Rep.res ((MulAut.conj g • H).subgroupOf (NumberField.PlaceDecomp.decomp E F w)).subtype
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) n) => S.hom y)
    (M4aHerbrand.ConjSqKProof.map_eq_map_of_hom_eq hgrp _ _ (fun a => ?_) n)
  obtain ⟨x, rfl⟩ : ∃ x : (AdeleRing (𝓞 F) F)ˣ, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
  change prG.hom (T.hom (Additive.ofMul x)) = T''.hom ((prH w₁).hom (Additive.ofMul x))
  rw [hT]
  change prG.hom (Additive.ofMul (g • x)) = T''.hom ((prH w₁).hom (Additive.ofMul x))
  rw [hactI]
  erw [hprG, hprH]
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_ofMul]
  erw [hT'']
  rw [coe_finPart_apply, coe_finPart_apply]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply E F g (x : AdeleRing (𝓞 F) F) hg

end S_M4aHerbrand_map_prG_map_eq_map_map_prH_of_smul_eq
end P2MW
export P2MW.S_M4aHerbrand_map_prG_map_eq_map_map_prH_of_smul_eq (solution)
