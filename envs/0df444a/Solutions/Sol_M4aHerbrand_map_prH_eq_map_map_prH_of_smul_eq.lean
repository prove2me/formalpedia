-- Prove2me | solution 1 for M4aHerbrand.map_prH_eq_map_map_prH_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4eefc679-902d-5905-a500-2ffa00928b77

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_groupCohomology_map_conj_eq_id
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_map_prH_eq_map_map_prH_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_map_prH_eq_map_map_prH_of_smul_eq.M4aHerbrand"
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart coe_finPart_apply IdeleGaloisDescent GenuineDescent.genuineDescentDatum_act_snd_apply GenuineDescent.genuineDescentDatum subsingleton_ideleGaloisDescent"
namespace ConjCoordHProof
p2m_open "M4aHerbrand"

open NumberField.PlaceDecomp NumberField.PlaceTransport

theorem map_eq_map_of_hom_eq {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ B) (φ₂ : Rep.res f₂ A ⟶ B)
    (hφ : ∀ a : A, φ₁.hom a = φ₂.hom a) (n : ℕ) :
    groupCohomology.map f₁ φ₁ n = groupCohomology.map f₂ φ₂ n := by
  subst h
  obtain rfl : φ₁ = φ₂ := by
    ext a
    exact hφ a
  rfl

noncomputable def conjRepHomH {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] (H : Subgroup G) (h : ↥H) :
    Rep.res (MulAut.conj h⁻¹).toMonoidHom (Rep.res H.subtype (Rep.ofMulDistribMulAction G M)) ⟶
      Rep.res H.subtype (Rep.ofMulDistribMulAction G M) :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (MulDistribMulAction.toMonoidHom M (h : G))).toIntLinearMap, fun x => LinearMap.ext fun a => by
    change Additive.ofMul ((h : G) • ((((MulAut.conj h⁻¹) x : ↥H) : G) • (Additive.toMul : _ ≃ M) a))
      = Additive.ofMul (((x : ↥H) : G) • ((h : G) • (Additive.toMul : _ ≃ M) a))
    rw [MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul, ← mul_smul, ← mul_assoc,
      ← mul_assoc, mul_inv_cancel, one_mul]⟩

theorem conjRepHomH_spec {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] (H : Subgroup G) (h : ↥H)
    (m : Rep.res (MulAut.conj h⁻¹).toMonoidHom (Rep.res H.subtype (Rep.ofMulDistribMulAction G M))) :
    (conjRepHomH (M := M) H h).hom m = (Rep.res H.subtype (Rep.ofMulDistribMulAction G M)).ρ (h⁻¹)⁻¹ m := by
  rw [inv_inv]
  rfl

end M4aHerbrand.ConjCoordHProof

open M4aHerbrand.ConjCoordHProof NumberField.PlaceDecomp NumberField.PlaceTransport in

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (H : Subgroup (F ≃ₐ[E] F))

    (prH : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ H))
          (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
    (hprH : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ),
      (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (w w₁ : HeightOneSpectrum (𝓞 F)) (h : ↥H) (hh : (h : F ≃ₐ[E] F) • w = w₁)
    (ch : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)) →* ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w)))
    (hch : ∀ x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w₁)),
      ((ch x : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F w))) : F ≃ₐ[E] F) = (h : F ≃ₐ[E] F)⁻¹ * (x : F ≃ₐ[E] F) * (h : F ≃ₐ[E] F))
    (Th : Rep.res ch (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ))
    (hTh : ∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (Th.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
      NumberField.PlaceTransport.transport (h : F ≃ₐ[E] F) hh (x : w.adicCompletion F))
    (n : ℕ) (y : groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) n) :
    (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w₁) ≤ H)) (prH w₁) n).hom y =
      (groupCohomology.map ch Th n).hom
        ((groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ H)) (prH w) n).hom y) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  obtain rfl : D = GenuineDescent.genuineDescentDatum E F := Subsingleton.elim _ _

  have hid := groupCohomology.map_conj_eq_id (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) h⁻¹ n
    (conjRepHomH (M := (AdeleRing (𝓞 F) F)ˣ) H h) (conjRepHomH_spec H h)
  have hy : (groupCohomology.map (MulAut.conj h⁻¹).toMonoidHom (conjRepHomH (M := (AdeleRing (𝓞 F) F)ˣ) H h) n).hom y = y := by
    rw [hid]; rfl
  conv_lhs => rw [← hy]

  have h1 := congrArg (fun T => T.hom y)
    (groupCohomology.map_comp (A := Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
      (B := Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
      (C := Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (decomp E F w₁) ≤ (decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(decomp E F w₁)) (w₁.adicCompletion F)ˣ))
      (MulAut.conj h⁻¹).toMonoidHom (Subgroup.inclusion (inf_le_left : H ⊓ (decomp E F w₁) ≤ H))
      (conjRepHomH (M := (AdeleRing (𝓞 F) F)ˣ) H h) (prH w₁) n)
  have h2 := congrArg (fun T => T.hom y)
    (groupCohomology.map_comp (A := Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
      (B := Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (decomp E F w) ≤ (decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(decomp E F w)) (w.adicCompletion F)ˣ))
      (C := Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (decomp E F w₁) ≤ (decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(decomp E F w₁)) (w₁.adicCompletion F)ˣ))
      (Subgroup.inclusion (inf_le_left : H ⊓ (decomp E F w) ≤ H)) ch (prH w) Th n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2]

  have hgrp : (MulAut.conj h⁻¹).toMonoidHom.comp (Subgroup.inclusion (inf_le_left : H ⊓ (decomp E F w₁) ≤ H)) =
      (Subgroup.inclusion (inf_le_left : H ⊓ (decomp E F w) ≤ H)).comp ch := by
    ext x : 1
    apply Subtype.ext
    change (((MulAut.conj h⁻¹) (Subgroup.inclusion (inf_le_left : H ⊓ (decomp E F w₁) ≤ H) x) : ↥H) : F ≃ₐ[E] F) =
      ((ch x : ↥(H ⊓ (decomp E F w))) : F ≃ₐ[E] F)
    rw [hch, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  refine congrArg
    (fun (S : groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) n ⟶
        groupCohomology (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (decomp E F w₁) ≤ (decomp E F w₁)))
          (Rep.ofMulDistribMulAction (↥(decomp E F w₁)) (w₁.adicCompletion F)ˣ)) n) => S.hom y)
    (map_eq_map_of_hom_eq hgrp _ _ (fun a => ?_) n)
  obtain ⟨x, rfl⟩ : ∃ x : (AdeleRing (𝓞 F) F)ˣ, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
  change (prH w₁).hom (Additive.ofMul ((h : F ≃ₐ[E] F) • x)) = Th.hom ((prH w).hom (Additive.ofMul x))
  rw [hactI]
  erw [hprH, hprH]
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_ofMul]
  erw [hTh]
  rw [coe_finPart_apply, coe_finPart_apply]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply E F (h : F ≃ₐ[E] F) (x : AdeleRing (𝓞 F) F) hh

end S_M4aHerbrand_map_prH_eq_map_map_prH_of_smul_eq
end P2MW
export P2MW.S_M4aHerbrand_map_prH_eq_map_map_prH_of_smul_eq (solution)
