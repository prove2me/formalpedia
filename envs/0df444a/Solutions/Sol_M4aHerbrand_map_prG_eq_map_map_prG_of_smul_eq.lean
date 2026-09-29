-- Prove2me | solution 1 for M4aHerbrand.map_prG_eq_map_map_prG_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/850225c6-c6ca-5f4d-ba27-a33b27fc71f1

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

namespace P2MW.S_M4aHerbrand_map_prG_eq_map_map_prG_of_smul_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_map_prG_eq_map_map_prG_of_smul_eq.M4aHerbrand"
open scoped NumberField.PlaceDecomp NumberField.PlaceTransport

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart coe_finPart_apply IdeleGaloisDescent GenuineDescent.genuineDescentDatum_act_snd_apply GenuineDescent.genuineDescentDatum subsingleton_ideleGaloisDescent"
namespace ConjCoordProof
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

noncomputable def resRepHom {G H : Type} [Group G] [Group H] (φ : H →* G) {M N : Type} [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction H N] (f : M →* N) (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m) :
    Rep.res φ (Rep.ofMulDistribMulAction G M) ⟶ Rep.ofMulDistribMulAction H N :=
  Rep.ofHom ⟨(MonoidHom.toAdditive f).toIntLinearMap, fun h => LinearMap.ext fun a => by
    change Additive.ofMul (f (φ h • (Additive.toMul : _ ≃ M) a)) = Additive.ofMul (h • f ((Additive.toMul : _ ≃ M) a))
    rw [hf]⟩

noncomputable def conjRepHom {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] (σ : G) :
    Rep.res (MulAut.conj σ⁻¹).toMonoidHom (Rep.ofMulDistribMulAction G M) ⟶ Rep.ofMulDistribMulAction G M :=
  resRepHom (MulAut.conj σ⁻¹).toMonoidHom (MulDistribMulAction.toMonoidHom M σ) fun h m => by
    change σ • ((MulAut.conj σ⁻¹) h • m) = h • σ • m
    rw [MulAut.conj_apply, inv_inv, ← mul_smul, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

theorem conjRepHom_spec {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M] (σ : G)
    (m : Rep.res (MulAut.conj σ⁻¹).toMonoidHom (Rep.ofMulDistribMulAction G M)) :
    (conjRepHom (M := M) σ).hom m = (Rep.ofMulDistribMulAction G M).ρ (σ⁻¹)⁻¹ m := by
  rw [inv_inv]
  rfl

end M4aHerbrand.ConjCoordProof

open M4aHerbrand.ConjCoordProof NumberField.PlaceDecomp NumberField.PlaceTransport in

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (hσ : σ • w = w₁)
    (c : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* ↥(NumberField.PlaceDecomp.decomp E F w))
    (hc : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w₁), ((c τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ)
    (T : Rep.res c (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)
    (hT : ∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (T.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
      NumberField.PlaceTransport.transport σ hσ (x : w.adicCompletion F))
    (n : ℕ) (y : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) n) :
    (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w₁).subtype (prG w₁) n).hom y =
      (groupCohomology.map c T n).hom ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (prG w) n).hom y) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  obtain rfl : D = GenuineDescent.genuineDescentDatum E F := Subsingleton.elim _ _

  have hid := groupCohomology.map_conj_eq_id (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) σ⁻¹ n
    (conjRepHom (M := (AdeleRing (𝓞 F) F)ˣ) σ) (conjRepHom_spec σ)
  have hy : (groupCohomology.map (MulAut.conj σ⁻¹).toMonoidHom (conjRepHom (M := (AdeleRing (𝓞 F) F)ˣ) σ) n).hom y = y := by
    rw [hid]; rfl
  conv_lhs => rw [← hy]

  have h1 := congrArg (fun T => T.hom y)
    (groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
      (B := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
      (C := Rep.ofMulDistribMulAction (↥(decomp E F w₁)) (w₁.adicCompletion F)ˣ)
      (MulAut.conj σ⁻¹).toMonoidHom (decomp E F w₁).subtype (conjRepHom (M := (AdeleRing (𝓞 F) F)ˣ) σ) (prG w₁) n)
  have h2 := congrArg (fun T => T.hom y)
    (groupCohomology.map_comp (A := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
      (B := Rep.ofMulDistribMulAction (↥(decomp E F w)) (w.adicCompletion F)ˣ)
      (C := Rep.ofMulDistribMulAction (↥(decomp E F w₁)) (w₁.adicCompletion F)ˣ)
      (decomp E F w).subtype c (prG w) T n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2]

  have hgrp : (MulAut.conj σ⁻¹).toMonoidHom.comp (decomp E F w₁).subtype = (decomp E F w).subtype.comp c := by
    ext τ : 1
    change (MulAut.conj σ⁻¹) (τ : F ≃ₐ[E] F) = ((c τ : ↥(decomp E F w)) : F ≃ₐ[E] F)
    rw [hc, MulAut.conj_apply, inv_inv]
  refine congrArg
    (fun (S : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) n ⟶
        groupCohomology (Rep.ofMulDistribMulAction (↥(decomp E F w₁)) (w₁.adicCompletion F)ˣ) n) => S.hom y)
    (map_eq_map_of_hom_eq hgrp _ _ (fun a => ?_) n)
  obtain ⟨x, rfl⟩ : ∃ x : (AdeleRing (𝓞 F) F)ˣ, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
  change (prG w₁).hom (Additive.ofMul (σ • x)) = T.hom ((prG w).hom (Additive.ofMul x))
  rw [hactI]
  erw [hprG, hprG]
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_ofMul]
  erw [hT]
  rw [coe_finPart_apply, coe_finPart_apply]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply E F σ (x : AdeleRing (𝓞 F) F) hσ

end S_M4aHerbrand_map_prG_eq_map_map_prG_of_smul_eq
end P2MW
export P2MW.S_M4aHerbrand_map_prG_eq_map_map_prG_of_smul_eq (solution)
