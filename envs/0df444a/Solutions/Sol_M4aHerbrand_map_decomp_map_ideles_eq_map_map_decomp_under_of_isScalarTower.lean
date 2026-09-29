-- Prove2me | solution 1 for M4aHerbrand.map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0af5087c-b0bb-5283-9835-3e6bc38d5465

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart coe_finPart_apply GenuineDescent.genuineBaseChange"
namespace CoordInfProof
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

end M4aHerbrand.CoordInfProof

open M4aHerbrand.CoordInfProof in

theorem solution
    (E F M : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra E F] [Algebra E M] [Algebra F M] [IsScalarTower E F M]
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ] [MulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ]

    (S : Subgroup (M ≃ₐ[E] M)) [S.Normal] (ι : (M ≃ₐ[E] M) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : M ≃ₐ[E] M) (x : F), algebraMap F M (ι (QuotientGroup.mk g) x) = g (algebraMap F M x))

    (J : Rep.res (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
          Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ)
    (hJ : ∀ x : (AdeleRing (𝓞 F) F)ˣ, J.hom (Additive.ofMul x) =
        Additive.ofMul (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange F M).β.toMonoidHom x))

    (W : HeightOneSpectrum (𝓞 M))
    (prG : Rep.res (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ)
    (hprG : ∀ x : (AdeleRing (𝓞 F) F)ˣ, prG.hom (Additive.ofMul x) = Additive.ofMul (finPart (W.under (𝓞 F)) x))
    (prM : Rep.res (NumberField.PlaceDecomp.decomp E M W).subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) (AdeleRing (𝓞 M) M)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hprM : ∀ x : (AdeleRing (𝓞 M) M)ˣ, prM.hom (Additive.ofMul x) = Additive.ofMul (finPart W x))

    (r : ↥(NumberField.PlaceDecomp.decomp E M W) →* ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))))
    (hr : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E M W)) (x : F),
      algebraMap F M (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x) = (σ : M ≃ₐ[E] M) (algebraMap F M x))
    (iD : Rep.res r (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) ((W.under (𝓞 F)).adicCompletion F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ)
    (hiD : ∀ x : ((W.under (𝓞 F)).adicCompletion F)ˣ,
      ((Additive.toMul (iD.hom (Additive.ofMul x)) : (W.adicCompletion M)ˣ) : W.adicCompletion M) =
        HeightOneSpectrum.Extension.adicCompletionSemialgHom F M (⟨W, rfl⟩ : (W.under (𝓞 F)).Extension (𝓞 M)) (x : (W.under (𝓞 F)).adicCompletion F))
    (n : ℕ) (y : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) n) :
    (groupCohomology.map (NumberField.PlaceDecomp.decomp E M W).subtype prM n).hom
        ((groupCohomology.map (ι.toMonoidHom.comp (QuotientGroup.mk' S)) J n).hom y) =
      (groupCohomology.map r iD n).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype prG n).hom y) := by

  have hgrp : (ι.toMonoidHom.comp (QuotientGroup.mk' S)).comp (NumberField.PlaceDecomp.decomp E M W).subtype =
      (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype.comp r := by
    ext σ x
    apply (algebraMap F M).injective
    change algebraMap F M (ι (QuotientGroup.mk (σ : M ≃ₐ[E] M)) x) =
      algebraMap F M (((r σ : ↥(NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F)))) : F ≃ₐ[E] F) x)
    rw [hι, hr]

  have h1 := congrArg (fun T => T.hom y)
    (groupCohomology.map_comp (ι.toMonoidHom.comp (QuotientGroup.mk' S)) (NumberField.PlaceDecomp.decomp E M W).subtype J prM n)
  have h2 := congrArg (fun T => T.hom y)
    (groupCohomology.map_comp (NumberField.PlaceDecomp.decomp E F (W.under (𝓞 F))).subtype r prG iD n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [← h1, ← h2]

  refine congrArg
    (fun (T : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) n ⟶
        groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E M W)) (W.adicCompletion M)ˣ) n) => T.hom y)
    (map_eq_map_of_hom_eq hgrp _ _ (fun a => ?_) n)
  obtain ⟨x, rfl⟩ : ∃ x : (AdeleRing (𝓞 F) F)ˣ, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
  change prM.hom (J.hom (Additive.ofMul x)) = iD.hom (prG.hom (Additive.ofMul x))
  rw [hJ]
  erw [hprM, hprG]
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_ofMul, coe_finPart_apply]
  erw [hiD]
  rfl

end S_M4aHerbrand_map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower
end P2MW
export P2MW.S_M4aHerbrand_map_decomp_map_ideles_eq_map_map_decomp_under_of_isScalarTower (solution)
