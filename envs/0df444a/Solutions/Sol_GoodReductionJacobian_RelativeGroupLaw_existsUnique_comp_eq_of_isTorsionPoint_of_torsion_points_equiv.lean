-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.existsUnique_comp_eq_of_isTorsionPoint_of_torsion_points_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bbd233d5-3325-50e3-8032-9d84387f68c2

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_isTorsionPoint_of_torsion_points_equiv

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) (hflat : Flat (L.schemeNsmul n))
    (H : Type u) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    (e : ∀ (T : Type u) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type u) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (z : SchemeHomOver t f) (hz : L.IsTorsionPoint t n z) :
    ∃! g : T ⟶ Spec (CommRingCat.of H), g ≫ (e H (.toConv (AlgHom.id K H))).val.1 = z.1 := by

  let N := L.schemeNsmul n
  let o₁ : Spec (CommRingCat.of K) ⟶ A := (L.one (𝟙 (Spec (CommRingCat.of K)))).1
  let Ker := L.schemeKer n
  let ι : Ker ⟶ A := pullback.fst N o₁
  let kstr : Ker ⟶ Spec (CommRingCat.of K) := pullback.snd N o₁
  let u : Spec (CommRingCat.of H) ⟶ A := (e H (.toConv (AlgHom.id K H))).val.1

  have nsmul_coe : ∀ {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t' f),
      (L.nsmul t' n x).1 = x.1 ≫ N := by
    intro T' t' x
    have hx : x = GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) := by
      apply Subtype.ext
      show x.1 = x.1 ≫ 𝟙 A
      rw [Category.comp_id]
    conv_lhs => rw [hx]
    rw [← L.nsmul_natural f t' x.1 x.2 n (RelativeGroupLaw.idPoint (f := f))]
    rfl
  have one_coe : ∀ {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of K)), (L.one t').1 = t' ≫ o₁ := by
    intro T' t'
    rw [← L.one_natural (𝟙 _) t' t' (Category.comp_id _)]
    rfl

  haveI : IsAffine Ker := isAffine_of_isAffineHom kstr
  let σ : Ker ≅ Spec Γ(Ker, ⊤) := Ker.isoSpec
  letI algB : Algebra K Γ(Ker, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ kstr.appTop).hom.toAlgebra
  have hσ : σ.inv ≫ kstr = Spec.map (CommRingCat.ofHom (algebraMap K Γ(Ker, ⊤))) := by
    rw [← Scheme.isoSpec_inv_naturality kstr, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hιf : ι ≫ f = kstr := by
    have h1 : ι ≫ N ≫ f = kstr ≫ o₁ ≫ f := by rw [← Category.assoc, pullback.condition, Category.assoc]
    rw [L.schemeNsmul_over] at h1
    rw [h1, (L.one (𝟙 (Spec (CommRingCat.of K)))).2, Category.comp_id]

  let κ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Γ(Ker, ⊤)))) f :=
    ⟨σ.inv ≫ ι, by rw [Category.assoc, hιf, hσ]⟩
  have hκ : L.IsTorsionPoint _ n κ := by
    show L.nsmul _ n κ = L.one _
    apply Subtype.ext
    rw [nsmul_coe, one_coe]
    show (σ.inv ≫ ι) ≫ N = Spec.map (CommRingCat.ofHom (algebraMap K Γ(Ker, ⊤))) ≫ o₁
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ]

  let β : H →ₐ[K] Γ(Ker, ⊤) := ((e Γ(Ker, ⊤)).symm ⟨κ, hκ⟩).ofConv
  have hβ : σ.inv ≫ ι = Spec.map (CommRingCat.ofHom β.toRingHom) ≫ u := by
    have h := he_nat H Γ(Ker, ⊤) β (.toConv (AlgHom.id K H))
    rw [AlgHom.comp_id] at h
    have h' : (e Γ(Ker, ⊤)) (WithConv.toConv β) = ⟨κ, hκ⟩ := Equiv.apply_symm_apply _ _
    rw [h'] at h
    exact h

  have hu' : u ≫ N = Spec.map (CommRingCat.ofHom (algebraMap K H)) ≫ o₁ := by
    rw [← nsmul_coe _ (e H (.toConv (AlgHom.id K H))).val, ← one_coe]
    exact congrArg Subtype.val (e H (.toConv (AlgHom.id K H))).property
  let gu : Spec (CommRingCat.of H) ⟶ Ker := pullback.lift u (Spec.map (CommRingCat.ofHom (algebraMap K H))) hu'
  have hgu : gu ≫ ι = u := pullback.lift_fst _ _ _
  have hgu₂ : gu ≫ kstr = Spec.map (CommRingCat.ofHom (algebraMap K H)) := pullback.lift_snd _ _ _
  have hβK : Spec.map (CommRingCat.ofHom β.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap K H)) =
      σ.inv ≫ kstr := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, β.comp_algebraMap, hσ]
  have hinv₁ : (σ.hom ≫ Spec.map (CommRingCat.ofHom β.toRingHom)) ≫ gu = 𝟙 Ker := by
    apply pullback.hom_ext
    · rw [Category.assoc, hgu, Category.id_comp, Category.assoc, ← hβ, Iso.hom_inv_id_assoc]
    · rw [Category.assoc, hgu₂, Category.id_comp, Category.assoc, hβK, Iso.hom_inv_id_assoc]
  have hinv₂ : gu ≫ (σ.hom ≫ Spec.map (CommRingCat.ofHom β.toRingHom)) = 𝟙 _ := by
    let γr : CommRingCat.of H ⟶ CommRingCat.of H :=
      Spec.preimage (gu ≫ σ.hom ≫ Spec.map (CommRingCat.ofHom β.toRingHom))
    have hγr : Spec.map γr = gu ≫ σ.hom ≫ Spec.map (CommRingCat.ofHom β.toRingHom) := Spec.map_preimage _
    have hγK : CommRingCat.ofHom (algebraMap K H) ≫ γr = CommRingCat.ofHom (algebraMap K H) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hγr, Category.assoc, Category.assoc, hβK, Iso.hom_inv_id_assoc, hgu₂]
    let γ : H →ₐ[K] H := AlgHom.mk γr.hom fun k => by
      have := congrArg (fun φ => φ.hom k) hγK
      simpa using this
    have hγ : γ = AlgHom.id K H := by
      have h := he_nat H H γ (.toConv (AlgHom.id K H))
      rw [AlgHom.comp_id] at h
      have h2 : Spec.map (CommRingCat.ofHom γ.toRingHom) = gu ≫ σ.hom ≫ Spec.map (CommRingCat.ofHom β.toRingHom) := hγr
      rw [h2, Category.assoc, Category.assoc, ← hβ, Iso.hom_inv_id_assoc, hgu] at h

      have h3 : e H (.toConv γ) = e H (.toConv (AlgHom.id K H)) := by
        apply Subtype.ext; apply Subtype.ext; exact h
      exact WithConv.toConv_injective ((e H).injective h3)
    rw [← hγr]
    have : γr = 𝟙 _ := by
      ext x
      exact congrArg (fun φ : H →ₐ[K] H => φ x) hγ
    rw [this, Spec.map_id]
  haveI : IsIso gu := ⟨⟨σ.hom ≫ Spec.map (CommRingCat.ofHom β.toRingHom), hinv₂, hinv₁⟩⟩
  haveI : Mono o₁ := ⟨fun g h w => by
    have w' := congrArg (fun φ => φ ≫ f) w
    simp only [Category.assoc] at w'
    rw [(L.one (𝟙 (Spec (CommRingCat.of K)))).2, Category.comp_id, Category.comp_id] at w'
    exact w'⟩
  haveI : Mono ι := inferInstance
  haveI : Mono u := by rw [← hgu]; exact mono_comp _ _

  have hz' : z.1 ≫ N = t ≫ o₁ := by
    rw [← nsmul_coe t z, ← one_coe t, hz]
  let g₀ : T ⟶ Ker := pullback.lift z.1 t hz'
  have hsol : (g₀ ≫ σ.hom ≫ Spec.map (CommRingCat.ofHom β.toRingHom)) ≫ u = z.1 := by
    rw [Category.assoc, Category.assoc, ← hβ, Iso.hom_inv_id_assoc]
    exact pullback.lift_fst _ _ _
  refine ⟨g₀ ≫ σ.hom ≫ Spec.map (CommRingCat.ofHom β.toRingHom), hsol, ?_⟩
  intro g hg
  rw [← cancel_mono u, hsol]
  exact hg

end S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_isTorsionPoint_of_torsion_points_equiv
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_comp_eq_of_isTorsionPoint_of_torsion_points_equiv (solution)
