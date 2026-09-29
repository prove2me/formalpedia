-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/305e99f8-0971-5dbc-9b6e-0e3c45716742

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mSepKer

theorem locallyQuasiFinite_of_etale {X Y : Scheme.{u}} (g : X ⟶ Y) [Etale g] : LocallyQuasiFinite g := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h : RingHom.Etale (g.appLE U V e).hom := HasRingHomProperty.appLE (P := @Etale) g inferInstance U V e
  algebraize [(g.appLE U V e).hom]
  show Algebra.QuasiFinite _ _
  infer_instance

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem isClosedImmersion_one (L : RelativeGroupLaw K f) [IsSeparated f] :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  have h : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f) := by
    rw [(L.one _).2]; infer_instance
  exact IsClosedImmersion.of_comp (L.one (𝟙 (Spec (CommRingCat.of K)))).1 f

theorem isClosedImmersion_endKerι (L : RelativeGroupLaw K f) [IsSeparated f] (β : SchemeHomOver f f) :
    IsClosedImmersion (L.endKerι β) := by
  haveI := isClosedImmersion_one L
  exact MorphismProperty.pullback_fst _ _ inferInstance

theorem isProper_endKerStr (L : RelativeGroupLaw K f) [IsProper f] (β : SchemeHomOver f f) :
    IsProper (L.endKerStr β) := by
  haveI := isClosedImmersion_endKerι L β
  rw [← RelativeGroupLaw.endKerι_comp_base]
  infer_instance

theorem isFinite_endKerStr (L : RelativeGroupLaw K f) [IsProper f] (β : SchemeHomOver f f)
    [Etale (L.endKerStr β)] : IsFinite (L.endKerStr β) := by
  haveI := isProper_endKerStr L β
  haveI := locallyQuasiFinite_of_etale (L.endKerStr β)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

abbrev KerPts (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) : Type u :=
  {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
    NeronModelInfra.schemeHomOverComp x β = L.one (𝟙 (Spec (CommRingCat.of K)))}

def kerPtsEquiv (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (L.endKerStr β) ≃ KerPts L β where
  toFun z := ⟨⟨z.1 ≫ L.endKerι β, by
      rw [Category.assoc, RelativeGroupLaw.endKerι_comp_base]; exact z.2⟩, by
      apply Subtype.ext
      change (z.1 ≫ L.endKerι β) ≫ β.1 = (L.one _).1
      rw [Category.assoc, RelativeGroupLaw.endKerι_comp, ← Category.assoc, z.2, Category.id_comp]⟩
  invFun x := ⟨pullback.lift x.1.1 (𝟙 _) (by
      have h := congrArg Subtype.val x.2
      change x.1.1 ≫ β.1 = (L.one _).1 at h
      rw [h, Category.id_comp]), by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _
      rw [pullback.lift_snd]⟩
  left_inv z := by
    apply Subtype.ext
    change pullback.lift (z.1 ≫ L.endKerι β) (𝟙 _) _ = z.1
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]; exact z.2.symm
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    change pullback.lift x.1.1 (𝟙 _) _ ≫ pullback.fst _ _ = x.1.1
    rw [pullback.lift_fst]

section Alg

variable (K : Type u) [Field K]

theorem evalAlgHom_bijective (I : Type u) [Fintype I] [DecidableEq I] :
    Function.Bijective (fun i : I => Pi.evalAlgHom K (fun _ : I => K) i) := by

  let e : I → (I → K) := fun i => Pi.single i 1
  have he : ∀ i k, e i k = if k = i then 1 else 0 := fun i k => by
    simp only [e, Pi.single_apply]
  constructor
  · intro i j hij
    by_contra hne
    have h := congrArg (fun ψ : (I → K) →ₐ[K] K => ψ (e i)) hij
    simp only [Pi.evalAlgHom_apply, he, if_neg (Ne.symm hne)] at h
    exact one_ne_zero h
  · intro ψ
    have hmul : ∀ i j, e i * e j = if i = j then e i else 0 := fun i j => by
      funext k
      simp only [Pi.mul_apply, he]
      split_ifs <;> simp_all
    have hsum1 : ∑ i, e i = 1 := by
      funext k
      rw [Finset.sum_apply, Pi.one_apply, Finset.sum_eq_single k]
      · rw [he, if_pos rfl]
      · intro i _ hik; rw [he, if_neg (Ne.symm hik)]
      · intro h; exact absurd (Finset.mem_univ k) h
    have hsum : ∑ i, ψ (e i) = 1 := by rw [← map_sum, hsum1, map_one]

    obtain ⟨i₀, hi₀⟩ : ∃ i₀, ψ (e i₀) ≠ 0 := by
      by_contra hall
      push Not at hall
      rw [Finset.sum_eq_zero (fun i _ => hall i)] at hsum
      exact zero_ne_one hsum
    have h1 : ψ (e i₀) = 1 := by
      have h : ψ (e i₀) * ψ (e i₀) = ψ (e i₀) * 1 := by rw [← map_mul, hmul, if_pos rfl, mul_one]
      exact mul_left_cancel₀ hi₀ h
    have h0 : ∀ i, i ≠ i₀ → ψ (e i) = 0 := fun i hi => by
      have h : ψ (e i) * ψ (e i₀) = 0 := by rw [← map_mul, hmul, if_neg hi, map_zero]
      rwa [h1, mul_one] at h
    refine ⟨i₀, ?_⟩
    apply AlgHom.ext
    intro v
    have hv : v = ∑ i, v i • e i := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [Pi.smul_apply, he, if_pos rfl, smul_eq_mul, mul_one]
      · intro i _ hik; rw [Pi.smul_apply, he, if_neg (Ne.symm hik), smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    change v i₀ = ψ v
    conv_rhs => rw [hv]
    rw [map_sum, Finset.sum_eq_single i₀]
    · rw [map_smul, h1, smul_eq_mul, mul_one]
    · intro i _ hi; rw [map_smul, h0 i hi, smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

variable [IsAlgClosed K]

theorem finite_and_natCard_algHom_eq_finrank (B : Type u) [CommRing B] [Algebra K B]
    [Algebra.FormallyEtale K B] [Module.Finite K B] :
    Finite (B →ₐ[K] K) ∧ Nat.card (B →ₐ[K] K) = Module.finrank K B := by
  classical
  obtain ⟨I, hI, Ai, _, _, e, hsep⟩ := (Algebra.FormallyEtale.iff_exists_algEquiv_prod K B).mp inferInstance

  have hAi : ∀ i, Function.Bijective (algebraMap K (Ai i)) := fun i => by
    haveI := hsep i
    haveI : Algebra.IsIntegral K (Ai i) := ⟨Algebra.IsSeparable.isIntegral K⟩
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ei : ∀ i, K ≃ₐ[K] Ai i := fun i => AlgEquiv.ofBijective (Algebra.ofId K (Ai i)) (hAi i)
  let e' : B ≃ₐ[K] (I → K) := e.trans (AlgEquiv.piCongrRight fun i => (ei i).symm)
  haveI := Fintype.ofFinite I
  let E : (B →ₐ[K] K) ≃ I :=
    (AlgEquiv.arrowCongr e' (AlgEquiv.refl : K ≃ₐ[K] K)).trans
      (Equiv.ofBijective _ (evalAlgHom_bijective K I)).symm
  refine ⟨Finite.of_equiv I E.symm, ?_⟩
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, ← Module.finrank_fintype_fun_eq_card K,
    LinearEquiv.finrank_eq e'.toLinearEquiv]

end Alg

section Count

variable {K : Type u} [Field K]

theorem finite_and_natCard_schemeHomOver_eq_finrank [IsAlgClosed K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] [Etale g] :
    Finite (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) g) ∧
      Nat.card (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) g) = g.finrank (IsLocalRing.closedPoint K) := by
  haveI : IsAffine Z := isAffine_of_isAffineHom g

  set ψ : CommRingCat.of K ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop with hψ
  have hg : g = Z.isoSpec.hom ≫ Spec.map ψ := by
    rw [hψ, Spec.map_comp, Scheme.isoSpec_hom_naturality_assoc, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have hSpec : Spec.map ψ = Z.isoSpec.inv ≫ g := by rw [hg, Iso.inv_hom_id_assoc]
  haveI : IsFinite (Spec.map ψ) := by rw [hSpec]; infer_instance
  haveI : Etale (Spec.map ψ) := by rw [hSpec]; infer_instance
  have hfin : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).mp inferInstance
  have het : ψ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance
  have hflat : ψ.hom.Flat := Flat.SpecMap_iff.mp inferInstance

  letI alg : Algebra K Γ(Z, ⊤) := ψ.hom.toAlgebra
  haveI : Algebra.Etale K Γ(Z, ⊤) := het
  haveI : Module.Finite K Γ(Z, ⊤) := hfin

  have hrank : g.finrank (IsLocalRing.closedPoint K) = Module.finrank K Γ(Z, ⊤) := by
    have h1 : g.finrank = (Spec.map ψ).finrank := by
      rw [hg]; exact Scheme.Hom.finrank_comp_left_of_isIso _ _
    rw [h1, Scheme.Hom.finrank_SpecMap_eq_finrank hfin hflat]
    change (letI := ψ.hom.toAlgebra; Module.rankAtStalk (R := K) Γ(Z, ⊤)) (IsLocalRing.closedPoint K) = _
    rw [Module.rankAtStalk_eq_finrank_of_free]
    rfl

  have E1 : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) g ≃
      {χ : Γ(Z, ⊤) ⟶ CommRingCat.of K // ψ ≫ χ = 𝟙 _} :=
    { toFun := fun x => ⟨Spec.preimage (x.1 ≫ Z.isoSpec.hom), by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage, Category.assoc, ← hg, x.2, Spec.map_id]⟩
      invFun := fun χ => ⟨Spec.map χ.1 ≫ Z.isoSpec.inv, by
        rw [Category.assoc, ← hSpec, ← Spec.map_comp, χ.2, Spec.map_id]⟩
      left_inv := fun x => Subtype.ext (by
        change Spec.map (Spec.preimage (x.1 ≫ Z.isoSpec.hom)) ≫ Z.isoSpec.inv = x.1
        rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id])
      right_inv := fun χ => Subtype.ext (by
        change Spec.preimage ((Spec.map χ.1 ≫ Z.isoSpec.inv) ≫ Z.isoSpec.hom) = χ.1
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Spec.preimage_map]) }
  have E2 : {χ : Γ(Z, ⊤) ⟶ CommRingCat.of K // ψ ≫ χ = 𝟙 _} ≃ (Γ(Z, ⊤) →ₐ[K] K) :=
    { toFun := fun χ =>
        { toRingHom := χ.1.hom
          commutes' := fun k => by
            have h := congrArg (fun η => η.hom k) χ.2
            simp [CommRingCat.hom_comp] at h
            exact h }
      invFun := fun a => ⟨CommRingCat.ofHom a.toRingHom, by
        ext k
        change a (ψ.hom k) = k
        exact a.commutes k⟩
      left_inv := fun χ => Subtype.ext (by ext b; rfl)
      right_inv := fun a => by ext b; rfl }
  obtain ⟨hF, hcard⟩ := finite_and_natCard_algHom_eq_finrank K Γ(Z, ⊤)
  refine ⟨Finite.of_equiv _ (E1.trans E2).symm, ?_⟩
  rw [Nat.card_congr (E1.trans E2), hcard, hrank]

end Count

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem main [IsAlgClosed K] [IsProper f] (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [Etale (L.endKerStr β)] :
    IsFinite (L.endKerStr β) ∧ Finite (KerPts L β) ∧ Nat.card (KerPts L β) = L.endDegree β := by
  haveI := isFinite_endKerStr L β
  obtain ⟨hF, hcard⟩ := finite_and_natCard_schemeHomOver_eq_finrank (L.endKerStr β)
  refine ⟨inferInstance, Finite.of_equiv _ (kerPtsEquiv L β), ?_⟩
  rw [← Nat.card_congr (kerPtsEquiv L β), hcard, RelativeGroupLaw.endDegree_of_isFinite]

end P2mSepKer

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    [IsProper f]
    (L : RelativeGroupLaw K f) (β : SchemeHomOver f f) [Etale (L.endKerStr β)] :
    IsFinite (L.endKerStr β) ∧
      Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        NeronModelInfra.schemeHomOverComp x β = L.one (𝟙 (Spec (CommRingCat.of K)))} ∧
      Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        NeronModelInfra.schemeHomOverComp x β = L.one (𝟙 (Spec (CommRingCat.of K)))} = L.endDegree β :=
  P2mSepKer.main L β

end

end S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale (solution)
