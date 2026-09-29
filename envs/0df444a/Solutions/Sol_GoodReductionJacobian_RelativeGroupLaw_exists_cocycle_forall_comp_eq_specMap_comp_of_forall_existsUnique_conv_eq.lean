-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/65ef8ec6-1ce7-5b0f-b2ce-7d30c6f4c27b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

section torsorSchHelpers

open scoped TensorProduct

theorem torsorSch_exists_algHom {R P C : Type} [CommRing R] [CommRing P] [Algebra R P]
    [CommRing C] [Algebra R C]
    (q : Spec (CommRingCat.of P) ⟶ Spec (CommRingCat.of R))
    (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R P)))
    (m : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of P))
    (hm : m ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    ∃ a : P →ₐ[R] C, Spec.map (CommRingCat.ofHom a.toRingHom) = m := by
  subst hq
  let ψ := Spec.preimage m
  have hψ : Spec.map ψ = m := Spec.map_preimage m
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap R P) ≫ ψ) =
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
    rw [Spec.map_comp, hψ, hm]
  have h2 := Spec.map_injective h1
  have hcomm : ∀ r : R, ψ.hom (algebraMap R P r) = algebraMap R C r := by
    intro r
    have h3 := congrArg (fun f => f.hom r) h2
    simpa using h3
  refine ⟨⟨ψ.hom, hcomm⟩, ?_⟩
  show Spec.map (CommRingCat.ofHom ψ.hom) = m
  rw [CommRingCat.ofHom_hom, hψ]

theorem torsorSch_exists_iso {R P : Type} [CommRing R] [CommRing P] [Algebra R P]
    (q : Spec (CommRingCat.of P) ⟶ Spec (CommRingCat.of R))
    (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    ∃ e : pullback q q ≅ Spec (CommRingCat.of (P ⊗[R] P)),
      e.inv ≫ pullback.fst q q = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ∧
      e.inv ≫ pullback.snd q q =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : P →ₐ[R] P ⊗[R] P)) := by
  subst hq
  exact ⟨pullbackSpecIso R P P, pullbackSpecIso_inv_fst R P P, pullbackSpecIso_inv_snd R P P⟩

theorem torsorSch_point {R : Type} [CommRing R]
    (H : Type) [CommRing H] [Bialgebra R H]
    (H_W : Type) [CommRing H_W] [Bialgebra R H_W] (π : H →ₐc[R] H_W)
    (P : Type) [CommRing P] [Algebra R P] (qa : H →ₐ[R] P)
    (htors : ∀ (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C),
      ∃! c : H_W →ₐ[R] C,
        WithConv.toConv (a.comp qa) =
          WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa))
    (q : Spec (CommRingCat.of P) ⟶ Spec (CommRingCat.of R))
    (e : pullback q q ≅ Spec (CommRingCat.of (P ⊗[R] P)))
    (he1 : e.inv ≫ pullback.fst q q = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (he2 : e.inv ≫ pullback.snd q q =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : P →ₐ[R] P ⊗[R] P)))
    (cU : H_W →ₐ[R] P ⊗[R] P)
    (hcU : WithConv.toConv ((Algebra.TensorProduct.includeLeft : P →ₐ[R] P ⊗[R] P).comp qa) =
      WithConv.toConv (cU.comp (π : H →ₐ[R] H_W)) *
        WithConv.toConv ((Algebra.TensorProduct.includeRight : P →ₐ[R] P ⊗[R] P).comp qa))
    (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C) (c : H_W →ₐ[R] C)
    (habc : WithConv.toConv (a.comp qa) =
      WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa))
    (ab : Spec (CommRingCat.of C) ⟶ pullback q q)
    (ha : ab ≫ pullback.fst q q = Spec.map (CommRingCat.ofHom a.toRingHom))
    (hb : ab ≫ pullback.snd q q = Spec.map (CommRingCat.ofHom b.toRingHom)) :
    ab ≫ e.hom ≫ Spec.map (CommRingCat.ofHom cU.toRingHom) = Spec.map (CommRingCat.ofHom c.toRingHom) := by
  let θ : P ⊗[R] P →ₐ[R] C := Algebra.TensorProduct.lift a b (fun x y => Commute.all _ _)

  have hθ : ab ≫ e.hom = Spec.map (CommRingCat.ofHom θ.toRingHom) := by
    rw [← cancel_mono e.inv, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, he1, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ha]
      congr 2
      ext x
      simp [θ]
    · rw [Category.assoc, he2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]
      congr 2
      ext x
      simp [θ]

  have hrel : WithConv.toConv (a.comp qa) =
      WithConv.toConv ((θ.comp cU).comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa) := by
    have hθL : θ.comp (Algebra.TensorProduct.includeLeft : P →ₐ[R] P ⊗[R] P) = a := by
      ext x
      simp [θ]
    have hθR : θ.comp (Algebra.TensorProduct.includeRight : P →ₐ[R] P ⊗[R] P) = b := by
      ext x
      simp [θ]
    have h1 := congrArg (fun w : WithConv (H →ₐ[R] P ⊗[R] P) => θ.comp w.ofConv) hcU
    simp only [AlgHom.comp_convMul_distrib, ← AlgHom.comp_assoc, hθL, hθR] at h1
    have h2 := congrArg WithConv.toConv h1
    rw [WithConv.toConv_ofConv] at h2
    exact h2
  have hθc : θ.comp cU = c := (htors C a b).unique hrel habc
  have hring : θ.toRingHom.comp cU.toRingHom = c.toRingHom := by
    rw [← hθc]; rfl
  rw [← Category.assoc, hθ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]

end torsorSchHelpers

theorem solution
    {R : Type} [CommRing R]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
    (H : Type) [CommRing H] [Bialgebra R H]
    (H_W : Type) [CommRing H_W] [Bialgebra R H_W] (π : H →ₐc[R] H_W)
    (P : Type) [CommRing P] [Algebra R P] (qa : H →ₐ[R] P)
    (htors : ∀ (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C),
      ∃! c : H_W →ₐ[R] C,
        WithConv.toConv (a.comp qa) =
          WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa))
    (u : Spec (CommRingCat.of H_W) ⟶ N) (hu : u ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R H_W)))
    (hmul : ∀ (C : Type) [CommRing C] [Algebra R C] (φ ψ : H_W →ₐ[R] C)
        (x y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R C))) gN),
      x.1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ u →
      y.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ u →
      (L.mul _ x y).1 =
        Spec.map (CommRingCat.ofHom (WithConv.ofConv (WithConv.toConv φ * WithConv.toConv ψ)).toRingHom) ≫ u)
    (q : Spec (CommRingCat.of P) ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R P))) :
    ∃ g : SchemeHomOver (pullback.fst q q ≫ q) gN,
      L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g)
        (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
          (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
                Category.assoc, ← pullback.condition (f := q) (g := q)]) g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
          (by
            simp only [Category.assoc]
            rw [← pullback.condition (f := q) (g := q),
              ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
              ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
              ← pullback.condition (f := q) (g := q)]))
        (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g ∧
      ∀ (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C) (c : H_W →ₐ[R] C),
        WithConv.toConv (a.comp qa) =
          WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa) →
        ∀ ab : Spec (CommRingCat.of C) ⟶ pullback q q,
          ab ≫ pullback.fst q q = Spec.map (CommRingCat.ofHom a.toRingHom) →
          ab ≫ pullback.snd q q = Spec.map (CommRingCat.ofHom b.toRingHom) →
          ab ≫ g.1 = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ u := by
  classical
  obtain ⟨cU, hcU⟩ := (htors (TensorProduct R P P)
    (Algebra.TensorProduct.includeLeft : P →ₐ[R] TensorProduct R P P)
    (Algebra.TensorProduct.includeRight : P →ₐ[R] TensorProduct R P P)).exists
  obtain ⟨e, he1, he2⟩ := torsorSch_exists_iso q hq

  let g1 : pullback q q ⟶ N := e.hom ≫ Spec.map (CommRingCat.ofHom cU.toRingHom) ≫ u
  have hg1 : g1 ≫ gN = pullback.fst q q ≫ q := by
    have hcUalg : cU.toRingHom.comp (algebraMap R H_W) = algebraMap R (TensorProduct R P P) :=
      RingHom.ext fun r => cU.commutes r
    have halg : Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap R P) =
        algebraMap R (TensorProduct R P P) := by
      ext r
      simp [Algebra.TensorProduct.algebraMap_apply]
    simp only [g1, Category.assoc]
    rw [hu, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcUalg, ← cancel_epi e.inv, e.inv_hom_id_assoc,
      ← Category.assoc, he1, hq, ← Spec.map_comp, ← CommRingCat.ofHom_comp, halg]

  have hpts : ∀ (C : Type) [CommRing C] [Algebra R C] (a b : P →ₐ[R] C) (c : H_W →ₐ[R] C),
      WithConv.toConv (a.comp qa) =
        WithConv.toConv (c.comp (π : H →ₐ[R] H_W)) * WithConv.toConv (b.comp qa) →
      ∀ ab : Spec (CommRingCat.of C) ⟶ pullback q q,
        ab ≫ pullback.fst q q = Spec.map (CommRingCat.ofHom a.toRingHom) →
        ab ≫ pullback.snd q q = Spec.map (CommRingCat.ofHom b.toRingHom) →
        ab ≫ g1 = Spec.map (CommRingCat.ofHom c.toRingHom) ≫ u := by
    intro C _ _ a b c habc ab ha hb
    have hP := torsorSch_point H H_W π P qa htors q e he1 he2 cU hcU C a b c habc ab ha hb
    show ab ≫ (e.hom ≫ Spec.map (CommRingCat.ofHom cU.toRingHom) ≫ u) = _
    rw [← Category.assoc e.hom, ← Category.assoc ab, hP]
  refine ⟨⟨g1, hg1⟩, ?_, hpts⟩

  haveI : IsAffine (pullback (pullback.snd q q) (pullback.fst q q)) := inferInstance
  obtain ⟨Γ3, em, hiso⟩ : ∃ (Γ3 : CommRingCat.{0}) (em : Spec Γ3 ⟶ pullback (pullback.snd q q) (pullback.fst q q)), IsIso em :=
    ⟨_, (pullback (pullback.snd q q) (pullback.fst q q)).isoSpec.inv, inferInstance⟩
  let φ0 : CommRingCat.of R ⟶ Γ3 := Spec.preimage (em ≫ (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q)))
  letI : Algebra R Γ3 := φ0.hom.toAlgebra
  have hem : em ≫ (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q)) = Spec.map (CommRingCat.ofHom (algebraMap R Γ3)) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]

  have hm1 : (em ≫ pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R Γ3)) := by
    rw [← hem]; simp only [Category.assoc]
  have hm2 : (em ≫ pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q) ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R Γ3)) := by
    rw [← hem]; simp only [Category.assoc]; rw [← pullback.condition]
  have hm3 : (em ≫ pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q) ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R Γ3)) := by
    rw [← hem]; simp only [Category.assoc]
    rw [← pullback.condition, ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)), ← pullback.condition, Category.assoc,
      ← pullback.condition]
  obtain ⟨a1, ha1⟩ := torsorSch_exists_algHom q hq (em ≫ pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) hm1
  obtain ⟨a2, ha2⟩ := torsorSch_exists_algHom q hq (em ≫ pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q) hm2
  obtain ⟨a3, ha3⟩ := torsorSch_exists_algHom q hq (em ≫ pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q) hm3
  obtain ⟨c12, hc12⟩ := (htors Γ3 a1 a2).exists
  obtain ⟨c23, hc23⟩ := (htors Γ3 a2 a3).exists

  have hc13 : WithConv.toConv (a1.comp qa) =
      WithConv.toConv ((WithConv.ofConv (WithConv.toConv c12 * WithConv.toConv c23)).comp (π : H →ₐ[R] H_W)) *
        WithConv.toConv (a3.comp qa) := by
    rw [AlgHom.convMul_comp_bialgHom_distrib, WithConv.toConv_ofConv, hc12, hc23, mul_assoc]

  have hg12 : (em ≫ pullback.fst (pullback.snd q q) (pullback.fst q q)) ≫ g1 = Spec.map (CommRingCat.ofHom c12.toRingHom) ≫ u :=
    hpts _ a1 a2 c12 hc12 _ (by rw [Category.assoc, ha1]) (by rw [Category.assoc, ha2])
  have hg23 : (em ≫ pullback.snd (pullback.snd q q) (pullback.fst q q)) ≫ g1 = Spec.map (CommRingCat.ofHom c23.toRingHom) ≫ u :=
    hpts _ a2 a3 c23 hc23 _ (by rw [Category.assoc, ← pullback.condition, ha2]) (by rw [Category.assoc, ha3])
  have hg13 : (em ≫ pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q) (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
      (by
        simp only [Category.assoc]
        rw [← pullback.condition (f := q) (g := q),
          ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
          ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
          ← pullback.condition (f := q) (g := q)])) ≫ g1 =
      Spec.map (CommRingCat.ofHom (WithConv.ofConv (WithConv.toConv c12 * WithConv.toConv c23)).toRingHom) ≫ u :=
    hpts _ a1 a3 _ hc13 _ (by rw [Category.assoc, pullback.lift_fst, ha1])
      (by rw [Category.assoc, pullback.lift_snd, ha3])

  have h12 : (schemeHomOverComp em hem (schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl ⟨g1, hg1⟩)).1 =
      Spec.map (CommRingCat.ofHom c12.toRingHom) ≫ u := by
    show em ≫ (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ g1) = _
    rw [← Category.assoc]; exact hg12
  have h23 : (schemeHomOverComp em hem (schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
      (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
            Category.assoc, ← pullback.condition (f := q) (g := q)]) ⟨g1, hg1⟩)).1 =
      Spec.map (CommRingCat.ofHom c23.toRingHom) ≫ u := by
    show em ≫ (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ g1) = _
    rw [← Category.assoc]; exact hg23
  have hL := congrArg Subtype.val (L.mul_natural (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q)) _ em hem (schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl ⟨g1, hg1⟩) (schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q))
      (by rw [← Category.assoc, ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q),
            Category.assoc, ← pullback.condition (f := q) (g := q)]) ⟨g1, hg1⟩))
  rw [schemeHomOverComp_coe] at hL
  have hM := hmul _ c12 c23 _ _ h12 h23
  apply Subtype.ext
  rw [← cancel_epi em, hL, hM, ← hg13, Category.assoc]
  rfl

end S_GoodReductionJacobian_RelativeGroupLaw_exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_cocycle_forall_comp_eq_specMap_comp_of_forall_existsUnique_conv_eq (solution)
