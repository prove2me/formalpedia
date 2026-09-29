-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_residueField_point_solutionScheme_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/084cb9f2-bf61-52d5-9b3b-3c6428ae7265

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_IsLocalRing_free_and_forall_sub_mem_maximalIdeal_and_isLocalRing_tensorProduct
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_schemeHomOverComp_lift_self_eq_one_of_cocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_residueField_point_solutionScheme_of_cocycle

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace PushTrivKpt

theorem exists_specMap_residueField_comp_eq_of_forall_sub_mem_maximalIdeal
    (R : Type) [CommRing R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    (hres : ∀ x : R', ∃ a : R, x - algebraMap R R' a ∈ IsLocalRing.maximalIdeal R') :
    ∃ σ : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R'),
      σ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) =
        Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) := by
  let φ : IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField R' := IsLocalRing.ResidueField.map (algebraMap R R')
  have hφres : ∀ r : R, φ (IsLocalRing.residue R r) = IsLocalRing.residue R' (algebraMap R R' r) := fun r => rfl
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := hres x
    refine ⟨IsLocalRing.residue R a, ?_⟩
    rw [hφres, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_sub]
    exact (IsLocalRing.maximalIdeal R').neg_mem ha
  let e : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField R' := RingEquiv.ofBijective φ hφ
  let ψ : R' →+* IsLocalRing.ResidueField R := e.symm.toRingHom.comp (IsLocalRing.residue R')
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  change e.symm (IsLocalRing.residue R' (algebraMap R R' r)) = algebraMap R (IsLocalRing.ResidueField R) r
  rw [← hφres]
  exact e.symm_apply_apply (IsLocalRing.residue R r)

end PushTrivKpt

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    {N : Scheme.{0}} (gN : N ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R gN)
    (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalRing R'] [Module.Finite R R'] [Module.Free R R']
    (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (hq : q = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (A₀ : Type) [CommRing A₀] [Algebra R A₀] [Algebra.FiniteType R A₀]
    (j : Spec (CommRingCat.of A₀) ⟶ N) [IsOpenImmersion j] (hj : j ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R A₀)))
    (g : SchemeHomOver (pullback.fst q q ≫ q) gN)
    (hg : L.mul (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q))
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
        (by rw [← Category.assoc, pullback.lift_fst, Category.assoc]) g)
    (hunit : Set.range (L.one (𝟙 (Spec (CommRingCat.of R)))).1.base ⊆ Set.range j.base)
    (P : Scheme.{0}) (gP : P ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver (pullback.fst q gP ≫ q) gN)
    (hsol : (Set.range u.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.fst q q) (𝟙 P) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) u) = (L.mul (pullback.fst (pullback.fst q q ≫ q) gP ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) gP) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) gP q gP (pullback.snd q q) (𝟙 P) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) u))))
    (huniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of R)) (h : SchemeHomOver (pullback.fst q t ≫ q) gN),
        (Set.range h.1.base ⊆ Set.range j.base ∧
          Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h)).1.base ⊆ Set.range j.base ∧
          (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.fst q q) (𝟙 T) (𝟙 _) (by simp) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc]) h) = (L.mul (pullback.fst (pullback.fst q q ≫ q) t ≫ pullback.fst q q ≫ q) (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) t) rfl g) (GoodReductionJacobian.schemeHomOverComp
            (pullback.map (pullback.fst q q ≫ q) t q t (pullback.snd q q) (𝟙 T) (𝟙 _)
              (by simp [pullback.condition]) (by simp))
            (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h))) →
        ∃! x : SchemeHomOver t gP, (GoodReductionJacobian.schemeHomOverComp
              (pullback.map q t q gP (𝟙 _) x.1 (𝟙 _) (by simp) (by simpa using x.2.symm))
              (by rw [pullback.lift_fst_assoc, Category.comp_id]) u) = h) :
    ∃ x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ P,
      x₀ ≫ gP = Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) := by
  classical

  let κ := IsLocalRing.ResidueField R
  let tκ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R κ))

  haveI : Nontrivial R' := inferInstance
  haveI : FaithfulSMul R R' := inferInstance
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI : IsLocalHom (algebraMap R R') := inferInstance
  have hres := (IsLocalRing.free_and_forall_sub_mem_maximalIdeal_and_isLocalRing_tensorProduct R R').2.1
  obtain ⟨σ₀, hσ₀'⟩ := PushTrivKpt.exists_specMap_residueField_comp_eq_of_forall_sub_mem_maximalIdeal R R' hres
  have hσ₀ : σ₀ ≫ q = tκ := by rw [hq]; exact hσ₀'

  let σ : Spec (CommRingCat.of κ) ⟶ pullback q tκ := pullback.lift σ₀ (𝟙 _) (by rw [hσ₀, Category.id_comp])
  have hσ₁ : σ ≫ pullback.fst q tκ = σ₀ := pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ pullback.snd q tκ = 𝟙 _ := pullback.lift_snd _ _ _
  have hone : ∀ z : ↥(pullback q tκ), z = σ.base (IsLocalRing.closedPoint κ) := by

    haveI : IsClosedImmersion tκ :=
      IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (algebraMap R κ)) IsLocalRing.residue_surjective
    haveI : IsClosedImmersion (pullback.fst q tκ) := MorphismProperty.pullback_fst _ _ inferInstance
    have hinj : Function.Injective (pullback.fst q tκ).base := (pullback.fst q tκ).isClosedEmbedding.injective
    have hfib : ∀ z : ↥(pullback q tκ), (pullback.fst q tκ).base z = IsLocalRing.closedPoint R' := by
      intro z

      have h1 : q.base ((pullback.fst q tκ).base z) = IsLocalRing.closedPoint R := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
        have : tκ.base ((pullback.snd q tκ).base z) = IsLocalRing.closedPoint R := by
          rw [Subsingleton.elim ((pullback.snd q tκ).base z) (IsLocalRing.closedPoint κ)]
          apply PrimeSpectrum.ext
          change Ideal.comap (algebraMap R κ) (IsLocalRing.closedPoint κ).asIdeal = IsLocalRing.maximalIdeal R
          rw [IsLocalRing.closedPoint]
          change Ideal.comap (IsLocalRing.residue R) (IsLocalRing.maximalIdeal κ) = _
          rw [IsLocalRing.maximalIdeal_eq_bot (R := κ), ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
        exact this

      have hqb : q.base ((pullback.fst q tκ).base z) =
          (Spec.map (CommRingCat.ofHom (algebraMap R R'))).base ((pullback.fst q tκ).base z) :=
        congrArg (fun q' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) => q'.base ((pullback.fst q tκ).base z)) hq
      have h2 : Ideal.comap (algebraMap R R') ((pullback.fst q tκ).base z).asIdeal = IsLocalRing.maximalIdeal R :=
        congrArg PrimeSpectrum.asIdeal (hqb.symm.trans h1)
      apply PrimeSpectrum.ext
      have hmax : ((pullback.fst q tκ).base z).asIdeal.IsMaximal :=
        Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (h2 ▸ IsLocalRing.maximalIdeal.isMaximal R)
      exact IsLocalRing.eq_maximalIdeal hmax
    intro z
    apply hinj
    rw [hfib, hfib]

  have hmc : pullback.fst q tκ ≫ q = (pullback.snd q tκ ≫ σ₀) ≫ q := by rw [Category.assoc, hσ₀, pullback.condition]
  let m : pullback q tκ ⟶ pullback q q := pullback.lift (pullback.fst q tκ) (pullback.snd q tκ ≫ σ₀) hmc
  have hm₁ : m ≫ pullback.fst q q = pullback.fst q tκ := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd q q = pullback.snd q tκ ≫ σ₀ := pullback.lift_snd _ _ _
  have hm : m ≫ (pullback.fst q q ≫ q) = pullback.fst q tκ ≫ q := by rw [← Category.assoc, hm₁]
  let h₀ : SchemeHomOver (pullback.fst q tκ ≫ q) gN := GoodReductionJacobian.schemeHomOverComp m hm g

  have hwc : (pullback.fst (pullback.fst q q ≫ q) tκ ≫ pullback.snd q q) ≫ q = (pullback.snd (pullback.fst q q ≫ q) tκ ≫ σ₀) ≫ q := by
    rw [Category.assoc, Category.assoc, hσ₀, ← pullback.condition (f := pullback.fst q q ≫ q) (g := tκ),
      ← pullback.condition (f := q) (g := q)]
  let w : pullback (pullback.fst q q ≫ q) tκ ⟶ pullback q q :=
    pullback.lift (pullback.fst (pullback.fst q q ≫ q) tκ ≫ pullback.snd q q) (pullback.snd (pullback.fst q q ≫ q) tκ ≫ σ₀) hwc
  have hw₁ : w ≫ pullback.fst q q = pullback.fst (pullback.fst q q ≫ q) tκ ≫ pullback.snd q q := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd q q = pullback.snd (pullback.fst q q ≫ q) tκ ≫ σ₀ := pullback.lift_snd _ _ _
  have hεc : pullback.fst (pullback.fst q q ≫ q) tκ ≫ pullback.snd q q = w ≫ pullback.fst q q := hw₁.symm
  let ε : pullback (pullback.fst q q ≫ q) tκ ⟶ pullback (pullback.snd q q) (pullback.fst q q) :=
    pullback.lift (pullback.fst (pullback.fst q q ≫ q) tκ) w hεc
  have hε₁ : ε ≫ pullback.fst (pullback.snd q q) (pullback.fst q q) = pullback.fst (pullback.fst q q ≫ q) tκ := pullback.lift_fst _ _ _
  have hε₂ : ε ≫ pullback.snd (pullback.snd q q) (pullback.fst q q) = w := pullback.lift_snd _ _ _
  have hε : ε ≫ (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ (pullback.fst q q ≫ q)) =
      pullback.fst (pullback.fst q q ≫ q) tκ ≫ pullback.fst q q ≫ q := by rw [← Category.assoc, hε₁]

  have hleg₂ : pullback.map (pullback.fst q q ≫ q) tκ q tκ (pullback.snd q q) (𝟙 _) (𝟙 _)
      (by simp [pullback.condition]) (by simp) ≫ m = w := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm₁, pullback.lift_fst, hw₁]
    · rw [Category.assoc, hm₂, ← Category.assoc, pullback.lift_snd, Category.comp_id, hw₂]
  have hleg₁ : pullback.map (pullback.fst q q ≫ q) tκ q tκ (pullback.fst q q) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ m =
      ε ≫ pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q)
        (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q)
        (by
          simp only [Category.assoc]
          rw [← pullback.condition (f := q) (g := q), ← Category.assoc (pullback.snd (pullback.snd q q) (pullback.fst q q)),
            ← pullback.condition (f := pullback.snd q q) (g := pullback.fst q q), Category.assoc,
            ← pullback.condition (f := q) (g := q)]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm₁, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hε₁]
    · rw [Category.assoc, hm₂, ← Category.assoc, pullback.lift_snd, Category.comp_id, Category.assoc, pullback.lift_snd,
        ← Category.assoc, hε₂, hw₂]

  have E := congrArg (GoodReductionJacobian.schemeHomOverComp ε hε) hg
  rw [L.mul_natural _ (pullback.fst (pullback.fst q q ≫ q) tκ ≫ pullback.fst q q ≫ q) ε hε] at E
  have hA : GoodReductionJacobian.schemeHomOverComp ε hε
      (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.snd q q) (pullback.fst q q)) rfl g) =
      GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) tκ) rfl g := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe]
    rw [← Category.assoc, hε₁]
  have hB : ∀ e₁, GoodReductionJacobian.schemeHomOverComp ε hε
      (GoodReductionJacobian.schemeHomOverComp (pullback.snd (pullback.snd q q) (pullback.fst q q)) e₁ g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) tκ q tκ (pullback.snd q q) (𝟙 _) (𝟙 _) (by simp [pullback.condition]) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h₀ := by
    intro e₁
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, h₀]
    rw [← Category.assoc, hε₂, ← hleg₂, Category.assoc]
  have hC : ∀ (e₀) (e₁), GoodReductionJacobian.schemeHomOverComp ε hε
      (GoodReductionJacobian.schemeHomOverComp
        (pullback.lift (pullback.fst (pullback.snd q q) (pullback.fst q q) ≫ pullback.fst q q)
          (pullback.snd (pullback.snd q q) (pullback.fst q q) ≫ pullback.snd q q) e₀) e₁ g) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) tκ q tκ (pullback.fst q q) (𝟙 _) (𝟙 _) (by simp) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc]) h₀ := by
    intro e₀ e₁
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, h₀]
    rw [← Category.assoc, ← hleg₁, Category.assoc]
  rw [hA, hB, hC] at E
  have c3 := E.symm

  have hδ : σ ≫ m = pullback.lift σ₀ σ₀ rfl := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm₁, hσ₁, pullback.lift_fst]
    · rw [Category.assoc, hm₂, ← Category.assoc, hσ₂, Category.id_comp, pullback.lift_snd]
  have hval : σ ≫ h₀.1 = (σ₀ ≫ q) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
    have hdu := GoodReductionJacobian.RelativeGroupLaw.schemeHomOverComp_lift_self_eq_one_of_cocycle gN L q g hg σ₀
    have h1 : σ ≫ h₀.1 = (pullback.lift σ₀ σ₀ rfl) ≫ g.1 := by
      change σ ≫ (m ≫ g.1) = _
      rw [← Category.assoc, hδ]
    have h2 : (pullback.lift σ₀ σ₀ rfl) ≫ g.1 = (L.one (σ₀ ≫ q)).1 := by
      have := congrArg Subtype.val hdu
      simpa only [GoodReductionJacobian.schemeHomOverComp_coe] using this
    have h3 : (L.one (σ₀ ≫ q)).1 = (σ₀ ≫ q) ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
      have := congrArg Subtype.val (L.one_natural (𝟙 _) (σ₀ ≫ q) (σ₀ ≫ q) (Category.comp_id _))
      simpa only [GoodReductionJacobian.schemeHomOverComp_coe] using this.symm
    rw [h1, h2, h3]
  have c1 : Set.range h₀.1.base ⊆ Set.range j.base := by
    rintro _ ⟨z, rfl⟩
    rw [hone z, ← Scheme.Hom.comp_apply, hval, Scheme.Hom.comp_apply]
    exact hunit ⟨_, rfl⟩

  have c2 : Set.range (L.mul (pullback.fst (pullback.fst q q ≫ q) tκ ≫ pullback.fst q q ≫ q)
      (GoodReductionJacobian.schemeHomOverComp (pullback.fst (pullback.fst q q ≫ q) tκ) rfl g)
      (GoodReductionJacobian.schemeHomOverComp
        (pullback.map (pullback.fst q q ≫ q) tκ q tκ (pullback.snd q q) (𝟙 _) (𝟙 _) (by simp [pullback.condition]) (by simp))
        (by rw [pullback.lift_fst_assoc, Category.assoc, ← pullback.condition]) h₀)).1.base ⊆ Set.range j.base := by
    rw [← c3]
    rintro _ ⟨z, rfl⟩
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply]
    exact c1 ⟨_, rfl⟩

  obtain ⟨x, hx, -⟩ := huniv _ tκ h₀ ⟨c1, c2, c3⟩
  exact ⟨x.1, x.2⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_residueField_point_solutionScheme_of_cocycle
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_residueField_point_solutionScheme_of_cocycle (solution)
