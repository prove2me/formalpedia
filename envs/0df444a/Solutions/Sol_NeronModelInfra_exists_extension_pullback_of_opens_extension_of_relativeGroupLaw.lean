-- Prove2me | solution 1 for NeronModelInfra.exists_extension_pullback_of_opens_extension_of_relativeGroupLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0d560a4c-91ab-570e-a0e9-9fab4e19de8f

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_extension_pullback_of_opens_extension_of_relativeGroupLaw
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [(Ideal.span {(p : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(p : ℤ)})]
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [Smooth g] [IsSeparated g] [QuasiCompact g]
    (L : RelativeGroupLaw ℤ g)
    (η : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))))
    (hη : (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base η = IsLocalRing.closedPoint R)
    (hirr : ∀ x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))),
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x = IsLocalRing.closedPoint R → η ⤳ x)
    (φη : SchemeHomOver (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))))
    (φK : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶
      pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (θ : pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ⟶
      pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
    (hθ₁ : θ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) =
      pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫
        pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hθ₂ : θ ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) =
      pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))))
    (hφ : φK ≫ θ = θ ≫ φη.1)
    (V : (pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).Opens)
    (v : (V : Scheme.{0}) ⟶ pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hv : v ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) =
      V.ι ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
    (hVη : ∀ x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))),
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hηV : η ∈ V)
    (hle : Set.range (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))).base ⊆ Set.range V.ι.base)
    (hlift : IsOpenImmersion.lift V.ι
        (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
          (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))) hle ≫ v =
      φK ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))) :
    ∃ gA : pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) ⟶ G,
      gA ≫ g = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) ≫ g ∧
      ∀ j : pullback g (specGenericFibreInclusion ℤ ℚ) ⟶
          pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))),
        j ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) =
          pullback.fst g (specGenericFibreInclusion ℤ ℚ) →
        j ≫ gA = φη.1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ) := by
  classical

  haveI : Mono (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) := by
    haveI : Epi (CommRingCat.ofHom (algebraMap ℤ R)) :=
      IsLocalization.epi (Ideal.span {(p : ℤ)}).primeCompl R
    haveI : Scheme.Spec.IsRightAdjoint := ⟨_, ⟨ΓSpec.adjunction⟩⟩
    show Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap ℤ R)).op)
    infer_instance
  haveI : Mono (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) := pullback.fst_of_mono

  have hVs : ∀ Z ∈ irreducibleComponents
      {x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) // (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V := by
    intro Z hZ
    let ηS : {x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) // (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x = IsLocalRing.closedPoint R} := ⟨η, hη⟩
    have hgen : closure ({ηS} : Set {x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) // (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x = IsLocalRing.closedPoint R}) =
        Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      rw [← specializes_iff_mem_closure, subtype_specializes_iff]
      exact hirr y.1 y.2
    have huniv : IsIrreducible
        (Set.univ : Set {x : ↥(pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) // (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))).base x = IsLocalRing.closedPoint R}) := by
      rw [← hgen]
      exact isIrreducible_singleton.closure
    exact ⟨ηS, hZ.2 huniv (Set.subset_univ Z) (Set.mem_univ _), hηV⟩

  obtain ⟨W, d, hd⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension R (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) V hVη hVs ⟨v, hv⟩
  obtain ⟨φp, hφp⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension R
      (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) V hVη hVs ⟨v, hv⟩ W d hd

  refine ⟨φp.1 ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))), ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, φp.2]

  have hφp' : V.ι ≫ φp.1 = v := hφp
  have hres : pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫ φp.1 = φK ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) := by
    rw [← hlift, ← hφp', ← Category.assoc, IsOpenImmersion.lift_fac]

  have hιQ : (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) = (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (Subsingleton.elim _ _)

  intro j hj
  change pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ⟶ _ at j
  change j ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) at hj
  show j ≫ φp.1 ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) = φη.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
  have hjg : j ≫ (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) = pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))]
    calc (j ≫ (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))
        = j ≫ ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) ≫ g) := by rw [Category.assoc, pullback.condition]
      _ = (j ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))) ≫ g := (Category.assoc _ _ _).symm
      _ = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ≫ g := by rw [hj]
      _ = pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) := pullback.condition
      _ = (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))) := by rw [Category.assoc, hιQ]
  let κ : pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ⟶ pullback (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) := pullback.lift j (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) hjg
  have hκ1 : κ ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) = j := pullback.lift_fst _ _ _
  have hκ2 : κ ≫ pullback.snd (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) = pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) := pullback.lift_snd _ _ _
  have hκθ : κ ≫ θ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hθ₁, ← Category.assoc, hκ1, Category.id_comp, hj]
    · rw [Category.assoc, hθ₂, hκ2, Category.id_comp]
  calc j ≫ φp.1 ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R))))
      = κ ≫ (pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ))) ≫ φp.1) ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) := by rw [← hκ1]; simp only [Category.assoc]
    _ = κ ≫ (φK ≫ pullback.fst (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) (Spec.map (CommRingCat.ofHom (algebraMap R ℚ)))) ≫ (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))) := by rw [hres]
    _ = κ ≫ φK ≫ (θ ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))) := by rw [hθ₁]; simp only [Category.assoc]
    _ = (κ ≫ θ) ≫ φη.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) := by
        rw [← Category.assoc φK θ, hφ]; simp only [Category.assoc]
    _ = φη.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) := by rw [hκθ, Category.id_comp]

end S_NeronModelInfra_exists_extension_pullback_of_opens_extension_of_relativeGroupLaw
end P2MW
export P2MW.S_NeronModelInfra_exists_extension_pullback_of_opens_extension_of_relativeGroupLaw (solution)
