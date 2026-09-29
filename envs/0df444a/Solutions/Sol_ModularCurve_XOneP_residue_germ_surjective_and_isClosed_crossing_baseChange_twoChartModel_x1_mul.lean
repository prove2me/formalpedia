-- Prove2me | solution 1 for ModularCurve.XOneP.residue_germ_surjective_and_isClosed_crossing_baseChange_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/569f9c23-0338-59b7-9e67-b459bc2ee36a

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_residue_germ_surjective_and_isClosed_crossing_baseChange_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

set_option autoImplicit false

p2m_attr_erase "instance" "IsScalarTower.of_algHom"

universe u

noncomputable section

namespace E4R1_CrossRat

theorem residue_germ_surjective_of_field (K : Type u) [Field K] (pt : Spec (CommRingCat.of K)) :
    Function.Surjective fun k : K => IsLocalRing.residue ((Spec (CommRingCat.of K)).presheaf.stalk pt)
      ((Spec (CommRingCat.of K)).presheaf.germ ⊤ pt trivial ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k)) := by
  letI : Algebra (CommRingCat.of K) ((Spec (CommRingCat.of K)).presheaf.stalk pt) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of K) pt
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of K)).presheaf.stalk pt) pt.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of K) pt
  have hpt : pt.asIdeal = ⊥ := by
    haveI : pt.asIdeal.IsPrime := pt.isPrime
    exact Ideal.eq_bot_of_prime _
  have hbij : Function.Bijective (algebraMap (CommRingCat.of K) ((Spec (CommRingCat.of K)).presheaf.stalk pt)) := by
    refine IsField.localization_map_bijective (M := pt.asIdeal.primeCompl) ?_ (Field.toIsField K)
    intro h0
    exact h0 (by rw [hpt]; exact Ideal.zero_mem _)
  intro z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨k, rfl⟩ := hbij.2 w
  exact ⟨k, rfl⟩

theorem residue_germ_surjective_and_isClosed {O : Type u} [CommRing O] [IsLocalRing O] {X : Scheme.{u}}
    (π : X ⟶ Spec (CommRingCat.of O))
    (s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ X)
    (hs : s ≫ π = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :
    (Function.Surjective fun o : O => IsLocalRing.residue (X.presheaf.stalk (s.base (IsLocalRing.closedPoint _)))
      (X.presheaf.germ ⊤ (s.base (IsLocalRing.closedPoint _)) trivial (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)))) ∧
    IsClosed ({s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))} : Set X) := by
  set k₀ := IsLocalRing.ResidueField O
  set pt : Spec (CommRingCat.of k₀) := IsLocalRing.closedPoint k₀
  set x := s.base pt
  constructor
  · intro z
    let w := s.residueFieldMap pt z
    obtain ⟨k, hk⟩ := residue_germ_surjective_of_field k₀ pt w
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective k
    refine ⟨o, (s.residueFieldMap pt).hom.injective ?_⟩
    change (X.residue x ≫ s.residueFieldMap pt) (X.presheaf.germ ⊤ x trivial (π.appTop _)) = w
    rw [Scheme.residue_residueFieldMap, CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap_apply]
    rw [← hk]
    change IsLocalRing.residue _ _ = IsLocalRing.residue _ _
    congr 2
    change (s.appTop (π.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))) =
      (Scheme.ΓSpecIso (CommRingCat.of k₀)).inv (IsLocalRing.residue O o)
    rw [← CommRingCat.comp_apply _ s.appTop, ← Scheme.Hom.comp_appTop, hs]
    exact (congrArg (fun φ => φ.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))).symm
  · haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    let s' := pullback.lift s (𝟙 _) (by rw [hs, Category.id_comp])
    have hsec : s' ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) = 𝟙 _ := pullback.lift_snd _ _ _
    haveI : IsClosedImmersion s' := isClosedImmersion_of_comp_eq_id _ s' hsec
    haveI : IsClosedImmersion (pullback.fst π (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    have hs' : s = s' ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    haveI : IsClosedImmersion s := by rw [hs']; infer_instance
    have hrange : Set.range s.base = {x} := by
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨q, rfl⟩
        rw [Subsingleton.elim q pt]
      · rintro rfl; exact ⟨pt, rfl⟩
    rw [← hrange]
    exact s.isClosedEmbedding.isClosed_range

end E4R1_CrossRat

end

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (hrat : ∀ x : ↥(pullback i₁.1 i₂.1),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)),
        s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
        s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base x)
    (ν : ↥(pullback i₁.1 i₂.1)) :
    (Function.Surjective fun o : O => IsLocalRing.residue ((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν)) ((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ ((pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν) trivial ((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)))) ∧
    IsClosed ({(pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν} : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))) := by
  obtain ⟨s, hs1, hs2⟩ := hrat ν
  rw [← hs2]
  exact E4R1_CrossRat.residue_germ_surjective_and_isClosed _ s hs1

end S_ModularCurve_XOneP_residue_germ_surjective_and_isClosed_crossing_baseChange_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_residue_germ_surjective_and_isClosed_crossing_baseChange_twoChartModel_x1_mul (solution)
