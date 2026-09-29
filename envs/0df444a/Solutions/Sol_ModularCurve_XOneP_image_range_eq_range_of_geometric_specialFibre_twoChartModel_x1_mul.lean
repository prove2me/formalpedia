-- Prove2me | solution 1 for ModularCurve.XOneP.image_range_eq_range_of_geometric_specialFibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/27442e1c-178e-5b65-9485-4a0bb1e50032

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_image_range_eq_range_of_geometric_specialFibre_twoChartModel_x1_mul

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian TensorProduct"

namespace ECL_N3a

universe u

theorem eq_of_irreducible_cover {X : Type u} [TopologicalSpace X] {S₁ S₂ T₁ T₂ : Set X}
    (hS₁ : IsIrreducible S₁) (hS₂ : IsIrreducible S₂) (hT₂ : IsIrreducible T₂)
    (hS₁c : IsClosed S₁) (hS₂c : IsClosed S₂) (hT₁c : IsClosed T₁) (hT₂c : IsClosed T₂)
    (hScov : S₁ ∪ S₂ = Set.univ) (hTcov : T₁ ∪ T₂ = Set.univ)
    {e : X} (heS : e ∈ S₁ \ S₂) (heT : e ∈ T₁ \ T₂)
    (hne : ¬ S₂ ⊆ S₁) (hne' : ¬ T₂ ⊆ T₁) : S₂ = T₂ := by
  have hS₂T : S₂ ⊆ T₁ ∨ S₂ ⊆ T₂ :=
    (isPreirreducible_iff_isClosed_union_isClosed.mp hS₂.isPreirreducible) T₁ T₂ hT₁c hT₂c (hTcov ▸ Set.subset_univ _)
  have hS₁T : S₁ ⊆ T₁ ∨ S₁ ⊆ T₂ :=
    (isPreirreducible_iff_isClosed_union_isClosed.mp hS₁.isPreirreducible) T₁ T₂ hT₁c hT₂c (hTcov ▸ Set.subset_univ _)
  have hTS : T₂ ⊆ S₁ ∨ T₂ ⊆ S₂ :=
    (isPreirreducible_iff_isClosed_union_isClosed.mp hT₂.isPreirreducible) S₁ S₂ hS₁c hS₂c (hScov ▸ Set.subset_univ _)
  have hS₁T₁ : S₁ ⊆ T₁ := by
    rcases hS₁T with h | h
    · exact h
    · exact absurd (h heS.1) heT.2
  have hS₂T₂ : S₂ ⊆ T₂ := by
    rcases hS₂T with h | h
    · exfalso
      rcases hTS with h' | h'
      · exact hne' (h'.trans hS₁T₁)
      · exact hne' (h'.trans h)
    · exact h
  rcases hTS with h' | h'
  · exact absurd (hS₂T₂.trans h') hne
  · exact le_antisymm hS₂T₂ h'

end ECL_N3a

open ECL_N3a in

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
    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j)) (hε : Set.range ε.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)))
    (k : Type) [Field k] [IsAlgClosed k] (ι₀ : (AlgebraicClosure (IsLocalRing.ResidueField A)) →+* k)
    {C₁ C₂ : Scheme.{0}} [IrreducibleSpace ↥C₁] [IrreducibleSpace ↥C₂]
    (i₁ : C₁ ⟶ (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))))) (i₂ : C₂ ⟶ (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))))) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))), z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base)
    (hε : ((sectionFibrePoint ε (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))).1).base (IsLocalRing.closedPoint k) ∈ Set.range i₁.base \ Set.range i₂.base)
    (hne : ¬ Set.range i₂.base ⊆ Set.range i₁.base)
    {D₁ D₂ : Scheme.{0}} (d₁ : D₁ ⟶ Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A)))) (d₂ : D₂ ⟶ Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))))
    [GeometricallyIntegral d₁] [GeometricallyIntegral d₂]
    (j₁ : D₁ ⟶ (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))) (j₂ : D₂ ⟶ (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))) [IsClosedImmersion j₁] [IsClosedImmersion j₂]
    (hj₁ : j₁ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) = d₁) (hj₂ : j₂ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) = d₂)
    (hcover₀ : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))), z ∈ Set.range j₁.base ∨ z ∈ Set.range j₂.base)
    (hε₀ : ((sectionFibrePoint ε (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))).1).base (IsLocalRing.closedPoint (AlgebraicClosure (IsLocalRing.ResidueField A))) ∈ Set.range j₁.base \ Set.range j₂.base)
    (hne₀ : ¬ Set.range j₂.base ⊆ Set.range j₁.base) :
    (pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))) (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) (𝟙 _) (Spec.map (CommRingCat.ofHom ι₀)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])).base '' Set.range i₂.base = Set.range j₂.base := by
  classical

  set π := pullback.map (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))) (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) (𝟙 _) (Spec.map (CommRingCat.ofHom ι₀)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) with hπ
  have hsι : (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))) = Spec.map (CommRingCat.ofHom ι₀) ≫ (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) := by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have hπfst : π ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))) := by
    rw [hπ, pullback.lift_fst, Category.comp_id]
  have hπsnd : π ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))) ≫ Spec.map (CommRingCat.ofHom ι₀) := by
    rw [hπ, pullback.lift_snd]
  have hB : IsPullback (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))) π (Spec.map (CommRingCat.ofHom ι₀)) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))) := by
    refine IsPullback.of_bot ?_ hπsnd.symm (IsPullback.of_hasPullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))).flip
    rw [hπfst, ← hsι]
    exact (IsPullback.of_hasPullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))).flip

  haveI : Surjective (Spec.map (CommRingCat.ofHom ι₀)) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  haveI hπsurj : Surjective π := MorphismProperty.of_isPullback hB inferInstance

  set T₁ : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))) := π.base ⁻¹' Set.range j₁.base with hT₁
  set T₂ : Set ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))) := π.base ⁻¹' Set.range j₂.base with hT₂
  have hT₁c : IsClosed T₁ := (j₁.isClosedEmbedding.isClosed_range).preimage π.continuous
  have hT₂c : IsClosed T₂ := (j₂.isClosedEmbedding.isClosed_range).preimage π.continuous
  have hTcov : T₁ ∪ T₂ = Set.univ := by
    ext z; simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true, hT₁, hT₂]; exact hcover₀ _

  have hQ : IsPullback (pullback.snd j₂ π ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))) (pullback.fst j₂ π)
      (Spec.map (CommRingCat.ofHom ι₀)) d₂ := by
    have h1 : IsPullback (pullback.snd j₂ π) (pullback.fst j₂ π) π j₂ := (IsPullback.of_hasPullback j₂ π).flip
    have h2 := h1.paste_horiz hB
    rwa [hj₂] at h2
  haveI : IsIntegral (pullback d₂ (Spec.map (CommRingCat.ofHom ι₀))) := inferInstance
  haveI : IrreducibleSpace ↥(pullback j₂ π) := by
    let e := hQ.isoPullback ≪≫ pullbackSymmetry _ _
    haveI : Nonempty ↥(pullback j₂ π) := ⟨e.inv.base (Nonempty.some inferInstance)⟩
    haveI : IsIntegral (pullback j₂ π) := isIntegral_of_isOpenImmersion e.hom
    infer_instance
  have hT₂irr : IsIrreducible T₂ := by
    have : T₂ = Set.range (pullback.snd j₂ π).base := by rw [hT₂, Scheme.Pullback.range_snd]
    rw [this]
    rw [← Set.image_univ]; exact (IrreducibleSpace.isIrreducible_univ _).image _ (pullback.snd j₂ π).continuous.continuousOn

  have hεπ : (sectionFibrePoint ε (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))).1 ≫ π = Spec.map (CommRingCat.ofHom ι₀) ≫ (sectionFibrePoint ε (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hπfst, Category.assoc]
      show pullback.lift ((Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))) ≫ ε.1) (𝟙 _) _ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom ι₀) ≫ pullback.lift ((Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) ≫ ε.1) (𝟙 _) _ ≫ pullback.fst _ _
      rw [pullback.lift_fst, pullback.lift_fst, ← Category.assoc, ← hsι]
    · rw [Category.assoc, hπsnd, Category.assoc]
      show pullback.lift ((Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))) ≫ ε.1) (𝟙 _) _ ≫ pullback.snd _ _ ≫ _ = Spec.map (CommRingCat.ofHom ι₀) ≫ pullback.lift ((Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))) ≫ ε.1) (𝟙 _) _ ≫ pullback.snd _ _
      rw [← Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp, Category.comp_id]
  have hεpt : π.base (((sectionFibrePoint ε (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))).1).base (IsLocalRing.closedPoint k)) =
      ((sectionFibrePoint ε (Spec.map (CommRingCat.ofHom ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A))))).1).base (IsLocalRing.closedPoint (AlgebraicClosure (IsLocalRing.ResidueField A))) := by
    rw [← Scheme.Hom.comp_apply, hεπ, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  have heT : ((sectionFibrePoint ε (Spec.map (CommRingCat.ofHom (ι₀.comp ((algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A))).comp (IsLocalRing.residue A)))))).1).base (IsLocalRing.closedPoint k) ∈ T₁ \ T₂ := by
    rw [hT₁, hT₂, Set.mem_diff, Set.mem_preimage, Set.mem_preimage, hεpt]
    exact hε₀

  have hne' : ¬ T₂ ⊆ T₁ := by
    intro h
    apply hne₀
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hπsurj.1 (j₂.base y)
    have hz₂ : z ∈ T₂ := by rw [hT₂, Set.mem_preimage, hz]; exact ⟨y, rfl⟩
    have := h hz₂
    rw [hT₁, Set.mem_preimage, hz] at this
    exact this

  have hS : Set.range i₂.base = T₂ :=
    eq_of_irreducible_cover (by rw [← Set.image_univ]; exact (IrreducibleSpace.isIrreducible_univ _).image _ i₁.continuous.continuousOn) (by rw [← Set.image_univ]; exact (IrreducibleSpace.isIrreducible_univ _).image _ i₂.continuous.continuousOn) hT₂irr
      i₁.isClosedEmbedding.isClosed_range i₂.isClosedEmbedding.isClosed_range hT₁c hT₂c
      (Set.eq_univ_of_forall fun z => hcover z) hTcov hε heT hne hne'
  show π.base '' Set.range i₂.base = Set.range j₂.base
  rw [hS, hT₂, Set.image_preimage_eq _ hπsurj.1]

end S_ModularCurve_XOneP_image_range_eq_range_of_geometric_specialFibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_image_range_eq_range_of_geometric_specialFibre_twoChartModel_x1_mul (solution)
