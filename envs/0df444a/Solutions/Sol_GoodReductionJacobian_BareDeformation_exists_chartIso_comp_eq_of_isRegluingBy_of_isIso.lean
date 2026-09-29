-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_chartIso_comp_eq_of_isRegluingBy_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/14a003dd-8f51-5133-8edc-8406b973c2e9

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_chartIso_comp_eq_of_isRegluingBy_of_isIso

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

namespace E160PHIA

variable {B B₁ : Type} [CommRing B] [CommRing B₁] [Algebra B B₁]
  {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}

theorem chart_base_eq (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (D₀ D D' : BareDeformation f₁ L₁ B) (U : D₀.A.Opens)
    (ιU : (U : Scheme.{0}) ⟶ D.A) (ιU' : (U : Scheme.{0}) ⟶ D'.A)
    (hg : (D₀.g ∣_ U) ≫ ιU = (D₀.g ⁻¹ᵁ U).ι ≫ D.g) (hg' : (D₀.g ∣_ U) ≫ ιU' = (D₀.g ⁻¹ᵁ U).ι ≫ D'.g)
    (e : D.A ≅ D'.A) (he : D.g ≫ e.hom = D'.g) (y : ↥(U : Scheme.{0})) :
    (ιU ≫ e.hom).base y = ιU'.base y := by
  obtain ⟨_, hsurj, _⟩ :=
    AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
      (algebraMap B B₁) hπ hker D₀.f f₁ D₀.g D₀.cart
  obtain ⟨x, hx⟩ := D₀.g.surjective (U.ι.base y)
  have hxU : x ∈ D₀.g ⁻¹ᵁ U := by
    change D₀.g.base x ∈ (U : Set _); rw [hx]; exact y.2

  have hy : (D₀.g ∣_ U).base ⟨x, hxU⟩ = y := by
    apply U.ι.isOpenEmbedding.injective
    change ((D₀.g ∣_ U) ≫ U.ι).base ⟨x, hxU⟩ = U.ι.base y
    rw [morphismRestrict_ι]; exact hx
  rw [← hy]
  change ((D₀.g ∣_ U) ≫ ιU ≫ e.hom).base ⟨x, hxU⟩ = ((D₀.g ∣_ U) ≫ ιU').base ⟨x, hxU⟩
  rw [← Category.assoc, hg, hg', Category.assoc, he]

end E160PHIA

theorem solution
    {B B₁ : Type} [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ D D' : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hD : D₀.IsRegluingBy 𝒰 τ D) (hD' : D₀.IsRegluingBy 𝒰 τ' D')
    (hiso : D.IsIso D') :
    ∃ (α : ∀ i : 𝒰.ι, ((↑(𝒰.U i) : Scheme.{0}) ≅ ↑(𝒰.U i)))
      (αr : ∀ (s : 𝒰.Idx 1) (_ : Fin 2), ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s))),
      (∀ i : 𝒰.ι, (α i).hom ≫ (𝒰.U i).ι ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f) ∧
      (∀ i : 𝒰.ι, (D₀.g ∣_ 𝒰.U i) ≫ (α i).hom = D₀.g ∣_ 𝒰.U i) ∧
      (∀ (s : 𝒰.Idx 1) (j : Fin 2),
        (αr s j).hom ≫ D₀.A.homOfLE (𝒰.inter_le s j) = D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).hom) ∧
      (∀ s : 𝒰.Idx 1, (αr s 0).hom ≫ (τ' s).hom = (τ s).hom ≫ (αr s 1).hom) := by
  obtain ⟨e, hef, heg⟩ := hiso
  obtain ⟨_, _, ι, hιo, hιf, _, hιg, hιgl⟩ := hD
  obtain ⟨_, _, ι', hιo', hιf', _, hιg', hιgl'⟩ := hD'
  haveI := hιo; haveI := hιo'

  have hpt : ∀ i (y : ↥(𝒰.U i)), (ι i ≫ e.hom).base y = (ι' i).base y := fun i y =>
    E160PHIA.chart_base_eq hπ hker D₀ D D' (𝒰.U i) (ι i) (ι' i) (hιg i) (hιg' i) e heg y
  have hrange : ∀ i, Set.range (ι i ≫ e.hom).base = Set.range (ι' i).base := by
    intro i; ext z; constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, (hpt i y).symm⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, hpt i y⟩
  let α : ∀ i : 𝒰.ι, ((↑(𝒰.U i) : Scheme.{0}) ≅ ↑(𝒰.U i)) := fun i =>
    IsOpenImmersion.isoOfRangeEq (ι i ≫ e.hom) (ι' i) (hrange i)
  have hα : ∀ i, (α i).hom ≫ ι' i = ι i ≫ e.hom := fun i =>
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

  have hαpt : ∀ i (y : ↥(𝒰.U i)), (α i).hom.base y = y := by
    intro i y
    apply (ι' i).isOpenEmbedding.injective
    change ((α i).hom ≫ ι' i).base y = (ι' i).base y
    rw [hα i]; exact hpt i y
  have hαr_range : ∀ (s : 𝒰.Idx 1) (j : Fin 2),
      Set.range (D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).hom).base =
        Set.range (D₀.A.homOfLE (𝒰.inter_le s j)).base := by
    intro s j
    ext z; constructor
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      change _ = (α (s.1 j)).hom.base ((D₀.A.homOfLE (𝒰.inter_le s j)).base w)
      rw [hαpt]
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      change (α (s.1 j)).hom.base ((D₀.A.homOfLE (𝒰.inter_le s j)).base w) = _
      rw [hαpt]
  let αr : ∀ (s : 𝒰.Idx 1) (_ : Fin 2), ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)) := fun s j =>
    IsOpenImmersion.isoOfRangeEq (D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).hom)
      (D₀.A.homOfLE (𝒰.inter_le s j)) (hαr_range s j)
  have hαr : ∀ (s : 𝒰.Idx 1) (j : Fin 2),
      (αr s j).hom ≫ D₀.A.homOfLE (𝒰.inter_le s j) = D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).hom :=
    fun s j => IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  refine ⟨α, αr, ?_, ?_, hαr, ?_⟩
  · intro i
    rw [← hιf' i, ← Category.assoc, hα i, Category.assoc, hef, hιf i]
    exact (hιf' i).symm
  · intro i
    rw [← cancel_mono (ι' i), Category.assoc, hα i, ← Category.assoc, hιg i, Category.assoc, heg, hιg' i]
  · intro s
    rw [← cancel_mono (D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι' (s.1 1))]
    calc ((αr s 0).hom ≫ (τ' s).hom) ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι' (s.1 1)
        = (αr s 0).hom ≫ (D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι' (s.1 0)) := by
          rw [hιgl' s, Category.assoc]
      _ = D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0) ≫ e.hom := by
          rw [← Category.assoc, hαr s 0, Category.assoc, hα]
      _ = (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1) ≫ e.hom := by
          rw [← Category.assoc, hιgl s, Category.assoc, Category.assoc]
      _ = ((τ s).hom ≫ (αr s 1).hom) ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι' (s.1 1) := by
          rw [← hα (s.1 1), ← Category.assoc (D₀.A.homOfLE _), ← hαr s 1]
          simp only [Category.assoc]

end S_GoodReductionJacobian_BareDeformation_exists_chartIso_comp_eq_of_isRegluingBy_of_isIso
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_chartIso_comp_eq_of_isRegluingBy_of_isIso (solution)
