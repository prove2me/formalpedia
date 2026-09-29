-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_comparison_isPullback_smooth_of_glued
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/768fb7fe-e52c-5e59-8d5d-cd518c19ac17

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
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_comparison_isPullback_smooth_of_glued

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

namespace E162RG3c

end E162RG3c

theorem solution
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)
    (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of B)) (ιU : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ X)
    (hX : (∀ i, IsOpenImmersion (ιU i)) ∧
      (∀ i, ιU i ≫ fX = (𝒰.U i).ι ≫ D₀.f) ∧
      (∀ x : X, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ιU i).base y = x) ∧
      (∀ s : 𝒰.Idx 1,
        D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ιU (s.1 0) = (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιU (s.1 1)) ∧
      (∀ (i j : 𝒰.ι) (y : ↑(𝒰.U i)) (y' : ↑(𝒰.U j)),
        (ιU i).base y = (ιU j).base y' ↔ (𝒰.U i).ι.base y = (𝒰.U j).ι.base y')) :
    ∃ gX : A₁ ⟶ X,
      (∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιU i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ gX) ∧
      IsPullback gX f₁ fX (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) ∧
      Smooth fX := by
  classical
  obtain ⟨hopen, hover, hsurj, hglue, hpts⟩ := hX
  haveI := hopen
  have hsm : ∀ {i j : 𝒰.ι}, i < j → StrictMono ![i, j] := fun {i j} hij =>
    Fin.strictMono_iff_lt_succ.mpr (fun k => by fin_cases k; simpa using hij)
  have hinter : ∀ s : 𝒰.Idx 1, 𝒰.inter s = 𝒰.U (s.1 0) ⊓ 𝒰.U (s.1 1) := fun s =>
    le_antisymm (le_inf (𝒰.inter_le s 0) (𝒰.inter_le s 1))
      (le_iInf fun k => by fin_cases k <;> simp)

  let 𝒱 : A₁.OpenCover := Scheme.Cover.mkOfCovers 𝒰.ι (fun j => ↑(D₀.g ⁻¹ᵁ 𝒰.U j))
    (fun j => (D₀.g ⁻¹ᵁ 𝒰.U j).ι)
    (fun a => by
      have ha : D₀.g.base a ∈ (⊤ : D₀.A.Opens) := trivial
      rw [← 𝒰.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at ha
      obtain ⟨j, hj⟩ := ha
      exact ⟨j, ⟨a, hj⟩, rfl⟩)
  let φ : ∀ j : 𝒰.ι, (↑(D₀.g ⁻¹ᵁ 𝒰.U j) : Scheme.{0}) ⟶ X := fun j => (D₀.g ∣_ 𝒰.U j) ≫ ιU j

  have key : ∀ (s : 𝒰.Idx 1) {P : Scheme.{0}}
      (a : P ⟶ ↑(D₀.g ⁻¹ᵁ 𝒰.U (s.1 0))) (b : P ⟶ ↑(D₀.g ⁻¹ᵁ 𝒰.U (s.1 1))),
      a ≫ (D₀.g ⁻¹ᵁ 𝒰.U (s.1 0)).ι = b ≫ (D₀.g ⁻¹ᵁ 𝒰.U (s.1 1)).ι → a ≫ φ (s.1 0) = b ≫ φ (s.1 1) := by
    intro s P a b hab
    have hrange : Set.range (a ≫ (D₀.g ⁻¹ᵁ 𝒰.U (s.1 0)).ι).base ⊆ Set.range (D₀.g ⁻¹ᵁ 𝒰.inter s).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      have hi : (a ≫ (D₀.g ⁻¹ᵁ 𝒰.U (s.1 0)).ι) p ∈ D₀.g ⁻¹ᵁ 𝒰.U (s.1 0) := by
        rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]; exact (a p).2
      have hj : (a ≫ (D₀.g ⁻¹ᵁ 𝒰.U (s.1 0)).ι) p ∈ D₀.g ⁻¹ᵁ 𝒰.U (s.1 1) := by
        rw [hab, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]; exact (b p).2
      show (a ≫ (D₀.g ⁻¹ᵁ 𝒰.U (s.1 0)).ι) p ∈ D₀.g ⁻¹ᵁ 𝒰.inter s
      rw [hinter s, Scheme.Hom.preimage_inf]
      exact ⟨hi, hj⟩
    let q₀ : P ⟶ ↑(D₀.g ⁻¹ᵁ 𝒰.inter s) := IsOpenImmersion.lift (D₀.g ⁻¹ᵁ 𝒰.inter s).ι _ hrange
    have hq₀ : q₀ ≫ (D₀.g ⁻¹ᵁ 𝒰.inter s).ι = a ≫ (D₀.g ⁻¹ᵁ 𝒰.U (s.1 0)).ι :=
      IsOpenImmersion.lift_fac _ _ _
    obtain ⟨q, hqdef⟩ : ∃ q : P ⟶ ↑(𝒰.inter s), q = q₀ ≫ (D₀.g ∣_ 𝒰.inter s) := ⟨_, rfl⟩
    have hq : q ≫ (𝒰.inter s).ι = a ≫ (D₀.g ⁻¹ᵁ 𝒰.U (s.1 0)).ι ≫ D₀.g := by
      rw [hqdef, Category.assoc, morphismRestrict_ι, ← Category.assoc, hq₀, Category.assoc]
    have hA : a ≫ (D₀.g ∣_ 𝒰.U (s.1 0)) = q ≫ D₀.A.homOfLE (𝒰.inter_le s 0) := by
      rw [← cancel_mono (𝒰.U (s.1 0)).ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, hq]
    have hB : b ≫ (D₀.g ∣_ 𝒰.U (s.1 1)) = q ≫ D₀.A.homOfLE (𝒰.inter_le s 1) := by
      rw [← cancel_mono (𝒰.U (s.1 1)).ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι, hq]
      rw [← Category.assoc, ← hab, Category.assoc]
    have hC : q ≫ (τ s).hom = q := by
      rw [hqdef, Category.assoc, hτg s]
    calc a ≫ φ (s.1 0) = q ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ιU (s.1 0) := by
          simp only [φ, ← Category.assoc, hA]
      _ = q ≫ (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιU (s.1 1) := by rw [hglue s]
      _ = q ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιU (s.1 1) := by rw [← Category.assoc, hC]
      _ = b ≫ φ (s.1 1) := by simp only [φ, ← Category.assoc, hB]
  have hcompat : ∀ i j : 𝒰.ι, pullback.fst (𝒱.f i) (𝒱.f j) ≫ φ i = pullback.snd (𝒱.f i) (𝒱.f j) ≫ φ j := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact key ⟨![i, j], hsm hij⟩ _ _ pullback.condition
    · have : pullback.fst (𝒱.f i) (𝒱.f i) = pullback.snd (𝒱.f i) (𝒱.f i) := by
        rw [← cancel_mono (𝒱.f i)]; exact pullback.condition
      rw [this]
    · exact (key ⟨![j, i], hsm hji⟩ _ _ pullback.condition.symm).symm
  let gX : A₁ ⟶ X := 𝒱.glueMorphisms φ hcompat
  have hgX : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιU i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ gX := fun i =>
    (𝒱.ι_glueMorphisms φ hcompat i).symm

  let 𝒲X : X.OpenCover := Scheme.Cover.mkOfCovers 𝒰.ι (fun i => ↑(𝒰.U i)) ιU hsurj

  have hsmooth : Smooth fX := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) 𝒲X]
    intro i
    change Smooth (ιU i ≫ fX)
    rw [hover i]
    haveI := D₀.bundle.smooth
    infer_instance
  refine ⟨gX, hgX, ?_, hsmooth⟩

  apply Scheme.isPullback_of_openCover gX f₁ fX _ 𝒲X
  intro k
  have hK : IsPullback (D₀.g ∣_ 𝒰.U k) ((D₀.g ⁻¹ᵁ 𝒰.U k).ι ≫ f₁) ((𝒰.U k).ι ≫ D₀.f)
      (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) :=
    (isPullback_morphismRestrict D₀.g (𝒰.U k)).paste_vert D₀.cart
  have hpt : ∀ (j : 𝒰.ι) (a : ↥(D₀.g ⁻¹ᵁ 𝒰.U j)), gX ((D₀.g ⁻¹ᵁ 𝒰.U j).ι a) = ιU j ((D₀.g ∣_ 𝒰.U j) a) := by
    intro j a
    rw [← Scheme.Hom.comp_apply, ← hgX j, Scheme.Hom.comp_apply]
  have hres : ∀ (j : 𝒰.ι) (a : ↥(D₀.g ⁻¹ᵁ 𝒰.U j)), (𝒰.U j).ι ((D₀.g ∣_ 𝒰.U j) a) = D₀.g a.1 := by
    intro j a
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  have hrangeEq : Set.range (D₀.g ⁻¹ᵁ 𝒰.U k).ι.base
      = Set.range (pullback.fst gX (𝒲X.f k)).base := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    ext a
    constructor
    · intro ha
      exact ⟨(D₀.g ∣_ 𝒰.U k) ⟨a, ha⟩, (hpt k ⟨a, ha⟩).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨j, hj⟩ : ∃ j, D₀.g a ∈ 𝒰.U j := by
        have : D₀.g a ∈ (⊤ : D₀.A.Opens) := trivial
        rw [← 𝒰.iSup_eq_top, TopologicalSpace.Opens.mem_iSup] at this
        exact this
      have h1 : gX a = ιU j ((D₀.g ∣_ 𝒰.U j) ⟨a, hj⟩) := hpt j ⟨a, hj⟩
      have hy' : ιU k y = ιU j ((D₀.g ∣_ 𝒰.U j) ⟨a, hj⟩) := hy.trans h1
      have h2 := (hpts k j y ((D₀.g ∣_ 𝒰.U j) ⟨a, hj⟩)).mp hy'
      rw [hres j ⟨a, hj⟩] at h2
      have hmem : (𝒰.U k).ι y ∈ 𝒰.U k := by rw [Scheme.Opens.ι_apply]; exact y.2
      rw [h2] at hmem
      show D₀.g a ∈ 𝒰.U k
      exact hmem
  let e₁ : (↑(D₀.g ⁻¹ᵁ 𝒰.U k) : Scheme.{0}) ≅ pullback gX (𝒲X.f k) :=
    IsOpenImmersion.isoOfRangeEq (D₀.g ⁻¹ᵁ 𝒰.U k).ι (pullback.fst gX (𝒲X.f k)) hrangeEq
  have he₁ : e₁.hom ≫ pullback.fst gX (𝒲X.f k) = (D₀.g ⁻¹ᵁ 𝒰.U k).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  refine hK.of_iso e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change (D₀.g ∣_ 𝒰.U k) ≫ 𝟙 _ = e₁.hom ≫ pullback.snd gX (𝒲X.f k)
    have hc : pullback.snd gX (𝒲X.f k) ≫ ιU k = pullback.fst gX (𝒲X.f k) ≫ gX :=
      pullback.condition.symm
    rw [Category.comp_id, ← cancel_mono (ιU k)]
    change _ = e₁.hom ≫ (pullback.snd gX (𝒲X.f k) ≫ ιU k)
    rw [hc, ← Category.assoc, he₁]
    exact hgX k
  · change ((D₀.g ⁻¹ᵁ 𝒰.U k).ι ≫ f₁) ≫ 𝟙 _ = e₁.hom ≫ pullback.fst gX (𝒲X.f k) ≫ f₁
    rw [Category.comp_id, ← Category.assoc, he₁]
  · change ((𝒰.U k).ι ≫ D₀.f) ≫ 𝟙 _ = 𝟙 _ ≫ ιU k ≫ fX
    rw [Category.comp_id, Category.id_comp, hover k]
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

end S_GoodReductionJacobian_BareDeformation_exists_comparison_isPullback_smooth_of_glued
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_comparison_isPullback_smooth_of_glued (solution)
