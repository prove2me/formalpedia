-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_orderedAffineCover_unit_chart_frame_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/7eab080c-c6ed-539a-ad14-3123fffcd754

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
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_unit_chart_frame_bare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] :
    ∃ (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι)
      (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)) (_ : e₀ ≫ (𝒰.U i₀).ι = (D₀.L.one (𝟙 _)).1)
      (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
      (_ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
      (_ : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))
      (σ : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)) ≃+* Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s)),
      (∀ (s : 𝒰.Idx 1) (x : Γ(D₀.A, 𝒰.inter s)),
        letI := algebraOfHom D₀.f (𝒰.inter s)
        σ s ((1 : (ResidueField B)) ⊗ₜ[B] x) =
          ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE (𝒰.baseChange_inter_le D₀.f (ResidueField B) s)).op).hom
            (((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)).hom x)) ∧
      (∀ (s : 𝒰.Idx 1) (a : (ResidueField B)),
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
        σ s (a ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) = algebraMap (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) a) := by
  classical
  haveI : IsProper D₀.f := D₀.bundle.proper
  haveI : CompactSpace ↥D₀.A := QuasiCompact.compactSpace_of_compactSpace D₀.f

  have hxU : ∃ U₀ : D₀.A.affineOpens, (D₀.L.one (𝟙 _)).1.base (IsLocalRing.closedPoint B) ∈ (U₀ : D₀.A.Opens) := by
    have hx : (D₀.L.one (𝟙 _)).1.base (IsLocalRing.closedPoint B) ∈ (⨆ U : D₀.A.affineOpens, (U : D₀.A.Opens)) := by
      rw [iSup_affineOpens_eq_top D₀.A]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨U₀, hU₀⟩ := hxU

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : D₀.A.affineOpens => ((U : D₀.A.Opens) : Set D₀.A))
    (fun U => (U : D₀.A.Opens).isOpen) (by
      intro x _
      have hx : x ∈ (⨆ U : D₀.A.affineOpens, (U : D₀.A.Opens)) := by
        rw [iSup_affineOpens_eq_top D₀.A]; trivial
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  let I : Type := ↥(insert U₀ t)
  letI : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  have hcov : ⨆ i : I, (i.1 : D₀.A.Opens) = ⊤ := by
    rw [← top_le_iff]
    intro x _
    obtain ⟨j₀, hj₀, hxj⟩ : ∃ j ∈ t, x ∈ ((j : D₀.A.Opens) : Set D₀.A) := by
      simpa only [Set.mem_iUnion, exists_prop] using ht (Set.mem_univ x)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨j₀, Finset.mem_insert_of_mem hj₀⟩, hxj⟩
  let 𝒰 : D₀.A.OrderedAffineCover := Scheme.OrderedAffineCover.mk I (fun i => (i.1 : D₀.A.Opens)) (fun i => i.1.2) hcov
  let i₀ : I := ⟨U₀, Finset.mem_insert_self _ _⟩

  have hpre : (D₀.L.one (𝟙 _)).1 ⁻¹ᵁ (𝒰.U i₀) = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 hU₀
  have hrange : Set.range (D₀.L.one (𝟙 _)).1.base ⊆ Set.range (𝒰.U i₀).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    have hp : p ∈ (D₀.L.one (𝟙 _)).1 ⁻¹ᵁ (𝒰.U i₀) := by rw [hpre]; trivial
    exact hp

  have hek : ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1 ≫ pullback.fst D₀.f (specMap B (ResidueField B)) =
      specMap B (ResidueField B) ≫ (D₀.L.one (𝟙 _)).1 := by
    have h1 := congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_one (specMap B (ResidueField B)) D₀.L (𝟙 _))
    rw [RelativeGroupLaw.baseChangePointToBase_coe] at h1
    rw [h1, ← D₀.L.one_natural (𝟙 _) (𝟙 _ ≫ specMap B (ResidueField B)) (specMap B (ResidueField B)) (by simp)]
    rfl
  have hrange1 : Set.range ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1.base ⊆
      Set.range ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    show (((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1 ≫ pullback.fst D₀.f (specMap B (ResidueField B))).base p ∈ (𝒰.U i₀ : Set D₀.A)
    rw [hek]
    have hp : (specMap B (ResidueField B)).base p ∈ (D₀.L.one (𝟙 _)).1 ⁻¹ᵁ (𝒰.U i₀) := by rw [hpre]; trivial
    exact hp

  have hCF : ∀ s : 𝒰.Idx 1, _ := fun s =>
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter D₀.f 𝒰 (ResidueField B) s
  choose σ hσ using hCF
  exact ⟨𝒰, i₀, IsOpenImmersion.lift (𝒰.U i₀).ι _ hrange, IsOpenImmersion.lift_fac _ _ _,
    IsOpenImmersion.lift ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι _ hrange1, IsOpenImmersion.lift_fac _ _ _,
    (𝒰.baseChange D₀.f (ResidueField B)).isAffineOpen i₀, σ, fun s x => (hσ s).1 x, fun s a => (hσ s).2 a⟩

end S_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_unit_chart_frame_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_orderedAffineCover_unit_chart_frame_bare (solution)
