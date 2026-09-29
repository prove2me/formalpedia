-- Prove2me | solution 1 for ModularCurve.DRModelPackage.mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9db04b2a-1840-58c3-8e50-dc359e93a6e7

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve AlgebraicGeometry.RelPicard

namespace COMPPack

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

def S : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := (Set.range (𝔛.compZero k).base)ᶜ

theorem isPreconnected_of_isOpen_of_subset_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PreirreducibleSpace X] (f : X → Y) (hf : Continuous f) (T : Set Y) (hT : IsOpen T) (hcov : T ⊆ Set.range f) :
    _root_.IsPreconnected T := by
  rw [← Set.image_preimage_eq_of_subset hcov]
  exact (((PreirreducibleSpace.isPreirreducible_univ (X := X)).open_subset (hT.preimage hf)
    (Set.subset_univ _)).image f hf.continuousOn).isPreconnected

theorem isPreconnected_S : _root_.IsPreconnected (S p 𝔛 k) := by
  haveI := 𝔛.compZero_isClosedImmersion k
  refine isPreconnected_of_isOpen_of_subset_range (𝔛.compInf k).base (𝔛.compInf k).continuous _
    (𝔛.compZero k).isClosedEmbedding.isClosed_range.isOpen_compl ?_
  intro y hy
  exact (𝔛.comp_jointly_surjective k y).resolve_right hy

theorem mem_connectedComponentIn_of_isPreconnected {α : Type*} [TopologicalSpace α] {T F : Set α} (hT : _root_.IsPreconnected T)
    (hTF : T ⊆ F) {e y : α} (he : e ∈ T) (hy : y ∈ T) : y ∈ connectedComponentIn F e :=
  hT.subset_connectedComponentIn he hTF hy

theorem S_subset_preimage_smoothLocus : S p 𝔛 k ⊆ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) := by
  intro y hy
  exact (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 k y).mpr
    (fun h => hy h.2)

noncomputable def ePt : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := ((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1).base (IsLocalRing.closedPoint k)

theorem fst_ePt_mem_smoothLocus : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (ePt p 𝔛 k) ∈ 𝔛.smoothLocus := by
  apply 𝔛.εinf_mem_smoothLocus
  refine ⟨((Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (IsLocalRing.closedPoint k), ?_⟩
  show _ = ((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1 ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (IsLocalRing.closedPoint k)
  have h : (sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1 ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) = (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ≫ 𝔛.εinf.1 :=
    pullback.lift_fst _ _ _
  rw [h, Scheme.Hom.comp_base, TopCat.comp_app]

theorem ePt_mem_range_compInf : ePt p 𝔛 k ∈ Set.range (𝔛.compInf k).base := by
  apply 𝔛.εinf_mem_compInf k
  refine ⟨IsLocalRing.closedPoint k, ?_⟩

  have h : DRModel.sectionFibre 𝔛.εinf (algebraMap ℤ k) = (sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1 := rfl
  rw [h]; rfl

theorem ePt_mem_S : ePt p 𝔛 k ∈ S p 𝔛 k := by
  intro h0
  have hsm := fst_ePt_mem_smoothLocus p 𝔛 k
  have := (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 k (ePt p 𝔛 k)).mp hsm
  exact this ⟨ePt_mem_range_compInf p 𝔛 k, h0⟩

end COMPPack

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
    (hy : y ∈ Set.range (𝔛.compInf k).base) (hy' : y ∉ Set.range (𝔛.compZero k).base) :
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y ∈ 𝔛.smoothLocus ∧
      y ∈ connectedComponentIn
        ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus :
            (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) :
          Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
        (((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1).base (IsLocalRing.closedPoint k)) := by
  refine ⟨?_, ?_⟩
  · exact COMPPack.S_subset_preimage_smoothLocus p 𝔛 k hy'
  · exact COMPPack.mem_connectedComponentIn_of_isPreconnected (COMPPack.isPreconnected_S p 𝔛 k)
      (COMPPack.S_subset_preimage_smoothLocus p 𝔛 k) (COMPPack.ePt_mem_S p 𝔛 k) hy'

end S_ModularCurve_DRModelPackage_mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf (solution)
