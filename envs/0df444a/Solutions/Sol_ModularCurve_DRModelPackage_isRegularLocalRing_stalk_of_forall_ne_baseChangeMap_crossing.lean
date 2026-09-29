-- Prove2me | solution 1 for ModularCurve.DRModelPackage.isRegularLocalRing_stalk_of_forall_ne_baseChangeMap_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/87fc4a55-0431-5035-bcfa-244319935a27

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_isRegularLocalRing_stalk_of_forall_ne_baseChangeMap_crossing
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_isRegularLocalRing_stalk_of_forall_ne_baseChangeMap_crossing.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel.baseChangeMap DRModel DRModel.toBase DRModelPackage DRModelPackage.mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "smoothLocus compZero compInf mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase"
namespace X0Reg
p2m_open "ModularCurve.DRModelPackage ModularCurve"

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O]

theorem smooth_preimage_smoothLocus_ι_comp_snd :
    Smooth (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
        𝔛.smoothLocus).ι ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := by
  have h1 := isPullback_morphismRestrict
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) 𝔛.smoothLocus
  have h2 := IsPullback.of_hasPullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
  have h := h1.paste_vert h2
  haveI : Smooth (𝔛.smoothLocus.ι ≫ DRModel.toBase p) := SmoothOfRelativeDimension.smooth 1 _
  exact MorphismProperty.of_isPullback h inferInstance

end ModularCurve.DRModelPackage.X0Reg

open ModularCurve.DRModelPackage.X0Reg in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (z : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hz : z ∉ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))
    (hne : ∀ n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      z ≠ (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n) :
    IsRegularLocalRing ((pullback (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk z) := by

  have hzW : z ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      𝔛.smoothLocus := by
    rcases ModularCurve.DRModelPackage.mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase
      p 𝔛 O hϖ κ toκ z with h | h | ⟨n, rfl⟩
    exacts [absurd h hz, h, absurd rfl (hne n)]

  haveI := smooth_preimage_smoothLocus_ι_comp_snd p 𝔛 O
  have hreg := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing O
    (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus).ι ≫
      pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⟨z, hzW⟩
  exact (AlgebraicGeometry.IsOpenImmersion.isRegularLocalRing_stalk_iff
    (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ 𝔛.smoothLocus).ι)
    ⟨z, hzW⟩).mpr hreg

end S_ModularCurve_DRModelPackage_isRegularLocalRing_stalk_of_forall_ne_baseChangeMap_crossing
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_isRegularLocalRing_stalk_of_forall_ne_baseChangeMap_crossing (solution)
