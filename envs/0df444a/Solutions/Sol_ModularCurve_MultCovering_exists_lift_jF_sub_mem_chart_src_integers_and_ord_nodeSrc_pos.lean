-- Prove2me | solution 1 for ModularCurve.MultCovering.exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/39685b91-5abd-5847-966c-353dc1f05898

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_jFun_jqFun
import Theorems.Thm_ModularCurve_MultCovering_jpF_eq_jqFun
import Theorems.Thm_ModularCurve_MultCovering_frickeInvolutionBar_jF
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jqFun modularFunctionFieldC PlaceSpecialization charLGeomPlaceOfPoint frickeInvolutionBar PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_jFun_jqFun pow_q_sq_eq_self_of_mem_ssJSet ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jF jpF jBar ChartCtx infChart zeroChart chart src ssValue edgeOf ssValue_edgeOf nodeSrc jpF_eq_jqFun frickeInvolutionBar_jF"
namespace P2MtieSrc
p2m_open "ModularCurve.MultCovering ModularCurve"

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem ord_jBar_sub (k : Type) [Field k] [DecidableEq k] (a c : k) :
    (charLGeomPlaceOfPoint k a).ord (jBar k - algebraMap k ↥(modularFunctionFieldC k 1) c)
      = if c = a then 1 else 0 :=
  ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a c

theorem mem_zeroChart_integers_iff (f : ↥(modularFunctionFieldBar (1 * p))) :
    f ∈ (zeroChart Γ).integers ↔ frickeInvolutionBar (1 * p) f ∈ (infChart Γ).integers := Iff.rfl

theorem zeroChart_residue_eq (f : ↥(modularFunctionFieldBar (1 * p))) (h : f ∈ (zeroChart Γ).integers) :
    (zeroChart Γ).residue ⟨f, h⟩
      = (infChart Γ).residue ⟨frickeInvolutionBar (1 * p) f, (mem_zeroChart_integers_iff Γ f).mp h⟩ := rfl

theorem infChart_residue_jpF (hA : A.LiesOverPrime p) :
    ∃ hjp : jpF p ∈ (infChart Γ).integers,
      (infChart Γ).residue ⟨jpF p, hjp⟩ = jBar (IsLocalRing.ResidueField ↥A) ^ p := by
  obtain ⟨hj, hjp, -, h2, -⟩ :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_jFun_jqFun
      Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply hA
  have key : ∀ f : ↥(modularFunctionFieldBar (1 * p)), f = PlaceSpecialization.jqFun (q := p) →
      ∃ hf : f ∈ (infChart Γ).integers,
        (infChart Γ).residue ⟨f, hf⟩ = jBar (IsLocalRing.ResidueField ↥A) ^ p := by
    rintro f rfl
    exact ⟨hjp, h2⟩
  exact key _ (jpF_eq_jqFun p)

theorem tie_srcLift (hA : A.LiesOverPrime p) (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ∃ xl : ↥A, IsLocalRing.residue ↥A xl = a ∧
      ∃ h : jF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (xl : AlgebraicClosure ℚ)
          ∈ (chart Γ (src p (edgeOf Γ a ha))).integers,
        0 < (nodeSrc Γ (edgeOf Γ a ha)).ord
          ((chart Γ (src p (edgeOf Γ a ha))).residue ⟨_, h⟩) := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  haveI : CharP ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) p :=
    charP_of_injective_algebraMap
      (algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)).injective p

  have hpp : (a ^ p) ^ p = a := by
    rw [← pow_mul, ← pow_two, ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet p ha]

  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (a ^ p)
  refine ⟨x ^ p, by rw [RingHom.map_pow, hx, hpp], ?_⟩

  obtain ⟨hjp, hresjp⟩ := infChart_residue_jpF Γ hA
  have hc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((x ^ p : ↥A) : AlgebraicClosure ℚ)
      ∈ (infChart Γ).integers := ((infChart Γ).algebraMap_mem_iff _).mpr (x ^ p).2
  have hmem : jpF p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((x ^ p : ↥A) : AlgebraicClosure ℚ)
      ∈ (infChart Γ).integers := (infChart Γ).integers.sub_mem hjp hc

  have hw : frickeInvolutionBar (1 * p)
      (jF p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((x ^ p : ↥A) : AlgebraicClosure ℚ))
      = jpF p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((x ^ p : ↥A) : AlgebraicClosure ℚ) := by
    rw [map_sub (frickeInvolutionBar (1 * p)), AlgEquiv.commutes, frickeInvolutionBar_jF]

  have h0 : jF p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((x ^ p : ↥A) : AlgebraicClosure ℚ)
      ∈ (zeroChart Γ).integers := by
    rw [mem_zeroChart_integers_iff, hw]; exact hmem
  refine ⟨h0, ?_⟩
  have hres : (zeroChart Γ).residue ⟨_, h0⟩ = (infChart Γ).residue ⟨_, hmem⟩ := by
    rw [zeroChart_residue_eq]
    congr 1
    exact Subtype.ext hw

  have e1 : (⟨jpF p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((x ^ p : ↥A) : AlgebraicClosure ℚ),
      hmem⟩ : ↥(infChart Γ).integers) = ⟨jpF p, hjp⟩ - ⟨_, hc⟩ := Subtype.ext rfl
  have hres2 : (infChart Γ).residue ⟨_, hmem⟩ =
      (jBar (IsLocalRing.ResidueField ↥A)
        - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (a ^ p)) ^ p := by
    rw [e1, RingHom.map_sub, hresjp, (infChart Γ).residue_algebraMap (x ^ p), RingHom.map_pow (IsLocalRing.residue ↥A) x p, hx,
      RingHom.map_pow (algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) (a ^ p) p,
      ← sub_pow_char]

  show 0 < (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ (edgeOf Γ a ha) ^ p)).ord
    ((zeroChart Γ).residue ⟨_, h0⟩)
  rw [hres, ssValue_edgeOf, hres2,
    show (jBar (IsLocalRing.ResidueField ↥A)
        - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (a ^ p)) ^ p
      = (jBar (IsLocalRing.ResidueField ↥A)
        - algebraMap (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) (a ^ p)) ^ ((p : ℕ) : ℤ)
      from (zpow_natCast _ p).symm,
    Place.ord_zpow, ord_jBar_sub, if_pos rfl, mul_one]
  exact_mod_cast (Fact.out : p.Prime).pos

end ModularCurve.MultCovering.P2MtieSrc

open _root_.ModularCurve.MultCovering _root_.P2MW.S_ModularCurve_MultCovering_exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos.ModularCurve.MultCovering in
theorem solution (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ∃ xl : ↥A, IsLocalRing.residue ↥A xl = a ∧
      ∃ h : jF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (xl : AlgebraicClosure ℚ)
          ∈ (chart Γ (src p (edgeOf Γ a ha))).integers,
        0 < (nodeSrc Γ (edgeOf Γ a ha)).ord
          ((chart Γ (src p (edgeOf Γ a ha))).residue ⟨_, h⟩) :=
  ModularCurve.MultCovering.P2MtieSrc.tie_srcLift Γ hA a ha

end S_ModularCurve_MultCovering_exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos
end P2MW
export P2MW.S_ModularCurve_MultCovering_exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos (solution)
