-- Prove2me | solution 1 for ModularCurve.natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_natCard_rationalAut_map_zmultiples_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f83017ef-9f95-5e35-9e77-91c0c57a99a3

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Theorems.Thm_WeierstrassCurve_natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype
import Theorems.Thm_ModularCurve_forall_kernelVariableChangeDeg_eq_iff_image_equivOfVariableChangeEq_zmultiples_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_natCard_rationalAut_map_zmultiples_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve

theorem solution
    {κ : Type} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (M' : ℕ) [NeZero M'] (hM'κ : ((M' : ℕ) : κ) ≠ 0)
    (W : WeierstrassCurve κ) [W.IsElliptic]
    (T : ↥M'.primeFactors → Polynomial κ)
    (hT : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt W (p : ℕ) (M'.factorization (p : ℕ)) (T p))
    (g : W.toAffine.Point) (hg : addOrderOf g = M')
    (hlink : ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : κ) (h₁ : W.toAffine.Nonsingular x₁ y₁),
      n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
      (T p).IsRoot x₁) :
    Nat.card {C : WeierstrassCurve.VariableChange κ //
        C • W = W ∧ ∀ p : ↥M'.primeFactors,
          ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (T p) = T p} =
      Nat.card {ι : W.toAffine.Point →+ W.toAffine.Point //
        ι ∈ WeierstrassCurve.rationalHomSet κ W W ∧
        (∃ ι' ∈ WeierstrassCurve.rationalHomSet κ W W, ι'.comp ι = AddMonoidHom.id _ ∧ ι.comp ι' = AddMonoidHom.id _) ∧
        (AddSubgroup.zmultiples g).map ι = AddSubgroup.zmultiples g} := by
  classical
  have hB := fun (C : WeierstrassCurve.VariableChange κ) (hC : C • W = W) =>
    ModularCurve.forall_kernelVariableChangeDeg_eq_iff_image_equivOfVariableChangeEq_zmultiples_eq
      M' hM'κ W T hT g hg hlink C hC
  have h1 : Nat.card {C : WeierstrassCurve.VariableChange κ //
        C • W = W ∧ ∀ p : ↥M'.primeFactors,
          ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (T p) = T p} =
      Nat.card {C : WeierstrassCurve.VariableChange κ //
        ∃ hC : C • W = W, (fun φ : W.toAffine.Point → W.toAffine.Point =>
          φ '' (AddSubgroup.zmultiples g : Set W.toAffine.Point) = (AddSubgroup.zmultiples g : Set W.toAffine.Point))
          (fun P => WeierstrassCurve.Affine.Point.equivOfVariableChangeEq hC P)} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro C
    constructor
    · rintro ⟨hC, hk⟩
      exact ⟨hC, (hB C hC).mp hk⟩
    · rintro ⟨hC, hi⟩
      exact ⟨hC, (hB C hC).mpr hi⟩
  rw [h1, WeierstrassCurve.natCard_variableChange_smul_eq_subtype_eq_natCard_rationalAut_subtype W
    (fun φ : W.toAffine.Point → W.toAffine.Point =>
      φ '' (AddSubgroup.zmultiples g : Set W.toAffine.Point) = (AddSubgroup.zmultiples g : Set W.toAffine.Point))]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro ι
  have hiff : ((⇑ι : W.toAffine.Point → W.toAffine.Point) '' (AddSubgroup.zmultiples g : Set W.toAffine.Point) =
        (AddSubgroup.zmultiples g : Set W.toAffine.Point)) ↔
      (AddSubgroup.zmultiples g).map ι = AddSubgroup.zmultiples g := by
    rw [← SetLike.coe_set_eq (p := (AddSubgroup.zmultiples g).map ι), AddSubgroup.coe_map]
  exact and_congr_right fun _ => and_congr_right fun _ => hiff

end S_ModularCurve_natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_natCard_rationalAut_map_zmultiples_eq
end P2MW
export P2MW.S_ModularCurve_natCard_variableChange_smul_eq_and_kernelVariableChangeDeg_eq_eq_natCard_rationalAut_map_zmultiples_eq (solution)
