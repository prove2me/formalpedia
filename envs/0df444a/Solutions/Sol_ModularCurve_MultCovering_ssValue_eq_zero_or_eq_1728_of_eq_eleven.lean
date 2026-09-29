-- Prove2me | solution 1 for ModularCurve.MultCovering.ssValue_eq_zero_or_eq_1728_of_eq_eleven
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6b12a3e5-a504-5df8-a6f5-91beeb693960

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_ofNat_1728_mem_ssJSet_eleven
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_ssValue_eq_zero_or_eq_1728_of_eq_eleven
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution (p : ℕ) [Fact p.Prime] (hp11 : p = 11)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) :
    ∀ e : Fin (mAnnuli p), ssValue Γ e = 0 ∨ ssValue Γ e = 1728 := by
  classical
  subst hp11
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) :=
    ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  have hm2 : mAnnuli 11 = 2 := by decide
  have h1728ne : (1728 : IsLocalRing.ResidueField ↥A) ≠ 0 := by
    rw [show (1728 : IsLocalRing.ResidueField ↥A) = ((1728 : ℕ) : IsLocalRing.ResidueField ↥A) by norm_cast,
      show (1728 : ℕ) = 11 * 157 + 1 by norm_num, Nat.cast_add, Nat.cast_mul,
      CharP.cast_eq_zero (IsLocalRing.ResidueField ↥A) 11, zero_mul, zero_add, Nat.cast_one]
    exact one_ne_zero
  have h0ss : (0 : IsLocalRing.ResidueField ↥A) ∈ ssJSet 11 (IsLocalRing.ResidueField ↥A) :=
    (ModularCurve.zero_mem_ssJSet_iff 11 (by norm_num) (IsLocalRing.ResidueField ↥A)).2 (by norm_num)
  have h1728ss : (1728 : IsLocalRing.ResidueField ↥A) ∈ ssJSet 11 (IsLocalRing.ResidueField ↥A) :=
    ModularCurve.ofNat_1728_mem_ssJSet_eleven (IsLocalRing.ResidueField ↥A)
  obtain ⟨e₀, he₀⟩ := exists_ssValue_eq Γ 0 h0ss
  obtain ⟨e₁, he₁⟩ := exists_ssValue_eq Γ 1728 h1728ss
  have hne : e₀ ≠ e₁ := by
    intro h; apply h1728ne; rw [← he₁, ← h, he₀]
  intro e
  by_cases h0 : e = e₀
  · left; rw [h0, he₀]
  · right
    have hee : e = e₁ := by
      apply Fin.ext
      have h0' : (e : ℕ) ≠ e₀ := fun h => h0 (Fin.ext h)
      have hne' : (e₀ : ℕ) ≠ e₁ := fun h => hne (Fin.ext h)
      have h1 : (e : ℕ) < 2 := lt_of_lt_of_eq e.isLt hm2
      have h2 : (e₀ : ℕ) < 2 := lt_of_lt_of_eq e₀.isLt hm2
      have h3 : (e₁ : ℕ) < 2 := lt_of_lt_of_eq e₁.isLt hm2
      omega
    rw [hee, he₁]

end S_ModularCurve_MultCovering_ssValue_eq_zero_or_eq_1728_of_eq_eleven
end P2MW
export P2MW.S_ModularCurve_MultCovering_ssValue_eq_zero_or_eq_1728_of_eq_eleven (solution)
