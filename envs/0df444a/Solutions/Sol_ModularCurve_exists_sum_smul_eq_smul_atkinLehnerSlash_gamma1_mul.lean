-- Prove2me | solution 1 for ModularCurve.exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b89850a8-912e-504d-b713-c126646815fe

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul
import Theorems.Thm_ModularCurve_qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul
import Theorems.Thm_ModularCurve_exists_sum_smul_eq_of_qExpansion_coeff_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false

open scoped MatrixGroups ModularForm in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
    {p₀ : PowerSeries ℤ} (hf : ModularCurve.IsIntegralQExp f p₀)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγp : (p : ℤ) ∣ γ 1 1) :
    ∃ (D : ℤ) (n : ℕ) (c : Fin n → ℂ)
      (F : Fin n → ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k)
      (r : Fin n → PowerSeries ℤ),
      D ≠ 0 ∧
      (∀ i, c i ∈ IntermediateField.adjoin ℚ
        ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ)) ∧
      (∀ i, ModularCurve.IsIntegralQExp (F i) (r i)) ∧
      ((D : ℂ) • fun τ : UpperHalfPlane =>
          ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ))
        = ∑ i, c i • (⇑(F i) : UpperHalfPlane → ℂ) := by
  obtain ⟨F, hF⟩ := ModularCurve.exists_modularForm_coe_eq_atkinLehnerSlash_gamma1_mul p M hpM f γ hγ hγp
  have hcoeff : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ)).coeff n ∈
      IntermediateField.adjoin ℚ ({Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (p : ℂ))} : Set ℂ) := by
    intro n
    rw [hF]
    exact ModularCurve.qExpansion_coeff_atkinLehnerSlash_mem_adjoin_exp_gamma1_mul p M hpM f hf γ hγ hγp n
  obtain ⟨n, c, G, r, hc, hG, hsum⟩ :=
    ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem (M * p) _ F hcoeff
  refine ⟨1, n, c, G, r, one_ne_zero, hc, hG, ?_⟩
  rw [Int.cast_one, one_smul, ← hF, hsum]

end S_ModularCurve_exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul
end P2MW
export P2MW.S_ModularCurve_exists_sum_smul_eq_smul_atkinLehnerSlash_gamma1_mul (solution)
