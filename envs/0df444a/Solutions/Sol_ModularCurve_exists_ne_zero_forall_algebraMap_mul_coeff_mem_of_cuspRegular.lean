-- Prove2me | solution 1 for ModularCurve.exists_ne_zero_forall_algebraMap_mul_coeff_mem_of_cuspRegular
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/8553556f-ae9e-5e23-93f4-ba19582a4ab7

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ne_zero_forall_algebraMap_mul_coeff_mem_of_cuspRegular
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace BddDenomAux

theorem exists_int_cast_eq_coeff_jq_pow (N : ℕ) (k : ℤ) : ∃ z : ℤ, (jq ^ N).coeff k = (z : ℚ) := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul]
  by_cases h : 0 ≤ k - -(N : ℤ)
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
    rw [hn, HahnSeries.ofPowerSeries_apply_coeff, jNumQ, ← map_pow, PowerSeries.coeff_map]
    exact ⟨PowerSeries.coeff n (jNum ^ N), by simp⟩
  · exact ⟨0, by rw [ModularCurve.ofPowerSeries_coeff_of_neg _ (lt_of_not_ge h)]; simp⟩

theorem coeff_mul_mem {L : Type*} [Field L] (A : ValuationSubring L) (x y : LaurentSeries L)
    (hx : ∀ k : ℤ, x.coeff k ∈ A) (hy : ∀ k : ℤ, y.coeff k ∈ A) (k : ℤ) : (x * y).coeff k ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact sum_mem fun ij _ => mul_mem (hx _) (hy _)

theorem exists_int_mul_inv_mem (A : ValuationSubring (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ (d : AlgebraicClosure ℚ) * c⁻¹ ∈ A := by
  have halg : IsAlgebraic ℤ c⁻¹ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c⁻¹)
  obtain ⟨d, hd0, hint⟩ := halg.exists_integral_multiple
  refine ⟨d, hd0, ?_⟩
  rw [Algebra.smul_def, eq_intCast] at hint
  have hint' : IsIntegral ↥A ((d : AlgebraicClosure ℚ) * c⁻¹) := by
    obtain ⟨p, hp, hpy⟩ := hint
    refine ⟨p.map (Int.castRingHom ↥A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap ↥A (AlgebraicClosure ℚ)).comp (Int.castRingHom ↥A))
        (algebraMap ℤ (AlgebraicClosure ℚ))]
    exact hpy
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint'
  rw [← hy]
  exact y.2

end BddDenomAux

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (g : LaurentSeries ℚ) (hg : g ∈ modularFunctionFieldFull M')
    (hreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) →
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) g, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M'))) :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ n : ℤ, algebraMap ℚ (AlgebraicClosure ℚ) (c * g.coeff n) ∈ A := by
  classical
  set J : ↥(modularFunctionFieldBar M') := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ with hJdef
  set G : ↥(modularFunctionFieldBar M') := ⟨coeffEmb (AlgebraicClosure ℚ) g,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hg⟩ with hGdef

  by_cases hg0 : g = 0
  · exact ⟨1, one_ne_zero, fun n => by simp [hg0]⟩
  have hG0 : G ≠ 0 := by
    intro h
    apply hg0
    ext k
    have hk := congrArg (fun x : ↥(modularFunctionFieldBar M') => (x : LaurentSeries (AlgebraicClosure ℚ)).coeff k) h
    simpa [hGdef, coeffEmb_coeff] using hk
  have hJ0 : J ≠ 0 := by
    intro h
    apply jq_ne_zero
    ext k
    have hk := congrArg (fun x : ↥(modularFunctionFieldBar M') => (x : LaurentSeries (AlgebraicClosure ℚ)).coeff k) h
    simpa [hJdef, coeffEmb_coeff] using hk

  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar M'
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ)
    (F := ↥(modularFunctionFieldBar M')) G hG0
  set N : ℕ := D.support.sup fun v => (-(D v)).toNat with hNdef
  have hN : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), P.ord G < 0 → -P.ord G ≤ (N : ℤ) := by
    intro P hP
    have hmem : P ∈ D.support := by
      rw [Finsupp.mem_support_iff, hD]; exact hP.ne
    have h1 : (-(D P)).toNat ≤ N := Finset.le_sup (f := fun v => (-(D v)).toNat) hmem
    have h2 : ((-(D P)).toNat : ℤ) = -(D P) := Int.toNat_of_nonneg (by rw [hD]; omega)
    have h3 : ((-(D P)).toNat : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
    rw [h2, hD] at h3
    exact h3

  set f : ↥(modularFunctionFieldBar M') := G * (J ^ N)⁻¹ with hfdef
  have hJN0 : J ^ N ≠ 0 := pow_ne_zero _ hJ0
  have hf0 : f ≠ 0 := mul_ne_zero hG0 (inv_ne_zero hJN0)
  have hordf : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
      W.ord f = W.ord G - N * W.ord J := by
    intro W
    rw [hfdef, W.ord_mul hG0 (inv_ne_zero hJN0), W.ord_inv, ← zpow_natCast, W.ord_zpow]
    ring
  have hpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), W.ord f < 0 →
      ∃ a : ↥A, 0 < W.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') (a : AlgebraicClosure ℚ)) := by
    intro W hW
    refine ⟨0, ?_⟩
    rw [ZeroMemClass.coe_zero, map_zero, sub_zero]
    rw [hordf] at hW
    by_contra hle
    push Not at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · rcases lt_or_ge (W.ord G) 0 with hGneg | hGnn
      · have h1 := hN W hGneg
        have h2 : (N : ℤ) ≤ -(N * W.ord J) := by nlinarith
        omega
      · have h2 : (0 : ℤ) ≤ -(N * W.ord J) := by nlinarith
        omega
    · have h1 := hreg W (le_of_eq heq.symm)
      rw [heq] at hW
      simp at hW
      omega

  obtain ⟨c, hc0, hc⟩ := ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg A M' f hf0 hpole

  have hJN : ∀ k : ℤ, (((J ^ N : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A := by
    intro k
    obtain ⟨z, hz⟩ := BddDenomAux.exists_int_cast_eq_coeff_jq_pow N k
    have : (((J ^ N : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ))) =
        coeffEmb (AlgebraicClosure ℚ) (jq ^ N) := by
      rw [map_pow]; rfl
    rw [this, coeffEmb_coeff, hz, map_intCast]
    exact intCast_mem A z
  have hJNv0 : (((J ^ N : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ))) ≠ 0 := by
    exact_mod_cast hJN0
  have hcG : ∀ k : ℤ, (c • (G : LaurentSeries (AlgebraicClosure ℚ))).coeff k ∈ A := by
    intro k
    have hfG : f * J ^ N = G := by rw [hfdef, inv_mul_cancel_right₀ hJN0]
    have hcoe : (G : LaurentSeries (AlgebraicClosure ℚ)) =
        (f : LaurentSeries (AlgebraicClosure ℚ)) * (((J ^ N : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ))) := by
      rw [← hfG]; rfl
    have : c • (G : LaurentSeries (AlgebraicClosure ℚ)) =
        (c • (f : LaurentSeries (AlgebraicClosure ℚ))) * (((J ^ N : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ))) := by
      rw [← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, hcoe, mul_assoc]
    rw [this]
    exact BddDenomAux.coeff_mul_mem A _ _ hc hJN k

  obtain ⟨d, hd0, hd⟩ := BddDenomAux.exists_int_mul_inv_mem A c
  refine ⟨d, by exact_mod_cast hd0, fun n => ?_⟩
  have : algebraMap ℚ (AlgebraicClosure ℚ) ((d : ℚ) * g.coeff n) =
      ((d : AlgebraicClosure ℚ) * c⁻¹) * (c • (G : LaurentSeries (AlgebraicClosure ℚ))).coeff n := by
    rw [map_mul, map_intCast, HahnSeries.coeff_smul, hGdef]
    simp only [coeffEmb_coeff, smul_eq_mul]
    field_simp
  rw [this]
  exact mul_mem hd (hcG n)

end S_ModularCurve_exists_ne_zero_forall_algebraMap_mul_coeff_mem_of_cuspRegular
end P2MW
export P2MW.S_ModularCurve_exists_ne_zero_forall_algebraMap_mul_coeff_mem_of_cuspRegular (solution)
