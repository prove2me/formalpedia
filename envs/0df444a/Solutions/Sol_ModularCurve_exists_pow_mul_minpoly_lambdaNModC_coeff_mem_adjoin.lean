-- Prove2me | solution 1 for ModularCurve.exists_pow_mul_minpoly_lambdaNModC_coeff_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/4fd2cc5d-19e4-5616-9d4e-587d376fabea

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Theorems.Thm_ModularCurve_jq_mul_lambdaModC_mul_one_sub_pow_four
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_pow_mul_minpoly_lambdaNModC_coeff_mem_adjoin
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

open Polynomial ModularCurve

noncomputable section

namespace LambdaIntlocSol

local notation "L" => LaurentSeries ℚ

abbrev Fμ : IntermediateField ℚ L := IntermediateField.adjoin ℚ ({lambdaModC ℚ} : Set L)

def muF : Fμ := ⟨lambdaModC ℚ, IntermediateField.mem_adjoin_simple_self ℚ (lambdaModC ℚ)⟩

def toF : Polynomial ℚ →+* Fμ := (Polynomial.aeval (R := ℚ) muF).toRingHom

theorem toF_injective : Function.Injective toF := by
  have ht : Transcendental ℚ (muF : Fμ) := by
    intro halg
    have halg' : @IsAlgebraic ℚ Fμ _ _ (Fμ).algebra muF := by
      convert halg
      exact Subsingleton.elim _ _
    have h2 : IsAlgebraic ℚ ((muF : Fμ) : L) := IntermediateField.isAlgebraic_iff.mp halg'
    exact ModularCurve.transcendental_lambdaModC ℚ h2
  exact transcendental_iff_injective.mp ht

theorem algebraMap_comp_toF :
    (algebraMap Fμ L).comp toF = Polynomial.eval₂RingHom (algebraMap ℚ L) (lambdaModC ℚ) := by
  refine Polynomial.ringHom_ext (fun r => ?_) ?_
  · simp [toF]
  · simp [toF]
    rfl

theorem algebraMap_toF (p : Polynomial ℚ) : algebraMap Fμ L (toF p) = aeval (lambdaModC ℚ) p := by
  have := congrArg (fun φ => φ p) algebraMap_comp_toF
  simpa [Polynomial.aeval_def] using this

theorem aeval_mu_injective : Function.Injective (aeval (R := ℚ) (lambdaModC ℚ) : Polynomial ℚ →ₐ[ℚ] L) :=
  transcendental_iff_injective.mp (ModularCurve.transcendental_lambdaModC ℚ)

def Dpoly : Polynomial ℚ := X * (1 - 16 * X) ^ 4
def Apoly : Polynomial ℚ := (1 + 224 * X + 256 * X ^ 2) ^ 3

theorem aeval_Dpoly : aeval (lambdaModC ℚ) Dpoly = lambdaModC ℚ * (1 - 16 * lambdaModC ℚ) ^ 4 := by
  simp [Dpoly, map_mul, map_pow, map_sub, map_ofNat]

theorem aeval_Apoly : aeval (lambdaModC ℚ) Apoly = (1 + 224 * lambdaModC ℚ + 256 * lambdaModC ℚ ^ 2) ^ 3 := by
  simp [Apoly, map_add, map_mul, map_pow, map_ofNat]

theorem Dpoly_ne_zero : Dpoly ≠ 0 := by
  rw [Dpoly]
  refine mul_ne_zero X_ne_zero (pow_ne_zero _ ?_)
  intro h
  have := congrArg (fun p : Polynomial ℚ => p.coeff 0) h
  simp at this

theorem aeval_Dpoly_ne_zero : aeval (lambdaModC ℚ) Dpoly ≠ 0 := fun h =>
  Dpoly_ne_zero (aeval_mu_injective (by rw [h, map_zero]))

theorem jq_eq : jq = aeval (lambdaModC ℚ) Apoly * (aeval (lambdaModC ℚ) Dpoly)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq₀ aeval_Dpoly_ne_zero, aeval_Apoly, aeval_Dpoly, ← mul_assoc]
  exact ModularCurve.jq_mul_lambdaModC_mul_one_sub_pow_four

abbrev Rm := Localization.Away Dpoly

scoped instance algXL : Algebra (Polynomial ℚ) L := (aeval (R := ℚ) (lambdaModC ℚ)).toRingHom.toAlgebra

theorem algebraMap_XL (p : Polynomial ℚ) : algebraMap (Polynomial ℚ) L p = aeval (lambdaModC ℚ) p := rfl

def liftL : Rm →+* L :=
  IsLocalization.Away.lift Dpoly (g := algebraMap (Polynomial ℚ) L) (isUnit_iff_ne_zero.mpr aeval_Dpoly_ne_zero)

scoped instance algRmL : Algebra Rm L := (liftL).toAlgebra

theorem algebraMap_RmL (r : Rm) : algebraMap Rm L r = liftL r := rfl

scoped instance towerXRmL : IsScalarTower (Polynomial ℚ) Rm L :=
  IsScalarTower.of_algebraMap_eq fun p => by
    rw [algebraMap_RmL, liftL, IsLocalization.Away.lift_eq]

def rj : Rm := algebraMap (Polynomial ℚ) Rm Apoly * IsLocalization.Away.invSelf Dpoly

theorem algebraMap_rj : algebraMap Rm L rj = jq := by
  rw [rj, map_mul, ← IsScalarTower.algebraMap_apply, algebraMap_XL, jq_eq]
  congr 1

  apply eq_inv_of_mul_eq_one_left
  rw [← algebraMap_XL, IsScalarTower.algebraMap_apply (Polynomial ℚ) Rm L, ← map_mul,
    mul_comm, IsLocalization.Away.mul_invSelf, map_one]

theorem isIntegral_jqN (q : ℕ) [NeZero q] (d₁ : ModularPolynomialData q) : IsIntegral Rm (jqN q) := by
  let φ : Polynomial ℤ →+* Rm := Polynomial.eval₂RingHom (Int.castRingHom Rm) rj
  refine ⟨d₁.Φ.map φ, d₁.monic.map φ, ?_⟩
  have hcomp : (algebraMap Rm L).comp φ = evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply]
    simp only [φ, Polynomial.coe_eval₂RingHom, eval₂_X, algebraMap_rj, evalAtJ_X]
  rw [Polynomial.eval₂_map, hcomp]
  exact d₁.eval_eq_zero

theorem jm_q (q : ℕ) [NeZero q] :
    jqN q * lambdaNModC ℚ q * (1 - 16 * lambdaNModC ℚ q) ^ 4
      = (1 + 224 * lambdaNModC ℚ q + 256 * lambdaNModC ℚ q ^ 2) ^ 3 := by
  have h := congrArg (qExpand ℚ q) ModularCurve.jq_mul_lambdaModC_mul_one_sub_pow_four
  simpa [jqN, lambdaNModC, map_mul, map_pow, map_sub, map_add, map_ofNat] using h

section integrality
variable (q : ℕ) [NeZero q]

abbrev B : Subalgebra Rm L := Algebra.adjoin Rm ({jqN q} : Set L)

theorem jqN_mem_B : jqN q ∈ B q := Algebra.subset_adjoin (Set.mem_singleton _)

def quadB : Polynomial (B q) := C (256 : B q) * X ^ 2 + C (224 : B q) * X + C (1 : B q)
def DB : Polynomial (B q) := X * (1 - C (16 : B q) * X) ^ 4
def Prel : Polynomial (B q) := quadB q ^ 3 - C (⟨jqN q, jqN_mem_B q⟩ : B q) * DB q

theorem aeval_map_int (P : Polynomial ℤ) (y : L) :
    aeval y (P.map (Int.castRingHom (B q))) = aeval y P := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.aeval_def]
  congr 1
  exact RingHom.ext_int _ _

theorem aeval_Prel : aeval (lambdaNModC ℚ q) (Prel q) = 0 := by
  have hC : algebraMap (B q) L (⟨jqN q, jqN_mem_B q⟩ : B q) = jqN q := rfl
  rw [Polynomial.aeval_def, Prel, quadB, DB]
  simp only [eval₂_sub, eval₂_mul, eval₂_add, eval₂_pow, eval₂_C, eval₂_X, eval₂_one]
  simp only [map_ofNat, map_one, hC]
  linear_combination -(jm_q q)

theorem natCast_B_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : B q) ≠ 0 := by
  intro h
  have h' : ((n : B q) : L) = 0 := by rw [h]; rfl
  have e : ((n : B q) : L) = algebraMap ℚ L (n : ℚ) := by simp
  rw [e, map_eq_zero] at h'
  exact hn (by exact_mod_cast h')

theorem natDegree_DB_le : (DB q).natDegree ≤ 5 := by
  rw [DB]
  refine natDegree_mul_le.trans ?_
  have h1 : (X : Polynomial (B q)).natDegree ≤ 1 := natDegree_X_le
  have h2 : ((1 - C (16 : B q) * X) ^ 4).natDegree ≤ 4 := by
    refine natDegree_pow_le.trans ?_
    have : (1 - C (16 : B q) * X).natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans ?_
      rw [natDegree_one]
      exact max_le (Nat.zero_le _) ((natDegree_C_mul_le _ _).trans natDegree_X_le)
    omega
  omega

theorem coeff_Prel_six : (Prel q).coeff 6 = 256 ^ 3 := by
  rw [Prel, coeff_sub]
  have hA : (quadB q ^ 3).coeff 6 = 256 ^ 3 := by
    rw [show (6 : ℕ) = 3 * 2 by norm_num, quadB, coeff_pow_of_natDegree_le (natDegree_quadratic_le)]
    simp [coeff_add, coeff_C_mul, coeff_X_pow, coeff_one]
  have hD : (C (⟨jqN q, jqN_mem_B q⟩ : B q) * DB q).coeff 6 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans (natDegree_DB_le q)) (by norm_num)
  rw [hA, hD, sub_zero]

theorem natDegree_Prel : (Prel q).natDegree = 6 := by
  apply le_antisymm
  · rw [Prel]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact natDegree_pow_le.trans (by have := natDegree_quadratic_le (a := (256 : B q)) (b := 224) (c := 1); rw [quadB]; omega)
    · exact (natDegree_C_mul_le _ _).trans ((natDegree_DB_le q).trans (by norm_num))
  · apply le_natDegree_of_ne_zero
    rw [coeff_Prel_six]
    exact pow_ne_zero _ (by exact_mod_cast natCast_B_ne_zero q (n := 256) (by norm_num))

theorem leadingCoeff_Prel : (Prel q).leadingCoeff = 256 ^ 3 := by
  rw [leadingCoeff, natDegree_Prel, coeff_Prel_six]

theorem isIntegral_B : IsIntegral (B q) (lambdaNModC ℚ q) := by
  have h := isIntegral_leadingCoeff_smul (Prel q) (lambdaNModC ℚ q) (aeval_Prel q)
  rw [leadingCoeff_Prel, Algebra.smul_def, mul_comm] at h

  set r : B q := algebraMap Rm (B q) (algebraMap (Polynomial ℚ) Rm (C ((256 ^ 3 : ℚ)⁻¹))) with hr
  refine IsIntegral.of_mul_unit (r := r) ?_ h
  have e1 : algebraMap (B q) L r = algebraMap (Polynomial ℚ) L (C ((256 ^ 3 : ℚ)⁻¹)) := by
    rw [hr, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [e1, algebraMap_XL, aeval_C, map_pow, map_ofNat]
  have e2 : ((256 : L)) = algebraMap ℚ L 256 := (map_ofNat _ 256).symm
  rw [e2, ← map_pow, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one]

theorem isIntegral_Rm (d₁ : ModularPolynomialData q) : IsIntegral Rm (lambdaNModC ℚ q) := by
  haveI : Algebra.IsIntegral Rm (B q) := Algebra.IsIntegral.adjoin fun x hx => by
    rw [Set.mem_singleton_iff] at hx; subst hx; exact isIntegral_jqN q d₁
  exact isIntegral_trans (R := Rm) (A := B q) _ (isIntegral_B q)

theorem exists_pow_smul_isIntegral (d₁ : ModularPolynomialData q) :
    ∃ N : ℕ, IsIntegral (Polynomial ℚ) ((Dpoly ^ N) • lambdaNModC ℚ q) := by
  obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Submonoid.powers Dpoly) (Rₘ := Rm)
    (lambdaNModC ℚ q) (isIntegral_Rm q d₁)
  obtain ⟨N, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hm
  exact ⟨N, hint⟩

end integrality

scoped instance algXF : Algebra (Polynomial ℚ) Fμ := toF.toAlgebra

theorem algebraMap_XF (p : Polynomial ℚ) : algebraMap (Polynomial ℚ) Fμ p = toF p := rfl

scoped instance towerXFL : IsScalarTower (Polynomial ℚ) Fμ L :=
  IsScalarTower.of_algebraMap_eq fun p => by rw [algebraMap_XF, algebraMap_toF, algebraMap_XL]

scoped instance faithfulXF : FaithfulSMul (Polynomial ℚ) Fμ :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr toF_injective

scoped instance isFractionRingXF : IsFractionRing (Polynomial ℚ) Fμ := by
  refine IsFractionRing.of_field (Polynomial ℚ) Fμ fun z => ?_
  obtain ⟨r, s, h⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ (z : L)).mp z.2
  refine ⟨r, s, Subtype.ext ?_⟩
  rw [h]
  show _ = ((algebraMap (Polynomial ℚ) Fμ r / algebraMap (Polynomial ℚ) Fμ s : Fμ) : L)
  rw [show ((algebraMap (Polynomial ℚ) Fμ r / algebraMap (Polynomial ℚ) Fμ s : Fμ) : L)
      = algebraMap Fμ L (algebraMap (Polynomial ℚ) Fμ r / algebraMap (Polynomial ℚ) Fμ s) from rfl,
    map_div₀, algebraMap_XF, algebraMap_XF, algebraMap_toF, algebraMap_toF]

theorem minpoly_smul_eq_scaleRoots {x : L} (hx : IsIntegral Fμ x) {d : Fμ} (hd : d ≠ 0) :
    minpoly Fμ (algebraMap Fμ L d * x) = (minpoly Fμ x).scaleRoots d := by
  have hdx : IsIntegral Fμ (algebraMap Fμ L d * x) := by
    have := hx.smul d
    rwa [Algebra.smul_def] at this
  have h1 : minpoly Fμ (algebraMap Fμ L d * x) ∣ (minpoly Fμ x).scaleRoots d :=
    minpoly.dvd Fμ _ (scaleRoots_aeval_eq_zero (minpoly.aeval Fμ x))
  have h2 : minpoly Fμ x ∣ (minpoly Fμ (algebraMap Fμ L d * x)).scaleRoots d⁻¹ := by
    apply minpoly.dvd
    have := scaleRoots_aeval_eq_zero (minpoly.aeval Fμ (algebraMap Fμ L d * x)) (r := d⁻¹)
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hd, map_one, one_mul] at this
  have hm1 : (minpoly Fμ (algebraMap Fμ L d * x)).Monic := minpoly.monic hdx
  have hm2 : ((minpoly Fμ x).scaleRoots d).Monic := (monic_scaleRoots_iff d).mpr (minpoly.monic hx)
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hm1 hm2 h1 ?_
  rw [natDegree_scaleRoots]
  have := natDegree_le_of_dvd h2 (((monic_scaleRoots_iff d⁻¹).mpr hm1).ne_zero)
  rwa [natDegree_scaleRoots] at this

theorem main (q : ℕ) [hq : Fact q.Prime] (k : ℕ) :
    ∃ N : ℕ, (lambdaModC ℚ * (1 - 16 * lambdaModC ℚ) ^ 4) ^ N *
        ((minpoly Fμ (lambdaNModC ℚ q)).coeff k : L) ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set L) := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  obtain ⟨d₁, -⟩ := ModularCurve.modularPolynomialFamily q hq.out
  obtain ⟨N, hy⟩ := exists_pow_smul_isIntegral q d₁

  set d : Fμ := algebraMap (Polynomial ℚ) Fμ (Dpoly ^ N) with hd_def
  have hdL : algebraMap Fμ L d = aeval (lambdaModC ℚ) Dpoly ^ N := by
    rw [hd_def, algebraMap_XF, algebraMap_toF, map_pow]
  have hd0 : d ≠ 0 := by
    intro h0
    have : algebraMap Fμ L d = 0 := by rw [h0, map_zero]
    rw [hdL] at this
    exact pow_ne_zero _ aeval_Dpoly_ne_zero this
  have hy' : (Dpoly ^ N) • lambdaNModC ℚ q = algebraMap Fμ L d * lambdaNModC ℚ q := by
    rw [Algebra.smul_def, algebraMap_XL, hdL, map_pow]

  have key := minpoly.isIntegrallyClosed_eq_field_fractions' (R := Polynomial ℚ) (S := L) Fμ hy
  rw [hy'] at key hy

  have hint : IsIntegral Fμ (lambdaNModC ℚ q) := by
    have h := (hy.tower_top (A := Fμ)).smul d⁻¹
    rwa [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd0, map_one, one_mul] at h
  have hscale := minpoly_smul_eq_scaleRoots hint hd0
  rw [hscale] at key

  set m₀ := minpoly Fμ (lambdaNModC ℚ q) with hm₀
  set c := (minpoly (Polynomial ℚ) (algebraMap Fμ L d * lambdaNModC ℚ q)).coeff k with hc
  have hk : m₀.coeff k * d ^ (m₀.natDegree - k) = algebraMap (Polynomial ℚ) Fμ c := by
    have := congrArg (fun P : Polynomial Fμ => P.coeff k) key
    simpa only [coeff_scaleRoots, coeff_map] using this
  refine ⟨N * (m₀.natDegree - k), ?_⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
  refine ⟨c, ?_⟩
  have e1 : aeval (lambdaModC ℚ) c = ((algebraMap (Polynomial ℚ) Fμ c : Fμ) : L) := by
    rw [algebraMap_XF, ← algebraMap_toF]; rfl
  have hdL' : ((d : Fμ) : L) = aeval (lambdaModC ℚ) Dpoly ^ N := hdL
  rw [e1, ← hk]
  have e2 : ((m₀.coeff k * d ^ (m₀.natDegree - k) : Fμ) : L) = ((m₀.coeff k : Fμ) : L) * ((d : Fμ) : L) ^ (m₀.natDegree - k) := by
    simp
  rw [e2, hdL', aeval_Dpoly, ← pow_mul, mul_comm]

end LambdaIntlocSol
p2m_reactivate "P2MW.S_ModularCurve_exists_pow_mul_minpoly_lambdaNModC_coeff_mem_adjoin.LambdaIntlocSol"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_pow_mul_minpoly_lambdaNModC_coeff_mem_adjoin.LambdaIntlocSol"

theorem solution (q : ℕ) [Fact q.Prime] (k : ℕ) :
    ∃ N : ℕ, (lambdaModC ℚ * (1 - 16 * lambdaModC ℚ) ^ 4) ^ N *
        ((minpoly (↥(IntermediateField.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)))) (lambdaNModC ℚ q)).coeff k
          : LaurentSeries ℚ) ∈ Algebra.adjoin ℚ ({lambdaModC ℚ} : Set (LaurentSeries ℚ)) :=
  LambdaIntlocSol.main q k

end S_ModularCurve_exists_pow_mul_minpoly_lambdaNModC_coeff_mem_adjoin
end P2MW
export P2MW.S_ModularCurve_exists_pow_mul_minpoly_lambdaNModC_coeff_mem_adjoin (solution)
