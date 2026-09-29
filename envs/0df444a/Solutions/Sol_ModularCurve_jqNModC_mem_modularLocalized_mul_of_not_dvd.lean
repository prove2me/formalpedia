-- Prove2me | solution 1 for ModularCurve.jqNModC_mem_modularLocalized_mul_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4721c4ef-1f83-5a9f-8b7e-9a5ef3164590

import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_modularPolynomial_kronecker
import Theorems.Thm_ModularCurve_jqNModC_mul_eq_pow
import Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jqNModC_mem_modularLocalized_mul_of_not_dvd
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_jqNModC_mem_modularLocalized_mul_of_not_dvd.ModularCurve"
open Polynomial

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.subring_le_localizedAtKer CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.redLocHom_apply CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom jqModC jqNModC jqNModC_one jqModC_eq_map_intCast qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_congr ModularPolynomialData transcendental_jqNModC transcendental_jqModC modularPolynomial_kronecker jqNModC_mul_eq_pow nonempty_modularPolynomialData"
p2m_open "ModularCurve"

section Furniture

variable {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]

private abbrev l2F : Type := LaurentSeries (AlgebraicClosure ℚ)

private abbrev l2K : Type := IsLocalRing.ResidueField A

private abbrev l2R (q : ℕ) [Fact q.Prime] : Subring l2F := CharPReduction.modularRing (N * q) A.toSubring

private abbrev l2O (q : ℕ) [Fact q.Prime] : Subring l2F :=
  CharPReduction.modularLocalized (N * q) A.toSubring (IsLocalRing.residue A)

private abbrev l2pi (q : ℕ) [Fact q.Prime] : l2O A N q →+* LaurentSeries (l2K A) :=
  CharPReduction.modularRedLocHom (N * q) A.toSubring (IsLocalRing.residue A)

private abbrev l2I (q : ℕ) [Fact q.Prime] : Ideal (l2O A N q) := RingHom.ker (l2pi A N q)

private theorem l2_R_le_O : l2R A N q ≤ l2O A N q :=
  CharPReduction.subring_le_localizedAtKer _ _ _ _

private def l2jO : l2O A N q :=
  ⟨jqModC (AlgebraicClosure ℚ), l2_R_le_O A N (CharPReduction.jqModC_mem_modularRing (N * q) A.toSubring)⟩

private def l2jNqO : l2O A N q :=
  ⟨jqNModC (AlgebraicClosure ℚ) (N * q),
    l2_R_le_O A N (CharPReduction.jqNModC_mem_modularRing (N * q) A.toSubring)⟩

private theorem l2_coe_jO : ((l2jO A N (q := q) : l2O A N q) : l2F) = jqModC (AlgebraicClosure ℚ) := rfl

private theorem l2_coe_jNqO :
    ((l2jNqO A N (q := q) : l2O A N q) : l2F) = jqNModC (AlgebraicClosure ℚ) (N * q) := rfl

private theorem l2_charP (hA : A.LiesOverPrime q) : CharP (l2K A) q := by
  have hmem : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simpa [ValuationSubring.LiesOverPrime] using hA
  have hq : ((q : ℕ) : l2K A) = 0 := by
    have h : IsLocalRing.residue A ((q : ℕ) : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa using h
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr hq

private theorem l2_coeffRed_jqModC (h : jqModC (AlgebraicClosure ℚ) ∈ CharPReduction.integralCoeffs A.toSubring) :
    CharPReduction.coeffRed A.toSubring (IsLocalRing.residue A) ⟨jqModC (AlgebraicClosure ℚ), h⟩ = jqModC (l2K A) := by
  ext n
  rw [CharPReduction.coeffRed_coeff]
  have hL : (⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h n⟩ : A.toSubring)
      = (((jqModC ℤ).coeff n : ℤ) : A.toSubring) := by
    ext
    push_cast
    rw [jqModC_eq_map_intCast, HahnSeries.map_coeff]
    rfl
  rw [hL, map_intCast]
  conv_rhs => rw [jqModC_eq_map_intCast]
  rw [HahnSeries.map_coeff]
  rfl

private theorem l2_coeffRed_jqNModC (M : ℕ) [NeZero M]
    (h : jqNModC (AlgebraicClosure ℚ) M ∈ CharPReduction.integralCoeffs A.toSubring) :
    CharPReduction.coeffRed A.toSubring (IsLocalRing.residue A) ⟨jqNModC (AlgebraicClosure ℚ) M, h⟩
      = jqNModC (l2K A) M := by
  have hqk : ∀ m : ℤ, (jqNModC (l2K A) M).coeff ((M : ℤ) * m) = (jqModC (l2K A)).coeff m := fun m => by
    rw [jqNModC, qExpand_coeff_mul]
  have hqk0 : ∀ {n : ℤ}, ¬ ((M : ℕ) : ℤ) ∣ n → (jqNModC (l2K A) M).coeff n = 0 := fun hn => by
    rw [jqNModC]
    exact qExpand_coeff_of_not_dvd _ _ hn
  have hqL : ∀ m : ℤ, (jqNModC (AlgebraicClosure ℚ) M).coeff ((M : ℤ) * m) = (jqModC (AlgebraicClosure ℚ)).coeff m :=
    fun m => by rw [jqNModC, qExpand_coeff_mul]
  have hqL0 : ∀ {n : ℤ}, ¬ ((M : ℕ) : ℤ) ∣ n → (jqNModC (AlgebraicClosure ℚ) M).coeff n = 0 := fun hn => by
    rw [jqNModC]
    exact qExpand_coeff_of_not_dvd _ _ hn
  ext n
  rw [CharPReduction.coeffRed_coeff]
  by_cases hn : ((M : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    have hL : (⟨(jqNModC (AlgebraicClosure ℚ) M).coeff ((M : ℤ) * m), h _⟩ : A.toSubring)
        = (((jqModC ℤ).coeff m : ℤ) : A.toSubring) := by
      ext
      push_cast
      rw [hqL, jqModC_eq_map_intCast, HahnSeries.map_coeff]
      rfl
    rw [hL, map_intCast, hqk]
    conv_rhs => rw [jqModC_eq_map_intCast]
    rw [HahnSeries.map_coeff]
    rfl
  · have hL : (⟨(jqNModC (AlgebraicClosure ℚ) M).coeff n, h n⟩ : A.toSubring) = 0 := by
      ext
      push_cast
      exact hqL0 hn
    rw [hL, map_zero, hqk0 hn]

private theorem l2_pi_jO : l2pi A N q (l2jO A N) = jqModC (l2K A) := by
  have h := CharPReduction.redLoc_coe (A := A.toSubring) (red := IsLocalRing.residue A) (R := l2R A N q)
    (hR := CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring)
    ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (N * q) A.toSubring⟩
  rw [CharPReduction.redRes_apply, l2_coeffRed_jqModC] at h
  exact h

private theorem l2_pi_jNqO : l2pi A N q (l2jNqO A N) = jqNModC (l2K A) (N * q) := by
  have h := CharPReduction.redLoc_coe (A := A.toSubring) (red := IsLocalRing.residue A) (R := l2R A N q)
    (hR := CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring)
    ⟨jqNModC (AlgebraicClosure ℚ) (N * q), CharPReduction.jqNModC_mem_modularRing (N * q) A.toSubring⟩
  rw [CharPReduction.redRes_apply, l2_coeffRed_jqNModC] at h
  exact h

private theorem l2_isUnit_of_pi_ne_zero (x : l2O A N q) (hx : l2pi A N q x ≠ 0) : IsUnit x := by
  obtain ⟨r, s, hs, hxs⟩ := (CharPReduction.mem_localizedAtKer _ _ _ _).mp x.2
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := IsLocalRing.residue A) x hxs
  rw [← CharPReduction.redLocHom_apply] at hspec
  have hr : r ∉ CharPReduction.redKer A.toSubring (IsLocalRing.residue A) (l2R A N q)
      (CharPReduction.modularRing_le_integralCoeffs (N * q) A.toSubring) := by
    rw [CharPReduction.notMem_redKer_iff, ← hspec]
    exact mul_ne_zero hx (CharPReduction.redRes_ne_zero_of_notMem hs)
  have hr0 : ((r : l2R A N q) : l2F) ≠ 0 := by
    intro h0
    apply hr
    rw [CharPReduction.redKer, RingHom.mem_ker]
    have : r = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hy : ((s : l2R A N q) : l2F) / (r : l2F) ∈ l2O A N q :=
    (CharPReduction.mem_localizedAtKer _ _ _ _).mpr ⟨s, r, hr, by rw [div_mul_cancel₀ _ hr0]⟩
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hy⟩, Subtype.ext ?_⟩
  change (x : l2F) * ((s : l2F) / (r : l2F)) = 1
  rw [mul_div_assoc', hxs, div_self hr0]

private theorem l2_ker_le_jacobson : RingHom.ker (l2pi A N q) ≤ (⊥ : Ideal (l2O A N q)).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  apply l2_isUnit_of_pi_ne_zero
  rw [map_add, map_mul, map_one, RingHom.mem_ker.mp hx, zero_mul, zero_add]
  exact one_ne_zero

private theorem l2_ker_isMaximal : (RingHom.ker (l2pi A N q)).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => ?_, fun J x _ hx hxJ => ?_⟩
  · rw [RingHom.mem_ker, map_one] at h
    exact one_ne_zero h
  · obtain ⟨u, rfl⟩ := l2_isUnit_of_pi_ne_zero A N x (RingHom.mem_ker.not.mp hx)
    simpa using J.mul_mem_left (↑u⁻¹ : l2O A N q) hxJ

end Furniture

section Polynomials

variable {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]

private def l2evJ (q : ℕ) [Fact q.Prime] : Polynomial ℤ →+* l2O A N q :=
  Polynomial.eval₂RingHom (Int.castRingHom (l2O A N q)) (l2jO A N)

private def l2P (data : ModularPolynomialData N) : Polynomial (l2O A N q) := data.Φ.map (l2evJ A N q)

private theorem l2P_monic (data : ModularPolynomialData N) : (l2P A N (q := q) data).Monic :=
  data.monic.map _

private theorem l2_aeval_P (data : ModularPolynomialData N) :
    Polynomial.aeval (R := l2O A N q) (jqNModC (AlgebraicClosure ℚ) N) (l2P A N data) = 0 := by
  have hrel : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC (AlgebraicClosure ℚ))).toRingHom
      (jqNModC (AlgebraicClosure ℚ) N) = 0 := by
    have h := data.eval_jqNModC_mul_eq_zero (AlgebraicClosure ℚ) 1
    have e : jqNModC (AlgebraicClosure ℚ) (1 * N) = jqNModC (AlgebraicClosure ℚ) N :=
      qExpand_congr (one_mul N) _
    rwa [jqNModC_one, e] at h
  rw [Polynomial.aeval_def, l2P, Polynomial.eval₂_map, ← hrel]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [l2evJ]
  · simp only [RingHom.comp_apply, l2evJ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, Polynomial.aeval_X]
    rfl

private theorem l2P_map_pi (data : ModularPolynomialData N) :
    (l2P A N data).map (l2pi A N q)
      = data.Φ.map (Polynomial.aeval (R := ℤ) (jqModC (l2K A))).toRingHom := by
  rw [l2P, Polynomial.map_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [l2evJ]
  · simp [l2evJ, l2_pi_jO]

private def l2G (dq : ModularPolynomialData q) : Polynomial (l2O A N q) :=
  dq.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom (l2O A N q))) (Polynomial.C (l2jNqO A N))

private theorem l2_aeval_G (dq : ModularPolynomialData q) :
    Polynomial.aeval (R := l2O A N q) (jqNModC (AlgebraicClosure ℚ) N) (l2G A N dq) = 0 := by
  have hrel := dq.eval_jqNModC_mul_eq_zero (AlgebraicClosure ℚ) N
  rw [Polynomial.aeval_def, l2G, ← Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, ← hrel]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

private theorem l2G_map_pi (hA : A.LiesOverPrime q) (dq : ModularPolynomialData q) :
    (l2G A N dq).map (l2pi A N q)
      = (Polynomial.X - Polynomial.C (jqNModC (l2K A) N)) ^ q
          * (Polynomial.X - Polynomial.C ((jqNModC (l2K A) N ^ q) ^ q)) := by
  haveI := l2_charP A hA
  haveI : CharP (LaurentSeries (l2K A)) q := charP_of_injective_ringHom HahnSeries.C_injective q
  have hNq : jqNModC (l2K A) (N * q) = jqNModC (l2K A) N ^ q := jqNModC_mul_eq_pow (l2K A) N

  have h1 : (l2G A N dq).map (l2pi A N q)
      = dq.Φ.eval₂ (Polynomial.mapRingHom (Int.castRingHom (LaurentSeries (l2K A))))
          (Polynomial.C (jqNModC (l2K A) N ^ q)) := by
    rw [l2G, ← Polynomial.coe_mapRingHom, Polynomial.hom_eval₂, Polynomial.coe_mapRingHom, Polynomial.map_C,
      l2_pi_jNqO, hNq]
    congr 1
    rw [Polynomial.mapRingHom_comp]
    congr 1
    exact RingHom.ext_int _ _

  have h2 : Polynomial.mapRingHom (Int.castRingHom (LaurentSeries (l2K A)))
      = (Polynomial.mapRingHom (ZMod.castHom (dvd_refl q) (LaurentSeries (l2K A)))).comp
          (Polynomial.mapRingHom (Int.castRingHom (ZMod q))) := by
    rw [Polynomial.mapRingHom_comp]
    congr 1
    exact RingHom.ext_int _ _
  rw [h1, h2, ← Polynomial.eval₂_map, modularPolynomial_kronecker q dq]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_mapRingHom, Polynomial.map_X]
  rw [sub_pow_char, ← Polynomial.C_pow, ← Polynomial.C_pow]

end Polynomials

section Ord

variable (k : Type*) [Field k]

private theorem l2_aeval_j_nzd :
    nonZeroDivisors (Polynomial k)
      ≤ Submonoid.comap (Polynomial.aeval (R := k) (jqModC k) : Polynomial k →ₐ[k] LaurentSeries k)
          (nonZeroDivisors (LaurentSeries k)) := by
  intro p hp
  rw [Submonoid.mem_comap]
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => nonZeroDivisors.ne_zero hp ?_
  exact (transcendental_iff_injective.mp (transcendental_jqModC k)) (by rw [h0, map_zero])

private def l2lift : RatFunc k →ₐ[k] LaurentSeries k :=
  RatFunc.liftAlgHom (Polynomial.aeval (R := k) (jqModC k)) (l2_aeval_j_nzd k)

private theorem l2lift_algebraMap (p : Polynomial k) :
    l2lift k (algebraMap (Polynomial k) (RatFunc k) p) = Polynomial.aeval (jqModC k) p := by
  have h := RatFunc.liftAlgHom_apply_div (Polynomial.aeval (R := k) (jqModC k)) (l2_aeval_j_nzd k) p 1
  rwa [map_one, div_one, map_one, div_one] at h

private theorem l2lift_X : l2lift k RatFunc.X = jqModC k := by
  rw [← RatFunc.algebraMap_X, l2lift_algebraMap, Polynomial.aeval_X]

private theorem l2lift_comp :
    ((l2lift k).toRingHom.comp (algebraMap (Polynomial k) (RatFunc k))).comp
        (Polynomial.mapRingHom (Int.castRingHom k))
      = (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp [l2lift_X]

private abbrev l2ratAlg : Algebra (RatFunc k) (LaurentSeries k) := (l2lift k).toRingHom.toAlgebra

variable {k}

private theorem l2_separable_bar {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (data : ModularPolynomialData N) :
    (data.Φ.map (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom).Separable := by
  have h := (data.separable_map_ratFunc_of_natCast_ne_zero k N hN).map (f := (l2lift k).toRingHom)
  rwa [Polynomial.map_map, Polynomial.map_map, l2lift_comp] at h

private theorem l2_twist {q : ℕ} [Fact q.Prime] [CharP k q] {M : ℕ} [NeZero M] (data : ModularPolynomialData M)
    {x y : LaurentSeries k} (h : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y = 0) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (x ^ q)).toRingHom (y ^ q) = 0 := by
  haveI : CharP (LaurentSeries k) q := charP_of_injective_ringHom HahnSeries.C_injective q
  haveI : ExpChar (LaurentSeries k) q := ExpChar.prime Fact.out
  have h' := congrArg (frobenius (LaurentSeries k) q) h
  rw [Polynomial.hom_eval₂, map_zero, frobenius_def] at h'
  convert h' using 2
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp [frobenius_def]

private theorem l2_aeval_ratPoly {M : ℕ} [NeZero M] (data : ModularPolynomialData M) (y : LaurentSeries k) :
    @Polynomial.aeval (RatFunc k) (LaurentSeries k) _ _ (l2ratAlg k) y
        ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (algebraMap (Polynomial k) (RatFunc k)))
      = data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom y := by
  letI := l2ratAlg k
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_map, ← l2lift_comp k]
  rfl

private theorem l2_aeval_ratPoly_twist {q : ℕ} (M : ℕ) [NeZero M] (data : ModularPolynomialData M)
    (y : LaurentSeries k) :
    @Polynomial.aeval (RatFunc k) (LaurentSeries k) _ _ (l2ratAlg k) y
        (((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map (Polynomial.expand k (q * q)).toRingHom).map
          (algebraMap (Polynomial k) (RatFunc k)))
      = data.Φ.eval₂ (Polynomial.aeval (R := ℤ) ((jqModC k ^ q) ^ q)).toRingHom y := by
  letI := l2ratAlg k
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_map, Polynomial.eval₂_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp [RingHom.algebraMap_toAlgebra]
  · simp [RingHom.algebraMap_toAlgebra, l2lift_X, pow_mul]

variable (k)

private theorem phiN_eval_pow_pow_ne_zero {q : ℕ} [Fact q.Prime] [CharP k q] {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N)
    (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom ((jqNModC k N ^ q) ^ q) ≠ 0 := by
  intro h0
  have hN : (N : k) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff k q N).mp h)

  have hrel : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC k)).toRingHom (jqNModC k N) = 0 := by
    have h := data.eval_jqNModC_mul_eq_zero k 1
    have e : jqNModC k (1 * N) = jqNModC k N := qExpand_congr (one_mul N) _
    rwa [jqNModC_one, e] at h
  have htw := l2_twist data (l2_twist data hrel)
  letI := l2ratAlg k
  set Φk : Polynomial (Polynomial k) := data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)) with hΦk
  set ΦR : Polynomial (RatFunc k) := Φk.map (algebraMap (Polynomial k) (RatFunc k)) with hΦR
  set ΦR' : Polynomial (RatFunc k) :=
    (Φk.map (Polynomial.expand k (q * q)).toRingHom).map (algebraMap (Polynomial k) (RatFunc k)) with hΦR'
  have hΦkm : Φk.Monic := data.monic.map _
  have hRm : ΦR.Monic := hΦkm.map _
  have hR'm : ΦR'.Monic := (hΦkm.map _).map _
  have hirr : Irreducible ΦR := data.irreducible_map_ratFunc_of_natCast_ne_zero k N hN
  have hR0 : Polynomial.aeval ((jqNModC k N ^ q) ^ q) ΦR = 0 := by
    rw [hΦR, hΦk, l2_aeval_ratPoly]; exact h0
  have hR'0 : Polynomial.aeval ((jqNModC k N ^ q) ^ q) ΦR' = 0 := by
    rw [hΦR', hΦk, l2_aeval_ratPoly_twist]; exact htw
  have hmin : ΦR = minpoly (RatFunc k) ((jqNModC k N ^ q) ^ q) := minpoly.eq_of_irreducible_of_monic hirr hR0 hRm
  have hdvd : ΦR ∣ ΦR' := by
    rw [hmin]
    exact minpoly.dvd (RatFunc k) _ hR'0
  have hdeg : ΦR'.natDegree ≤ ΦR.natDegree := by
    rw [hΦR', hΦR, (hΦkm.map _).natDegree_map, hΦkm.natDegree_map, hΦkm.natDegree_map]
  have heq : ΦR' = ΦR := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hRm hR'm hdvd hdeg

  have hconst : ∀ i, (Φk.coeff i).natDegree = 0 := by
    intro i
    have hc := congrArg (fun p => Polynomial.coeff p i) heq
    simp only [hΦR', hΦR, Polynomial.coeff_map] at hc
    have hc' : Polynomial.expand k (q * q) (Φk.coeff i) = Φk.coeff i :=
      IsFractionRing.injective (Polynomial k) (RatFunc k) hc
    have hdeg' := congrArg Polynomial.natDegree hc'
    rw [Polynomial.natDegree_expand] at hdeg'
    have hq2 : 2 ≤ q * q := by nlinarith [(Fact.out : q.Prime).two_le]
    by_contra hne
    have hpos : 0 < (Φk.coeff i).natDegree := Nat.pos_of_ne_zero hne
    nlinarith

  set Q : Polynomial k := Φk.map Polynomial.constantCoeff with hQ
  have hQm : Q.Monic := hΦkm.map _
  have hQ0 : Polynomial.aeval (jqNModC k N) Q = 0 := by
    have hrel' : Φk.eval₂ (Polynomial.aeval (R := k) (jqModC k)).toRingHom (jqNModC k N) = 0 := by
      rw [hΦk, Polynomial.eval₂_map, ← hrel]
      congr 1
      apply Polynomial.ringHom_ext <;> simp
    rw [Polynomial.aeval_def, hQ, Polynomial.eval₂_map, ← hrel', Polynomial.eval₂_eq_sum_range,
      Polynomial.eval₂_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [Polynomial.eq_C_of_natDegree_eq_zero (hconst i)]
    simp
  exact transcendental_jqNModC k N ⟨Q, hQm.ne_zero, hQ0⟩

variable {k}

private theorem l2_mem_range_of_separable_of_pow {κ E : Type*} [Field κ] [Field E] [Algebra κ E] {q : ℕ}
    [Fact q.Prime] [CharP E q] {x : E} (hint : IsIntegral κ x) (hsep : (minpoly κ x).Separable)
    (hpow : x ^ q ∈ (algebraMap κ E).range) : x ∈ (algebraMap κ E).range := by
  obtain ⟨c, hc⟩ := hpow
  have hdvd : minpoly κ x ∣ Polynomial.X ^ q - Polynomial.C c := minpoly.dvd κ x (by simp [hc])
  have hdvdE : (minpoly κ x).map (algebraMap κ E) ∣ (Polynomial.X - Polynomial.C x) ^ q := by
    have h := Polynomial.map_dvd (algebraMap κ E) hdvd
    rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hc, Polynomial.C_pow,
      ← sub_pow_char] at h
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow (Polynomial.prime_X_sub_C x) q).mp hdvdE
  have hsepE : ((minpoly κ x).map (algebraMap κ E)).Separable := hsep.map
  have hi1 : i ≤ 1 := by
    by_contra hlt
    have hlt' : 2 ≤ i := by omega
    have h2 : (Polynomial.X - Polynomial.C x) * (Polynomial.X - Polynomial.C x)
        ∣ (minpoly κ x).map (algebraMap κ E) := by
      rw [← sq]
      exact (pow_dvd_pow _ hlt').trans hassoc.symm.dvd
    exact Polynomial.not_isUnit_X_sub_C x (hsepE.squarefree _ h2)
  have hdegE : ((minpoly κ x).map (algebraMap κ E)).natDegree = i := by
    rw [Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hassoc),
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  rw [Polynomial.natDegree_map] at hdegE
  have hpos := minpoly.natDegree_pos hint
  exact minpoly.natDegree_eq_one_iff.mp (by omega)

end Ord

section Bezout

variable {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]

private theorem l2_exists_bezout (hA : A.LiesOverPrime q) (hqN : ¬ q ∣ N) (data : ModularPolynomialData N)
    (dq : ModularPolynomialData q) :
    ∃ (a b : Polynomial (l2O A N q)) (o : l2O A N q),
      ∀ i, (a * l2P A N data + b * l2G A N dq - (Polynomial.X - Polynomial.C o)).coeff i
        ∈ RingHom.ker (l2pi A N q) := by
  haveI hK : CharP (l2K A) q := l2_charP A hA
  haveI : CharP (LaurentSeries (l2K A)) q := charP_of_injective_ringHom HahnSeries.C_injective q
  have hN : (N : l2K A) ≠ 0 := fun h => hqN ((CharP.cast_eq_zero_iff (l2K A) q N).mp h)
  haveI hmax : (l2I A N q).IsMaximal := l2_ker_isMaximal A N
  letI : Field (l2O A N q ⧸ l2I A N q) := Ideal.Quotient.field _

  let ι : (l2O A N q ⧸ l2I A N q) →+* LaurentSeries (l2K A) :=
    Ideal.Quotient.lift (l2I A N q) (l2pi A N q) fun a ha => RingHom.mem_ker.mp ha
  have hιmk : ∀ x : l2O A N q, ι (Ideal.Quotient.mk (l2I A N q) x) = l2pi A N q x := fun x =>
    Ideal.Quotient.lift_mk _ _ _
  have hιcomp : ι.comp (Ideal.Quotient.mk (l2I A N q)) = l2pi A N q := RingHom.ext hιmk
  have hι : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).mpr fun a ha => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hιmk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr ha)
  letI : Algebra (l2O A N q ⧸ l2I A N q) (LaurentSeries (l2K A)) := ι.toAlgebra
  have halg : algebraMap (l2O A N q ⧸ l2I A N q) (LaurentSeries (l2K A)) = ι := rfl

  set Pb := (l2P A N data).map (Ideal.Quotient.mk (l2I A N q)) with hPb
  set Gb := (l2G A N dq).map (Ideal.Quotient.mk (l2I A N q)) with hGb
  set jb := jqNModC (l2K A) N with hjb
  have hPbE : Pb.map ι = data.Φ.map (Polynomial.aeval (R := ℤ) (jqModC (l2K A))).toRingHom := by
    rw [hPb, Polynomial.map_map, hιcomp, l2P_map_pi]
  have hGbE : Gb.map ι = (Polynomial.X - Polynomial.C jb) ^ q * (Polynomial.X - Polynomial.C ((jb ^ q) ^ q)) := by
    rw [hGb, Polynomial.map_map, hιcomp, l2G_map_pi A N hA]
  have hPbm : Pb.Monic := (l2P_monic A N data).map _
  have hPbsepE : (Pb.map ι).Separable := by
    rw [hPbE]
    exact l2_separable_bar hN data
  have hPbsep : Pb.Separable := (Polynomial.separable_map ι).mp hPbsepE

  have hrelK : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqModC (l2K A))).toRingHom jb = 0 := by
    have h := data.eval_jqNModC_mul_eq_zero (l2K A) 1
    have e : jqNModC (l2K A) (1 * N) = jqNModC (l2K A) N := qExpand_congr (one_mul N) _
    rwa [jqNModC_one, e] at h
  have hPb_jb : Polynomial.aeval jb Pb = 0 := by
    rw [Polynomial.aeval_def, halg, ← Polynomial.eval_map, hPbE, Polynomial.eval_map]; exact hrelK

  have hint : IsIntegral (l2O A N q ⧸ l2I A N q) jb := ⟨Pb, hPbm, by rw [← Polynomial.aeval_def]; exact hPb_jb⟩
  have hsep : (minpoly (l2O A N q ⧸ l2I A N q) jb).Separable := hPbsep.of_dvd (minpoly.dvd _ _ hPb_jb)
  have hpow : jb ^ q ∈ (algebraMap (l2O A N q ⧸ l2I A N q) (LaurentSeries (l2K A))).range :=
    ⟨Ideal.Quotient.mk (l2I A N q) (l2jNqO A N), by rw [halg, hιmk, l2_pi_jNqO, hjb, jqNModC_mul_eq_pow]⟩
  obtain ⟨jK, hjK⟩ := l2_mem_range_of_separable_of_pow hint hsep hpow
  rw [halg] at hjK

  have hroot : Pb.IsRoot jK := by
    rw [Polynomial.IsRoot.def]
    apply hι
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hPbE, hjK, Polynomial.eval_map]
    exact hrelK
  set P1 := Pb /ₘ (Polynomial.X - Polynomial.C jK) with hP1
  have hfac : (Polynomial.X - Polynomial.C jK) * P1 = Pb := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  set z := (jK ^ q) ^ q with hz
  have hιz : ι z = (jb ^ q) ^ q := by
    rw [hz, map_pow, map_pow, hjK]
  have hGbfac : Gb = (Polynomial.X - Polynomial.C jK) ^ q * (Polynomial.X - Polynomial.C z) := by
    apply Polynomial.map_injective ι hι
    rw [hGbE, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.map_C, hjK, hιz]

  have hP1jK : ¬ P1.IsRoot jK := by
    intro hr
    obtain ⟨P2, hP2⟩ := Polynomial.dvd_iff_isRoot.mpr hr
    have h2 : (Polynomial.X - Polynomial.C jK) * (Polynomial.X - Polynomial.C jK) ∣ Pb :=
      ⟨P2, by rw [← hfac, hP2]; ring⟩
    exact Polynomial.not_isUnit_X_sub_C jK (hPbsep.squarefree _ h2)
  have hP1z : ¬ P1.IsRoot z := by
    intro hr
    have hPbz : Pb.eval z = 0 := by
      rw [← hfac, Polynomial.eval_mul, Polynomial.IsRoot.def.mp hr, mul_zero]
    apply phiN_eval_pow_pow_ne_zero (l2K A) hqN data
    have h := congrArg ι hPbz
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hPbE, Polynomial.eval_map, hιz] at h
    exact h
  have hcop : IsCoprime P1 ((Polynomial.X - Polynomial.C jK) ^ (q - 1) * (Polynomial.X - Polynomial.C z)) := by
    have h1 : IsCoprime P1 (Polynomial.X - Polynomial.C jK) :=
      (((Polynomial.irreducible_X_sub_C jK).coprime_iff_not_dvd).mpr
        fun h => hP1jK (Polynomial.dvd_iff_isRoot.mp h)).symm
    have h2 : IsCoprime P1 (Polynomial.X - Polynomial.C z) :=
      (((Polynomial.irreducible_X_sub_C z).coprime_iff_not_dvd).mpr
        fun h => hP1z (Polynomial.dvd_iff_isRoot.mp h)).symm
    exact h1.pow_right.mul_right h2
  obtain ⟨u, v, huv⟩ := hcop

  have hq1 : (Polynomial.X - Polynomial.C jK) ^ q
      = (Polynomial.X - Polynomial.C jK) * (Polynomial.X - Polynomial.C jK) ^ (q - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : q.Prime).one_lt.le]
  have hbez : u * Pb + v * Gb = Polynomial.X - Polynomial.C jK := by
    rw [← hfac, hGbfac, hq1]
    linear_combination (Polynomial.X - Polynomial.C jK) * huv

  obtain ⟨a, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective u
  obtain ⟨b, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective v
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective jK
  refine ⟨a, b, o, fun i => ?_⟩
  rw [RingHom.mem_ker, ← hιmk, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ← hPb, ← hGb, hbez, sub_self,
    Polynomial.coeff_zero, map_zero]

end Bezout

section Assembly

variable {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]

private abbrev l2M (q : ℕ) [Fact q.Prime] : Submodule (l2O A N q) l2F :=
  Subalgebra.toSubmodule (Algebra.adjoin (l2O A N q) {jqNModC (AlgebraicClosure ℚ) N})

private theorem l2_jN_mem_M : jqNModC (AlgebraicClosure ℚ) N ∈ l2M A N q :=
  Algebra.self_mem_adjoin_singleton _ _

set_option synthInstance.maxHeartbeats 1600000 in

private abbrev l2IM (q : ℕ) [Fact q.Prime] : Submodule (l2O A N q) l2F := RingHom.ker (l2pi A N q) • l2M A N q

private theorem l2M_fg (data : ModularPolynomialData N) : (l2M A N q).FG :=
  IsIntegral.fg_adjoin_singleton ⟨l2P A N data, l2P_monic A N data, by
    simpa [Polynomial.aeval_def] using l2_aeval_P A N (q := q) data⟩

private theorem l2_smul_mul_mem {x y : l2F} (hx : x ∈ l2IM A N q) (hy : y ∈ l2M A N q) : x * y ∈ l2IM A N q := by
  refine Submodule.smul_induction_on hx (fun i hi m hm => ?_) (fun x₁ x₂ h₁ h₂ => ?_)
  · rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul hi (Subalgebra.mul_mem _ hm hy)
  · rw [add_mul]
    exact Submodule.add_mem _ h₁ h₂

private theorem l2_jN_mem_sup (hA : A.LiesOverPrime q) (hqN : ¬ q ∣ N) (data : ModularPolynomialData N)
    (dq : ModularPolynomialData q) :
    jqNModC (AlgebraicClosure ℚ) N
      ∈ Subalgebra.toSubmodule (⊥ : Subalgebra (l2O A N q) l2F) ⊔ l2IM A N q := by
  obtain ⟨a, b, o, hD⟩ := l2_exists_bezout A N hA hqN data dq
  set D : Polynomial (l2O A N q) := a * l2P A N data + b * l2G A N dq - (Polynomial.X - Polynomial.C o) with hDdef
  have hval : Polynomial.aeval (R := l2O A N q) (jqNModC (AlgebraicClosure ℚ) N) D
      = -(jqNModC (AlgebraicClosure ℚ) N - algebraMap (l2O A N q) l2F o) := by
    simp only [hDdef, map_sub, map_add, map_mul, l2_aeval_P, l2_aeval_G, mul_zero, add_zero, Polynomial.aeval_X,
      Polynomial.aeval_C, zero_sub]
  have hDmem : Polynomial.aeval (R := l2O A N q) (jqNModC (AlgebraicClosure ℚ) N) D ∈ l2IM A N q := by
    rw [Polynomial.aeval_eq_sum_range]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem_smul (hD i) (Subalgebra.pow_mem _ (l2_jN_mem_M A N) i)
  have hrepr : jqNModC (AlgebraicClosure ℚ) N
      = algebraMap (l2O A N q) l2F o - Polynomial.aeval (R := l2O A N q) (jqNModC (AlgebraicClosure ℚ) N) D := by
    rw [hval]; ring
  rw [hrepr]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Algebra.mem_bot.mpr ⟨o, rfl⟩)) (Submodule.mem_sup_right hDmem)

private theorem l2M_le_sup (hA : A.LiesOverPrime q) (hqN : ¬ q ∣ N) (data : ModularPolynomialData N)
    (dq : ModularPolynomialData q) :
    l2M A N q ≤ Subalgebra.toSubmodule (⊥ : Subalgebra (l2O A N q) l2F) ⊔ l2IM A N q := by
  intro x hx
  refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact l2_jN_mem_sup A N hA hqN data dq
  · intro r
    exact Submodule.mem_sup_left (Algebra.mem_bot.mpr ⟨r, rfl⟩)
  · intro y z _ _ hy hz
    exact Submodule.add_mem _ hy hz
  · intro y z _ hz' hy hz
    obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨z₀, hz₀, z₁, hz₁, rfl⟩ := Submodule.mem_sup.mp hz
    have hzM : z₀ + z₁ ∈ l2M A N q := hz'
    have h00 : y₀ * z₀ ∈ Subalgebra.toSubmodule (⊥ : Subalgebra (l2O A N q) l2F) :=
      Subalgebra.mul_mem _ hy₀ hz₀
    have h1 : y₁ * (z₀ + z₁) ∈ l2IM A N q := l2_smul_mul_mem A N hy₁ hzM
    have h2 : y₀ * z₁ ∈ l2IM A N q := by
      obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp hy₀
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ r hz₁
    have hsplit : (y₀ + y₁) * (z₀ + z₁) = y₀ * z₀ + (y₀ * z₁ + y₁ * (z₀ + z₁)) := by ring
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h00) (Submodule.mem_sup_right (Submodule.add_mem _ h2 h1))

end Assembly

end ModularCurve

end

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) :
    jqNModC (AlgebraicClosure ℚ) N
      ∈ CharPReduction.modularLocalized (N * q) A.toSubring (IsLocalRing.residue A) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  obtain ⟨dq⟩ := nonempty_modularPolynomialData q
  have hle : l2M A N q ≤ Subalgebra.toSubmodule (⊥ : Subalgebra (l2O A N q) l2F) :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (l2M_fg A N data) (l2_ker_le_jacobson A N)
      (l2M_le_sup A N hA hqN data dq)
  obtain ⟨o, ho⟩ := Algebra.mem_bot.mp (hle (l2_jN_mem_M A N))
  rw [← ho]
  exact o.2

end S_ModularCurve_jqNModC_mem_modularLocalized_mul_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_jqNModC_mem_modularLocalized_mul_of_not_dvd (solution)
