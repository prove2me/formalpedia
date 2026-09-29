-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_mul_eq_natCast_mul_add_jInvChartInf_mul_of_coeff_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b6c9abe1-cf14-51c1-b357-0b2fa01d8c7a

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_mem_adjoin_jq_inv_of_isIntegral_and_exists_mul_eq
import Theorems.Thm_ModularCurve_functionFieldGeneration
import Theorems.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
import Theorems.Thm_Subalgebra_exists_mul_mem_map_ker_of_eval_derivative_map_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_mul_eq_natCast_mul_add_jInvChartInf_mul_of_coeff_zero_mem
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open scoped Classical
open Polynomial ModularCurve WithZero IntermediateField

namespace CuspInftyTower

local notation "Λ" => LaurentSeries ℚ

section QAdic

def 𝒪 : Subring Λ := (Valued.v : Valuation Λ ℤᵐ⁰).integer

theorem mem_𝒪_iff (f : Λ) : f ∈ 𝒪 ↔ ∀ n : ℤ, n < 0 → f.coeff n = 0 := by
  rw [𝒪, Valuation.mem_integer_iff]
  have h := LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := ℚ) (D := 0) (f := f)
  simpa using h

theorem exists_powerSeries_of_mem_𝒪 {f : Λ} (hf : f ∈ 𝒪) : ∃ F : PowerSeries ℚ, (F : Λ) = f :=
  (LaurentSeries.val_le_one_iff_eq_coe (K := ℚ) f).mp hf

theorem coe_powerSeries_mem_𝒪 (F : PowerSeries ℚ) : (F : Λ) ∈ 𝒪 :=
  (LaurentSeries.val_le_one_iff_eq_coe (K := ℚ) (F : Λ)).mpr ⟨F, rfl⟩

theorem coeff_zero_coe_powerSeries (F : PowerSeries ℚ) :
    (F : Λ).coeff 0 = PowerSeries.constantCoeff F := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, LaurentSeries.coeff_coe_powerSeries]

theorem C_mem_𝒪 (c : ℚ) : (HahnSeries.C c : Λ) ∈ 𝒪 := by
  rw [mem_𝒪_iff]
  intro n hn
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn.ne]

def ρ : ↥𝒪 →+* ℚ where
  toFun f := (f : Λ).coeff 0
  map_one' := by simp
  map_mul' f g := by
    obtain ⟨F, hF⟩ := exists_powerSeries_of_mem_𝒪 f.2
    obtain ⟨G, hG⟩ := exists_powerSeries_of_mem_𝒪 g.2
    change ((f : Λ) * (g : Λ)).coeff 0 = (f : Λ).coeff 0 * (g : Λ).coeff 0
    rw [← hF, ← hG, ← map_mul]
    change ((F * G : PowerSeries ℚ) : Λ).coeff 0 = (F : Λ).coeff 0 * (G : Λ).coeff 0
    rw [coeff_zero_coe_powerSeries, coeff_zero_coe_powerSeries, coeff_zero_coe_powerSeries, map_mul]
  map_zero' := by simp
  map_add' f g := by simp

@[scoped simp] theorem ρ_apply (f : ↥𝒪) : ρ f = (f : Λ).coeff 0 := rfl

theorem coeff_zero_mul {f g : Λ} (hf : f ∈ 𝒪) (hg : g ∈ 𝒪) :
    (f * g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  have := map_mul ρ ⟨f, hf⟩ ⟨g, hg⟩
  simpa using this

theorem coeff_zero_pow {f : Λ} (hf : f ∈ 𝒪) (n : ℕ) : (f ^ n).coeff 0 = f.coeff 0 ^ n := by
  have := map_pow ρ ⟨f, hf⟩ n
  simpa using this

theorem inv_mem_𝒪_and_coeff {f : Λ} (hf : f ∈ 𝒪) (h0 : f.coeff 0 ≠ 0) :
    f⁻¹ ∈ 𝒪 ∧ f⁻¹.coeff 0 = (f.coeff 0)⁻¹ := by
  obtain ⟨Φ, hΦ⟩ := exists_powerSeries_of_mem_𝒪 hf
  have hc : PowerSeries.constantCoeff Φ ≠ 0 := by
    rwa [← coeff_zero_coe_powerSeries, hΦ]
  have hinv : f⁻¹ = ((Φ⁻¹ : PowerSeries ℚ) : Λ) := by
    have hf0 : f ≠ 0 := fun h => h0 (by rw [h, HahnSeries.coeff_zero])
    apply mul_left_cancel₀ hf0
    rw [mul_inv_cancel₀ hf0, ← hΦ, ← map_mul, PowerSeries.mul_inv_cancel Φ hc, map_one]
  refine ⟨by rw [hinv]; exact coe_powerSeries_mem_𝒪 _, ?_⟩
  rw [hinv, coeff_zero_coe_powerSeries, PowerSeries.constantCoeff_inv, ← hΦ,
    coeff_zero_coe_powerSeries]

def 𝔮 : Λ := HahnSeries.single (1 : ℤ) 1

theorem 𝔮_pow (n : ℕ) : 𝔮 ^ n = HahnSeries.single (n : ℤ) (1 : ℚ) := by
  rw [𝔮, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]

theorem 𝔮_ne_zero : 𝔮 ≠ 0 := by
  rw [𝔮]; exact HahnSeries.single_ne_zero one_ne_zero

theorem 𝔮_pow_mul_mem_𝒪 (n : ℕ) {f : Λ} (hf : f ∈ 𝒪) : 𝔮 ^ n * f ∈ 𝒪 := by
  rw [mem_𝒪_iff] at hf ⊢
  intro m hm
  rw [𝔮_pow, HahnSeries.coeff_single_mul, one_mul]
  exact hf _ (by omega)

theorem coeff_zero_𝔮_pow_mul {n : ℕ} (hn : 0 < n) {f : Λ} (hf : f ∈ 𝒪) :
    (𝔮 ^ n * f).coeff 0 = 0 := by
  rw [𝔮_pow, HahnSeries.coeff_single_mul, one_mul]
  exact (mem_𝒪_iff f).mp hf _ (by omega)

theorem 𝔮_mul_jq : 𝔮 * jq = ((jNumQ : PowerSeries ℚ) : Λ) := by
  rw [𝔮, jq, ← mul_assoc, HahnSeries.single_mul_single, one_mul,
    show (1 : ℤ) + -1 = 0 by norm_num, HahnSeries.single_zero_one, one_mul]

theorem 𝔮_mul_jq_mem_𝒪 : 𝔮 * jq ∈ 𝒪 := by rw [𝔮_mul_jq]; exact coe_powerSeries_mem_𝒪 _

theorem coeff_zero_𝔮_mul_jq : (𝔮 * jq).coeff 0 = 1 := by
  rw [𝔮_mul_jq, coeff_zero_coe_powerSeries, constantCoeff_jNumQ]

theorem jq_inv_mem_𝒪_and_coeff : jq⁻¹ ∈ 𝒪 ∧ jq⁻¹.coeff 0 = 0 := by
  have h := inv_mem_𝒪_and_coeff 𝔮_mul_jq_mem_𝒪 (by rw [coeff_zero_𝔮_mul_jq]; exact one_ne_zero)
  have heq : jq⁻¹ = 𝔮 ^ 1 * (𝔮 * jq)⁻¹ := by
    rw [pow_one, mul_inv, ← mul_assoc, mul_inv_cancel₀ 𝔮_ne_zero, one_mul]
  rw [heq]
  exact ⟨𝔮_pow_mul_mem_𝒪 1 h.1, coeff_zero_𝔮_pow_mul one_pos h.1⟩

variable (e : ℕ) [NeZero e]

theorem qExpand_mem_𝒪 {f : Λ} (hf : f ∈ 𝒪) : qExpand ℚ e f ∈ 𝒪 := by
  rw [mem_𝒪_iff] at hf ⊢
  intro n hn
  by_cases hdvd : (e : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    apply hf
    have he : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
    by_contra hk
    push Not at hk
    exact absurd hn (not_lt.mpr (mul_nonneg he.le hk))
  · exact qExpand_coeff_of_not_dvd (R := ℚ) e f hdvd

theorem coeff_zero_qExpand (f : Λ) : (qExpand ℚ e f).coeff 0 = f.coeff 0 := by
  have h := qExpand_coeff_mul (R := ℚ) e f 0
  rwa [mul_zero] at h

theorem qExpand_ne_zero {f : Λ} (hf : f ≠ 0) : qExpand ℚ e f ≠ 0 := fun h =>
  hf (qExpand_injective (R := ℚ) (N := e) (by rw [h, map_zero]))

end QAdic

section Zp

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Zp : Type := ↥(GaloisRep.ratLocalizedAt p)

scoped instance span_p_isPrime : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp.out)

scoped instance : IsDiscreteValuationRing (Zp p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p hp.out
scoped instance : IsFractionRing (Zp p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
scoped instance isLocalizationAtPrime : IsLocalization.AtPrime (Zp p) (Ideal.span {(p : ℤ)}) :=
  GaloisRep.isLocalization_ratLocalizedAt hp.out

theorem inv_intCast_mem {y : ℤ} (hy : ¬ (p : ℤ) ∣ y) :
    ((y : ℚ))⁻¹ ∈ GaloisRep.ratLocalizedAt p := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ dvd_zero _)
  change ((y : ℚ)⁻¹).den.Coprime p
  rw [Rat.inv_intCast_den, if_neg hy0]
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr ?_)
  intro h
  exact hy (Int.natCast_dvd.mpr h)

theorem maximalIdeal_eq : IsLocalRing.maximalIdeal (Zp p) = Ideal.span {(p : Zp p)} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(p : ℤ)}) (Zp p), Ideal.map_span,
    Set.image_singleton, map_natCast]

theorem mem_maximalIdeal_iff (x : Zp p) :
    x ∈ IsLocalRing.maximalIdeal (Zp p) ↔ ∃ c : Zp p, x = p * c := by
  rw [maximalIdeal_eq, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [← hc, mul_comm]⟩
  · rintro ⟨c, hc⟩; exact ⟨c, by rw [hc, mul_comm]⟩

def InP (r : ℚ) : Prop := ∃ c ∈ GaloisRep.ratLocalizedAt p, r = (p : ℚ) * c

theorem inP_iff (x : Zp p) : InP p (x : ℚ) ↔ x ∈ IsLocalRing.maximalIdeal (Zp p) := by
  rw [mem_maximalIdeal_iff]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨⟨c, hc⟩, Subtype.ext (by simpa using h)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, c.2, by simpa using congrArg (fun z : Zp p => (z : ℚ)) hc⟩

theorem not_inP_iff_isUnit (x : Zp p) : ¬ InP p (x : ℚ) ↔ IsUnit x := by
  rw [inP_iff, ← IsLocalRing.notMem_maximalIdeal]

theorem not_inP_one : ¬ InP p ((1 : Zp p) : ℚ) := by
  rw [not_inP_iff_isUnit]; exact isUnit_one

theorem inP_zero : InP p 0 := ⟨0, Subring.zero_mem _, by simp⟩

theorem exists_int_sub_mem (z : Zp p) : ∃ n : ℤ, z - (n : Zp p) ∈ IsLocalRing.maximalIdeal (Zp p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set D : ℕ := (z : ℚ).den with hD
  set N : ℤ := (z : ℚ).num with hN
  have hDcop : D.Coprime p := z.2
  set d' : ℕ := ((D : ZMod p)⁻¹).val with hd'
  have hmod : ((D * d' : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_mul, hd', ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one D hDcop]
  have hdvd : (p : ℤ) ∣ ((D * d' : ℕ) : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [← Nat.cast_mul, hmod, sub_self]
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨N * d', ?_⟩
  rw [mem_maximalIdeal_iff]

  have hDne : (D : ℚ) ≠ 0 := by exact_mod_cast (z : ℚ).den_ne_zero
  have hDinv : ((D : ℤ) : ℚ)⁻¹ ∈ GaloisRep.ratLocalizedAt p := by
    refine inv_intCast_mem p (fun h => ?_)
    have : p ∣ D := Int.natCast_dvd_natCast.mp h
    exact hp.out.one_lt.ne' ((Nat.coprime_comm.mp hDcop).eq_one_of_dvd this ▸ rfl)
  refine ⟨⟨-((N : ℚ) * k) * ((D : ℤ) : ℚ)⁻¹, Subring.mul_mem _
    (Subring.neg_mem _ (Subring.mul_mem _ (intCast_mem _ _) (intCast_mem _ _))) hDinv⟩,
    Subtype.ext ?_⟩
  have hz : (z : ℚ) = N / D := by rw [hD, hN, Rat.num_div_den]
  have hk' : ((D : ℤ) : ℚ) * (d' : ℚ) - 1 = (p : ℚ) * (k : ℚ) := by exact_mod_cast hk
  have key : (N : ℚ) / D - ((N * d' : ℤ) : ℚ) = (p : ℚ) * (-((N : ℚ) * k) * ((D : ℤ) : ℚ)⁻¹) := by
    push_cast
    field_simp
    linear_combination (-(N : ℚ)) * hk'
  rw [AddSubgroupClass.coe_sub, Subring.coe_mul, Subring.coe_intCast, Subring.coe_natCast, hz]
  push_cast at key ⊢
  exact key

theorem residue_int_surjective :
    Function.Surjective fun n : ℤ => IsLocalRing.residue (Zp p) (n : Zp p) := by
  intro k
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective k
  obtain ⟨n, hn⟩ := exists_int_sub_mem p z
  refine ⟨n, ?_⟩
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hn

end Zp

section IntB

variable (p : ℕ) [hp : Fact p.Prime]

def uΛ : Λ := jq⁻¹

theorem uΛ_ne_zero : uΛ ≠ 0 := inv_ne_zero jq_ne_zero

theorem uΛ_mul_jq : uΛ * jq = 1 := inv_mul_cancel₀ jq_ne_zero

abbrev A0 : Subalgebra (Zp p) Λ := Algebra.adjoin (Zp p) {uΛ}

def IsIntB (x : Λ) : Prop := IsIntegral ↥(A0 p) x

variable {p}

theorem IsIntB.add {x y : Λ} (hx : IsIntB p x) (hy : IsIntB p y) : IsIntB p (x + y) := IsIntegral.add hx hy
theorem IsIntB.mul {x y : Λ} (hx : IsIntB p x) (hy : IsIntB p y) : IsIntB p (x * y) := IsIntegral.mul hx hy
theorem IsIntB.pow {x : Λ} (hx : IsIntB p x) (n : ℕ) : IsIntB p (x ^ n) := IsIntegral.pow hx n

variable (p)

theorem isIntB_of_mem_A0 {x : Λ} (hx : x ∈ A0 p) : IsIntB p x :=
  isIntegral_algebraMap (R := ↥(A0 p)) (A := Λ) (x := ⟨x, hx⟩)

theorem isIntB_uΛ : IsIntB p uΛ := isIntB_of_mem_A0 p (Algebra.subset_adjoin rfl)

theorem isIntB_algebraMap (r : Zp p) : IsIntB p (algebraMap (Zp p) Λ r) :=
  isIntB_of_mem_A0 p (Subalgebra.algebraMap_mem _ r)

theorem isIntB_zero : IsIntB p 0 := isIntegral_zero
theorem isIntB_one : IsIntB p 1 := isIntegral_one

theorem isIntB_intCast (n : ℤ) : IsIntB p (n : Λ) := by
  have := isIntB_algebraMap p (n : Zp p); rwa [map_intCast] at this

theorem aeval_uΛ_mem_A0 (f : (Zp p)[X]) : aeval uΛ f ∈ A0 p :=
  Polynomial.aeval_mem_adjoin_singleton _ _

theorem isIntB_aeval_uΛ (f : (Zp p)[X]) : IsIntB p (aeval uΛ f) := isIntB_of_mem_A0 p (aeval_uΛ_mem_A0 p f)

theorem intCast_ne_zero_Λ {D : ℤ} (hD : D ≠ 0) : (D : Λ) ≠ 0 := by
  rw [show (D : Λ) = algebraMap ℚ Λ (D : ℚ) by rw [map_intCast]]
  exact (_root_.map_ne_zero _).mpr (by exact_mod_cast hD)

theorem coe_ratHom_eq (K : IntermediateField ℚ Λ) (f : ℚ →+* ↥K) (q : ℚ) :
    ((f q : ↥K) : Λ) = algebraMap ℚ Λ q := by
  rw [eq_ratCast f q, SubfieldClass.coe_ratCast, ← eq_ratCast (algebraMap ℚ Λ) q]

section Bivariate

variable {S : Type*} [CommRing S] [Algebra (Zp p) S]

theorem algebraMap_comp_aeval_adjoin (s : S) :
    (algebraMap ↥(Algebra.adjoin (Zp p) ({s} : Set S)) S).comp
        (aeval (⟨s, Algebra.subset_adjoin rfl⟩ : ↥(Algebra.adjoin (Zp p) ({s} : Set S)))).toRingHom
      = (aeval (R := Zp p) s).toRingHom := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C]
    rfl
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
    rfl

theorem isIntegral_adjoin_of_bivariate {s b : S} (P : Polynomial (Polynomial (Zp p))) (hm : P.Monic)
    (h0 : P.eval₂ (aeval (R := Zp p) s).toRingHom b = 0) :
    IsIntegral ↥(Algebra.adjoin (Zp p) ({s} : Set S)) b := by
  refine ⟨P.map (aeval (⟨s, Algebra.subset_adjoin rfl⟩ :
    ↥(Algebra.adjoin (Zp p) ({s} : Set S)))).toRingHom, hm.map _, ?_⟩
  rw [eval₂_map, algebraMap_comp_aeval_adjoin, h0]

theorem exists_bivariate_of_isIntegral_adjoin {s b : S}
    (h : IsIntegral ↥(Algebra.adjoin (Zp p) ({s} : Set S)) b) :
    ∃ P : Polynomial (Polynomial (Zp p)), P.Monic ∧ P.eval₂ (aeval (R := Zp p) s).toRingHom b = 0 := by
  obtain ⟨Q, hQm, hQ⟩ := h
  set Q' : Polynomial S := Q.map (algebraMap ↥(Algebra.adjoin (Zp p) ({s} : Set S)) S) with hQ'
  have hQ'm : Q'.Monic := hQm.map _
  have hlifts : Q' ∈ Polynomial.lifts (aeval (R := Zp p) s).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hQ', Polynomial.coeff_map]
    have hmem : ((Q.coeff n : ↥(Algebra.adjoin (Zp p) ({s} : Set S))) : S)
        ∈ (aeval (R := Zp p) s).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (Q.coeff n).2
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq⟩
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hQ'm
  refine ⟨P, hPm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hPmap, hQ', Polynomial.eval_map, hQ]

theorem isIntegral_adjoin_iff_of_ringHom {S' : Type*} [CommRing S'] [Algebra (Zp p) S']
    (f : S →+* S') (hf : Function.Injective f)
    (hcomm : f.comp (algebraMap (Zp p) S) = algebraMap (Zp p) S') {s b : S} :
    IsIntegral ↥(Algebra.adjoin (Zp p) ({s} : Set S)) b ↔
      IsIntegral ↥(Algebra.adjoin (Zp p) ({f s} : Set S')) (f b) := by
  have hcomp : f.comp (aeval (R := Zp p) s).toRingHom = (aeval (R := Zp p) (f s)).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C]
      exact congrFun (congrArg DFunLike.coe hcomm) c
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
  constructor
  · intro h
    obtain ⟨P, hPm, hP⟩ := exists_bivariate_of_isIntegral_adjoin p h
    refine isIntegral_adjoin_of_bivariate p P hPm ?_
    rw [← hcomp, ← Polynomial.hom_eval₂, hP, map_zero]
  · intro h
    obtain ⟨P, hPm, hP⟩ := exists_bivariate_of_isIntegral_adjoin p h
    refine isIntegral_adjoin_of_bivariate p P hPm (hf ?_)
    rw [Polynomial.hom_eval₂, hcomp, hP, map_zero]

end Bivariate

theorem algebraMap_Zp_eq (c : Zp p) : algebraMap (Zp p) Λ c = algebraMap ℚ Λ (c : ℚ) := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
    ModularCurve.algebraMap_apply_eq_single, HahnSeries.C_apply]
  try rfl

theorem algebraMap_Zp_eq_C (c : Zp p) : algebraMap (Zp p) Λ c = HahnSeries.C (c : ℚ) := by
  rw [algebraMap_Zp_eq, ModularCurve.algebraMap_apply_eq_single, HahnSeries.C_apply]

def constO : Zp p →+* ↥𝒪 :=
  (algebraMap (Zp p) Λ).codRestrict 𝒪 (fun c => by rw [algebraMap_Zp_eq_C]; exact C_mem_𝒪 _)

@[scoped simp] theorem coe_constO (c : Zp p) : ((constO p c : ↥𝒪) : Λ) = HahnSeries.C (c : ℚ) := by
  change algebraMap (Zp p) Λ c = _; exact algebraMap_Zp_eq_C p c

theorem coeff_zero_algebraMap (c : Zp p) : (algebraMap (Zp p) Λ c).coeff 0 = c := by
  rw [algebraMap_Zp_eq_C, HahnSeries.C_apply, HahnSeries.coeff_single_same]

theorem mem_𝒪_and_coeff_zero_mem {x : Λ} (hx : IsIntB p x) :
    x ∈ 𝒪 ∧ x.coeff 0 ∈ GaloisRep.ratLocalizedAt p := by
  obtain ⟨P, hPm, hP⟩ := exists_bivariate_of_isIntegral_adjoin p hx
  have hu := jq_inv_mem_𝒪_and_coeff
  set κ : Polynomial (Zp p) →+* ↥𝒪 := eval₂RingHom (constO p) ⟨uΛ, hu.1⟩ with hκ
  have hcompat : (𝒪.subtype).comp κ = (aeval (R := Zp p) uΛ).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, hκ, coe_eval₂RingHom, eval₂_C, Subring.subtype_apply, coe_constO,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, algebraMap_Zp_eq_C]
    · rw [RingHom.comp_apply, hκ, coe_eval₂RingHom, eval₂_X, Subring.subtype_apply,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
  have hroot : eval₂ (algebraMap ↥𝒪 Λ) x (P.map κ) = 0 := by
    rw [eval₂_map, show algebraMap ↥𝒪 Λ = 𝒪.subtype from rfl, hcompat, hP]
  have hxO : x ∈ 𝒪 :=
    (Valuation.integer.integers (Valued.v : Valuation Λ ℤᵐ⁰)).mem_of_integral ⟨P.map κ, hPm.map κ, hroot⟩
  refine ⟨hxO, ?_⟩
  set x' : ↥𝒪 := ⟨_, hxO⟩ with hx'
  have hroot' : P.eval₂ κ x' = 0 := by
    apply Subtype.ext
    change 𝒪.subtype (P.eval₂ κ x') = 0
    rw [Polynomial.hom_eval₂, hcompat, show 𝒪.subtype x' = x from rfl, hP]
  have hcompat' : (algebraMap (Zp p) ℚ).comp (evalRingHom 0) = ρ.comp κ := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, RingHom.comp_apply, coe_evalRingHom, eval_C, hκ, coe_eval₂RingHom, eval₂_C,
        ρ_apply, coe_constO, HahnSeries.C_apply, HahnSeries.coeff_single_same]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, coe_evalRingHom, eval_X, hκ, coe_eval₂RingHom, eval₂_X,
        ρ_apply, map_zero]
      exact hu.2.symm
  have hint : IsIntegral (Zp p) (x.coeff 0) := by
    refine ⟨P.map (evalRingHom 0), hPm.map _, ?_⟩
    rw [eval₂_map, hcompat', show x.coeff 0 = ρ x' from rfl, ← Polynomial.hom_eval₂, hroot', map_zero]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Zp p) (K := ℚ)).mp hint
  rw [← hy]
  exact y.2

def 𝒪p : Subring Λ where
  carrier := {x | x ∈ 𝒪 ∧ x.coeff 0 ∈ GaloisRep.ratLocalizedAt p}
  mul_mem' {a b} ha hb := ⟨Subring.mul_mem _ ha.1 hb.1, by
    rw [coeff_zero_mul ha.1 hb.1]; exact Subring.mul_mem _ ha.2 hb.2⟩
  one_mem' := ⟨Subring.one_mem _, by simp⟩
  add_mem' {a b} ha hb := ⟨Subring.add_mem _ ha.1 hb.1, by
    rw [HahnSeries.coeff_add]; exact Subring.add_mem _ ha.2 hb.2⟩
  zero_mem' := ⟨Subring.zero_mem _, by simp⟩
  neg_mem' {a} ha := ⟨Subring.neg_mem _ ha.1, by rw [HahnSeries.coeff_neg]; exact Subring.neg_mem _ ha.2⟩

def ev : ↥(𝒪p p) →+* Zp p where
  toFun x := ⟨(x : Λ).coeff 0, x.2.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    change ((a : Λ) * b).coeff 0 = (a : Λ).coeff 0 * (b : Λ).coeff 0
    exact coeff_zero_mul a.2.1 b.2.1)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by
    change ((a : Λ) + b).coeff 0 = (a : Λ).coeff 0 + (b : Λ).coeff 0
    rw [HahnSeries.coeff_add])

@[scoped simp] theorem coe_ev (x : ↥(𝒪p p)) : ((ev p x : Zp p) : ℚ) = (x : Λ).coeff 0 := rfl

theorem IsIntB.mem_𝒪p {x : Λ} (hx : IsIntB p x) : x ∈ 𝒪p p := mem_𝒪_and_coeff_zero_mem p hx

theorem inP_coeff_iff {x : Λ} (hx : x ∈ 𝒪p p) :
    InP p (x.coeff 0) ↔ ev p ⟨x, hx⟩ ∈ IsLocalRing.maximalIdeal (Zp p) := by
  rw [← inP_iff]; rfl

theorem inv_mem_𝒪p {x : Λ} (hx : x ∈ 𝒪p p) (h : ¬ InP p (x.coeff 0)) : x⁻¹ ∈ 𝒪p p := by
  have hu : IsUnit (ev p ⟨x, hx⟩) := by
    rwa [inP_coeff_iff p hx, IsLocalRing.notMem_maximalIdeal] at h
  have h0 : x.coeff 0 ≠ 0 := by
    intro h0
    apply h
    rw [h0]; exact inP_zero p
  have hi := inv_mem_𝒪_and_coeff hx.1 h0
  refine ⟨hi.1, ?_⟩
  rw [hi.2]
  obtain ⟨w, hw⟩ := hu
  have hw' : (w : Zp p) * (↑(w⁻¹) : Zp p) = 1 := Units.mul_inv w
  have hcoe : ((w : Zp p) : ℚ) = x.coeff 0 := by rw [hw]; rfl
  have : (x.coeff 0)⁻¹ = ((↑(w⁻¹) : Zp p) : ℚ) := by
    rw [← hcoe]
    have h2 := congrArg (fun z : Zp p => (z : ℚ)) hw'
    simp only [Subring.coe_mul, Subring.coe_one] at h2
    exact (eq_inv_of_mul_eq_one_right h2).symm
  rw [this]
  exact Subtype.mem _

theorem ne_zero_of_not_inP {x : Λ} (h : ¬ InP p (x.coeff 0)) : x ≠ 0 := by
  rintro rfl
  exact h (by rw [HahnSeries.coeff_zero]; exact inP_zero p)

theorem not_inP_mul {x y : Λ} (hx : x ∈ 𝒪p p) (hy : y ∈ 𝒪p p) (hx' : ¬ InP p (x.coeff 0))
    (hy' : ¬ InP p (y.coeff 0)) : ¬ InP p ((x * y).coeff 0) := by
  have hxy : x * y ∈ 𝒪p p := Subring.mul_mem _ hx hy
  rw [inP_coeff_iff p hxy]
  rw [inP_coeff_iff p hx] at hx'
  rw [inP_coeff_iff p hy] at hy'
  have : ev p ⟨x * y, hxy⟩ = ev p ⟨x, hx⟩ * ev p ⟨y, hy⟩ := by
    rw [← map_mul]; rfl
  rw [this]
  exact fun h => ((IsLocalRing.maximalIdeal.isMaximal (Zp p)).isPrime.mem_or_mem h).elim hx' hy'

theorem not_inP_pow {x : Λ} (hx : x ∈ 𝒪p p) (hx' : ¬ InP p (x.coeff 0)) (n : ℕ) :
    ¬ InP p ((x ^ n).coeff 0) := by
  induction n with
  | zero => rw [pow_zero]; exact fun h => not_inP_one p (by simpa using h)
  | succ n ih => rw [pow_succ]; exact not_inP_mul p (Subring.pow_mem _ hx n) hx ih hx'

theorem not_inP_of_coeff_eq_one {x : Λ} (h : x.coeff 0 = 1) : ¬ InP p (x.coeff 0) := by
  rw [h]; exact fun h' => not_inP_one p (by simpa using h')

theorem intCast_mem_𝒪p (n : ℤ) : (n : Λ) ∈ 𝒪p p := (isIntB_intCast p n).mem_𝒪p

theorem ev_intCast (n : ℤ) : ev p ⟨(n : Λ), intCast_mem_𝒪p p n⟩ = n := by
  apply Subtype.ext
  rw [coe_ev]
  change ((n : Λ)).coeff 0 = ((n : Zp p) : ℚ)
  rw [show ((n : Zp p) : ℚ) = n by simp, ← map_intCast (HahnSeries.C (Γ := ℤ) (R := ℚ)) n,
    HahnSeries.C_apply, HahnSeries.coeff_single_same]

theorem uΛ_mem_𝒪p : uΛ ∈ 𝒪p p := (isIntB_uΛ p).mem_𝒪p

theorem ev_uΛ : ev p ⟨uΛ, uΛ_mem_𝒪p p⟩ = 0 := by
  apply Subtype.ext
  rw [coe_ev]
  exact jq_inv_mem_𝒪_and_coeff.2

end IntB

section GoodDef

variable (p : ℕ) [hp : Fact p.Prime]

structure Good (K : IntermediateField ℚ Λ) (e : ℕ) [NeZero e] : Prop where
  jq_mem : jq ∈ K
  frac : ∀ x ∈ K, ∃ b ∈ K, ∃ s ∈ K, IsIntB p b ∧ IsIntB p s ∧ s ≠ 0 ∧ s * x = b
  gen : ∀ x ∈ K, IsIntB p x → InP p (x.coeff 0) →
    ∃ s ∈ K, ∃ c ∈ K, ∃ d ∈ K, IsIntB p s ∧ IsIntB p c ∧ IsIntB p d ∧ ¬ InP p (s.coeff 0) ∧
      s * x = (p : Λ) * c + uΛ * d
  inv_mem : ∃ a ∈ K, ∃ s ∈ K, IsIntB p a ∧ IsIntB p s ∧ ¬ InP p (s.coeff 0) ∧
    s * (qExpand ℚ e jq)⁻¹ = a

end GoodDef

section Typed

variable (p : ℕ) [hp : Fact p.Prime] (K : IntermediateField ℚ Λ)

theorem coe_algebraMap_ZpK (r : Zp p) :
    ((algebraMap (Zp p) ↥K r : ↥K) : Λ) = algebraMap (Zp p) Λ r := by
  first
    | (change ((algebraMap ℚ ↥K (r : ℚ) : ↥K) : Λ) = algebraMap ℚ Λ (r : ℚ); exact coe_ratHom_eq K _ _)
    | exact (IsScalarTower.algebraMap_apply (Zp p) ↥K Λ r).symm
    | (rw [algebraMap_Zp_eq, IsScalarTower.algebraMap_apply (Zp p) ℚ ↥K r]; exact coe_ratHom_eq K _ _)

def BK : Subalgebra (Zp p) Λ where
  carrier := {x | x ∈ K ∧ IsIntB p x}
  mul_mem' {a b} ha hb := ⟨K.mul_mem ha.1 hb.1, ha.2.mul hb.2⟩
  one_mem' := ⟨K.one_mem, isIntB_one p⟩
  add_mem' {a b} ha hb := ⟨K.add_mem ha.1 hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨K.zero_mem, isIntB_zero p⟩
  algebraMap_mem' r := ⟨by rw [algebraMap_Zp_eq]; exact K.algebraMap_mem _, isIntB_algebraMap p r⟩

variable {p K}

theorem BK.memK (b : ↥(BK p K)) : (b : Λ) ∈ K := b.2.1
theorem BK.isIntB (b : ↥(BK p K)) : IsIntB p (b : Λ) := b.2.2
theorem BK.mem_𝒪p (b : ↥(BK p K)) : (b : Λ) ∈ 𝒪p p := (BK.isIntB b).mem_𝒪p

variable (p K)

def evK : ↥(BK p K) →+* Zp p where
  toFun b := ev p ⟨(b : Λ), BK.mem_𝒪p b⟩
  map_one' := by rw [← (ev p).map_one]; rfl
  map_mul' a b := by rw [← map_mul]; rfl
  map_zero' := by rw [← (ev p).map_zero]; rfl
  map_add' a b := by rw [← map_add]; rfl

def 𝔪K : Ideal ↥(BK p K) := Ideal.comap (evK p K) (IsLocalRing.maximalIdeal (Zp p))

scoped instance 𝔪K_isPrime : (𝔪K p K).IsPrime := Ideal.comap_isPrime _ _

variable {p K}

theorem mem_𝔪K_iff (b : ↥(BK p K)) : b ∈ 𝔪K p K ↔ InP p ((b : Λ).coeff 0) := by
  rw [𝔪K, Ideal.mem_comap, inP_coeff_iff p (BK.mem_𝒪p b)]; rfl

private theorem _root_.CuspInftyTower.mem_primeCompl_iff (b : ↥(BK p K)) : b ∈ (𝔪K p K).primeCompl ↔ ¬ InP p ((b : Λ).coeff 0) := by
  rw [Ideal.mem_primeCompl_iff, mem_𝔪K_iff]

p2m_export "CuspInftyTower" "mem_primeCompl_iff"
theorem coe_ne_zero_of_mem_primeCompl {b : ↥(BK p K)} (hb : b ∈ (𝔪K p K).primeCompl) : (b : Λ) ≠ 0 :=
  ne_zero_of_not_inP p ((mem_primeCompl_iff b).mp hb)

variable (p K)

def RK : Subalgebra (Zp p) Λ where
  carrier := {x | ∃ a s : ↥(BK p K), s ∈ (𝔪K p K).primeCompl ∧ x = a * ((s : Λ))⁻¹}
  mul_mem' := by
    rintro _ _ ⟨a₁, s₁, hs₁, rfl⟩ ⟨a₂, s₂, hs₂, rfl⟩
    refine ⟨a₁ * a₂, s₁ * s₂, mul_mem hs₁ hs₂, ?_⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, mul_inv]; ring
  one_mem' := ⟨1, 1, Submonoid.one_mem _, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a₁, s₁, hs₁, rfl⟩ ⟨a₂, s₂, hs₂, rfl⟩
    refine ⟨a₁ * s₂ + a₂ * s₁, s₁ * s₂, mul_mem hs₁ hs₂, ?_⟩
    have h1 := coe_ne_zero_of_mem_primeCompl hs₁
    have h2 := coe_ne_zero_of_mem_primeCompl hs₂
    rw [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_mul]
    field_simp
  zero_mem' := ⟨0, 1, Submonoid.one_mem _, by simp⟩
  algebraMap_mem' r := ⟨algebraMap (Zp p) (BK p K) r, 1, Submonoid.one_mem _, by simp⟩

variable {p K}

theorem BK_le_RK : BK p K ≤ RK p K := fun x hx =>
  ⟨⟨x, hx⟩, 1, Submonoid.one_mem _, by simp⟩

theorem RK_subset_K {x : Λ} (hx : x ∈ RK p K) : x ∈ K := by
  obtain ⟨a, s, hs, rfl⟩ := hx
  exact K.mul_mem (BK.memK a) (K.inv_mem (BK.memK s))

theorem RK_mem_𝒪p {x : Λ} (hx : x ∈ RK p K) : x ∈ 𝒪p p := by
  obtain ⟨a, s, hs, rfl⟩ := hx
  exact Subring.mul_mem _ (BK.mem_𝒪p a) (inv_mem_𝒪p p (BK.mem_𝒪p s) ((mem_primeCompl_iff s).mp hs))

theorem div_mem_RK {a s : Λ} (haK : a ∈ K) (ha : IsIntB p a) (hsK : s ∈ K) (hs : IsIntB p s)
    (hsP : ¬ InP p (s.coeff 0)) : a * s⁻¹ ∈ RK p K :=
  ⟨⟨a, haK, ha⟩, ⟨s, hsK, hs⟩, (mem_primeCompl_iff _).mpr hsP, rfl⟩

variable (p K)

scoped instance algBKK : Algebra ↥(BK p K) ↥K :=
  (({ toFun := fun b => ⟨(b : Λ), BK.memK b⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl } : ↥(BK p K) →+* ↥K)).toAlgebra

scoped instance algRKK : Algebra ↥(RK p K) ↥K :=
  (({ toFun := fun r => ⟨(r : Λ), RK_subset_K r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl } : ↥(RK p K) →+* ↥K)).toAlgebra

scoped instance algBR : Algebra ↥(BK p K) ↥(RK p K) := (Subalgebra.inclusion (BK_le_RK (p := p) (K := K))).toRingHom.toAlgebra

scoped instance : IsScalarTower ↥(BK p K) ↥K Λ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
scoped instance : IsScalarTower ↥(RK p K) ↥K Λ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
scoped instance : IsScalarTower ↥(BK p K) ↥(RK p K) Λ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
scoped instance : IsScalarTower ↥(BK p K) ↥(RK p K) ↥K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance faithfulSMul_BKK : FaithfulSMul ↥(BK p K) ↥K :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y h =>
    Subtype.ext (congrArg (fun z : ↥K => (z : Λ)) h)

scoped instance faithfulSMul_RKK : FaithfulSMul ↥(RK p K) ↥K :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y h =>
    Subtype.ext (congrArg (fun z : ↥K => (z : Λ)) h)

scoped instance isLocalization_RK : IsLocalization.AtPrime ↥(RK p K) (𝔪K p K) := by
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    have hs0 := coe_ne_zero_of_mem_primeCompl hs
    have hinv : ((s : Λ))⁻¹ ∈ RK p K := ⟨1, s, hs, by simp⟩
    refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
    change (s : Λ) * ((s : Λ))⁻¹ = 1
    exact mul_inv_cancel₀ hs0
  · rintro ⟨x, a, s, hs, rfl⟩
    refine ⟨(a, ⟨s, hs⟩), Subtype.ext ?_⟩
    change (a : Λ) * ((s : Λ))⁻¹ * s = a
    rw [mul_assoc, inv_mul_cancel₀ (coe_ne_zero_of_mem_primeCompl hs), mul_one]
  · intro x y hxy
    exact ⟨1, by rw [Subalgebra.inclusion_injective _ hxy]⟩

variable {p K}

theorem isFractionRing_BK {e : ℕ} [NeZero e] (hK : Good p K e) : IsFractionRing ↥(BK p K) ↥K := by
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨b, hbK, s, hsK, hb, hs, hs0, hsx⟩ := hK.frac (x : Λ) x.2
  refine ⟨⟨b, hbK, hb⟩, ⟨s, hsK, hs⟩, Subtype.ext ?_⟩
  change (x : Λ) = b / s
  rw [eq_div_iff hs0, mul_comm]; exact hsx

theorem isFractionRing_RK {e : ℕ} [NeZero e] (hK : Good p K e) : IsFractionRing ↥(RK p K) ↥K := by
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨b, hbK, s, hsK, hb, hs, hs0, hsx⟩ := hK.frac (x : Λ) x.2
  refine ⟨⟨b, BK_le_RK ⟨hbK, hb⟩⟩, ⟨s, BK_le_RK ⟨hsK, hs⟩⟩, Subtype.ext ?_⟩
  change (x : Λ) = b / s
  rw [eq_div_iff hs0, mul_comm]; exact hsx

theorem A0_subset (hj : jq ∈ K) {z : Λ} (hz : z ∈ A0 p) : z ∈ K := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact K.inv_mem hj
  | algebraMap r =>
    rw [algebraMap_Zp_eq]
    exact K.algebraMap_mem (r : ℚ)
  | add x y _ _ hx hy => exact K.add_mem hx hy
  | mul x y _ _ hx hy => exact K.mul_mem hx hy

theorem A0_le_BK (hj : jq ∈ K) : A0 p ≤ BK p K := fun z hz => ⟨A0_subset hj hz, isIntB_of_mem_A0 p hz⟩

theorem uΛ_mem_BK (hj : jq ∈ K) : uΛ ∈ BK p K := A0_le_BK hj (Algebra.subset_adjoin rfl)

theorem isIntB_of_isIntegral_BK (hj : jq ∈ K) {L : Type*} [CommRing L] [Algebra ↥(BK p K) L]
    (ι : L →+* Λ) (halg : ∀ b : ↥(BK p K), ι (algebraMap _ L b) = (b : Λ))
    {y : L} (hy : IsIntegral ↥(BK p K) y) : IsIntB p (ι y) := by
  let ιₐ : L →ₐ[↥(BK p K)] Λ := { ι with commutes' := fun b => halg b }
  have hyΛ : IsIntegral ↥(BK p K) (ι y) := hy.map ιₐ
  letI algAB : Algebra ↥(A0 p) ↥(BK p K) := (Subalgebra.inclusion (A0_le_BK (p := p) hj)).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(A0 p) ↥(BK p K) Λ := IsScalarTower.of_algebraMap_eq (fun z => rfl)
  haveI : Algebra.IsIntegral ↥(A0 p) ↥(BK p K) := ⟨fun b => by
    have hb : IsIntegral ↥(A0 p) (IsScalarTower.toAlgHom ↥(A0 p) ↥(BK p K) Λ b) := b.2.2
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(A0 p) ↥(BK p K) Λ) ?_).mp hb
    intro x y hxy
    exact Subtype.ext hxy⟩
  exact isIntegral_trans _ hyΛ

theorem isIntegrallyClosed_BK {e : ℕ} [NeZero e] (hK : Good p K e) : IsIntegrallyClosed ↥(BK p K) := by
  haveI := isFractionRing_BK hK
  refine (isIntegrallyClosed_iff ↥K).mpr fun {y} hy => ?_
  have hy' : IsIntB p (y : Λ) :=
    isIntB_of_isIntegral_BK hK.jq_mem (L := ↥K) (algebraMap ↥K Λ) (fun _ => rfl) hy
  exact ⟨⟨y, y.2, hy'⟩, rfl⟩

theorem isIntegrallyClosed_RK {e : ℕ} [NeZero e] (hK : Good p K e) : IsIntegrallyClosed ↥(RK p K) := by
  haveI := isIntegrallyClosed_BK hK
  exact isIntegrallyClosed_of_isLocalization ↥(RK p K) (𝔪K p K).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

variable (p K)

def evR : ↥(RK p K) →+* Zp p where
  toFun x := ev p ⟨(x : Λ), RK_mem_𝒪p x.2⟩
  map_one' := by rw [← (ev p).map_one]; rfl
  map_mul' a b := by rw [← map_mul]; rfl
  map_zero' := by rw [← (ev p).map_zero]; rfl
  map_add' a b := by rw [← map_add]; rfl

def πR : ↥(RK p K) →+* IsLocalRing.ResidueField (Zp p) := (IsLocalRing.residue (Zp p)).comp (evR p K)

variable {p K}

theorem evR_apply (x : ↥(RK p K)) : evR p K x = ev p ⟨(x : Λ), RK_mem_𝒪p x.2⟩ := rfl

theorem πR_eq_zero_iff (x : ↥(RK p K)) : πR p K x = 0 ↔ InP p ((x : Λ).coeff 0) := by
  rw [πR, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, evR_apply, ← inP_coeff_iff]

theorem πR_intCast (n : ℤ) : πR p K (n : ↥(RK p K)) = IsLocalRing.residue (Zp p) n := by
  have h : (⟨((n : ↥(RK p K)) : Λ), RK_mem_𝒪p (n : ↥(RK p K)).2⟩ : ↥(𝒪p p)) = ⟨(n : Λ), intCast_mem_𝒪p p n⟩ :=
    Subtype.ext (SubringClass.coe_intCast _ n)
  rw [πR, RingHom.comp_apply, evR_apply, h, ev_intCast]

theorem πR_int_surjective : Function.Surjective fun n : ℤ => πR p K (n : ↥(RK p K)) := by
  intro k
  obtain ⟨n, hn⟩ := residue_int_surjective p k
  exact ⟨n, by change πR p K (n : ↥(RK p K)) = k; rw [πR_intCast]; exact hn⟩

def uR (hj : jq ∈ K) : ↥(RK p K) := ⟨uΛ, BK_le_RK (uΛ_mem_BK hj)⟩

@[scoped simp] theorem coe_uR (hj : jq ∈ K) : ((uR (p := p) hj : ↥(RK p K)) : Λ) = uΛ := rfl

theorem mem_span_of_πR_eq_zero {e : ℕ} [NeZero e] (hK : Good p K e) (x : ↥(RK p K)) (hx : πR p K x = 0) :
    x ∈ Ideal.span {(p : ↥(RK p K)), uR hK.jq_mem} := by
  rw [πR_eq_zero_iff] at hx
  obtain ⟨a', s', hs', hxas⟩ := x.2
  have hs'P := (mem_primeCompl_iff s').mp hs'
  have hs'ne : (s' : Λ) ≠ 0 := ne_zero_of_not_inP p hs'P

  have ha'P : InP p ((a' : Λ).coeff 0) := by
    have heq : (a' : Λ) = (x : Λ) * (s' : Λ) := by rw [hxas, mul_assoc, inv_mul_cancel₀ hs'ne, mul_one]
    rw [inP_coeff_iff p (BK.mem_𝒪p a')]
    have : ev p ⟨(a' : Λ), BK.mem_𝒪p a'⟩
        = ev p ⟨(x : Λ), RK_mem_𝒪p x.2⟩ * ev p ⟨(s' : Λ), BK.mem_𝒪p s'⟩ := by
      rw [← map_mul]; exact congrArg (ev p) (Subtype.ext heq)
    rw [this]
    exact Ideal.mul_mem_right _ _ ((inP_coeff_iff p (RK_mem_𝒪p x.2)).mp hx)
  obtain ⟨s₂, hs₂K, c, hcK, d, hdK, hs₂, hc, hd, hs₂P, hrel⟩ :=
    hK.gen (a' : Λ) (BK.memK a') (BK.isIntB a') ha'P
  have hden : ¬ InP p ((s₂ * (s' : Λ)).coeff 0) := not_inP_mul p hs₂.mem_𝒪p (BK.mem_𝒪p s') hs₂P hs'P
  have hdenK : s₂ * (s' : Λ) ∈ K := K.mul_mem hs₂K (BK.memK s')
  have hdenI : IsIntB p (s₂ * (s' : Λ)) := hs₂.mul (BK.isIntB s')
  set cR : ↥(RK p K) := ⟨c * (s₂ * (s' : Λ))⁻¹, div_mem_RK hcK hc hdenK hdenI hden⟩ with hcR
  set dR : ↥(RK p K) := ⟨d * (s₂ * (s' : Λ))⁻¹, div_mem_RK hdK hd hdenK hdenI hden⟩ with hdR
  have hxeq : x = (p : ↥(RK p K)) * cR + uR hK.jq_mem * dR := by
    apply Subtype.ext
    have hs₂ne : s₂ ≠ 0 := ne_zero_of_not_inP p hs₂P
    rw [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_mul, SubringClass.coe_natCast, coe_uR, hxas]
    change (a' : Λ) * ((s' : Λ))⁻¹ = (p : Λ) * (c * (s₂ * (s' : Λ))⁻¹) + uΛ * (d * (s₂ * (s' : Λ))⁻¹)
    field_simp
    linear_combination hrel
  rw [hxeq]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

theorem isIntegral_of_isIntB {P L : Type*} [CommRing P] [CommRing L] [Algebra P L]
    (ι : L →+* Λ) (hι : Function.Injective ι) (uP : P) (huP : ι (algebraMap P L uP) = uΛ)
    (cP : Zp p →+* P) (hcP : ∀ r, ι (algebraMap P L (cP r)) = algebraMap (Zp p) Λ r)
    {y : L} (hy : IsIntB p (ι y)) : IsIntegral P y := by
  obtain ⟨Q, hQm, hQ⟩ := exists_bivariate_of_isIntegral_adjoin p hy
  refine ⟨Q.map (eval₂RingHom cP uP), hQm.map _, ?_⟩
  apply hι
  rw [eval₂_map, Polynomial.hom_eval₂, map_zero, ← hQ]
  congr 1
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, aeval_C, hcP]
  · rw [RingHom.comp_apply, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, aeval_X, huP]

end Typed

section Twisted

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (e : ℕ) [NeZero e]

def uE : Λ := (qExpand ℚ e jq)⁻¹

def tE : Λ := qExpand ℚ (e * ℓ) jq * uE e ^ ℓ

theorem uE_eq : uE e = qExpand ℚ e uΛ := by
  rw [uE, uΛ, map_inv₀]

theorem uE_ne_zero : uE e ≠ 0 := inv_ne_zero (qExpand_ne_zero e jq_ne_zero)

theorem uE_mem_𝒪_and_coeff : uE e ∈ 𝒪 ∧ (uE e).coeff 0 = 0 := by
  rw [uE_eq]
  exact ⟨qExpand_mem_𝒪 e jq_inv_mem_𝒪_and_coeff.1,
    by rw [coeff_zero_qExpand]; exact jq_inv_mem_𝒪_and_coeff.2⟩

theorem tE_eq : tE ℓ e = qExpand ℚ e (qExpand ℚ ℓ jq * (jq⁻¹) ^ ℓ) := by
  rw [tE, map_mul, map_pow, qExpand_qExpand, ← uΛ, ← uE_eq]

theorem exists_twisted :
    ∃ h : Polynomial (Polynomial ℤ), h.Monic ∧ h.map (evalRingHom 0) = X ^ (ℓ + 1) - X ^ ℓ ∧
      h.eval₂ (eval₂RingHom (algebraMap ℤ Λ) (uE e)) (tE ℓ e) = 0 ∧
      tE ℓ e ∈ 𝒪 ∧ (tE ℓ e).coeff 0 = 1 := by
  have hℓ1 : ¬ ℓ ∣ 1 := fun h => hℓ.out.one_lt.ne' (Nat.dvd_one.mp h)
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  obtain ⟨-, ⟨ht, ⟨h, hm, hmap, hev⟩, ht0, -⟩, -⟩ :=
    ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd 1 ℓ hℓ1
  set F1 := modularFunctionFieldFull (1 * ℓ) with hF1
  set ι : ↥F1 →+* Λ := algebraMap ↥F1 Λ with hι
  have hιapp : ∀ x : ↥F1, ι x = (x : Λ) := fun _ => rfl
  have hιu : ι (ModularCurve.IgusaScheme.jFull (1 * ℓ))⁻¹ = jq⁻¹ := by
    rw [map_inv₀]; rfl
  have hιt : ι (⟨qExpand ℚ ℓ jq, jqd_mem_full (1 * ℓ) (dvd_mul_left ℓ 1)⟩ *
      (ModularCurve.IgusaScheme.jFull (1 * ℓ))⁻¹ ^ ℓ) = qExpand ℚ ℓ jq * (jq⁻¹) ^ ℓ := by
    rw [map_mul, map_pow, hιu]; rfl
  have hcomm : ι.comp (algebraMap (Zp ℓ) ↥F1) = algebraMap (Zp ℓ) Λ := by
    refine RingHom.ext fun r => ?_
    first
      | (change ((algebraMap ℚ ↥F1 (r : ℚ) : ↥F1) : Λ) = algebraMap ℚ Λ (r : ℚ); exact coe_ratHom_eq F1 _ _)
      | (rw [RingHom.comp_apply, algebraMap_Zp_eq, IsScalarTower.algebraMap_apply (Zp ℓ) ℚ ↥F1 r]; exact coe_ratHom_eq F1 _ _)

  have hev1 : h.eval₂ (eval₂RingHom (algebraMap ℤ Λ) jq⁻¹) (qExpand ℚ ℓ jq * (jq⁻¹) ^ ℓ) = 0 := by
    have h1 := congrArg ι hev
    rw [map_zero, Polynomial.hom_eval₂, hιt] at h1
    have hcomp : ι.comp (eval₂RingHom (algebraMap ℤ ↥F1) (ModularCurve.IgusaScheme.jFull (1 * ℓ))⁻¹)
        = eval₂RingHom (algebraMap ℤ Λ) jq⁻¹ := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [RingHom.comp_apply, coe_eval₂RingHom, coe_eval₂RingHom, eval₂_X, eval₂_X, hιu]
    rwa [hcomp] at h1

  have hev2 : h.eval₂ (eval₂RingHom (algebraMap ℤ Λ) (uE e)) (tE ℓ e) = 0 := by
    have h2 := congrArg (qExpand ℚ e) hev1
    rw [map_zero, Polynomial.hom_eval₂, ← tE_eq] at h2
    have hcomp : (qExpand ℚ e).comp (eval₂RingHom (algebraMap ℤ Λ) jq⁻¹)
        = eval₂RingHom (algebraMap ℤ Λ) (uE e) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [RingHom.comp_apply, coe_eval₂RingHom, coe_eval₂RingHom, eval₂_X, eval₂_X, ← uΛ, ← uE_eq]
    rwa [hcomp] at h2

  have ht1 : (qExpand ℚ ℓ jq * (jq⁻¹) ^ ℓ) ∈ 𝒪 := by
    have hint : IsIntB ℓ (qExpand ℚ ℓ jq * (jq⁻¹) ^ ℓ) := by
      have hb := (ModularCurve.IgusaScheme.mem_chartAlg_iff (1 * ℓ) ℓ).mp ht
      have := (isIntegral_adjoin_iff_of_ringHom ℓ ι Subtype.coe_injective hcomm).mp hb
      rw [hιu, hιt] at this
      exact this
    exact (mem_𝒪_and_coeff_zero_mem ℓ hint).1
  have ht0' : (qExpand ℚ ℓ jq * (jq⁻¹) ^ ℓ).coeff 0 = 1 := by
    rw [← hιt, hιapp]; exact ht0
  refine ⟨h, hm, hmap, hev2, ?_, ?_⟩
  · rw [tE_eq]; exact qExpand_mem_𝒪 e ht1
  · rw [tE_eq, coeff_zero_qExpand, ht0']

theorem tE_inv_eq : (qExpand ℚ (e * ℓ) jq)⁻¹ = uE e ^ ℓ * (tE ℓ e)⁻¹ := by
  rw [tE, mul_inv, ← mul_assoc, mul_comm (uE e ^ ℓ) ((qExpand ℚ (e * ℓ) jq)⁻¹), mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (uE_ne_zero e)), mul_one]

end Twisted

section Step

variable (p : ℕ) [hp : Fact p.Prime]

def Enew (K : IntermediateField ℚ Λ) (e ℓ : ℕ) [NeZero e] [Fact ℓ.Prime] : IntermediateField ↥K Λ :=
  IntermediateField.adjoin ↥K {qExpand ℚ (e * ℓ) jq}

def EnewQ (K : IntermediateField ℚ Λ) (e ℓ : ℕ) [NeZero e] [Fact ℓ.Prime] : IntermediateField ℚ Λ :=
  Subfield.toIntermediateField (Enew K e ℓ).toSubfield (fun q => by
    rw [IntermediateField.mem_toSubfield,
      show algebraMap ℚ Λ q = ((⟨algebraMap ℚ Λ q, K.algebraMap_mem q⟩ : ↥K) : Λ) from rfl]
    exact (Enew K e ℓ).algebraMap_mem (⟨algebraMap ℚ Λ q, K.algebraMap_mem q⟩ : ↥K))

theorem mem_EnewQ {K : IntermediateField ℚ Λ} {e ℓ : ℕ} [NeZero e] [Fact ℓ.Prime] {x : Λ} :
    x ∈ EnewQ K e ℓ ↔ x ∈ Enew K e ℓ := Iff.rfl

theorem eval_derivative_ne_zero_of_dvd {κ : Type*} [Field κ] {g : κ[X]} {n : ℕ}
    (hdvd : g ∣ X ^ n * (X - Polynomial.C 1)) (hroot : g.eval 1 = 0) : g.derivative.eval 1 ≠ 0 := by
  obtain ⟨k, hk⟩ := hdvd
  set w := g /ₘ (X - Polynomial.C 1) with hw
  have hgw : (X - Polynomial.C 1) * w = g := (mul_divByMonic_eq_iff_isRoot).mpr hroot
  have hwk : w * k = X ^ n := by
    have h2 : (X - Polynomial.C (1 : κ)) * (w * k) = (X - Polynomial.C 1) * X ^ n := by
      rw [← mul_assoc, hgw, ← hk, mul_comm]
    exact mul_left_cancel₀ (X_sub_C_ne_zero 1) h2
  have hw1 : w.eval 1 ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval (1 : κ)) hwk
    rw [eval_mul, h0, zero_mul, eval_pow, eval_X, one_pow] at this
    exact zero_ne_one this
  have hd : g.derivative = w + (X - Polynomial.C 1) * derivative w := by
    rw [← hgw, derivative_mul, derivative_X_sub_C, one_mul]
  rw [hd, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  exact hw1

set_option maxHeartbeats 16000000 in
theorem step {K : IntermediateField ℚ Λ} {e : ℕ} [NeZero e] (hK : Good p K e) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    Good p (EnewQ K e ℓ) (e * ℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩

  set x₀ : Λ := qExpand ℚ (e * ℓ) jq with hx₀
  set E : IntermediateField ↥K Λ := Enew K e ℓ with hEdef
  obtain ⟨h, hmon, hmap, hev, htO, ht0⟩ := exists_twisted ℓ e
  set u₁ : Λ := uE e with hu₁
  set t₁ : Λ := tE ℓ e with ht₁
  have hu₁O := uE_mem_𝒪_and_coeff e
  have ht₁ne : t₁ ≠ 0 := ne_zero_of_not_inP p (not_inP_of_coeff_eq_one p ht0)
  have ht₁𝒪p : t₁ ∈ 𝒪p p := ⟨htO, by rw [ht0]; exact Subring.one_mem _⟩
  have hjK : jq ∈ K := hK.jq_mem
  have hKE : ∀ z : Λ, z ∈ K → z ∈ E := fun z hz => IntermediateField.algebraMap_mem E (⟨z, hz⟩ : ↥K)
  have hx₀E : x₀ ∈ E := IntermediateField.mem_adjoin_simple_self ↥K x₀

  obtain ⟨a, haK, s, hsK, ha, hs, hsP, hsu⟩ := hK.inv_mem
  have hs0 : s ≠ 0 := ne_zero_of_not_inP p hsP
  have hu₁as : u₁ = a * s⁻¹ := by
    rw [← hsu, hu₁, uE]; field_simp
  have hu₁K : u₁ ∈ K := by rw [hu₁as]; exact K.mul_mem haK (K.inv_mem hsK)
  have hu₁R : u₁ ∈ RK p K := by rw [hu₁as]; exact div_mem_RK haK ha hsK hs hsP
  have ht₁E : t₁ ∈ E := by
    rw [ht₁, tE]; exact E.mul_mem hx₀E (pow_mem (hKE _ hu₁K) ℓ)

  haveI : IsFractionRing ↥(RK p K) ↥K := isFractionRing_RK hK
  haveI : IsIntegrallyClosed ↥(RK p K) := isIntegrallyClosed_RK hK
  set uRK : ↥(RK p K) := uR (p := p) hjK with huRK
  set u₁R : ↥(RK p K) := ⟨u₁, hu₁R⟩ with hu₁Rdef

  haveI : CharZero ↥K := inferInstance
  have hcompK : ∀ (P : Polynomial (Polynomial ℤ)) (uK' : ↥K) (y : Λ),
      P.eval₂ (eval₂RingHom (algebraMap ℤ Λ) (uK' : Λ)) y
        = (P.map (eval₂RingHom (Int.castRingHom ↥K) uK')).eval₂ (algebraMap ↥K Λ) y := by
    intro P uK' y
    rw [eval₂_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [coe_eval₂RingHom, eval₂_X, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]; rfl
  have ht₁K : IsIntegral ↥K t₁ := by
    refine ⟨h.map (eval₂RingHom (Int.castRingHom ↥K) ⟨u₁, hu₁K⟩), hmon.map _, ?_⟩
    rw [← hcompK]; exact hev
  have hx₀t : x₀ = t₁ * (u₁ ^ ℓ)⁻¹ := by
    rw [ht₁, tE, ← hu₁, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (uE_ne_zero e)), mul_one]
  have hx₀K : IsIntegral ↥K x₀ := by
    rw [hx₀t]
    exact ht₁K.mul (isIntegral_algebraMap (x := (⟨(u₁ ^ ℓ)⁻¹, K.inv_mem (pow_mem hu₁K ℓ)⟩ : ↥K)))
  haveI hfd : FiniteDimensional ↥K ↥E := IntermediateField.adjoin.finiteDimensional hx₀K
  haveI : Algebra.IsSeparable ↥K ↥E := Algebra.IsSeparable.of_integral _ _
  have hEadj : E.toSubalgebra = Algebra.adjoin ↥K {x₀} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hx₀K.isAlgebraic

  haveI : IsScalarTower ↥(RK p K) ↥K ↥E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥(BK p K) ↥K ↥E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥(BK p K) ↥(RK p K) ↥E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have clear : ∀ z : ↥E, IsIntegral ↥(RK p K) z → ∃ m : Λ, m ∈ K ∧ IsIntB p m ∧ ¬ InP p (m.coeff 0) ∧
      IsIntB p (m * (z : Λ)) := by
    intro z hz
    obtain ⟨⟨m, hm⟩, hmz⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (𝔪K p K).primeCompl (Rₘ := ↥(RK p K)) z hz
    refine ⟨(m : Λ), BK.memK m, BK.isIntB m, (mem_primeCompl_iff m).mp hm, ?_⟩
    have h1 : IsIntB p (((m • z : ↥E)) : Λ) :=
      isIntB_of_isIntegral_BK hjK (L := ↥E) (algebraMap ↥E Λ) (fun _ => rfl) hmz
    rwa [Algebra.smul_def, MulMemClass.coe_mul] at h1
  have mem_𝒪p_of_int : ∀ z : ↥E, IsIntegral ↥(RK p K) z → (z : Λ) ∈ 𝒪p p := by
    intro z hz
    obtain ⟨m, hmK, hm, hmP, hmz⟩ := clear z hz
    have hm0 : m ≠ 0 := ne_zero_of_not_inP p hmP
    have : (z : Λ) = m⁻¹ * (m * (z : Λ)) := by rw [← mul_assoc, inv_mul_cancel₀ hm0, one_mul]
    rw [this]
    exact Subring.mul_mem _ (inv_mem_𝒪p p hm.mem_𝒪p hmP) hmz.mem_𝒪p

  set κ := IsLocalRing.ResidueField (Zp p)
  set D : Subalgebra ↥(RK p K) ↥E := integralClosure ↥(RK p K) ↥E with hDdef
  have D_mem_𝒪p : ∀ z : ↥D, ((z : ↥E) : Λ) ∈ 𝒪p p := fun z => mem_𝒪p_of_int (z : ↥E) z.2
  let ψD : ↥D →+* ↥(𝒪p p) :=
    { toFun := fun z => ⟨((z : ↥E) : Λ), D_mem_𝒪p z⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  set φ : ↥D →+* κ := (IsLocalRing.residue (Zp p)).comp ((ev p).comp ψD) with hφdef
  have φ_apply : ∀ z : ↥D, φ z = IsLocalRing.residue (Zp p) (ev p ⟨((z : ↥E) : Λ), D_mem_𝒪p z⟩) :=
    fun _ => rfl
  have φ_eq_zero_iff : ∀ z : ↥D, φ z = 0 ↔ InP p (((z : ↥E) : Λ).coeff 0) := fun z => by
    rw [φ_apply, IsLocalRing.residue_eq_zero_iff, ← inP_coeff_iff]
  have φ_ne_zero_iff : ∀ z : ↥D, φ z ≠ 0 ↔ ¬ InP p (((z : ↥E) : Λ).coeff 0) := fun z => by
    rw [Ne, φ_eq_zero_iff]
  have φ_algebraMap : ∀ r : ↥(RK p K), φ (algebraMap ↥(RK p K) ↥D r) = πR p K r := fun _ => rfl
  have hφsurj : Function.Surjective (φ.comp (algebraMap ↥(RK p K) ↥D)) := by
    intro k
    obtain ⟨n, hn⟩ := πR_int_surjective (p := p) (K := K) k
    exact ⟨n, by rw [RingHom.comp_apply, φ_algebraMap]; exact hn⟩

  set tE' : ↥E := ⟨t₁, ht₁E⟩ with htE'
  set g : Polynomial ↥(RK p K) := h.map (eval₂RingHom (Int.castRingHom ↥(RK p K)) u₁R) with hg
  have hgmon : g.Monic := hmon.map _
  have hgt' : aeval tE' g = 0 := by
    have hinjE : Function.Injective (algebraMap ↥E Λ) := Subtype.coe_injective
    apply hinjE
    rw [map_zero, aeval_def, Polynomial.hom_eval₂, hg, eval₂_map, ← hev]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
    rfl
  have htRint : IsIntegral ↥(RK p K) tE' := ⟨g, hgmon, by rw [← aeval_def]; exact hgt'⟩
  set tD : ↥D := ⟨tE', htRint⟩ with htD
  have hgt : aeval tD g = 0 := by
    have hinjDE : Function.Injective (algebraMap ↥D ↥E) := Subtype.coe_injective
    apply hinjDE
    rw [map_zero, ← aeval_algebraMap_apply]
    exact hgt'
  have hφt : φ tD = 1 := by
    rw [φ_apply, ← (IsLocalRing.residue (Zp p)).map_one]
    congr 1
    apply Subtype.ext
    rw [coe_ev]
    exact ht0

  have ht_top : Algebra.adjoin ↥K {((tD : ↥D) : ↥E)} = ⊤ := by
    change Algebra.adjoin ↥K {(⟨t₁, ht₁E⟩ : ↥(IntermediateField.adjoin ↥K {x₀}))} = ⊤
    have hpb := (IntermediateField.adjoin.powerBasis hx₀K).adjoin_gen_eq_top
    rw [IntermediateField.adjoin.powerBasis_gen] at hpb
    rw [eq_top_iff, ← hpb, Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    have hgen : IntermediateField.AdjoinSimple.gen ↥K x₀
        = algebraMap ↥K _ ⟨(u₁ ^ ℓ)⁻¹, K.inv_mem (pow_mem hu₁K ℓ)⟩
          * (⟨t₁, ht₁E⟩ : ↥(IntermediateField.adjoin ↥K {x₀})) := by
      apply Subtype.ext
      change x₀ = (u₁ ^ ℓ)⁻¹ * t₁
      rw [hx₀t, mul_comm]
    rw [hgen]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Algebra.subset_adjoin rfl)

  have hsimple : ((g.map (φ.comp (algebraMap ↥(RK p K) ↥D))).derivative).eval (φ tD) ≠ 0 := by
    have hψu : (φ.comp (algebraMap ↥(RK p K) ↥D)) u₁R = 0 := by
      rw [RingHom.comp_apply, φ_algebraMap, πR_eq_zero_iff]
      change InP p (u₁.coeff 0)
      rw [hu₁, hu₁O.2]; exact inP_zero p
    have hgmap : g.map (φ.comp (algebraMap ↥(RK p K) ↥D)) = X ^ ℓ * (X - Polynomial.C 1) := by
      rw [hg, Polynomial.map_map]
      have hcomp : (φ.comp (algebraMap ↥(RK p K) ↥D)).comp (eval₂RingHom (Int.castRingHom ↥(RK p K)) u₁R)
          = (Int.castRingHom κ).comp (evalRingHom 0) := by
        refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
        have h2 : ((Int.castRingHom κ).comp (evalRingHom 0)) X = 0 := by
          rw [RingHom.comp_apply, coe_evalRingHom, eval_X, map_zero]
        rw [h2, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
        exact hψu
      rw [hcomp, ← Polynomial.map_map, hmap, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_pow,
        map_X, map_one]
      ring
    have hroot : (g.map (φ.comp (algebraMap ↥(RK p K) ↥D))).eval 1 = 0 := by
      have h1 : φ (aeval tD g) = 0 := by rw [hgt, map_zero]
      rw [aeval_def, hom_eval₂, hφt, ← eval_map] at h1
      exact h1
    have hdvd : g.map (φ.comp (algebraMap ↥(RK p K) ↥D)) ∣ X ^ ℓ * (X - Polynomial.C 1) := by rw [hgmap]
    rw [hφt]
    exact eval_derivative_ne_zero_of_dvd hdvd hroot

  have gen' : ∀ x ∈ EnewQ K e ℓ, IsIntB p x → InP p (x.coeff 0) →
      ∃ s ∈ EnewQ K e ℓ, ∃ c ∈ EnewQ K e ℓ, ∃ d ∈ EnewQ K e ℓ,
        IsIntB p s ∧ IsIntB p c ∧ IsIntB p d ∧ ¬ InP p (s.coeff 0) ∧
        s * x = (p : Λ) * c + uΛ * d := by
    intro x hxE hxint hxP
    rw [mem_EnewQ] at hxE
    change x ∈ E at hxE

    have hxR : IsIntegral ↥(RK p K) (⟨x, hxE⟩ : ↥E) :=
      isIntegral_of_isIntB (p := p) (P := ↥(RK p K)) (L := ↥E) (algebraMap ↥E Λ) Subtype.coe_injective
        uRK rfl (algebraMap (Zp p) ↥(RK p K)) (fun r => rfl) hxint
    set xD : ↥D := ⟨⟨x, hxE⟩, hxR⟩ with hxD
    have hφx : φ xD = 0 := (φ_eq_zero_iff xD).mpr hxP
    obtain ⟨sD, hsφ, hmem⟩ :=
      Subalgebra.exists_mul_mem_map_ker_of_eval_derivative_map_ne_zero
        (P := ↥(RK p K)) (K := ↥K) (L := ↥E) D φ hφsurj tD ht_top g hgmon hgt hsimple xD hxR hφx

    have hle : (RingHom.ker (φ.comp (algebraMap ↥(RK p K) ↥D))).map (algebraMap ↥(RK p K) ↥D)
        ≤ Ideal.span {(p : ↥D), algebraMap ↥(RK p K) ↥D uRK} := by
      refine (Ideal.map_mono (fun r hr => mem_span_of_πR_eq_zero hK r ?_)).trans ?_
      · rw [RingHom.mem_ker, RingHom.comp_apply, φ_algebraMap] at hr; exact hr
      · rw [Ideal.map_span, Set.image_pair, map_natCast]
    obtain ⟨c₁, c₂, hc₁₂⟩ := Ideal.mem_span_pair.mp (hle hmem)

    obtain ⟨ms, hmsK, hms, hmsP, hmss⟩ := clear (sD : ↥E) sD.2
    obtain ⟨m₁, hm₁K, hm₁, hm₁P, hm₁c⟩ := clear (c₁ : ↥E) c₁.2
    obtain ⟨m₂, hm₂K, hm₂, hm₂P, hm₂c⟩ := clear (c₂ : ↥E) c₂.2
    have hsP' : ¬ InP p ((((sD : ↥D) : ↥E) : Λ).coeff 0) := (φ_ne_zero_iff sD).mp hsφ

    have hrelΛ : (((sD : ↥D) : ↥E) : Λ) * x
        = (((c₁ : ↥D) : ↥E) : Λ) * (p : Λ) + (((c₂ : ↥D) : ↥E) : Λ) * uΛ := by
      have h1 := congrArg (fun z : ↥D => ((z : ↥E) : Λ)) hc₁₂
      simp only [Subalgebra.coe_mul, Subalgebra.coe_add, MulMemClass.coe_mul, AddMemClass.coe_add] at h1
      rw [← h1]
      have hp' : (((p : ↥D) : ↥E) : Λ) = (p : Λ) := by
        rw [SubringClass.coe_natCast, SubringClass.coe_natCast]
      rw [hp']
      try rfl
    set S : Λ := (ms * (((sD : ↥D) : ↥E) : Λ)) * m₁ * m₂ with hS
    have hEmem : ∀ z : ↥D, (((z : ↥D) : ↥E) : Λ) ∈ E := fun z => ((z : ↥D) : ↥E).2
    refine ⟨S, ?_, m₂ * ms * (m₁ * (((c₁ : ↥D) : ↥E) : Λ)), ?_, m₁ * ms * (m₂ * (((c₂ : ↥D) : ↥E) : Λ)), ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_EnewQ, hS]
      exact E.mul_mem (E.mul_mem (E.mul_mem (hKE _ hmsK) (hEmem sD)) (hKE _ hm₁K)) (hKE _ hm₂K)
    · rw [mem_EnewQ]
      exact E.mul_mem (E.mul_mem (hKE _ hm₂K) (hKE _ hmsK)) (E.mul_mem (hKE _ hm₁K) (hEmem c₁))
    · rw [mem_EnewQ]
      exact E.mul_mem (E.mul_mem (hKE _ hm₁K) (hKE _ hmsK)) (E.mul_mem (hKE _ hm₂K) (hEmem c₂))
    · rw [hS]; exact (hmss.mul hm₁).mul hm₂
    · exact (hm₂.mul hms).mul hm₁c
    · exact (hm₁.mul hms).mul hm₂c
    · rw [hS]
      refine not_inP_mul p ?_ hm₂.mem_𝒪p ?_ hm₂P
      · exact Subring.mul_mem _ (Subring.mul_mem _ hms.mem_𝒪p (D_mem_𝒪p sD)) hm₁.mem_𝒪p
      refine not_inP_mul p ?_ hm₁.mem_𝒪p ?_ hm₁P
      · exact Subring.mul_mem _ hms.mem_𝒪p (D_mem_𝒪p sD)
      exact not_inP_mul p hms.mem_𝒪p (D_mem_𝒪p sD) hmsP hsP'
    · rw [hS]
      linear_combination (ms * m₁ * m₂) * hrelΛ

  have frac' : ∀ x ∈ EnewQ K e ℓ, ∃ b ∈ EnewQ K e ℓ, ∃ s ∈ EnewQ K e ℓ,
      IsIntB p b ∧ IsIntB p s ∧ s ≠ 0 ∧ s * x = b := by
    intro x hxE
    rw [mem_EnewQ] at hxE
    change x ∈ E at hxE
    have hxadj : x ∈ Algebra.adjoin ↥K {x₀} := by
      rw [← hEadj]; exact hxE

    obtain ⟨mt, hmtK, hmt, hmtP, hmtt⟩ := clear tE' htRint
    have ha0 : a ≠ 0 := by
      intro ha0
      apply uE_ne_zero e
      rw [← hu₁, hu₁as, ha0, zero_mul]
    have hx₀rel : (a ^ ℓ * mt) * x₀ = s ^ ℓ * (mt * t₁) := by
      rw [hx₀t, hu₁as, mul_pow, inv_pow, mul_inv, inv_inv]
      field_simp
    simp only [mem_EnewQ]
    change ∃ b ∈ E, ∃ s ∈ E, IsIntB p b ∧ IsIntB p s ∧ s ≠ 0 ∧ s * x = b
    induction hxadj using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff] at hz; subst hz
      refine ⟨s ^ ℓ * (mt * t₁), ?_, a ^ ℓ * mt, ?_, (hs.pow ℓ).mul hmtt, (ha.pow ℓ).mul hmt, ?_, hx₀rel⟩
      · exact E.mul_mem (pow_mem (hKE _ hsK) ℓ) (E.mul_mem (hKE _ hmtK) ht₁E)
      · exact hKE _ (K.mul_mem (pow_mem haK ℓ) hmtK)
      · exact mul_ne_zero (pow_ne_zero _ ha0) (ne_zero_of_not_inP p hmtP)
    | algebraMap r =>
      obtain ⟨b, hbK, s', hs'K, hb, hs', hs'0, hrel⟩ := hK.frac (r : Λ) r.2
      exact ⟨b, hKE _ hbK, s', hKE _ hs'K, hb, hs', hs'0, hrel⟩
    | add y z hy hz ihy ihz =>
      obtain ⟨b₁, hb₁E, s₁, hs₁E, hb₁, hs₁, hs₁0, h₁⟩ := ihy (by rw [← hEadj] at hy; exact hy)
      obtain ⟨b₂, hb₂E, s₂, hs₂E, hb₂, hs₂, hs₂0, h₂⟩ := ihz (by rw [← hEadj] at hz; exact hz)
      refine ⟨s₂ * b₁ + s₁ * b₂, E.add_mem (E.mul_mem hs₂E hb₁E) (E.mul_mem hs₁E hb₂E), s₁ * s₂,
        E.mul_mem hs₁E hs₂E, (hs₂.mul hb₁).add (hs₁.mul hb₂), hs₁.mul hs₂, mul_ne_zero hs₁0 hs₂0, ?_⟩
      linear_combination s₂ * h₁ + s₁ * h₂
    | mul y z hy hz ihy ihz =>
      obtain ⟨b₁, hb₁E, s₁, hs₁E, hb₁, hs₁, hs₁0, h₁⟩ := ihy (by rw [← hEadj] at hy; exact hy)
      obtain ⟨b₂, hb₂E, s₂, hs₂E, hb₂, hs₂, hs₂0, h₂⟩ := ihz (by rw [← hEadj] at hz; exact hz)
      refine ⟨b₁ * b₂, E.mul_mem hb₁E hb₂E, s₁ * s₂, E.mul_mem hs₁E hs₂E, hb₁.mul hb₂, hs₁.mul hs₂,
        mul_ne_zero hs₁0 hs₂0, ?_⟩
      linear_combination (s₂ * z) * h₁ + b₁ * h₂

  have inv' : ∃ a' ∈ EnewQ K e ℓ, ∃ s' ∈ EnewQ K e ℓ, IsIntB p a' ∧ IsIntB p s' ∧
      ¬ InP p (s'.coeff 0) ∧ s' * (qExpand ℚ (e * ℓ) jq)⁻¹ = a' := by
    obtain ⟨mt, hmtK, hmt, hmtP, hmtt⟩ := clear tE' htRint
    refine ⟨a ^ ℓ * mt, ?_, s ^ ℓ * (mt * t₁), ?_, (ha.pow ℓ).mul hmt, (hs.pow ℓ).mul hmtt, ?_, ?_⟩
    · rw [mem_EnewQ]
      exact hKE _ (K.mul_mem (pow_mem haK ℓ) hmtK)
    · rw [mem_EnewQ]
      exact E.mul_mem (pow_mem (hKE _ hsK) ℓ) (E.mul_mem (hKE _ hmtK) ht₁E)
    · exact not_inP_mul p (Subring.pow_mem _ hs.mem_𝒪p _) (Subring.mul_mem _ hmt.mem_𝒪p ht₁𝒪p)
        (not_inP_pow p hs.mem_𝒪p hsP ℓ) (not_inP_mul p hmt.mem_𝒪p ht₁𝒪p hmtP (not_inP_of_coeff_eq_one p ht0))
    · rw [tE_inv_eq ℓ e, ← hu₁, ← ht₁, hu₁as, mul_pow, inv_pow]
      field_simp
  exact ⟨mem_EnewQ.mpr (hKE _ hjK), frac', gen', inv'⟩

end Step

section Base

variable (p : ℕ) [hp : Fact p.Prime]

def K1 : IntermediateField ℚ Λ := IntermediateField.adjoin ℚ {jq}

theorem jq_mem_K1 : jq ∈ K1 := IntermediateField.mem_adjoin_simple_self ℚ jq
theorem uΛ_mem_K1 : uΛ ∈ K1 := (K1).inv_mem jq_mem_K1

theorem A0_mem_K1 {z : Λ} (hz : z ∈ A0 p) : z ∈ K1 := A0_subset (K := K1) jq_mem_K1 hz

theorem coeff_zero_aeval_uΛ (f : (Zp p)[X]) : (aeval uΛ f).coeff 0 = ((f.coeff 0 : Zp p) : ℚ) := by
  set cst : Zp p →+* ↥(𝒪p p) :=
    (algebraMap (Zp p) Λ).codRestrict (𝒪p p) (fun r => (isIntB_algebraMap p r).mem_𝒪p) with hcst
  set κ₀ : (Zp p)[X] →+* ↥(𝒪p p) := eval₂RingHom cst ⟨uΛ, uΛ_mem_𝒪p p⟩ with hκ₀
  have h1 : ((𝒪p p).subtype).comp κ₀ = (aeval (R := Zp p) uΛ).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, hκ₀, coe_eval₂RingHom, eval₂_C, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, aeval_C]; rfl
    · rw [RingHom.comp_apply, hκ₀, coe_eval₂RingHom, eval₂_X, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, aeval_X]; rfl
  have h2 : (ev p).comp κ₀ = evalRingHom 0 := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, hκ₀, coe_eval₂RingHom, eval₂_C, coe_evalRingHom, eval_C]
      apply Subtype.ext; rw [coe_ev]; exact coeff_zero_algebraMap p c
    · rw [RingHom.comp_apply, hκ₀, coe_eval₂RingHom, eval₂_X, coe_evalRingHom, eval_X]
      exact ev_uΛ p
  have h3 : aeval uΛ f = ((κ₀ f : ↥(𝒪p p)) : Λ) :=
    (congrArg (fun g : (Zp p)[X] →+* Λ => g f) h1).symm
  calc (aeval uΛ f).coeff 0 = ((ev p (κ₀ f) : Zp p) : ℚ) := by rw [h3]; rfl
    _ = ((evalRingHom 0 f : Zp p) : ℚ) := by rw [← RingHom.comp_apply, h2]
    _ = _ := by rw [coe_evalRingHom, ← coeff_zero_eq_eval_zero]

theorem frac_K1 : ∀ x ∈ K1, ∃ b ∈ K1, ∃ s ∈ K1, IsIntB p b ∧ IsIntB p s ∧ s ≠ 0 ∧ s * x = b := by
  intro x hx
  obtain ⟨b, hb, s, hs, hs0, hrel⟩ := (ModularCurve.mem_adjoin_jq_inv_of_isIntegral_and_exists_mul_eq p).2 x hx
  exact ⟨b, A0_mem_K1 p hb, s, A0_mem_K1 p hs, isIntB_of_mem_A0 p hb, isIntB_of_mem_A0 p hs, hs0, hrel⟩

theorem gen_K1 : ∀ x ∈ K1, IsIntB p x → InP p (x.coeff 0) →
    ∃ s ∈ K1, ∃ c ∈ K1, ∃ d ∈ K1, IsIntB p s ∧ IsIntB p c ∧ IsIntB p d ∧ ¬ InP p (s.coeff 0) ∧
      s * x = (p : Λ) * c + uΛ * d := by
  intro x hxK hx hxP
  have hxA : x ∈ A0 p := (ModularCurve.mem_adjoin_jq_inv_of_isIntegral_and_exists_mul_eq p).1 x hxK hx
  obtain ⟨f, rfl⟩ : ∃ f : (Zp p)[X], aeval uΛ f = x := by
    rwa [A0, Algebra.adjoin_singleton_eq_range_aeval] at hxA
  rw [coeff_zero_aeval_uΛ, inP_iff, mem_maximalIdeal_iff] at hxP
  obtain ⟨c₀, hc₀⟩ := hxP
  refine ⟨1, (K1).one_mem, algebraMap (Zp p) Λ c₀, ?_, aeval uΛ f.divX, ?_, isIntB_one p,
    isIntB_algebraMap p c₀, isIntB_aeval_uΛ p _, ?_, ?_⟩
  · exact A0_mem_K1 p (Subalgebra.algebraMap_mem _ _)
  · exact A0_mem_K1 p (aeval_uΛ_mem_A0 p _)
  · rw [HahnSeries.coeff_one]; simp only [if_true]
    exact fun h => not_inP_one p (by simpa using h)
  · conv_lhs => rw [one_mul, ← X_mul_divX_add f]
    rw [map_add, map_mul, aeval_X, aeval_C, hc₀, map_mul, map_natCast]
    ring

theorem good_K1 : Good p K1 1 := by
  refine ⟨jq_mem_K1, frac_K1 p, gen_K1 p, uΛ, uΛ_mem_K1, 1, (K1).one_mem, isIntB_uΛ p, isIntB_one p, ?_, ?_⟩
  · rw [HahnSeries.coeff_one]; simp only [if_true]
    exact fun h => not_inP_one p (by simpa using h)
  · rw [one_mul, qExpand_one_apply]; rfl

end Base

section Assembly

variable (p : ℕ) [hp : Fact p.Prime]

theorem full_one_eq : modularFunctionFieldFull 1 = K1 := by
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  rw [(ModularCurve.functionFieldGeneration_iff_full_eq 1).mp functionFieldGeneration_one,
    modularFunctionField_one]; rfl

theorem EnewQ_eq (a ℓ : ℕ) [NeZero a] [Fact ℓ.Prime] :
    EnewQ (modularFunctionFieldFull a) a ℓ = modularFunctionFieldFull (ℓ * a) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  set K := modularFunctionFieldFull a with hKdef
  have hKle : K ≤ modularFunctionFieldFull (ℓ * a) := full_degeneracy_le (dvd_mul_left a ℓ)
  apply le_antisymm
  ·
    set F'' : IntermediateField ↥K Λ :=
      Subfield.toIntermediateField (modularFunctionFieldFull (ℓ * a)).toSubfield
        (fun k => by rw [IntermediateField.mem_toSubfield]; exact hKle k.2) with hF''
    have hle : Enew K a ℓ ≤ F'' := by
      rw [Enew, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      change qExpand ℚ (a * ℓ) jq ∈ modularFunctionFieldFull (ℓ * a)
      rw [qExpand_congr (mul_comm a ℓ)]
      exact jqd_mem_full (ℓ * a) dvd_rfl
    intro x hx
    exact hle hx
  · change IntermediateField.adjoin ℚ (divisorExpansions (ℓ * a)) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro x ⟨d, hd, hdvd, rfl⟩
    haveI := hd
    have hgen := ModularCurve.functionFieldGeneration (ℓ * a) d hdvd hd
    have hle : IntermediateField.adjoin ℚ {jq, qExpand ℚ (ℓ * a) jq} ≤ EnewQ K a ℓ := by
      rw [IntermediateField.adjoin_le_iff]
      rintro y (rfl | rfl)
      · have hjK : jq ∈ K := by
          have := jqd_mem_full a (one_dvd a); rwa [qExpand_one_apply] at this
        exact mem_EnewQ.mpr ((Enew K a ℓ).algebraMap_mem (⟨jq, hjK⟩ : ↥K))
      · change qExpand ℚ (ℓ * a) jq ∈ EnewQ K a ℓ
        rw [mem_EnewQ, qExpand_congr (mul_comm ℓ a)]
        exact IntermediateField.mem_adjoin_simple_self ↥K _
    exact hle hgen

theorem good_full (M : ℕ) [hM : NeZero M] : Good p (modularFunctionFieldFull M) M := by
  have key : ∀ M : ℕ, ∀ _hM : NeZero M, Good p (modularFunctionFieldFull M) M := by
    intro M
    apply UniqueFactorizationMonoid.induction_on_prime
      (P := fun M => ∀ _hM : NeZero M, Good p (modularFunctionFieldFull M) M)
    · intro h; exact absurd rfl h.out
    · intro x hx _
      obtain rfl := Nat.isUnit_iff.mp hx
      have h := good_K1 p
      rw [← full_one_eq] at h
      exact h
    · intro a ℓ ha hℓ ih _
      haveI : Fact ℓ.Prime := ⟨Nat.prime_iff.mpr hℓ⟩
      haveI : NeZero a := ⟨ha⟩
      have hstep := step p (ih inferInstance) ℓ
      rw [EnewQ_eq] at hstep
      obtain ⟨h1, h2, h3, h4⟩ := hstep
      refine ⟨h1, h2, h3, ?_⟩
      rw [qExpand_congr (mul_comm ℓ a)]
      exact h4
  exact key M hM

end Assembly

section Final

open ModularCurve.IgusaScheme

variable (M p : ℕ) [NeZero M] [hp : Fact p.Prime]

theorem isIntB_iff_mem_chartAlgInf (b : ↥(modularFunctionFieldFull M)) :
    b ∈ chartAlgInf M p ↔ IsIntB p (b : Λ) := by
  rw [mem_chartAlg_iff]
  have hcomm : (algebraMap ↥(modularFunctionFieldFull M) Λ).comp
      (algebraMap (Zp p) ↥(modularFunctionFieldFull M)) = algebraMap (Zp p) Λ := by
    refine RingHom.ext fun r => ?_
    first
      | (change ((algebraMap ℚ ↥(modularFunctionFieldFull M) (r : ℚ) : ↥(modularFunctionFieldFull M)) : Λ)
          = algebraMap ℚ Λ (r : ℚ); exact coe_ratHom_eq _ _ _)
      | exact (IsScalarTower.algebraMap_apply (Zp p) ↥(modularFunctionFieldFull M) Λ r).symm
      | (rw [RingHom.comp_apply, algebraMap_Zp_eq, IsScalarTower.algebraMap_apply (Zp p) ℚ ↥(modularFunctionFieldFull M) r];
         exact coe_ratHom_eq _ _ _)
  have h := isIntegral_adjoin_iff_of_ringHom p (S := ↥(modularFunctionFieldFull M)) (S' := Λ)
    (algebraMap ↥(modularFunctionFieldFull M) Λ) Subtype.coe_injective hcomm (s := (jFull M)⁻¹) (b := b)
  rw [h]
  have hu : (algebraMap ↥(modularFunctionFieldFull M) Λ) (jFull M)⁻¹ = uΛ := by
    rw [map_inv₀]; rfl
  rw [hu]; rfl

theorem main (b : ↥(chartAlgInf M p))
    (hb : ∃ c ∈ GaloisRep.ratLocalizedAt p,
      ((b : ↥(modularFunctionFieldFull M)) : Λ).coeff 0 = (p : ℚ) * c) :
    ∃ s c d : ↥(chartAlgInf M p),
      (¬ ∃ c' ∈ GaloisRep.ratLocalizedAt p,
        ((s : ↥(modularFunctionFieldFull M)) : Λ).coeff 0 = (p : ℚ) * c') ∧
      s * b = (p : ↥(chartAlgInf M p)) * c + jInvChartInf M p * d := by
  have hG := good_full p M
  have hbint : IsIntB p ((b : ↥(modularFunctionFieldFull M)) : Λ) :=
    (isIntB_iff_mem_chartAlgInf M p _).mp b.2
  obtain ⟨s, hsK, c, hcK, d, hdK, hs, hc, hd, hsP, hrel⟩ :=
    hG.gen _ (b : ↥(modularFunctionFieldFull M)).2 hbint hb
  refine ⟨⟨⟨s, hsK⟩, (isIntB_iff_mem_chartAlgInf M p _).mpr hs⟩,
    ⟨⟨c, hcK⟩, (isIntB_iff_mem_chartAlgInf M p _).mpr hc⟩,
    ⟨⟨d, hdK⟩, (isIntB_iff_mem_chartAlgInf M p _).mpr hd⟩, hsP, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change s * ((b : ↥(modularFunctionFieldFull M)) : Λ)
    = ((((p : ↥(chartAlgInf M p)) : ↥(modularFunctionFieldFull M)) : Λ)) * c
      + (((jInvChartInf M p : ↥(chartAlgInf M p)) : ↥(modularFunctionFieldFull M)) : Λ) * d
  rw [hrel]
  have hp' : ((((p : ↥(chartAlgInf M p)) : ↥(modularFunctionFieldFull M)) : Λ)) = (p : Λ) := by
    rw [SubringClass.coe_natCast, SubringClass.coe_natCast]
  rw [hp']
  try rfl

end Final

end CuspInftyTower
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_mul_eq_natCast_mul_add_jInvChartInf_mul_of_coeff_zero_mem.CuspInftyTower"

open ModularCurve ModularCurve.IgusaScheme in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (b : ↥(chartAlgInf M p))
    (hb : ∃ c ∈ GaloisRep.ratLocalizedAt p,
      ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ).coeff 0 = (p : ℚ) * c) :
    ∃ s c d : ↥(chartAlgInf M p),
      (¬ ∃ c' ∈ GaloisRep.ratLocalizedAt p,
        ((s : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ).coeff 0 = (p : ℚ) * c') ∧
      s * b = (p : ↥(chartAlgInf M p)) * c + jInvChartInf M p * d :=
  CuspInftyTower.main M p b hb

end
end S_ModularCurve_IgusaScheme_exists_mul_eq_natCast_mul_add_jInvChartInf_mul_of_coeff_zero_mem
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_mul_eq_natCast_mul_add_jInvChartInf_mul_of_coeff_zero_mem (solution)
