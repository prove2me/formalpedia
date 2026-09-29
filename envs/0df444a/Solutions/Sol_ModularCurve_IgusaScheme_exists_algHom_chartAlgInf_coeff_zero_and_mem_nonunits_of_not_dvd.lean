-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e376b230-e16e-5aa2-b1e3-db7cf92f5549

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_ModularPolynomialData_weighted_support_le
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical
open Polynomial ModularCurve ModularCurve.IgusaScheme WithZero

namespace NeronLeg1CuspSections

section QAdic

def 𝒪 : Subring (LaurentSeries ℚ) := (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).integer

theorem mem_𝒪_iff (f : LaurentSeries ℚ) : f ∈ 𝒪 ↔ ∀ n : ℤ, n < 0 → f.coeff n = 0 := by
  rw [𝒪, Valuation.mem_integer_iff]
  have h := LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := ℚ) (D := 0) (f := f)
  simpa using h

theorem exists_powerSeries_of_mem_𝒪 {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) :
    ∃ F : PowerSeries ℚ, (F : LaurentSeries ℚ) = f :=
  (LaurentSeries.val_le_one_iff_eq_coe (K := ℚ) f).mp hf

theorem coe_powerSeries_mem_𝒪 (F : PowerSeries ℚ) : (F : LaurentSeries ℚ) ∈ 𝒪 :=
  (LaurentSeries.val_le_one_iff_eq_coe (K := ℚ) (F : LaurentSeries ℚ)).mpr ⟨F, rfl⟩

theorem coeff_zero_coe_powerSeries (F : PowerSeries ℚ) :
    (F : LaurentSeries ℚ).coeff 0 = PowerSeries.constantCoeff F := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, LaurentSeries.coeff_coe_powerSeries]

theorem C_mem_𝒪 (c : ℚ) : (HahnSeries.C c : LaurentSeries ℚ) ∈ 𝒪 := by
  rw [mem_𝒪_iff]
  intro n hn
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hn.ne]

def ρ : ↥𝒪 →+* ℚ where
  toFun f := (f : LaurentSeries ℚ).coeff 0
  map_one' := by simp
  map_mul' f g := by
    obtain ⟨F, hF⟩ := exists_powerSeries_of_mem_𝒪 f.2
    obtain ⟨G, hG⟩ := exists_powerSeries_of_mem_𝒪 g.2
    change ((f : LaurentSeries ℚ) * (g : LaurentSeries ℚ)).coeff 0
      = (f : LaurentSeries ℚ).coeff 0 * (g : LaurentSeries ℚ).coeff 0
    rw [← hF, ← hG, ← map_mul]
    change ((F * G : PowerSeries ℚ) : LaurentSeries ℚ).coeff 0
      = (F : LaurentSeries ℚ).coeff 0 * (G : LaurentSeries ℚ).coeff 0
    rw [coeff_zero_coe_powerSeries, coeff_zero_coe_powerSeries, coeff_zero_coe_powerSeries, map_mul]
  map_zero' := by simp
  map_add' f g := by simp

@[scoped simp] theorem ρ_apply (f : ↥𝒪) : ρ f = (f : LaurentSeries ℚ).coeff 0 := rfl

theorem ρ_C (c : ℚ) : ρ ⟨HahnSeries.C c, C_mem_𝒪 c⟩ = c := by
  change (HahnSeries.C c : LaurentSeries ℚ).coeff 0 = c
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]

theorem coeff_zero_single_mul_of_mem_𝒪 {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) {m : ℤ} (hm : 0 < m) :
    (HahnSeries.single m (1 : ℚ) * f).coeff 0 = 0 := by
  rw [HahnSeries.coeff_single_mul, one_mul]
  exact (mem_𝒪_iff f).mp hf _ (by omega)

theorem single_mul_mem_𝒪 {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) {m : ℤ} (hm : 0 ≤ m) :
    HahnSeries.single m (1 : ℚ) * f ∈ 𝒪 := by
  rw [mem_𝒪_iff] at hf ⊢
  intro n hn
  rw [HahnSeries.coeff_single_mul, one_mul]
  exact hf _ (by omega)

end QAdic

section Zl

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem mem_ratLocalizedAt_iff (x : ℚ) :
    x ∈ GaloisRep.ratLocalizedAt ℓ ↔ x ∈ (Rat.padicValuation ℓ).integer := by
  have hℓ : ℓ.Prime := Fact.out
  rw [Valuation.mem_integer_iff]
  change x.den.Coprime ℓ ↔ _
  simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  by_cases hx : x = 0
  · subst hx; simp
  rw [if_neg hx, ← WithZero.exp_zero, WithZero.exp_le_exp, neg_nonpos, padicValRat_def]
  constructor
  · intro hcop
    have hnd : ¬ ℓ ∣ x.den := fun hd =>
      hℓ.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) hd)
    rw [padicValNat.eq_zero_of_not_dvd hnd]
    simp
  · intro hval
    by_contra hcop
    have hd : ℓ ∣ x.den := by
      by_contra hnd
      exact hcop ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hnd).symm

    have hnum : ¬ (ℓ : ℤ) ∣ x.num := by
      intro hn
      have h1 : ℓ ∣ x.num.natAbs := Int.natCast_dvd.mp (by simpa using hn)
      have h2 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 x.reduced) hd
      exact hℓ.one_lt.ne' h2
    rw [padicValInt.eq_zero_of_not_dvd hnum] at hval
    have h3 : 1 ≤ padicValNat ℓ x.den :=
      one_le_padicValNat_of_dvd x.den_ne_zero hd
    have h4 : ((padicValNat ℓ x.den : ℕ) : ℤ) ≤ 0 := by
      simpa using hval
    omega

theorem mem_ratLocalizedAt_of_isIntegral {x : ℚ}
    (hx : IsIntegral ↥(GaloisRep.ratLocalizedAt ℓ) x) : x ∈ GaloisRep.ratLocalizedAt ℓ := by
  rw [mem_ratLocalizedAt_iff]
  have hle : (GaloisRep.ratLocalizedAt ℓ) ≤ (Rat.padicValuation ℓ).integer :=
    fun y hy => (mem_ratLocalizedAt_iff ℓ y).mp hy
  have hx' : IsIntegral ↥(Rat.padicValuation ℓ).integer x :=
    hx.map_of_comp_eq (Subring.inclusion hle) (RingHom.id ℚ) (by ext; rfl)
  exact (Valuation.integer.integers (Rat.padicValuation ℓ)).mem_of_integral hx'

end Zl

section Bivariate

variable {M ℓ : ℕ} [NeZero M] [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull M) : Type)
set_option quotPrecheck false in
local notation "ℤℓ" => (↥(GaloisRep.ratLocalizedAt ℓ) : Type)

theorem algebraMap_Zl_apply (c : ℤℓ) :
    algebraMap ℤℓ F c = algebraMap ℚ F (c : ℚ) := rfl

theorem coe_algebraMap_rat (q : ℚ) :
    ((algebraMap ℚ F q : F) : LaurentSeries ℚ) = HahnSeries.C q := by
  simp

theorem algebraMap_comp_aeval_adjoin (s : F) :
    (algebraMap ↥(Algebra.adjoin ℤℓ ({s} : Set F)) F).comp
        (aeval (⟨s, Algebra.subset_adjoin rfl⟩ : ↥(Algebra.adjoin ℤℓ ({s} : Set F)))).toRingHom
      = (aeval (R := ℤℓ) s).toRingHom := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C]
    rfl
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
    rfl

theorem isIntegral_adjoin_of_bivariate {s b : F} (P : Polynomial (Polynomial ℤℓ)) (hm : P.Monic)
    (h0 : P.eval₂ (aeval (R := ℤℓ) s).toRingHom b = 0) :
    IsIntegral ↥(Algebra.adjoin ℤℓ ({s} : Set F)) b := by
  refine ⟨P.map (aeval (⟨s, Algebra.subset_adjoin rfl⟩ :
    ↥(Algebra.adjoin ℤℓ ({s} : Set F)))).toRingHom, hm.map _, ?_⟩
  rw [eval₂_map, algebraMap_comp_aeval_adjoin, h0]

theorem exists_bivariate_of_isIntegral_adjoin {s b : F}
    (h : IsIntegral ↥(Algebra.adjoin ℤℓ ({s} : Set F)) b) :
    ∃ P : Polynomial (Polynomial ℤℓ), P.Monic ∧ P.eval₂ (aeval (R := ℤℓ) s).toRingHom b = 0 := by
  obtain ⟨Q, hQm, hQ⟩ := h
  set Q' : Polynomial F := Q.map (algebraMap ↥(Algebra.adjoin ℤℓ ({s} : Set F)) F) with hQ'
  have hQ'm : Q'.Monic := hQm.map _
  have hlifts : Q' ∈ Polynomial.lifts (aeval (R := ℤℓ) s).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hQ', Polynomial.coeff_map]
    have hmem : ((Q.coeff n : ↥(Algebra.adjoin ℤℓ ({s} : Set F))) : F) ∈ (aeval (R := ℤℓ) s).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (Q.coeff n).2
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq⟩
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hQ'm
  refine ⟨P, hPm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hPmap, hQ', Polynomial.eval_map, hQ]

theorem isIntegral_adjoin_map (σ : F ≃ₐ[ℚ] F) {s b : F}
    (h : IsIntegral ↥(Algebra.adjoin ℤℓ ({s} : Set F)) b) :
    IsIntegral ↥(Algebra.adjoin ℤℓ ({σ s} : Set F)) (σ b) := by
  obtain ⟨P, hPm, hP⟩ := exists_bivariate_of_isIntegral_adjoin h
  refine isIntegral_adjoin_of_bivariate P hPm ?_
  have hcomp : ((σ : F ≃ₐ[ℚ] F) : F →+* F).comp (aeval (R := ℤℓ) s).toRingHom = (aeval (R := ℤℓ) (σ s)).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, aeval_C,
        RingHom.coe_coe, algebraMap_Zl_apply, AlgEquiv.commutes]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, aeval_X,
        RingHom.coe_coe]
  have h1 := Polynomial.hom_eval₂ P (aeval (R := ℤℓ) s).toRingHom ((σ : F ≃ₐ[ℚ] F) : F →+* F) b
  rw [hP, map_zero, hcomp] at h1
  exact h1.symm

def constO : ℤℓ →+* ↥𝒪 :=
  ((algebraMap ℚ (LaurentSeries ℚ)).comp (GaloisRep.ratLocalizedAt ℓ).subtype).codRestrict 𝒪
    (fun c => by
      rw [RingHom.comp_apply, algebraMap_laurentSeries_eq_single, ← HahnSeries.C_apply]
      exact C_mem_𝒪 _)

@[scoped simp] theorem coe_constO (c : ℤℓ) :
    ((constO c : ↥𝒪) : LaurentSeries ℚ) = HahnSeries.C (c : ℚ) := by
  change algebraMap ℚ (LaurentSeries ℚ) (c : ℚ) = _
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]

theorem coe_mem_𝒪_and_coeff_zero_mem {s b : F} (hs : ((s : F) : LaurentSeries ℚ) ∈ 𝒪)
    (hs0 : ((s : F) : LaurentSeries ℚ).coeff 0 = 0)
    (hb : IsIntegral ↥(Algebra.adjoin ℤℓ ({s} : Set F)) b) :
    ((b : F) : LaurentSeries ℚ) ∈ 𝒪 ∧
      ((b : F) : LaurentSeries ℚ).coeff 0 ∈ GaloisRep.ratLocalizedAt ℓ := by
  obtain ⟨P, hPm, hP⟩ := exists_bivariate_of_isIntegral_adjoin hb

  set κ : Polynomial ℤℓ →+* ↥𝒪 := eval₂RingHom (constO (ℓ := ℓ)) ⟨_, hs⟩ with hκ
  set ιF : F →+* LaurentSeries ℚ := (modularFunctionFieldFull M).toSubalgebra.val.toRingHom
    with hιF
  have hιF_apply : ∀ x : F, ιF x = (x : LaurentSeries ℚ) := fun x => rfl
  have hcompat : (𝒪.subtype).comp κ = ιF.comp (aeval (R := ℤℓ) s).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, RingHom.comp_apply, hκ, coe_eval₂RingHom, eval₂_C, Subring.subtype_apply,
        coe_constO, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, hιF_apply,
        algebraMap_Zl_apply, coe_algebraMap_rat]
    · rw [RingHom.comp_apply, RingHom.comp_apply, hκ, coe_eval₂RingHom, eval₂_X, Subring.subtype_apply,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X, hιF_apply]

  have hroot : eval₂ (algebraMap ↥𝒪 (LaurentSeries ℚ)) ((b : F) : LaurentSeries ℚ) (P.map κ) = 0 := by
    rw [eval₂_map, show algebraMap ↥𝒪 (LaurentSeries ℚ) = 𝒪.subtype from rfl, hcompat,
      ← hιF_apply b, ← Polynomial.hom_eval₂, hP, map_zero]
  have hbO : ((b : F) : LaurentSeries ℚ) ∈ 𝒪 :=
    (Valuation.integer.integers (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰)).mem_of_integral
      ⟨P.map κ, hPm.map κ, hroot⟩
  refine ⟨hbO, ?_⟩

  set b' : ↥𝒪 := ⟨_, hbO⟩ with hb'
  have hroot' : P.eval₂ κ b' = 0 := by
    apply Subtype.ext
    change 𝒪.subtype (P.eval₂ κ b') = 0
    rw [Polynomial.hom_eval₂, hcompat, show 𝒪.subtype b' = ιF b from rfl, ← Polynomial.hom_eval₂,
      hP, map_zero]
  have hcompat' : (algebraMap ℤℓ ℚ).comp (evalRingHom 0) = ρ.comp κ := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, RingHom.comp_apply, coe_evalRingHom, eval_C, hκ, coe_eval₂RingHom, eval₂_C,
        ρ_apply, coe_constO, HahnSeries.C_apply, HahnSeries.coeff_single_same]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, coe_evalRingHom, eval_X, hκ, coe_eval₂RingHom, eval₂_X,
        ρ_apply, map_zero]
      exact hs0.symm
  have hint : IsIntegral ℤℓ (((b : F) : LaurentSeries ℚ).coeff 0) := by
    refine ⟨P.map (evalRingHom 0), hPm.map _, ?_⟩
    rw [eval₂_map, hcompat', show ((b : F) : LaurentSeries ℚ).coeff 0 = ρ b' from rfl,
      ← Polynomial.hom_eval₂, hroot', map_zero]
  exact mem_ratLocalizedAt_of_isIntegral ℓ hint

end Bivariate

section OUnits

theorem inv_mem_𝒪_and_coeff {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) (h0 : f.coeff 0 ≠ 0) :
    f⁻¹ ∈ 𝒪 ∧ f⁻¹.coeff 0 = (f.coeff 0)⁻¹ := by
  obtain ⟨Φ, hΦ⟩ := exists_powerSeries_of_mem_𝒪 hf
  have hc : PowerSeries.constantCoeff Φ ≠ 0 := by
    rwa [← coeff_zero_coe_powerSeries, hΦ]
  have hinv : f⁻¹ = ((Φ⁻¹ : PowerSeries ℚ) : LaurentSeries ℚ) := by
    have hf0 : f ≠ 0 := fun h => h0 (by rw [h, HahnSeries.coeff_zero])
    apply mul_left_cancel₀ hf0
    rw [mul_inv_cancel₀ hf0, ← hΦ, ← map_mul, PowerSeries.mul_inv_cancel Φ hc, map_one]
  refine ⟨by rw [hinv]; exact coe_powerSeries_mem_𝒪 _, ?_⟩
  rw [hinv, coeff_zero_coe_powerSeries, PowerSeries.constantCoeff_inv, ← hΦ,
    coeff_zero_coe_powerSeries]

def 𝔮 : LaurentSeries ℚ := HahnSeries.single (1 : ℤ) 1

theorem 𝔮_pow (n : ℕ) : 𝔮 ^ n = HahnSeries.single (n : ℤ) (1 : ℚ) := by
  rw [𝔮, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]

theorem 𝔮_pow_mem_𝒪 (n : ℕ) : 𝔮 ^ n ∈ 𝒪 := by
  rw [𝔮_pow, ← mul_one (HahnSeries.single (n : ℤ) (1 : ℚ))]
  exact single_mul_mem_𝒪 (Subring.one_mem _) (by positivity)

theorem coeff_zero_𝔮_pow_mul {n : ℕ} (hn : 0 < n) {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) :
    (𝔮 ^ n * f).coeff 0 = 0 := by
  rw [𝔮_pow]; exact coeff_zero_single_mul_of_mem_𝒪 hf (by exact_mod_cast hn)

theorem 𝔮_pow_mul_mem_𝒪 (n : ℕ) {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) : 𝔮 ^ n * f ∈ 𝒪 :=
  Subring.mul_mem _ (𝔮_pow_mem_𝒪 n) hf

theorem 𝔮_ne_zero : 𝔮 ≠ 0 := by
  rw [𝔮]; exact HahnSeries.single_ne_zero one_ne_zero

theorem 𝔮_mul_jq : 𝔮 * jq = ((jNumQ : PowerSeries ℚ) : LaurentSeries ℚ) := by
  rw [𝔮, jq, ← mul_assoc, HahnSeries.single_mul_single, one_mul,
    show (1 : ℤ) + -1 = 0 by norm_num, HahnSeries.single_zero_one, one_mul]

theorem 𝔮_mul_jq_mem_𝒪 : 𝔮 * jq ∈ 𝒪 := by rw [𝔮_mul_jq]; exact coe_powerSeries_mem_𝒪 _

theorem coeff_zero_𝔮_mul_jq : (𝔮 * jq).coeff 0 = 1 := by
  rw [𝔮_mul_jq, coeff_zero_coe_powerSeries, constantCoeff_jNumQ]

variable (p : ℕ) [Fact p.Prime]

scoped instance instNeZeroP : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem 𝔮_pow_mul_jp : 𝔮 ^ p * qExpand ℚ p jq = qExpand ℚ p (𝔮 * jq) := by
  rw [map_mul, 𝔮_pow, 𝔮, qExpand_single, mul_one]

theorem qExpand_mem_𝒪 {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) : qExpand ℚ p f ∈ 𝒪 := by
  rw [mem_𝒪_iff] at hf ⊢
  intro n hn
  by_cases hdvd : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    apply hf
    have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    by_contra hk
    push Not at hk
    exact absurd hn (not_lt.mpr (mul_nonneg hp.le hk))
  · exact qExpand_coeff_of_not_dvd (R := ℚ) p f hdvd

theorem coeff_zero_qExpand (f : LaurentSeries ℚ) : (qExpand ℚ p f).coeff 0 = f.coeff 0 := by
  have h := qExpand_coeff_mul (R := ℚ) p f 0
  rwa [mul_zero] at h

theorem E_mem_𝒪 : 𝔮 ^ p * qExpand ℚ p jq ∈ 𝒪 := by
  rw [𝔮_pow_mul_jp]; exact qExpand_mem_𝒪 p 𝔮_mul_jq_mem_𝒪

theorem coeff_zero_E : (𝔮 ^ p * qExpand ℚ p jq).coeff 0 = 1 := by
  rw [𝔮_pow_mul_jp, coeff_zero_qExpand, coeff_zero_𝔮_mul_jq]

theorem jp_ne_zero : qExpand ℚ p jq ≠ 0 := fun h =>
  jq_ne_zero (qExpand_injective (R := ℚ) (N := p) (by rw [h, map_zero]))

theorem jq_inv_eq : jq⁻¹ = 𝔮 ^ 1 * (𝔮 * jq)⁻¹ := by
  rw [pow_one, mul_inv, ← mul_assoc, mul_inv_cancel₀ 𝔮_ne_zero, one_mul]

theorem jq_inv_mem_𝒪_and_coeff : jq⁻¹ ∈ 𝒪 ∧ jq⁻¹.coeff 0 = 0 := by
  have h := inv_mem_𝒪_and_coeff 𝔮_mul_jq_mem_𝒪 (by rw [coeff_zero_𝔮_mul_jq]; exact one_ne_zero)
  rw [jq_inv_eq]
  exact ⟨𝔮_pow_mul_mem_𝒪 1 h.1, coeff_zero_𝔮_pow_mul one_pos h.1⟩

theorem jp_inv_eq : (qExpand ℚ p jq)⁻¹ = 𝔮 ^ p * (𝔮 ^ p * qExpand ℚ p jq)⁻¹ := by
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ 𝔮_ne_zero), one_mul]

theorem jp_inv_mem_𝒪_and_coeff : (qExpand ℚ p jq)⁻¹ ∈ 𝒪 ∧ (qExpand ℚ p jq)⁻¹.coeff 0 = 0 := by
  have h := inv_mem_𝒪_and_coeff (E_mem_𝒪 p) (by rw [coeff_zero_E]; exact one_ne_zero)
  rw [jp_inv_eq]
  exact ⟨𝔮_pow_mul_mem_𝒪 p h.1, coeff_zero_𝔮_pow_mul (Fact.out : p.Prime).pos h.1⟩

theorem t_series_eq : qExpand ℚ p jq * (jq⁻¹) ^ p
    = (𝔮 ^ p * qExpand ℚ p jq) * ((𝔮 * jq) ^ p)⁻¹ := by
  rw [mul_pow, mul_inv, inv_pow]
  have h𝔮 : (𝔮 : LaurentSeries ℚ) ^ p ≠ 0 := pow_ne_zero _ 𝔮_ne_zero
  field_simp

theorem t_series_mem_𝒪_and_coeff :
    qExpand ℚ p jq * (jq⁻¹) ^ p ∈ 𝒪 ∧ (qExpand ℚ p jq * (jq⁻¹) ^ p).coeff 0 = 1 := by
  have hA : (𝔮 * jq) ^ p ∈ 𝒪 := Subring.pow_mem _ 𝔮_mul_jq_mem_𝒪 p
  have hA0 : ((𝔮 * jq) ^ p).coeff 0 = 1 := by
    have := map_pow ρ ⟨_, 𝔮_mul_jq_mem_𝒪⟩ p
    simp only [ρ_apply, SubmonoidClass.mk_pow, coeff_zero_𝔮_mul_jq, one_pow] at this
    exact this
  have hAi := inv_mem_𝒪_and_coeff hA (by rw [hA0]; exact one_ne_zero)
  rw [t_series_eq]
  refine ⟨Subring.mul_mem _ (E_mem_𝒪 p) hAi.1, ?_⟩
  have := map_mul ρ ⟨_, E_mem_𝒪 p⟩ ⟨_, hAi.1⟩
  simp only [ρ_apply, MulMemClass.mk_mul_mk, coeff_zero_E, hAi.2, hA0, inv_one, mul_one] at this
  exact this

theorem wt_series_eq : jq * ((qExpand ℚ p jq)⁻¹) ^ p
    = 𝔮 ^ (p ^ 2 - 1) * ((𝔮 * jq) * ((𝔮 ^ p * qExpand ℚ p jq) ^ p)⁻¹) := by
  have h𝔮 : (𝔮 : LaurentSeries ℚ) ≠ 0 := 𝔮_ne_zero
  have hjp := jp_ne_zero p
  have hp2 : p ^ 2 - 1 + 1 = p * p := by
    have := (Fact.out : p.Prime).one_lt
    have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [Nat.sub_add_cancel h1, pow_two]
  have hpow : (𝔮 : LaurentSeries ℚ) ^ (p ^ 2 - 1) * 𝔮 = (𝔮 ^ p) ^ p := by
    rw [← pow_succ, hp2, pow_mul]
  rw [mul_pow, mul_inv, inv_pow]
  field_simp
  rw [mul_assoc, hpow]

theorem wt_series_mem_𝒪_and_coeff :
    jq * ((qExpand ℚ p jq)⁻¹) ^ p ∈ 𝒪 ∧ (jq * ((qExpand ℚ p jq)⁻¹) ^ p).coeff 0 = 0 := by
  have hEp : (𝔮 ^ p * qExpand ℚ p jq) ^ p ∈ 𝒪 := Subring.pow_mem _ (E_mem_𝒪 p) p
  have hEp0 : ((𝔮 ^ p * qExpand ℚ p jq) ^ p).coeff 0 = 1 := by
    have := map_pow ρ ⟨_, E_mem_𝒪 p⟩ p
    simp only [ρ_apply, SubmonoidClass.mk_pow, coeff_zero_E, one_pow] at this
    exact this
  have hEi := inv_mem_𝒪_and_coeff hEp (by rw [hEp0]; exact one_ne_zero)
  have hin : (𝔮 * jq) * ((𝔮 ^ p * qExpand ℚ p jq) ^ p)⁻¹ ∈ 𝒪 :=
    Subring.mul_mem _ 𝔮_mul_jq_mem_𝒪 hEi.1
  have hpos : 0 < p ^ 2 - 1 := by
    have := (Fact.out : p.Prime).one_lt
    have : 2 * 2 ≤ p ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul this this
    omega
  rw [wt_series_eq]
  exact ⟨𝔮_pow_mul_mem_𝒪 _ hin, coeff_zero_𝔮_pow_mul hpos hin⟩

end OUnits

section HPoly

def dcoef (p : ℕ) (Φ : Polynomial (Polynomial ℤ)) (a b : ℕ) : ℤ :=
  ((Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p)).coeff b).coeff a

def Mx (p : ℕ) : ℕ := p ^ 2 + p

def hPoly (p : ℕ) (Φ : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℤ) :=
  X ^ (p + 1) - X ^ p +
    ∑ b ∈ Finset.range (p + 1), ∑ a ∈ Finset.range (Mx p),
      C (C (dcoef p Φ a b) * X ^ (Mx p - a - p * b)) * X ^ b

theorem dcoef_bound {p : ℕ} [Fact p.Prime] (data : ModularPolynomialData p) {a b : ℕ}
    (h : dcoef p data.Φ a b ≠ 0) :
    a + p * b + 1 ≤ Mx p := by
  have h1 := (ModularCurve.ModularPolynomialData.weighted_support_le p data).1 b a h
  have hp := (Fact.out : p.Prime).one_lt
  rw [Mx]
  have h2 : 1 ≤ p ^ 2 + p := by nlinarith
  omega

theorem hPoly_monic (p : ℕ) (Φ : Polynomial (Polynomial ℤ)) : (hPoly p Φ).Monic := by
  rw [hPoly, sub_add_eq_add_sub, add_sub_assoc]
  apply monic_X_pow_add
  have hdeg : ∀ q : Polynomial (Polynomial ℤ), q.degree ≤ p → q.degree < ((p + 1 : ℕ) : WithBot ℕ) :=
    fun q hq => lt_of_le_of_lt hq (by exact_mod_cast Nat.lt_succ_self p)
  apply hdeg
  refine (degree_sub_le _ _).trans (max_le ?_ (degree_X_pow_le p))
  refine (degree_sum_le _ _).trans (Finset.sup_le fun b hb => ?_)
  refine (degree_sum_le _ _).trans (Finset.sup_le fun a ha => ?_)
  refine (degree_C_mul_X_pow_le _ _).trans ?_
  exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)

theorem hPoly_map_evalRingHom_zero {p : ℕ} [Fact p.Prime] (data : ModularPolynomialData p) :
    (hPoly p data.Φ).map (evalRingHom 0) = X ^ (p + 1) - X ^ p := by
  rw [hPoly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_pow, map_X,
    add_eq_left, Polynomial.map_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  rw [Polynomial.map_sum]
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, coe_evalRingHom, eval_mul, eval_C,
    eval_pow, eval_X]
  by_cases hd : dcoef p data.Φ a b = 0
  · rw [hd, zero_mul, C_0, zero_mul]
  · have hle := dcoef_bound data hd
    have hpos : Mx p - a - p * b ≠ 0 := by omega
    rw [zero_pow hpos, mul_zero, C_0, zero_mul]

end HPoly

section ModEq

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull (N * p)) : Type)

def jF : F := jFull (N * p)

def jpF : F := ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩

def uF : F := (jFull (N * p))⁻¹

def tF : F := jpF N p * uF N p ^ p

@[scoped simp] theorem coe_jF : ((jF N p : F) : LaurentSeries ℚ) = jq := rfl
@[scoped simp] theorem coe_jpF : ((jpF N p : F) : LaurentSeries ℚ) = qExpand ℚ p jq := rfl
@[scoped simp] theorem coe_uF : ((uF N p : F) : LaurentSeries ℚ) = jq⁻¹ := by
  rw [uF, IntermediateField.coe_inv, coe_jFull]
@[scoped simp] theorem coe_tF : ((tF N p : F) : LaurentSeries ℚ) = qExpand ℚ p jq * (jq⁻¹) ^ p := by
  rw [tF, IntermediateField.coe_mul, IntermediateField.coe_pow, coe_jpF, coe_uF]

theorem jF_ne_zero : jF N p ≠ 0 := jFull_ne_zero (N * p)
theorem uF_ne_zero : uF N p ≠ 0 := inv_ne_zero (jFull_ne_zero (N * p))
theorem jpF_ne_zero : jpF N p ≠ 0 := fun h =>
  jp_ne_zero p (by simpa using congrArg (fun z : F => (z : LaurentSeries ℚ)) h)
theorem uF_mul_jF : uF N p * jF N p = 1 := inv_mul_cancel₀ (jFull_ne_zero (N * p))
theorem uF_eq_inv : uF N p = (jF N p)⁻¹ := rfl

def ιF : F →+* LaurentSeries ℚ := (modularFunctionFieldFull (N * p)).toSubalgebra.val.toRingHom

@[scoped simp] theorem ιF_apply (x : F) : ιF N p x = (x : LaurentSeries ℚ) := rfl

theorem ιF_injective : Function.Injective (ιF N p) := Subtype.coe_injective

theorem modularEquation (data : ModularPolynomialData p) :
    data.Φ.eval₂ (eval₂RingHom (algebraMap ℤ F) (jF N p)) (jpF N p) = 0 := by
  apply ιF_injective N p
  rw [Polynomial.hom_eval₂, map_zero]
  have hcomp : (ιF N p).comp (eval₂RingHom (algebraMap ℤ F) (jF N p)) = evalAtJ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, ιF_apply, coe_jF, evalAtJ_X]
  rw [hcomp, ιF_apply, coe_jpF]
  exact data.eval_eq_zero

def θu : Polynomial ℤ →+* F := eval₂RingHom (algebraMap ℤ F) (uF N p)

def θj : Polynomial ℤ →+* F := eval₂RingHom (algebraMap ℤ F) (jF N p)

theorem monomial_twist {a b : ℕ} (hab : a + p * b ≤ Mx p) (d : ℤ) :
    uF N p ^ Mx p * (algebraMap ℤ F d * jF N p ^ a * jpF N p ^ b)
      = algebraMap ℤ F d * uF N p ^ (Mx p - a - p * b) * tF N p ^ b := by
  have hu : uF N p ≠ 0 := uF_ne_zero N p
  have hsplit : uF N p ^ Mx p = uF N p ^ (Mx p - a - p * b) * uF N p ^ (p * b) * uF N p ^ a := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [hsplit, tF, mul_pow, ← pow_mul]
  have hua : uF N p ^ a * jF N p ^ a = 1 := by rw [← mul_pow, uF_mul_jF, one_pow]
  calc uF N p ^ (Mx p - a - p * b) * uF N p ^ (p * b) * uF N p ^ a *
        (algebraMap ℤ F d * jF N p ^ a * jpF N p ^ b)
      = algebraMap ℤ F d * uF N p ^ (Mx p - a - p * b) * (jpF N p ^ b * uF N p ^ (p * b))
          * (uF N p ^ a * jF N p ^ a) := by ring
    _ = _ := by rw [hua, mul_one]

theorem hPoly_eval (data : ModularPolynomialData p) :
    (hPoly p data.Φ).eval₂ (θu N p) (tF N p) = 0 := by
  have hu : uF N p ≠ 0 := uF_ne_zero N p
  set D : Polynomial (Polynomial ℤ) := data.Φ - (X ^ (p + 1) - C (X ^ p) * X ^ p) with hD
  have hΦ : data.Φ = X ^ (p + 1) - C (X ^ p) * X ^ p + D := by rw [hD]; ring

  have hmod := modularEquation N p data
  rw [hΦ, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    coe_eval₂RingHom, eval₂_pow, eval₂_X] at hmod

  have hDsum : D.eval₂ (eval₂RingHom (algebraMap ℤ F) (jF N p)) (jpF N p)
      = ∑ b ∈ D.support, ∑ a ∈ (D.coeff b).support,
          algebraMap ℤ F (dcoef p data.Φ a b) * jF N p ^ a * jpF N p ^ b := by
    rw [eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hD, dcoef]

  have hkey : uF N p ^ Mx p * (jpF N p ^ (p + 1) - jF N p ^ p * jpF N p ^ p
      + D.eval₂ (eval₂RingHom (algebraMap ℤ F) (jF N p)) (jpF N p)) = 0 := by
    rw [hmod, mul_zero]
  rw [mul_add, mul_sub, hDsum, Finset.mul_sum] at hkey

  have h1 : uF N p ^ Mx p * jpF N p ^ (p + 1) = tF N p ^ (p + 1) := by
    have := monomial_twist N p (a := 0) (b := p + 1) (by rw [Mx]; ring_nf; exact le_rfl) 1
    rw [map_one, one_mul, pow_zero, one_mul, one_mul,
      show Mx p - 0 - p * (p + 1) = 0 by rw [Mx]; ring_nf; omega, pow_zero, one_mul] at this
    exact this
  have h2 : uF N p ^ Mx p * (jF N p ^ p * jpF N p ^ p) = tF N p ^ p := by
    have := monomial_twist N p (a := p) (b := p) (by rw [Mx]; ring_nf; exact le_rfl) 1
    rw [map_one, one_mul, one_mul,
      show Mx p - p - p * p = 0 by rw [Mx]; ring_nf; omega, pow_zero, one_mul] at this
    exact this
  have h3 : ∀ b ∈ D.support, uF N p ^ Mx p * ∑ a ∈ (D.coeff b).support,
        algebraMap ℤ F (dcoef p data.Φ a b) * jF N p ^ a * jpF N p ^ b
      = ∑ a ∈ (D.coeff b).support,
        algebraMap ℤ F (dcoef p data.Φ a b) * uF N p ^ (Mx p - a - p * b) * tF N p ^ b := by
    intro b hb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hd : dcoef p data.Φ a b ≠ 0 := by
      rw [dcoef, ← hD]; exact Polynomial.mem_support_iff.mp ha
    exact monomial_twist N p (by have := dcoef_bound data hd; omega) _
  rw [h1, h2, Finset.sum_congr rfl h3] at hkey

  rw [hPoly, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_pow, eval₂_X, eval₂_finsetSum]
  simp only [eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  have hθ : ∀ a b, θu N p (C (dcoef p data.Φ a b) * X ^ (Mx p - a - p * b))
      = algebraMap ℤ F (dcoef p data.Φ a b) * uF N p ^ (Mx p - a - p * b) := by
    intro a b
    rw [θu, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  simp only [hθ]

  rw [← hkey]
  congr 1
  symm
  have hinner : ∀ b, ∑ a ∈ (D.coeff b).support,
        algebraMap ℤ F (dcoef p data.Φ a b) * uF N p ^ (Mx p - a - p * b) * tF N p ^ b
      = ∑ a ∈ Finset.range (Mx p),
        algebraMap ℤ F (dcoef p data.Φ a b) * uF N p ^ (Mx p - a - p * b) * tF N p ^ b := by
    intro b
    apply Finset.sum_subset
    · intro a ha
      rw [Finset.mem_range]
      have hd : dcoef p data.Φ a b ≠ 0 := by
        rw [dcoef, ← hD]; exact Polynomial.mem_support_iff.mp ha
      have := dcoef_bound data hd
      omega
    · intro a _ ha
      have hzero : dcoef p data.Φ a b = 0 := by
        rw [dcoef, ← hD]; simpa using ha
      rw [hzero, map_zero, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun b _ => hinner b)]
  apply Finset.sum_subset
  · intro b hb
    rw [Finset.mem_range]
    obtain ⟨a, ha⟩ : ∃ a, (D.coeff b).coeff a ≠ 0 := by
      by_contra hall
      push Not at hall
      exact (Polynomial.mem_support_iff.mp hb) (Polynomial.ext fun a => by simpa using hall a)
    have hd : dcoef p data.Φ a b ≠ 0 := by rw [dcoef, ← hD]; exact ha
    have := dcoef_bound data hd
    have hp := (Fact.out : p.Prime).one_lt
    rw [Mx] at this
    nlinarith
  · intro b _ hb
    have hzero : D.coeff b = 0 := by simpa using hb
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [show dcoef p data.Φ a b = 0 by rw [dcoef, ← hD, hzero, coeff_zero], map_zero, zero_mul,
      zero_mul]

end ModEq

section Charts

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull (N * p)) : Type)
set_option quotPrecheck false in
local notation "ℤp" => (↥(GaloisRep.ratLocalizedAt p) : Type)
local notation "w" => atkinLehnerInvolutionFull N p

theorem tF_mem_chartAlgInf : tF N p ∈ chartAlgInf (N * p) p := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  rw [mem_chartAlg_iff]
  refine isIntegral_adjoin_of_bivariate ((hPoly p data.Φ).map (mapRingHom (Int.castRingHom ℤp)))
    ((hPoly_monic p data.Φ).map _) ?_
  rw [eval₂_map]
  have hcomp : (aeval (R := ℤp) ((jFull (N * p))⁻¹ : F)).toRingHom.comp (mapRingHom (Int.castRingHom ℤp))
      = θu N p := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, coe_mapRingHom, map_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      aeval_X, θu, coe_eval₂RingHom, eval₂_X]
    rfl
  rw [hcomp]
  exact hPoly_eval N p data

theorem atkinLehner_swap (hpN : ¬ p ∣ N) : w (jF N p) = jpF N p ∧ w (jpF N p) = jF N p := by
  have hσ : IsAtkinLehnerAutFull N p (atkinLehnerInvolutionFull N p) :=
    isAtkinLehnerAutFull_atkinLehnerInvolutionFull N p
      (ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N p Fact.out hpN)
  obtain ⟨h1, h2⟩ := hσ 1 inferInstance (one_dvd N)
  have hjF : jF N p = ⟨qExpand ℚ 1 jq, jqd_mem_full (N * p) (Dvd.dvd.mul_right (one_dvd N) p)⟩ :=
    Subtype.ext (by change jq = qExpand ℚ 1 jq; rw [qExpand_one_apply])
  have hjpF : jpF N p =
      ⟨qExpand ℚ (1 * p) jq, jqd_mem_full (N * p) (Nat.mul_dvd_mul_right (one_dvd N) p)⟩ :=
    Subtype.ext (by change qExpand ℚ p jq = qExpand ℚ (1 * p) jq; rw [qExpand_congr (one_mul p)])
  rw [hjF, hjpF]
  exact ⟨h1, h2⟩

theorem w_uF (hpN : ¬ p ∣ N) : w (uF N p) = (jpF N p)⁻¹ := by
  rw [uF_eq_inv, map_inv₀, (atkinLehner_swap N p hpN).1]

theorem w_tF (hpN : ¬ p ∣ N) : w (tF N p) = jF N p * ((jpF N p)⁻¹) ^ p := by
  rw [tF, map_mul, map_pow, w_uF N p hpN, (atkinLehner_swap N p hpN).2]

theorem coe_w_uF (hpN : ¬ p ∣ N) : ((w (uF N p) : F) : LaurentSeries ℚ) = (qExpand ℚ p jq)⁻¹ := by
  rw [w_uF N p hpN, IntermediateField.coe_inv, coe_jpF]

theorem coe_w_tF (hpN : ¬ p ∣ N) :
    ((w (tF N p) : F) : LaurentSeries ℚ) = jq * ((qExpand ℚ p jq)⁻¹) ^ p := by
  rw [w_tF N p hpN, IntermediateField.coe_mul, IntermediateField.coe_pow, IntermediateField.coe_inv,
    coe_jF, coe_jpF]

theorem cuspInf (b : ↥(chartAlgInf (N * p) p)) :
    ((b : F) : LaurentSeries ℚ) ∈ 𝒪 ∧ ((b : F) : LaurentSeries ℚ).coeff 0 ∈ GaloisRep.ratLocalizedAt p := by
  have hu := jq_inv_mem_𝒪_and_coeff
  exact coe_mem_𝒪_and_coeff_zero_mem (s := uF N p) (by rw [coe_uF]; exact hu.1)
    (by rw [coe_uF]; exact hu.2) ((mem_chartAlg_iff (N * p) p).mp b.2)

theorem cuspZero (hpN : ¬ p ∣ N) (b : ↥(chartAlgInf (N * p) p)) :
    ((w (b : F) : F) : LaurentSeries ℚ) ∈ 𝒪 ∧
      ((w (b : F) : F) : LaurentSeries ℚ).coeff 0 ∈ GaloisRep.ratLocalizedAt p := by
  have hu := jp_inv_mem_𝒪_and_coeff p
  have hint : IsIntegral ↥(Algebra.adjoin ℤp ({w (uF N p)} : Set F)) (w (b : F)) :=
    isIntegral_adjoin_map (atkinLehnerInvolutionFull N p) ((mem_chartAlg_iff (N * p) p).mp b.2)
  exact coe_mem_𝒪_and_coeff_zero_mem (s := w (uF N p)) (by rw [coe_w_uF N p hpN]; exact hu.1)
    (by rw [coe_w_uF N p hpN]; exact hu.2) hint

def cuspRetraction (φ : F →ₐ[ℚ] F)
    (hφ : ∀ b : ↥(chartAlgInf (N * p) p), ((φ (b : F) : F) : LaurentSeries ℚ) ∈ 𝒪 ∧
      ((φ (b : F) : F) : LaurentSeries ℚ).coeff 0 ∈ GaloisRep.ratLocalizedAt p) :
    ↥(chartAlgInf (N * p) p) →ₐ[ℤp] ℤp where
  toFun b := ⟨((φ (b : F) : F) : LaurentSeries ℚ).coeff 0, (hφ b).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' b c := Subtype.ext (by
    have := map_mul ρ ⟨_, (hφ b).1⟩ ⟨_, (hφ c).1⟩
    simp only [ρ_apply, MulMemClass.mk_mul_mk] at this
    change ((φ ((b * c : ↥(chartAlgInf (N * p) p)) : F) : F) : LaurentSeries ℚ).coeff 0 = _
    rw [Subalgebra.coe_mul, map_mul, IntermediateField.coe_mul, this]
    rfl)
  map_zero' := Subtype.ext (by simp)
  map_add' b c := Subtype.ext (by
    change ((φ ((b + c : ↥(chartAlgInf (N * p) p)) : F) : F) : LaurentSeries ℚ).coeff 0 = _
    rw [Subalgebra.coe_add, map_add, IntermediateField.coe_add, HahnSeries.coeff_add]
    rfl)
  commutes' c := Subtype.ext (by
    change ((φ ((algebraMap ℤp ↥(chartAlgInf (N * p) p) c : ↥(chartAlgInf (N * p) p)) : F) : F) :
      LaurentSeries ℚ).coeff 0 = (c : ℚ)
    rw [Subalgebra.coe_algebraMap, algebraMap_Zl_apply, AlgHom.commutes, coe_algebraMap_rat,
      HahnSeries.C_apply, HahnSeries.coeff_single_same])

theorem cuspRetraction_apply (φ : F →ₐ[ℚ] F) (hφ) (b : ↥(chartAlgInf (N * p) p)) :
    ((cuspRetraction N p φ hφ b : ℤp) : ℚ) = ((φ (b : F) : F) : LaurentSeries ℚ).coeff 0 := rfl

end Charts

section Gauss

abbrev ιK (K : Type*) [CommRing K] : LaurentSeries ℤ →+* LaurentSeries K :=
  coeffMap (Int.castRingHom K)

variable (p : ℕ) [Fact p.Prime]

abbrev ϖ : LaurentSeries ℤ →+* LaurentSeries (ZMod p) := coeffMap (Int.castRingHom (ZMod p))

theorem ιK_injective (K : Type*) [CommRing K] [CharZero K] : Function.Injective (ιK K) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff n) h
  simp only [coeffMap_coeff, eq_intCast, Int.cast_inj] at h1
  exact h1

variable {p}

theorem ιK_ne_zero_of_ϖ {y : LaurentSeries ℤ} (hy : ϖ p y ≠ 0) : ιK ℚ y ≠ 0 := by
  intro h
  apply hy
  rw [show y = 0 from ιK_injective ℚ (by rw [h, map_zero]), map_zero]

variable {M : ℕ} [NeZero M]

set_option quotPrecheck false in
local notation "FM" => (↥(modularFunctionFieldFull M) : Type)

theorem mem_nonunits_of_presentation (W₀ : ValuationSubring FM)
    (hW₀ : ∀ f : FM, f ∈ W₀ ↔ ∃ x y : LaurentSeries ℤ, ϖ p y ≠ 0 ∧
      (f : LaurentSeries ℚ) * ιK ℚ y = ιK ℚ x)
    {f : FM} {x y : LaurentSeries ℤ} (hy : ϖ p y ≠ 0) (hx : ϖ p x = 0)
    (h : (f : LaurentSeries ℚ) * ιK ℚ y = ιK ℚ x) : f ∈ W₀.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  have hf : f ∈ W₀ := (hW₀ f).mpr ⟨x, y, hy, h⟩
  refine ⟨hf, (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_⟩
  by_cases hf0 : f = 0
  · apply not_isUnit_zero (M₀ := ↥W₀)
    have : (⟨f, hf⟩ : ↥W₀) = 0 := Subtype.ext hf0
    rwa [this] at hu

  obtain ⟨u, hu'⟩ := hu
  have hinvmem : f⁻¹ ∈ W₀ := by
    have hmul : ((↑u⁻¹ : ↥W₀) : FM) * f = 1 := by
      have := congrArg (fun z : ↥W₀ => (z : FM)) u.inv_mul
      simpa [hu'] using this
    rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _
  obtain ⟨x', y', hy', h'⟩ := (hW₀ f⁻¹).mp hinvmem

  have hf0' : (f : LaurentSeries ℚ) ≠ 0 := fun e => hf0 (Subtype.ext e)
  have hprod : ιK ℚ (y * y') = ιK ℚ (x * x') := by
    rw [map_mul, map_mul, ← h, ← h', IntermediateField.coe_inv]; field_simp
  have hprod' : y * y' = x * x' := ιK_injective ℚ hprod
  have h0 : ϖ p (y * y') = 0 := by rw [hprod', map_mul, hx, zero_mul]
  rw [map_mul] at h0
  exact mul_ne_zero hy hy' h0

theorem mem_nonunits_comap_iff (σ : FM ≃ₐ[ℚ] FM) (W₀ W₁ : ValuationSubring FM)
    (hW₁ : ∀ f : FM, f ∈ W₁ ↔ σ f ∈ W₀) (f : FM) :
    f ∈ W₁.nonunits ↔ σ f ∈ W₀.nonunits := by
  have key : ∀ (V : ValuationSubring FM) (g : FM), g ∈ V.nonunits ↔ g ∈ V ∧ (g = 0 ∨ g⁻¹ ∉ V) := by
    intro V g
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    constructor
    · rintro ⟨hg, hm⟩
      refine ⟨hg, ?_⟩
      by_cases hg0 : g = 0
      · exact Or.inl hg0
      · right
        intro hinv
        apply (IsLocalRing.mem_maximalIdeal _).mp hm
        exact ⟨⟨⟨g, hg⟩, ⟨g⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hg0),
          Subtype.ext (inv_mul_cancel₀ hg0)⟩, rfl⟩
    · rintro ⟨hg, hor⟩
      refine ⟨hg, (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_⟩
      rcases hor with h0 | hinv
      · apply not_isUnit_zero (M₀ := ↥V)
        have : (⟨g, hg⟩ : ↥V) = 0 := Subtype.ext h0
        rwa [this] at hu
      · obtain ⟨u, hu'⟩ := hu
        apply hinv
        have hmul : ((↑u⁻¹ : ↥V) : FM) * g = 1 := by
          have := congrArg (fun z : ↥V => (z : FM)) u.inv_mul
          simpa [hu'] using this
        rw [inv_eq_of_mul_eq_one_left hmul]; exact SetLike.coe_mem _
  rw [key, key, hW₁, hW₁, map_inv₀, EmbeddingLike.map_eq_zero_iff]

end Gauss

section Assembly

variable (N p : ℕ) [NeZero N] [Fact p.Prime]

set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull (N * p)) : Type)
set_option quotPrecheck false in
local notation "ℤp" => (↥(GaloisRep.ratLocalizedAt p) : Type)
local notation "w" => atkinLehnerInvolutionFull N p
local notation "J" => jqModC ℤ
local notation "Jp" => qExpand ℤ p (jqModC ℤ)

theorem coe_jF' : ((jF N p : F) : LaurentSeries ℚ) = ιK ℚ J := by
  rw [coe_jF, coeffMap_jqModC, jqModC_rat]

theorem coe_jpF' : ((jpF N p : F) : LaurentSeries ℚ) = ιK ℚ Jp := by
  rw [coe_jpF, coeffMap_qExpand, coeffMap_jqModC, jqModC_rat]

theorem ϖ_J_ne_zero : ϖ p J ≠ 0 := by
  rw [coeffMap_jqModC]; exact jqModC_ne_zero_of_nontrivial _

theorem ϖ_Jp_ne_zero : ϖ p Jp ≠ 0 := by
  rw [coeffMap_qExpand, coeffMap_jqModC]
  exact fun h => jqModC_ne_zero_of_nontrivial (ZMod p)
    (qExpand_injective (R := ZMod p) (N := p) (by rw [h, map_zero]))

theorem ϖ_Jp_sub_J_pow : ϖ p (Jp - J ^ p) = 0 := by
  rw [map_sub, map_pow, coeffMap_qExpand, coeffMap_jqModC,
    qExpand_jqModC_eq_pow_unconditional (ZMod p), sub_self]

theorem pres_t_sub_one :
    (((tF N p - 1 : F)) : LaurentSeries ℚ) * ιK ℚ (J ^ p) = ιK ℚ (Jp - J ^ p) := by
  have hj : ιK ℚ (J ^ p) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ (ιK_ne_zero_of_ϖ (ϖ_J_ne_zero p))
  have ht : tF N p = jpF N p / jF N p ^ p := by rw [tF, uF_eq_inv, inv_pow, div_eq_mul_inv]
  rw [ht, AddSubgroupClass.coe_sub, IntermediateField.coe_div, IntermediateField.coe_pow, coe_jpF', coe_jF',
    IntermediateField.coe_one, ← map_pow, map_sub, sub_mul, div_mul_cancel₀ _ hj, one_mul]

theorem pres_w_witness (hpN : ¬ p ∣ N) :
    ((w (tF N p ^ p - uF N p ^ (p ^ 2 - 1)) : F) : LaurentSeries ℚ) * ιK ℚ (Jp ^ (p ^ 2))
      = ιK ℚ (J ^ p - Jp) := by
  have hjp0 : jpF N p ≠ 0 := jpF_ne_zero N p
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos

  have hF : w (tF N p ^ p - uF N p ^ (p ^ 2 - 1)) * jpF N p ^ (p ^ 2) = jF N p ^ p - jpF N p := by
    rw [map_sub, map_pow, map_pow, w_tF N p hpN, w_uF N p hpN, mul_pow, ← pow_mul, ← pow_two, sub_mul,
      mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hjp0), mul_one, inv_pow]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast (jpF N p) (p ^ 2), ← zpow_neg, ← zpow_add₀ hjp0]
    rw [show -(((p ^ 2 - 1 : ℕ)) : ℤ) + ((p ^ 2 : ℕ) : ℤ) = 1 by push_cast [Nat.cast_sub hp1]; ring,
      zpow_one]
  have hcoe := congrArg (fun z : F => (z : LaurentSeries ℚ)) hF
  simp only [IntermediateField.coe_mul, IntermediateField.coe_pow, AddSubgroupClass.coe_sub, coe_jF',
    coe_jpF'] at hcoe
  rw [map_pow (ιK ℚ), map_sub (ιK ℚ), map_pow (ιK ℚ)]
  exact hcoe

theorem main (hpN : ¬ p ∣ N) :
    (∃ ε : Fin 2 → (↥(chartAlgInf (N * p) p) →ₐ[ℤp] ℤp),
      ∀ b : ↥(chartAlgInf (N * p) p),
        ((ε 0 b : ℤp) : ℚ) = ((b : F) : LaurentSeries ℚ).coeff 0 ∧
        ((ε 1 b : ℤp) : ℚ) = ((w (b : F) : F) : LaurentSeries ℚ).coeff 0) ∧
    (tF N p ∈ chartAlgInf (N * p) p ∧
      (∃ h : Polynomial (Polynomial ℤ), h.Monic ∧
        h.map (Polynomial.evalRingHom 0) = X ^ (p + 1) - X ^ p ∧
        h.eval₂ (Polynomial.eval₂RingHom (algebraMap ℤ F) (uF N p)) (tF N p) = 0) ∧
      ((tF N p : F) : LaurentSeries ℚ).coeff 0 = 1 ∧
      ((w (tF N p) : F) : LaurentSeries ℚ).coeff 0 = 0) ∧
    (∀ W₀ W₁ : ValuationSubring F,
      (∀ f : F, f ∈ W₀ ↔ ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x) →
      (∀ f : F, f ∈ W₁ ↔ w f ∈ W₀) →
      (tF N p - 1 ∈ W₀.nonunits ∧ ((w (tF N p - 1) : F) : LaurentSeries ℚ).coeff 0 = -1) ∧
      (tF N p ^ p - uF N p ^ (p ^ 2 - 1) ∈ W₁.nonunits ∧
        ((tF N p ^ p - uF N p ^ (p ^ 2 - 1) : F) : LaurentSeries ℚ).coeff 0 = 1)) := by
  have ht := t_series_mem_𝒪_and_coeff p
  have hwt := wt_series_mem_𝒪_and_coeff p
  have hu := jq_inv_mem_𝒪_and_coeff
  refine ⟨?_, ⟨tF_mem_chartAlgInf N p, ?_, ?_, ?_⟩, ?_⟩

  · let ε₀ := cuspRetraction N p (AlgHom.id ℚ F) (fun b => cuspInf N p b)
    let ε₁ := cuspRetraction N p (atkinLehnerInvolutionFull N p : F ≃ₐ[ℚ] F).toAlgHom
      (fun b => cuspZero N p hpN b)
    refine ⟨![ε₀, ε₁], fun b => ⟨rfl, rfl⟩⟩

  · obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
    exact ⟨hPoly p data.Φ, hPoly_monic p data.Φ, hPoly_map_evalRingHom_zero data, hPoly_eval N p data⟩

  · rw [coe_tF]; exact ht.2

  · rw [coe_w_tF N p hpN]; exact hwt.2

  · intro W₀ W₁ hW₀ hW₁
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact mem_nonunits_of_presentation W₀ hW₀ (by rw [map_pow]; exact pow_ne_zero _ (ϖ_J_ne_zero p))
        (ϖ_Jp_sub_J_pow p) (pres_t_sub_one N p)
    · have h1 := map_sub ρ ⟨_, by rw [← coe_w_tF N p hpN] at hwt; exact hwt.1⟩ 1
      rw [map_sub, map_one]
      simp only [ρ_apply, map_one] at h1
      rw [AddSubgroupClass.coe_sub, IntermediateField.coe_one]
      rw [← coe_w_tF N p hpN] at hwt
      have : (((w (tF N p) : F) : LaurentSeries ℚ) - 1).coeff 0 = ((w (tF N p) : F) : LaurentSeries ℚ).coeff 0 - 1 := by
        rw [HahnSeries.coeff_sub, HahnSeries.coeff_one, if_pos rfl]
      rw [this, hwt.2, zero_sub]
    · rw [mem_nonunits_comap_iff (atkinLehnerInvolutionFull N p) W₀ W₁ hW₁]
      exact mem_nonunits_of_presentation W₀ hW₀ (by rw [map_pow]; exact pow_ne_zero _ (ϖ_Jp_ne_zero p))
        (by rw [← neg_sub, map_neg, ϖ_Jp_sub_J_pow, neg_zero]) (pres_w_witness N p hpN)
    · have hmem_t : ((tF N p : F) : LaurentSeries ℚ) ∈ 𝒪 := by rw [coe_tF]; exact ht.1
      have hmem_u : ((uF N p : F) : LaurentSeries ℚ) ∈ 𝒪 := by rw [coe_uF]; exact hu.1
      have h1 := map_sub ρ (⟨_, hmem_t⟩ ^ p) (⟨_, hmem_u⟩ ^ (p ^ 2 - 1))
      rw [map_pow, map_pow] at h1
      simp only [ρ_apply, SubmonoidClass.mk_pow] at h1
      have hpos : p ^ 2 - 1 ≠ 0 := by
        have := (Fact.out : p.Prime).one_lt
        have : 2 * 2 ≤ p ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul this this
        omega
      rw [AddSubgroupClass.coe_sub, IntermediateField.coe_pow, IntermediateField.coe_pow]
      change ((((tF N p : F) : LaurentSeries ℚ) ^ p - ((uF N p : F) : LaurentSeries ℚ) ^ (p ^ 2 - 1))).coeff 0 = 1
      have h2 : ((↑((⟨((tF N p : F) : LaurentSeries ℚ) ^ p, Subring.pow_mem _ hmem_t _⟩ : ↥𝒪)
          - ⟨((uF N p : F) : LaurentSeries ℚ) ^ (p ^ 2 - 1), Subring.pow_mem _ hmem_u _⟩) : LaurentSeries ℚ))
          = ((tF N p : F) : LaurentSeries ℚ) ^ p - ((uF N p : F) : LaurentSeries ℚ) ^ (p ^ 2 - 1) := rfl
      rw [h2] at h1
      rw [h1, coe_tF, ht.2, coe_uF, hu.2, one_pow, zero_pow hpos, sub_zero]

end Assembly

end NeronLeg1CuspSections
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd.NeronLeg1CuspSections"

open Polynomial ModularCurve ModularCurve.IgusaScheme in
theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let u : ↥(modularFunctionFieldFull (N * p)) := (jFull (N * p))⁻¹
    let jp : ↥(modularFunctionFieldFull (N * p)) :=
      ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩
    let t : ↥(modularFunctionFieldFull (N * p)) := jp * u ^ p

    (∃ ε : Fin 2 → (↥(chartAlgInf (N * p) p) →ₐ[↥(GaloisRep.ratLocalizedAt p)]
        ↥(GaloisRep.ratLocalizedAt p)),
      ∀ b : ↥(chartAlgInf (N * p) p),
        ((ε 0 b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)
            = ((b : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ).coeff 0 ∧
        ((ε 1 b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)
            = ((atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))) :
                ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ).coeff 0) ∧

    (t ∈ chartAlgInf (N * p) p ∧
      (∃ h : Polynomial (Polynomial ℤ), h.Monic ∧
        h.map (Polynomial.evalRingHom 0) = X ^ (p + 1) - X ^ p ∧
        h.eval₂ (Polynomial.eval₂RingHom (algebraMap ℤ ↥(modularFunctionFieldFull (N * p))) u) t
          = 0) ∧
      ((t : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ).coeff 0 = 1 ∧
      ((atkinLehnerInvolutionFull N p t : ↥(modularFunctionFieldFull (N * p))) :
        LaurentSeries ℚ).coeff 0 = 0) ∧

    (∀ W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull (N * p)),
      (∀ f : ↥(modularFunctionFieldFull (N * p)), f ∈ W₀ ↔
        ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y
            = coeffMap (Int.castRingHom ℚ) x) →
      (∀ f : ↥(modularFunctionFieldFull (N * p)), f ∈ W₁ ↔
        atkinLehnerInvolutionFull N p f ∈ W₀) →
      (t - 1 ∈ W₀.nonunits ∧
        ((atkinLehnerInvolutionFull N p (t - 1) : ↥(modularFunctionFieldFull (N * p))) :
          LaurentSeries ℚ).coeff 0 = -1) ∧
      (t ^ p - u ^ (p ^ 2 - 1) ∈ W₁.nonunits ∧
        ((t ^ p - u ^ (p ^ 2 - 1) : ↥(modularFunctionFieldFull (N * p))) :
          LaurentSeries ℚ).coeff 0 = 1)) := by
  intro u jp t
  exact NeronLeg1CuspSections.main N p hpN

end
end S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd (solution)
