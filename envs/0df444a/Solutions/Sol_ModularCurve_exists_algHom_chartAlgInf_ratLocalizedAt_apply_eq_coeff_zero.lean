-- Prove2me | solution 1 for ModularCurve.exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/1257507a-ccd0-5d8b-ba0a-d7a8bfbc18ee

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Classical
p2m_open "Polynomial AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero.ModularCurve WithZero"

namespace ModularCurve
namespace CuspSectionQExp
p2m_open "ModularCurve"

section QAdic

def 𝒪 : Subring (LaurentSeries ℚ) := (Valued.v : Valuation (LaurentSeries ℚ) ℤᵐ⁰).integer

theorem mem_𝒪_iff (f : LaurentSeries ℚ) : f ∈ 𝒪 ↔ ∀ n : ℤ, n < 0 → f.coeff n = 0 := by
  rw [𝒪, Valuation.mem_integer_iff]
  have h := LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := ℚ) (D := 0) (f := f)
  simpa using h

theorem exists_powerSeries_of_mem_𝒪 {f : LaurentSeries ℚ} (hf : f ∈ 𝒪) :
    ∃ F : PowerSeries ℚ, (F : LaurentSeries ℚ) = f :=
  (LaurentSeries.val_le_one_iff_eq_coe (K := ℚ) f).mp hf

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

end QAdic

section Zp

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

end Zp

section Bivariate

variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {ℓ : ℕ} [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "F" => (↥F₀ : Type)
set_option quotPrecheck false in
local notation "Zp" => (↥(GaloisRep.ratLocalizedAt ℓ) : Type)

theorem coe_algebraMap_R (c : Zp) :
    ((algebraMap Zp F c : F) : LaurentSeries ℚ) = HahnSeries.C (c : ℚ) := by
  have h : (algebraMap F (LaurentSeries ℚ)).comp (algebraMap ℚ F) =
      (HahnSeries.C : ℚ →+* LaurentSeries ℚ) := Subsingleton.elim _ _
  have h' := RingHom.congr_fun h (c : ℚ)
  rw [RingHom.comp_apply, IntermediateField.algebraMap_apply] at h'
  exact h'

theorem algebraMap_comp_aeval_adjoin (s : F) :
    (algebraMap ↥(Algebra.adjoin Zp ({s} : Set F)) F).comp
        (aeval (⟨s, Algebra.subset_adjoin rfl⟩ : ↥(Algebra.adjoin Zp ({s} : Set F)))).toRingHom
      = (aeval (R := Zp) s).toRingHom := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C]
    rfl
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X]
    rfl

theorem exists_bivariate_of_isIntegral_adjoin {s b : F}
    (h : IsIntegral ↥(Algebra.adjoin Zp ({s} : Set F)) b) :
    ∃ P : Polynomial (Polynomial Zp), P.Monic ∧ P.eval₂ (aeval (R := Zp) s).toRingHom b = 0 := by
  obtain ⟨Q, hQm, hQ⟩ := h
  set Q' : Polynomial F := Q.map (algebraMap ↥(Algebra.adjoin Zp ({s} : Set F)) F) with hQ'
  have hQ'm : Q'.Monic := hQm.map _
  have hlifts : Q' ∈ Polynomial.lifts (aeval (R := Zp) s).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hQ', Polynomial.coeff_map]
    have hmem : ((Q.coeff n : ↥(Algebra.adjoin Zp ({s} : Set F))) : F) ∈ (aeval (R := Zp) s).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (Q.coeff n).2
    obtain ⟨q, hq⟩ := hmem
    exact ⟨q, hq⟩
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hQ'm
  refine ⟨P, hPm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hPmap, hQ', Polynomial.eval_map, hQ]

def constO : Zp →+* ↥𝒪 :=
  ((HahnSeries.C : ℚ →+* LaurentSeries ℚ).comp (GaloisRep.ratLocalizedAt ℓ).subtype).codRestrict 𝒪
    (fun _ => C_mem_𝒪 _)

@[scoped simp] theorem coe_constO (c : Zp) :
    ((constO c : ↥𝒪) : LaurentSeries ℚ) = HahnSeries.C (c : ℚ) := rfl

theorem coe_mem_𝒪_and_coeff_zero_mem {s b : F} (hs : ((s : F) : LaurentSeries ℚ) ∈ 𝒪)
    (hs0 : ((s : F) : LaurentSeries ℚ).coeff 0 = 0)
    (hb : IsIntegral ↥(Algebra.adjoin Zp ({s} : Set F)) b) :
    ((b : F) : LaurentSeries ℚ) ∈ 𝒪 ∧
      ((b : F) : LaurentSeries ℚ).coeff 0 ∈ GaloisRep.ratLocalizedAt ℓ := by
  obtain ⟨P, hPm, hP⟩ := exists_bivariate_of_isIntegral_adjoin hb

  set κ : Polynomial Zp →+* ↥𝒪 := eval₂RingHom (constO (ℓ := ℓ)) ⟨_, hs⟩ with hκ
  set ιF : F →+* LaurentSeries ℚ := algebraMap F (LaurentSeries ℚ) with hιF
  have hιF_apply : ∀ x : F, ιF x = (x : LaurentSeries ℚ) := fun x =>
    IntermediateField.algebraMap_apply F₀ x
  have hcompat : (𝒪.subtype).comp κ = ιF.comp (aeval (R := Zp) s).toRingHom := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, RingHom.comp_apply, hκ, coe_eval₂RingHom, eval₂_C, Subring.subtype_apply,
        coe_constO, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, hιF_apply,
        coe_algebraMap_R]
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
    rw [Polynomial.hom_eval₂, hcompat, show 𝒪.subtype b' = ιF b from (hιF_apply b).symm,
      ← Polynomial.hom_eval₂, hP, map_zero]
  have hcompat' : (algebraMap Zp ℚ).comp (evalRingHom 0) = ρ.comp κ := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [RingHom.comp_apply, RingHom.comp_apply, coe_evalRingHom, eval_C, hκ, coe_eval₂RingHom, eval₂_C,
        ρ_apply, coe_constO, HahnSeries.C_apply, HahnSeries.coeff_single_same]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, coe_evalRingHom, eval_X, hκ, coe_eval₂RingHom, eval₂_X,
        ρ_apply, map_zero]
      exact hs0.symm
  have hint : IsIntegral Zp (((b : F) : LaurentSeries ℚ).coeff 0) := by
    refine ⟨P.map (evalRingHom 0), hPm.map _, ?_⟩
    rw [eval₂_map, hcompat', show ((b : F) : LaurentSeries ℚ).coeff 0 = ρ b' from rfl,
      ← Polynomial.hom_eval₂, hroot', map_zero]
  exact mem_ratLocalizedAt_of_isIntegral ℓ hint

end Bivariate

section Charts

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [Fact p.Prime]
  (j : ↥F₀) [Fact (j ≠ 0)]

set_option quotPrecheck false in
local notation "F" => (↥F₀ : Type)
set_option quotPrecheck false in
local notation "Zp" => (↥(GaloisRep.ratLocalizedAt p) : Type)
set_option quotPrecheck false in
local notation "B" => TwoChartIntegralModel.chartAlgInf Zp F j

theorem cuspInf (hj : ∀ n : ℤ, n ≤ 0 → ((j : LaurentSeries ℚ)⁻¹).coeff n = 0) (b : ↥B) :
    ((b : F) : LaurentSeries ℚ) ∈ 𝒪 ∧ ((b : F) : LaurentSeries ℚ).coeff 0 ∈ GaloisRep.ratLocalizedAt p := by
  have hcoe : (((j⁻¹ : F) : F) : LaurentSeries ℚ) = ((j : F) : LaurentSeries ℚ)⁻¹ := by
    simp
  refine coe_mem_𝒪_and_coeff_zero_mem (ℓ := p) (s := (j⁻¹ : F)) ?_ ?_
    ((TwoChartIntegralModel.mem_chartAlg_iff Zp F).mp b.2)
  · rw [hcoe, mem_𝒪_iff]
    exact fun n hn => hj n hn.le
  · rw [hcoe]
    exact hj 0 le_rfl

set_option synthInstance.maxHeartbeats 1600000 in

def cuspRetraction (hj : ∀ n : ℤ, n ≤ 0 → ((j : LaurentSeries ℚ)⁻¹).coeff n = 0) :
    ↥B →ₐ[Zp] Zp where
  toFun b := ⟨((b : F) : LaurentSeries ℚ).coeff 0, (cuspInf F₀ p j hj b).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' b c := Subtype.ext (by
    have := map_mul ρ ⟨_, (cuspInf F₀ p j hj b).1⟩ ⟨_, (cuspInf F₀ p j hj c).1⟩
    simp only [ρ_apply, MulMemClass.mk_mul_mk] at this
    change (((b * c : ↥B) : F) : LaurentSeries ℚ).coeff 0 = _
    rw [Subalgebra.coe_mul, IntermediateField.coe_mul, this]
    rfl)
  map_zero' := Subtype.ext (by simp)
  map_add' b c := Subtype.ext (by
    change (((b + c : ↥B) : F) : LaurentSeries ℚ).coeff 0 = _
    rw [Subalgebra.coe_add, IntermediateField.coe_add, HahnSeries.coeff_add]
    rfl)
  commutes' c := Subtype.ext (by
    change (((algebraMap Zp ↥B c : ↥B) : F) : LaurentSeries ℚ).coeff 0 = (c : ℚ)
    rw [Subalgebra.coe_algebraMap, coe_algebraMap_R, HahnSeries.C_apply, HahnSeries.coeff_single_same])

theorem cuspRetraction_apply (hj) (b : ↥B) :
    ((cuspRetraction F₀ p j hj b : Zp) : ℚ) = ((b : F) : LaurentSeries ℚ).coeff 0 := rfl

end Charts

end ModularCurve.CuspSectionQExp
p2m_reactivate "P2MW.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero.ModularCurve P2MW.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero.ModularCurve.CuspSectionQExp"
p2m_reactivate "P2MW.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero.ModularCurve P2MW.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero.ModularCurve.CuspSectionQExp"

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero.ModularCurve ModularCurve.CuspSectionQExp in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [Fact p.Prime]
    (j : ↥F₀) [Fact (j ≠ 0)]
    (hj : ∀ n : ℤ, n ≤ 0 → ((j : LaurentSeries ℚ)⁻¹).coeff n = 0) :
    ∃ ε : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        →ₐ[↥(GaloisRep.ratLocalizedAt p)] ↥(GaloisRep.ratLocalizedAt p),
      ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
        (∀ n : ℤ, n < 0 → ((b : ↥F₀) : LaurentSeries ℚ).coeff n = 0) ∧
        ((ε b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) = ((b : ↥F₀) : LaurentSeries ℚ).coeff 0 := by
  classical
  refine ⟨cuspRetraction F₀ p j hj, fun b => ⟨?_, cuspRetraction_apply F₀ p j hj b⟩⟩
  exact (mem_𝒪_iff _).mp (cuspInf F₀ p j hj b).1

end S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero
end P2MW
export P2MW.S_ModularCurve_exists_algHom_chartAlgInf_ratLocalizedAt_apply_eq_coeff_zero (solution)
