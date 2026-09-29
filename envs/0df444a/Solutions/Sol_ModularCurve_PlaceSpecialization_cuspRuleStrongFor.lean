-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.cuspRuleStrongFor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/37d52c63-e0b0-5625-90ad-9b2e92ea773e

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import Theorems.Thm_ModularCurve_cuspChartInftyZero_place_unique
import Theorems.Thm_ModularCurve_cuspChartZeroInfty_place_unique
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jqN
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_cuspRuleStrongFor
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

noncomputable section

namespace P2MWs12
namespace CuspRule

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ne_zero_of_ord_ne_zero (v : Place K F) {f : F} (h : v.ord f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h (Place.ord_zero v)

theorem ne_zero_of_ord_pos (v : Place K F) {f : F} (h : 0 < v.ord f) : f ≠ 0 :=
  ne_zero_of_ord_ne_zero v h.ne'

theorem ne_zero_of_ord_neg (v : Place K F) {f : F} (h : v.ord f < 0) : f ≠ 0 :=
  ne_zero_of_ord_ne_zero v h.ne

theorem ord_pow (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  simpa only [zpow_natCast] using v.ord_zpow f (n : ℤ)

theorem ord_div (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    v.ord (f / g) = v.ord f - v.ord g := by
  rw [div_eq_mul_inv, v.ord_mul hf (inv_ne_zero hg), v.ord_inv]
  ring

theorem ord_sub_algebraMap_of_ord_neg (v : Place K F) {f : F} (hf : v.ord f < 0) (a : K) :
    v.ord (f - algebraMap K F a) = v.ord f := by
  by_cases ha : a = 0
  · simp [ha]
  have hca : -algebraMap K F a ≠ 0 := neg_ne_zero.mpr ((map_ne_zero _).mpr ha)
  have h0 : v.ord (-algebraMap K F a) = 0 := by rw [v.ord_neg, v.ord_algebraMap]
  rw [sub_eq_add_neg]
  exact v.ord_add_eq_of_lt (ne_zero_of_ord_neg v hf) hca (by rw [h0]; exact hf)

theorem ord_sub_algebraMap_of_ne (v : Place K F) {f : F} {c₀ : K}
    (h : 0 < v.ord (f - algebraMap K F c₀)) {a : K} (ha : a ≠ c₀) :
    v.ord (f - algebraMap K F a) = 0 := by
  have hne : algebraMap K F (c₀ - a) ≠ 0 := (map_ne_zero _).mpr (sub_ne_zero.mpr ha.symm)
  have hsplit : f - algebraMap K F a = algebraMap K F (c₀ - a) + (f - algebraMap K F c₀) := by
    rw [map_sub]; ring
  rw [hsplit, v.ord_add_eq_of_lt hne (ne_zero_of_ord_pos v h) (by rwa [v.ord_algebraMap]),
    v.ord_algebraMap]

theorem ord_eq_zero_of_ord_sub_pos (v : Place K F) {f : F} {c₀ : K} (hc₀ : c₀ ≠ 0)
    (h : 0 < v.ord (f - algebraMap K F c₀)) : v.ord f = 0 := by
  simpa using ord_sub_algebraMap_of_ne v h (a := 0) (Ne.symm hc₀)

theorem ne_zero_of_ord_sub_pos (v : Place K F) {f : F} {c₀ : K} (hc₀ : c₀ ≠ 0)
    (h : 0 < v.ord (f - algebraMap K F c₀)) : f ≠ 0 := by
  rintro rfl
  rw [zero_sub, v.ord_neg, v.ord_algebraMap] at h
  exact lt_irrefl _ h

theorem mem_of_ord_sub_pos (v : Place K F) {f : F} {c₀ : K}
    (h : 0 < v.ord (f - algebraMap K F c₀)) : f ∈ v.toValuationSubring := by
  have h1 : f - algebraMap K F c₀ ∈ v.toValuationSubring :=
    (v.mem_iff_ord_nonneg (ne_zero_of_ord_pos v h)).mpr h.le
  simpa using add_mem h1 (v.algebraMap_mem' c₀)

theorem mem_maximalIdeal_of_ord_pos (v : Place K F) (g : v.toValuationSubring)
    (h : 0 < v.ord (g : F)) : g ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Place.adicValuation_coe_eq_one_iff]
  intro h1
  simp [Place.ord, h1] at h

theorem residue_eq_algebraMap_of_ord_sub_pos (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) {c₀ : K} (h : 0 < v.ord (f - algebraMap K F c₀)) :
    IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField c₀ := by
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact mem_maximalIdeal_of_ord_pos v _ (by simpa using h)

theorem residue_eq_zero_of_ord_pos (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : 0 < v.ord f) :
    IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField 0 := by
  rw [map_zero, IsLocalRing.residue_eq_zero_iff]
  exact mem_maximalIdeal_of_ord_pos v _ h

theorem residue_div_pow_eq_algebraMap (v : Place K F) {f g : F} {a b : K} (hb : b ≠ 0) (n : ℕ)
    (hfa : 0 < v.ord (f - algebraMap K F a)) (hgb : 0 < v.ord (g - algebraMap K F b))
    (ht : f / g ^ n ∈ v.toValuationSubring) :
    IsLocalRing.residue v.toValuationSubring ⟨f / g ^ n, ht⟩
      = algebraMap K v.ResidueField (a / b ^ n) := by
  have hfO := mem_of_ord_sub_pos v hfa
  have hgO := mem_of_ord_sub_pos v hgb
  have hg0 : g ≠ 0 := ne_zero_of_ord_sub_pos v hb hgb
  have hmul : (⟨f / g ^ n, ht⟩ : v.toValuationSubring) * ⟨g, hgO⟩ ^ n = ⟨f, hfO⟩ := by
    ext
    simp [div_mul_cancel₀ _ (pow_ne_zero n hg0)]
  have hres := congrArg (IsLocalRing.residue v.toValuationSubring) hmul
  rw [map_mul, map_pow, residue_eq_algebraMap_of_ord_sub_pos v hgO hgb,
    residue_eq_algebraMap_of_ord_sub_pos v hfO hfa] at hres
  have hb' : algebraMap K v.ResidueField b ^ n ≠ 0 := pow_ne_zero n ((map_ne_zero _).mpr hb)
  rw [map_div₀, map_pow]
  exact eq_div_of_mul_eq hb' hres

end Generic

section ValRing

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem vs_ne_zero_of_one_lt {j : L} (h : 1 < A.valuation j) : j ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  exact not_lt_zero' h

theorem vs_coe_ne_of_one_lt {j : L} (h : 1 < A.valuation j) (a : A) : (a : L) ≠ j := by
  intro hja
  subst hja
  exact lt_irrefl _ (h.trans_le (A.valuation_le_one a))

theorem vs_one_lt_of_eq_pow {b c : L} (hb : 1 < A.valuation b) {n : ℕ} (hn : n ≠ 0)
    (hc : A.valuation c = A.valuation b ^ n) : 1 < A.valuation c := by
  rw [hc]
  exact one_lt_pow₀ hb hn

theorem vs_one_lt_of_pow_eq {b c : L} (hb : 1 < A.valuation b) (n : ℕ)
    (hc : A.valuation c ^ n = A.valuation b) : 1 < A.valuation c := by
  by_contra hle
  have h1 : A.valuation c ^ n ≤ 1 := pow_le_one₀ zero_le' (not_lt.mp hle)
  have h2 : A.valuation b ≤ 1 := hc.symm.trans_le h1
  exact lt_irrefl _ (hb.trans_le h2)

theorem vs_valuation_div_pow_lt_one {b c : L} (hb : 1 < A.valuation b) {n : ℕ} (hn : 1 < n)
    (hc : A.valuation c = A.valuation b ^ n) : A.valuation (b / c ^ n) < 1 := by
  have hb0 : A.valuation b ≠ 0 := (map_ne_zero _).mpr (vs_ne_zero_of_one_lt A hb)
  rw [map_div₀, map_pow, hc, ← pow_mul, div_lt_one₀ (pow_pos (zero_lt_iff.mpr hb0) _)]
  calc A.valuation b = A.valuation b ^ 1 := (pow_one _).symm
    _ < A.valuation b ^ (n * n) := pow_lt_pow_right₀ hb (by nlinarith)

end ValRing

section LiesOver

variable {L : Type*} [Field L]

theorem liesOverPrime_of_ringHom (A : ValuationSubring L) (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type*} [Field k] [CharP k ℓ] (red : A →+* k) : A.LiesOverPrime ℓ := by
  rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff]
  by_contra hge
  have hmem : ((ℓ : A) : L) = (ℓ : L) := by simp
  have hle : A.valuation (ℓ : L) ≤ 1 := hmem ▸ A.valuation_le_one (ℓ : A)
  have heq : A.valuation ((ℓ : A) : L) = 1 := by
    rw [hmem]
    exact le_antisymm hle (not_lt.mp hge)
  have hunit : IsUnit (ℓ : A) := (A.valuation_eq_one_iff _).mpr heq
  have hk := hunit.map red
  rw [map_natCast, CharP.cast_eq_zero k ℓ] at hk
  exact not_isUnit_zero hk

end LiesOver

section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem chart_pos_of_dichotomy (u : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (n : ℕ)
    (h : f / g ^ n - algebraMap K F 0 = 0 ∨ 0 < u.ord (f / g ^ n - algebraMap K F 0)) :
    0 < u.ord (f * g⁻¹ ^ n) := by
  rw [map_zero, sub_zero] at h
  rcases h with h | h
  · exact absurd h (div_ne_zero hf (pow_ne_zero n hg))
  · rwa [div_eq_mul_inv, ← inv_pow] at h

end Chart

section Packet

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {p : ℕ} [NeZero p]
  {k : Type*} [Field k] (red : ↥A →+* k)

local notation "Qb" => AlgebraicClosure ℚ
local notation "FB" => ModularCurve.modularFunctionFieldBar p
local notation "cB" => algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar p)
local notation "FC" => ModularCurve.modularFunctionFieldC k p

theorem chart_vanishes_at_point (w : Place Qb FB) (u : Place k FC) (f g : FB) (Fd Gd : FC)
    {b c : Qb} (hfb : 0 < w.ord (f - cB b)) (hgc : 0 < w.ord (g - cB c))
    (hb : 1 < A.valuation b) (hp1 : 1 < p) (hc : A.valuation c = A.valuation b ^ p)
    (hR4 : ∀ τ : A, A.valuation (τ : Qb) < 1 → red τ = 0)
    (hFd : Fd ≠ 0) (hGd : Gd ≠ 0)
    (d7 : ∀ (τ : A) (ht : f / g ^ p ∈ w.toValuationSubring),
      (∀ a : A, w.ord (g - cB (a : Qb)) ≤ 0) →
      IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
          = algebraMap Qb w.ResidueField (τ : Qb) →
        Fd / Gd ^ p - algebraMap k FC (red τ) = 0 ∨
          0 < u.ord (Fd / Gd ^ p - algebraMap k FC (red τ))) :
    0 < u.ord (Fd * Gd⁻¹ ^ p) := by
  have hb0 : b ≠ 0 := vs_ne_zero_of_one_lt A hb
  have hc1 : 1 < A.valuation c := vs_one_lt_of_eq_pow A hb (by omega) hc
  have hc0 : c ≠ 0 := vs_ne_zero_of_one_lt A hc1
  have hτ : A.valuation (b / c ^ p) < 1 := vs_valuation_div_pow_lt_one A hb hp1 hc
  let τ : A := ⟨b / c ^ p, (A.valuation_le_one_iff _).mp hτ.le⟩
  have hf0 : f ≠ 0 := ne_zero_of_ord_sub_pos w hb0 hfb
  have hg0 : g ≠ 0 := ne_zero_of_ord_sub_pos w hc0 hgc
  have htne : f / g ^ p ≠ 0 := div_ne_zero hf0 (pow_ne_zero p hg0)
  have htord : w.ord (f / g ^ p) = 0 := by
    rw [ord_div w hf0 (pow_ne_zero p hg0), ord_pow, ord_eq_zero_of_ord_sub_pos w hb0 hfb,
      ord_eq_zero_of_ord_sub_pos w hc0 hgc]
    ring
  have ht : f / g ^ p ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg htne).mpr htord.ge
  have hres : IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
      = algebraMap Qb w.ResidueField (τ : Qb) :=
    residue_div_pow_eq_algebraMap w hc0 p hfb hgc ht
  have h := d7 τ ht (fun a => (ord_sub_algebraMap_of_ne w hgc (vs_coe_ne_of_one_lt A hc1 a)).le) hres
  rw [hR4 τ hτ] at h
  exact chart_pos_of_dichotomy u hFd hGd p h

theorem chart_vanishes_at_cusp (w : Place Qb FB) (u : Place k FC) (f g : FB) (Fd Gd : FC)
    (hf : w.ord f = -1) (hg : w.ord g = -(p : ℤ)) (hp1 : 1 < p)
    (hFd : Fd ≠ 0) (hGd : Gd ≠ 0)
    (d7 : ∀ (τ : A) (ht : f / g ^ p ∈ w.toValuationSubring),
      (∀ a : A, w.ord (g - cB (a : Qb)) ≤ 0) →
      IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
          = algebraMap Qb w.ResidueField (τ : Qb) →
        Fd / Gd ^ p - algebraMap k FC (red τ) = 0 ∨
          0 < u.ord (Fd / Gd ^ p - algebraMap k FC (red τ))) :
    0 < u.ord (Fd * Gd⁻¹ ^ p) := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp1
  have hf0 : f ≠ 0 := ne_zero_of_ord_neg w (by rw [hf]; norm_num)
  have hgneg : w.ord g < 0 := by rw [hg]; omega
  have hg0 : g ≠ 0 := ne_zero_of_ord_neg w hgneg
  have htne : f / g ^ p ≠ 0 := div_ne_zero hf0 (pow_ne_zero p hg0)
  have htpos : 0 < w.ord (f / g ^ p) := by
    rw [ord_div w hf0 (pow_ne_zero p hg0), ord_pow, hf, hg]
    have h4 : (4 : ℤ) ≤ (p : ℤ) * p := by nlinarith
    linarith
  have ht : f / g ^ p ∈ w.toValuationSubring := (w.mem_iff_ord_nonneg htne).mpr htpos.le
  have hres : IsLocalRing.residue w.toValuationSubring ⟨_, ht⟩
      = algebraMap Qb w.ResidueField ((0 : A) : Qb) := by
    rw [ZeroMemClass.coe_zero]
    exact residue_eq_zero_of_ord_pos w ht htpos
  have h := d7 0 ht (fun a => by rw [ord_sub_algebraMap_of_ord_neg w hgneg a]; exact hgneg.le) hres
  rw [map_zero] at h
  exact chart_pos_of_dichotomy u hFd hGd p h

theorem not_valued_of_value (w : Place Qb FB) (f : FB) {b : Qb} (hfb : 0 < w.ord (f - cB b))
    (hb : 1 < A.valuation b) : ∀ a : A, w.ord (f - cB (a : Qb)) ≤ 0 :=
  fun a => (ord_sub_algebraMap_of_ne w hfb (vs_coe_ne_of_one_lt A hb a)).le

theorem not_valued_of_pole (w : Place Qb FB) (f : FB) (hf : w.ord f < 0) :
    ∀ a : A, w.ord (f - cB (a : Qb)) ≤ 0 :=
  fun a => by rw [ord_sub_algebraMap_of_ord_neg w hf a]; exact hf.le

end Packet

section Pic

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {ℓ p : ℕ} [Fact ℓ.Prime] [NeZero p]
  {data : ModularCurve.ModularPolynomialData ℓ} {hKr : ModularCurve.KroneckerCongruence ℓ data}
  {k : Type*} [Field k] [CharP k ℓ] {red : ↥A →+* k}
  {hα : ModularCurve.HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p ℓ}
  {hβ : ModularCurve.HeckeBetaBarIntegral (AlgebraicClosure ℚ) p ℓ}
  (S : ModularCurve.PlaceSpecialization A ℓ p data hKr k red hα hβ)

theorem spPic0_mk_placeDiff_eq_zero
    (x c : Place (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar p))
    (h : ModularCurve.placeDiff p x c ∈ Divisor.degZero) (hsp : S.sp x = S.sp c) :
    S.spPic0 (Pic0.mk ⟨ModularCurve.placeDiff p x c, h⟩) = 0 := by
  obtain ⟨D', hD', hcl⟩ := S.spPic0_compat ⟨ModularCurve.placeDiff p x c, h⟩
  rw [hcl]
  have hD0 : (D' : Divisor k (ModularCurve.modularFunctionFieldC k p)) = 0 := by
    rw [hD']
    show Finsupp.mapDomain S.sp (Finsupp.single x 1 - Finsupp.single c 1) = 0
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hsp, sub_self]
  have hD0' : D' = 0 := Subtype.ext hD0
  rw [hD0', Pic0.mk_zero]

end Pic

end P2MWs12.CuspRule

end

open P2MWs12.CuspRule in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ p : ℕ) [Fact ℓ.Prime] [NeZero p] (hp : p.Prime) (hℓp : ℓ ≠ p)
    (data : ModularCurve.ModularPolynomialData ℓ) (hKr : ModularCurve.KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : ↥A →+* k)
    (hα : ModularCurve.HeckeAlphaBarIntegral (AlgebraicClosure ℚ) p ℓ)
    (hβ : ModularCurve.HeckeBetaBarIntegral (AlgebraicClosure ℚ) p ℓ)
    (S : ModularCurve.PlaceSpecialization A ℓ p data hKr k red hα hβ) :
    ModularCurve.CuspRuleStrongFor A S.spPic0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro x j₁ j₂ hinf hzero _hgal hx1 hx2 hj1

  have hp1 : 1 < p := hp.one_lt
  have hpk : (p : k) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff k ℓ] at h0
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hp).mp h0)
  have hR4 : ∀ τ : A, A.valuation (τ : AlgebraicClosure ℚ) < 1 → red τ = 0 := fun τ hτ =>
    ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A ℓ
      (liesOverPrime_of_ringHom A ℓ red) red τ hτ
  have hFr := ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime p

  have hJinf : (cuspInftyBar p).ord (jBar p) = -1 := ModularCurve.ord_cuspInftyBar_coeffEmb_jq p
  have hJpinf : (cuspInftyBar p).ord (jpBar p) = -(p : ℤ) :=
    ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand p p (dvd_refl p)
  have hJzero : (cuspZeroBar p).ord (jBar p) = -(p : ℤ) :=
    ModularCurve.ord_cuspZeroBar_coeffEmb_jq p hFr
  have hJpzero : (cuspZeroBar p).ord (jpBar p) = -1 :=
    ModularCurve.ord_cuspZeroBar_coeffEmb_jqN p hFr

  have hxt : (S.sp x).ord (⟨jqModC k, jqModC_mem k p⟩ : ModularCurve.modularFunctionFieldC k p) < 0 :=
    S.d0_j_pole x (not_valued_of_value A x (jBar p) hx1 hj1)
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  ·

    have hj2 : 1 < A.valuation j₂ := vs_one_lt_of_eq_pow A hj1 hp.ne_zero hv
    have hxN : (S.sp x).ord (⟨jqNModC k p, jqNModC_mem k p⟩ : ModularCurve.modularFunctionFieldC k p) < 0 :=
      S.d0_jN_pole x (not_valued_of_value A x (jpBar p) hx2 hj2)
    have hQx := chart_vanishes_at_point A red x (S.sp x) (jBar p) (jpBar p)
      ⟨jqModC k, jqModC_mem k p⟩ ⟨jqNModC k p, jqNModC_mem k p⟩ hx1 hx2 hj1 hp1 hv hR4
      (ne_zero_of_ord_neg _ hxt) (ne_zero_of_ord_neg _ hxN) (S.d7_dictZero x)

    have hit : (S.sp (cuspInftyBar p)).ord
        (⟨jqModC k, jqModC_mem k p⟩ : ModularCurve.modularFunctionFieldC k p) < 0 :=
      S.d0_j_pole _ (not_valued_of_pole A _ (jBar p) (by rw [hJinf]; norm_num))
    have hiN : (S.sp (cuspInftyBar p)).ord
        (⟨jqNModC k p, jqNModC_mem k p⟩ : ModularCurve.modularFunctionFieldC k p) < 0 :=
      S.d0_jN_pole _ (not_valued_of_pole A _ (jpBar p) (by rw [hJpinf]; omega))
    have hQi := chart_vanishes_at_cusp A red (cuspInftyBar p) (S.sp (cuspInftyBar p)) (jBar p) (jpBar p)
      ⟨jqModC k, jqModC_mem k p⟩ ⟨jqNModC k p, jqNModC_mem k p⟩ hJinf hJpinf hp1
      (ne_zero_of_ord_neg _ hit) (ne_zero_of_ord_neg _ hiN) (S.d7_dictZero _)
    have hsp : S.sp x = S.sp (cuspInftyBar p) :=
      ModularCurve.cuspChartZeroInfty_place_unique k p hpk (S.sp x) (S.sp (cuspInftyBar p))
        hxt hQx hit hQi
    exact spPic0_mk_placeDiff_eq_zero S x (cuspInftyBar p) hinf hsp
  ·

    have hj2 : 1 < A.valuation j₂ := vs_one_lt_of_pow_eq A hj1 p hv
    have hxN : (S.sp x).ord (⟨jqNModC k p, jqNModC_mem k p⟩ : ModularCurve.modularFunctionFieldC k p) < 0 :=
      S.d0_jN_pole x (not_valued_of_value A x (jpBar p) hx2 hj2)
    have hQx := chart_vanishes_at_point A red x (S.sp x) (jpBar p) (jBar p)
      ⟨jqNModC k p, jqNModC_mem k p⟩ ⟨jqModC k, jqModC_mem k p⟩ hx2 hx1 hj2 hp1 hv.symm hR4
      (ne_zero_of_ord_neg _ hxN) (ne_zero_of_ord_neg _ hxt) (S.d7_dictInfty x)

    have hzt : (S.sp (cuspZeroBar p)).ord
        (⟨jqModC k, jqModC_mem k p⟩ : ModularCurve.modularFunctionFieldC k p) < 0 :=
      S.d0_j_pole _ (not_valued_of_pole A _ (jBar p) (by rw [hJzero]; omega))
    have hzN : (S.sp (cuspZeroBar p)).ord
        (⟨jqNModC k p, jqNModC_mem k p⟩ : ModularCurve.modularFunctionFieldC k p) < 0 :=
      S.d0_jN_pole _ (not_valued_of_pole A _ (jpBar p) (by rw [hJpzero]; norm_num))
    have hQz := chart_vanishes_at_cusp A red (cuspZeroBar p) (S.sp (cuspZeroBar p)) (jpBar p) (jBar p)
      ⟨jqNModC k p, jqNModC_mem k p⟩ ⟨jqModC k, jqModC_mem k p⟩ hJpzero hJzero hp1
      (ne_zero_of_ord_neg _ hzN) (ne_zero_of_ord_neg _ hzt) (S.d7_dictInfty _)
    have hsp : S.sp x = S.sp (cuspZeroBar p) :=
      ModularCurve.cuspChartInftyZero_place_unique k p (S.sp x) (S.sp (cuspZeroBar p))
        hxt hQx hzt hQz
    exact spPic0_mk_placeDiff_eq_zero S x (cuspZeroBar p) hzero hsp

end S_ModularCurve_PlaceSpecialization_cuspRuleStrongFor
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_cuspRuleStrongFor (solution)
