-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.not_isInftySide_of_isZeroSide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ab37e92c-9320-5778-86a3-c6916fb3502a

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide.ModularCurve.PlaceSpecialization"

set_option autoImplicit false

noncomputable section
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide.ModularCurve"
namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_one_apply jq coeff_jq_neg_one ModularPolynomialData coeffEmb coeffEmb_coeff PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence qSeriesBar qSeriesBar_zero mem_qIntegersBar_iff cuspInftyBar cuspInftyBar_toValuationSubring deg_eq_one_modularFunctionFieldBar"
p2m_open "ModularCurve"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple"
p2m_open "ModularCurve.PlaceSpecialization"
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q]

theorem liesOverPrime_of_ringHom (red : A →+* k) : A.LiesOverPrime q := by
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
  rw [ValuationSubring.mem_nonunits_iff]
  have hmem : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hle : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ≤ 1 := (A.valuation_le_one_iff _).mpr hmem
  rcases hle.lt_or_eq with h | h
  · exact h
  · exfalso
    have hu : IsUnit ((⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ : A)) := (A.valuation_eq_one_iff _).mpr h
    have h2 := hu.map red
    have h3 : red ⟨((q : ℕ) : AlgebraicClosure ℚ), hmem⟩ = ((q : ℕ) : k) := by
      rw [← map_natCast red q]
      congr 1
    rw [h3, CharP.cast_eq_zero k q] at h2
    exact not_isUnit_zero h2

end PlaceSpecialization
end ModularCurve
end

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_one_apply jq coeff_jq_neg_one ModularPolynomialData coeffEmb coeffEmb_coeff PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence qSeriesBar qSeriesBar_zero mem_qIntegersBar_iff cuspInftyBar cuspInftyBar_toValuationSubring deg_eq_one_modularFunctionFieldBar"
p2m_open "ModularCurve"

namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple.tInfty ProlongationTuple.tZero ProlongationTuple.IsInftySide ProlongationTuple.IsZeroSide ProlongationTuple"
p2m_open "ModularCurve.PlaceSpecialization"

section General
variable {M : ℕ} [NeZero M]

theorem hasValue_pow'' {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)}
    {g : modularFunctionFieldBar M} {a : AlgebraicClosure ℚ} (h : W.HasValue g a) (n : ℕ) :
    W.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using W.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem ord_sub_algebraMap_pos_of_hasValue' (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M))
    (g : modularFunctionFieldBar M) (c : AlgebraicClosure ℚ) (h : W.HasValue g c)
    (hne : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) c ≠ 0) :
    0 < W.ord (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) c) := by
  have hm : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar M) c ∈ W.toValuationSubring :=
    sub_mem h.mem (W.algebraMap_mem' c)
  have hres : IsLocalRing.residue W.toValuationSubring ⟨_, hm⟩ = 0 := by
    have hsplit : (⟨_, hm⟩ : W.toValuationSubring) = ⟨g, h.mem⟩ - algebraMap (AlgebraicClosure ℚ) W.toValuationSubring c :=
      Subtype.ext rfl
    rw [hsplit, map_sub, h.residue_eq, Place.residue_algebraMap, sub_self]
  have hnn := W.ord_nonneg_of_mem hm
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm', hu⟩ := W.exists_isUnit_of_ord_eq_zero hne heq.symm
    have := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu
    exact this hres

theorem ord_cuspInftyBar_coeffEmb_qExpand_neg (d : ℕ) [NeZero d] (hmem : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq) ∈ modularFunctionFieldBar M) :
    (cuspInftyBar M).ord (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), hmem⟩ : modularFunctionFieldBar M) < 0 := by
  set x : modularFunctionFieldBar M := ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), hmem⟩ with hx
  have hc : (qSeriesBar (AlgebraicClosure ℚ) (modularFunctionFieldBar M) x).coeff ((d : ℤ) * (-1)) ≠ 0 := by
    show (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq)).coeff _ ≠ 0
    rw [coeffEmb_coeff, qExpand_coeff_mul, coeff_jq_neg_one, map_one]
    exact one_ne_zero
  have hne : x ≠ 0 := by
    intro h0
    apply hc
    rw [h0, qSeriesBar_zero, HahnSeries.coeff_zero]
  have hnot : x ∉ (cuspInftyBar M).toValuationSubring := by
    rw [cuspInftyBar_toValuationSubring, mem_qIntegersBar_iff, not_le]
    have hle := HahnSeries.order_le_of_coeff_ne_zero hc
    have hd : (0 : ℤ) < (d : ℤ) := by
      have := (NeZero.ne d)
      omega
    nlinarith
  by_contra hge
  push_neg at hge
  exact hnot ((cuspInftyBar M).mem_of_ord_nonneg hne hge)

end General

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}

theorem inv_mem_nonunits_of_not_mem' {e : AlgebraicClosure ℚ} (he : e ∉ A) : e⁻¹ ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  have h1 : ¬ A.valuation e ≤ 1 := fun h => he ((A.valuation_le_one_iff e).mp h)
  push_neg at h1
  rw [map_inv₀]
  exact inv_lt_one_of_one_lt₀ h1

theorem pow_succ_mem_nonunits' {x : AlgebraicClosure ℚ} (hx : x ∈ A.nonunits) (m : ℕ) : x ^ (m + 1) ∈ A.nonunits := by
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [pow_succ]; exact mul_mem ih hx

end PlaceSpecialization

end ModularCurve

end

noncomputable section
p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide.ModularCurve.PlaceSpecialization"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hW : ProlongationTuple.IsZeroSide P W) :
    ¬ ProlongationTuple.IsInftySide P W := by
  rintro ⟨hc, τ₁, hτ₁, hv₁⟩
  obtain ⟨hc', τ₀, hτ₀, hv₀⟩ := hW
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hA : A.LiesOverPrime q := liesOverPrime_of_ringHom red
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q = m + 1 + 1 := ⟨q - 2, by omega⟩
  suffices hnu : (((τ₁ * τ₀ : A)) : AlgebraicClosure ℚ) ∈ A.nonunits by
    have hlt : A.valuation (((τ₁ * τ₀ : A)) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hnu
    have h0 := ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q hA red (τ₁ * τ₀) hlt
    rw [map_mul, hτ₁, hτ₀, mul_one] at h0
    exact one_ne_zero h0
  set j : modularFunctionFieldBar (N * q) := ProlongationTuple.jFun N q with hj
  set j' : modularFunctionFieldBar (N * q) := ProlongationTuple.jQFun N q with hj'
  have hval0 : ∀ {g : modularFunctionFieldBar (N * q)} {τ : A}, red τ = 1 →
      W.HasValue g (τ : AlgebraicClosure ℚ) → g ≠ 0 := by
    intro g τ hτ hg h0
    rw [h0] at hg
    have h00 : W.HasValue (0 : modularFunctionFieldBar (N * q)) 0 := by simpa using W.hasValue_algebraMap 0
    have : (τ : AlgebraicClosure ℚ) = 0 := hg.unique h00
    have hτ0 : τ = 0 := Subtype.ext this
    rw [hτ0, map_zero] at hτ
    exact zero_ne_one hτ
  have hj0 : j ≠ 0 := by
    intro h0
    apply hval0 hτ₁ hv₁
    show ProlongationTuple.jQFun N q / ProlongationTuple.jFun N q ^ q = 0
    rw [← hj, h0, zero_pow (by omega), div_zero]
  have hj'0 : j' ≠ 0 := by
    intro h0
    apply hval0 hτ₀ hv₀
    show ProlongationTuple.jFun N q / ProlongationTuple.jQFun N q ^ q = 0
    rw [← hj', h0, zero_pow (by omega), div_zero]
  set u : modularFunctionFieldBar (N * q) := j * j' with hu
  have hu0 : u ≠ 0 := mul_ne_zero hj0 hj'0
  have hprod : ProlongationTuple.tInfty N q * ProlongationTuple.tZero N q = u * (u ^ q)⁻¹ := by
    show ProlongationTuple.jQFun N q / ProlongationTuple.jFun N q ^ q *
      (ProlongationTuple.jFun N q / ProlongationTuple.jQFun N q ^ q) = _
    rw [hu, mul_pow, mul_inv, div_eq_mul_inv, div_eq_mul_inv, ← hj, ← hj']
    ring
  have hv : W.HasValue (u * (u ^ q)⁻¹) ((τ₁ : AlgebraicClosure ℚ) * τ₀) := hprod ▸ hv₁.mul hv₀
  have hτne : ((τ₁ : AlgebraicClosure ℚ) * τ₀) ≠ 0 := by
    intro h0
    have : τ₁ * τ₀ = 0 := Subtype.ext (by push_cast; exact h0)
    have h1 : red (τ₁ * τ₀) = 1 := by rw [map_mul, hτ₁, hτ₀, mul_one]
    rw [this, map_zero] at h1
    exact zero_ne_one h1
  have hordu : W.ord u = 0 := by
    have h1 := hv.ord_eq_zero hτne
    rw [W.ord_mul hu0 (inv_ne_zero (pow_ne_zero _ hu0)), Place.ord_inv, ← zpow_natCast, Place.ord_zpow] at h1
    have : (1 - (q : ℤ)) * W.ord u = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · omega
    · exact h
  have hordj : W.ord j ≤ 0 := by have h := hc 0; simpa using h
  have hordj' : W.ord j' ≤ 0 := by have h := hc' 0; simpa using h
  rw [hu, W.ord_mul hj0 hj'0] at hordu
  have hj_ord : W.ord j = 0 := by omega
  have hj'_ord : W.ord j' = 0 := by omega
  have hsurj : Function.Surjective (algebraMap (AlgebraicClosure ℚ) W.ResidueField) :=
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField W).mp (deg_eq_one_modularFunctionFieldBar (N * q) W)
  obtain ⟨hjm, hju⟩ := W.exists_isUnit_of_ord_eq_zero hj0 hj_ord
  obtain ⟨e, he, he0⟩ := W.exists_hasValue_of_surjective hsurj hjm
  have he0 := he0 hju
  obtain ⟨hjm', hju'⟩ := W.exists_isUnit_of_ord_eq_zero hj'0 hj'_ord
  obtain ⟨e', he', he'0⟩ := W.exists_hasValue_of_surjective hsurj hjm'
  have he'0 := he'0 hju'

  have hmem1 : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) ∈ modularFunctionFieldBar (N * q) := by
    rw [qExpand_one_apply]; exact (ProlongationTuple.jFun N q).2
  have hjpole := ord_cuspInftyBar_coeffEmb_qExpand_neg (M := N * q) 1 hmem1
  have hj'pole := ord_cuspInftyBar_coeffEmb_qExpand_neg (M := N * q) q (ProlongationTuple.jQFun N q).2
  have hjeq : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), hmem1⟩ :
      modularFunctionFieldBar (N * q)) = j := Subtype.ext (by rw [hj]; show coeffEmb _ (qExpand ℚ 1 jq) = coeffEmb _ jq; rw [qExpand_one_apply])
  have hj'eq : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq), (ProlongationTuple.jQFun N q).2⟩ :
      modularFunctionFieldBar (N * q)) = j' := Subtype.ext rfl
  rw [hjeq] at hjpole
  rw [hj'eq] at hj'pole
  have heA : e ∉ A := by
    intro heA
    have h1 := hc ⟨e, heA⟩
    have hne : j - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) e ≠ 0 := by
      intro h0
      have hconst : j = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) e := sub_eq_zero.mp h0
      rw [hconst] at hjpole
      have h3 := (cuspInftyBar (N * q)).ord_nonneg_of_mem ((cuspInftyBar (N * q)).algebraMap_mem' e)
      omega
    have h2 := ord_sub_algebraMap_pos_of_hasValue' W j e he hne
    change W.ord (j - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) e) ≤ 0 at h1
    omega
  have he'A : e' ∉ A := by
    intro he'A
    have h1 := hc' ⟨e', he'A⟩
    have hne : j' - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) e' ≠ 0 := by
      intro h0
      have hconst : j' = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) e' := sub_eq_zero.mp h0
      rw [hconst] at hj'pole
      have h3 := (cuspInftyBar (N * q)).ord_nonneg_of_mem ((cuspInftyBar (N * q)).algebraMap_mem' e')
      omega
    have h2 := ord_sub_algebraMap_pos_of_hasValue' W j' e' he' hne
    change W.ord (j' - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) e') ≤ 0 at h1
    omega
  set x : AlgebraicClosure ℚ := e * e' with hx
  have hx0 : x ≠ 0 := mul_ne_zero he0 he'0
  have hxu : W.HasValue u x := he.mul he'
  have hval : W.HasValue (u * (u ^ q)⁻¹) (x * (x ^ q)⁻¹) :=
    hxu.mul ((hasValue_pow'' hxu q).inv (pow_ne_zero _ hx0))
  have hτx : ((τ₁ : AlgebraicClosure ℚ) * τ₀) = x * (x ^ q)⁻¹ := hv.unique hval
  have hid : x * (x ^ q)⁻¹ = (x⁻¹) ^ (m + 1) := by
    rw [hm, pow_succ, mul_inv, mul_comm ((x ^ (m + 1))⁻¹), ← mul_assoc, mul_inv_cancel₀ hx0, one_mul, inv_pow]
  have hxn : x⁻¹ ∈ A.nonunits := by
    rw [hx, mul_inv]
    exact mul_mem (inv_mem_nonunits_of_not_mem' heA) (inv_mem_nonunits_of_not_mem' he'A)
  show ((τ₁ : AlgebraicClosure ℚ) * τ₀) ∈ A.nonunits
  rw [hτx, hid]
  exact pow_succ_mem_nonunits' hxn m

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_not_isInftySide_of_isZeroSide (solution)
