-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_modularUnit_eq_mul_ord_jqModC_of_not_isAffineGeomPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d394edcd-0795-5fe2-bab8-7465b2b87902

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_modularUnit_eq_mul_ord_jqModC_of_not_isAffineGeomPlace
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
open AlgebraicCurve ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace G2Reduction

private theorem desc
    (k : Type*) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q] :
    ∃ G : Polynomial k, G.natDegree = q - 1 ∧
      HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
          (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k)) *
        (ModularCurve.qExpand k q (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ k
          (ModularCurve.dedekindEtaUnit.map (Int.castRingHom k))))⁻¹
        = Polynomial.aeval (ModularCurve.jqModC k) G := by
  exact ModularCurve.exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP k q

section UnitForms
section AnyRing

variable (R : Type*) [CommRing R] (q : ℕ) [NeZero q]

private noncomputable def unitForm : LaurentSeries R :=
  HahnSeries.single (1 : ℤ) 1 *
      HahnSeries.ofPowerSeries ℤ R (dedekindEtaUnit.map (Int.castRingHom R)) *
    (HahnSeries.single (-(q : ℤ)) 1 *
      qExpand R q (HahnSeries.ofPowerSeries ℤ R (dedekindEtaUnitInv.map (Int.castRingHom R))))

variable {R}

private theorem coeffMap_ofPowerSeries' {S : Type*} [CommRing S] (f : R →+* S) (p : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R p) = HahnSeries.ofPowerSeries ℤ S (p.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

private theorem coeffMap_unitForm {S : Type*} [CommRing S] (f : R →+* S) :
    coeffMap f (unitForm R q) = unitForm S q := by
  have h1 : f.comp (Int.castRingHom R) = Int.castRingHom S := RingHom.ext_int _ _
  simp only [unitForm, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries',
    coeffSemilinearAut.coeffMap_qExpand]
  rw [← RingHom.comp_apply (PowerSeries.map f), ← PowerSeries.map_comp, h1,
    ← RingHom.comp_apply (PowerSeries.map f) (PowerSeries.map (Int.castRingHom R)), ← PowerSeries.map_comp, h1]

end AnyRing

section AnyField

variable (K : Type*) [Field K] (q : ℕ) [NeZero q]

private theorem eta_ne_zero :
    HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)) ≠ 0 := by
  intro h
  have h0 := congrArg (fun s : LaurentSeries K => s.coeff 0) h
  simp only [HahnSeries.coeff_zero] at h0
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff] at h0
  simp [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_dedekindEtaUnit] at h0

private theorem unitForm_eq_field :
    unitForm K q =
      HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K
          (dedekindEtaUnit.map (Int.castRingHom K)) *
        (qExpand K q (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K
          (dedekindEtaUnit.map (Int.castRingHom K))))⁻¹ := by
  have hne : qExpand K q (HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K
      (dedekindEtaUnit.map (Int.castRingHom K))) ≠ 0 := by
    intro h
    rw [← map_zero (qExpand K q)] at h
    exact mul_ne_zero (HahnSeries.single_ne_zero one_ne_zero) (eta_ne_zero K) (qExpand_injective q h)
  rw [eq_mul_inv_iff_mul_eq₀ hne, unitForm, map_mul, qExpand_single, mul_one]
  have hU : (HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnitInv.map (Int.castRingHom K))) *
      HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)) = 1 := by
    rw [← map_mul, ← map_mul (PowerSeries.map (Int.castRingHom K)), mul_comm dedekindEtaUnitInv,
      dedekindEtaUnit_mul_inv, map_one, map_one]
  have hS : (HahnSeries.single (-(q : ℤ)) (1 : K)) * HahnSeries.single ((q : ℤ)) (1 : K) = 1 := by
    rw [HahnSeries.single_mul_single, neg_add_cancel, one_mul, HahnSeries.single_zero_one]
  calc HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)) *
        (HahnSeries.single (-(q : ℤ)) 1 * qExpand K q (HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnitInv.map (Int.castRingHom K)))) *
        (HahnSeries.single ((q : ℤ)) 1 * qExpand K q (HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K))))
      = HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)) *
        ((HahnSeries.single (-(q : ℤ)) 1 * HahnSeries.single ((q : ℤ)) 1) *
          qExpand K q (HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnitInv.map (Int.castRingHom K)) *
            HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)))) := by
          rw [map_mul]; ring
    _ = _ := by rw [hS, hU, map_one (qExpand K q)]; ring

end AnyField

section Rational

variable (q : ℕ) [NeZero q]

private theorem modularUnitSeries_eq_unitForm : modularUnitSeries q = unitForm ℚ q := by
  rw [unitForm_eq_field, modularUnitSeries, deltaSeriesN, deltaSeries, dedekindEtaUnitQ]

variable (L : Type*) [Field L] [Algebra ℚ L]

private theorem coeffEmb_modularUnitSeries : coeffEmb L (modularUnitSeries q) = unitForm L q := by
  rw [modularUnitSeries_eq_unitForm, coeffEmb, coeffMap_unitForm]

end Rational
end UnitForms

section Ultrametric
open Polynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem ord_pow (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  simpa using v.ord_zpow f n

private theorem ord_const {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hc' : algebraMap K F c ≠ 0 := (_root_.map_ne_zero (algebraMap K F)).mpr hc
  have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
    ⟨⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simp [hc']), Subtype.ext (by simp [hc'])⟩, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rw [hu] at this
  exact this

private theorem ord_add_ge {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have hvf := v.adicValuation_ne_zero hf
  have hvg := v.adicValuation_ne_zero hg
  have hvfg := v.adicValuation_ne_zero hfg
  have hmax := v.adicValuation.map_add f g
  rcases le_total (v.adicValuation f) (v.adicValuation g) with h | h
  · rw [max_eq_right h] at hmax
    have hlog := (WithZero.log_le_log hvfg hvg).mpr hmax
    refine le_trans (min_le_right _ _) ?_
    simp only [Place.ord]
    exact neg_le_neg hlog
  · rw [max_eq_left h] at hmax
    have hlog := (WithZero.log_le_log hvfg hvf).mpr hmax
    refine le_trans (min_le_left _ _) ?_
    simp only [Place.ord]
    exact neg_le_neg hlog

private theorem ord_add_eq_left {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by
  have hvf := v.adicValuation_ne_zero hf
  have hvg := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← WithZero.log_lt_log hvg hvf]
    simp only [Place.ord] at h
    linarith
  simp only [Place.ord, v.adicValuation.map_add_eq_of_lt_left hlt]

private theorem ord_sum_ge {ι : Type*} (s : Finset ι) (t : ι → F) (b : ℤ)
    (ht : ∀ i ∈ s, t i = 0 ∨ b ≤ v.ord (t i)) :
    (∑ i ∈ s, t i) = 0 ∨ b ≤ v.ord (∑ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hts : (∑ i ∈ s, t i) = 0 ∨ b ≤ v.ord (∑ i ∈ s, t i) :=
      ih fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have hta := ht a (Finset.mem_insert_self a s)
    rcases hta with hta | hta
    · rw [hta, zero_add]; exact hts
    rcases hts with hts | hts
    · rw [hts, add_zero]; right; exact hta
    by_cases ha0 : t a = 0
    · rw [ha0, zero_add]; right; exact hts
    by_cases hs0 : (∑ i ∈ s, t i) = 0
    · rw [hs0, add_zero]; right; exact hta
    by_cases hsum : t a + ∑ i ∈ s, t i = 0
    · left; exact hsum
    · right
      exact le_trans (le_min hta hts) (ord_add_ge v ha0 hs0 hsum)

private theorem ord_aeval_ge {x : F} (hx : v.ord x < 0) (hx0 : x ≠ 0) {m : ℕ} (G : K[X])
    (hG : G.natDegree ≤ m) : aeval x G = 0 ∨ (m : ℤ) * v.ord x ≤ v.ord (aeval x G) := by
  rw [Polynomial.aeval_eq_sum_range]
  refine ord_sum_ge v _ _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  by_cases hc : G.coeff i = 0
  · left; simp [hc]
  · right
    rw [Algebra.smul_def, v.ord_mul ((_root_.map_ne_zero _).mpr hc) (pow_ne_zero _ hx0), ord_const v hc,
      zero_add, ord_pow]
    have hi' : (i : ℤ) ≤ m := by exact_mod_cast (Nat.lt_succ_iff.mp hi).trans hG
    nlinarith

private theorem ord_aeval_eq {x : F} (hx : v.ord x < 0) (hx0 : x ≠ 0) (G : K[X]) (hG : G ≠ 0) :
    v.ord (aeval x G) = (G.natDegree : ℤ) * v.ord x := by
  set n := G.natDegree with hn
  have hlc : G.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hG
  have htop : v.ord (aeval x (C G.leadingCoeff * X ^ n)) = (n : ℤ) * v.ord x := by
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
      v.ord_mul ((_root_.map_ne_zero _).mpr hlc) (pow_ne_zero _ hx0), ord_const v hlc, zero_add, ord_pow]
  have htop0 : aeval x (C G.leadingCoeff * X ^ n) ≠ 0 := by
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    exact mul_ne_zero ((_root_.map_ne_zero _).mpr hlc) (pow_ne_zero _ hx0)
  have hsplit : G = C G.leadingCoeff * X ^ n + G.eraseLead := by
    rw [add_comm, Polynomial.eraseLead_add_C_mul_X_pow]
  by_cases he : G.eraseLead = 0
  · rw [hsplit, he, add_zero, htop]
  · rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · exfalso
      apply he
      rw [Polynomial.eq_C_of_natDegree_eq_zero hn0, Polynomial.eraseLead_C]
    · have hdeg : G.eraseLead.natDegree ≤ n - 1 := Polynomial.eraseLead_natDegree_le G
      by_cases hr : aeval x G.eraseLead = 0
      · rw [hsplit, map_add, hr, add_zero, htop]
      · have hge : ((n - 1 : ℕ) : ℤ) * v.ord x ≤ v.ord (aeval x G.eraseLead) :=
          (ord_aeval_ge v hx hx0 G.eraseLead hdeg).resolve_left hr
        have hlt : (n : ℤ) * v.ord x < ((n - 1 : ℕ) : ℤ) * v.ord x := by
          have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          rw [this]; nlinarith
        rw [hsplit, map_add, ord_add_eq_left v htop0 hr (by rw [htop]; exact lt_of_lt_of_le hlt hge),
          htop]
end Ultrametric

section Assembly

variable {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}

private theorem coe_residue₁_unit (R : ProlongationTuple P) (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers) :
    ((R.residue₁ ⟨u, h₁⟩ : modularFunctionFieldC k N) : LaurentSeries k) = unitForm k q := by
  have hyu : coeffMap A.subtype (unitForm A q) = (u : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coeffMap_unitForm, hu, coeffEmb_modularUnitSeries]
  have hy : coeffMap A.subtype (unitForm A q) ∈ modularFunctionFieldBar (N * q) := by
    rw [hyu]; exact u.2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (unitForm A q) hy
  have hsub : (⟨u, h₁⟩ : R.R₁.integers) = ⟨⟨coeffMap A.subtype (unitForm A q), hy⟩, h⟩ :=
    Subtype.ext (Subtype.ext hyu.symm)
  rw [hsub, residue₁_apply, R.ι_coe, hres, coeffMap_coeffMap, coeffMap_unitForm]

private theorem exists_residue₁_eq_aeval (R : ProlongationTuple P) (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers) :
    ∃ G : Polynomial k, G.natDegree = q - 1 ∧
      R.residue₁ ⟨u, h₁⟩ = Polynomial.aeval (jGeomGen k N) G := by
  obtain ⟨G, hG, hGeq⟩ := desc k q
  refine ⟨G, hG, Subtype.ext ?_⟩
  rw [coe_residue₁_unit R u hu h₁, unitForm_eq_field, hGeq]
  exact Polynomial.aeval_algHom_apply (modularFunctionFieldC k N).val (jGeomGen k N) G

private theorem ord_jGeomGen_neg (v : Place k (modularFunctionFieldC k N))
    (hv : ¬ IsAffineGeomPlace k N v) : v.ord (jGeomGen k N) < 0 := by
  by_contra hnot
  push Not at hnot
  have hj0 : jGeomGen k N ≠ 0 := by
    intro h0
    have := congrArg (fun x : modularFunctionFieldC k N => (x : LaurentSeries k)) h0
    simp only [coe_jGeomGen, ZeroMemClass.coe_zero] at this
    exact jqModC_ne_zero_def k this
  have hj : jGeomGen k N ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hj0 hnot
  apply hv
  refine ⟨hj, ?_⟩
  obtain ⟨dataN⟩ := nonempty_modularPolynomialData N
  set V := v.toValuationSubring
  have hpair := evalModularPair_jGeomGen_eq_zero k N dataN
  have hint : IsIntegral V (jNGeomGen k N) := by
    refine ⟨dataN.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom V) (⟨jGeomGen k N, hj⟩ : V)),
      dataN.monic.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap V (modularFunctionFieldC k N)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom V) (⟨jGeomGen k N, hj⟩ : V)) =
        Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionFieldC k N)) (jGeomGen k N) := by
      refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
      simp
    rw [hcomp]
    exact hpair
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

end Assembly

end G2Reduction

open G2Reduction in
theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    v.ord (R.residue₁ ⟨u, h₁⟩) = ((q : ℤ) - 1) * v.ord ⟨jqModC k, jqModC_mem k N⟩ := by
  have _ := hqN
  obtain ⟨G, hG, hres⟩ := exists_residue₁_eq_aeval R u hu h₁
  have hjneg := ord_jGeomGen_neg v hv
  have hj0 : jGeomGen k N ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hjneg; exact lt_irrefl _ hjneg
  have hG0 : G ≠ 0 := by
    rintro rfl
    have h2 := (Fact.out : q.Prime).two_le
    simp at hG; omega
  have hq : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
    have := (Fact.out : q.Prime).one_lt; omega
  rw [hres, ord_aeval_eq v hjneg hj0 G hG0, hG, hq]
  rfl

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_modularUnit_eq_mul_ord_jqModC_of_not_isAffineGeomPlace
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_modularUnit_eq_mul_ord_jqModC_of_not_isAffineGeomPlace (solution)
