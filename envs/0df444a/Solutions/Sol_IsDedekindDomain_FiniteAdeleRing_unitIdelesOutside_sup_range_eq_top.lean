-- Prove2me | solution 1 for IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_sup_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4079fdfd-74b9-5425-94dd-6a1ab825e576

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_FiniteAdeleRing_unitIdelesOutside_sup_range_eq_top

set_option autoImplicit false
open scoped nonZeroDivisors

namespace P2mS26JS

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors

noncomputable section

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

lemma apply_mul_inv_apply (v : HeightOneSpectrum R) (δ : (FiniteAdeleRing R K)ˣ) :
    (δ : FiniteAdeleRing R K) v * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = 1 := by
  change ((δ : FiniteAdeleRing R K) * ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)) v = 1
  rw [Units.mul_inv]
  rfl

lemma valued_apply_ne_zero (v : HeightOneSpectrum R) (δ : (FiniteAdeleRing R K)ˣ) :
    Valued.v ((δ : FiniteAdeleRing R K) v) ≠ 0 := by
  intro h
  have h1 := congrArg Valued.v (apply_mul_inv_apply R K v δ)
  rw [Valuation.map_mul, Valuation.map_one, h, zero_mul] at h1
  exact zero_ne_one h1

def expAt (v : HeightOneSpectrum R) (δ : (FiniteAdeleRing R K)ˣ) : ℤ :=
  -log (Valued.v ((δ : FiniteAdeleRing R K) v))

lemma expAt_one (v : HeightOneSpectrum R) : expAt R K v 1 = 0 := by
  simp only [expAt, Units.val_one]
  change -log (Valued.v (1 : v.adicCompletion K)) = 0
  rw [Valuation.map_one, log_one, neg_zero]

lemma expAt_mul (v : HeightOneSpectrum R) (x y : (FiniteAdeleRing R K)ˣ) :
    expAt R K v (x * y) = expAt R K v x + expAt R K v y := by
  simp only [expAt, Units.val_mul]
  change -log (Valued.v ((x : FiniteAdeleRing R K) v * (y : FiniteAdeleRing R K) v)) = _
  rw [Valuation.map_mul, log_mul (valued_apply_ne_zero R K v x) (valued_apply_ne_zero R K v y)]
  ring

lemma expAt_inv (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    expAt R K v x⁻¹ = -expAt R K v x := by
  have h := expAt_mul R K v x x⁻¹
  rw [mul_inv_cancel, expAt_one] at h
  omega

lemma expAt_eq_zero_iff (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    expAt R K v x = 0 ↔ Valued.v ((x : FiniteAdeleRing R K) v) = 1 := by
  rw [expAt, neg_eq_zero]
  constructor
  · intro h
    have h2 := exp_log (valued_apply_ne_zero R K v x)
    rw [← h2, h, exp_zero]
  · intro h
    rw [h, log_one]

lemma eq_one_of_mul_eq_one_of_le_one {a b : ℤᵐ⁰} (hab : a * b = 1) (ha : a ≤ 1) (hb : b ≤ 1) : a = 1 := by
  have hb1 : b = 1 := le_antisymm hb (by
    calc (1 : ℤᵐ⁰) = a * b := hab.symm
    _ ≤ 1 * b := by gcongr
    _ = b := one_mul b)
  rw [hb1, mul_one] at hab
  exact hab

lemma expAt_eq_zero_of_integral {v : HeightOneSpectrum R} {x : (FiniteAdeleRing R K)ˣ}
    (hx : Valued.v ((x : FiniteAdeleRing R K) v) ≤ 1)
    (hxi : Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) ≤ 1) :
    expAt R K v x = 0 := by
  rw [expAt_eq_zero_iff]
  have hmul : Valued.v ((x : FiniteAdeleRing R K) v) *
      Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) = 1 := by
    have h2 := congrArg Valued.v (apply_mul_inv_apply R K v x)
    rwa [Valuation.map_mul, Valuation.map_one] at h2
  exact eq_one_of_mul_eq_one_of_le_one hmul hx hxi

lemma integral_of_expAt_eq_zero {v : HeightOneSpectrum R} {x : (FiniteAdeleRing R K)ˣ} (h : expAt R K v x = 0) :
    Valued.v ((x : FiniteAdeleRing R K) v) ≤ 1 ∧
      Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) ≤ 1 := by
  have h1 : Valued.v ((x : FiniteAdeleRing R K) v) = 1 := (expAt_eq_zero_iff R K v x).1 h
  have h2 : Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) = 1 := by
    rw [← expAt_eq_zero_iff, expAt_inv, h, neg_zero]
  exact ⟨h1.le, h2.le⟩

lemma finite_expAt_ne_zero (x : (FiniteAdeleRing R K)ˣ) :
    {v : HeightOneSpectrum R | expAt R K v x ≠ 0}.Finite := by
  have hx : ∀ᶠ v in Filter.cofinite, (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
    (x : FiniteAdeleRing R K).2
  have hxi : ∀ᶠ v in Filter.cofinite,
      ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
    ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K).2
  have hboth := hx.and hxi
  rw [Filter.eventually_cofinite] at hboth
  refine hboth.subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  intro hcon
  exact hv (expAt_eq_zero_of_integral R K
    ((mem_adicCompletionIntegers R K v).mp hcon.1) ((mem_adicCompletionIntegers R K v).mp hcon.2))

omit [IsDedekindDomain R] in
lemma coeIdeal_asIdeal_ne_zero (v : HeightOneSpectrum R) : (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot

lemma mulSupport_zpow_subset (e : HeightOneSpectrum R → ℤ) :
    (Function.mulSupport fun v => (v.asIdeal : FractionalIdeal R⁰ K) ^ (e v)) ⊆ {v | e v ≠ 0} := by
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  intro h0
  exact hv (by rw [show e v = 0 from h0, zpow_zero])

def assoc (x : (FiniteAdeleRing R K)ˣ) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (expAt R K v x)

lemma assoc_ne_zero (x : (FiniteAdeleRing R K)ˣ) : assoc R K x ≠ 0 := by
  rw [assoc, finprod_eq_prod_of_mulSupport_subset _ (s := (finite_expAt_ne_zero R K x).toFinset)
    (by simpa using mulSupport_zpow_subset R K _)]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (coeIdeal_asIdeal_ne_zero R K v)

lemma count_assoc (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    FractionalIdeal.count K v (assoc R K x) = expAt R K v x :=
  FractionalIdeal.count_finprod K v _ (Filter.eventually_cofinite.mpr (by simpa using finite_expAt_ne_zero R K x))

theorem count_spanSingleton_eq_neg_log_valuation (v : HeightOneSpectrum R) (u : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (u : K)) = -log (v.valuation K (u : K)) := by
  classical
  rw [← valuationOfNeZeroToFun_eq v u]
  set n : R := (IsLocalization.sec R⁰ (u : K)).1 with hn
  set d : ↥R⁰ := (IsLocalization.sec R⁰ (u : K)).2 with hd
  have hsec : (u : K) * algebraMap R K (d : R) = algebraMap R K n := IsLocalization.sec_spec R⁰ (u : K)
  have hd0 : algebraMap R K (d : R) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have h_aJ : FractionalIdeal.spanSingleton R⁰ (u : K) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K (d : R)))⁻¹ * ↑(Ideal.span {n}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    field_simp
    linear_combination hsec
  rw [FractionalIdeal.count_well_defined K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr u.ne_zero) h_aJ]
  show _ = -log ((valuationOfNeZeroToFun v u : Multiplicative ℤ) : ℤᵐ⁰)
  rw [valuationOfNeZeroToFun]
  simp only [← hn, ← hd]
  rw [show ((Multiplicative.ofAdd _ : Multiplicative ℤ) : ℤᵐ⁰) = exp _ from rfl, log_exp]
  ring

abbrev prin (u : Kˣ) : (FiniteAdeleRing R K)ˣ :=
  Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u

lemma valued_algebraMap_apply (v : HeightOneSpectrum R) (k : K) :
    Valued.v ((algebraMap K (FiniteAdeleRing R K) k) v) = v.valuation K k :=
  valuedAdicCompletion_eq_valuation' v k

lemma expAt_prin (v : HeightOneSpectrum R) (u : Kˣ) : expAt R K v (prin R K u) = -log (v.valuation K (u : K)) := by
  unfold expAt
  rw [Units.coe_map, MonoidHom.coe_coe, valued_algebraMap_apply]

end

end P2mS26JS

open scoped nonZeroDivisors in

theorem solution
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum R))
    (hS : ∀ c : ClassGroup R, ∃ I : (Ideal R)⁰, ClassGroup.mk0 I = c ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.asIdeal ∣ (I : Ideal R) → v ∈ S) :
    IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S ⊔
      (Units.map (algebraMap K (IsDedekindDomain.FiniteAdeleRing R K) :
        K →* IsDedekindDomain.FiniteAdeleRing R K)).range = ⊤ := by
  classical
  rw [eq_top_iff]
  rintro δ -

  obtain ⟨I, hI, hIS⟩ := hS (ClassGroup.mk (K := K) (Units.mk0 (P2mS26JS.assoc R K δ) (P2mS26JS.assoc_ne_zero R K δ)))⁻¹
  have h1 : ClassGroup.mk (K := K) (Units.mk0 (P2mS26JS.assoc R K δ) (P2mS26JS.assoc_ne_zero R K δ) *
      FractionalIdeal.mk0 K I) = 1 := by
    rw [map_mul, ClassGroup.mk_mk0, hI, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨a, ha⟩ := h1.principal
  have hprod : P2mS26JS.assoc R K δ * ((I : Ideal R) : FractionalIdeal R⁰ K) =
      FractionalIdeal.spanSingleton R⁰ a := by
    apply FractionalIdeal.coeToSubmodule_injective
    change ((P2mS26JS.assoc R K δ * ((I : Ideal R) : FractionalIdeal R⁰ K) : FractionalIdeal R⁰ K) : Submodule R K) =
      ((FractionalIdeal.spanSingleton R⁰ a : FractionalIdeal R⁰ K) : Submodule R K)
    rw [FractionalIdeal.coe_spanSingleton]
    simpa [FractionalIdeal.coe_mk0] using ha
  have hI0 : ((I : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (nonZeroDivisors.coe_ne_zero I)
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, FractionalIdeal.spanSingleton_zero] at hprod
    exact mul_ne_zero (P2mS26JS.assoc_ne_zero R K δ) hI0 hprod
  set u : Kˣ := Units.mk0 a ha0 with hu

  have hmem : δ * (P2mS26JS.prin R K u)⁻¹ ∈ IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S := by
    intro v hv
    have hcount : FractionalIdeal.count K v ((I : Ideal R) : FractionalIdeal R⁰ K) = 0 := by
      by_contra hne
      rw [FractionalIdeal.count_coe K v (nonZeroDivisors.coe_ne_zero I)] at hne
      exact hv (hIS v ((Associates.count_ne_zero_iff_dvd (nonZeroDivisors.coe_ne_zero I) v.irreducible).1
        (by exact_mod_cast hne)))
    have hexp : P2mS26JS.expAt R K v (δ * (P2mS26JS.prin R K u)⁻¹) = 0 := by
      rw [P2mS26JS.expAt_mul, P2mS26JS.expAt_inv, P2mS26JS.expAt_prin,
        ← P2mS26JS.count_spanSingleton_eq_neg_log_valuation, hu, Units.val_mk0, ← hprod,
        FractionalIdeal.count_mul K v (P2mS26JS.assoc_ne_zero R K δ) hI0, P2mS26JS.count_assoc, hcount]
      ring
    obtain ⟨h1, h2⟩ := P2mS26JS.integral_of_expAt_eq_zero R K hexp
    exact ⟨(IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).2 h1,
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers R K v).2 h2⟩
  rw [← inv_mul_cancel_right δ (P2mS26JS.prin R K u)]
  exact Subgroup.mul_mem_sup hmem ⟨u, rfl⟩

end S_IsDedekindDomain_FiniteAdeleRing_unitIdelesOutside_sup_range_eq_top
end P2MW
export P2MW.S_IsDedekindDomain_FiniteAdeleRing_unitIdelesOutside_sup_range_eq_top (solution)
