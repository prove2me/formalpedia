-- Prove2me | solution 1 for IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/60c1e6d4-0d97-5fbd-a222-74904bcfaa36

import Mathlib
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff

set_option autoImplicit false
p2m_open "IsDedekindDomain P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.IsDedekindDomain"
open scoped nonZeroDivisors

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "IsDedekindDomain P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero"

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "FiniteAdeleRing mk HeightOneSpectrum FiniteAdeleRing.unitIdeles FiniteAdeleRing.unitIdelesOutside FiniteAdeleRing.unitIdeles_le_unitIdelesOutside"
namespace FiniteAdeleRing
p2m_export "IsDedekindDomain.FiniteAdeleRing" "ext unitIdeles unitIdelesOutside unitIdeles_le_unitIdelesOutside"
namespace Ws25E5
p2m_open "IsDedekindDomain.FiniteAdeleRing IsDedekindDomain"

noncomputable section

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

lemma far_mul_apply (x y : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (x * y) v = x v * y v := rfl

lemma far_one_apply (v : HeightOneSpectrum R) : (1 : FiniteAdeleRing R K) v = 1 := rfl

def evalAt (v : HeightOneSpectrum R) : (FiniteAdeleRing R K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (RestrictedProduct.evalRingHom _ v).toMonoidHom

@[scoped simp] lemma evalAt_val (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    (evalAt R K v x : v.adicCompletion K) = (x : FiniteAdeleRing R K) v := rfl

lemma valued_ne_zero (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    Valued.v ((x : FiniteAdeleRing R K) v) ≠ 0 := by
  rw [← evalAt_val]
  simp only [ne_eq, map_eq_zero]
  exact (evalAt R K v x).ne_zero

def expAt (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) : ℤ :=
  -log (Valued.v ((x : FiniteAdeleRing R K) v))

lemma expAt_one (v : HeightOneSpectrum R) : expAt R K v 1 = 0 := by
  rw [expAt, Units.val_one, far_one_apply, map_one, log_one, neg_zero]

lemma expAt_mul (v : HeightOneSpectrum R) (x y : (FiniteAdeleRing R K)ˣ) :
    expAt R K v (x * y) = expAt R K v x + expAt R K v y := by
  simp only [expAt]
  rw [Units.val_mul, far_mul_apply, map_mul,
    log_mul (valued_ne_zero R K v x) (valued_ne_zero R K v y)]
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
    rw [← exp_log (valued_ne_zero R K v x), h, exp_zero]
  · intro h
    rw [h, log_one]

private lemma eq_one_of_mul_eq_one_of_le_one {a b : ℤᵐ⁰} (hab : a * b = 1)
    (ha : a ≤ 1) (hb : b ≤ 1) : a = 1 := by
  have hb1 : b = 1 := le_antisymm hb (by
    calc (1 : ℤᵐ⁰) = a * b := hab.symm
    _ ≤ 1 * b := by gcongr
    _ = b := one_mul b)
  rw [hb1, mul_one] at hab
  exact hab

theorem expAt_eq_zero_of_integral {v : HeightOneSpectrum R} {x : (FiniteAdeleRing R K)ˣ}
    (hx : Valued.v ((x : FiniteAdeleRing R K) v) ≤ 1)
    (hxi : Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) ≤ 1) :
    expAt R K v x = 0 := by
  rw [expAt_eq_zero_iff]
  have hmul : Valued.v ((x : FiniteAdeleRing R K) v) *
      Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) = 1 := by
    rw [← map_mul, ← far_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      far_one_apply, map_one]
  exact eq_one_of_mul_eq_one_of_le_one hmul hx hxi

theorem finite_support_expAt (x : (FiniteAdeleRing R K)ˣ) :
    {v : HeightOneSpectrum R | expAt R K v x ≠ 0}.Finite := by
  have hx : ∀ᶠ v in Filter.cofinite,
      (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K := (x : FiniteAdeleRing R K).2
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
    ((mem_adicCompletionIntegers R K v).mp hcon.1)
    ((mem_adicCompletionIntegers R K v).mp hcon.2))

omit [IsDedekindDomain R] in
lemma coeIdeal_asIdeal_ne_zero (v : HeightOneSpectrum R) :
    (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot

lemma zpow_asIdeal_ne_zero (v : HeightOneSpectrum R) (n : ℤ) :
    (v.asIdeal : FractionalIdeal R⁰ K) ^ n ≠ 0 :=
  zpow_ne_zero n (coeIdeal_asIdeal_ne_zero R K v)

lemma mulSupport_zpow_subset (e : HeightOneSpectrum R → ℤ) :
    (Function.mulSupport fun v => (v.asIdeal : FractionalIdeal R⁰ K) ^ (e v)) ⊆
      {v | e v ≠ 0} := by
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  simp only [Set.mem_setOf_eq]
  intro h0
  exact hv (by rw [h0, zpow_zero])

def assocIdeal (x : (FiniteAdeleRing R K)ˣ) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (expAt R K v x)

lemma assocIdeal_ne_zero (x : (FiniteAdeleRing R K)ˣ) : assocIdeal R K x ≠ 0 := by
  rw [assocIdeal, finprod_eq_prod_of_mulSupport_subset _
    (s := (finite_support_expAt R K x).toFinset)
    (by simpa using mulSupport_zpow_subset R K _)]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_asIdeal_ne_zero R K v _

theorem count_assocIdeal (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    FractionalIdeal.count K v (assocIdeal R K x) = expAt R K v x :=
  FractionalIdeal.count_finprod K v _ (Filter.eventually_cofinite.mpr
    (by simpa using finite_support_expAt R K x))

theorem assocIdeal_mul (x y : (FiniteAdeleRing R K)ˣ) :
    assocIdeal R K (x * y) = assocIdeal R K x * assocIdeal R K y := by
  unfold assocIdeal
  rw [← finprod_mul_distrib
    ((finite_support_expAt R K x).subset (mulSupport_zpow_subset R K _))
    ((finite_support_expAt R K y).subset (mulSupport_zpow_subset R K _))]
  apply finprod_congr
  intro v
  rw [expAt_mul, zpow_add₀ (coeIdeal_asIdeal_ne_zero R K v)]

theorem fractionalIdeal_eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J :=
  calc I = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
        (FractionalIdeal.count K v I) :=
      (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI).symm
  _ = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
        (FractionalIdeal.count K v J) := finprod_congr fun v => by rw [h v]
  _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ

def contentHom : (FiniteAdeleRing R K)ˣ →* ClassGroup R where
  toFun x := ClassGroup.mk (K := K) (Units.mk0 (assocIdeal R K x) (assocIdeal_ne_zero R K x))
  map_one' := by
    have h1 : assocIdeal R K (1 : (FiniteAdeleRing R K)ˣ) = 1 := by
      unfold assocIdeal
      rw [finprod_eq_one_of_forall_eq_one]
      intro v
      rw [expAt_one, zpow_zero]
    rw [← map_one (ClassGroup.mk (R := R) (K := K))]
    congr 1
    exact Units.ext (by simpa using h1)
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    exact Units.ext (by simpa using assocIdeal_mul R K x y)

@[scoped simp] lemma contentHom_apply (x : (FiniteAdeleRing R K)ˣ) :
    contentHom R K x = ClassGroup.mk (K := K) (Units.mk0 (assocIdeal R K x) (assocIdeal_ne_zero R K x)) :=
  rfl

theorem count_spanSingleton_eq_neg_log_valuation (v : HeightOneSpectrum R) (u : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (u : K)) =
      -log (v.valuation K (u : K)) := by
  classical
  rw [← valuationOfNeZeroToFun_eq v u]
  set n : R := (IsLocalization.sec R⁰ (u : K)).1 with hn
  set d : ↥R⁰ := (IsLocalization.sec R⁰ (u : K)).2 with hd
  have hsec : (u : K) * algebraMap R K (d : R) = algebraMap R K n :=
    IsLocalization.sec_spec R⁰ (u : K)
  have hd0 : algebraMap R K (d : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have h_aJ : FractionalIdeal.spanSingleton R⁰ (u : K) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K (d : R)))⁻¹ * ↑(Ideal.span {n}) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    field_simp
    linear_combination hsec
  rw [FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr u.ne_zero) h_aJ]
  show _ = -log ((valuationOfNeZeroToFun v u : Multiplicative ℤ) : ℤᵐ⁰)
  rw [valuationOfNeZeroToFun]
  simp only [← hn, ← hd]
  rw [show ((Multiplicative.ofAdd _ : Multiplicative ℤ) : ℤᵐ⁰) = exp _ from rfl, log_exp]
  ring

lemma valued_coe_eq_valuation (v : HeightOneSpectrum R) (k : K) :
    Valued.v ((algebraMap K (FiniteAdeleRing R K) k) v) = v.valuation K k := by
  show Valued.v ((k : v.adicCompletion K)) = _
  exact valuedAdicCompletion_eq_valuation' v k

theorem expAt_principal (v : HeightOneSpectrum R) (u : Kˣ) :
    expAt R K v (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u) =
      -log (v.valuation K (u : K)) := by
  unfold expAt
  rw [Units.coe_map, MonoidHom.coe_coe, valued_coe_eq_valuation]

theorem contentHom_principal (u : Kˣ) :
    contentHom R K (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u)
      = 1 := by
  rw [contentHom_apply, ClassGroup.mk_eq_one_iff]
  have key : assocIdeal R K
      (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u) =
      FractionalIdeal.spanSingleton R⁰ (u : K) := by
    apply fractionalIdeal_eq_of_count_eq R K (assocIdeal_ne_zero R K _)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr u.ne_zero)
    intro v
    rw [count_assocIdeal, count_spanSingleton_eq_neg_log_valuation, expAt_principal]
  simp only [Units.val_mk0, key]
  rw [FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(u : K), rfl⟩⟩

lemma expAt_eq_zero_of_mem_unitIdeles {x : (FiniteAdeleRing R K)ˣ} (h : x ∈ unitIdeles R K)
    (v : HeightOneSpectrum R) : expAt R K v x = 0 :=
  expAt_eq_zero_of_integral R K ((mem_adicCompletionIntegers R K v).mp (h.1 v))
    ((mem_adicCompletionIntegers R K v).mp (h.2 v))

lemma mem_unitIdeles_of_expAt_eq_zero {x : (FiniteAdeleRing R K)ˣ}
    (h : ∀ v : HeightOneSpectrum R, expAt R K v x = 0) : x ∈ unitIdeles R K := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · exact (mem_adicCompletionIntegers R K v).mpr ((expAt_eq_zero_iff R K v x).mp (h v)).le
  · have h' : expAt R K v x⁻¹ = 0 := by rw [expAt_inv, h v, neg_zero]
    exact (mem_adicCompletionIntegers R K v).mpr ((expAt_eq_zero_iff R K v x⁻¹).mp h').le

theorem contentHom_eq_one_of_mem_unitIdeles {x : (FiniteAdeleRing R K)ˣ} (h : x ∈ unitIdeles R K) :
    contentHom R K x = 1 := by
  have h1 : assocIdeal R K x = 1 := by
    unfold assocIdeal
    rw [finprod_eq_one_of_forall_eq_one]
    intro v
    rw [expAt_eq_zero_of_mem_unitIdeles R K h v, zpow_zero]
  rw [contentHom_apply, ← map_one (ClassGroup.mk (R := R) (K := K))]
  congr 1
  exact Units.ext (by simpa using h1)

theorem ker_contentHom_eq :
    (contentHom R K).ker = unitIdeles R K ⊔
      (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)).range := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker, contentHom_apply, ClassGroup.mk_eq_one_iff] at hx
    obtain ⟨a, ha⟩ := hx.principal
    have ha' : assocIdeal R K x = FractionalIdeal.spanSingleton R⁰ a := by
      apply FractionalIdeal.coeToSubmodule_injective
      show (assocIdeal R K x : Submodule R K) = (FractionalIdeal.spanSingleton R⁰ a : Submodule R K)
      rw [FractionalIdeal.coe_spanSingleton]
      simpa using ha
    have ha0 : a ≠ 0 := by
      intro h0
      apply assocIdeal_ne_zero R K x
      rw [ha', h0, FractionalIdeal.spanSingleton_zero]
    set u : Kˣ := Units.mk0 a ha0 with hu
    set p : (FiniteAdeleRing R K)ˣ :=
      Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u with hp
    have hquot : x * p⁻¹ ∈ unitIdeles R K := by
      apply mem_unitIdeles_of_expAt_eq_zero
      intro v
      rw [expAt_mul, expAt_inv]
      have h1 : expAt R K v x = FractionalIdeal.count K v (assocIdeal R K x) :=
        (count_assocIdeal R K v x).symm
      have h2 : expAt R K v p = FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton R⁰ (u : K)) := by
        rw [hp, expAt_principal, count_spanSingleton_eq_neg_log_valuation]
      rw [h1, h2, ha']
      simp [hu]
    have hxp : x = (x * p⁻¹) * p := by group
    rw [hxp]
    exact Subgroup.mul_mem_sup hquot ⟨u, rfl⟩
  · rw [sup_le_iff]
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      exact contentHom_eq_one_of_mem_unitIdeles R K hx
    · rintro _ ⟨u, rfl⟩
      rw [MonoidHom.mem_ker]
      exact contentHom_principal R K u

theorem assocIdeal_principal (u : Kˣ) :
    assocIdeal R K (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u) =
      FractionalIdeal.spanSingleton R⁰ (u : K) := by
  apply fractionalIdeal_eq_of_count_eq R K (assocIdeal_ne_zero R K _)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr u.ne_zero)
  intro v
  rw [count_assocIdeal, count_spanSingleton_eq_neg_log_valuation, expAt_principal]

theorem assocIdeal_one : assocIdeal R K (1 : (FiniteAdeleRing R K)ˣ) = 1 := by
  unfold assocIdeal
  rw [finprod_eq_one_of_forall_eq_one]
  intro v
  rw [expAt_one, zpow_zero]

def phi : (FiniteAdeleRing R K)ˣ →* (FractionalIdeal R⁰ K)ˣ where
  toFun x := Units.mk0 (assocIdeal R K x) (assocIdeal_ne_zero R K x)
  map_one' := Units.ext (by rw [Units.val_mk0, Units.val_one, assocIdeal_one])
  map_mul' x y := Units.ext (by rw [Units.val_mk0, Units.val_mul, Units.val_mk0, Units.val_mk0, assocIdeal_mul])

theorem phi_val (x : (FiniteAdeleRing R K)ˣ) : ((phi R K x : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = assocIdeal R K x := rfl

theorem contentHom_eq_mk_phi (x : (FiniteAdeleRing R K)ˣ) : contentHom R K x = ClassGroup.mk (K := K) (phi R K x) := rfl

theorem phi_principal (u : Kˣ) :
    phi R K (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) u) = toPrincipalIdeal R K u :=
  Units.ext (by rw [phi_val, assocIdeal_principal, coe_toPrincipalIdeal])

theorem count_phi (v : HeightOneSpectrum R) (x : (FiniteAdeleRing R K)ˣ) :
    FractionalIdeal.count K v ((phi R K x : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = expAt R K v x :=
  count_assocIdeal R K v x

theorem ker_phi : (phi R K).ker = unitIdeles R K := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    apply mem_unitIdeles_of_expAt_eq_zero
    intro v
    rw [← count_phi, hx, Units.val_one, FractionalIdeal.count_one]
  · intro hx
    apply Units.ext
    rw [phi_val, Units.val_one]
    unfold assocIdeal
    rw [finprod_eq_one_of_forall_eq_one]
    intro v
    rw [expAt_eq_zero_of_mem_unitIdeles R K hx v, zpow_zero]

private lemma log_exp_neg_one_zpow (n : ℤ) : log ((exp (-1 : ℤ)) ^ n) = -n := by
  rw [← exp_zsmul, log_exp, smul_neg, zsmul_one, Int.cast_id]

theorem exists_forall_expAt_eq (e : HeightOneSpectrum R → ℤ) (he : ∀ᶠ v in Filter.cofinite, e v = 0) :
    ∃ j : (FiniteAdeleRing R K)ˣ, ∀ w : HeightOneSpectrum R, expAt R K w j = e w := by
  classical
  choose π hπ using fun v : HeightOneSpectrum R => valuation_exists_uniformizer K v
  have hval : ∀ v : HeightOneSpectrum R,
      Valued.v ((algebraMap K (FiniteAdeleRing R K) (π v)) v) = exp (-1 : ℤ) := fun v => by
    rw [valued_coe_eq_valuation, hπ v]
  obtain ⟨a, ha⟩ : ∃ a : (v : HeightOneSpectrum R) → v.adicCompletion K, ∀ v, a v = (algebraMap K (FiniteAdeleRing R K) (π v)) v :=
    ⟨_, fun _ => rfl⟩
  have hva : ∀ v, Valued.v (a v) = exp (-1 : ℤ) := fun v => by rw [ha]; exact hval v
  have ha0 : ∀ v, a v ≠ 0 := fun v => by
    intro h
    have := hva v
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  have hmem : ∀ v, e v = 0 → a v ^ e v ∈ v.adicCompletionIntegers K := fun v hv => by
    rw [hv, zpow_zero]; exact one_mem _
  have hmem' : ∀ v, e v = 0 → (a v)⁻¹ ^ e v ∈ v.adicCompletionIntegers K := fun v hv => by
    rw [hv, zpow_zero]; exact one_mem _
  obtain ⟨f, hf⟩ : ∃ f : FiniteAdeleRing R K, ∀ v, f v = a v ^ e v :=
    ⟨⟨fun v => a v ^ e v, he.mono fun v hv => hmem v hv⟩, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : FiniteAdeleRing R K, ∀ v, g v = (a v)⁻¹ ^ e v :=
    ⟨⟨fun v => (a v)⁻¹ ^ e v, he.mono fun v hv => hmem' v hv⟩, fun _ => rfl⟩
  have hfg : f * g = 1 := RestrictedProduct.ext _ _ fun v => by
    show f v * g v = 1
    rw [hf, hg, ← mul_zpow, mul_inv_cancel₀ (ha0 v), one_zpow]
  have hgf : g * f = 1 := by rw [mul_comm]; exact hfg
  refine ⟨⟨f, g, hfg, hgf⟩, fun w => ?_⟩
  rw [expAt]
  show -log (Valued.v (f w)) = e w
  rw [hf, map_zpow₀, hva w, log_exp_neg_one_zpow, neg_neg]

theorem phi_surjective : Function.Surjective (phi R K) := by
  intro I
  obtain ⟨j, hj⟩ := exists_forall_expAt_eq R K (fun v => FractionalIdeal.count K v ((I : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K))
    (FractionalIdeal.finite_factors _)
  refine ⟨j, Units.ext ?_⟩
  rw [phi_val]
  apply fractionalIdeal_eq_of_count_eq R K (assocIdeal_ne_zero R K j) I.ne_zero
  intro v
  rw [count_assocIdeal, hj]

theorem expAt_eq_zero_of_mem_unitIdelesOutside {T : Set (HeightOneSpectrum R)} {x : (FiniteAdeleRing R K)ˣ}
    (hx : x ∈ unitIdelesOutside R K T) {v : HeightOneSpectrum R} (hv : v ∉ T) : expAt R K v x = 0 :=
  expAt_eq_zero_of_integral R K ((mem_adicCompletionIntegers R K v).mp (hx v hv).1)
    ((mem_adicCompletionIntegers R K v).mp (hx v hv).2)

theorem mem_unitIdelesOutside_of_expAt_eq_zero {T : Set (HeightOneSpectrum R)} {x : (FiniteAdeleRing R K)ˣ}
    (h : ∀ v : HeightOneSpectrum R, v ∉ T → expAt R K v x = 0) : x ∈ unitIdelesOutside R K T := by
  intro v hv
  refine ⟨?_, ?_⟩
  · exact (mem_adicCompletionIntegers R K v).mpr ((expAt_eq_zero_iff R K v x).mp (h v hv)).le
  · have h' : expAt R K v x⁻¹ = 0 := by rw [expAt_inv, h v hv, neg_zero]
    exact (mem_adicCompletionIntegers R K v).mpr ((expAt_eq_zero_iff R K v x⁻¹).mp h').le

def Pv (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (coeIdeal_asIdeal_ne_zero R K v)

theorem Pv_val (v : HeightOneSpectrum R) : ((Pv R K v : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = v.asIdeal := rfl

theorem mk_Pv_mem {T : Set (HeightOneSpectrum R)} {v : HeightOneSpectrum R} (hv : v ∈ T) :
    ClassGroup.mk (K := K) (Pv R K v) ∈
      {c : ClassGroup R | ∃ v ∈ T, ∃ h : v.asIdeal ∈ (Ideal R)⁰, ClassGroup.mk0 ⟨v.asIdeal, h⟩ = c} := by
  refine ⟨v, hv, mem_nonZeroDivisors_of_ne_zero v.ne_bot, ?_⟩
  rw [← ClassGroup.mk_mk0 K]
  exact congrArg _ (Units.ext (by rw [FractionalIdeal.coe_mk0, Pv_val]))

theorem mk_phi_mem_closure_of_mem_unitIdelesOutside {T : Set (HeightOneSpectrum R)} {u : (FiniteAdeleRing R K)ˣ}
    (hu : u ∈ unitIdelesOutside R K T) :
    ClassGroup.mk (K := K) (phi R K u) ∈ Subgroup.closure
      {c : ClassGroup R | ∃ v ∈ T, ∃ h : v.asIdeal ∈ (Ideal R)⁰, ClassGroup.mk0 ⟨v.asIdeal, h⟩ = c} := by
  classical
  have hprod : phi R K u = ∏ v ∈ (finite_support_expAt R K u).toFinset, Pv R K v ^ expAt R K v u := by
    apply Units.ext
    rw [phi_val, Units.coe_prod, assocIdeal, finprod_eq_prod_of_mulSupport_subset _
      (s := (finite_support_expAt R K u).toFinset) (by simpa using mulSupport_zpow_subset R K _)]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [Units.val_zpow_eq_zpow_val, Pv_val]
  rw [hprod, map_prod]
  refine Subgroup.prod_mem _ (fun v hv => ?_)
  rw [map_zpow]

  have hvT : v ∈ T := by
    by_contra hvT
    have : expAt R K v u ≠ 0 := by simpa using hv
    exact this (expAt_eq_zero_of_mem_unitIdelesOutside R K hu hvT)
  exact Subgroup.zpow_mem _ (Subgroup.subset_closure (mk_Pv_mem R K hvT)) _

theorem exists_mem_unitIdelesOutside_phi_eq {T : Set (HeightOneSpectrum R)} {v : HeightOneSpectrum R} (hv : v ∈ T) :
    ∃ j ∈ unitIdelesOutside R K T, phi R K j = Pv R K v := by
  classical
  obtain ⟨j, hj⟩ := exists_forall_expAt_eq R K (fun w => if w = v then 1 else 0)
    (by
      refine (Set.finite_singleton v).subset ?_ |> Filter.eventually_cofinite.mpr
      intro w hw
      by_contra hne
      exact hw (if_neg hne))
  refine ⟨j, mem_unitIdelesOutside_of_expAt_eq_zero R K (fun w hw => ?_), Units.ext ?_⟩
  · rw [hj]
    exact if_neg (fun h : w = v => hw (by rw [h]; exact hv))
  · rw [phi_val, Pv_val]
    apply fractionalIdeal_eq_of_count_eq R K (assocIdeal_ne_zero R K j) (coeIdeal_asIdeal_ne_zero R K v)
    intro w
    rw [count_assocIdeal, hj]
    by_cases hw : w = v
    · subst hw; rw [if_pos rfl, FractionalIdeal.count_self]
    · rw [if_neg hw, eq_comm]
      exact FractionalIdeal.count_maximal_coprime K _ (Ne.symm hw)

end

end IsDedekindDomain.FiniteAdeleRing.Ws25E5
p2m_reactivate "P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.IsDedekindDomain P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.IsDedekindDomain.FiniteAdeleRing P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.IsDedekindDomain.FiniteAdeleRing.Ws25E5"
p2m_reactivate "P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.IsDedekindDomain P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.IsDedekindDomain.FiniteAdeleRing"
p2m_reactivate "P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.IsDedekindDomain"

open _root_.IsDedekindDomain _root_.P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff.IsDedekindDomain IsDedekindDomain.FiniteAdeleRing.Ws25E5 in
theorem solution
    (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ φ : (FiniteAdeleRing R K)ˣ →* (FractionalIdeal R⁰ K)ˣ,
      (∀ x : (FiniteAdeleRing R K)ˣ, ((φ x : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
        ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (-(WithZero.log (Valued.v ((x : FiniteAdeleRing R K) v))))) ∧
      (∀ k : Kˣ, φ (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) k) = toPrincipalIdeal R K k) ∧
      Function.Surjective φ ∧
      φ.ker = IsDedekindDomain.FiniteAdeleRing.unitIdeles R K ∧
      (∀ (T : Set (HeightOneSpectrum R)) (x : (FiniteAdeleRing R K)ˣ),
        x ∈ (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)).range ⊔
            IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K T ↔
          ClassGroup.mk K (φ x) ∈ Subgroup.closure
            {c : ClassGroup R | ∃ v ∈ T, ∃ h : v.asIdeal ∈ (Ideal R)⁰, ClassGroup.mk0 ⟨v.asIdeal, h⟩ = c}) := by
  classical
  refine ⟨phi R K, fun x => rfl, phi_principal R K, phi_surjective R K, ker_phi R K, fun T x => ?_⟩
  constructor
  ·
    intro hx
    obtain ⟨p, hp, u, hu, rfl⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨k, rfl⟩ := hp
    rw [map_mul, map_mul, phi_principal]
    have h1 : ClassGroup.mk (K := K) (toPrincipalIdeal R K k) = 1 := by
      rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
      exact ⟨⟨(k : K), rfl⟩⟩
    rw [h1, one_mul]
    exact mk_phi_mem_closure_of_mem_unitIdelesOutside R K hu
  ·
    intro hx

    have hle : Subgroup.closure {c : ClassGroup R | ∃ v ∈ T, ∃ h : v.asIdeal ∈ (Ideal R)⁰, ClassGroup.mk0 ⟨v.asIdeal, h⟩ = c} ≤
        (IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K T).map ((ClassGroup.mk (K := K)).comp (phi R K)) := by
      rw [Subgroup.closure_le]
      rintro c ⟨v, hv, h, rfl⟩
      obtain ⟨j, hj, hjv⟩ := exists_mem_unitIdelesOutside_phi_eq R K hv
      refine ⟨j, hj, ?_⟩
      rw [MonoidHom.comp_apply, hjv, ← ClassGroup.mk_mk0 K]
      exact congrArg _ (Units.ext (by rw [FractionalIdeal.coe_mk0, Pv_val]))
    obtain ⟨u, hu, hux⟩ := hle hx

    have hker : x * u⁻¹ ∈ (contentHom R K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, contentHom_eq_mk_phi, contentHom_eq_mk_phi]
      rw [MonoidHom.comp_apply] at hux
      rw [← hux, mul_inv_cancel]
    rw [ker_contentHom_eq] at hker
    obtain ⟨w, hw, p, hp, hwp⟩ := Subgroup.mem_sup.mp hker
    have hx' : x = p * (w * u) := by
      calc x = (x * u⁻¹) * u := by group
        _ = (w * p) * u := by rw [hwp]
        _ = p * (w * u) := by rw [mul_comm w p, mul_assoc]
    rw [hx']
    exact Subgroup.mul_mem_sup hp (mul_mem (IsDedekindDomain.FiniteAdeleRing.unitIdeles_le_unitIdelesOutside R K T hw) hu)

end S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
end P2MW
export P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff (solution)
