-- Prove2me | solution 1 for NumberField.AdelicLevel.finiteIdeleClassNumberOne_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/ba530779-540d-5c64-a5d7-265c4ee8a8b7

import Definitions.Def_NumberField_AdelicLevel
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.NumberTheory.NumberField.ClassNumber
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat

set_option autoImplicit false

namespace M4aP1R

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

open scoped nonZeroDivisors

namespace ClassFieldAxiom

section Carrier

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

abbrev IdeleGroup := (AdeleRing R K)ˣ

noncomputable def principalIdeles : Subgroup (IdeleGroup R K) :=
  (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K)).range

end Carrier

end ClassFieldAxiom

namespace ClassFieldAxiom

noncomputable section

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

section ComponentExponent

def adeleEvalAt (v : HeightOneSpectrum R) : AdeleRing R K →+* v.adicCompletion K :=
  (RestrictedProduct.evalRingHom _ v).comp
    (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K))

@[scoped simp] lemma adeleEvalAt_apply (v : HeightOneSpectrum R) (x : AdeleRing R K) :
    adeleEvalAt R K v x = x.2 v := rfl

def ideleEvalAt (v : HeightOneSpectrum R) : IdeleGroup R K →* (v.adicCompletion K)ˣ :=
  Units.map (adeleEvalAt R K v).toMonoidHom

@[scoped simp] lemma ideleEvalAt_val (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    (ideleEvalAt R K v x : v.adicCompletion K) = (x : AdeleRing R K).2 v := rfl

lemma valued_ideleEvalAt_ne_zero (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    (Valued.v ((ideleEvalAt R K v x : v.adicCompletion K))) ≠ 0 := by
  simp only [ne_eq, map_eq_zero]
  exact (ideleEvalAt R K v x).ne_zero

def ideleExponentAt (v : HeightOneSpectrum R) (x : IdeleGroup R K) : ℤ :=
  -log (Valued.v ((ideleEvalAt R K v x : v.adicCompletion K)))

@[scoped simp] lemma ideleExponentAt_one (v : HeightOneSpectrum R) :
    ideleExponentAt R K v 1 = 0 := by
  simp [ideleExponentAt]

lemma ideleExponentAt_mul (v : HeightOneSpectrum R) (x y : IdeleGroup R K) :
    ideleExponentAt R K v (x * y) = ideleExponentAt R K v x + ideleExponentAt R K v y := by
  simp only [ideleExponentAt, map_mul, Units.val_mul]
  rw [log_mul (valued_ideleEvalAt_ne_zero R K v x) (valued_ideleEvalAt_ne_zero R K v y)]
  ring

lemma ideleExponentAt_inv (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    ideleExponentAt R K v x⁻¹ = -ideleExponentAt R K v x := by
  have h := ideleExponentAt_mul R K v x x⁻¹
  rw [mul_inv_cancel, ideleExponentAt_one] at h
  omega

lemma ideleExponentAt_eq_zero_iff (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    ideleExponentAt R K v x = 0 ↔
      Valued.v ((ideleEvalAt R K v x : v.adicCompletion K)) = 1 := by
  rw [ideleExponentAt, neg_eq_zero]
  constructor
  · intro h
    have h2 := exp_log (valued_ideleEvalAt_ne_zero R K v x)
    rw [← h2, h, exp_zero]
  · intro h
    rw [h, log_one]

lemma ideleExponentAt_prod {ι : Type*} (v : HeightOneSpectrum R) (s : Finset ι)
    (f : ι → IdeleGroup R K) :
    ideleExponentAt R K v (∏ i ∈ s, f i) = ∑ i ∈ s, ideleExponentAt R K v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ideleExponentAt_mul, ih]

lemma ideleExponentAt_pow (v : HeightOneSpectrum R) (x : IdeleGroup R K) (n : ℕ) :
    ideleExponentAt R K v (x ^ n) = n * ideleExponentAt R K v x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ideleExponentAt_mul, ih]; push_cast; ring

end ComponentExponent

section FiniteSupport

private lemma eq_one_of_mul_eq_one_of_le_one {a b : ℤᵐ⁰} (hab : a * b = 1)
    (ha : a ≤ 1) (hb : b ≤ 1) : a = 1 := by
  have hb1 : b = 1 := le_antisymm hb (by
    calc (1 : ℤᵐ⁰) = a * b := hab.symm
    _ ≤ 1 * b := by gcongr
    _ = b := one_mul b)
  rw [hb1, mul_one] at hab
  exact hab

lemma ideleEvalAt_inv (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    ((ideleEvalAt R K v x⁻¹ : v.adicCompletion K)) =
      ((ideleEvalAt R K v x : v.adicCompletion K))⁻¹ := by
  rw [map_inv, Units.val_inv_eq_inv_val]

theorem ideleExponentAt_eq_zero_of_integral {v : HeightOneSpectrum R} {x : IdeleGroup R K}
    (hx : Valued.v ((x : AdeleRing R K).2 v) ≤ 1)
    (hxi : Valued.v (((x⁻¹ : IdeleGroup R K) : AdeleRing R K).2 v) ≤ 1) :
    ideleExponentAt R K v x = 0 := by
  rw [ideleExponentAt_eq_zero_iff]
  have hmul : Valued.v ((ideleEvalAt R K v x : v.adicCompletion K)) *
      Valued.v ((ideleEvalAt R K v x⁻¹ : v.adicCompletion K)) = 1 := by
    have h1 : ((ideleEvalAt R K v x : v.adicCompletion K)) *
        ((ideleEvalAt R K v x⁻¹ : v.adicCompletion K)) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have h2 := congrArg Valued.v h1
    rwa [Valuation.map_mul, Valuation.map_one] at h2
  exact eq_one_of_mul_eq_one_of_le_one hmul hx hxi

theorem finite_mulSupport_ideleExponentAt (x : IdeleGroup R K) :
    {v : HeightOneSpectrum R | ideleExponentAt R K v x ≠ 0}.Finite := by
  have hx : ∀ᶠ v in Filter.cofinite,
      ((x : AdeleRing R K).2 : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
    ((x : AdeleRing R K).2 : FiniteAdeleRing R K).2
  have hxi : ∀ᶠ v in Filter.cofinite,
      (((x⁻¹ : IdeleGroup R K) : AdeleRing R K).2 : FiniteAdeleRing R K) v ∈
        v.adicCompletionIntegers K :=
    (((x⁻¹ : IdeleGroup R K) : AdeleRing R K).2 : FiniteAdeleRing R K).2
  have hboth := hx.and hxi
  rw [Filter.eventually_cofinite] at hboth
  refine hboth.subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  intro hcon
  exact hv (ideleExponentAt_eq_zero_of_integral R K
    ((mem_adicCompletionIntegers R K v).mp hcon.1)
    ((mem_adicCompletionIntegers R K v).mp hcon.2))

end FiniteSupport

section AssociatedIdeal

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

def associatedFractionalIdeal (x : IdeleGroup R K) : FractionalIdeal R⁰ K :=
  ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (ideleExponentAt R K v x)

lemma associatedFractionalIdeal_ne_zero (x : IdeleGroup R K) :
    associatedFractionalIdeal R K x ≠ 0 := by
  rw [associatedFractionalIdeal, finprod_eq_prod_of_mulSupport_subset _
    (s := (finite_mulSupport_ideleExponentAt R K x).toFinset)
    (by simpa using mulSupport_zpow_subset R K _)]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_asIdeal_ne_zero R K v _

theorem count_associatedFractionalIdeal (v : HeightOneSpectrum R) (x : IdeleGroup R K) :
    FractionalIdeal.count K v (associatedFractionalIdeal R K x) = ideleExponentAt R K v x :=
  FractionalIdeal.count_finprod K v _ (Filter.eventually_cofinite.mpr
    (by simpa using finite_mulSupport_ideleExponentAt R K x))

theorem associatedFractionalIdeal_mul (x y : IdeleGroup R K) :
    associatedFractionalIdeal R K (x * y) =
      associatedFractionalIdeal R K x * associatedFractionalIdeal R K y := by
  unfold associatedFractionalIdeal
  rw [← finprod_mul_distrib
    ((finite_mulSupport_ideleExponentAt R K x).subset (mulSupport_zpow_subset R K _))
    ((finite_mulSupport_ideleExponentAt R K y).subset (mulSupport_zpow_subset R K _))]
  apply finprod_congr
  intro v
  rw [ideleExponentAt_mul, zpow_add₀ (coeIdeal_asIdeal_ne_zero R K v)]

theorem fractionalIdeal_eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J :=
  calc I = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
        (FractionalIdeal.count K v I) :=
      (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI).symm
  _ = ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
        (FractionalIdeal.count K v J) := finprod_congr fun v => by rw [h v]
  _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ

end AssociatedIdeal

section ContentHom

def contentHom : IdeleGroup R K →* ClassGroup R where
  toFun x := ClassGroup.mk K (Units.mk0 (associatedFractionalIdeal R K x)
    (associatedFractionalIdeal_ne_zero R K x))
  map_one' := by
    have h1 : associatedFractionalIdeal R K (1 : IdeleGroup R K) = 1 := by
      unfold associatedFractionalIdeal
      rw [finprod_eq_one_of_forall_eq_one]
      intro v
      rw [ideleExponentAt_one, zpow_zero]
    rw [← map_one (ClassGroup.mk (R := R) K)]
    congr 1
    exact Units.ext (by simpa using h1)
  map_mul' x y := by
    rw [← map_mul]
    congr 1
    exact Units.ext (by simpa using associatedFractionalIdeal_mul R K x y)

@[scoped simp] lemma contentHom_apply (x : IdeleGroup R K) :
    contentHom R K x = ClassGroup.mk K (Units.mk0 (associatedFractionalIdeal R K x)
      (associatedFractionalIdeal_ne_zero R K x)) := rfl

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

theorem ideleExponentAt_principal (v : HeightOneSpectrum R) (u : Kˣ) :
    ideleExponentAt R K v
      (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) u) =
      -log (v.valuation K (u : K)) := by
  unfold ideleExponentAt
  congr 1
  show log (Valued.v ((algebraMap K (AdeleRing R K) (u : K)).2 v)) = _
  rw [AdeleRing.algebraMap_snd_apply, valuedAdicCompletion_eq_valuation']

theorem contentHom_principal (u : Kˣ) :
    contentHom R K (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) u) = 1 := by
  rw [contentHom_apply, ClassGroup.mk_eq_one_iff]
  have key : associatedFractionalIdeal R K
      (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) u) =
      FractionalIdeal.spanSingleton R⁰ (u : K) := by
    apply fractionalIdeal_eq_of_count_eq R K (associatedFractionalIdeal_ne_zero R K _)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr u.ne_zero)
    intro v
    rw [count_associatedFractionalIdeal, count_spanSingleton_eq_neg_log_valuation,
      ideleExponentAt_principal]
  simp only [Units.val_mk0, key]
  rw [FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(u : K), rfl⟩⟩

end ContentHom

section KernelClause

def unramifiedIdeles : Subgroup (IdeleGroup R K) where
  carrier := {x | ∀ v : HeightOneSpectrum R, ideleExponentAt R K v x = 0}
  one_mem' v := ideleExponentAt_one R K v
  mul_mem' hx hy v := by rw [ideleExponentAt_mul, hx v, hy v, add_zero]
  inv_mem' hx v := by rw [ideleExponentAt_inv, hx v, neg_zero]

@[scoped simp] lemma mem_unramifiedIdeles_iff (x : IdeleGroup R K) :
    x ∈ unramifiedIdeles R K ↔ ∀ v : HeightOneSpectrum R, ideleExponentAt R K v x = 0 :=
  Iff.rfl

def unramifiedIdelesOutside (T : Set (HeightOneSpectrum R)) : Subgroup (IdeleGroup R K) where
  carrier := {x | ∀ v : HeightOneSpectrum R, v ∉ T → ideleExponentAt R K v x = 0}
  one_mem' v _ := ideleExponentAt_one R K v
  mul_mem' hx hy v hv := by rw [ideleExponentAt_mul, hx v hv, hy v hv, add_zero]
  inv_mem' hx v hv := by rw [ideleExponentAt_inv, hx v hv, neg_zero]

@[scoped simp] lemma mem_unramifiedIdelesOutside_iff (T : Set (HeightOneSpectrum R))
    (x : IdeleGroup R K) :
    x ∈ unramifiedIdelesOutside R K T ↔
      ∀ v : HeightOneSpectrum R, v ∉ T → ideleExponentAt R K v x = 0 :=
  Iff.rfl

@[scoped simp] lemma unramifiedIdelesOutside_empty :
    unramifiedIdelesOutside R K (∅ : Set (HeightOneSpectrum R)) = unramifiedIdeles R K := by
  ext x
  simp [unramifiedIdelesOutside, unramifiedIdeles]

lemma unramifiedIdelesOutside_mono {T T' : Set (HeightOneSpectrum R)} (h : T ⊆ T') :
    unramifiedIdelesOutside R K T ≤ unramifiedIdelesOutside R K T' :=
  fun _ hx v hv => hx v fun hvT => hv (h hvT)

lemma unramifiedIdeles_le_unramifiedIdelesOutside (T : Set (HeightOneSpectrum R)) :
    unramifiedIdeles R K ≤ unramifiedIdelesOutside R K T :=
  fun _ hx v _ => hx v

theorem ker_le_unramifiedIdeles_sup_principal :
    MonoidHom.ker (contentHom R K) ≤ unramifiedIdeles R K ⊔ principalIdeles R K := by
  intro x hx
  rw [MonoidHom.mem_ker, contentHom_apply, ClassGroup.mk_eq_one_iff] at hx

  obtain ⟨a, ha⟩ := hx.principal
  have ha' : associatedFractionalIdeal R K x = FractionalIdeal.spanSingleton R⁰ a := by
    apply FractionalIdeal.coeToSubmodule_injective
    show (associatedFractionalIdeal R K x : Submodule R K) =
      (FractionalIdeal.spanSingleton R⁰ a : Submodule R K)
    rw [FractionalIdeal.coe_spanSingleton]
    simpa using ha
  have ha0 : a ≠ 0 := by
    intro h0
    apply associatedFractionalIdeal_ne_zero R K x
    rw [ha', h0, FractionalIdeal.spanSingleton_zero]
  set u : Kˣ := Units.mk0 a ha0 with hu
  set p : IdeleGroup R K :=
    Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) u with hp

  have hquot : x * p⁻¹ ∈ unramifiedIdeles R K := by
    intro v
    rw [ideleExponentAt_mul, ideleExponentAt_inv]
    have h1 : ideleExponentAt R K v x =
        FractionalIdeal.count K v (associatedFractionalIdeal R K x) :=
      (count_associatedFractionalIdeal R K v x).symm
    have h2 : ideleExponentAt R K v p = FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton R⁰ (u : K)) := by
      rw [hp, ideleExponentAt_principal, count_spanSingleton_eq_neg_log_valuation]
    rw [h1, h2, ha']
    simp [hu]

  have hxp : x = (x * p⁻¹) * p := by group
  rw [hxp]
  exact Subgroup.mul_mem_sup hquot ⟨u, rfl⟩

end KernelClause

section SurjectivityClause

variable [DecidableEq (HeightOneSpectrum R)]

def finiteAdeleInr : FiniteAdeleRing R K →* AdeleRing R K where
  toFun b := ((1, b) : InfiniteAdeleRing K × FiniteAdeleRing R K)
  map_one' := rfl
  map_mul' b b' := by
    show ((1, b * b') : InfiniteAdeleRing K × FiniteAdeleRing R K) = (1 * 1, b * b')
    rw [one_mul]

omit [DecidableEq (HeightOneSpectrum R)] in
@[scoped simp] lemma finiteAdeleInr_snd (b : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (finiteAdeleInr R K b).2 v = b v := rfl

end SurjectivityClause

end

end ClassFieldAxiom
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R.ClassFieldAxiom"

namespace GL2StrongApprox

open Matrix ClassFieldAxiom M4aP1R.ClassFieldAxiom

noncomputable section

theorem subsingleton_classGroup_ringOfIntegers_rat : Subsingleton (ClassGroup (𝓞 ℚ)) :=
  Fintype.card_le_one_iff_subsingleton.mp (le_of_eq Rat.classNumber_eq)

theorem snd_mem_adicCompletionIntegers_of_mem_unramifiedIdeles
    {j : IdeleGroup (𝓞 ℚ) ℚ} (hj : j ∈ unramifiedIdeles (𝓞 ℚ) ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((j : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) v ∈ v.adicCompletionIntegers ℚ := by
  have h0 := (mem_unramifiedIdeles_iff (𝓞 ℚ) ℚ j).mp hj v
  have h1 := (ideleExponentAt_eq_zero_iff (𝓞 ℚ) ℚ v j).mp h0
  rw [ideleEvalAt_val] at h1
  exact (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr h1.le

theorem exists_unramified_mul_principal_finiteIdele_rat
    (δ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ j ∈ unramifiedIdeles (𝓞 ℚ) ℚ, ∃ q : ℚˣ,
      (δ : FiniteAdeleRing (𝓞 ℚ) ℚ)
          = ((j : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q : ℚˣ) : ℚ)
        ∧ ((δ⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
          = (((j⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q⁻¹ : ℚˣ) : ℚ) := by
  classical

  set x : IdeleGroup (𝓞 ℚ) ℚ := Units.map (finiteAdeleInr (𝓞 ℚ) ℚ) δ with hxdef

  haveI : Subsingleton (ClassGroup (𝓞 ℚ)) := subsingleton_classGroup_ringOfIntegers_rat
  have hker : x ∈ MonoidHom.ker (contentHom (𝓞 ℚ) ℚ) := by
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _

  have hsup : x ∈ unramifiedIdeles (𝓞 ℚ) ℚ ⊔ principalIdeles (𝓞 ℚ) ℚ :=
    ker_le_unramifiedIdeles_sup_principal (𝓞 ℚ) ℚ hker
  obtain ⟨j, hj, p, hp, hjp⟩ := Subgroup.mem_sup.mp hsup
  obtain ⟨q, hq⟩ := hp
  refine ⟨j, hj, q, ?_, ?_⟩
  ·
    have h1 : ((x : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2
        = (δ : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      rw [hxdef]; rfl
    have h4 : ((p : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q : ℚˣ) : ℚ) := by
      rw [← hq]; rfl
    calc (δ : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = ((x : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := h1.symm
      _ = (((j * p : IdeleGroup (𝓞 ℚ) ℚ) : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := by
          rw [hjp]
      _ = ((j : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * ((p : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := rfl
      _ = ((j : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q : ℚˣ) : ℚ) := by rw [h4]
  ·
    have hjp' : j⁻¹ * p⁻¹ = x⁻¹ := by
      rw [← hjp, _root_.mul_inv_rev]
      exact mul_comm _ _
    have hq' : Units.map (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) : ℚ →* AdeleRing (𝓞 ℚ) ℚ) q⁻¹
        = p⁻¹ := by
      rw [map_inv, hq]
    have h1 : ((x⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2
        = ((δ⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      rw [hxdef]; rfl
    have h4 : ((p⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q⁻¹ : ℚˣ) : ℚ) := by
      rw [← hq']; rfl
    calc ((δ⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = ((x⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := h1.symm
      _ = (((j⁻¹ * p⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := by
          rw [hjp']
      _ = (((j⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * ((p⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 := rfl
      _ = (((j⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ)
            * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q⁻¹ : ℚˣ) : ℚ) := by rw [h4]

theorem finiteIdeleClassNumberOne_rat_impl (δ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ α : ℚˣ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ),
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((α⁻¹ : ℚˣ) : ℚ)
          * (δ : FiniteAdeleRing (𝓞 ℚ) ℚ)) v ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ),
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((α : ℚˣ) : ℚ)
          * ((δ⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) v
          ∈ v.adicCompletionIntegers ℚ) := by
  obtain ⟨j, hj, q, hdec, hdecinv⟩ := exists_unramified_mul_principal_finiteIdele_rat δ
  refine ⟨q, fun v => ?_, fun v => ?_⟩
  ·
    have hkey : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q⁻¹ : ℚˣ) : ℚ)
        * (δ : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = ((j : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      rw [hdec, mul_left_comm, ← map_mul, Units.inv_mul, map_one, mul_one]
    rw [hkey]
    exact snd_mem_adicCompletionIntegers_of_mem_unramifiedIdeles hj v
  ·
    have hkey : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((q : ℚˣ) : ℚ)
        * ((δ⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)
        = (((j⁻¹ : IdeleGroup (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
      rw [hdecinv, mul_left_comm, ← map_mul, Units.mul_inv, map_one, mul_one]
    rw [hkey]
    exact snd_mem_adicCompletionIntegers_of_mem_unramifiedIdeles
      ((unramifiedIdeles (𝓞 ℚ) ℚ).inv_mem hj) v

end
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R.ClassFieldAxiom"

end GL2StrongApprox
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R.ClassFieldAxiom"

end M4aP1R
p2m_reactivate "P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R.ClassFieldAxiom P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.M4aP1R"

#print axioms M4aP1R.GL2StrongApprox.finiteIdeleClassNumberOne_rat_impl

theorem solution
    (δ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
    ∃ α : ℚˣ,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
              ((α⁻¹ : ℚˣ) : ℚ)
            * (δ : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) v
          ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
              ((α : ℚˣ) : ℚ)
            * ((δ⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
                IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) v
          ∈ v.adicCompletionIntegers ℚ) := by
  exact M4aP1R.GL2StrongApprox.finiteIdeleClassNumberOne_rat_impl δ

end S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat
end P2MW
export P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat (solution)
