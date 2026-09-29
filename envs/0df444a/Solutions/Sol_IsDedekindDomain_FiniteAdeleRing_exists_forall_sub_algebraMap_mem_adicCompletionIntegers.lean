-- Prove2me | solution 1 for IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7109174c-e540-5dd2-94e9-113b42991ff9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers

p2m_open "IsDedekindDomain P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.IsDedekindDomain.HeightOneSpectrum"

namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum.ext FiniteAdeleRing exists_forall_sub_mem_ideal HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "valuation_of_algebraMap intValuation_le_pow_iff_mem valuedAdicCompletion_eq_valuation adicCompletion_valueGroup_eq algebraMap_adicCompletion intValuation_lt_one_iff_mem asIdeal mem_adicCompletionIntegers isPrime intValuation_ne_zero adicCompletion valuation coe_mem_adicCompletionIntegers ne_bot intValuation_le_one adicCompletionIntegers valuedAdicCompletion_surjective irreducible adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers intValuation_if_neg prime intValuation"
p2m_open "IsDedekindDomain.HeightOneSpectrum IsDedekindDomain"

section Multiplicative

open scoped WithZero
lemma s2_exists_ofAdd_natCast_of_le_one {x : ℤᵐ⁰} (hx : x ≠ 0) (hx' : x ≤ 1) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) = x := by
  lift x to Multiplicative ℤ using hx
  norm_cast at hx'
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos hx')
  use k
  rw [← hk, Int.neg_neg]
  rfl

lemma s2_exists_ofAdd_natCast_lt {x : ℤᵐ⁰} (hx : x ≠ 0) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) < x := by
  obtain ⟨y, hnz, hyx⟩ := WithZero.exists_ne_zero_and_lt hx
  lift y to Multiplicative ℤ using hnz
  use y.natAbs
  apply lt_of_le_of_lt _ hyx
  norm_cast
  exact inv_mabs_le y

end Multiplicative

lemma s2_intValuation_eq_coe_neg_multiplicity {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {a : A} (hnz : a ≠ 0) :
    v.intValuation a = WithZero.exp (-(multiplicity v.asIdeal (Ideal.span {a}) : ℤ)) := by
  classical
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [intValuation_if_neg _ hnz, Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot]
  nth_rw 1 [← normalize_eq v.asIdeal]
  congr
  symm
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb]

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

lemma s2_ne_zero_of_some_le_intValuation {a : A} {m : Multiplicative ℤ} (h : m ≤ v.intValuation a)
    : a ≠ 0 := by
  rintro rfl
  simp at h

lemma s2_emultiplicity_eq_of_valuation_eq_ofAdd {a : A} {k : ℕ}
    (hv : v.intValuation a = (Multiplicative.ofAdd (-(k : ℤ)))) :
    emultiplicity v.asIdeal (Ideal.span {a}) = k := by
  classical
  have hnz : a ≠ 0 := s2_ne_zero_of_some_le_intValuation _ (le_of_eq hv.symm)
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  simp only [intValuation_if_neg _ hnz, WithZero.exp, ofAdd_neg, WithZero.coe_inv, inv_inj,
    WithZero.coe_inj, EmbeddingLike.apply_eq_iff_eq, Nat.cast_inj] at hv
  rw [← hv, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb,
    Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot, normalize_eq]

lemma s2_exists_adicValued_mul_sub_le {a b : A} {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0)
    (hle : γ ≤ v.intValuation a)
    (hle' : v.intValuation b ≤ v.intValuation a) :
    ∃ y, v.intValuation (y * a - b) ≤ γ := by

  have hγ' : γ ≤ 1 := by
    apply hle.trans
    apply intValuation_le_one
  obtain ⟨n, hn⟩ := s2_exists_ofAdd_natCast_of_le_one hγ hγ'
  rw [← hn, ← WithZero.exp] at hle ⊢
  have hnz : a ≠ 0 := s2_ne_zero_of_some_le_intValuation _ hle
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]

  rw [s2_intValuation_eq_coe_neg_multiplicity _ hnz, WithZero.exp_le_exp, neg_le_neg_iff,
    Int.ofNat_le] at hle
  have hm : emultiplicity v.asIdeal (Ideal.span {a}) ≤ n :=
    le_of_eq_of_le
      (s2_emultiplicity_eq_of_valuation_eq_ofAdd v <| s2_intValuation_eq_coe_neg_multiplicity v hnz)
      (ENat.coe_le_coe.mpr hle)
  have hb : b ∈ v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) := by
    rwa [← intValuation_le_pow_iff_mem, ← s2_intValuation_eq_coe_neg_multiplicity _ hnz]

  rw [← Ideal.irreducible_pow_sup_of_ge hnb (irreducible v) n hm] at hb

  obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.mp hb
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz
  use y

  rwa [hy, ← hxz, sub_add_cancel_right, intValuation_le_pow_iff_mem, neg_mem_iff]

open MonoidWithZeroHom in
lemma s2_exists_adicValued_sub_lt_of_adicValued_le_one {x : (WithVal (v.valuation K))}
    (γ : ((WithZero (Multiplicative ℤ)))ˣ) (hx : Valued.v x ≤ 1) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by

  obtain ⟨⟨n, d, hd⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors A) x
  dsimp only at hnd

  have hnd' := congr_arg Valued.v hnd
  simp only [map_mul] at hnd'
  have hge : Valued.v ((algebraMap A (WithVal (v.valuation K))) d) ≥
      Valued.v ((algebraMap A (WithVal (v.valuation K))) n) :=
    calc Valued.v ((algebraMap A (WithVal (v.valuation K))) d)
          ≥ (valuation K v) x.ofVal *
            (valuation K v) ((algebraMap A (WithVal (v.valuation K))) d).ofVal :=
                mul_le_of_le_one_left' hx
        _ = Valued.v ((algebraMap A (WithVal (v.valuation K))) n) := hnd'
  simp only [ge_iff_le, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hge
  simp only [valuation_of_algebraMap] at hge
  have hdz : (algebraMap A (WithVal (v.valuation K)) d) ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ (fun _ ↦ id) hd

  have hv : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hdz
  let hu : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) * γ.val ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact ⟨hv, γ.ne_zero⟩
  obtain ⟨γ', hγ, hγu, hγv⟩ := WithZero.exists_ne_zero_and_lt_and_lt hu hv
  simp only [WithVal.algebraMap_right_apply, WithVal.valued_toVal, valuation_of_algebraMap] at hγv

  obtain ⟨a, hval⟩ := s2_exists_adicValued_mul_sub_le v hγ hγv.le hge
  use a
  rw [← eq_div_iff_mul_eq hdz] at hnd
  rw [adicCompletion.valuedAdicCompletion_def, ← adicCompletion.equiv_apply, map_sub,
    adicCompletion.equiv_apply, adicCompletion.equiv_apply,
    adicCompletion.toCompletion_ofCompletion, adicCompletion.toCompletion_ofCompletion,
    ← UniformSpace.Completion.coe_sub, Valued.extensionValuation_apply_coe, hnd, sub_div' hdz,
    map_div₀]
  rw [← Valuation.pos_iff Valued.v, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hdz
  simp only [WithVal.algebraMap_right_apply, WithVal.equiv_symm_apply,
    ← WithVal.toVal_mul, ← WithVal.toVal_sub, WithVal.valued_toVal, ← map_mul, ← map_sub] at hγu ⊢
  rw [div_lt_iff₀' hdz, valuation_of_algebraMap]
  exact lt_of_le_of_lt hval hγu

open scoped WithZero

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

scoped instance s2_isRankOneDiscrete_valuedAdicCompletion : Valuation.IsRankOneDiscrete vK where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

open Valuation.IsRankOneDiscrete in

theorem s2_closureAlgebraMapIntegers_eq_integers :
    closure (algebraMap A (v.adicCompletion K)).range =
    SetLike.coe (v.adicCompletionIntegers K) := by
  apply subset_antisymm

  · apply closure_minimal _ (Valued.isClosed_valuationSubring _)
    rintro b ⟨a, rfl⟩
    exact coe_mem_adicCompletionIntegers v a

  · let f := fun (k : WithVal (v.valuation K)) => (k : v.adicCompletion K)
    suffices h : closure (f '' (f ⁻¹' (adicCompletionIntegers K v))) ⊆
        closure (algebraMap A (adicCompletion K v)).range by
      apply Set.Subset.trans _ h
      exact DenseRange.subset_closure_image_preimage_of_isOpen
        ((adicCompletion.ofCompletion_surjective K v).denseRange.comp
          UniformSpace.Completion.denseRange_coe (adicCompletion.continuous_ofCompletion K v))
        (Valued.isOpen_valuationSubring _)

    apply closure_minimal _ isClosed_closure
    rintro k ⟨x, hx, rfl⟩
    unfold f at hx
    rw [Set.mem_preimage, SetLike.mem_coe, mem_adicCompletionIntegers,
        adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply] at hx
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Valued.mem_nhds] at hU
    obtain ⟨γ, hγ⟩ := hU
    let γ' := Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt _).toMulEquiv γ
    obtain ⟨a, ha⟩ := s2_exists_adicValued_sub_lt_of_adicValued_le_one K v γ' hx
    use algebraMap A K a
    constructor
    · use a
      rfl
    · apply hγ
      simp only [sub_zero, WithVal.equiv_symm_apply, Set.mem_setOf_eq]
      rwa [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
        valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (valuedAdicCompletion_surjective K v)]

open Valuation.IsRankOneDiscrete in

theorem s2_exists_adicValued_sub_lt_of_adicCompletionInteger
    (x : v.adicCompletionIntegers K) (γ : ℤᵐ⁰ˣ) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  have h := s2_closureAlgebraMapIntegers_eq_integers K v
  rw [Set.ext_iff] at h
  specialize h x
  simp_rw [RingHom.coe_range, Subtype.coe_prop, iff_true, mem_closure_iff_nhds] at h
  specialize h { y | Valued.v (y  - (x : v.adicCompletion K)) < γ.val }
  have hn : {y | Valued.v (y - (x : v.adicCompletion K)) < γ.val} ∈ nhds x.val := by
    rw [Valued.mem_nhds]
    use (Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt vK).toMulEquiv).symm γ
    have hsurj := (valuedAdicCompletion_surjective K v)
    intro y hy
    have hy' := (valueGroup₀_equiv_withZeroMulInt_strictMono vK) hy
    rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hsurj] at hy'
    refine lt_of_lt_of_eq hy' ?_
    exact MulEquiv.apply_symm_apply (valueGroup₀_equiv_withZeroMulInt vK).toMulEquiv _
  obtain ⟨z, ⟨hz, a, ha⟩⟩ := h hn
  use a
  rw [algebraMap_adicCompletion, Function.comp_apply] at ha
  rwa [ha]

theorem s2_exists_forall_adicValued_sub_lt {ι : Type*} (s : Finset ι)
    (e : ι → (WithZero (Multiplicative ℤ))ˣ) (valuation : ι → HeightOneSpectrum A)
    (injective : Function.Injective valuation)
    (x : (i : ι) → (valuation i).adicCompletionIntegers K) :
    ∃ a, ∀ i ∈ s, Valued.v ((algebraMap A K a) - (x i).val) < (e i).val := by

  choose f hf using fun (i : s) =>
    s2_exists_adicValued_sub_lt_of_adicCompletionInteger K (valuation i) (x i) (e i)

  have hexists_e' : ∀ (i : ι), ∃ (e' : ℕ), (Multiplicative.ofAdd (-(e' : ℤ))) < (e i).val := by
    intro i
    apply s2_exists_ofAdd_natCast_lt (e i).ne_zero
  choose e' he' using hexists_e'
  have hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (fun i ↦ (valuation i).asIdeal) i ≠ (fun i ↦ (valuation i).asIdeal) j := by
    intro _ _ _ _
    exact mt <| fun hij ↦ injective (HeightOneSpectrum.ext hij)

  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun i => (valuation i).asIdeal) e' (fun i hi => (valuation i).prime) hinj f
  use a
  intro i hi
  specialize ha i hi
  specialize hf ⟨i, hi⟩
  rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := K),
    ← valuedAdicCompletion_eq_valuation, algebraMap.coe_sub] at ha
  refine lt_of_le_of_lt ?_ (Valuation.map_add_lt _ (ha.trans_lt (he' i)) hf)
  apply le_of_eq
  congr
  rw [add_sub, sub_eq_sub_iff_add_eq_add, add_right_cancel_iff,
    add_comm_sub, add_sub, eq_sub_iff_add_eq]
  rfl

open scoped algebraMap

theorem s2_exists_nonZeroDivisor_smul_mem_adicCompletionIntegers (a : FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : HeightOneSpectrum A,
      (d : v.adicCompletion K) * a v ∈ v.adicCompletionIntegers K := by
  classical
  have hbad : {v : HeightOneSpectrum A | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2
  choose b hb hba using fun v : HeightOneSpectrum A ↦
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  refine ⟨∏ v ∈ hbad.toFinset, b v, prod_mem fun v _ ↦ hb v, fun v ↦ ?_⟩
  by_cases hv : a v ∈ v.adicCompletionIntegers K
  · exact mul_mem (coe_mem_adicCompletionIntegers v _) hv
  · have hvmem : v ∈ hbad.toFinset := hbad.mem_toFinset.mpr hv
    rw [← Finset.prod_erase_mul _ _ hvmem, algebraMap.coe_mul, mul_assoc]
    exact mul_mem (coe_mem_adicCompletionIntegers v _) (by rw [mul_comm]; exact hba v)

theorem s2_exists_sub_algebraMap_mem_adicCompletionIntegers (a : FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  classical

  obtain ⟨d, hd, hda⟩ := s2_exists_nonZeroDivisor_smul_mem_adicCompletionIntegers K a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd

  have hsupp : {v : HeightOneSpectrum A | v.intValuation d < 1}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {d})
      (by simpa [Ideal.span_singleton_eq_bot] using hd0)
    refine h.subset fun v hv ↦ ?_
    rw [Set.mem_setOf_eq, intValuation_lt_one_iff_mem] at hv
    exact (Ideal.dvd_span_singleton).mpr hv

  obtain ⟨c, hc⟩ := s2_exists_forall_adicValued_sub_lt K hsupp.toFinset
    (fun v ↦ Units.mk0 (v.intValuation d) (v.intValuation_ne_zero d hd0))
    id Function.injective_id (fun v ↦ ⟨(d : v.adicCompletion K) * a v, hda v⟩)

  refine ⟨algebraMap A K c / algebraMap A K d, fun v ↦ ?_⟩
  have hdK : algebraMap A K d ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors K (fun _ ↦ id) hd
  have hdv : Valued.v ((d : A) : v.adicCompletion K) ≠ 0 := by
    rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
    exact v.intValuation_ne_zero d hd0

  have key : ∀ v : HeightOneSpectrum A,
      Valued.v ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
        ≤ Valued.v (((d : A) : v.adicCompletion K)) := by
    intro v
    by_cases hv : v.intValuation d < 1
    ·
      have h := hc v (hsupp.mem_toFinset.mpr hv)
      simp only [id_eq, Units.val_mk0] at h
      rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
      calc Valued.v ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
          = Valued.v (((c : A) : v.adicCompletion K) - (d : v.adicCompletion K) * a v) := by
            rw [← Valuation.map_neg, neg_sub]
        _ ≤ v.intValuation d := le_of_lt h
    ·
      rw [not_lt] at hv
      have hd1 : Valued.v (((d : A) : v.adicCompletion K)) = 1 := by
        rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
        exact le_antisymm (v.intValuation_le_one d) hv
      rw [hd1, ← mem_adicCompletionIntegers]
      exact sub_mem (hda v) (coe_mem_adicCompletionIntegers v c)

  rw [mem_adicCompletionIntegers]
  have hdne : ((d : A) : v.adicCompletion K) ≠ 0 := by
    intro h0
    exact hdv (by rw [h0, map_zero])
  have hmap : algebraMap K (v.adicCompletion K) (algebraMap A K c / algebraMap A K d)
      = ((c : A) : v.adicCompletion K) / ((d : A) : v.adicCompletion K) := by
    rw [map_div₀]
    rfl
  have hrw : a v - algebraMap K (v.adicCompletion K) (algebraMap A K c / algebraMap A K d)
      = ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
        / ((d : A) : v.adicCompletion K) := by
    rw [hmap, sub_div, mul_comm ((d : A) : v.adicCompletion K) (a v),
      mul_div_assoc, div_self hdne, mul_one]
  rw [hrw, map_div₀, div_le_one₀ (zero_lt_iff.mpr hdv)]
  exact key v

end IsDedekindDomain.HeightOneSpectrum
p2m_reactivate "P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.IsDedekindDomain P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.IsDedekindDomain.HeightOneSpectrum"
p2m_reactivate "P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.IsDedekindDomain"

theorem solution
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K :=
  IsDedekindDomain.HeightOneSpectrum.s2_exists_sub_algebraMap_mem_adicCompletionIntegers K a

end S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers
end P2MW
export P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers (solution)
