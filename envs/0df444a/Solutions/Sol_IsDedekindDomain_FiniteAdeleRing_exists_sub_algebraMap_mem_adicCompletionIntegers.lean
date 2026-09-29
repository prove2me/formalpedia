-- Prove2me | solution 1 for IsDedekindDomain.FiniteAdeleRing.exists_sub_algebraMap_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1a1674ba-bb71-5793-8a50-aed5b1a4e4b1

import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.Factorization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_sub_algebraMap_mem_adicCompletionIntegers

set_option autoImplicit false

open scoped WithZero

namespace M4aP1R

namespace Approx

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Multiplicative

lemma exists_ofAdd_natCast_of_le_one {x : ℤᵐ⁰} (hx : x ≠ 0) (hx' : x ≤ 1) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) = x := by
  lift x to Multiplicative ℤ using hx
  norm_cast at hx'
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos hx')
  use k
  rw [← hk, Int.neg_neg]
  rfl

lemma exists_ofAdd_natCast_lt {x : ℤᵐ⁰} (hx : x ≠ 0) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) < x := by
  obtain ⟨y, hnz, hyx⟩ := WithZero.exists_ne_zero_and_lt hx
  lift y to Multiplicative ℤ using hnz
  use y.natAbs
  apply lt_of_le_of_lt _ hyx
  norm_cast
  exact inv_mabs_le y

end Multiplicative

variable {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] (v : HeightOneSpectrum A)

theorem exists_valued_algebraMap_sub_lt (x : v.adicCompletionIntegers K) (γ : ℤᵐ⁰ˣ)
    (hγ : (γ : ℤᵐ⁰) ≤ 1) :
    ∃ a : A, Valued.v (((algebraMap A K a : K) : v.adicCompletion K) - (x : v.adicCompletion K)) < γ := by

  obtain ⟨t, ht⟩ := valuedAdicCompletion_surjective K v (γ : ℤᵐ⁰)
  have ht0 : t ≠ 0 := fun h => γ.ne_zero (by rw [← ht, h, map_zero])
  have hrt : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict t ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ht0
  have hn : {z : v.adicCompletion K | Valued.v (z - (x : v.adicCompletion K)) < γ} ∈
      nhds (x : v.adicCompletion K) := by
    refine Valued.mem_nhds.mpr ⟨Units.mk0 _ hrt, fun z hz => ?_⟩
    have hz' : Valued.v (z - (x : v.adicCompletion K)) < Valued.v t :=
      (Valuation.restrict_lt_iff _).mp hz
    rw [ht] at hz'
    exact hz'
  obtain ⟨_, hz, y, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) (x : v.adicCompletion K)) _ hn
  have hy1 : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < γ := hz
  have hyint : v.valuation K y ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
    have h : Valued.v (algebraMap K (v.adicCompletion K) y) ≤ 1 := by
      have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
        (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) (x : v.adicCompletion K)
      rw [sub_add_cancel] at this
      exact this.trans (max_le (hy1.le.trans hγ) hx1)
    rwa [show algebraMap K (v.adicCompletion K) y = (y : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyint γ
  refine ⟨a, ?_⟩
  have ha' : Valued.v (((algebraMap A K a : K) : v.adicCompletion K) -
      algebraMap K (v.adicCompletion K) y) < γ := by
    rw [show ((algebraMap A K a : K) : v.adicCompletion K) - algebraMap K (v.adicCompletion K) y
        = ((algebraMap A K a - y : K) : v.adicCompletion K) from
        (map_sub (algebraMap K (v.adicCompletion K)) (algebraMap A K a) y).symm,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha
  have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
    (((algebraMap A K a : K) : v.adicCompletion K) - algebraMap K (v.adicCompletion K) y)
    (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K))
  rw [sub_add_sub_cancel] at this
  exact lt_of_le_of_lt this (max_lt ha' hy1)

theorem exists_adicValued_sub_lt_of_adicCompletionInteger
    (x : v.adicCompletionIntegers K) (γ : ℤᵐ⁰ˣ) :
    ∃ a, Valued.v ((algebraMap A K a : v.adicCompletion K) - (x : v.adicCompletion K)) < γ.val := by
  by_cases hγ : (γ : ℤᵐ⁰) ≤ 1
  · exact exists_valued_algebraMap_sub_lt K v x γ hγ
  · obtain ⟨a, ha⟩ := exists_valued_algebraMap_sub_lt K v x 1 (by rw [Units.val_one])
    exact ⟨a, ha.trans (by rw [Units.val_one]; exact lt_of_not_ge hγ)⟩

variable {v}

theorem exists_forall_adicValued_sub_lt {ι : Type*} (s : Finset ι)
    (e : ι → (WithZero (Multiplicative ℤ))ˣ) (valuation : ι → HeightOneSpectrum A)
    (injective : Function.Injective valuation)
    (x : (i : ι) → (valuation i).adicCompletionIntegers K) :
    ∃ a, ∀ i ∈ s, Valued.v ((algebraMap A K a) - (x i).val) < (e i).val := by

  choose f hf using fun (i : s) =>
    exists_adicValued_sub_lt_of_adicCompletionInteger K (valuation i) (x i) (e i)

  have hexists_e' : ∀ (i : ι), ∃ (e' : ℕ), (Multiplicative.ofAdd (-(e' : ℤ))) < (e i).val := by
    intro i
    apply exists_ofAdd_natCast_lt (e i).ne_zero
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

theorem exists_nonZeroDivisor_smul_mem_adicCompletionIntegers (a : FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : HeightOneSpectrum A,
      (d : v.adicCompletion K) * a v ∈ v.adicCompletionIntegers K := by
  classical

  have hbad : {v : HeightOneSpectrum A | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2

  choose b hb hba using fun v : HeightOneSpectrum A ↦
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)

  refine ⟨∏ v ∈ hbad.toFinset, b v, prod_mem fun v _ ↦ hb v, fun v ↦ ?_⟩
  by_cases hv : a v ∈ v.adicCompletionIntegers K
  ·
    exact mul_mem (coe_mem_adicCompletionIntegers v _) hv
  ·
    have hvmem : v ∈ hbad.toFinset := hbad.mem_toFinset.mpr hv
    rw [← Finset.prod_erase_mul _ _ hvmem, algebraMap.coe_mul, mul_assoc]
    exact mul_mem (coe_mem_adicCompletionIntegers v _) (by rw [mul_comm]; exact hba v)

theorem exists_sub_algebraMap_mem_adicCompletionIntegers (a : FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  classical

  obtain ⟨d, hd, hda⟩ := exists_nonZeroDivisor_smul_mem_adicCompletionIntegers K a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd

  have hsupp : {v : HeightOneSpectrum A | v.intValuation d < 1}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {d})
      (by simpa [Ideal.span_singleton_eq_bot] using hd0)
    refine h.subset fun v hv ↦ ?_
    rw [Set.mem_setOf_eq, intValuation_lt_one_iff_mem] at hv
    exact (Ideal.dvd_span_singleton).mpr hv

  obtain ⟨c, hc⟩ := exists_forall_adicValued_sub_lt K hsupp.toFinset
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

end Approx

theorem Approx.exists_sub_algebraMap_mem_adicCompletionIntegers_impl
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K :=
  Approx.exists_sub_algebraMap_mem_adicCompletionIntegers K a

end M4aP1R

#print axioms M4aP1R.Approx.exists_sub_algebraMap_mem_adicCompletionIntegers_impl

theorem solution
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  exact M4aP1R.Approx.exists_sub_algebraMap_mem_adicCompletionIntegers_impl K a

end S_IsDedekindDomain_FiniteAdeleRing_exists_sub_algebraMap_mem_adicCompletionIntegers
end P2MW
export P2MW.S_IsDedekindDomain_FiniteAdeleRing_exists_sub_algebraMap_mem_adicCompletionIntegers (solution)
