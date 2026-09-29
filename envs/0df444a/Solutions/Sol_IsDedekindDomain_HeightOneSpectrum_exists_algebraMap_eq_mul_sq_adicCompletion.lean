-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_algebraMap_eq_mul_sq_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/17de6f8d-ebcb-59d4-86c8-08ddfefe64c1

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_NumberField_Completion_HenselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_algebraMap_eq_mul_sq_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Polynomial

namespace QMa

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem _root_.QMa.mem_maximalIdeal_iff (y : v.adicCompletionIntegers K) :
    y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ Valued.v (y : v.adicCompletion K) < 1 :=
  Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v

p2m_export "QMa" "mem_maximalIdeal_iff"

theorem exists_sq_add_self_eq (a : v.adicCompletionIntegers K)
    (ha : a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) :
    ∃ z : v.adicCompletionIntegers K, z ^ 2 + z = a := by
  set f : (v.adicCompletionIntegers K)[X] := Polynomial.X ^ 2 + Polynomial.X - Polynomial.C a with hf
  have hmonic : f.Monic := by
    have h1 : f = Polynomial.X ^ 2 + (Polynomial.X - Polynomial.C a) := by rw [hf]; ring
    rw [h1]
    refine (Polynomial.monic_X_pow 2).add_of_left ?_
    rw [Polynomial.degree_X_sub_C, Polynomial.degree_X_pow]
    exact_mod_cast one_lt_two
  have heval : f.eval 0 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    have h0 : f.eval 0 = -a := by simp [hf]
    rw [h0]
    exact neg_mem ha
  have hderiv : IsUnit ((Polynomial.derivative f).eval 0) := by
    have h0 : (Polynomial.derivative f).eval 0 = 1 := by
      simp [hf]
    rw [h0]
    exact isUnit_one
  obtain ⟨z, hz, -⟩ := HenselianLocalRing.is_henselian f hmonic 0 heval hderiv
  refine ⟨z, ?_⟩
  have h : z ^ 2 + z - a = 0 := by simpa [hf] using hz
  exact sub_eq_zero.mp h

theorem exists_sq_eq_of_valued_sub_one_lt (u : v.adicCompletion K)
    (hu : Valued.v (u - 1) < Valued.v (4 : v.adicCompletion K)) :
    ∃ c : v.adicCompletion K, c ^ 2 = u := by
  have h4 : (4 : v.adicCompletion K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 4]
    exact (map_ne_zero (algebraMap K (v.adicCompletion K))).mpr (by norm_num)
  have h4v : Valued.v (4 : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr h4
  have h4le : Valued.v (4 : v.adicCompletion K) ≤ 1 := by
    have h := (4 : v.adicCompletionIntegers K).2
    rw [mem_adicCompletionIntegers] at h
    simp at h ⊢
    exact h

  have hva : Valued.v ((u - 1) / 4) < 1 := by
    rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr h4v)]
    exact hu
  set aO : v.adicCompletionIntegers K := ⟨(u - 1) / 4, by rw [mem_adicCompletionIntegers]; exact hva.le⟩ with haO
  have hamem : aO ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) :=
    (mem_maximalIdeal_iff K v aO).mpr hva
  obtain ⟨z, hz⟩ := exists_sq_add_self_eq K v aO hamem
  have hz' : (z : v.adicCompletion K) ^ 2 + (z : v.adicCompletion K) = (u - 1) / 4 := by
    have h := congrArg ((↑) : v.adicCompletionIntegers K → v.adicCompletion K) hz
    simpa [haO] using h
  refine ⟨1 + 2 * (z : v.adicCompletion K), ?_⟩
  calc (1 + 2 * (z : v.adicCompletion K)) ^ 2
      = 1 + 4 * ((z : v.adicCompletion K) ^ 2 + (z : v.adicCompletion K)) := by ring
    _ = 1 + 4 * ((u - 1) / 4) := by rw [hz']
    _ = u := by rw [mul_div_cancel₀ _ h4]; ring

end QMa

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (d : v.adicCompletion K) (hd : d ≠ 0) :
    ∃ (d' : K) (c : v.adicCompletion K), c ≠ 0 ∧ algebraMap K (v.adicCompletion K) d' = d * c ^ 2 := by
  have hvd : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).mpr hd
  have h4 : (4 : v.adicCompletion K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 4]
    exact (map_ne_zero (algebraMap K (v.adicCompletion K))).mpr (by norm_num)
  have hγ0 : Valued.v (4 * d) ≠ 0 := (Valuation.ne_zero_iff _).mpr (mul_ne_zero h4 hd)

  have hnhds : {y : v.adicCompletion K | Valued.v (y - d) < Valued.v (4 * d)} ∈ nhds d := by
    rw [Valued.mem_nhds]
    have h' : Valued.v.restrict (4 * d) ≠ 0 := by simp [h4, hd]
    refine ⟨Units.mk0 _ h', fun y hy => ?_⟩
    rw [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hy
    exact hy
  obtain ⟨d', hd'⟩ := (denseRange_algebraMap K v).mem_nhds hnhds
  have hlt : Valued.v (algebraMap K (v.adicCompletion K) d' - d) < Valued.v (4 * d) := hd'

  set u : v.adicCompletion K := algebraMap K (v.adicCompletion K) d' / d with hudef
  have hu1 : Valued.v (u - 1) < Valued.v (4 : v.adicCompletion K) := by
    have hrw : u - 1 = (algebraMap K (v.adicCompletion K) d' - d) / d := by
      rw [hudef]; field_simp
    rw [hrw, map_div₀, div_lt_iff₀ (zero_lt_iff.mpr hvd), ← map_mul]
    exact hlt
  obtain ⟨c, hc⟩ := QMa.exists_sq_eq_of_valued_sub_one_lt K v u hu1
  have hu0 : u ≠ 0 := by
    rw [hudef]
    exact div_ne_zero (fun h0 => by
      rw [h0, zero_sub, Valuation.map_neg] at hlt
      have h44 : Valued.v (4 * d) ≤ Valued.v d := by
        rw [map_mul]
        have h4le : Valued.v (4 : v.adicCompletion K) ≤ 1 := by
          have h := (4 : v.adicCompletionIntegers K).2
          rw [mem_adicCompletionIntegers] at h
          simp at h ⊢
          exact h
        exact mul_le_of_le_one_left' h4le
      exact lt_irrefl _ (lt_of_lt_of_le hlt h44)) hd
  refine ⟨d', c, ?_, ?_⟩
  · rintro rfl
    apply hu0
    rw [← hc]; ring
  · rw [hc, hudef, mul_div_cancel₀ _ hd]

end S_IsDedekindDomain_HeightOneSpectrum_exists_algebraMap_eq_mul_sq_adicCompletion
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_algebraMap_eq_mul_sq_adicCompletion (solution)
