-- Prove2me | solution 1 for HyperMatchDelay.Batching.reduction_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:05:12.487005+00:00
-- url     : https://prove2.me/submissions/0d19b019-3779-400b-af7e-0bc904c5b003

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace Aux_HyperMatchDelay_reduction_4
open HyperMatchDelay.Batching

theorem mem_window {n d z : ℕ} {i : ℤ} {v : ℕ} :
    v ∈ window n d z i ↔ v ∈ Finset.Icc 1 n ∧
      ((z : ℤ) + i * d ≤ (v : ℤ) ∧ (v : ℤ) ≤ (z : ℤ) + (i + 1) * d - 1) := by
  unfold window; exact Finset.mem_filter

/-- An edge of the shareability graph lies in at least `r` batches when `diam e ≤ d - r`. -/
theorem count_batches (n d k : ℕ) (hd : 1 ≤ d) (E : Finset (Finset ℕ)) (w : Finset ℕ → ℝ)
    (hE : IsShareability n d k E w) (e : Finset ℕ) (he : e ∈ E) (r : ℕ) (hr1 : 1 ≤ r)
    (hr : (diam e : ℤ) ≤ (d : ℤ) - r) :
    (r : ℝ) ≤ ∑ z ∈ Finset.range d, ∑ i ∈ batchIndices n d,
      (if e ∈ batchEdges E n d z i then (1 : ℝ) else 0) := by
  classical
  obtain ⟨hsub, hne, -, -, -⟩ := hE e he
  have hd0 : (0 : ℤ) < d := by exact_mod_cast hd
  set m := e.min' hne with hm
  set M := e.max' hne with hM
  have hdiam : (diam e : ℤ) = (M : ℤ) - m := by
    unfold diam; rw [dif_pos hne]
    have : e.min' hne ≤ e.max' hne := e.min'_le_max' hne
    rw [Nat.cast_sub this]
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hsub (e.min'_mem hne))).1
  have hMn : M ≤ n := (Finset.mem_Icc.mp (hsub (e.max'_mem hne))).2
  set t : ℕ → ℤ := fun s => (m : ℤ) - s with ht
  set p : ℕ → ℕ × ℤ := fun s => (((t s) % d).toNat, (t s) / d) with hp
  have hz : ∀ s, (((p s).1 : ℕ) : ℤ) = (t s) % d := fun s =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hd0.ne')
  have hdecomp : ∀ s, (((p s).1 : ℕ) : ℤ) + (p s).2 * d = t s := by
    intro s
    rw [hz]
    have := Int.mul_ediv_add_emod (t s) d
    simp only [hp]
    linarith
  have hgood : ∀ s ∈ Finset.range r, p s ∈ Finset.range d ×ˢ batchIndices n d ∧
      e ∈ batchEdges E n d (p s).1 (p s).2 := by
    intro s hs
    have hsr : s < r := Finset.mem_range.mp hs
    have hzlt : (p s).1 < d := by
      have := Int.emod_lt_of_pos (t s) hd0
      have h2 := hz s
      omega
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hzlt, ?_⟩, ?_⟩
    · unfold batchIndices
      rw [Finset.mem_Icc]
      have hdc := hdecomp s
      have hz0 : (0 : ℤ) ≤ ((p s).1 : ℤ) := Int.natCast_nonneg _
      have hzd : ((p s).1 : ℤ) < d := by exact_mod_cast hzlt
      have hts : t s = (m : ℤ) - s := rfl
      constructor
      · by_contra h
        push_neg at h
        have h2 : (p s).2 ≤ -2 := by omega
        have : (p s).2 * (d : ℤ) ≤ -2 * d := mul_le_mul_of_nonneg_right h2 hd0.le
        have hrd : (r : ℤ) ≤ d := by have := Int.natCast_nonneg (diam e); omega
        have : (s : ℤ) < r := by exact_mod_cast hsr
        have : (1 : ℤ) ≤ m := by exact_mod_cast hm1
        nlinarith
      · have hle : t s ≤ n := by
          rw [hts]
          have : m ≤ n := (e.min'_le_max' hne).trans hMn
          have : (m : ℤ) ≤ n := by exact_mod_cast this
          have : (0 : ℤ) ≤ s := Int.natCast_nonneg _
          linarith
        have : (p s).2 = t s / d := rfl
        rw [this]
        exact Int.ediv_le_ediv hd0 hle
    · unfold batchEdges
      refine Finset.mem_filter.mpr ⟨he, fun v hv => ?_⟩
      rw [mem_window]
      refine ⟨hsub hv, ?_, ?_⟩
      · rw [hdecomp s, ht]
        have : m ≤ v := e.min'_le v hv
        have : (m : ℤ) ≤ v := by exact_mod_cast this
        have : (0 : ℤ) ≤ s := Int.natCast_nonneg _
        simp only; linarith
      · have hvM : v ≤ M := e.le_max' v hv
        have hvM' : (v : ℤ) ≤ M := by exact_mod_cast hvM
        have : ((p s).1 : ℤ) + ((p s).2 + 1) * d - 1 = t s + d - 1 := by
          rw [← hdecomp s]; ring
        rw [this, ht]
        have : (s : ℤ) + 1 ≤ r := by exact_mod_cast hsr
        simp only
        linarith
  have hinj : Set.InjOn p (Finset.range r) := by
    intro s1 _ s2 _ h
    have h1 := hdecomp s1
    have h2 := hdecomp s2
    rw [h] at h1
    rw [h1] at h2
    simp only [ht] at h2
    omega
  rw [← Finset.sum_product']
  calc (r : ℝ) = ∑ q ∈ (Finset.range r).image p, (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_image_of_injOn hinj, Finset.card_range, nsmul_eq_mul,
          mul_one]
    _ = ∑ q ∈ (Finset.range r).image p, (if e ∈ batchEdges E n d q.1 q.2 then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
        rw [if_pos (hgood s hs).2]
    _ ≤ ∑ q ∈ Finset.range d ×ˢ batchIndices n d,
          (if e ∈ batchEdges E n d q.1 q.2 then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
          exact (hgood s hs).1
        · intro q _ _; split_ifs <;> norm_num

end Aux_HyperMatchDelay_reduction_4

open HyperMatchDelay.Batching Aux_HyperMatchDelay_reduction_4 in
theorem solution (n d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w)
    (Mt : Finset (Finset ℕ)) (hMt : IsMatching E Mt)
    (Mzi : ℕ → ℤ → Finset (Finset ℕ))
    (hMzi : ∀ z ∈ Finset.range d, ∀ i ∈ batchIndices n d,
      IsMatching (batchEdges E n d z i) (Mzi z i))
    (h3 : ∀ z ∈ Finset.range d, ∀ i ∈ batchIndices n d,
      weight w (Mt.filter (fun e => (d : ℤ) - k < (diam e : ℤ)) ∩ batchEdges E n d z i) +
        (1 / (k : ℝ)) *
          weight w (Mt.filter (fun e => (diam e : ℤ) ≤ (d : ℤ) - k) ∩ batchEdges E n d z i) ≤
      weight w (Mzi z i)) :
    weight w Mt / d ≤
      (1 / (d : ℝ)) * ∑ z ∈ Finset.range d, ∑ i ∈ batchIndices n d, weight w (Mzi z i) := by
  classical
  set I := batchIndices n d
  set L := Mt.filter (fun e => (d : ℤ) - k < (diam e : ℤ)) with hL
  set S := Mt.filter (fun e => (diam e : ℤ) ≤ (d : ℤ) - k) with hS
  set N : Finset ℕ → ℝ := fun e => ∑ z ∈ Finset.range d, ∑ i ∈ I,
    (if e ∈ batchEdges E n d z i then (1 : ℝ) else 0) with hN
  have hwinter : ∀ (A : Finset (Finset ℕ)) z i, weight w (A ∩ batchEdges E n d z i) =
      ∑ e ∈ A, (if e ∈ batchEdges E n d z i then w e else 0) := by
    intro A z i
    unfold weight
    rw [Finset.sum_ite_mem]
  have hswap : ∀ A : Finset (Finset ℕ), ∑ z ∈ Finset.range d, ∑ i ∈ I,
      weight w (A ∩ batchEdges E n d z i) = ∑ e ∈ A, w e * N e := by
    intro A
    simp only [hwinter, hN, Finset.mul_sum]
    symm
    calc ∑ e ∈ A, ∑ z ∈ Finset.range d, ∑ i ∈ I,
          w e * (if e ∈ batchEdges E n d z i then (1 : ℝ) else 0)
        = ∑ z ∈ Finset.range d, ∑ e ∈ A, ∑ i ∈ I,
          w e * (if e ∈ batchEdges E n d z i then (1 : ℝ) else 0) := Finset.sum_comm
      _ = ∑ z ∈ Finset.range d, ∑ i ∈ I, ∑ e ∈ A,
          w e * (if e ∈ batchEdges E n d z i then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun z _ => Finset.sum_comm
      _ = ∑ z ∈ Finset.range d, ∑ i ∈ I, ∑ e ∈ A,
          (if e ∈ batchEdges E n d z i then w e else 0) := by
          refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun e _ => ?_
          split_ifs <;> simp
  have hwnn : ∀ e ∈ Mt, 0 ≤ w e := fun e he => (hE e (hMt.1 he)).2.2.2.2
  have hLb : weight w L ≤ ∑ e ∈ L, w e * N e := by
    unfold weight
    refine Finset.sum_le_sum fun e he => ?_
    have heM := (Finset.mem_filter.mp he).1
    have hdiam : diam e < d := (hE e (hMt.1 heM)).2.2.1
    have := count_batches n d k hd E w hE e (hMt.1 heM) 1 le_rfl (by push_cast; omega)
    rw [Nat.cast_one] at this
    calc w e = w e * 1 := (mul_one _).symm
      _ ≤ w e * N e := mul_le_mul_of_nonneg_left this (hwnn e heM)
  have hSb : weight w S ≤ (1 / (k : ℝ)) * ∑ e ∈ S, w e * N e := by
    unfold weight
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun e he => ?_
    obtain ⟨heM, hdk⟩ := Finset.mem_filter.mp he
    have := count_batches n d k hd E w hE e (hMt.1 heM) k hk hdk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have h2 : w e * k ≤ w e * N e := mul_le_mul_of_nonneg_left this (hwnn e heM)
    calc w e = 1 / (k : ℝ) * (w e * k) := by field_simp
      _ ≤ 1 / (k : ℝ) * (w e * N e) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsplit : weight w Mt = weight w L + weight w S := by
    unfold weight
    rw [hL, hS, ← Finset.sum_filter_add_sum_filter_not Mt (fun e => (d : ℤ) - k < (diam e : ℤ))]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext e; simp [not_lt]
  have htot : weight w Mt ≤ ∑ z ∈ Finset.range d, ∑ i ∈ I, weight w (Mzi z i) := by
    calc weight w Mt = weight w L + weight w S := hsplit
      _ ≤ ∑ e ∈ L, w e * N e + (1 / (k : ℝ)) * ∑ e ∈ S, w e * N e := add_le_add hLb hSb
      _ = ∑ z ∈ Finset.range d, ∑ i ∈ I, (weight w (L ∩ batchEdges E n d z i) +
            (1 / (k : ℝ)) * weight w (S ∩ batchEdges E n d z i)) := by
          rw [← hswap L, ← hswap S, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ ≤ ∑ z ∈ Finset.range d, ∑ i ∈ I, weight w (Mzi z i) :=
          Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun i hi => h3 z hz i hi
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_eq_mul_one_div, mul_comm]
  exact mul_le_mul_of_nonneg_left htot (by positivity)
