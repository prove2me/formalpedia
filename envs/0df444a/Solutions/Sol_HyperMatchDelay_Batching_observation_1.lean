-- Prove2me | solution 1 for HyperMatchDelay.Batching.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:04:08.100801+00:00
-- url     : https://prove2.me/submissions/f95bfbc9-ff53-4973-ba93-aa6a576e3361

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

end HyperMatchDelay.Batching

open HyperMatchDelay.Batching

theorem solution (n d k : ℕ) (hd : 1 ≤ d) (E : Finset (Finset ℕ))
    (w : Finset ℕ → ℝ) (hE : IsShareability n d k E w) (e : Finset ℕ) (he : e ∈ E) :
    d - diam e ≤ ((Finset.range d).filter (fun z => e ∈ shiftEdges E n d z)).card := by
  obtain ⟨hsub, hne, hdiam, -, -⟩ := hE e he
  set a := e.min' hne with ha
  set b := e.max' hne with hb
  have hdiam' : diam e = b - a := by simp [diam, hne, ha, hb]
  have hamem : a ∈ e := Finset.min'_mem e hne
  have hbmem : b ∈ e := Finset.max'_mem e hne
  have hab : a ≤ b := Finset.min'_le e b hbmem
  have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hsub hamem)).1
  have hbn : b ≤ n := (Finset.mem_Icc.mp (hsub hbmem)).2
  have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
  let f : ℕ → ℕ := fun r => (((a : ℤ) - r) % d).toNat
  have hf : ∀ r ∈ Finset.range (d - diam e),
      (((a : ℤ) - r) % d) = (f r : ℤ) := by
    intro r _
    have : 0 ≤ ((a : ℤ) - r) % d := Int.emod_nonneg _ hdpos.ne'
    simp [f, Int.toNat_of_nonneg this]
  calc d - diam e = (Finset.range (d - diam e)).card := by simp
    _ ≤ _ := Finset.card_le_card_of_injOn f ?_ ?_
  · intro r hr
    have hr : r ∈ Finset.range (d - diam e) := hr
    have hr' : r < d - diam e := Finset.mem_range.mp hr
    have hrd : r < d := by omega
    have hz := hf r hr
    have hz0 : 0 ≤ ((a : ℤ) - r) % d := Int.emod_nonneg _ hdpos.ne'
    have hzd : ((a : ℤ) - r) % d < d := Int.emod_lt_of_pos _ hdpos
    have hdecomp := Int.emod_add_mul_ediv ((a : ℤ) - r) d
    set i := ((a : ℤ) - r) / d with hi
    set z := f r with hzdef
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · have : (z : ℤ) < d := by rw [← hz]; exact hzd
      exact_mod_cast this
    · unfold shiftEdges
      rw [Finset.mem_biUnion]
      refine ⟨i, ?_, ?_⟩
      · rw [batchIndices, Finset.mem_Icc]
        constructor
        · by_contra hlt
          push_neg at hlt
          have : i ≤ -2 := by omega
          nlinarith
        · apply Int.le_ediv_of_mul_le hdpos
          have : (a : ℤ) ≤ n := by
            have := hab; have := hbn; omega
          nlinarith
      · unfold batchEdges
        rw [Finset.mem_filter]
        refine ⟨he, ?_⟩
        intro v hv
        have hvI := Finset.mem_Icc.mp (hsub hv)
        have hav : a ≤ v := Finset.min'_le e v hv
        have hvb : v ≤ b := Finset.le_max' e v hv
        unfold window
        rw [Finset.mem_filter]
        refine ⟨hsub hv, ?_, ?_⟩
        · rw [hz] at hdecomp
          have : (v : ℤ) ≥ a := by exact_mod_cast hav
          nlinarith
        · rw [hz] at hdecomp
          have : (v : ℤ) ≤ b := by exact_mod_cast hvb
          have h2 : (b : ℤ) = a + diam e := by rw [hdiam']; omega
          have h3 : (r : ℤ) + diam e + 1 ≤ d := by omega
          nlinarith
  · intro r1 hr1 r2 hr2 h
    have hr1 : r1 ∈ Finset.range (d - diam e) := hr1
    have hr2 : r2 ∈ Finset.range (d - diam e) := hr2
    have hr1' := Finset.mem_range.mp hr1
    have hr2' := Finset.mem_range.mp hr2
    have e1 := hf r1 hr1
    have e2 := hf r2 hr2
    have : ((a : ℤ) - r1) % d = ((a : ℤ) - r2) % d := by rw [e1, e2]; exact congrArg _ h
    have h3 : (d : ℤ) ∣ ((a : ℤ) - r2) - ((a : ℤ) - r1) := Int.ModEq.dvd this
    have h4 : ((a : ℤ) - r2) - ((a : ℤ) - r1) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h3
      rw [abs_lt]
      constructor <;> omega
    have : (r1 : ℤ) = r2 := by omega
    exact_mod_cast this

