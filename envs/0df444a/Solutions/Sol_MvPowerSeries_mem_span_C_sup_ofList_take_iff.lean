-- Prove2me | solution 1 for MvPowerSeries.mem_span_C_sup_ofList_take_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/f9807e81-c0f7-5db0-856e-eaf469c9bd7c

import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Order
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_mem_span_C_sup_ofList_take_iff

open MvPowerSeries

theorem solution {R : Type*} [CommRing R] (ϖ : R) (n k : ℕ) (F : MvPowerSeries (Fin n) R) :
    F ∈ Ideal.span {(C ϖ : MvPowerSeries (Fin n) R)} ⊔
        Ideal.ofList ((List.ofFn fun j : Fin n => (X j : MvPowerSeries (Fin n) R)).take k) ↔
      ∀ m : Fin n →₀ ℕ, (∀ j : Fin n, (j : ℕ) < k → m j = 0) → ϖ ∣ coeff m F := by

  have mem_span_C_iff : ∀ F : MvPowerSeries (Fin n) R,
      F ∈ Ideal.span {(C ϖ : MvPowerSeries (Fin n) R)} ↔ ∀ m : Fin n →₀ ℕ, ϖ ∣ coeff m F := by
    intro F
    rw [Ideal.mem_span_singleton]
    constructor
    · rintro ⟨G, rfl⟩ m
      rw [coeff_C_mul]
      exact dvd_mul_right _ _
    · intro h
      refine ⟨(fun m => (h m).choose : (Fin n →₀ ℕ) → R), ?_⟩
      ext m
      rw [coeff_C_mul]
      exact (h m).choose_spec

  have exists_eq_add_X_mul : ∀ (a : Fin n) (F : MvPowerSeries (Fin n) R),
      ∃ G H : MvPowerSeries (Fin n) R,
        F = G + (X a : MvPowerSeries (Fin n) R) * H ∧
          ∀ m : Fin n →₀ ℕ, coeff m G = if m a = 0 then coeff m F else 0 := by
    intro a F
    refine ⟨(fun m => if m a = 0 then coeff m F else 0 : (Fin n →₀ ℕ) → R),
      (fun m => coeff (m + Finsupp.single a 1) F : (Fin n →₀ ℕ) → R), ?_, fun m => rfl⟩
    ext m
    rw [map_add, X_def, coeff_monomial_mul]
    by_cases hma : m a = 0
    · have hnle : ¬ Finsupp.single a 1 ≤ m := by
        rw [Finsupp.single_le_iff]
        omega
      rw [if_neg hnle, add_zero]
      show coeff m F = if m a = 0 then coeff m F else 0
      rw [if_pos hma]
    · have hle : Finsupp.single a 1 ≤ m := by
        rw [Finsupp.single_le_iff]
        omega
      rw [if_pos hle, one_mul]
      show coeff m F = (if m a = 0 then coeff m F else 0) +
        coeff ((m - Finsupp.single a 1) + Finsupp.single a 1) F
      rw [if_neg hma, tsub_add_cancel_of_le hle, zero_add]

  induction k generalizing F with
  | zero =>
    simp only [List.take_zero, Ideal.ofList_nil, sup_bot_eq]
    rw [mem_span_C_iff]
    constructor
    · intro h m _
      exact h m
    · intro h m
      exact h m (fun j hj => absurd hj (Nat.not_lt_zero _))
  | succ k ih =>
    by_cases hk : k < n
    · have hlen : k < (List.ofFn fun j : Fin n => (X j : MvPowerSeries (Fin n) R)).length := by
        simpa using hk
      have htake : (List.ofFn fun j : Fin n => (X j : MvPowerSeries (Fin n) R)).take (k + 1)
          = (List.ofFn fun j : Fin n => (X j : MvPowerSeries (Fin n) R)).take k
            ++ [(X (⟨k, hk⟩ : Fin n) : MvPowerSeries (Fin n) R)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlen, List.getElem_ofFn]
        rfl
      rw [htake, Ideal.ofList_append, Ideal.ofList_singleton, ← sup_assoc]
      constructor
      · intro hF m hm
        obtain ⟨F₁, hF₁, F₂, hF₂, rfl⟩ := Submodule.mem_sup.mp hF
        rw [map_add]
        refine dvd_add ((ih F₁).mp hF₁ m (fun j hj => hm j (Nat.lt_succ_of_lt hj))) ?_
        obtain ⟨H, rfl⟩ := Ideal.mem_span_singleton.mp hF₂
        have hmk : m ⟨k, hk⟩ = 0 := hm ⟨k, hk⟩ (Nat.lt_succ_self k)
        rw [X_def, coeff_monomial_mul, if_neg]
        · exact dvd_zero _
        · rw [Finsupp.single_le_iff]
          omega
      · intro hF
        obtain ⟨G, H, hFGH, hG⟩ := exists_eq_add_X_mul (⟨k, hk⟩ : Fin n) F
        have hGmem : G ∈ Ideal.span {(C ϖ : MvPowerSeries (Fin n) R)} ⊔
            Ideal.ofList ((List.ofFn fun j : Fin n => (X j : MvPowerSeries (Fin n) R)).take k) := by
          refine (ih G).mpr ?_
          intro m hm
          by_cases hmk : m ⟨k, hk⟩ = 0
          · rw [hG m, if_pos hmk]
            refine hF m ?_
            intro j hj
            have hj' : (j : ℕ) < k ∨ (j : ℕ) = k := by omega
            rcases hj' with hj' | hj'
            · exact hm j hj'
            · have : j = (⟨k, hk⟩ : Fin n) := Fin.ext hj'
              rw [this]
              exact hmk
          · rw [hG m, if_neg hmk]
            exact dvd_zero _
        have hXH : (X (⟨k, hk⟩ : Fin n) : MvPowerSeries (Fin n) R) * H ∈
            Ideal.span {(X (⟨k, hk⟩ : Fin n) : MvPowerSeries (Fin n) R)} :=
          Ideal.mem_span_singleton.mpr ⟨H, rfl⟩
        rw [hFGH]
        exact Submodule.add_mem _ (Submodule.mem_sup_left hGmem) (Submodule.mem_sup_right hXH)
    · have hlen : (List.ofFn fun j : Fin n => (X j : MvPowerSeries (Fin n) R)).length ≤ k := by
        simp only [List.length_ofFn]
        omega
      rw [List.take_of_length_le (le_trans hlen (Nat.le_succ k)), ← List.take_of_length_le hlen]
      refine (ih F).trans ⟨fun h m hm => h m (fun j hj => hm j (Nat.lt_succ_of_lt hj)), fun h m hm => h m ?_⟩
      intro j hj
      refine hm j ?_
      have := j.isLt
      omega

end S_MvPowerSeries_mem_span_C_sup_ofList_take_iff
end P2MW
export P2MW.S_MvPowerSeries_mem_span_C_sup_ofList_take_iff (solution)
