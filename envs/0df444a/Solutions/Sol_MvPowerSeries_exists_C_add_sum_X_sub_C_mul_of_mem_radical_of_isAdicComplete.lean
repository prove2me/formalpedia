-- Prove2me | solution 1 for MvPowerSeries.exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d5baef91-a35a-5f00-8675-e3a808bb1b80

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete

set_option autoImplicit false

open MvPowerSeries

universe u

noncomputable section

namespace DivTopNil

variable {E : Type u} [CommRing E] {d : ℕ}

private def delta (i : Fin d) (c : MvPowerSeries (Fin d) E) : MvPowerSeries (Fin d) E :=
  fun α => if ∀ j, j < i → α j = 0 then coeff (α + Finsupp.single i 1) c else 0

private theorem coeff_delta (i : Fin d) (c : MvPowerSeries (Fin d) E) (α : Fin d →₀ ℕ) :
    coeff α (delta i c) = if ∀ j, j < i → α j = 0 then coeff (α + Finsupp.single i 1) c else 0 := rfl

private theorem delta_add (i : Fin d) (c c' : MvPowerSeries (Fin d) E) : delta i (c + c') = delta i c + delta i c' := by
  ext α; simp only [coeff_delta, map_add]; split_ifs <;> simp

private theorem coeff_X_mul (i : Fin d) (q : MvPowerSeries (Fin d) E) (β : Fin d →₀ ℕ) :
    coeff β (X i * q) = if Finsupp.single i 1 ≤ β then coeff (β - Finsupp.single i 1) q else 0 := by
  rw [X, coeff_monomial_mul]
  split_ifs <;> simp

private theorem eq_C_add_sum_X_mul_delta (c : MvPowerSeries (Fin d) E) :
    c = C (constantCoeff c) + ∑ i, X i * delta i c := by
  ext β
  rw [map_add, map_sum, coeff_C]
  simp only [coeff_X_mul, coeff_delta]
  by_cases hβ : β = 0
  · subst hβ
    rw [if_pos rfl, coeff_zero_eq_constantCoeff, Finset.sum_eq_zero, add_zero]
    intro i _
    rw [if_neg]
    intro h
    have := h i
    simp at this
  · rw [if_neg hβ, zero_add]

    have hne : (Finset.univ.filter fun j : Fin d => β j ≠ 0).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
      apply hβ
      ext j
      simpa using hcon (Finset.mem_univ j)
    set i₀ := (Finset.univ.filter fun j : Fin d => β j ≠ 0).min' hne with hi₀
    have hi₀mem : β i₀ ≠ 0 := by
      have := Finset.min'_mem _ hne
      rw [← hi₀, Finset.mem_filter] at this
      exact this.2
    have hi₀min : ∀ j, j < i₀ → β j = 0 := by
      intro j hj
      by_contra hcon
      have : i₀ ≤ j := by
        rw [hi₀]
        exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcon⟩)
      exact absurd hj (not_lt.mpr this)
    have hle : Finsupp.single i₀ 1 ≤ β := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr hi₀mem
    rw [Finset.sum_eq_single i₀]
    · rw [if_pos hle, if_pos, tsub_add_cancel_of_le hle]
      intro j hj
      rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (ne_of_gt hj), tsub_zero]
      exact hi₀min j hj
    · intro i _ hi
      rcases lt_or_gt_of_ne hi with hlt | hgt
      ·
        rw [if_neg]
        rw [Finsupp.single_le_iff]
        simp [hi₀min i hlt]
      ·
        split_ifs with h1 h2
        · exfalso
          have := h2 i₀ hgt
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (ne_of_gt hgt), tsub_zero] at this
          exact hi₀mem this
        · rfl
        · rfl
    · intro h; exact absurd (Finset.mem_univ i₀) h

variable (b : Fin d → E)

private def rho (c : MvPowerSeries (Fin d) E) : MvPowerSeries (Fin d) E := ∑ i, C (b i) * delta i c

private theorem step (c : MvPowerSeries (Fin d) E) :
    c = C (constantCoeff c) + ∑ i, (X i - C (b i)) * delta i c + rho b c := by
  conv_lhs => rw [eq_C_add_sum_X_mul_delta c]
  simp only [rho, sub_mul, Finset.sum_sub_distrib]
  abel

private def S (c : MvPowerSeries (Fin d) E) (m : ℕ) : E := ∑ l ∈ Finset.range m, constantCoeff ((rho b)^[l] c)
private def Q (c : MvPowerSeries (Fin d) E) (m : ℕ) (i : Fin d) : MvPowerSeries (Fin d) E :=
  ∑ l ∈ Finset.range m, delta i ((rho b)^[l] c)

private theorem iter (c : MvPowerSeries (Fin d) E) (m : ℕ) :
    c = C (S b c m) + ∑ i, (X i - C (b i)) * Q b c m i + (rho b)^[m] c := by
  induction m with
  | zero => simp [S, Q]
  | succ m ih =>
    have hS : S b c (m + 1) = S b c m + constantCoeff ((rho b)^[m] c) := Finset.sum_range_succ _ _
    have hQ : ∀ i, Q b c (m + 1) i = Q b c m i + delta i ((rho b)^[m] c) := fun i => Finset.sum_range_succ _ _
    rw [hS, Function.iterate_succ_apply', map_add]
    simp only [hQ, mul_add, Finset.sum_add_distrib]
    conv_lhs => rw [ih, step b ((rho b)^[m] c)]
    abel

private def AllIn (I : Ideal E) (c : MvPowerSeries (Fin d) E) : Prop := ∀ α, coeff α c ∈ I

private theorem allIn_top (c : MvPowerSeries (Fin d) E) : AllIn ⊤ c := fun _ => Submodule.mem_top

private theorem allIn_delta {I : Ideal E} {c : MvPowerSeries (Fin d) E} (h : AllIn I c) (i : Fin d) : AllIn I (delta i c) := by
  intro α
  rw [coeff_delta]
  split_ifs
  · exact h _
  · exact I.zero_mem

private theorem allIn_rho {I : Ideal E} {c : MvPowerSeries (Fin d) E} (h : AllIn I c) :
    AllIn (Ideal.span (Set.range b) * I) (rho b c) := by
  intro α
  rw [rho, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [coeff_C_mul]
  exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (allIn_delta h i α)

private theorem allIn_iterate_rho (c : MvPowerSeries (Fin d) E) (l : ℕ) :
    AllIn (Ideal.span (Set.range b) ^ l) ((rho b)^[l] c) := by
  induction l with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact allIn_top c
  | succ l ih =>
    rw [Function.iterate_succ_apply', pow_succ']
    exact allIn_rho b ih

end DivTopNil

end

noncomputable section

namespace DivTopNil

variable {E : Type u} [CommRing E] {d : ℕ} (b : Fin d → E)

private theorem pow_le_pow_of_le {I I' : Ideal E} (h : I ≤ I') : ∀ n : ℕ, I ^ n ≤ I' ^ n
  | 0 => by rw [pow_zero, pow_zero]
  | n + 1 => by rw [pow_succ, pow_succ]; exact Ideal.mul_mono (pow_le_pow_of_le h n) h

private theorem constantCoeff_iterate_rho_mem (c : MvPowerSeries (Fin d) E) (l : ℕ) :
    constantCoeff ((rho b)^[l] c) ∈ Ideal.span (Set.range b) ^ l := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact allIn_iterate_rho b c l 0

private theorem S_sub_S_mem (c : MvPowerSeries (Fin d) E) {m n : ℕ} (hmn : m ≤ n) :
    S b c n - S b c m ∈ Ideal.span (Set.range b) ^ m := by
  induction n, hmn using Nat.le_induction with
  | base => rw [sub_self]; exact Ideal.zero_mem _
  | succ n hmn ih =>
    have hS : S b c (n + 1) = S b c n + constantCoeff ((rho b)^[n] c) := Finset.sum_range_succ _ _
    rw [hS, add_sub_right_comm]
    exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right hmn (constantCoeff_iterate_rho_mem b c n))

private theorem coeff_Q_sub_Q_mem (c : MvPowerSeries (Fin d) E) (i : Fin d) (α : Fin d →₀ ℕ) {m n : ℕ} (hmn : m ≤ n) :
    coeff α (Q b c n i) - coeff α (Q b c m i) ∈ Ideal.span (Set.range b) ^ m := by
  induction n, hmn using Nat.le_induction with
  | base => rw [sub_self]; exact Ideal.zero_mem _
  | succ n hmn ih =>
    have hQ : Q b c (n + 1) i = Q b c n i + delta i ((rho b)^[n] c) := Finset.sum_range_succ _ _
    rw [hQ, map_add, add_sub_right_comm]
    exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right hmn (allIn_delta (allIn_iterate_rho b c n) i α))

private theorem mem_smul_top_iff {I : Ideal E} {x : E} : x ∈ (I • ⊤ : Submodule E E) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]

private theorem coeff_lin (x : E) (w : Fin d → MvPowerSeries (Fin d) E) (β : Fin d →₀ ℕ) :
    coeff β (C x + ∑ i, (X i - C (b i)) * w i) =
      (if β = 0 then x else 0) + ∑ i, ((if Finsupp.single i 1 ≤ β then coeff (β - Finsupp.single i 1) (w i) else 0)
        - b i * coeff β (w i)) := by
  rw [map_add, coeff_C, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sub_mul, map_sub, coeff_X_mul, coeff_C_mul]

private theorem coeff_lin_mem {I : Ideal E} {x : E} (hx : x ∈ I) {w : Fin d → MvPowerSeries (Fin d) E}
    (hw : ∀ i α, coeff α (w i) ∈ I) (β : Fin d →₀ ℕ) :
    coeff β (C x + ∑ i, (X i - C (b i)) * w i) ∈ I := by
  rw [coeff_lin]
  refine I.add_mem ?_ (I.sum_mem fun i _ => I.sub_mem ?_ (I.mul_mem_left _ (hw i β)))
  · split_ifs; exacts [hx, I.zero_mem]
  · split_ifs; exacts [hw i _, I.zero_mem]

private theorem main (J : Ideal E) [IsAdicComplete J E] (hb : ∀ i, b i ∈ J.radical) (c : MvPowerSeries (Fin d) E) :
    ∃ (r : E) (q : Fin d → MvPowerSeries (Fin d) E), c = C r + ∑ i, (X i - C (b i)) * q i := by

  have h𝔞 : Ideal.span (Set.range b) ≤ J.radical := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact hb i
  obtain ⟨M, hM⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h𝔞 (Submodule.fg_span (Set.finite_range b))
  have hpow : ∀ n : ℕ, Ideal.span (Set.range b) ^ (n * M) ≤ J ^ n := fun n => by
    rw [mul_comm, pow_mul]; exact pow_le_pow_of_le hM n

  have hS : ∀ {m n : ℕ}, m ≤ n → S b c (m * M) ≡ S b c (n * M) [SMOD (J ^ m • ⊤ : Submodule E E)] := by
    intro m n hmn
    rw [SModEq.sub_mem, mem_smul_top_iff, ← neg_sub, Ideal.neg_mem_iff]
    exact hpow m (S_sub_S_mem b c (Nat.mul_le_mul_right M hmn))
  obtain ⟨r, hr⟩ := IsPrecomplete.prec' (I := J) (fun n => S b c (n * M)) hS

  have hQ : ∀ (i : Fin d) (α : Fin d →₀ ℕ) {m n : ℕ}, m ≤ n →
      coeff α (Q b c (m * M) i) ≡ coeff α (Q b c (n * M) i) [SMOD (J ^ m • ⊤ : Submodule E E)] := by
    intro i α m n hmn
    rw [SModEq.sub_mem, mem_smul_top_iff, ← neg_sub, Ideal.neg_mem_iff]
    exact hpow m (coeff_Q_sub_Q_mem b c i α (Nat.mul_le_mul_right M hmn))
  choose L hL using fun i α => IsPrecomplete.prec' (I := J) (fun n => coeff α (Q b c (n * M) i)) (hQ i α)
  let q : Fin d → MvPowerSeries (Fin d) E := fun i α => L i α
  have hq : ∀ i α, coeff α (q i) = L i α := fun _ _ => rfl
  refine ⟨r, q, ?_⟩

  ext β
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, mem_smul_top_iff]

  have hit := iter b c (n * M)
  have hρ : coeff β ((rho b)^[n * M] c) ∈ J ^ n := hpow n (allIn_iterate_rho b c (n * M) β)
  have hdiff : coeff β (C (S b c (n * M)) + ∑ i, (X i - C (b i)) * Q b c (n * M) i) -
      coeff β (C r + ∑ i, (X i - C (b i)) * q i) ∈ J ^ n := by
    rw [← map_sub]
    have halg : (C (S b c (n * M)) + ∑ i, (X i - C (b i)) * Q b c (n * M) i) -
        (C r + ∑ i, (X i - C (b i)) * q i) =
        C (S b c (n * M) - r) + ∑ i, (X i - C (b i)) * (Q b c (n * M) i - q i) := by
      rw [map_sub]; simp only [mul_sub, Finset.sum_sub_distrib]; abel
    rw [halg]
    refine coeff_lin_mem b ?_ (fun i α => ?_) β
    · have h := hr n
      rw [SModEq.sub_mem, mem_smul_top_iff] at h
      exact h
    · have h := hL i α n
      rw [SModEq.sub_mem, mem_smul_top_iff] at h
      rw [map_sub, hq]
      exact h
  have : coeff β c - coeff β (C r + ∑ i, (X i - C (b i)) * q i) =
      (coeff β (C (S b c (n * M)) + ∑ i, (X i - C (b i)) * Q b c (n * M) i) -
        coeff β (C r + ∑ i, (X i - C (b i)) * q i)) +
      coeff β ((rho b)^[n * M] c) := by
    conv_lhs => rw [hit]
    rw [map_add]
    ring
  rw [this]
  exact (J ^ n).add_mem hdiff hρ

end DivTopNil

end

theorem solution
    {E : Type u} [CommRing E] (J : Ideal E) [IsAdicComplete J E]
    {d : ℕ} (b : Fin d → E) (hb : ∀ i, b i ∈ J.radical) (c : MvPowerSeries (Fin d) E) :
    ∃ (r : E) (q : Fin d → MvPowerSeries (Fin d) E),
      c = MvPowerSeries.C r + ∑ i, (MvPowerSeries.X i - MvPowerSeries.C (b i)) * q i := by
  obtain ⟨r, q, h⟩ := DivTopNil.main b J hb c
  exact ⟨r, q, h⟩

end S_MvPowerSeries_exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete
end P2MW
export P2MW.S_MvPowerSeries_exists_C_add_sum_X_sub_C_mul_of_mem_radical_of_isAdicComplete (solution)
