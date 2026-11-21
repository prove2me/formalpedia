-- Prove2me | solution 1 for MulticlassOmni.Lipschitz.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:14:07.388745+00:00
-- url     : https://prove2.me/submissions/2a20836e-df4b-4524-8c5d-9639f112ec14

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_Packings
import Definitions.Def_MulticlassOmni_Lipschitz_Construction
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses
import Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_3
import Theorems.Thm_MulticlassOmni_Lipschitz_lemma_2_1

section
namespace MulticlassOmni.Dev.B3
open MulticlassOmni.Lipschitz

theorem eOne_eq {k : ℕ} (h : 0 < k) : eOne k = Pi.single (⟨0, h⟩ : Fin k) (1:ℝ) := by
  funext y
  by_cases hy : (y : ℕ) = 0
  · have : y = ⟨0, h⟩ := Fin.ext hy
    subst this; simp [eOne]
  · have : y ≠ ⟨0, h⟩ := fun e => hy (by simp [e])
    simp [eOne, hy, Pi.single_apply, this]

theorem dot_eOne {k : ℕ} (h : 0 < k) (v : Fin k → ℝ) : dot (eOne k) v = v ⟨0, h⟩ := by
  rw [eOne_eq h]
  simp only [dot]
  rw [Finset.sum_eq_single (⟨0, h⟩ : Fin k)]
  · simp
  · intro y _ hy; simp [Pi.single_apply, hy]
  · intro hh; exact absurd (Finset.mem_univ _) hh

end MulticlassOmni.Dev.B3
end

section
namespace MulticlassOmni.Dev.F43
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.B3

variable {k N : ℕ}

theorem dot_sub (v u w : Fin k → ℝ) : dot v (u - w) = dot v u - dot v w := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

theorem some_mem_avail (π : Fin N → Fin 2) (i : Fin N) : some i ∈ avail π ↔ π i = 1 := by
  simp [avail]

theorem none_mem_avail (π : Fin N → Fin 2) : none ∈ avail π := by simp [avail]

theorem aSel_mem (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (σ : Equiv.Perm (Fin N))
    (r : Fin k → ℝ) : aSel x η π σ r ∈ avail π := by
  classical
  unfold aSel
  by_cases h1 : ∀ a ∈ avail π, dot r (costA k) ≤ dot r (cost x η a)
  · rw [if_pos h1]; simp [avail]
  · rw [if_neg h1]
    simp only
    by_cases h2 : ((Finset.univ.filter
      (fun i => π i = 1 ∧ ∀ a ∈ avail π, dot r (costB x η i) ≤ dot r (cost x η a))).image σ).Nonempty
    · rw [dif_pos h2]
      have hmem := Finset.min'_mem _ h2
      obtain ⟨m, hm, hm2⟩ := Finset.mem_image.1 hmem
      have key : π (σ.symm (Finset.min' _ h2)) = 1 := by
        rw [← hm2]; simp only [Equiv.symm_apply_apply]; exact (Finset.mem_filter.1 hm).2.1
      exact (some_mem_avail π _).2 key
    · rw [dif_neg h2]; simp [avail]

theorem aSel_min (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (σ : Equiv.Perm (Fin N))
    (r : Fin k → ℝ) : ∀ a' ∈ avail π, dot r (cost x η (aSel x η π σ r)) ≤ dot r (cost x η a') := by
  classical
  intro a' ha'
  by_cases h1 : ∀ a ∈ avail π, dot r (costA k) ≤ dot r (cost x η a)
  · have : aSel x η π σ r = none := by unfold aSel; rw [if_pos h1]
    rw [this]; exact h1 a' ha'
  · have h1' := h1
    push Not at h1'
    obtain ⟨a0, ha0, ha0lt⟩ := h1'
    obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image (avail π) (fun a => dot r (cost x η a)) ⟨a0, ha0⟩
    have hbn : b ≠ none := by
      rintro rfl
      have := hbmin a0 ha0
      have e : cost x η none = costA k := rfl
      rw [e] at this
      linarith
    obtain ⟨i, rfl⟩ := Option.ne_none_iff_exists'.1 hbn
    have hπ : π i = 1 := by
      simp only [avail, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at hb
      rcases hb with h | ⟨j, hj, hji⟩
      · exact absurd h (by simp)
      · cases hji; exact hj
    have hMne : ((Finset.univ.filter
      (fun i => π i = 1 ∧ ∀ a ∈ avail π, dot r (costB x η i) ≤ dot r (cost x η a))).image σ).Nonempty :=
      ⟨σ i, Finset.mem_image.2 ⟨i, by simp [hπ]; exact hbmin, rfl⟩⟩
    have hsel : aSel x η π σ r = some (σ.symm ((Finset.univ.filter
      (fun i => π i = 1 ∧ ∀ a ∈ avail π, dot r (costB x η i) ≤ dot r (cost x η a))).image σ |>.min' hMne)) := by
      unfold aSel; rw [if_neg h1]; simp only; rw [dif_pos hMne]
    rw [hsel]
    have hmem := Finset.min'_mem _ hMne
    obtain ⟨m, hm, hm2⟩ := Finset.mem_image.1 hmem
    rw [← hm2]
    simp only [Equiv.symm_apply_apply]
    exact (Finset.mem_filter.1 hm).2.2 a' ha'

theorem aSel_none (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (σ : Equiv.Perm (Fin N))
    (r : Fin k → ℝ) (h : ∀ a ∈ avail π, dot r (costA k) ≤ dot r (cost x η a)) :
    aSel x η π σ r = none := by
  classical
  unfold aSel; rw [if_pos h]

theorem aSel_some (x : Fin N → Fin k → ℝ) (η : ℝ) (π : Fin N → Fin 2) (σ : Equiv.Perm (Fin N))
    (r : Fin k → ℝ) (i : Fin N) (hπ : π i = 1)
    (h : ∀ a ∈ avail π, a ≠ some i → dot r (cost x η (some i)) < dot r (cost x η a)) :
    aSel x η π σ r = some i := by
  classical
  have hA : none ∈ avail π := by simp [avail]
  have hi : some i ∈ avail π := by simp [avail, hπ]
  have h1 : ¬ ∀ a ∈ avail π, dot r (costA k) ≤ dot r (cost x η a) := by
    intro hh
    have := hh _ hi
    have := h none hA (by simp)
    simp only [cost] at *
    linarith
  have hM : (Finset.univ.filter
      (fun j => π j = 1 ∧ ∀ a ∈ avail π, dot r (costB x η j) ≤ dot r (cost x η a))) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hj2⟩
      by_contra hne
      have hjm : some j ∈ avail π := by simp [avail, hj]
      have := h (some j) hjm (by simpa using hne)
      have := hj2 (some i) hi
      simp only [cost] at *
      linarith
    · rintro rfl
      refine ⟨hπ, fun a ha => ?_⟩
      by_cases hai : a = some j
      · subst hai; exact le_refl _
      · exact (h a ha hai).le
  have hne : (({i} : Finset (Fin N)).image σ).Nonempty := by simp
  unfold aSel
  rw [if_neg h1]
  simp only [hM]
  rw [dif_pos (by simpa using hne)]
  simp

end MulticlassOmni.Dev.F43
end

section
namespace MulticlassOmni.Dev.F43
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.B3

variable {k N : ℕ}

theorem sum_vbar (hk : 0 < k) : ∑ y, vbar k y = 1 := by
  have : (k:ℝ) ≠ 0 := by positivity
  simp [vbar]; field_simp

theorem dot_costB (x : Fin N → Fin k → ℝ) (η : ℝ) (j : Fin N) (v : Fin k → ℝ) :
    dot v (costB x η j - costA k) =
      -(k:ℝ) * dot v (x j - vbar k) + (1 / 256 - 2 * η) * ∑ y, v y := by
  have : ∀ y, v y * (costB x η j - costA k) y =
      -(k:ℝ) * (v y * (x j - vbar k) y) + (1 / 256 - 2 * η) * v y := by
    intro y; simp [costB]; ring
  simp only [dot]
  rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]

theorem dot_x_w (hk : 0 < k) (xi xj : Fin k → ℝ) (hi : ∑ y, xi y = 1) (hj : ∑ y, xj y = 1) :
    dot xi (xj - vbar k) = dot (xi - vbar k) (xj - vbar k) := by
  have hw : ∑ y, (xj - vbar k) y = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hj, sum_vbar hk, sub_self]
  have : dot (xi - vbar k) (xj - vbar k) = dot xi (xj - vbar k) - dot (vbar k) (xj - vbar k) := by
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have h2 : dot (vbar k) (xj - vbar k) = 0 := by
    have e : dot (vbar k) (xj - vbar k) = (1 / (k:ℝ)) * ∑ y, (xj - vbar k) y := by
      simp only [dot, vbar, Finset.mul_sum]
    rw [e, hw]; simp
  linarith

theorem delta_e1 (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ) (j : Fin N) :
    dot (eOne k) (costB x η j - costA k) = 1 + 1 / 256 - (k:ℝ) * x j ⟨0, hk⟩ - 2 * η := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  simp [costB, costA, vbar, dot_eOne hk]
  field_simp
  ring

section gaps
variable (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ)
  (hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k))
  (hsph : ∀ i, ∑ y, (x i y - vbar k y) ^ 2 = 1 / (256 * (k:ℝ)))
  (hsep : ∀ i j, i ≠ j → dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / (256 * (k:ℝ)))

include hk hs hsph in
theorem delta_self (i : Fin N) : dot (x i) (costB x η i - costA k) = -2 * η := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  rw [dot_costB, (hs i).2, dot_x_w hk _ _ (hs i).2 (hs i).2]
  have : dot (x i - vbar k) (x i - vbar k) = 1 / (256 * (k:ℝ)) := by
    rw [← hsph i]; simp [dot, sq]
  rw [this]; field_simp; ring

include hk hs hsep in
theorem delta_other (i j : Fin N) (hij : i ≠ j) :
    2 * η ≤ dot (x i) (costB x η j - costA k) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  rw [dot_costB, (hs i).2, dot_x_w hk _ _ (hs i).2 (hs j).2]
  have := hsep i j hij
  rw [le_div_iff₀ (by positivity)] at this
  have h2 : (k:ℝ) * dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / 256 := by
    have : (k:ℝ) * dot (x i - vbar k) (x j - vbar k) * 256 ≤ 1 - 1024 * η := by nlinarith
    linarith
  nlinarith

end gaps

theorem dot_qLip (x : Fin N → Fin k → ℝ) (η : ℝ) (b : Fin 2) (i : Fin N) (w : Fin k → ℝ) :
    dot (qLip x η b i) w = alpha x η b i * dot (eOne k) w + (1 - alpha x η b i) * dot (x i) w := by
  simp only [dot, qLip, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro y _ <;> ring

end MulticlassOmni.Dev.F43
end

section
namespace MulticlassOmni.Dev.F43
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.B3

variable {k N : ℕ}

theorem alpha_facts (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 16384)
    (h1 : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ))) (b : Fin 2) (i : Fin N) :
    0 ≤ alpha x η b i ∧ alpha x η b i ≤ 1 ∧
      alpha x η b i * (dot (eOne k) (costB x η i - costA k) + 2 * η) = (3 - 2 * ((b : ℕ) : ℝ)) * η := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hx1 : (k:ℝ) * x i ⟨0, hk⟩ ≤ 15 / 16 := by
    have := h1 i ⟨0, hk⟩ rfl
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have hDpos : 17 / 256 ≤ dot (eOne k) (costB x η i - costA k) + 2 * η := by
    rw [delta_e1 hk]; linarith
  have hbl : ((b : ℕ) : ℝ) = 0 ∨ ((b : ℕ) : ℝ) = 1 := by
    have := b.isLt
    interval_cases hb : (b : ℕ) <;> simp
  refine ⟨?_, ?_, ?_⟩
  · unfold alpha
    apply div_nonneg
    · rcases hbl with h | h <;> rw [h] <;> nlinarith
    · linarith
  · unfold alpha
    rw [div_le_one (by linarith)]
    rcases hbl with h | h <;> rw [h] <;> nlinarith
  · unfold alpha
    field_simp

theorem core (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ) (hη0 : 0 < η) (hη : η ≤ 1 / 16384)
    (hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k))
    (h1 : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ)))
    (hsph : ∀ i, ∑ y, (x i y - vbar k y) ^ 2 = 1 / (256 * (k:ℝ)))
    (hsep : ∀ i j, i ≠ j → dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / (256 * (k:ℝ)))
    (σ : Equiv.Perm (Fin N)) (i : Fin N) (b : Fin 2) (β : ℕ) (π : Fin N → Fin 2)
    (hβ : β = 1 ∨ β = 2) (hπb : π i = 1 → (b : ℕ) = β - 1) :
    ∃ astar, aSel x η π σ (bench x β i) = astar ∧ astar ∈ avail π ∧
      ∀ a ∈ avail π, a ≠ astar →
        dot (qLip x η b i) (cost x η astar) + η ≤ dot (qLip x η b i) (cost x η a) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hx1 : ∀ j, (k:ℝ) * x j ⟨0, hk⟩ ≤ 15 / 16 := by
    intro j
    have := h1 j ⟨0, hk⟩ rfl
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  have de1 : ∀ j, 2 * η ≤ dot (eOne k) (costB x η j - costA k) := by
    intro j; rw [delta_e1 hk]; linarith [hx1 j]
  obtain ⟨hα0, hα1, hαD⟩ := alpha_facts hk x η hη0 hη h1 b i
  set q := qLip x η b i with hq
  have dsub : ∀ j, dot q (costB x η j) = dot q (costA k) + dot q (costB x η j - costA k) := by
    intro j; rw [dot_sub]; ring
  have Qother : ∀ j, j ≠ i → 2 * η ≤ dot q (costB x η j - costA k) := by
    intro j hj
    rw [hq, dot_qLip]
    have := de1 j
    have := delta_other hk x η hs hsep i j (Ne.symm hj)
    nlinarith
  have Qself : dot q (costB x η i - costA k) = (1 - 2 * ((b : ℕ) : ℝ)) * η := by
    rw [hq, dot_qLip, delta_self hk x η hs hsph i]
    have := delta_e1 hk x η i
    have hD : dot (eOne k) (costB x η i - costA k) = (dot (eOne k) (costB x η i - costA k) + 2 * η) - 2 * η := by ring
    rw [hD]
    nlinarith
  have hcA : ∀ a : Option (Fin N), a = none ∨ ∃ j, a = some j := by
    intro a; cases a with
    | none => left; rfl
    | some j => right; exact ⟨j, rfl⟩
  have cn : cost x η none = costA k := rfl
  have cs : ∀ j, cost x η (some j) = costB x η j := fun _ => rfl
  by_cases hcase : β = 1 ∨ π i = 0
  · -- A is the Bayes action
    have hbench : ∀ j, π j = 1 → 0 ≤ dot (bench x β i) (costB x η j - costA k) := by
      intro j hj
      by_cases hb1 : β = 1
      · simp only [bench, hb1, if_true]
        have := de1 j; linarith
      · have hpi : π i = 0 := by tauto
        have hji : j ≠ i := by rintro rfl; omega
        simp only [bench, hb1, if_false]
        have := delta_other hk x η hs hsep i j (Ne.symm hji); linarith
    refine ⟨none, ?_, none_mem_avail π, ?_⟩
    · apply aSel_none
      intro a ha
      rcases hcA a with rfl | ⟨j, rfl⟩
      · exact le_refl _
      · rw [cs]
        have hj := (some_mem_avail π j).1 ha
        have := hbench j hj
        rw [dot_sub] at this; linarith
    · intro a ha hne
      rcases hcA a with rfl | ⟨j, rfl⟩
      · exact absurd rfl hne
      · rw [cn, cs, dsub j]
        have hj := (some_mem_avail π j).1 ha
        by_cases hji : j = i
        · subst hji
          have hb0 : (b : ℕ) = 0 := by
            have := hπb hj
            rcases hcase with h | h
            · omega
            · omega
          rw [Qself, hb0]
          simp
          try linarith
        · have := Qother j hji
          linarith
  · push Not at hcase
    obtain ⟨hb1, hpi⟩ := hcase
    have hb2 : β = 2 := by omega
    have hπ1 : π i = 1 := by have := Fin.is_lt (π i); omega
    have hb1' : (b : ℕ) = 1 := by have := hπb hπ1; omega
    have hb1R : ((b : ℕ) : ℝ) = 1 := by exact_mod_cast hb1'
    have hbench : bench x β i = x i := by simp [bench, hb1]
    refine ⟨some i, ?_, (some_mem_avail π i).2 hπ1, ?_⟩
    · rw [hbench]
      apply aSel_some x η π σ _ i hπ1
      intro a ha hne
      rcases hcA a with rfl | ⟨j, rfl⟩
      · have := delta_self hk x η hs hsph i
        rw [dot_sub] at this
        rw [cn, cs]
        linarith
      · rw [cs, cs]
        have hji : j ≠ i := fun e => hne (by rw [e])
        have := delta_other hk x η hs hsep i j (Ne.symm hji)
        have h2 := delta_self hk x η hs hsph i
        rw [dot_sub] at this h2
        linarith
    · intro a ha hne
      rcases hcA a with rfl | ⟨j, rfl⟩
      · rw [cn, cs, dsub i, Qself, hb1R]; linarith
      · rw [cs, cs, dsub j, dsub i, Qself, hb1R]
        have hji : j ≠ i := fun e => hne (by rw [e])
        have := Qother j hji
        linarith

end MulticlassOmni.Dev.F43
end

section
namespace MulticlassOmni.Dev.F43

open MulticlassOmni.Lipschitz

theorem eta_small (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (hlt : ε < (δ ^ 2 / 192) ^ 2 / ((k : ℝ) * Real.log ((k : ℝ) + 1))) :
    0 < eta k ε ∧ eta k ε ≤ δ := by
  set m := δ ^ 2 / 192 with hm
  have hm0 : 0 < m := by positivity
  have hm1 : m ≤ 1 := by rw [hm]; nlinarith
  set c := m ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hL : 1 < Real.log ((k : ℝ) + 1) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  set L := Real.log ((k : ℝ) + 1) with hLdef
  have hs : (k:ℝ) * ε < c / L := by
    have := hlt
    rw [lt_div_iff₀ (by positivity)] at this
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  set s := (k:ℝ) * ε with hsdef
  have hs0 : 0 < s := by positivity
  have hsL : s * L < c := by rwa [lt_div_iff₀ (by positivity)] at hs
  have hsc : s < c := by
    have : c / L < c := by rw [div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  have hc1 : c ≤ 1 := by rw [hc]; nlinarith
  have hε1 : ε < 1 := by
    have : ε ≤ s := by rw [hsdef]; nlinarith
    linarith
  have hlogε : 0 < Real.log (1 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  have hX0 : 0 < (k:ℝ) * ε * Real.log (1 / ε) := by positivity
  refine ⟨by unfold eta; positivity, ?_⟩
  -- bound X
  have hlogk : Real.log (k:ℝ) ≤ L := Real.log_le_log (by linarith) (by linarith)
  have hsplit : Real.log (1 / ε) = Real.log (k:ℝ) - Real.log s := by
    rw [one_div, Real.log_inv, hsdef, Real.log_mul (by positivity) hε.ne']
    ring
  set u := Real.sqrt s with hu
  have hu0 : 0 < u := Real.sqrt_pos.2 hs0
  have hus : u ^ 2 = s := Real.sq_sqrt hs0.le
  have hlogs : Real.log s = 2 * Real.log u := by
    rw [← hus, Real.log_pow]; norm_num
  have hlu : -Real.log u ≤ 1 / u := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / u by positivity)
    rw [one_div, Real.log_inv] at this
    rw [one_div]; linarith
  have hu_lt : u < m := by
    rw [hu]; rw [show m = Real.sqrt (m ^ 2) by rw [Real.sqrt_sq hm0.le]]
    exact Real.sqrt_lt_sqrt hs0.le hsc
  have h1 : s * Real.log (k:ℝ) ≤ s * L := mul_le_mul_of_nonneg_left hlogk hs0.le
  have h2 : s * (-Real.log s) ≤ 2 * u := by
    rw [hlogs, ← hus]
    have : u ^ 2 * (-(2 * Real.log u)) = 2 * u ^ 2 * (-Real.log u) := by ring
    rw [this]
    have h3 : 2 * u ^ 2 * (-Real.log u) ≤ 2 * u ^ 2 * (1 / u) :=
      mul_le_mul_of_nonneg_left hlu (by positivity)
    have h4 : 2 * u ^ 2 * (1 / u) = 2 * u := by field_simp
    linarith
  have hX : (k:ℝ) * ε * Real.log (1 / ε) ≤ (δ / 8) ^ 2 := by
    have : (k:ℝ) * ε * Real.log (1 / ε) = s * Real.log (k:ℝ) + s * (-Real.log s) := by
      rw [hsplit, ← hsdef]; ring
    rw [this]
    have : (δ / 8) ^ 2 = 3 * m := by rw [hm]; ring
    rw [this]
    have : c ≤ m := by rw [hc]; nlinarith
    nlinarith
  unfold eta
  have := Real.sqrt_le_sqrt hX
  rw [Real.sqrt_sq (by positivity)] at this
  linarith

end MulticlassOmni.Dev.F43
end

section
namespace MulticlassOmni.Lipschitz
open MulticlassOmni.Dev.F43

theorem chk_lemma_4_3 :
    ∀ Cpack : ℝ, 0 < Cpack → ∃ c : ℝ, 0 < c ∧
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε < c / ((k : ℝ) * Real.log ((k : ℝ) + 1)) →
        ∀ (N : ℕ) (x : Fin N → Fin k → ℝ), IsSection41Packing Cpack k (eta k ε) x →
          ∀ σ : Equiv.Perm (Fin N),
            (∀ π : Fin N → Fin 2, IsBoundedProper (hardLoss x (eta k ε) π σ)) ∧
            ∀ (i : Fin N) (b : Fin 2) (β : ℕ) (π : Fin N → Fin 2),
              (β = 1 ∨ β = 2) → (π i = 1 → (b : ℕ) = β - 1) →
                (∀ r ∈ stdSimplex ℝ (Fin k),
                  expect (qLip x (eta k ε) b i)
                      (hardLoss x (eta k ε) π σ (bench x β i)) ≤
                    expect (qLip x (eta k ε) b i) (hardLoss x (eta k ε) π σ r)) ∧
                ∀ r ∈ stdSimplex ℝ (Fin k),
                  eta k ε * (if aSel x (eta k ε) π σ r ≠ aSel x (eta k ε) π σ (bench x β i)
                      then 1 else 0) ≤
                    expect (qLip x (eta k ε) b i)
                      (fun y => hardLoss x (eta k ε) π σ r y -
                        hardLoss x (eta k ε) π σ (bench x β i) y) ∧
                  0 ≤ eta k ε * (if aSel x (eta k ε) π σ r ≠ aSel x (eta k ε) π σ (bench x β i)
                      then 1 else 0) := by
  intro Cpack hC
  obtain ⟨C₁, η₀, _, hη₀, hB3⟩ := lemma_B_3 Cpack hC
  set δ := min η₀ (1 / 16384) with hδ
  have hδ0 : 0 < δ := lt_min hη₀ (by norm_num)
  have hδ1 : δ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  refine ⟨(δ ^ 2 / 192) ^ 2, by positivity, ?_⟩
  intro k hk ε hε hlt N x hx σ
  obtain ⟨hη0, hηδ⟩ := eta_small δ hδ0 hδ1 k hk ε hε hlt
  set η := eta k ε with hηdef
  have hηA : η ≤ η₀ := le_trans hηδ (min_le_left _ _)
  have hηB : η ≤ 1 / 16384 := le_trans hηδ (min_le_right _ _)
  have hk0 : 0 < k := by omega
  obtain ⟨_, hcost, _⟩ := hB3 k hk η hη0 hηA N x hx
  obtain ⟨X₀, hX, hinj, hmem, _⟩ := hx
  obtain ⟨_, hsimp, _, hfirst, hsph, hsep⟩ := hX
  have hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k) := fun i => hsimp _ (hmem i)
  have h1 : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ)) :=
    fun i y hy => hfirst _ (hmem i) y hy
  have hsph' : ∀ i, ∑ y, (x i y - vbar k y) ^ 2 = 1 / (256 * (k:ℝ)) :=
    fun i => hsph _ (hmem i)
  have hsep' : ∀ i j, i ≠ j → dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / (256 * (k:ℝ)) := by
    intro i j hij
    have := hsep _ (hmem i) _ (hmem j) (fun e => hij (hinj e))
    have e : 8000 * (16 * η / 125) = 1024 * η := by ring
    rwa [e] at this
  have dcomm : ∀ u v : Fin k → ℝ, dot u v = dot v u := by
    intro u v; simp [dot, mul_comm]
  refine ⟨?_, ?_⟩
  · intro π
    refine ⟨?_, ?_⟩
    · have := lemma_2_1 (A := ↥(avail π)) (fun a => cost x η a.1)
        (fun r => ⟨aSel x η π σ r, aSel_mem x η π σ r⟩)
        (by
          intro r _ a'
          rw [dcomm, dcomm (cost x η a'.1)]
          exact aSel_min x η π σ r a'.1 a'.2)
      exact this
    · intro r _ y
      have := hcost (aSel x η π σ r) y
      show cost x η (aSel x η π σ r) y ∈ Set.Icc (0:ℝ) 1
      constructor <;> linarith [this.1, this.2]
  · intro i b β π hβ hπb
    obtain ⟨astar, hastar, hmemA, hgap⟩ :=
      core hk0 x η hη0 hηB hs h1 hsph' hsep' σ i b β π hβ hπb
    have hhard : hardLoss x η π σ (bench x β i) = cost x η astar := by
      funext y; simp only [hardLoss, hastar]
    have hexp : ∀ g : Fin k → ℝ, expect (qLip x η b i) g = dot (qLip x η b i) g := fun g => rfl
    have key : ∀ r, η * (if aSel x η π σ r ≠ astar then 1 else 0) ≤
        dot (qLip x η b i) (cost x η (aSel x η π σ r)) - dot (qLip x η b i) (cost x η astar) := by
      intro r
      by_cases h : aSel x η π σ r = astar
      · simp [h]
      · simp only [h, ne_eq, not_false_eq_true, if_true, mul_one]
        have := hgap _ (aSel_mem x η π σ r) h
        linarith
    refine ⟨fun r _ => ?_, fun r _ => ⟨?_, ?_⟩⟩
    · rw [hhard, hexp, hexp]
      have := key r
      have h0 : 0 ≤ η * (if aSel x η π σ r ≠ astar then 1 else 0) := by
        split_ifs <;> linarith
      show _ ≤ dot (qLip x η b i) (cost x η (aSel x η π σ r))
      linarith
    · rw [hexp, hhard]
      have e : dot (qLip x η b i) (fun y => hardLoss x η π σ r y - cost x η astar y) =
          dot (qLip x η b i) (cost x η (aSel x η π σ r)) - dot (qLip x η b i) (cost x η astar) := by
        rw [← dot_sub]; rfl
      rw [e]
      rw [hastar]
      exact key r
    · split_ifs <;> linarith

end MulticlassOmni.Lipschitz
end

theorem solution : type_of% @MulticlassOmni.Lipschitz.chk_lemma_4_3 := @MulticlassOmni.Lipschitz.chk_lemma_4_3
