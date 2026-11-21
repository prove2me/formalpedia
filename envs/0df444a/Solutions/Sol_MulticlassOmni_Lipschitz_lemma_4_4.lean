-- Prove2me | solution 1 for MulticlassOmni.Lipschitz.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T19:33:33.774121+00:00
-- url     : https://prove2.me/submissions/8b15f7a6-8fc7-40d1-92cd-2161d16f7bb3

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses
import Definitions.Def_MulticlassOmni_Lipschitz_Packings
import Definitions.Def_MulticlassOmni_Lipschitz_Construction
import Theorems.Thm_MulticlassOmni_Lipschitz_lemma_B_3

section
namespace MulticlassOmni.Dev.Basic
open MulticlassOmni.Lipschitz

theorem coe_sum_ereal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

theorem isProper_of {k : ℕ} (ℓ : Loss k)
    (h : ∀ q ∈ stdSimplex ℝ (Fin k), ∀ r ∈ stdSimplex ℝ (Fin k),
      ∑ y, q y * ℓ q y ≤ ∑ y, q y * ℓ r y) : IsProper ℓ := by
  refine ⟨?_, ?_⟩
  · intro p hp i
    simp [toEReal, hp]
  · intro p hp q hq
    have e1 : ∑ i, (q i : EReal) * toEReal ℓ q i = ((∑ y, q y * ℓ q y : ℝ) : EReal) := by
      simp only [toEReal, hq, if_true]
      simp only [← EReal.coe_mul]; rw [coe_sum_ereal]
    have e2 : ∑ i, (q i : EReal) * toEReal ℓ p i = ((∑ y, q y * ℓ p y : ℝ) : EReal) := by
      simp only [toEReal, hp, if_true]
      simp only [← EReal.coe_mul]; rw [coe_sum_ereal]
    rw [e1, e2]
    exact_mod_cast h q hq p hp

end MulticlassOmni.Dev.Basic

namespace MulticlassOmni.Lipschitz
open MulticlassOmni.Dev.Basic

end MulticlassOmni.Lipschitz
end

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
/-! Abstract soft-min algebra for Lemma 4.4: a finite action set `A`, cost vectors `c a`,
temperature `γ > 0`. -/

noncomputable section

namespace MulticlassOmni.Dev.L44
open MulticlassOmni.Lipschitz

variable {α : Type} {k : ℕ}

/-- partition function -/
def Zf (A : Finset α) (c : α → Fin k → ℝ) (γ : ℝ) (r : Fin k → ℝ) : ℝ :=
  ∑ a ∈ A, Real.exp (-(dot r (c a)) / γ)

/-- soft-min -/
def smf (A : Finset α) (c : α → Fin k → ℝ) (γ : ℝ) (r : Fin k → ℝ) : ℝ :=
  -γ * Real.log (Zf A c γ r)

/-- soft-min weights -/
def wtf (A : Finset α) (c : α → Fin k → ℝ) (γ : ℝ) (r : Fin k → ℝ) (a : α) : ℝ :=
  Real.exp (-(dot r (c a)) / γ) / Zf A c γ r

/-- gradient -/
def grdf (A : Finset α) (c : α → Fin k → ℝ) (γ : ℝ) (r : Fin k → ℝ) : Fin k → ℝ :=
  ∑ a ∈ A, wtf A c γ r a • c a

/-- tangent value `H(r) + ⟨∇H(r), q - r⟩` -/
def Ff (A : Finset α) (c : α → Fin k → ℝ) (γ : ℝ) (r q : Fin k → ℝ) : ℝ :=
  smf A c γ r + dot (grdf A c γ r) (q - r)

variable (A : Finset α) (c : α → Fin k → ℝ) (γ : ℝ)

theorem dot_comm' (u v : Fin k → ℝ) : dot u v = dot v u := by
  simp [dot, mul_comm]

theorem dot_unitVec (g : Fin k → ℝ) (y : Fin k) : dot (unitVec y) g = g y := by
  simp [dot, unitVec, Pi.single_apply]

theorem dot_sub' (v u w : Fin k → ℝ) : dot v (u - w) = dot v u - dot v w := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]

theorem dot_sum_smul (f : α → ℝ) (d : Fin k → ℝ) :
    dot (∑ a ∈ A, f a • c a) d = ∑ a ∈ A, f a * dot (c a) d := by
  simp only [dot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun y _ => by ring))

theorem Zf_pos (hA : A.Nonempty) (r : Fin k → ℝ) : 0 < Zf A c γ r :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) hA

theorem wtf_pos (hA : A.Nonempty) (r : Fin k → ℝ) (a : α) : 0 < wtf A c γ r a :=
  div_pos (Real.exp_pos _) (Zf_pos A c γ hA r)

theorem sum_wtf (hA : A.Nonempty) (r : Fin k → ℝ) : ∑ a ∈ A, wtf A c γ r a = 1 := by
  unfold wtf
  rw [← Finset.sum_div]
  exact div_self (Zf_pos A c γ hA r).ne'

theorem exp_le_Zf (r : Fin k → ℝ) {a : α} (ha : a ∈ A) :
    Real.exp (-(dot r (c a)) / γ) ≤ Zf A c γ r :=
  Finset.single_le_sum (f := fun a => Real.exp (-(dot r (c a)) / γ))
    (fun _ _ => (Real.exp_pos _).le) ha

theorem wtf_le_one (hA : A.Nonempty) (r : Fin k → ℝ) {a : α} (ha : a ∈ A) :
    wtf A c γ r a ≤ 1 := by
  unfold wtf
  rw [div_le_one (Zf_pos A c γ hA r)]
  exact exp_le_Zf A c γ r ha

theorem log_wtf (hA : A.Nonempty) (r : Fin k → ℝ) (a : α) :
    Real.log (wtf A c γ r a) = -(dot r (c a)) / γ - Real.log (Zf A c γ r) := by
  unfold wtf
  rw [Real.log_div (Real.exp_pos _).ne' (Zf_pos A c γ hA r).ne', Real.log_exp]

/-- entropy form of the tangent value -/
theorem Ff_ent (hA : A.Nonempty) (hγ : γ ≠ 0) (r q : Fin k → ℝ) :
    Ff A c γ r q = ∑ a ∈ A, wtf A c γ r a * dot q (c a) +
      γ * ∑ a ∈ A, wtf A c γ r a * Real.log (wtf A c γ r a) := by
  unfold Ff smf grdf
  rw [dot_sum_smul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have h1 : ∀ a ∈ A, wtf A c γ r a * dot q (c a) +
      γ * (wtf A c γ r a * Real.log (wtf A c γ r a)) =
      wtf A c γ r a * dot (c a) (q - r) - γ * Real.log (Zf A c γ r) * wtf A c γ r a := by
    intro a _
    rw [log_wtf A c γ hA, dot_sub', dot_comm' (c a) q, dot_comm' (c a) r]
    field_simp
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_wtf A c γ hA]
  ring

/-- Gibbs variational inequality -/
theorem gibbs (w t : α → ℝ) (hw : ∀ a ∈ A, 0 < w a) (hs : ∑ a ∈ A, w a = 1) :
    ∑ a ∈ A, w a * t a - ∑ a ∈ A, w a * Real.log (w a) ≤
      Real.log (∑ a ∈ A, Real.exp (t a)) := by
  have hA : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h; simp at hs
  set Z := ∑ a ∈ A, Real.exp (t a) with hZ
  have hZ0 : 0 < Z := Finset.sum_pos (fun _ _ => Real.exp_pos _) hA
  have key : ∀ a ∈ A, w a * t a - w a * Real.log (w a) - w a * Real.log Z ≤
      Real.exp (t a) / Z - w a := by
    intro a ha
    have hwa := hw a ha
    have hx : 0 < Real.exp (t a) / (Z * w a) := by positivity
    have h1 := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_mul hZ0.ne' hwa.ne',
      Real.log_exp] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hwa.le
    have e : w a * (Real.exp (t a) / (Z * w a) - 1) = Real.exp (t a) / Z - w a := by
      field_simp
    rw [e] at h2
    nlinarith
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← hZ, div_self hZ0.ne', hs, ← Finset.sum_mul, hs] at hsum
  linarith

theorem ent_lower (hA : A.Nonempty) (r : Fin k → ℝ) :
    -Real.log (A.card : ℝ) ≤ ∑ a ∈ A, wtf A c γ r a * Real.log (wtf A c γ r a) := by
  have := gibbs A (wtf A c γ r) (fun _ => 0) (fun a _ => wtf_pos A c γ hA r a) (sum_wtf A c γ hA r)
  simp only [mul_zero, Finset.sum_const_zero, Real.exp_zero, Finset.sum_const, nsmul_eq_mul,
    mul_one, zero_sub] at this
  linarith

theorem ent_upper (hA : A.Nonempty) (r : Fin k → ℝ) :
    ∑ a ∈ A, wtf A c γ r a * Real.log (wtf A c γ r a) ≤ 0 := by
  apply Finset.sum_nonpos
  intro a ha
  have h0 := wtf_pos A c γ hA r a
  have h1 := wtf_le_one A c γ hA r ha
  exact mul_nonpos_of_nonneg_of_nonpos h0.le (Real.log_nonpos h0.le h1)

/-- tangent (supergradient) inequality -/
theorem tangent (hA : A.Nonempty) (hγ : 0 < γ) (r q : Fin k → ℝ) :
    smf A c γ q ≤ Ff A c γ r q := by
  rw [Ff_ent A c γ hA hγ.ne']
  have := gibbs A (wtf A c γ r) (fun a => -(dot q (c a)) / γ)
    (fun a _ => wtf_pos A c γ hA r a) (sum_wtf A c γ hA r)
  have e : ∑ a ∈ A, wtf A c γ r a * (-(dot q (c a)) / γ) =
      -(∑ a ∈ A, wtf A c γ r a * dot q (c a)) / γ := by
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => by ring)
  rw [e] at this
  unfold smf Zf
  set S := ∑ a ∈ A, wtf A c γ r a * dot q (c a)
  set E := ∑ a ∈ A, wtf A c γ r a * Real.log (wtf A c γ r a)
  set L := Real.log (∑ a ∈ A, Real.exp (-dot q (c a) / γ))
  have h2 := mul_le_mul_of_nonneg_left this hγ.le
  have e2 : γ * (-S / γ - E) = -S - γ * E := by field_simp
  rw [e2] at h2
  linarith

theorem Ff_self (r : Fin k → ℝ) : Ff A c γ r r = smf A c γ r := by
  simp [Ff, dot]

theorem expect_Ff (r q : Fin k → ℝ) (hq : ∑ y, q y = 1) :
    ∑ y, q y * Ff A c γ r (unitVec y) = Ff A c γ r q := by
  unfold Ff
  have h : ∀ y, q y * (smf A c γ r + dot (grdf A c γ r) (unitVec y - r)) =
      q y * smf A c γ r + q y * grdf A c γ r y - q y * dot (grdf A c γ r) r := by
    intro y
    rw [dot_sub', dot_comm', dot_unitVec]; ring
  rw [Finset.sum_congr rfl (fun y _ => h y), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, hq, dot_sub']
  simp only [dot, one_mul]
  rw [show ∑ x, q x * grdf A c γ r x = ∑ y, grdf A c γ r y * q y from
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
  ring

/-- upper range bound -/
theorem Ff_unit_le (hA : A.Nonempty) (hγ : 0 < γ) (y : Fin k) (hc : ∀ a ∈ A, c a y ≤ 3 / 4)
    (r : Fin k → ℝ) : Ff A c γ r (unitVec y) ≤ 3 / 4 := by
  rw [Ff_ent A c γ hA hγ.ne']
  have h1 := ent_upper A c γ hA r
  have h2 : ∑ a ∈ A, wtf A c γ r a * dot (unitVec y) (c a) ≤ ∑ a ∈ A, wtf A c γ r a * (3 / 4) := by
    apply Finset.sum_le_sum
    intro a ha
    rw [dot_unitVec]
    exact mul_le_mul_of_nonneg_left (hc a ha) (wtf_pos A c γ hA r a).le
  rw [← Finset.sum_mul, sum_wtf A c γ hA] at h2
  nlinarith

/-- lower range bound -/
theorem Ff_unit_ge (hA : A.Nonempty) (hγ : 0 < γ) (y : Fin k) (hc : ∀ a ∈ A, 1 / 4 ≤ c a y)
    (r : Fin k → ℝ) : 1 / 4 - γ * Real.log (A.card : ℝ) ≤ Ff A c γ r (unitVec y) := by
  refine le_trans ?_ (tangent A c γ hA hγ r (unitVec y))
  unfold smf Zf
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have h1 : ∑ a ∈ A, Real.exp (-dot (unitVec y) (c a) / γ) ≤
      (A.card : ℝ) * Real.exp (-(1 / 4) / γ) := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro a ha
    rw [dot_unitVec]
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hγ.le
    linarith [hc a ha]
  have hZ : 0 < ∑ a ∈ A, Real.exp (-dot (unitVec y) (c a) / γ) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hA
  have h2 := Real.log_le_log hZ h1
  rw [Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hγ.le
  have e : γ * (Real.log (A.card : ℝ) + -(1 / 4) / γ) = γ * Real.log (A.card : ℝ) - 1 / 4 := by
    field_simp; ring
  rw [e] at h3
  linarith

/-- the soft-min weight of a non-minimal action at a point with margin `η` -/
theorem wtf_le_exp (hγ : 0 < γ) (s : Fin k → ℝ) (η : ℝ) {a0 a : α} (ha0 : a0 ∈ A)
    (hm : dot s (c a0) + η ≤ dot s (c a)) : wtf A c γ s a ≤ Real.exp (-η / γ) := by
  have hA : A.Nonempty := ⟨a0, ha0⟩
  unfold wtf
  have hZ := exp_le_Zf A c γ s ha0
  calc Real.exp (-(dot s (c a)) / γ) / Zf A c γ s
      ≤ Real.exp (-(dot s (c a)) / γ) / Real.exp (-(dot s (c a0)) / γ) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hZ
    _ = Real.exp (-(dot s (c a)) / γ - -(dot s (c a0)) / γ) := by rw [Real.exp_sub]
    _ ≤ Real.exp (-η / γ) := by
        apply Real.exp_le_exp.2
        rw [← sub_div]
        apply div_le_div_of_nonneg_right _ hγ.le
        linarith

/-- (39): the excess at a point whose minimal action has margin `η` both there and at `q` -/
theorem regret_upper (hγ : 0 < γ) (η : ℝ) (hη : 0 ≤ η) (s q : Fin k → ℝ) {a0 : α} (ha0 : a0 ∈ A)
    (hu : ∀ a ∈ A, a ≠ a0 → dot s (c a0) + η ≤ dot s (c a))
    (hv : ∀ a ∈ A, a ≠ a0 → dot q (c a0) + η ≤ dot q (c a))
    (hv2 : ∀ a ∈ A, dot q (c a) - dot q (c a0) ≤ 1 / 2) :
    Ff A c γ s q - smf A c γ q ≤ (1 / 2 + γ) * ((A.card : ℝ) * Real.exp (-η / γ)) := by
  classical
  have hA : A.Nonempty := ⟨a0, ha0⟩
  set e := Real.exp (-η / γ) with he
  have he0 : 0 < e := Real.exp_pos _
  set v0 := dot q (c a0)
  -- (i) Ff s q ≤ v0 + card * e / 2
  have hF : Ff A c γ s q ≤ v0 + (A.card : ℝ) * e / 2 := by
    rw [Ff_ent A c γ hA hγ.ne']
    have h1 := ent_upper A c γ hA s
    have h2 : ∀ a ∈ A, wtf A c γ s a * dot q (c a) ≤ wtf A c γ s a * v0 + e / 2 := by
      intro a ha
      by_cases hae : a = a0
      · subst hae; linarith
      · have hw := wtf_le_exp A c γ hγ s η ha0 (hu a ha hae)
        have hw0 := wtf_pos A c γ hA s a
        have hd0 : 0 ≤ dot q (c a) - v0 := by linarith [hv a ha hae]
        have hd1 := hv2 a ha
        have : wtf A c γ s a * (dot q (c a) - v0) ≤ e * (1 / 2) :=
          mul_le_mul hw hd1 hd0 he0.le
        nlinarith
    have h3 := Finset.sum_le_sum h2
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_wtf A c γ hA, Finset.sum_const,
      nsmul_eq_mul] at h3
    nlinarith
  -- (ii) smf q ≥ v0 - γ * card * e
  have hS : v0 - γ * ((A.card : ℝ) * e) ≤ smf A c γ q := by
    unfold smf Zf
    have h1 : ∀ a ∈ A, Real.exp (-(dot q (c a)) / γ) ≤
        Real.exp (-v0 / γ) * ((if a = a0 then 1 else 0) + e) := by
      intro a ha
      by_cases hae : a = a0
      · subst hae; simp only [if_true]
        have : Real.exp (-v0 / γ) * 1 ≤ Real.exp (-v0 / γ) * (1 + e) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        simpa using this
      · simp only [hae, if_false, zero_add]
        rw [he, ← Real.exp_add]
        apply Real.exp_le_exp.2
        rw [← add_div]
        apply div_le_div_of_nonneg_right _ hγ.le
        linarith [hv a ha hae]
    have h2 := Finset.sum_le_sum h1
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq' A a0, if_pos ha0,
      Finset.sum_const, nsmul_eq_mul] at h2
    have hZ : 0 < ∑ a ∈ A, Real.exp (-(dot q (c a)) / γ) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) hA
    have h3 := Real.log_le_log hZ h2
    rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp] at h3
    have h4 : Real.log (1 + (A.card : ℝ) * e) ≤ (A.card : ℝ) * e := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + (A.card : ℝ) * e by positivity)
      linarith
    have h5 := mul_le_mul_of_nonneg_left (h3.trans (by linarith [h4] :
      -v0 / γ + Real.log (1 + (A.card : ℝ) * e) ≤ -v0 / γ + (A.card : ℝ) * e)) hγ.le
    have e6 : γ * (-v0 / γ + (A.card : ℝ) * e) = -v0 + γ * ((A.card : ℝ) * e) := by
      field_simp
    rw [e6] at h5
    show v0 - γ * ((A.card : ℝ) * e) ≤ -γ * Real.log (∑ a ∈ A, Real.exp (-dot q (c a) / γ))
    linarith
  nlinarith

/-- (41): the excess when the selected action at `r` is not `a0` -/
theorem regret_lower (hγ : 0 < γ) (η : ℝ) (hη : 0 ≤ η) (r q : Fin k → ℝ) {a0 b : α}
    (ha0 : a0 ∈ A) (hb : b ∈ A) (hba : b ≠ a0)
    (hv : ∀ a ∈ A, a ≠ a0 → dot q (c a0) + η ≤ dot q (c a))
    (hr : dot r (c b) ≤ dot r (c a0)) :
    η / 2 - γ * Real.log (A.card : ℝ) ≤ Ff A c γ r q - smf A c γ q := by
  classical
  have hA : A.Nonempty := ⟨a0, ha0⟩
  set v0 := dot q (c a0)
  set w := wtf A c γ r
  -- w a0 ≤ 1/2
  have hw0b : w a0 ≤ w b := by
    unfold w wtf
    apply div_le_div_of_nonneg_right _ (Zf_pos A c γ hA r).le
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ hγ.le
    linarith
  have hpair : w a0 + w b ≤ 1 := by
    have hsub : ({a0, b} : Finset α) ⊆ A := by
      intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun z _ _ => (wtf_pos A c γ hA r z).le)
    rw [Finset.sum_pair (Ne.symm hba), sum_wtf A c γ hA] at this
    exact this
  have hhalf : w a0 ≤ 1 / 2 := by linarith
  -- Σ w v ≥ v0 + η (1 - w a0)
  have hsum : v0 + η * (1 - w a0) ≤ ∑ a ∈ A, w a * dot q (c a) := by
    have h1 : ∀ a ∈ A, w a * v0 + (η * w a - η * (if a = a0 then w a else 0)) ≤
        w a * dot q (c a) := by
      intro a ha
      have hwa := wtf_pos A c γ hA r a
      by_cases hae : a = a0
      · subst hae; simp [v0]
      · simp only [hae, if_false, mul_zero, sub_zero]
        have := hv a ha hae
        nlinarith
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_ite_eq' A a0, if_pos ha0, sum_wtf A c γ hA] at h2
    linarith
  have hF : ∑ a ∈ A, w a * dot q (c a) - γ * Real.log (A.card : ℝ) ≤ Ff A c γ r q := by
    rw [Ff_ent A c γ hA hγ.ne']
    have := ent_lower A c γ hA r
    nlinarith
  have hS : smf A c γ q ≤ v0 := by
    unfold smf
    have h1 := exp_le_Zf A c γ q ha0
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hγ.le
    have e : γ * (-v0 / γ) = -v0 := by field_simp
    rw [e] at h3
    linarith
  nlinarith

end MulticlassOmni.Dev.L44
end
end

section
/-! Lemma 4.4, Lipschitz part: the tangent loss `F(r, e_y)` is `1/(4γ)`-Lipschitz in `ℓ1` on the
simplex, by the mean-value inequality on segments and a covariance bound on the derivative. -/

noncomputable section

namespace MulticlassOmni.Dev.L44
open MulticlassOmni.Lipschitz

variable {α : Type} {k : ℕ}

/-- covariance-type bound: `|E_s[G] E_s[E] - E_s[GE]|`, unnormalised -/
theorem cov_bound (A : Finset α) (s G E : α → ℝ) (M : ℝ) (hs : ∀ a ∈ A, 0 ≤ s a)
    (hG : ∀ a ∈ A, |G a| ≤ M) (hE : ∀ a ∈ A, ∀ b ∈ A, |E b - E a| ≤ 1) :
    |(∑ a ∈ A, s a * G a) * (∑ a ∈ A, s a * E a) - (∑ a ∈ A, s a * G a * E a) * (∑ a ∈ A, s a)|
      ≤ M * (∑ a ∈ A, s a) ^ 2 := by
  have e : (∑ a ∈ A, s a * G a) * (∑ a ∈ A, s a * E a) -
      (∑ a ∈ A, s a * G a * E a) * (∑ a ∈ A, s a) =
      ∑ a ∈ A, ∑ b ∈ A, s a * s b * G a * (E b - E a) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  have e2 : M * (∑ a ∈ A, s a) ^ 2 = ∑ a ∈ A, ∑ b ∈ A, s a * s b * M := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [e, e2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a ha => ?_))
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b hb => ?_))
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hs a ha), abs_of_nonneg (hs b hb)]
  have h1 := hG a ha
  have h2 := hE a ha b hb
  have h3 : 0 ≤ s a * s b := mul_nonneg (hs a ha) (hs b hb)
  have h4 : |G a| * |E b - E a| ≤ M * 1 :=
    mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  calc s a * s b * |G a| * |E b - E a| = (s a * s b) * (|G a| * |E b - E a|) := by ring
    _ ≤ (s a * s b) * (M * 1) := mul_le_mul_of_nonneg_left h4 h3
    _ = s a * s b * M := by ring

theorem lip_tilde (A : Finset α) (c : α → Fin k → ℝ) (γ : ℝ) (hA : A.Nonempty) (hγ : 0 < γ)
    (hc : ∀ a ∈ A, ∀ y, 1 / 4 ≤ c a y ∧ c a y ≤ 3 / 4)
    (r r' : Fin k → ℝ) (hr : r ∈ stdSimplex ℝ (Fin k)) (hr' : r' ∈ stdSimplex ℝ (Fin k))
    (y : Fin k) :
    |Ff A c γ r (unitVec y) - Ff A c γ r' (unitVec y)| ≤ l1dist r r' / (4 * γ) := by
  set v : Fin k → ℝ := r - r' with hv
  set V := l1dist r r' with hV
  set u : α → ℝ := fun a => dot r' (c a) with hu
  set G : α → ℝ := fun a => dot v (c a) with hG
  set s : α → ℝ → ℝ := fun a t => Real.exp (-(u a + t * G a) / γ) with hs
  set E : α → ℝ → ℝ := fun a t => c a y - (u a + t * G a) with hE
  set Zt : ℝ → ℝ := fun t => ∑ a ∈ A, s a t with hZt
  set ψ : ℝ → ℝ := fun t => -γ * Real.log (Zt t) + (∑ a ∈ A, s a t * E a t) / Zt t with hψdef
  have hdot : ∀ (t : ℝ) a, dot (r' + t • v) (c a) = u a + t * G a := by
    intro t a
    simp only [hu, hG, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hZ : ∀ t : ℝ, Zf A c γ (r' + t • v) = Zt t := by
    intro t
    simp only [Zf, hZt, hs, hdot]
  have hψ : ∀ t : ℝ, Ff A c γ (r' + t • v) (unitVec y) = ψ t := by
    intro t
    unfold Ff smf grdf
    rw [dot_sum_smul, hZ]
    simp only [hψdef]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [dot_sub', dot_comm' (c a) (unitVec y), dot_unitVec, dot_comm' (c a), hdot]
    simp only [wtf, hdot, hZ, hs, hE]
    ring
  have hZpos : ∀ t, 0 < Zt t := fun t => Finset.sum_pos (fun _ _ => Real.exp_pos _) hA
  -- derivatives
  have hsd : ∀ a (t : ℝ), HasDerivAt (s a) (s a t * (-(G a) / γ)) t := by
    intro a t
    have h1 : HasDerivAt (fun t : ℝ => -(u a + t * G a) / γ) (-(G a) / γ) t := by
      have := ((((hasDerivAt_id t).mul_const (G a)).const_add (u a)).neg).div_const γ
      simpa using this
    exact h1.exp
  have hEd : ∀ a (t : ℝ), HasDerivAt (E a) (-(G a)) t := by
    intro a t
    have := (((hasDerivAt_id t).mul_const (G a)).const_add (u a)).const_sub (c a y)
    simpa using this
  have hZd : ∀ t : ℝ, HasDerivAt Zt (∑ a ∈ A, s a t * (-(G a) / γ)) t :=
    fun t => HasDerivAt.fun_sum (fun a _ => hsd a t)
  have hNd : ∀ t : ℝ, HasDerivAt (fun t => ∑ a ∈ A, s a t * E a t)
      (∑ a ∈ A, (s a t * (-(G a) / γ) * E a t + s a t * (-(G a)))) t :=
    fun t => HasDerivAt.fun_sum (fun a _ => (hsd a t).mul (hEd a t))
  set D : ℝ → ℝ := fun t => -γ * ((∑ a ∈ A, s a t * (-(G a) / γ)) / Zt t) +
      ((∑ a ∈ A, (s a t * (-(G a) / γ) * E a t + s a t * (-(G a)))) * Zt t -
        (∑ a ∈ A, s a t * E a t) * (∑ a ∈ A, s a t * (-(G a) / γ))) / Zt t ^ 2 with hD
  have hψd : ∀ t : ℝ, HasDerivAt ψ (D t) t := by
    intro t
    exact (((hZd t).log (hZpos t).ne').const_mul (-γ)).add ((hNd t).fun_div (hZd t) (hZpos t).ne')
  -- bounds
  have hsum_v : ∑ z, v z = 0 := by
    simp [hv, Finset.sum_sub_distrib, hr.2, hr'.2]
  have hGb : ∀ a ∈ A, |G a| ≤ V / 4 := by
    intro a ha
    have e : G a = ∑ z, v z * (c a z - 1 / 2) := by
      have : ∑ z, v z * (c a z - 1 / 2) = ∑ z, v z * c a z - (1 / 2) * ∑ z, v z := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun z _ => by ring)
      rw [this, hsum_v]; simp [hG, dot]
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : V / 4 = ∑ z, |v z| * (1 / 4) := by
      rw [← Finset.sum_mul, hV, l1dist]; simp [hv]; ring
    rw [this]
    refine Finset.sum_le_sum (fun z _ => ?_)
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_le]
    constructor <;> linarith [(hc a ha z).1, (hc a ha z).2]
  have hEb : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ a ∈ A, ∀ b ∈ A, |E b t - E a t| ≤ 1 := by
    intro t ht a ha b hb
    have hrt0 : ∀ z, 0 ≤ (r' + t • v) z := by
      intro z
      have e : (r' + t • v) z = (1 - t) * r' z + t * r z := by
        simp [hv]; ring
      rw [e]
      have := hr.1 z; have := hr'.1 z
      nlinarith [ht.1, ht.2]
    have hrt1 : ∑ z, (r' + t • v) z = 1 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hsum_v, hr'.2]
      ring
    have e : E b t - E a t = (c b y - c a y) - ∑ z, (r' + t • v) z * (c b z - c a z) := by
      simp only [hE]
      rw [← hdot, ← hdot]
      simp only [dot, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e]
    have hX : |∑ z, (r' + t • v) z * (c b z - c a z)| ≤ 1 / 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : (1:ℝ) / 2 = ∑ z, (r' + t • v) z * (1 / 2) := by
        rw [← Finset.sum_mul, hrt1]; ring
      rw [this]
      refine Finset.sum_le_sum (fun z _ => ?_)
      rw [abs_mul, abs_of_nonneg (hrt0 z)]
      apply mul_le_mul_of_nonneg_left _ (hrt0 z)
      rw [abs_le]
      constructor <;> linarith [(hc a ha z).1, (hc a ha z).2, (hc b hb z).1, (hc b hb z).2]
    have hy : |c b y - c a y| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [(hc a ha y).1, (hc a ha y).2, (hc b hb y).1, (hc b hb y).2]
    calc |(c b y - c a y) - ∑ z, (r' + t • v) z * (c b z - c a z)|
        ≤ |c b y - c a y| + |∑ z, (r' + t • v) z * (c b z - c a z)| := abs_sub _ _
      _ ≤ 1 := by linarith
  have hDb : ∀ t ∈ Set.Icc (0:ℝ) 1, |D t| ≤ V / (4 * γ) := by
    intro t ht
    set S1 := ∑ a ∈ A, s a t * G a
    set S2 := ∑ a ∈ A, s a t * E a t
    set S3 := ∑ a ∈ A, s a t * G a * E a t
    have hZ0 := hZpos t
    have e1 : ∑ a ∈ A, s a t * (-(G a) / γ) = -(1 / γ) * S1 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    have e2 : ∑ a ∈ A, (s a t * (-(G a) / γ) * E a t + s a t * (-(G a))) =
        -(1 / γ) * S3 - S1 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    have eD : D t = (S1 * S2 - S3 * Zt t) / (γ * Zt t ^ 2) := by
      simp only [hD]
      rw [e1, e2]
      field_simp
      ring
    have hcov := cov_bound A (fun a => s a t) G (fun a => E a t) (V / 4)
      (fun a _ => (Real.exp_pos _).le) hGb (fun a ha b hb => hEb t ht a ha b hb)
    rw [eD, abs_div, abs_of_pos (by positivity : 0 < γ * Zt t ^ 2), div_le_div_iff₀ (by positivity)
      (by positivity)]
    have : |S1 * S2 - S3 * Zt t| ≤ V / 4 * Zt t ^ 2 := hcov
    nlinarith [sq_nonneg (Zt t)]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := ψ) (f' := D)
    (fun t _ => (hψd t).hasDerivWithinAt)
    (fun t ht => by rw [Real.norm_eq_abs]; exact hDb t (Set.Ico_subset_Icc_self ht))
  rw [Real.norm_eq_abs, ← hψ, ← hψ] at hmvt
  have e1 : r' + (1:ℝ) • v = r := by simp [hv]
  have e0 : r' + (0:ℝ) • v = r' := by simp
  rw [e1, e0] at hmvt
  exact hmvt

end MulticlassOmni.Dev.L44
end
end

section
namespace MulticlassOmni.Dev.L44
open MulticlassOmni.Lipschitz MulticlassOmni.Dev.F43

theorem card_avail_le {N : ℕ} (π : Fin N → Fin 2) : ((avail π).card : ℝ) ≤ (N : ℝ) + 1 := by
  have h : (avail π).card ≤ N + 1 := by
    unfold avail
    refine (Finset.card_insert_le _ _).trans ?_
    have := (Finset.card_image_le (s := Finset.univ.filter (fun i => π i = 1)) (f := some)).trans
      (Finset.card_filter_le _ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  exact_mod_cast h

theorem dot_mem_Icc {k : ℕ} (q w : Fin k → ℝ) (hq : q ∈ stdSimplex ℝ (Fin k)) (lo hi : ℝ)
    (hw : ∀ y, w y ∈ Set.Icc lo hi) : dot q w ∈ Set.Icc lo hi := by
  have e1 : ∑ y, q y * lo = lo := by rw [← Finset.sum_mul, hq.2, one_mul]
  have e2 : ∑ y, q y * hi = hi := by rw [← Finset.sum_mul, hq.2, one_mul]
  constructor
  · rw [← e1]; exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hw y).1 (hq.1 y))
  · rw [← e2]; exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hw y).2 (hq.1 y))

/-- margins at the benchmark point `f_β(x_i)` -/
theorem bench_margin {k N : ℕ} (hk : 0 < k) (x : Fin N → Fin k → ℝ) (η : ℝ) (hη0 : 0 < η)
    (hη : η ≤ 1 / 16384)
    (hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k))
    (h1 : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ)))
    (hsph : ∀ i, ∑ y, (x i y - vbar k y) ^ 2 = 1 / (256 * (k:ℝ)))
    (hsep : ∀ i j, i ≠ j → dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / (256 * (k:ℝ)))
    (i : Fin N) (β : ℕ) (π : Fin N → Fin 2) :
    ∃ a0 ∈ avail π, ∀ a ∈ avail π, a ≠ a0 →
      dot (bench x β i) (cost x η a0) + η ≤ dot (bench x β i) (cost x η a) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have cn : cost x η none = costA k := rfl
  have cs : ∀ j, cost x η (some j) = costB x η j := fun _ => rfl
  have hcA : ∀ a : Option (Fin N), a = none ∨ ∃ j, a = some j := by
    intro a; cases a with
    | none => left; rfl
    | some j => right; exact ⟨j, rfl⟩
  by_cases hb1 : β = 1
  · refine ⟨none, none_mem_avail π, ?_⟩
    intro a _ hne
    rcases hcA a with rfl | ⟨j, rfl⟩
    · exact absurd rfl hne
    · have hx1 : (k:ℝ) * x j ⟨0, hk⟩ ≤ 15 / 16 := by
        have := h1 j ⟨0, hk⟩ rfl
        rw [le_div_iff₀ (by positivity)] at this
        nlinarith
      have := delta_e1 hk x η j
      rw [dot_sub] at this
      simp only [bench, hb1, if_true, cn, cs]
      linarith
  · have hbx : bench x β i = x i := by simp [bench, hb1]
    rw [hbx]
    by_cases hpi : π i = 1
    · refine ⟨some i, (some_mem_avail π i).2 hpi, ?_⟩
      intro a _ hne
      have hself := delta_self hk x η hs hsph i
      rw [dot_sub] at hself
      rcases hcA a with rfl | ⟨j, rfl⟩
      · rw [cn, cs]; linarith
      · have hji : j ≠ i := fun e => hne (by rw [e])
        have := delta_other hk x η hs hsep i j (Ne.symm hji)
        rw [dot_sub] at this
        rw [cs, cs]; linarith
    · refine ⟨none, none_mem_avail π, ?_⟩
      intro a ha hne
      rcases hcA a with rfl | ⟨j, rfl⟩
      · exact absurd rfl hne
      · have hj := (some_mem_avail π j).1 ha
        have hji : j ≠ i := by rintro rfl; exact hpi hj
        have := delta_other hk x η hs hsep i j (Ne.symm hji)
        rw [dot_sub] at this
        rw [cn, cs]; linarith


/-- (29), (40) and `γ log(N+1) = η/8`, from the size bounds on `N`. -/
theorem param_facts (C₁ : ℝ) (hC₁ : 2 ≤ C₁) (k N : ℕ) (hkR : (3:ℝ) ≤ k) (ε η : ℝ) (hε : 0 < ε)
    (hε4 : ε ≤ 1 / 4) (hη0 : 0 < η) (hη2 : η ^ 2 = 64 * ((k:ℝ) * ε * (-Real.log ε)))
    (hηC : η ≤ 1 / (512 * C₁ ^ 9))
    (hNlo : C₁ ^ (-(k : ℝ)) * η ^ (-((k : ℝ) - 2) / 2) ≤ (N : ℝ))
    (hNhi : (N : ℝ) ≤ η ^ (-((k : ℝ) - 2) / 2)) (hN128R : (128:ℝ) ≤ N) :
    0 < gam N η ∧ gam N η * Real.log ((N:ℝ) + 1) = η / 8 ∧ 32 * ε ≤ η * gam N η ∧
      gam N η ≤ η / 8 ∧ ((N:ℝ) + 1) * Real.exp (-η / gam N η) ≤ η / 512 := by
  have hlog4 : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
    rw [one_div, Real.log_inv, show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  have hlogε : Real.log ε ≤ -2 * Real.log 2 := by
    rw [← hlog4]; exact Real.log_le_log hε hε4
  have hεη : ε ≤ η ^ 2 := by
    rw [hη2]
    have h1 : 1 ≤ -Real.log ε := by linarith
    have h2 : 3 * ε ≤ (k:ℝ) * ε := by nlinarith
    have h3 : (k:ℝ) * ε * 1 ≤ (k:ℝ) * ε * (-Real.log ε) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hlogη : Real.log ε ≤ 2 * Real.log η := by
    have := Real.log_le_log hε hεη
    rwa [Real.log_pow] at this
  have hlC : 0 < Real.log C₁ := Real.log_pos (by linarith)
  have hl512 : 0 < Real.log 512 := Real.log_pos (by norm_num)
  have hlogηC : Real.log η ≤ -(Real.log 512 + 9 * Real.log C₁) := by
    have := Real.log_le_log hη0 hηC
    rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  have hNpos : (0:ℝ) < N := by linarith
  have hlogNlo : -(k:ℝ) * Real.log C₁ + (-((k:ℝ) - 2) / 2) * Real.log η ≤ Real.log N := by
    have hp1 : 0 < C₁ ^ (-(k : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have hp2 : 0 < η ^ (-((k : ℝ) - 2) / 2) := Real.rpow_pos_of_pos hη0 _
    have := Real.log_le_log (mul_pos hp1 hp2) hNlo
    rwa [Real.log_mul hp1.ne' hp2.ne', Real.log_rpow (by linarith), Real.log_rpow hη0] at this
  have hlogNhi : Real.log N ≤ (-((k:ℝ) - 2) / 2) * Real.log η := by
    have := Real.log_le_log hNpos hNhi
    rwa [Real.log_rpow hη0] at this
  set ℓ := Real.log ((N:ℝ) + 1) with hℓ
  have hℓN : Real.log N ≤ ℓ := Real.log_le_log hNpos (by linarith)
  have hℓ2 : ℓ ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) hNpos.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hc4 : 4 * ℓ ≤ (k:ℝ) * (-Real.log ε) := by
    have h0 : 0 ≤ ((k:ℝ) - 2) * (2 * Real.log η - Real.log ε) :=
      mul_nonneg (by linarith) (by linarith)
    have h1 : 4 * Real.log N ≤ -2 * ((k:ℝ) - 2) * Real.log η := by linarith
    linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hgam : gam N η = η / (8 * ℓ) := by rw [gam]
  set γ := gam N η with hγdef
  have hγ0 : 0 < γ := by rw [hgam]; positivity
  have hγℓ : γ * ℓ = η / 8 := by rw [hgam]; field_simp
  have hηγℓ : η / γ = 8 * ℓ := by rw [hgam]; field_simp
  refine ⟨hγ0, hγℓ, ?_, ?_, ?_⟩
  · have e : η * γ * (8 * ℓ) = η ^ 2 := by rw [hgam]; field_simp
    rw [hη2] at e
    have h1 : 64 * ε * (4 * ℓ) ≤ 64 * ε * ((k:ℝ) * (-Real.log ε)) :=
      mul_le_mul_of_nonneg_left hc4 (by positivity)
    have h2 : 32 * ε * (8 * ℓ) ≤ η * γ * (8 * ℓ) := by linarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  · have : γ * 1 ≤ γ * ℓ := mul_le_mul_of_nonneg_left hℓ1 hγ0.le
    linarith
  · have h7 : Real.log 512 - Real.log η ≤ 7 * ℓ := by
      set l := Real.log C₁
      set P := Real.log 512
      set Le := Real.log η
      have hK : 0 ≤ 7 * (k:ℝ) / 2 - 8 := by linarith
      have hm : (7 * (k:ℝ) / 2 - 8) * (P + 9 * l) ≤ (7 * (k:ℝ) / 2 - 8) * (-Le) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
      have hm2 : 0 ≤ ((k:ℝ) - 3) * P := mul_nonneg (by linarith) hl512.le
      have hm3 : 0 ≤ ((k:ℝ) - 3) * l := mul_nonneg (by linarith) hlC.le
      have hNl : 7 * (-(k:ℝ) * l + (-((k:ℝ) - 2) / 2) * Le) ≤ 7 * ℓ := by linarith
      linarith
    have e1 : Real.exp (-η / γ) = Real.exp (-(8 * ℓ)) := by rw [neg_div, hηγℓ]
    rw [e1]
    calc ((N:ℝ) + 1) * Real.exp (-(8 * ℓ)) = Real.exp ℓ * Real.exp (-(8 * ℓ)) := by
          rw [hℓ, Real.exp_log (by positivity)]
      _ = Real.exp (-(7 * ℓ)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (Real.log (η / 512)) := by
          apply Real.exp_le_exp.2
          rw [Real.log_div hη0.ne' (by norm_num)]
          linarith
      _ = η / 512 := Real.exp_log (by positivity)


theorem smoothLoss_eq {k N : ℕ} (x : Fin N → Fin k → ℝ) (η ε : ℝ) (π : Fin N → Fin 2)
    (r : Fin k → ℝ) (y : Fin k) : smoothLoss x η ε π r y =
      64 * ε / η * (Ff (avail π) (cost x η) (gam N η) r (unitVec y) - 1 / 4 + η / 8) := rfl

theorem sum_smoothLoss {k N : ℕ} (x : Fin N → Fin k → ℝ) (η ε : ℝ) (π : Fin N → Fin 2)
    (q r : Fin k → ℝ) (hq : ∑ y, q y = 1) :
    ∑ y, q y * smoothLoss x η ε π r y =
      64 * ε / η * (Ff (avail π) (cost x η) (gam N η) r q - 1 / 4 + η / 8) := by
  simp only [smoothLoss_eq]
  set K := 64 * ε / η
  have e : ∀ y, q y * (K * (Ff (avail π) (cost x η) (gam N η) r (unitVec y) - 1 / 4 + η / 8)) =
      K * (q y * Ff (avail π) (cost x η) (gam N η) r (unitVec y)) + K * (-1 / 4 + η / 8) * q y := by
    intro y; ring
  rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, expect_Ff _ _ _ r q hq, hq]
  ring

theorem lip_part {k N : ℕ} (x : Fin N → Fin k → ℝ) (η ε : ℝ) (hη0 : 0 < η) (hε : 0 < ε)
    (hη1 : η ≤ 1) (hγ0 : 0 < gam N η) (hηγ : 32 * ε ≤ η * gam N η) (hγle : gam N η ≤ η / 8)
    (hcost : ∀ a y, cost x η a y ∈ Set.Icc (1 / 4 : ℝ) (3 / 4))
    (π : Fin N → Fin 2) (hcl : gam N η * Real.log ((avail π).card : ℝ) ≤ η / 8) :
    IsLipProper (smoothLoss x η ε π) := by
  set γ := gam N η with hγdef
  set A := avail π with hAdef
  have hA : A.Nonempty := ⟨none, none_mem_avail π⟩
  set K := 64 * ε / η with hK
  have hK0 : 0 < K := by positivity
  have hK2γ : K ≤ 2 * γ := by
    rw [hK, div_le_iff₀ hη0]; linarith
  have hcostI : ∀ a y, 1 / 4 ≤ cost x η a y ∧ cost x η a y ≤ 3 / 4 :=
    fun a y => ⟨(hcost a y).1, (hcost a y).2⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · apply MulticlassOmni.Dev.Basic.isProper_of
    intro q hq r _
    rw [sum_smoothLoss x η ε π q q hq.2, sum_smoothLoss x η ε π q r hq.2, Ff_self]
    have := tangent A (cost x η) γ hA hγ0 r q
    exact mul_le_mul_of_nonneg_left (by linarith) hK0.le
  · intro r _ y
    have hup := Ff_unit_le A (cost x η) γ hA hγ0 y (fun a _ => (hcostI a y).2) r
    have hlo := Ff_unit_ge A (cost x η) γ hA hγ0 y (fun a _ => (hcostI a y).1) r
    rw [smoothLoss_eq]
    constructor
    · apply mul_nonneg hK0.le; linarith
    · have h1 : K * (Ff A (cost x η) γ r (unitVec y) - 1 / 4 + η / 8) ≤
          K * (1 / 2 + η / 8) := mul_le_mul_of_nonneg_left (by linarith) hK0.le
      have h2 : K * (1 / 2 + η / 8) ≤ 2 * γ * (1 / 2 + η / 8) :=
        mul_le_mul_of_nonneg_right hK2γ (by positivity)
      have h3 : 2 * γ * (1 / 2 + η / 8) ≤ 2 * (1 / 8) * (1 / 2 + 1 / 8) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
      linarith
  · intro r hr r' hr' y
    have hl := lip_tilde A (cost x η) γ hA hγ0 (fun a _ y => hcostI a y) r r' hr hr' y
    rw [smoothLoss_eq, smoothLoss_eq, ← mul_sub, abs_mul, abs_of_pos hK0]
    have e : Ff A (cost x η) γ r (unitVec y) - 1 / 4 + η / 8 -
        (Ff A (cost x η) γ r' (unitVec y) - 1 / 4 + η / 8) =
        Ff A (cost x η) γ r (unitVec y) - Ff A (cost x η) γ r' (unitVec y) := by
      ring
    rw [e]
    have hV : 0 ≤ l1dist r r' := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have h1 := mul_le_mul_of_nonneg_left hl hK0.le
    have h2 : K * (l1dist r r' / (4 * γ)) ≤ l1dist r r' := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have : K ≤ 4 * γ := by linarith
      have := mul_le_mul_of_nonneg_right this hV
      linarith
    linarith

theorem regret_part {k N : ℕ} (x : Fin N → Fin k → ℝ) (η ε : ℝ) (hη0 : 0 < η) (hε : 0 < ε)
    (hη1 : η ≤ 1)
    (hγ0 : 0 < gam N η) (hγle : gam N η ≤ η / 8)
    (hcost : ∀ a y, cost x η a y ∈ Set.Icc (1 / 4 : ℝ) (3 / 4))
    (π : Fin N → Fin 2) (hcl : gam N η * Real.log ((avail π).card : ℝ) ≤ η / 8)
    (hθ : ((avail π).card : ℝ) * Real.exp (-η / gam N η) ≤ η / 512)
    (σ : Equiv.Perm (Fin N)) (s q : Fin k → ℝ) (hq : q ∈ stdSimplex ℝ (Fin k))
    (astar : Option (Fin N)) (hastar : aSel x η π σ s = astar) (hmemA : astar ∈ avail π)
    (hgap : ∀ a ∈ avail π, a ≠ astar → dot q (cost x η astar) + η ≤ dot q (cost x η a))
    (hmar : ∀ a ∈ avail π, a ≠ astar → dot s (cost x η astar) + η ≤ dot s (cost x η a))
    (r : Fin k → ℝ) :
    24 * ε * (if aSel x η π σ r ≠ aSel x η π σ s then 1 else 0) - ε / 8 ≤
      expect q (fun y => smoothLoss x η ε π r y - smoothLoss x η ε π s y) := by
  set γ := gam N η with hγdef
  set A := avail π with hAdef
  have hA : A.Nonempty := ⟨none, none_mem_avail π⟩
  set K := 64 * ε / η with hK
  have hK0 : 0 < K := by positivity
  have hKη : K * η = 64 * ε := by rw [hK]; field_simp
  have hv2 : ∀ a ∈ A, dot q (cost x η a) - dot q (cost x η astar) ≤ 1 / 2 := by
    intro a _
    have h1 := dot_mem_Icc q (cost x η a) hq _ _ (hcost a)
    have h2 := dot_mem_Icc q (cost x η astar) hq _ _ (hcost astar)
    linarith [h1.2, h2.1]
  have hup := regret_upper A (cost x η) γ hγ0 η hη0.le s q hmemA hmar hgap hv2
  have hD0 : Ff A (cost x η) γ s q - smf A (cost x η) γ q ≤ η / 512 := by
    have : (1 / 2 + γ) * ((A.card : ℝ) * Real.exp (-η / γ)) ≤ 1 * (η / 512) :=
      mul_le_mul (by linarith) hθ (by positivity) (by norm_num)
    linarith
  have hE : expect q (fun y => smoothLoss x η ε π r y - smoothLoss x η ε π s y) =
      K * (Ff A (cost x η) γ r q - Ff A (cost x η) γ s q) := by
    unfold expect
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [sum_smoothLoss x η ε π q r hq.2, sum_smoothLoss x η ε π q s hq.2]
    ring
  rw [hE, hastar]
  by_cases hsel : aSel x η π σ r = astar
  · simp only [hsel, ne_eq, not_true_eq_false, if_false, mul_zero, zero_sub]
    have ht := tangent A (cost x η) γ hA hγ0 r q
    have h1 : K * (-(η / 512)) ≤ K * (Ff A (cost x η) γ r q - Ff A (cost x η) γ s q) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0.le
    have h2 : K * (-(η / 512)) = -(ε / 8) := by
      have : K * (-(η / 512)) = -(K * η) / 512 := by ring
      rw [this, hKη]; ring
    linarith
  · simp only [hsel, ne_eq, not_false_eq_true, if_true, mul_one]
    have hlow := regret_lower A (cost x η) γ hγ0 η hη0.le r q hmemA (aSel_mem x η π σ r) hsel
      hgap (aSel_min x η π σ r astar hmemA)
    have h1 : K * (3 * η / 8 - η / 512) ≤ K * (Ff A (cost x η) γ r q - Ff A (cost x η) γ s q) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0.le
    have h2 : K * (3 * η / 8 - η / 512) = 24 * ε - ε / 8 := by
      have : K * (3 * η / 8 - η / 512) = (K * η) * (3 / 8 - 1 / 512) := by ring
      rw [this, hKη]; ring
    linarith

end MulticlassOmni.Dev.L44

namespace MulticlassOmni.Lipschitz
open MulticlassOmni.Dev.F43 MulticlassOmni.Dev.L44 MulticlassOmni.Dev.Basic

theorem chk_lemma_4_4 :
    ∀ Cpack : ℝ, 0 < Cpack → ∃ c : ℝ, 0 < c ∧
      ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ε < c / ((k : ℝ) * Real.log ((k : ℝ) + 1)) →
        ∀ (N : ℕ) (x : Fin N → Fin k → ℝ), IsSection41Packing Cpack k (eta k ε) x →
          (∀ π : Fin N → Fin 2, IsLipProper (smoothLoss x (eta k ε) ε π)) ∧
          ∀ (σ : Equiv.Perm (Fin N)) (i : Fin N) (b : Fin 2) (β : ℕ) (π : Fin N → Fin 2),
            (β = 1 ∨ β = 2) → (π i = 1 → (b : ℕ) = β - 1) →
              ∀ r ∈ stdSimplex ℝ (Fin k),
                24 * ε * (if aSel x (eta k ε) π σ r ≠ aSel x (eta k ε) π σ (bench x β i)
                    then 1 else 0) - ε / 8 ≤
                  expect (qLip x (eta k ε) b i)
                    (fun y => smoothLoss x (eta k ε) ε π r y -
                      smoothLoss x (eta k ε) ε π (bench x β i) y) := by
  intro Cpack hC
  obtain ⟨C₁, η₀, hC₁, hη₀, hB3⟩ := lemma_B_3 Cpack hC
  set δ := min (min η₀ (1 / 16384)) (1 / (512 * C₁ ^ 9)) with hδ
  have hC9 : 0 < 512 * C₁ ^ 9 := by positivity
  have hδ0 : 0 < δ := lt_min (lt_min hη₀ (by norm_num)) (by positivity)
  have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (by norm_num))
  refine ⟨(δ ^ 2 / 192) ^ 2, by positivity, ?_⟩
  intro k hk ε hε hlt N x hx
  obtain ⟨hη0, hηδ⟩ := eta_small δ hδ0 hδ1 k hk ε hε hlt
  set η := eta k ε with hηdef
  have hηA : η ≤ η₀ := le_trans hηδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hηB : η ≤ 1 / 16384 := le_trans hηδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hηC : η ≤ 1 / (512 * C₁ ^ 9) := le_trans hηδ (min_le_right _ _)
  have hk0 : 0 < k := by omega
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨⟨hNlo, hNhi, hN128⟩, hcost, hqmem⟩ := hB3 k hk η hη0 hηA N x hx
  -- facts about ε
  have hL4 : 1 < Real.log ((k : ℝ) + 1) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hε4 : ε ≤ 1 / 4 := by
    have hc1 : (δ ^ 2 / 192) ^ 2 ≤ 1 / 4 := by
      have h1 : δ ^ 2 ≤ 1 := by nlinarith
      have h2 : δ ^ 2 / 192 ≤ 1 := by linarith
      have h3 : 0 ≤ δ ^ 2 / 192 := by positivity
      nlinarith
    have h := hlt
    rw [lt_div_iff₀ (by positivity)] at h
    have hkl : (3:ℝ) ≤ (k:ℝ) * Real.log ((k:ℝ) + 1) := by nlinarith
    have : ε * 3 ≤ ε * ((k:ℝ) * Real.log ((k:ℝ) + 1)) := mul_le_mul_of_nonneg_left hkl hε.le
    linarith
  have hlog1ε : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
  have hlogε0 : 0 ≤ -Real.log ε := by
    have := Real.log_nonpos hε.le (by linarith); linarith
  have hη2 : η ^ 2 = 64 * ((k:ℝ) * ε * (-Real.log ε)) := by
    have hX : 0 ≤ (k:ℝ) * ε * Real.log (1 / ε) := by
      rw [hlog1ε]
      exact mul_nonneg (by positivity) hlogε0
    rw [hηdef, eta, mul_pow, Real.sq_sqrt hX, hlog1ε]
    norm_num
  have hN128R : (128:ℝ) ≤ N := by exact_mod_cast hN128
  obtain ⟨hγ0, hγℓ, hηγ, hγle, hθN⟩ :=
    param_facts C₁ hC₁ k N hkR ε η hε hε4 hη0 hη2 hηC hNlo hNhi hN128R
  set ℓ := Real.log ((N:ℝ) + 1) with hℓ
  set γ := gam N η with hγdef
  have hθ : ∀ π : Fin N → Fin 2, ((avail π).card : ℝ) * Real.exp (-η / γ) ≤ η / 512 :=
    fun π => le_trans (mul_le_mul_of_nonneg_right (card_avail_le π) (Real.exp_pos _).le) hθN
  have hcardlog : ∀ π : Fin N → Fin 2, γ * Real.log ((avail π).card : ℝ) ≤ η / 8 := by
    intro π
    have hpos : (0:ℝ) < (avail π).card := by
      exact_mod_cast Finset.card_pos.2 ⟨none, none_mem_avail π⟩
    have := Real.log_le_log hpos (card_avail_le π)
    rw [← hγℓ]
    exact mul_le_mul_of_nonneg_left this hγ0.le
  refine ⟨fun π => lip_part x η ε hη0 hε (hηB.trans (by norm_num)) hγ0 hηγ hγle hcost π
    (hcardlog π), ?_⟩
  intro σ i b β π hβ hπb r _
  obtain ⟨X₀, hX, hinj, hmem, _⟩ := hx
  obtain ⟨_, hsimp, _, hfirst, hsph, hsep⟩ := hX
  have hs : ∀ i, x i ∈ stdSimplex ℝ (Fin k) := fun i => hsimp _ (hmem i)
  have h1 : ∀ i, ∀ y : Fin k, (y : ℕ) = 0 → x i y ≤ 15 / (16 * (k : ℝ)) :=
    fun i y hy => hfirst _ (hmem i) y hy
  have hsph' : ∀ i, ∑ y, (x i y - vbar k y) ^ 2 = 1 / (256 * (k:ℝ)) :=
    fun i => hsph _ (hmem i)
  have hsep' : ∀ i j, i ≠ j →
      dot (x i - vbar k) (x j - vbar k) ≤ (1 - 1024 * η) / (256 * (k:ℝ)) := by
    intro i j hij
    have := hsep _ (hmem i) _ (hmem j) (fun e => hij (hinj e))
    have e : 8000 * (16 * η / 125) = 1024 * η := by ring
    rwa [e] at this
  obtain ⟨astar, hastar, hmemA, hgap⟩ :=
    core hk0 x η hη0 hηB hs h1 hsph' hsep' σ i b β π hβ hπb
  obtain ⟨a0, ha0, hmar⟩ := bench_margin hk0 x η hη0 hηB hs h1 hsph' hsep' i β π
  have ha0e : astar = a0 := by
    by_contra hne
    have h := aSel_min x η π σ (bench x β i) a0 ha0
    rw [hastar] at h
    have := hmar astar hmemA hne
    linarith
  subst ha0e
  exact regret_part x η ε hη0 hε (hηB.trans (by norm_num)) hγ0 hγle hcost π (hcardlog π) (hθ π) σ (bench x β i)
    (qLip x η b i) (hqmem i b) astar hastar hmemA hgap hmar r

end MulticlassOmni.Lipschitz
end

theorem solution : type_of% @MulticlassOmni.Lipschitz.chk_lemma_4_4 := @MulticlassOmni.Lipschitz.chk_lemma_4_4
