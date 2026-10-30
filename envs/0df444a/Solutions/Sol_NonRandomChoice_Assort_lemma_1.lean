-- Prove2me | solution 1 for NonRandomChoice.Assort.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:07:22.56526+00:00
-- url     : https://prove2.me/submissions/fb3dc9fa-c312-4d95-a7a0-b299f1c7f64f

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_NonRandomChoice_Assort_Model

namespace NRCLemma1
open RevenueOrdered.Ratio NonRandomChoice.Assort

lemma rev_split {N : ℕ} (P : Fin N → Finset (Fin N) → ℝ) (p : Fin N → ℝ) (c : ℝ)
    (S : Finset (Fin N)) :
    revenue P p S = c * (1 - noPurchase P S) + ∑ x ∈ S, P x S * (p x - c) := by
  unfold revenue noPurchase
  rw [sub_sub_cancel, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => by ring)

lemma key {N : ℕ} (P : Fin N → Finset (Fin N) → ℝ)
    (hP : RevenueOrdered.Ratio.IsRegular P) (p : Fin N → ℝ) (hp : Antitone p)
    (f : Fin N → ℝ → ℝ) (D : Fin N → Set ℝ)
    (hconv : ∀ i, ConvexOn ℝ (D i) (f i))
    (hrep : ∀ (S : Finset (Fin N)) (i : Fin N), i ∈ S →
      noPurchase P S ∈ D i ∧ P i S = f i (noPurchase P S))
    (S U : Finset (Fin N)) (k : Fin N) (hkS : k ∈ S) (hSU : S ⊆ U)
    (hU : ∀ i ∈ U, i ≤ k) (M : ℝ)
    (h1 : revenue P p U ≤ M) (h2 : revenue P p (S.erase k) ≤ M) :
    revenue P p S ≤ M := by
  set E := S.erase k with hE
  have hES : E ⊆ S := Finset.erase_subset k S
  have hEU : E ⊆ U := hES.trans hSU
  set t := noPurchase P S
  set s := noPurchase P E
  set u := noPurchase P U
  have hut : u ≤ t := hP.noPurchase_mono S U hSU
  have hts : t ≤ s := hP.noPurchase_mono E S hES
  have hw : ∀ x ∈ U, 0 ≤ p x - p k := fun x hx => sub_nonneg.2 (hp (hU x hx))
  -- (a) lower bound on revenue U
  have ha : p k * (1 - u) + ∑ x ∈ E, f x u * (p x - p k) ≤ revenue P p U := by
    rw [rev_split P p (p k) U]
    gcongr
    calc ∑ x ∈ E, f x u * (p x - p k) = ∑ x ∈ E, P x U * (p x - p k) :=
          Finset.sum_congr rfl (fun x hx => by rw [(hrep U x (hEU hx)).2])
      _ ≤ ∑ x ∈ U, P x U * (p x - p k) :=
          Finset.sum_le_sum_of_subset_of_nonneg hEU
            (fun x hx _ => mul_nonneg (hP.nonneg x U) (hw x hx))
  -- (b) revenue S
  have hb : revenue P p S = p k * (1 - t) + ∑ x ∈ E, f x t * (p x - p k) := by
    rw [rev_split P p (p k) S]
    congr 1
    rw [hE, ← Finset.sum_erase S (a := k) (by simp : P k S * (p k - p k) = 0)]
    exact Finset.sum_congr rfl (fun x hx => by rw [(hrep S x (Finset.mem_of_mem_erase hx)).2])
  -- (c) revenue E
  have hc : revenue P p E = p k * (1 - s) + ∑ x ∈ E, f x s * (p x - p k) := by
    rw [rev_split P p (p k) E]
    congr 1
    exact Finset.sum_congr rfl (fun x hx => by rw [(hrep E x hx).2])
  -- t is a convex combination of u and s
  have htmem : t ∈ segment ℝ u s := by
    rw [segment_eq_Icc (hut.trans hts)]; exact ⟨hut, hts⟩
  obtain ⟨a, b, ha0, hb0, hab, htab⟩ := htmem
  simp only [smul_eq_mul] at htab
  have hsum : ∑ x ∈ E, f x t * (p x - p k) ≤
      a * ∑ x ∈ E, f x u * (p x - p k) + b * ∑ x ∈ E, f x s * (p x - p k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x hx
    have hcv := (hconv x).2 (hrep U x (hEU hx)).1 (hrep E x hx).1 ha0 hb0 hab
    simp only [smul_eq_mul] at hcv
    rw [htab] at hcv
    have := mul_le_mul_of_nonneg_right hcv (hw x (hEU hx))
    linarith
  have haM : a * (p k * (1 - u) + ∑ x ∈ E, f x u * (p x - p k)) ≤ a * M :=
    mul_le_mul_of_nonneg_left (ha.trans h1) ha0
  have hbM : b * (p k * (1 - s) + ∑ x ∈ E, f x s * (p x - p k)) ≤ b * M :=
    mul_le_mul_of_nonneg_left (hc ▸ h2) hb0
  have hpk : p k * (1 - t) = a * (p k * (1 - u)) + b * (p k * (1 - s)) := by
    rw [← htab]; have : b = 1 - a := by linarith
    subst this; ring
  rw [hb]
  have hM : a * M + b * M = M := by rw [← add_mul, hab, one_mul]
  nlinarith

lemma roSet_zero (N : ℕ) : roSet N 0 = ∅ := by
  ext i; simp [roSet]

theorem lemma_1' {N : ℕ} (P : Fin N → Finset (Fin N) → ℝ)
    (hP : RevenueOrdered.Ratio.IsRegular P) (p : Fin N → ℝ) (hp : Antitone p)
    (f : Fin N → ℝ → ℝ) (D : Fin N → Set ℝ)
    (hconv : ∀ i, ConvexOn ℝ (D i) (f i))
    (hrep : ∀ (S : Finset (Fin N)) (i : Fin N), i ∈ S →
      RevenueOrdered.Ratio.noPurchase P S ∈ D i ∧
        P i S = f i (RevenueOrdered.Ratio.noPurchase P S)) :
    ∃ n : ℕ, n ≤ N ∧ ∀ S : Finset (Fin N),
      RevenueOrdered.Ratio.revenue P p S ≤ RevenueOrdered.Ratio.revenue P p (roSet N n) := by
  obtain ⟨n0, hn0, hmax⟩ := Finset.exists_max_image (Finset.range (N + 1))
    (fun n => revenue P p (roSet N n)) ⟨0, by simp⟩
  refine ⟨n0, Nat.lt_succ_iff.1 (Finset.mem_range.1 hn0), ?_⟩
  set M := revenue P p (roSet N n0)
  have hempty : revenue P p ∅ ≤ M := by
    have := hmax 0 (by simp); rwa [roSet_zero] at this
  suffices h : ∀ m : ℕ, ∀ S : Finset (Fin N), S.card ≤ m → revenue P p S ≤ M from
    fun S => h S.card S le_rfl
  intro m
  induction m with
  | zero => intro S hS; rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hS)]; exact hempty
  | succ m ih =>
    intro S hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact hempty
    set k := S.max' hne
    have hkS : k ∈ S := S.max'_mem hne
    have hU : ∀ i ∈ roSet N (k.val + 1), i ≤ k := by
      intro i hi; simp [roSet] at hi; exact Fin.le_iff_val_le_val.2 (by omega)
    have hSU : S ⊆ roSet N (k.val + 1) := by
      intro i hi
      have := S.le_max' i hi
      simp only [roSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.lt_succ_iff.2 (Fin.le_iff_val_le_val.1 this)
    apply key P hP p hp f D hconv hrep S _ k hkS hSU hU M
    · exact hmax _ (Finset.mem_range.2 (by omega))
    · apply ih
      rw [Finset.card_erase_of_mem hkS]; omega

end NRCLemma1

theorem solution {N : ℕ} (P : Fin N → Finset (Fin N) → ℝ)
    (hP : RevenueOrdered.Ratio.IsRegular P) (p : Fin N → ℝ) (hp : Antitone p)
    (f : Fin N → ℝ → ℝ) (D : Fin N → Set ℝ)
    (hconv : ∀ i, ConvexOn ℝ (D i) (f i))
    (_hnonneg : ∀ i, ∀ x ∈ D i, 0 ≤ f i x)
    (hrep : ∀ (S : Finset (Fin N)) (i : Fin N), i ∈ S →
      RevenueOrdered.Ratio.noPurchase P S ∈ D i ∧
        P i S = f i (RevenueOrdered.Ratio.noPurchase P S)) :
    ∃ n : ℕ, n ≤ N ∧ ∀ S : Finset (Fin N),
      RevenueOrdered.Ratio.revenue P p S ≤
        RevenueOrdered.Ratio.revenue P p (NonRandomChoice.Assort.roSet N n) :=
  NRCLemma1.lemma_1' P hP p hp f D hconv hrep
