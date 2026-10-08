-- Prove2me | solution 1 for GilmoreGomory61.CuttingStock.knapsack_maximum_test
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:36:55.377165+00:00
-- url     : https://prove2.me/submissions/41adfd7d-4829-476c-b0b5-96973c1ed60d

import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Knapsack

open Classical

namespace GilmoreGomory61.CuttingStock

section KN
variable {m k : ℕ} (I : Instance m k)

def KFeas (s : ℕ) (y : ℝ) (a : Fin m → ℕ) : Prop :=
  (∀ i : Fin m, s ≤ i.val → a i = 0) ∧ patLen I a ≤ y

lemma gk_term_nonneg (s : ℕ) (hpos : ∀ i : Fin m, i.val < s → 0 < I.ℓ i)
    (a : Fin m → ℕ) (h0 : ∀ i : Fin m, s ≤ i.val → a i = 0) (i : Fin m) :
    0 ≤ I.ℓ i * (a i : ℝ) := by
  by_cases h : i.val < s
  · exact mul_nonneg (hpos i h).le (Nat.cast_nonneg _)
  · rw [h0 i (not_lt.1 h)]; simp

lemma gk_attain (b : Fin m → ℝ) (s : ℕ) (hpos : ∀ i : Fin m, i.val < s → 0 < I.ℓ i) (y : ℝ)
    (h : ∃ a, KFeas I s y a) :
    ∃ aS, KFeas I s y aS ∧ ∀ a, KFeas I s y a → (∑ i, b i * (a i : ℝ)) ≤ ∑ i, b i * (aS i : ℝ) := by
  have hmem : ∀ a, KFeas I s y a →
      a ∈ Fintype.piFinset (fun i : Fin m => Finset.range (if i.val < s then ⌊y / I.ℓ i⌋₊ + 1 else 1)) := by
    intro a ha
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    split_ifs with hi
    · have h1 : I.ℓ i * (a i : ℝ) ≤ patLen I a :=
        Finset.single_le_sum (f := fun i => I.ℓ i * (a i : ℝ))
          (fun i _ => gk_term_nonneg I s hpos a ha.1 i) (Finset.mem_univ i)
      have h2 : (a i : ℝ) ≤ y / I.ℓ i := by
        rw [le_div_iff₀ (hpos i hi)]; nlinarith [ha.2]
      have := Nat.le_floor h2
      omega
    · rw [ha.1 i (not_lt.1 hi)]; omega
  obtain ⟨a0, ha0⟩ := h
  obtain ⟨aS, haS, hmax⟩ := Finset.exists_max_image
    ((Fintype.piFinset (fun i : Fin m => Finset.range (if i.val < s then ⌊y / I.ℓ i⌋₊ + 1 else 1))).filter
      (KFeas I s y)) (fun a => ∑ i, b i * (a i : ℝ))
    ⟨a0, Finset.mem_filter.2 ⟨hmem a0 ha0, ha0⟩⟩
  exact ⟨aS, (Finset.mem_filter.1 haS).2, fun a ha =>
    hmax a (Finset.mem_filter.2 ⟨hmem a ha, ha⟩)⟩

lemma gk_eq (b : Fin m → ℝ) (s : ℕ) (y : ℝ) (aS : Fin m → ℕ) (h : KFeas I s y aS)
    (hmax : ∀ a, KFeas I s y a → (∑ i, b i * (a i : ℝ)) ≤ ∑ i, b i * (aS i : ℝ)) :
    knapF I b s y = ((∑ i, b i * (aS i : ℝ) : ℝ) : EReal) := by
  unfold knapF
  apply le_antisymm
  · refine iSup_le fun a => iSup_le fun ha => ?_
    exact EReal.coe_le_coe_iff.2 (hmax a ha)
  · exact le_iSup_of_le aS (le_iSup_of_le h le_rfl)

lemma gk_bot (b : Fin m → ℝ) (s : ℕ) (y : ℝ) (h : ¬ ∃ a, KFeas I s y a) :
    knapF I b s y = ⊥ := by
  unfold knapF
  exact iSup_eq_bot.2 fun a => iSup_eq_bot.2 fun ha => absurd ⟨a, ha⟩ h

lemma gk_le (b : Fin m → ℝ) (s : ℕ) (y : ℝ) (a : Fin m → ℕ) (h : KFeas I s y a) :
    ((∑ i, b i * (a i : ℝ) : ℝ) : EReal) ≤ knapF I b s y :=
  le_iSup_of_le a (le_iSup_of_le h le_rfl)

lemma gk_le_of (b : Fin m → ℝ) (s : ℕ) (y : ℝ) (T : EReal)
    (h : ∀ a, KFeas I s y a → ((∑ i, b i * (a i : ℝ) : ℝ) : EReal) ≤ T) :
    knapF I b s y ≤ T :=
  iSup_le fun a => iSup_le fun ha => h a ha

lemma gk_split (g : Fin m → ℝ) (a : Fin m → ℕ) (p : Fin m) :
    ∑ i, g i * (a i : ℝ) = g p * (a p : ℝ) + ∑ i, g i * ((Function.update a p 0 i : ℕ) : ℝ) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    ← Finset.add_sum_erase _ (fun i => g i * ((Function.update a p 0 i : ℕ) : ℝ)) (Finset.mem_univ p)]
  simp only [Function.update_self, Nat.cast_zero, mul_zero, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have : i ≠ p := Finset.ne_of_mem_erase hi
  simp [Function.update_of_ne this]

theorem gk_max {m k : ℕ} (I : Instance m k)
    (hℓ : ∀ i, 0 < I.ℓ i) (b : Fin m → ℝ) (L c : ℝ) (hL : 0 ≤ L) :
    ∃ aStar : Fin m → ℕ,
      patLen I aStar ≤ L ∧
      (∀ a : Fin m → ℕ, patLen I a ≤ L →
        (∑ i, b i * (a i : ℝ)) ≤ ∑ i, b i * (aStar i : ℝ)) ∧
      knapF I b m L = ((∑ i, b i * (aStar i : ℝ) : ℝ) : EReal) ∧
      ((∃ a : Fin m → ℕ, patLen I a ≤ L ∧
        c < ∑ i, b i * (a i : ℝ)) ↔ c < ∑ i, b i * (aStar i : ℝ)) := by
  have hv : ∀ a : Fin m → ℕ, ∀ i : Fin m, m ≤ i.val → a i = 0 := fun a i hi =>
    absurd i.isLt (not_lt.2 hi)
  obtain ⟨aS, haS, hmax⟩ := gk_attain I b m (fun i _ => hℓ i) L
    ⟨fun _ => 0, hv _, by simpa [patLen] using hL⟩
  have hmax' : ∀ a : Fin m → ℕ, patLen I a ≤ L →
      (∑ i, b i * (a i : ℝ)) ≤ ∑ i, b i * (aS i : ℝ) := fun a ha => hmax a ⟨hv a, ha⟩
  refine ⟨aS, haS.2, hmax', gk_eq I b m L aS haS hmax, ?_⟩
  constructor
  · rintro ⟨a, ha, hc⟩
    exact lt_of_lt_of_le hc (hmax' a ha)
  · intro hc
    exact ⟨aS, haS.2, hc⟩


theorem gk_dp {m k : ℕ} (I : Instance m k)
    (b : Fin m → ℝ) (s : ℕ) (hs : s < m)
    (hℓ : ∀ i : Fin m, i.val ≤ s → 0 < I.ℓ i) (x : ℝ) :
    knapF I b (s + 1) x =
      ⨆ r ∈ Finset.range (⌊x / I.ℓ ⟨s, hs⟩⌋₊ + 1),
        (((r : ℝ) * b ⟨s, hs⟩ : ℝ) : EReal) +
          knapF I b s (x - r * I.ℓ ⟨s, hs⟩) := by
  set p : Fin m := ⟨s, hs⟩ with hp
  have hpos : ∀ i : Fin m, i.val < s → 0 < I.ℓ i := fun i hi => hℓ i hi.le
  apply le_antisymm
  · refine gk_le_of I b (s+1) x _ fun a ha => ?_
    obtain ⟨h0, hfit⟩ := ha
    set r := a p with hr
    set a' := Function.update a p 0 with ha'
    have h0' : ∀ i : Fin m, s ≤ i.val → a' i = 0 := by
      intro i hi
      by_cases hip : i = p
      · subst hip; simp [ha']
      · have : s + 1 ≤ i.val := by
          have : i.val ≠ s := fun h => hip (Fin.ext h)
          omega
        simp [ha', Function.update_of_ne hip, h0 i this]
    have hnn : 0 ≤ patLen I a' := by
      unfold patLen
      exact Finset.sum_nonneg fun i _ => gk_term_nonneg I s hpos a' h0' i
    have hsp : patLen I a = I.ℓ p * (r : ℝ) + patLen I a' := gk_split I.ℓ a p
    have hsb : (∑ i, b i * (a i : ℝ)) = b p * (r : ℝ) + ∑ i, b i * (a' i : ℝ) := gk_split b a p
    have hpp : 0 < I.ℓ p := hℓ p (by simp [hp])
    have hrle : r ∈ Finset.range (⌊x / I.ℓ p⌋₊ + 1) := by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      apply Nat.le_floor
      rw [le_div_iff₀ hpp]
      nlinarith
    have hfeas : KFeas I s (x - r * I.ℓ p) a' := ⟨h0', by nlinarith⟩
    refine le_iSup₂_of_le r hrle ?_
    rw [hsb, EReal.coe_add]
    have e : ((b p * (r : ℝ) : ℝ) : EReal) = (((r : ℝ) * b p : ℝ) : EReal) := by rw [mul_comm]
    rw [e]
    exact add_le_add_right (gk_le I b s _ a' hfeas) _
  · refine iSup₂_le fun r hr => ?_
    by_cases hex : ∃ a', KFeas I s (x - r * I.ℓ p) a'
    · obtain ⟨aS, haS, hmax⟩ := gk_attain I b s hpos _ hex
      rw [gk_eq I b s _ aS haS hmax, ← EReal.coe_add]
      set a := Function.update aS p (r : ℕ) with ha
      have hsp : patLen I a = I.ℓ p * (r : ℝ) + patLen I aS := by
        have := gk_split I.ℓ a p
        have e : Function.update a p 0 = aS := by
          rw [ha, Function.update_idem]
          exact Function.update_eq_self_iff.2 (haS.1 p (by simp [hp])).symm
        rw [e] at this
        unfold patLen
        simpa [ha] using this
      have hsb : (∑ i, b i * (a i : ℝ)) = b p * (r : ℝ) + ∑ i, b i * (aS i : ℝ) := by
        have := gk_split b a p
        have e : Function.update a p 0 = aS := by
          rw [ha, Function.update_idem]
          exact Function.update_eq_self_iff.2 (haS.1 p (by simp [hp])).symm
        rw [e] at this
        simpa [ha] using this
      have hfeas : KFeas I (s+1) x a := by
        refine ⟨?_, by rw [hsp]; linarith [haS.2]⟩
        intro i hi
        have hip : i ≠ p := fun h => by subst h; simp [hp] at hi
        rw [ha, Function.update_of_ne hip]
        exact haS.1 i (by
          have : i.val ≠ s := fun h => hip (Fin.ext h)
          omega)
      have := gk_le I b (s+1) x a hfeas
      rw [hsb] at this
      have e : ((b p * (r : ℝ) + ∑ i, b i * (aS i : ℝ) : ℝ) : EReal) =
          (((r : ℝ) * b p + ∑ i, b i * (aS i : ℝ) : ℝ) : EReal) := by rw [mul_comm (b p)]
      rwa [e] at this
    · rw [gk_bot I b s _ hex]
      simp

end KN
end GilmoreGomory61.CuttingStock

open GilmoreGomory61.CuttingStock


theorem solution {m k : ℕ} (I : Instance m k)
    (hℓ : ∀ i, 0 < I.ℓ i) (b : Fin m → ℝ) (L c : ℝ) (hL : 0 ≤ L) :
    ∃ aStar : Fin m → ℕ,
      patLen I aStar ≤ L ∧
      (∀ a : Fin m → ℕ, patLen I a ≤ L →
        (∑ i, b i * (a i : ℝ)) ≤ ∑ i, b i * (aStar i : ℝ)) ∧
      knapF I b m L = ((∑ i, b i * (aStar i : ℝ) : ℝ) : EReal) ∧
      ((∃ a : Fin m → ℕ, patLen I a ≤ L ∧
        c < ∑ i, b i * (a i : ℝ)) ↔ c < ∑ i, b i * (aStar i : ℝ)) := by
  exact gk_max I hℓ b L c hL
