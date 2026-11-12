-- Prove2me | solution 1 for NarrowDNF.Approx.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:54:26.256894+00:00
-- url     : https://prove2.me/submissions/2bd0806e-61ab-4185-affb-809ded0ffe22

import Mathlib
import Definitions.Def_NarrowDNF_Approx_Certificates

section
set_option autoImplicit false
namespace NarrowDNF.Dev.L41
open NarrowDNF.Approx
open Classical

noncomputable def wt {n : ℕ} (p : ℝ) (x : Cube n) : ℝ := ∏ i : Fin n, FriedgutCoalition.bern p (x i)

lemma prob_eq {n : ℕ} (p : ℝ) (E : Cube n → Prop) [DecidablePred E] :
    prob p E = ∑ x : Cube n, if E x then wt p x else 0 := by
  unfold prob FriedgutCoalition.wProb wt
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : E x <;> simp [h]

lemma wt_nonneg {n : ℕ} (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : Cube n) : 0 ≤ wt p x :=
  Finset.prod_nonneg (fun j _ => by
    simp only [FriedgutCoalition.bern]; split_ifs <;> linarith)

lemma mem_activeUnion {n : ℕ} (J : ActivationFamily n) (x : Cube n) (i : Fin n) :
    i ∈ activeUnion J x ↔ ∃ S : Finset (Fin n), J S (fun j => x j) = true ∧ i ∈ S := by
  unfold activeUnion
  simp [Finset.mem_biUnion]

lemma mem_activeOnes {n : ℕ} (J : ActivationFamily n) (x : Cube n) (i : Fin n) :
    i ∈ activeOnes J x ↔ i ∈ activeUnion J x ∧ x i = true := by
  unfold activeOnes
  simp

/-- the truncation of x to its active ones -/
noncomputable def trunc {n : ℕ} (J : ActivationFamily n) (x : Cube n) : Cube n :=
  fun i => decide (i ∈ activeOnes J x)

lemma trunc_le {n : ℕ} (J : ActivationFamily n) (x : Cube n) : trunc J x ≤ x := by
  intro i
  unfold trunc
  by_cases h : i ∈ activeOnes J x
  · have := ((mem_activeOnes J x i).1 h).2
    simp [h, this]
  · simp [h]

lemma trunc_eq_on {n : ℕ} (J : ActivationFamily n) (x : Cube n) (i : Fin n)
    (hi : i ∈ activeUnion J x) : trunc J x i = x i := by
  unfold trunc
  by_cases h : x i = true
  · have : i ∈ activeOnes J x := (mem_activeOnes J x i).2 ⟨hi, h⟩
    simp [this, h]
  · have : i ∉ activeOnes J x := fun h' => h ((mem_activeOnes J x i).1 h').2
    simp [this]
    simpa using h

lemma activeUnion_trunc {n : ℕ} (J : ActivationFamily n) (hJ : IncreasingActivations J)
    (x : Cube n) : activeUnion J (trunc J x) = activeUnion J x := by
  ext i
  rw [mem_activeUnion, mem_activeUnion]
  constructor
  · rintro ⟨S, hS, hi⟩
    refine ⟨S, ?_, hi⟩
    have := hJ S (fun j : S => (trunc_le J x) j)
    rw [hS] at this
    exact Bool.eq_true_of_true_le this
  · rintro ⟨S, hS, hi⟩
    refine ⟨S, ?_, hi⟩
    have : (fun j : S => trunc J x j) = fun j : S => x j := by
      funext j
      apply trunc_eq_on
      exact (mem_activeUnion J x j).2 ⟨S, hS, j.2⟩
    rw [this]; exact hS

lemma atom_trunc {n : ℕ} (J : ActivationFamily n) (hJ : IncreasingActivations J)
    (x : Cube n) : atom J (trunc J x) = atom J x := by
  have hA := activeUnion_trunc J hJ x
  unfold atom
  rw [hA]
  congr 1
  funext i
  exact trunc_eq_on J x i i.2

lemma cert {n : ℕ} (J : ActivationFamily n) (u : Cube n → Bool)
    (hJ : IncreasingActivations J) (hu : Monotone u) (humeas : AdaptiveMeasurable J u)
    (x : Cube n) (hx : u x = true) : PositiveCertificate u (activeOnes J x) := by
  intro y hy
  have h1 : u (trunc J x) = true := by
    rw [humeas _ _ (atom_trunc J hJ x)]; exact hx
  have h2 : trunc J x ≤ y := by
    intro i
    unfold trunc
    by_cases h : i ∈ activeOnes J x
    · simp [h, hy i h]
    · simp [h]
  have := hu h2
  rw [h1] at this
  exact Bool.eq_true_of_true_le this

lemma evalDNF_mono {n : ℕ} (g : DNF n) : Monotone (evalDNF g) := by
  intro x y hxy
  unfold evalDNF
  by_cases h : ∃ T ∈ g, ∀ i ∈ T, x i = true
  · obtain ⟨T, hT, hT'⟩ := h
    have : ∃ T ∈ g, ∀ i ∈ T, y i = true :=
      ⟨T, hT, fun i hi => Bool.eq_true_of_true_le (by have := hxy i; rw [hT' i hi] at this; exact this)⟩
    simp [this]
  · simp [h]

lemma card_activeOnes_le {n : ℕ} (J : ActivationFamily n) (x : Cube n) :
    (activeOnes J x).card ≤ (activeUnion J x).card := by
  unfold activeOnes; exact Finset.card_filter_le _ _

lemma prob_mono {n : ℕ} (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (E F : Cube n → Prop)
    (h : ∀ x, E x → F x) : prob p E ≤ prob p F := by
  rw [prob_eq, prob_eq]
  refine Finset.sum_le_sum (fun x _ => ?_)
  by_cases hE : E x
  · simp [hE, h x hE]
  · simp only [hE, if_false]
    split_ifs
    · exact wt_nonneg p h0 h1 x
    · exact le_refl _

end NarrowDNF.Dev.L41

namespace NarrowDNF.Approx
open NarrowDNF.Dev.L41 in
theorem chk_lemma_4_1 {n : ℕ} (p : ℝ) (J : ActivationFamily n) (u : Cube n → Bool)
    (hp : 0 < p) (hp_one : p < 1) (hJ : IncreasingActivations J)
    (hu : Monotone u) (humeas : AdaptiveMeasurable J u) :
    (∀ x, u x = true → PositiveCertificate u (activeOnes J x)) ∧
    (∀ w : ℕ, width (truncatedDNF J u w) ≤ w ∧ Monotone (evalDNF (truncatedDNF J u w)) ∧
      (∀ y, evalDNF (truncatedDNF J u w) y ≤ u y) ∧
      error p u (evalDNF (truncatedDNF J u w)) ≤
        prob p (fun x => w < (activeOnes J x).card) ∧
      prob p (fun x => w < (activeOnes J x).card) ≤ activeCost p J / ((w : ℝ) + 1)) := by
  have hc := cert J u hJ hu humeas
  refine ⟨hc, fun w => ?_⟩
  have hmem : ∀ x, u x = true → (activeOnes J x).card ≤ w →
      activeOnes J x ∈ truncatedDNF J u w := by
    intro x hx hw
    unfold truncatedDNF
    rw [Finset.mem_image]
    exact ⟨x, by simp [hx, hw], rfl⟩
  have hle : ∀ y, evalDNF (truncatedDNF J u w) y ≤ u y := by
    intro y
    unfold evalDNF
    by_cases h : ∃ T ∈ truncatedDNF J u w, ∀ i ∈ T, y i = true
    · obtain ⟨T, hT, hT'⟩ := h
      unfold truncatedDNF at hT
      rw [Finset.mem_image] at hT
      obtain ⟨x, hx, rfl⟩ := hT
      have hx' : u x = true := by simpa using (Finset.mem_filter.1 hx).2.1
      have := hc x hx' y hT'
      simp [this]
    · simp [h]
  refine ⟨?_, evalDNF_mono _, hle, ?_, ?_⟩
  · unfold width truncatedDNF
    refine Finset.sup_le (fun T hT => ?_)
    rw [Finset.mem_image] at hT
    obtain ⟨x, hx, rfl⟩ := hT
    exact (Finset.mem_filter.1 hx).2.2
  · unfold error
    refine prob_mono p hp.le hp_one.le _ _ (fun x hx => ?_)
    by_contra hcon
    push Not at hcon
    have hux : u x = true := by
      cases hu' : u x
      · exfalso
        have h3 := hle x
        rw [hu'] at h3
        have h2 : evalDNF (truncatedDNF J u w) x = false := by
          cases hg : evalDNF (truncatedDNF J u w) x
          · rfl
          · rw [hg] at h3; exact absurd h3 (by decide)
        exact hx (by rw [hu', h2])
      · rfl
    have hmem' := hmem x hux hcon
    have : evalDNF (truncatedDNF J u w) x = true := by
      unfold evalDNF
      simp only [decide_eq_true_eq]
      refine ⟨activeOnes J x, hmem', fun i hi => ?_⟩
      exact ((mem_activeOnes J x i).1 hi).2
    exact hx (by rw [hux, this])
  · unfold activeCost
    rw [prob_eq, expect, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_le_sum (fun x _ => ?_)
    have hw0 : 0 ≤ wt p x := wt_nonneg p hp.le hp_one.le x
    have hw : (0 : ℝ) < (w : ℝ) + 1 := by positivity
    by_cases h : w < (activeOnes J x).card
    · simp only [h, if_true]
      have h1 : ((w : ℝ) + 1) ≤ ((activeUnion J x).card : ℝ) := by
        exact_mod_cast (h.trans_le (card_activeOnes_le J x))
      have : (1 : ℝ) ≤ ((activeUnion J x).card : ℝ) * ((w : ℝ) + 1)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hw]; linarith
      calc wt p x = wt p x * 1 := by ring
        _ ≤ wt p x * (((activeUnion J x).card : ℝ) * ((w : ℝ) + 1)⁻¹) :=
            mul_le_mul_of_nonneg_left this hw0
        _ = _ := by unfold wt; ring
    · simp only [h, if_false]
      positivity

end NarrowDNF.Approx
end

theorem solution : type_of% @NarrowDNF.Approx.chk_lemma_4_1 := @NarrowDNF.Approx.chk_lemma_4_1
