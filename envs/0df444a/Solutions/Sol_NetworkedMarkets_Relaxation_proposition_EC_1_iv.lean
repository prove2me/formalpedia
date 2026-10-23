-- Prove2me | solution 1 for NetworkedMarkets.Relaxation.proposition_EC_1_iv
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:46:13.900029+00:00
-- url     : https://prove2.me/submissions/ce0309d8-3c3e-4699-bb89-b7502608a219

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NMAux4
open NetworkedMarkets.Relaxation
variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

lemma gB_eq (M : Market S B) (j : B) (hb : 0 < M.b j) (q : ℝ) :
    M.gB j q = M.b j * ((q / M.b j) * (M.Fb j).Finv (1 - q / M.b j)) := by
  simp only [Market.gB]; field_simp

lemma hS_eq (M : Market S B) (i : S) (hs : 0 < M.s i) (q : ℝ) :
    M.hS i q = M.s i * ((q / M.s i) * (M.Fs i).Finv (q / M.s i)) := by
  simp only [Market.hS]; field_simp

lemma mid_gB (M : Market S B) (hM : M.Standing) (j : B) (a c : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ M.b j) (hc : 0 ≤ c) (hc' : c ≤ M.b j) :
    (M.gB j a + M.gB j c) / 2 ≤ M.gB j ((a + c) / 2) ∧
      (a ≠ c → (M.gB j a + M.gB j c) / 2 < M.gB j ((a + c) / 2)) := by
  have hb := hM.1.2.1 j
  have hcc := hM.2.1 j
  have key : a ≠ c → (M.gB j a + M.gB j c) / 2 < M.gB j ((a + c) / 2) := by
    intro hne
    have hu : a / M.b j ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg ha hb.le, (div_le_one hb).mpr ha'⟩
    have hv : c / M.b j ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg hc hb.le, (div_le_one hb).mpr hc'⟩
    have hne' : a / M.b j ≠ c / M.b j := by
      intro h; apply hne; field_simp at h; linarith
    have := hcc.2 hu hv hne' (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    rw [gB_eq M j hb a, gB_eq M j hb c, gB_eq M j hb ((a + c) / 2)]
    have e : (a + c) / 2 / M.b j = 1/2 * (a / M.b j) + 1/2 * (c / M.b j) := by ring
    rw [e]
    nlinarith
  refine ⟨?_, key⟩
  by_cases h : a = c
  · subst h; ring_nf; rfl
  · exact (key h).le

lemma mid_hS (M : Market S B) (hM : M.Standing) (i : S) (a c : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ M.s i) (hat : (M.Fs i).vbar = ⊤ → a < M.s i)
    (hc : 0 ≤ c) (hc' : c ≤ M.s i) (hct : (M.Fs i).vbar = ⊤ → c < M.s i) :
    M.hS i ((a + c) / 2) ≤ (M.hS i a + M.hS i c) / 2 ∧
      (a ≠ c → M.hS i ((a + c) / 2) < (M.hS i a + M.hS i c) / 2) := by
  have hs := hM.1.1 i
  have hcc := hM.2.2 i
  have key : a ≠ c → M.hS i ((a + c) / 2) < (M.hS i a + M.hS i c) / 2 := by
    intro hne
    have hu : a / M.s i ∈ (M.Fs i).sellerUnitDom :=
      ⟨div_nonneg ha hs.le, (div_le_one hs).mpr ha', fun ht => (div_lt_one hs).mpr (hat ht)⟩
    have hv : c / M.s i ∈ (M.Fs i).sellerUnitDom :=
      ⟨div_nonneg hc hs.le, (div_le_one hs).mpr hc', fun ht => (div_lt_one hs).mpr (hct ht)⟩
    have hne' : a / M.s i ≠ c / M.s i := by
      intro h; apply hne; field_simp at h; linarith
    have := hcc.2 hu hv hne' (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    rw [hS_eq M i hs a, hS_eq M i hs c, hS_eq M i hs ((a + c) / 2)]
    have e : (a + c) / 2 / M.s i = 1/2 * (a / M.s i) + 1/2 * (c / M.s i) := by ring
    rw [e]
    nlinarith
  refine ⟨?_, key⟩
  by_cases h : a = c
  · subst h; ring_nf; rfl
  · exact (key h).le

lemma feas_nonneg_qs (M : Market S B) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (h : M.Feas7 x qs qb) (i : S) : 0 ≤ qs i := by
  have := h.2.1 i
  have : qs i = ∑ j ∈ M.nbrS i, x i j := by linarith
  rw [this]; exact Finset.sum_nonneg (fun j hj => h.2.2.2.2.1 i j (by simpa [Market.nbrS] using hj))

lemma feas_nonneg_qb (M : Market S B) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (h : M.Feas7 x qs qb) (j : B) : 0 ≤ qb j := by
  have := h.1 j
  have : qb j = ∑ i ∈ M.nbrB j, x i j := by linarith
  rw [this]; exact Finset.sum_nonneg (fun i hi => h.2.2.2.2.1 i j (by simpa [Market.nbrB] using hi))

lemma feas_mid (M : Market S B) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    {x' : S → B → ℝ} {qs' : S → ℝ} {qb' : B → ℝ}
    (h : M.Feas7 x qs qb) (h' : M.Feas7 x' qs' qb') :
    M.Feas7 (fun i j => (x i j + x' i j) / 2) (fun i => (qs i + qs' i) / 2)
      (fun j => (qb j + qb' j) / 2) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h'
  refine ⟨fun j => ?_, fun i => ?_, fun j => ?_, fun i => ?_, fun i j he => ?_, fun i ht => ?_⟩
  · simp only; rw [← Finset.sum_div, Finset.sum_add_distrib]; linarith [a1 j, b1 j]
  · simp only; rw [← Finset.sum_div, Finset.sum_add_distrib]; linarith [a2 i, b2 i]
  · simp only; linarith [a3 j, b3 j]
  · simp only; linarith [a4 i, b4 i]
  · simp only; linarith [a5 i j he, b5 i j he]
  · simp only; linarith [a6 i ht, b6 i ht]

end NMAux4

open NetworkedMarkets.Relaxation NMAux4 in
theorem solution {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (x' : S → B → ℝ) (qs' : S → ℝ) (qb' : B → ℝ)
    (hopt : M.IsOpt7 x qs qb) (hopt' : M.IsOpt7 x' qs' qb') :
    qs = qs' ∧ qb = qb' := by
  have hF := hopt.1
  have hF' := hopt'.1
  have hmid := feas_mid M hF hF'
  have h1 := hopt.2 _ _ _ hmid
  have hle1 := hopt.2 _ _ _ hF'
  have hle2 := hopt'.2 _ _ _ hF
  set Dg : B → ℝ := fun j => M.gB j ((qb j + qb' j) / 2) - (M.gB j (qb j) + M.gB j (qb' j)) / 2
  set Dh : S → ℝ := fun i => (M.hS i (qs i) + M.hS i (qs' i)) / 2 - M.hS i ((qs i + qs' i) / 2)
  have hDg : ∀ j, 0 ≤ Dg j ∧ (qb j ≠ qb' j → 0 < Dg j) := by
    intro j
    have := mid_gB M hM j (qb j) (qb' j) (feas_nonneg_qb M hF j) (hF.2.2.1 j)
      (feas_nonneg_qb M hF' j) (hF'.2.2.1 j)
    exact ⟨by simp only [Dg]; linarith [this.1], fun hne => by simp only [Dg]; linarith [this.2 hne]⟩
  have hDh : ∀ i, 0 ≤ Dh i ∧ (qs i ≠ qs' i → 0 < Dh i) := by
    intro i
    have := mid_hS M hM i (qs i) (qs' i) (feas_nonneg_qs M hF i) (hF.2.2.2.1 i) (hF.2.2.2.2.2 i)
      (feas_nonneg_qs M hF' i) (hF'.2.2.2.1 i) (hF'.2.2.2.2.2 i)
    exact ⟨by simp only [Dh]; linarith [this.1], fun hne => by simp only [Dh]; linarith [this.2 hne]⟩
  have hexp : M.h (fun i => (qs i + qs' i) / 2) (fun j => (qb j + qb' j) / 2) =
      (M.h qs qb + M.h qs' qb') / 2 + ∑ j, Dg j + ∑ i, Dh i := by
    simp only [Market.h, Dg, Dh, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
      Finset.mul_sum]
    have : ∑ i, M.c i * ((qs i + qs' i) / 2) = (∑ i, M.c i * qs i + ∑ i, M.c i * qs' i) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    rw [this]; ring
  have hSg : 0 ≤ ∑ j, Dg j := Finset.sum_nonneg (fun j _ => (hDg j).1)
  have hSh : 0 ≤ ∑ i, Dh i := Finset.sum_nonneg (fun i _ => (hDh i).1)
  constructor
  · funext i
    by_contra hne
    have : 0 < ∑ i, Dh i := Finset.sum_pos' (fun i _ => (hDh i).1) ⟨i, Finset.mem_univ _, (hDh i).2 hne⟩
    linarith
  · funext j
    by_contra hne
    have : 0 < ∑ j, Dg j := Finset.sum_pos' (fun j _ => (hDg j).1) ⟨j, Finset.mem_univ _, (hDg j).2 hne⟩
    linarith
