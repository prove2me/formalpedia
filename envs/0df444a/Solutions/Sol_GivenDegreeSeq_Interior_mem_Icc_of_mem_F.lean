-- Prove2me | solution 1 for GivenDegreeSeq.Interior.mem_Icc_of_mem_F
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:23:25.15275+00:00
-- url     : https://prove2.me/submissions/ea9de93f-6b07-4360-9537-4162e68d809c

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_ScalingLimit

set_option autoImplicit false
open GivenDegreeSeq.Interior

open Classical in
lemma gdi_graphic_lt {n : ℕ} (d : Fin n → ℕ) (h : IsGraphic d) (i : Fin n) : d i < n := by
  obtain ⟨G, hG⟩ := h
  have := G.degree_lt_card_verts i
  rw [hG i] at this
  simpa using this

lemma gdi_endpoints (d : (n : ℕ) → Fin n → ℕ) (f : ℝ → ℝ)
    (hd : ∀ n, IsGraphic (d n))
    (hlim : Filter.Tendsto (scalingError d f) Filter.atTop (nhds 0)) :
    (0 ≤ f 0 ∧ f 0 ≤ 1) ∧ (0 ≤ f 1 ∧ f 1 ≤ 1) := by
  have key : ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ h : 0 < n,
      |(d n ⟨0, h⟩ : ℝ) / n - f 0| < ε ∧
      |(d n ⟨n - 1, Nat.sub_lt h Nat.one_pos⟩ : ℝ) / n - f 1| < ε := by
    intro ε hε
    have h1 := hlim.eventually (gt_mem_nhds hε)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h1
    refine ⟨max N 1, lt_of_lt_of_le Nat.one_pos (le_max_right _ _), ?_⟩
    have hpos : 0 < max N 1 := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
    have hh := hN (max N 1) (le_max_left _ _)
    unfold scalingError at hh
    rw [dif_pos hpos] at hh
    have hs : 0 ≤ (1 / ((max N 1 : ℕ) : ℝ)) * ∑ i : Fin (max N 1),
        |(d (max N 1) i : ℝ) / (max N 1 : ℕ) - f (((i : ℕ) + 1 : ℝ) / (max N 1 : ℕ))| := by
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have a1 := abs_nonneg ((d (max N 1) ⟨0, hpos⟩ : ℝ) / (max N 1 : ℕ) - f 0)
    have a2 := abs_nonneg ((d (max N 1) ⟨max N 1 - 1, Nat.sub_lt hpos Nat.one_pos⟩ : ℝ) / (max N 1 : ℕ) - f 1)
    constructor <;> linarith
  have bnd : ∀ (n : ℕ) (i : Fin n), 0 ≤ (d n i : ℝ) / n ∧ (d n i : ℝ) / n ≤ 1 := by
    intro n i
    have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) i.2)
    have := gdi_graphic_lt (d n) (hd n) i
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hn]
    exact_mod_cast this.le
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨n, h, h0, _⟩ := key ε hε
    have := (abs_lt.1 h0).2
    have := (bnd n ⟨0, h⟩).1
    linarith
  · refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨n, h, h0, _⟩ := key ε hε
    have := (abs_lt.1 h0).1
    have := (bnd n ⟨0, h⟩).2
    linarith
  · refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨n, h, _, h0⟩ := key ε hε
    have := (abs_lt.1 h0).2
    have := (bnd n ⟨n - 1, Nat.sub_lt h Nat.one_pos⟩).1
    linarith
  · refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨n, h, _, h0⟩ := key ε hε
    have := (abs_lt.1 h0).1
    have := (bnd n ⟨n - 1, Nat.sub_lt h Nat.one_pos⟩).2
    linarith

theorem solution (f : ℝ → ℝ) (hf : f ∈ setF) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨⟨hanti, _⟩, d, hd, _, hlim⟩ := hf
  obtain ⟨⟨h0a, h0b⟩, ⟨h1a, h1b⟩⟩ := gdi_endpoints d f (fun n => (hd n).2) hlim
  intro x hx
  have e0 := hanti (Set.left_mem_Icc.2 zero_le_one) hx hx.1
  have e1 := hanti hx (Set.right_mem_Icc.2 zero_le_one) hx.2
  exact ⟨by linarith, by linarith⟩
