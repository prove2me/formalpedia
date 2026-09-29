-- Prove2me | solution 1 for GravesWillems.Serial.backlog_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:56:08.898281+00:00
-- url     : https://prove2.me/submissions/ff303ee3-a30e-4073-a05f-2211a55b73c1

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog

namespace GravesWillems.Serial

theorem aux_bcf_window_add (d : ℤ → ℝ) {a b c : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    windowDemand d a b + windowDemand d b c = windowDemand d a c := by
  unfold windowDemand
  rw [← Finset.Ioc_union_Ioc_eq_Ioc h₁ h₂,
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]

theorem aux_bcf_sum_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) {i j : ℕ} (h : i ≤ j) :
    ∑ m ∈ Finset.Icc i j, f m = f i + ∑ m ∈ Finset.Icc (i + 1) j, f m := by
  rw [Finset.Icc_add_one_left_eq_Ioc, Finset.add_sum_Ioc_eq_sum_Icc h]

theorem aux_bcf_main (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) :
    ∀ (r i : ℕ) (t : ℤ) (n : ℕ) (h : i ≤ n), n = i + r →
      backlogAux T B d (r + 1) i t =
        max 0 ((Finset.Icc i n).sup' (Finset.nonempty_Icc.mpr h)
          (fun j => windowDemand d (t - ((∑ m ∈ Finset.Icc i j, T m : ℕ) : ℤ)) t
            - ∑ m ∈ Finset.Icc i j, B m)) := by
  intro r
  induction r with
  | zero =>
    intro i t n h hn
    subst hn
    simp only [Finset.Icc_self, Finset.sup'_singleton, Finset.sum_singleton]
    simp [backlogAux]
  | succ r ih =>
    intro i t n h hn
    have hn' : i + 1 ≤ n := by omega
    have IH := ih (i + 1) (t - (T i : ℤ)) n hn' (by omega)
    rw [show r + 1 + 1 = (r + 1) + 1 from rfl]
    rw [backlogAux, IH]
    set A : ℝ := windowDemand d (t - (T i : ℤ)) t - B i with hA
    set F : ℕ → ℝ := fun j => windowDemand d (t - ((∑ m ∈ Finset.Icc i j, T m : ℕ) : ℤ)) t
            - ∑ m ∈ Finset.Icc i j, B m with hF
    set G : ℕ → ℝ := fun j => windowDemand d (t - (T i : ℤ) -
        ((∑ m ∈ Finset.Icc (i + 1) j, T m : ℕ) : ℤ)) (t - (T i : ℤ))
            - ∑ m ∈ Finset.Icc (i + 1) j, B m with hG
    have hFi : F i = A := by
      simp [hF, hA]
    have hFG : ∀ j, i + 1 ≤ j → F j = A + G j := by
      intro j hj
      simp only [hF, hG, hA]
      rw [aux_bcf_sum_split T (by omega : i ≤ j), aux_bcf_sum_split B (by omega : i ≤ j)]
      have key := aux_bcf_window_add d
        (a := t - (T i : ℤ) - ((∑ m ∈ Finset.Icc (i + 1) j, T m : ℕ) : ℤ))
        (b := t - (T i : ℤ)) (c := t) (by omega) (by omega)
      have e : t - ((T i + ∑ m ∈ Finset.Icc (i + 1) j, T m : ℕ) : ℤ) =
          t - (T i : ℤ) - ((∑ m ∈ Finset.Icc (i + 1) j, T m : ℕ) : ℤ) := by
        push_cast; ring
      rw [e, ← key]
      ring
    have lhs_eq : windowDemand d (t - (T i : ℤ)) t +
        max 0 ((Finset.Icc (i + 1) n).sup' (Finset.nonempty_Icc.mpr hn') G) - B i =
        A + max 0 ((Finset.Icc (i + 1) n).sup' (Finset.nonempty_Icc.mpr hn') G) := by
      rw [hA]; ring
    rw [lhs_eq]
    apply le_antisymm
    · apply max_le (le_max_left _ _)
      rcases le_total ((Finset.Icc (i + 1) n).sup' (Finset.nonempty_Icc.mpr hn') G) 0 with hs | hs
      · rw [max_eq_left hs, add_zero]
        refine le_trans ?_ (le_max_right _ _)
        rw [← hFi]
        exact Finset.le_sup' F (Finset.mem_Icc.mpr ⟨le_rfl, h⟩)
      · rw [max_eq_right hs]
        refine le_trans ?_ (le_max_right _ _)
        have : (Finset.Icc (i + 1) n).sup' (Finset.nonempty_Icc.mpr hn') G ≤
            (Finset.Icc i n).sup' (Finset.nonempty_Icc.mpr h) F - A := by
          apply Finset.sup'_le
          intro j hj
          have hj' := Finset.mem_Icc.mp hj
          have := Finset.le_sup' F (Finset.mem_Icc.mpr ⟨(by omega : i ≤ j), hj'.2⟩)
          rw [hFG j hj'.1] at this
          linarith
        linarith
    · apply max_le (le_max_left _ _)
      apply Finset.sup'_le
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      refine le_trans ?_ (le_max_right _ _)
      rcases Nat.eq_or_lt_of_le hj'.1 with hji | hji
      · subst hji
        rw [hFi]
        have := le_max_left 0 ((Finset.Icc (i + 1) n).sup' (Finset.nonempty_Icc.mpr hn') G)
        linarith
      · rw [hFG j hji]
        have h1 := Finset.le_sup' G (Finset.mem_Icc.mpr ⟨hji, hj'.2⟩)
        have h2 := le_max_right 0 ((Finset.Icc (i + 1) n).sup' (Finset.nonempty_Icc.mpr hn') G)
        linarith

end GravesWillems.Serial

open GravesWillems.Serial

theorem solution (N : ℕ) (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 N) (t : ℤ) :
    backlog N T B d i t =
      max 0 ((Finset.Icc i N).sup' (Finset.nonempty_Icc.mpr (Finset.mem_Icc.mp hi).2)
        (fun j => windowDemand d (t - ((∑ m ∈ Finset.Icc i j, T m : ℕ) : ℤ)) t
          - ∑ m ∈ Finset.Icc i j, B m)) := by
  have hi' := Finset.mem_Icc.mp hi
  unfold backlog
  rw [show N + 1 - i = (N - i) + 1 by omega]
  exact aux_bcf_main T B d (N - i) i t N hi'.2 (by omega)
